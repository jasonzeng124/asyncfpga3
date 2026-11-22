#!/usr/bin/env python3
"""mk_specs_all.py RS OUTDIR RESULTS_PART...  (shard B, 2026-11-21) -- research's mk_board_specs.py (claude/research
research/tools/suite/mk_board_specs.py, same rules: status=PASS, rule=clean, bits=EQUIVALENT, ffmux-clean; the shipped
iteration's sizes / trims / seed / search ENV / memo MLIR) for EVERY seed, not only the lowest, and only for kernels
whose suite vectors formal's bench boundary takes (no '// benchvec' memory vectors), or with --mem also those (written
with MEM=1: v10screen.sh decodes them with shard C's margin/bram/memtask.sh and runs only the structural bound).  Writes OUTDIR/K_s<seed>.spec
(+ sizes / trims files) with FASM=00000000 (no judged fasm: v10screen.sh reports the md5 instead) and OUTDIR/list.txt."""
import glob, os, re, shutil, sys
MEM = "--mem" in sys.argv; argv = [a for a in sys.argv if a != "--mem"]
CACHE = "research/data/autorw/cache.tsv"
STAGEFIX = "--stagefix" in argv; argv = [a for a in argv if a != "--stagefix"]   # research 2026-11-22 00:16: flows v11 on
# record stage-aware _SDELAY trims, which trim_lines.py names only with TRIM_STAGEFIX=1 in its environment
if "--cache" in argv: i = argv.index("--cache"); CACHE = argv[i + 1]; del argv[i:i + 2]   # e.g. cache_v11.tsv for flow v11   # --mem: also memory kernels (benchvec vectors)
RS, out, parts = argv[1], argv[2], argv[3:]
memo = {}
for l in open(os.path.join(RS, CACHE)):
    f = l.rstrip("\n").split("\t")
    if not l.startswith("#") and len(f) >= 4 and f[2] != "none": memo[(f[1], f[2])] = f[3]
def vecfile(k):
    special = {"xorshift": "xor19", "collatz": "col18", "collatz64": "c6419", "ipow": "ipow17"}
    if k in special: return "research/data/eventgraph/gate/%s.hex" % special[k]
    if k == "isprime": return "research/data/alltable/isp17.hex"
    if k == "gcd": return "research/data/suite/vec/gcd8.hex"
    v = "kernels/%s/vec.hex" % k
    return v if os.path.exists(os.path.join(RS, v)) else "research/data/suite/vec/%s.hex" % k
os.makedirs(out, exist_ok=True); lst = []
for p in parts:
    for rf in sorted(glob.glob(os.path.join(p, "*", "result.txt"))):
        txt = open(rf).read().strip()
        if not txt: continue
        line = txt.splitlines()[-1]; m = re.match(r"(\S+) (\d+) status=(\S+)", line)
        if not m: continue
        k, s, st = m.group(1), int(m.group(2)), m.group(3); kv = dict(re.findall(r"(\w+)=(\S+)", line))
        if st != "PASS" or kv.get("rule") != "clean" or kv.get("bits") != "EQUIVALENT" or "ffmux-clean" not in line: continue
        vf = os.path.join(RS, vecfile(k))
        mem = os.path.exists(vf) and open(vf).readline().startswith("// benchvec")
        if not os.path.exists(vf) or (mem and not MEM): continue
        d = os.path.dirname(rf); a = os.path.join(d, "auto")
        try: last = [l for l in open(os.path.join(a, "result.txt")).read().splitlines() if l.startswith("CLEAN it=")][-1]
        except (OSError, IndexError): print("%s s%d: no CLEAN line" % (k, s)); continue
        it = re.match(r"CLEAN it=(\d+)", last).group(1)
        try: seed = open(os.path.join(a, "seed_%s.txt" % it)).read().split()[0]
        except (OSError, IndexError): print("%s s%d: no seed file" % (k, s)); continue
        sz = os.path.join(a, "sizes_%s.vh" % it)
        if not os.path.exists(sz): print("%s s%d: no sizes" % (k, s)); continue
        mm = re.search(r"; search ([^)]*)\)", last); env = mm.group(1).strip() if mm else ""
        try:   # flow v11's late finish phase: routes symtrim_from <= I <= overbuild_to were built with BD_SYMTRIM (research's
            # mk_board_specs.py since 2026-11-21 08:17 UTC, as auto_size.sh's build())
            sf = int(open(os.path.join(a, "symtrim_from.txt")).read().split()[0])
            ot = int(open(os.path.join(a, "overbuild_to.txt")).read().split()[0]) if os.path.exists(os.path.join(a, "overbuild_to.txt")) else 10 ** 6
            if sf <= int(it) <= ot: env = (env + " BD_DEFINES=-DBD_SYMTRIM").strip()
        except (OSError, IndexError, ValueError): pass
        if STAGEFIX: env = (env + " TRIM_STAGEFIX=1").strip()
        rw = kv.get("rw", "none"); mlir = "-"; pm = re.match(r"([a-z0-9_]+)\(memo@", rw)
        if pm and pm.group(1) != "none":
            mlir = memo.get((k, pm.group(1)))
            if not mlir: print("%s s%d: rw %s not in memo" % (k, s, rw)); continue
        elif rw != "none" and not rw.startswith("none"): print("%s s%d: rw %s not understood" % (k, s, rw)); continue
        tr = os.path.join(a, "trim_%s.txt" % it); has_tr = os.path.exists(tr) and open(tr).read().strip()
        nm = "%s_s%d" % (k, s); rel = os.path.relpath(out, os.path.join(os.path.dirname(__file__), "../../../.."))
        shutil.copy(sz, os.path.join(out, nm + "_sizes.vh"))
        if has_tr: shutil.copy(tr, os.path.join(out, nm + "_trims.txt"))
        open(os.path.join(out, nm + ".spec"), "w").write(
            "# %s seed %d, route %s (farm %s): P=%s; rw=%s\nMEM=%d\nK=%s\nSEED=%s\nSIZES=%s/%s_sizes.vh\nTRIMS=%s\nMLIR=%s\nENV=%s\nSDF=%s\nFASM=00000000\n"
            % (k, s, re.search(r"route=(\S+)", last).group(1), os.path.relpath(d, os.path.dirname(os.path.dirname(d))), kv.get("P", "NA"), rw, int(mem),
               k, seed, rel, nm, ("%s/%s_trims.txt" % (rel, nm)) if has_tr else "-", mlir, env, kv.get("sdf", "")))
        lst.append(nm)
open(os.path.join(out, "list.txt"), "w").write("\n".join(sorted(set(lst))) + "\n")
print("%d specs" % len(set(lst)))
