#!/usr/bin/env python3
"""mk_board_specs.py OUTDIR RESULTS_PART... -- one board_rebuild.sh spec per kernel, from a flow's farm results.

For each kernel with a judged rule-CLEAN route that PASSED (status=PASS, rule=clean, bits=EQUIVALENT, ffmux-clean),
the route of its lowest seed: OUTDIR/K.spec, OUTDIR/K_sizes.vh (the shipped iteration's sizes_I.vh), OUTDIR/K_trims.txt
(its trim_I.txt; TRIMS=- when the route was not trimmed). The route is rebuilt exactly as auto_size.sh's AUTO_TRIM_ONLY
path rebuilds a shipped route from a farm save: the iteration I from "CLEAN it=I", its seed from seed_I.txt, the search
phase's structure from the line's "(last it J; search ENV)" when that phase shipped it, and the proved MLIR from the
result line's rw=PASS(memo@...) through the memo table (--cache, default research/data/autorw/cache.tsv: the kernel's
row's output file; rw=none: no override), and BD_DEFINES=-DBD_SYMTRIM for a route of flow v11's late finish phase
(symtrim_from.txt <= I <= overbuild_to.txt, as auto_size.sh's build()). SDF = the result line's sdf; FASM = 00000000, a placeholder that
board_rebuild.sh refuses (it prints the trimmed fasm's md5: --fill writes it in after a rebuild).
    --fill OUTDIR/K.spec MD5   writes the trimmed fasm md5 into one spec (after a rebuild that matched its SDF)
Prints one line per kernel (spec written, or why not)."""
import glob
import os
import re
import shutil
import sys

R = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../.."))


def fill(spec, md5):
    s = open(spec).read()
    s2 = re.sub(r"^FASM=.*$", "FASM=%s" % md5[:8], s, flags=re.M)
    open(spec, "w").write(s2)
    print("%s: FASM=%s" % (spec, md5[:8]))


def main():
    if sys.argv[1] == "--fill":
        return fill(sys.argv[2], sys.argv[3])
    args = sys.argv[1:]
    cache = os.path.join(R, "research/data/autorw/cache.tsv")
    if "--cache" in args:
        i = args.index("--cache"); cache = args[i + 1]; del args[i:i + 2]
    out, parts = args[0], args[1:]
    memo = {}
    for l in open(cache):
        if l.startswith("#") or not l.strip():
            continue
        f = l.rstrip("\n").split("\t")
        if len(f) >= 4 and f[2] != "none":
            memo[(f[1], f[2])] = f[3]
    best = {}
    for p in parts:
        for rf in glob.glob(os.path.join(p, "*", "result.txt")):
            line = open(rf).read().strip().splitlines()[-1] if open(rf).read().strip() else ""
            m = re.match(r"(\S+) (\d+) status=(\S+)", line)
            if not m:
                continue
            k, s, st = m.group(1), int(m.group(2)), m.group(3)
            kv = dict(re.findall(r"(\w+)=(\S+)", line))
            if st != "PASS" or kv.get("rule") != "clean" or kv.get("bits") != "EQUIVALENT" or "ffmux-clean" not in line:
                continue
            if k not in best or s < best[k][0]:
                best[k] = (s, os.path.dirname(rf), kv)
    os.makedirs(out, exist_ok=True)
    for k in sorted(best):
        s, d, kv = best[k]
        a = os.path.join(d, "auto")
        try:
            last = [l for l in open(os.path.join(a, "result.txt")).read().splitlines() if l.startswith("CLEAN it=")][-1]
        except (OSError, IndexError):
            print("%s s%d: no CLEAN line in auto/result.txt: no spec" % (k, s)); continue
        it = re.match(r"CLEAN it=(\d+)", last).group(1)
        try:
            seed = open(os.path.join(a, "seed_%s.txt" % it)).read().split()[0]
        except (OSError, IndexError):
            print("%s s%d: no seed_%s.txt: no spec" % (k, s, it)); continue
        sz = os.path.join(a, "sizes_%s.vh" % it)
        if not os.path.exists(sz):
            print("%s s%d: no sizes_%s.vh: no spec" % (k, s, it)); continue
        env = ""
        m = re.search(r"; search ([^)]*)\)", last)
        if m:
            env = m.group(1).strip()
        # flow v11's late finish phase (AUTO_OVERBUILD_LATE): routes symtrim_from <= I <= overbuild_to were built with
        # BD_DEFINES=-DBD_SYMTRIM (auto_size.sh build()); the spec must build them the same way
        try:
            sf = int(open(os.path.join(a, "symtrim_from.txt")).read().split()[0])
            ot = int(open(os.path.join(a, "overbuild_to.txt")).read().split()[0]) if os.path.exists(
                os.path.join(a, "overbuild_to.txt")) else 10 ** 6
            if sf <= int(it) <= ot:
                env = (env + " BD_DEFINES=-DBD_SYMTRIM").strip()
        except (OSError, IndexError, ValueError):
            pass
        rw = kv.get("rw", "none")
        mlir = "-"
        pm = re.match(r"([a-z0-9_]+)\(memo@", rw)
        if pm and pm.group(1) != "none":
            mlir = memo.get((k, pm.group(1)))
            if not mlir:
                print("%s s%d: rw=%s has no row in %s: no spec" % (k, s, rw, cache)); continue
        elif rw != "none" and not rw.startswith("none"):
            print("%s s%d: rw=%s not understood: no spec" % (k, s, rw)); continue
        tr = os.path.join(a, "trim_%s.txt" % it)
        has_tr = os.path.exists(tr) and open(tr).read().strip()
        rel = os.path.relpath(out, R)
        shutil.copy(sz, os.path.join(out, "%s_sizes.vh" % k))
        if has_tr:
            shutil.copy(tr, os.path.join(out, "%s_trims.txt" % k))
        sdf = kv.get("sdf", "")
        task = os.path.relpath(d, os.path.dirname(os.path.dirname(d)))
        open(os.path.join(out, "%s.spec" % k), "w").write(
            "# %s seed %d, shipped route %s (farm results %s): rule CLEAN, PASS %s draws, bits EQUIVALENT, ffmux-clean;"
            " P=%s; rw=%s\nK=%s\nSEED=%s\nSIZES=%s/%s_sizes.vh\nTRIMS=%s\nMLIR=%s\nENV=%s\nSDF=%s\nFASM=00000000\n"
            % (k, s, re.search(r"route=(\S+)", last).group(1), task, kv.get("draws", "?"), kv.get("P", "NA"), rw, k, seed,
               rel, k, ("%s/%s_trims.txt" % (rel, k)) if has_tr else "-", mlir, env, sdf))
        print("%s s%d it %s seed %s%s%s -> %s.spec" % (k, s, it, seed, " ENV " + env if env else "",
                                                       " MLIR " + mlir if mlir != "-" else "", k))


if __name__ == "__main__":
    main()
