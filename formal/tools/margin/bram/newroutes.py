#!/usr/bin/env python3
"""margin/bram/newroutes.py RS OUT_ROUTES [--ref origin/claude/cluster] [--nd 16] (shard C): research's automatic-suite
routes of MEMORY kernels (benchvec vectors under RS) that no margin/bram/routes_mem*.txt has judged yet, from the farm's
results/suite*/N/{result.txt,auto/result.txt,auto/sizes_<it>.vh} on the cluster branch: one routes line per route
(K SEED SIZES SDF8 NDRAWS HOSTPORT=1 [the search's env]), sizes copied to margin/bram/sizes/K_SEED_<sdf8>.vh. The latest
request per (kernel, seed, sdf) wins. Routes the farm did not build (no sdf=) are skipped. Feed OUT_ROUTES to a c_mem
request (c_mem5.sh shows the form)."""
import argparse, glob, os, re, subprocess, sys
ap = argparse.ArgumentParser(); ap.add_argument("rs"); ap.add_argument("out")
ap.add_argument("--ref", default="origin/claude/cluster"); ap.add_argument("--nd", type=int, default=16); a = ap.parse_args()
H = os.path.dirname(os.path.abspath(__file__)); R = os.path.abspath(os.path.join(H, "..", "..", "..", ".."))
git = lambda *x: subprocess.run(["git", "-C", R] + list(x), capture_output=True, text=True).stdout
def memk(k):
    for v in ("kernels/%s/vec.hex" % k, "research/data/suite/vec/%s.hex" % k):
        f = os.path.join(a.rs, v)
        if os.path.exists(f):
            return open(f).readline().startswith("// benchvec")
    return False
done = set()
for f in glob.glob(os.path.join(H, "routes_mem*.txt")):
    for l in open(f):
        t = l.split()
        if t and not l.startswith("#") and "NOCAP" not in l:
            done.add((t[0], t[1], t[3]))
files = [p for p in git("ls-tree", "-r", "--name-only", a.ref, "results/").split()
         if re.match(r"^results/(?!fm_)[^/]+/\d+/result\.txt$", p)]
rows = {}
for p in sorted(files, key=lambda p: (p.split("/")[1], int(p.split("/")[2]))):
    r = git("show", "%s:%s" % (a.ref, p)).strip().splitlines()
    if not r: continue
    t = r[-1].split()
    if len(t) < 2: continue
    k, s = t[0], t[1]
    m = re.search(r"\bsdf=([0-9a-f]{8})", r[-1])
    if not m or not memk(k): continue
    d = os.path.dirname(p)
    ar = git("show", "%s:%s/auto/result.txt" % (a.ref, d)).strip().splitlines()
    if not ar: continue
    mm = re.search(r"(?:route=|last route )su_\w+?_(\d+)\b", ar[-1])
    if not mm: continue
    it = mm.group(1)
    env = re.search(r"; search ([^)]*)\)", ar[-1])
    rows[(k, s, m.group(1))] = (d, it, env.group(1).strip() if env else "", re.search(r"status=(\S+)", r[-1]).group(1) if "status=" in r[-1] else "?")
out = ["# K SEED SIZES SDF8 NDRAWS [ENV...]  (newroutes.py from %s: memory routes no routes_mem*.txt has judged)" % a.ref]
for (k, s, sdf), (d, it, env, st) in sorted(rows.items()):
    if (k, s, sdf) in done: continue
    sz = os.path.join(H, "sizes", "%s_%s_%s.vh" % (k, s, sdf))
    txt = git("show", "%s:%s/auto/sizes_%s.vh" % (a.ref, d, it))
    if not txt: continue
    open(sz, "w").write(txt)
    out.append("%s %s %s %s %d HOSTPORT=1 %s  # research: %s (%s)" % (k, s, os.path.relpath(sz, R), sdf, a.nd, env, st, d))
open(a.out, "w").write("\n".join(out) + "\n")
print("newroutes: %d new memory routes -> %s" % (len(out) - 1, a.out), file=sys.stderr)
