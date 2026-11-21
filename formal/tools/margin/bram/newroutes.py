#!/usr/bin/env python3
"""margin/bram/newroutes.py RS OUT_ROUTES [--ref origin/claude/cluster] [--nd 16] (shard C): research's automatic-suite
routes of MEMORY kernels (benchvec vectors under RS) that no margin/bram/routes_mem*.txt has judged yet, from the farm's
results/suite*/N/{result.txt,auto/result.txt,auto/sizes_<it>.vh} on the cluster branch: one routes line per route
(K SEED SIZES SDF8 NDRAWS HOSTPORT=1 [the search's env]), sizes copied to margin/bram/sizes/K_SEED_<sdf8>.vh. The latest
request per (kernel, seed, sdf) wins. Routes the farm did not build (no sdf=) are skipped. Feed OUT_ROUTES to a c_mem
request (c_mem5.sh shows the form)."""
import argparse, glob, hashlib, os, re, subprocess, sys
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
            done.add((t[0], t[1], t[3], "TRIM=" in l))      # a trimmed route keeps its SDF: judged apart from its build
files = [p for p in git("ls-tree", "-r", "--name-only", a.ref, "results/").split()
         if re.match(r"^results/(?!fm_)[^/]+/\d+/result\.txt$", p)]
_rf = {}
def rf0(req):
    """ " BDC_RING_FUSE=0" when the request built without ring fusion: its research commit predates flow v8 (no
    _RING_FUSE_DEFAULT in bdc/emit.py) or its request script exports BDC_RING_FUSE=0 (suite10d: v7 loops). Our builds
    run at research HEAD, where BDC_AUTO alone turns fusion on; the SAME / DIFFERENT sdf check catches a wrong guess."""
    if req not in _rf:
        c = re.search(r"^commit\s+(\S+)", git("show", "%s:results/%s/status.txt" % (a.ref, req)), re.M)
        c = c.group(1) if c else ""
        rg = lambda x: subprocess.run(["git", "-C", a.rs] + x, capture_output=True, text=True).stdout
        em = rg(["show", "%s:bdc/emit.py" % c]) if c else ""
        if c and not em:                      # commit not in RS: refuse rather than guess "before v8"
            sys.exit("newroutes: research commit %s (request %s) not in %s: git fetch there first" % (c, req, a.rs))
        old = c and "_RING_FUSE_DEFAULT" not in em
        sc = rg(["show", "%s:research/cluster/requests/%s.sh" % (c, req)]) if c else ""
        fx = re.search(r"cloud/fixtures/(\w+)/\$K/comp", sc)   # exit1: the request swaps in another fixture's MLIR
        _rf[req] = (" BDC_RING_FUSE=0" if (old or re.search(r"\bBDC_RING_FUSE=0\b", sc)) else "") + \
                   (" FIXTURES=" + fx.group(1) if fx and fx.group(1) != "frontend" else "")
    return _rf[req]
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
    # NOT CLEAN searches ship the least-short iteration ("shipped it=N"), not the last route
    mm = re.search(r"shipped it=(\d+)", ar[-1]) or re.search(r"(?:route=|last route )su_\w+?_(\d+)\b", ar[-1])
    if not mm: continue
    it = mm.group(1)
    env = re.search(r"; search ([^)]*)\)", ar[-1])
    # an alternate-seed finish (finseeds DA arm: "alt it N seed X su_.. <sdf8>") placed with seed X, not SEED; and the
    # loop's own record of the shipped iteration's placer seed (auto/seed_<it>.txt: e.g. 104 for kernel seed 4 when the
    # loop re-seeded), which an alt line does not cover
    alt = re.search(r"^alt it \d+ seed (\d+) \S+ %s\b" % m.group(1), git("show", "%s:%s/task.txt" % (a.ref, d)), re.M)
    if not alt:
        sd = git("show", "%s:%s/auto/seed_%s.txt" % (a.ref, d, it)).split()
        if sd and sd[0].isdigit() and sd[0] != s:
            alt = re.match(r"(\d+)", sd[0])
    # which fixture the task built from: task.txt's md5 of build/frontend/K/comp/handshake_transformed.mlir (exit1,
    # suite13t, mixed reruns) against each cloud/fixtures/<dir>/K copy in RS -- per task, not per request
    fxt = None
    mt = re.search(r"\b([0-9a-f]{32})\s+build/frontend/%s/comp/handshake_transformed\.mlir" % re.escape(k),
                   git("show", "%s:%s/task.txt" % (a.ref, d)))
    if mt:
        for fd in sorted(glob.glob(os.path.join(a.rs, "cloud", "fixtures", "*", k, "comp", "handshake_transformed.mlir"))):
            if hashlib.md5(open(fd, "rb").read()).hexdigest() == mt.group(1):
                fxt = fd.split(os.sep)[-4]; break
    # AUTO_TRIM (research's suite13t on): auto/trim_<it>.txt is the shipped route's MACRO=LEN record; the SDF does not change
    tr = git("show", "%s:%s/auto/trim_%s.txt" % (a.ref, d, it)).strip()
    trf = ""
    if tr:
        trf = os.path.join(H, "trims", "%s_%s_%s.txt" % (k, s, m.group(1))); os.makedirs(os.path.dirname(trf), exist_ok=True)
        open(trf, "w").write(tr + "\n"); trf = " TRIM=" + os.path.relpath(trf, R)
    rq = rf0(d.split("/")[1])
    if fxt is not None:   # the task's own md5 decides FIXTURES (the request-level guess is dropped)
        rq = re.sub(r" FIXTURES=\S+", "", rq) + (" FIXTURES=" + fxt if fxt != "frontend" else "")
    rows[(k, s, m.group(1))] = (d, it, (env.group(1).strip() if env else "") + rq
                                + (" PNR_SEED=" + alt.group(1) if alt else "") + trf, re.search(r"status=(\S+)", r[-1]).group(1) if "status=" in r[-1] else "?")
out = ["# K SEED SIZES SDF8 NDRAWS [ENV...]  (newroutes.py from %s: memory routes no routes_mem*.txt has judged)" % a.ref]
for (k, s, sdf), (d, it, env, st) in sorted(rows.items()):
    if (k, s, sdf, " TRIM=" in env) in done: continue
    sz = os.path.join(H, "sizes", "%s_%s_%s.vh" % (k, s, sdf))
    txt = git("show", "%s:%s/auto/sizes_%s.vh" % (a.ref, d, it))
    if not txt: continue
    open(sz, "w").write(txt)
    out.append("%s %s %s %s %d HOSTPORT=1 %s  # research: %s (%s)" % (k, s, os.path.relpath(sz, R), sdf, a.nd, env, st, d))
open(a.out, "w").write("\n".join(out) + "\n")
print("newroutes: %d new memory routes -> %s" % (len(out) - 1, a.out), file=sys.stderr)
