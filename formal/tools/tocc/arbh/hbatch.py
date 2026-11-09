"""arbh adversarial batch (UNTRUSTED): pairs x corners x {mid, advH, advA, advO} x kappa {0, 0.44} -> hbatch.log"""
import sys, os, json, subprocess, math
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, "/tmp/claude-0/arbh")
from hchk import run
pairs = [(12, 18), (17, 5), (1071, 462), (0x49e9c618, 0x35bf992e)]
NW = int(os.environ.get("NW", "1"))
def sim(c, a, b, adv, tag):
    fn = "/tmp/claude-0/arbh/runs/h_%d_%d_c%d_%s.pkl" % (a, b, c, tag)
    if not os.path.exists(fn):
        subprocess.run(["python3", "/tmp/claude-0/arbh/simk.py", str(c), str(a), str(b)], env=dict(os.environ, ADV=json.dumps(adv), OUT=fn), stdout=subprocess.DEVNULL, check=True)
    return fn
jobs = []
for (a, b) in pairs:
    for c in (1, 0):
        S = json.load(open("/tmp/claude-0/arbh/advspec_c%d.json" % c))
        jobs.append((c, a, b, {}, "mid"))
        for m in ("advH", "advA", "advO"):
            for k in (0, 0.44): jobs.append((c, a, b, dict(S[m], kappa=k), "%s_k%s" % (m, k)))
with ThreadPoolExecutor(NW) as ex: fns = list(ex.map(lambda j: sim(*j), jobs))
for j, fn in zip(jobs, fns):
    c, a, b, _, tag = j
    r = run(fn, "/tmp/claude-0/arbh/runs/h_%d_%d_c%d_mid.pkl" % (a, b, c))
    print("(%d,%d) c=%d %-10s out %s want %d ok=%s timeout=%s hz=%d exact-count-diffs=%d latch-held-same=%s holdbad=%s D-changes %d (mid %d) min hold slack %s" % (
        a, b, c, tag, r["res"], math.gcd(a, b), r["ok"], r["timeout"], r["hz"], r["ndiff"], r["latch_same"], r["holdbad"], r["nD"], r["nD_ref"], r["minslack"]), flush=True)
