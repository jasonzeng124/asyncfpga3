"""adversarial batch (UNTRUSTED): pairs x corners x {adv (race 1: A-only past hi, B-only past lo), adv2 (+ {A,B}->reader-open
paths lo, D paths hi)} x kappa {0, 0.44}; compares with the mid run of the same pair: gcd, hazchk, exact event counts,
reader-latch held values, X22Y81.B5 changes read while a reader is transparent."""
import sys, os, json, pickle, subprocess, math
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, "/tmp/claude-0/arbh")
from chk import run, captures, dchg_open, ev
pairs = [(12, 18), (17, 5), (1071, 462), (0x49e9c618, 0x35bf992e), (0x80000000, 0x40000000), (3280387012, 271041745)]
def sim(c, a, b, adv, tag):
    fn = "/tmp/claude-0/arbh/runs/b_%d_%d_c%d_%s.pkl" % (a, b, c, tag)
    if not os.path.exists(fn):
        subprocess.run(["python3", "/tmp/claude-0/arbh/simk.py", str(c), str(a), str(b)], env=dict(os.environ, ADV=json.dumps(adv), OUT=fn), stdout=subprocess.DEVNULL, check=True)
    return fn
jobs = []
for (a, b) in pairs:
    for c in (1, 0):
        S1 = json.load(open("/tmp/claude-0/arbh/sets_c%d.json" % c)); S2 = json.load(open("/tmp/claude-0/arbh/sets2_c%d.json" % c))
        jobs.append((c, a, b, {}, "mid"))
        for k in (0, 0.44):
            jobs.append((c, a, b, dict(hiG=S1["hiG"], loG=S1["loG"], kappa=k), "adv_k%s" % k))
            jobs.append((c, a, b, dict(S2, kappa=k), "adv2_k%s" % k))
with ThreadPoolExecutor(2) as ex: fns = list(ex.map(lambda j: sim(*j), jobs))
for j, fn in zip(jobs, fns):
    c, a, b, _, tag = j
    ref = "/tmp/claude-0/arbh/runs/b_%d_%d_c%d_mid.pkl" % (a, b, c)
    r = run(fn, ref); H = pickle.load(open(fn, "rb")); R = pickle.load(open(ref, "rb"))
    capok = captures(H) == captures(R); do = dchg_open(H)
    nA = len(ev(H, "SLICE_X22Y87.A6")); nB = len(ev(H, "SLICE_X27Y80.A6"))
    # every iteration: order of A_i = X22Y87.A6(2i) vs B_i = X27Y80.A6(2i+2)
    sk = [ev(H, "SLICE_X22Y87.A6")[2 * i] - ev(H, "SLICE_X27Y80.A6")[2 * i + 2] for i in range(min(nA // 2, nB // 2 - 1))]
    print("(%d,%d) c=%d %-9s out %s want %d timeout=%s hz=%d exact-count-diffs=%d reader-held-values-same=%s B5-changes %d, read-while-transparent %s | A-B skew per iteration: max %s min %s (#A after B: %d/%d)" % (
        a, b, c, tag, r["res"], math.gcd(a, b), H["tend"] > 49_000_000, r["hz"], r["ndiff"], capok, len(ev(H, "SLICE_X22Y81.B5")), do[:3],
        max(sk) if sk else None, min(sk) if sk else None, sum(1 for x in sk if x > 0), len(sk)), flush=True)
