#!/usr/bin/env python3
"""margin/margin.py (shard C, UNTRUSTED search): single-pin adversary sweep + per-race kappa bisection.

    python3 margin.py NET.json BND.json RANKED.json OUTDIR [--jobs J] [--top N] [--khi 0.45] [--klo 0.20]
                      [--pairs P ...] [--w 20] [--w0] [--tmax-factor 1.3]

Adversary (as tools-B/ps/ctlsweep.py, tools/huff/simadv.py --classes): corner 0, g = 1, kappa = P/100 exactly; the
candidate's route (q's arc on pin i + the copy-chain hops into it) at floor((1+k) FAST_MAX), every other arc of the
circuit at ceil((1-k) FAST_MIN); LUT pins >= w ps when --w (H_RUNT(w)). Sequential env, broad data release, reset
400 ns. One run per (candidate, kappa) with all --pairs in sequence; FAIL = wrong or missing out0 by tmax (tmax =
tmax-factor x the reference run's end at the same kappa; a FAIL is re-run with the full 5 us before it is reported).
Phase 1: every candidate (in RANKED order, first --top) at khi. Phase 2: each failing candidate bisected on the
0.01 grid in (klo, khi]: kappa_fail = smallest grid kappa that fails, assuming failure is monotone in kappa between
the bracket ends (checked only at the ends; NOT a theorem). Phase 3 (--w0): the same bisection without H_RUNT for
the races found. Writes OUTDIR/sweep_w*.txt (one line per run, resumable), margins.txt, summary.txt and, for the
binding race, OUTDIR/witness/ (classes JSON, command, result, dump) at kappa_fail.
"""
import argparse, json, os, resource, subprocess, sys, time, threading
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
SIM = os.path.join(HERE, "..", "huff", "simadv.py")
ap = argparse.ArgumentParser()
ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("ranked"); ap.add_argument("out")
ap.add_argument("--jobs", type=int, default=2); ap.add_argument("--top", type=int, default=0)
ap.add_argument("--khi", type=float, default=0.45); ap.add_argument("--klo", type=float, default=0.20)
ap.add_argument("--pairs", nargs="+", default=["0x49e9c618,0x35bf992e", "1071,462"])
ap.add_argument("--w", type=int, default=20); ap.add_argument("--w0", action="store_true")
ap.add_argument("--tmax-factor", type=float, default=1.3); ap.add_argument("--tfull", type=int, default=5_000_000)
ap.add_argument("--arbs", default=None, help="arbs.json: rows whose q is an arbiter state LUT are flagged (ArbOK unchecked)")
ap.add_argument("--memcap", type=float, default=3.0, help="GB address-space cap per simulation")
ap.add_argument("--wallcap", type=int, default=900, help="s per simulation")
ap.add_argument("--only", nargs="*", default=None, help="node:pin keys to restrict to (tests)")
a = ap.parse_args()
KD = 100
os.makedirs(a.out, exist_ok=True); TMP = os.path.join(a.out, "tmp"); os.makedirs(TMP, exist_ok=True)
R = json.load(open(a.ranked))
if a.only: R = [r for r in R if "%s:%d" % (r["node"], r["pin"]) in set(a.only)]
R = [r for r in R if r.get("kre", 0) < 2]          # q and pin i active in some reference run
if a.top: R = R[:a.top]
LOG = open(os.path.join(a.out, "log.txt"), "a")
def log(*x):
    s = time.strftime("%H:%M:%S ") + " ".join(str(y) for y in x); print(s, flush=True); LOG.write(s + "\n"); LOG.flush()

def sim(arcs, P, w, tmax, tag, dump=None):
    cf = os.path.join(TMP, "c_%s.json" % tag)
    json.dump({"S": arcs, "F": []}, open(cf, "w"))
    cmd = ["python3", SIM, a.net, a.bnd, "--pairs", *a.pairs, "--corner", "0", "--kappa", "%.2f" % (P / KD),
           "--classes", cf, "--cdefault", "F", "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", str(tmax)] + (["--w", str(w)] if w else [])
    if dump: cmd += ["--dump", dump]
    t0 = time.time()
    cap = int(a.memcap * 2**30)
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, KDEN=str(KD)), timeout=a.wallcap,
                           preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (cap, cap)))
    except subprocess.TimeoutExpired:
        return ("ERROR", 0, 0, time.time() - t0, "TIMEOUT after %d s" % a.wallcap, cmd, cf)
    res = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
    st = [l for l in r.stderr.splitlines() if l.startswith("sim:") and "events" in l]
    ev = tend = 0
    if st:
        f = st[-1].split(); ev = int(f[1]); tend = int(f[5])
    if not res: return ("ERROR", 0, 0, time.time() - t0, ("MemoryError(cap %.1f GB)" % a.memcap if "MemoryError" in r.stderr else "") + r.stderr[-200:].replace("\n", " "), cmd, cf)
    return ("OK" if res[0].startswith("RESULT OK") else "FAIL", ev, tend, time.time() - t0, res[0], cmd, cf)

# reference runs (no slow arcs) -> tmax per (kappa, w)
TM = {}; TML = threading.Lock()
def tmax_for(P, w):
  with TML:
    if (P, w) not in TM:
        v = sim([], P, w, a.tfull, "ref_%d_%d" % (P, w))
        if v[0] != "OK": log("REFERENCE RUN FAILS at kappa %.2f w %d: %s" % (P / KD, w, v[4])); TM[(P, w)] = a.tfull
        else: TM[(P, w)] = int(v[2] * a.tmax_factor); log("ref k=%.2f w=%d: %d events, end %d ps, %.1f s -> tmax %d" % (P / KD, w, v[1], v[2], v[3], TM[(P, w)]))
  return TM[(P, w)]

def verdict(r, P, w, store):
    """one (candidate, kappa) verdict; cached in store; FAIL re-run with tfull."""
    key = "%s %d %d %d" % (r["node"], r["pin"], P, w)
    if key in store: return store[key]
    tag = "%s_%d_%d_%d" % (r["node"].replace("/", "_"), r["pin"], P, w)
    tm = tmax_for(P, w)
    v = sim(r["arcs"], P, w, tm, tag)
    if v[0] == "FAIL" and v[2] > tm and tm < a.tfull:
        tm = a.tfull; v = sim(r["arcs"], P, w, tm, tag)   # cut at the short tmax: confirm with the full one
    kind = v[0] if v[0] != "ERROR" else "UNDECIDED"   # memory/time cap hit (typically a runt livelock); counted as failing
    if kind == "FAIL":   # wrong value / ended quiet with an answer missing / still active at tmax (livelock?)
        kind = "FAIL-quiet" if v[2] <= tm else "FAIL-noanswer"
        if "got []" not in v[4]: kind = "FAIL-wrong"
    line = "%s %s events %d tend %d %.1fs | %s" % (key, kind, v[1], v[2], v[3], v[4])
    store[key] = kind
    with open(os.path.join(a.out, "sweep_w%d.txt" % w), "a") as f: f.write(line + "\n")
    if kind != "OK": log(line)
    return kind

def load(w):
    st = {}
    p = os.path.join(a.out, "sweep_w%d.txt" % w)
    if os.path.exists(p):
        for l in open(p):
            f = l.split()
            if len(f) > 4 and f[4] != "ERROR": st[" ".join(f[:4])] = f[4]
    return st

def bisect_quiet(r, w, store, lo, hi):
    """smallest grid kappa in [lo, hi] whose run ends quiet with no answer (a finite witness), or None"""
    if verdict(r, hi, w, store) != "FAIL-quiet": return None
    lo -= 1
    while hi - lo > 1:
        m = (lo + hi) // 2
        if verdict(r, m, w, store) == "FAIL-quiet": hi = m
        else: lo = m
    return hi

def bisect(r, w, store, Phi):
    lo, hi = round(a.klo * KD), Phi          # invariant: verdict(hi) fails; lo untested or passes
    if verdict(r, lo, w, store) != "OK": return lo, "fails already at klo"
    while hi - lo > 1:
        m = (lo + hi) // 2
        if verdict(r, m, w, store) != "OK": hi = m
        else: lo = m
    return hi, ""

ARBQ = {x["q"] for x in json.load(open(a.arbs))} if a.arbs else set()
Phi = round(a.khi * KD)
t0 = time.time()
rows = []
for w in ([a.w] + ([0] if a.w0 and a.w else [])):
    store = load(w)
    tmax_for(Phi, w); tmax_for(round(a.klo * KD), w)
    if w == a.w:
        log("phase 1: %d candidates at kappa %.2f, w %d, %d jobs" % (len(R), a.khi, w, a.jobs))
        with ThreadPoolExecutor(a.jobs) as ex:
            v1 = list(ex.map(lambda r: verdict(r, Phi, w, store), R))
        fails = [r for r, v in zip(R, v1) if v != "OK"]
        log("phase 1 done: %d of %d fail at %.2f (%.0f s)" % (len(fails), len(R), a.khi, time.time() - t0))
    else:
        fails = [r for r in fails]
        with ThreadPoolExecutor(a.jobs) as ex:
            list(ex.map(lambda r: verdict(r, Phi, w, store), fails))
    with ThreadPoolExecutor(a.jobs) as ex:
        res = list(ex.map(lambda r: (r, bisect(r, w, store, Phi) if store["%s %d %d %d" % (r["node"], r["pin"], Phi, w)] != "OK" else (None, "passes at khi")), fails))
    with ThreadPoolExecutor(a.jobs) as ex:
        qs = list(ex.map(lambda x: bisect_quiet(x[0], w, store, x[1][0], Phi) if x[1][0] is not None else None, res))
    for (r, (Pf, note)), Pq in zip(res, qs):
        if r["node"] in ARBQ: note = (note + " " if note else "") + "ARBITER-STATE(ArbOK unchecked: may be excluded by H_ARB)"
        rows.append(dict(w=w, node=r["node"], pin=r["pin"], src=r["src"], name=r["name"], latch=r["latch"],
                         kquiet=(Pq / KD if Pq is not None else None),
                         kfail=(Pf / KD if Pf is not None else None), note=note,
                         kind=store.get("%s %d %d %d" % (r["node"], r["pin"], Pf, w)) if Pf is not None else "OK",
                         kre=r.get("kre"), arcs=r["arcs"]))
    log("w=%d bisection done (%.0f s)" % (w, time.time() - t0))

# report
with open(os.path.join(a.out, "margins.txt"), "w") as f:
    f.write("# single-pin races that fail (simulation, UNTRUSTED search; corner 0, g = 1); pairs: %s\n" % " ".join(a.pairs))
    f.write("# swept: %d candidates (storage gate q, live pin i) at kappa %.2f, w = %d; others: none found up to %.2f\n" % (len(R), a.khi, a.w, a.khi))
    f.write("# w  node pin  source(fork)  kappa_fail  kind(at kappa_fail)  kappa_quiet(first quiet deadlock: finite witness)  note  route(arcs)  [kappa_fail = smallest failing 0.01-grid kappa in (%.2f, %.2f]]\n" % (a.klo, a.khi))
    for x in sorted(rows, key=lambda x: (x["w"], x["kfail"] if x["kfail"] is not None else 9)):
        f.write("w=%-2d %s %d %s %s %s %s %s %s\n" % (x["w"], x["node"], x["pin"], x["src"],
                "%.2f" % x["kfail"] if x["kfail"] is not None else "none<=%.2f" % a.khi, x["kind"],
                "quiet@%.2f" % x["kquiet"] if x.get("kquiet") is not None else "quiet:none<=%.2f" % a.khi, (x["note"] or "-").replace(" ", "_"),
                ",".join("%s/%d" % (n, p) for n, p in x["arcs"])))
summ = []
for w in sorted({x["w"] for x in rows} | {a.w}, reverse=True):
    rw = [x for x in rows if x["w"] == w and x["kfail"] is not None]
    if not rw:
        summ.append("w=%d: kappa* > %.2f (no single-pin race of the %d swept fails at %.2f)" % (w, a.khi, len(R), a.khi)); continue
    rn = [x for x in rw if "ARBITER" not in x["note"]] or rw
    b = min(rn, key=lambda x: x["kfail"])
    for x in rw:
        if "ARBITER" in x["note"] and x["kfail"] < b["kfail"]:
            summ.append("w=%d: NOTE arbiter-state row %s pin %d fails at %.2f (%s): not a behaviour unless ArbOK holds; not checked" % (w, x["node"], x["pin"], x["kfail"], x["kind"]))
    summ.append("w=%d: kappa* = %.2f (search, untrusted)  race: %s pin %d (cell %s) slow route from %s; kind %s; %d races fail <= %.2f"
                % (w, b["kfail"], b["node"], b["pin"], b["name"], b["src"], b["kind"], len(rw), a.khi))
    if b.get("kquiet") is not None: summ.append("  first quiet (finite) failure of that race: kappa %.2f" % b["kquiet"])
    if w == a.w:   # the witness: at kappa_fail (command + verdict) and, if any, at the first quiet kappa (with dump)
        wd = os.path.join(a.out, "witness"); os.makedirs(wd, exist_ok=True)
        json.dump({"S": b["arcs"], "F": []}, open(os.path.join(wd, "classes.json"), "w"))
        with open(os.path.join(wd, "command.txt"), "w") as f:
            for P, dump in ((round(b["kfail"] * KD), None),) + (((round(b["kquiet"] * KD), os.path.join(wd, "dump_quiet.json")),) if b.get("kquiet") is not None else ()):
                v = sim(b["arcs"], P, w, a.tfull, "witness", dump=dump)
                f.write("# kappa %.2f w %d: %s (events %d, end %d ps)\nKDEN=100 %s\n" % (P / KD, w, v[4], v[1], v[2], " ".join(v[5]).replace(v[6], "classes.json")))
                if dump: subprocess.run(["xz", "-f", dump])
                summ.append("  witness kappa %.2f w %d: %s (%s/witness/)" % (P / KD, w, v[4], a.out))
summ.append("wall %.0f s, %d jobs" % (time.time() - t0, a.jobs))
open(os.path.join(a.out, "summary.txt"), "w").write("\n".join(summ) + "\n")
print("\n".join(summ))
