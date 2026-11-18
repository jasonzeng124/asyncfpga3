#!/usr/bin/env python3
"""ca_fast_check.py CORNER_DIR [--lines N] [--seed S] [--verify-like K] [--jobs J] [--old-jobs J] -- CA_FAST=1
against the old path, run for run, on one corner SDF.

CORNER_DIR is a corner_audit --out directory (soak.sdf, soak_routed.json beside it, as corner_audit writes them).
Runs the base spec (chain geometry and logs kept), N sensitivity specs (a sized line's chains at 0, the lines drawn
with seed S from every chain the route has; --lines all for every one) and K verify-like specs (several lines at
once, each at a fractional scale, as corner_audit's verify makes them), each twice: as before (a fresh
`corner_audit.py --_worker` process per spec, CA_FAST unset) and with CA_FAST=1 (the base run in this process, every
other spec a fork of it).  Every worker output is compared WHOLE: every constraint (rule, margin, knob, text), the
chain geometry, and the tighten / skew / arb_fork logs.  Prints one line per spec and the times; exit 1 on any
difference.  The guards are the sizing rule's (corner_audit defaults); set CA_SIZERULE / CA_JOINAWARE /
BD_SKEW_STEER_SELF / BD_SKEW_AND_JOIN in the environment as auto_size.sh does.  CA_OLD_TOOLS=<dir>: run the old
path from another checkout's research/tools (e.g. the commit before CA_FAST, extracted with git archive)."""
import argparse, json, os, random, re, subprocess, sys, time, pathlib

HERE = pathlib.Path(__file__).resolve().parent
TOOLS = HERE.parent
sys.path.insert(0, str(TOOLS))

ap = argparse.ArgumentParser()
ap.add_argument("corner_dir", type=pathlib.Path)
ap.add_argument("--lines", default="8")
ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--verify-like", type=int, default=2)
ap.add_argument("--jobs", type=int, default=1, help="CA_FAST forks at a time")
ap.add_argument("--old-jobs", type=int, default=1, help="old worker processes at a time")
ap.add_argument("--skip-old", action="store_true", help="time the fast path only")
a = ap.parse_args()
sdf = (a.corner_dir / "soak.sdf").resolve()
spec = {"a_frac": 0.03, "a_min": 50, "glo": 0.97, "ghi": 1.03, "drop_const": True, "rule_a_link": True,
        "osc": [], "cut": [], "drop": []}

os.environ["CA_FAST"] = "1"
import corner_audit as CA          # noqa: E402  (reads CA_FAST at import)
assert CA.FAST

t0 = time.time(); c0 = time.process_time()
base = json.loads(json.dumps(CA.worker(sdf, {**spec, "chains": True, "keep_logs": True})))
CA.BASE_ARB[:] = [base["arb_rc"], base["arb_log"]]
import ca_fast                     # noqa: E402
pool = ca_fast.Pool()
t_base, c_base = time.time() - t0, time.process_time() - c0
geo = base["chains"]
lines = {}
for b in geo:                      # chain base -> line, as corner_audit groups them (knob_of_base)
    lines.setdefault(CA.macro(CA.knob_of_base(b, {})), []).append(b)
macs = sorted(lines)
rng = random.Random(a.seed)
pick = macs if a.lines == "all" else sorted(rng.sample(macs, min(int(a.lines), len(macs))))
specs = [("sens " + m, {**spec, "scale": {b: 0.0 for b in lines[m]}}) for m in pick]
for k in range(a.verify_like):
    ms = rng.sample(macs, min(len(macs), 12))
    specs.append(("verify-like %d (%d lines)" % (k, len(ms)),
                  {**spec, "keep_logs": True,
                   "scale": {b: rng.choice([0.25, 0.5, 0.75, 1.5]) for m in ms for b in lines[m]}}))
t0 = time.time()
fast = pool.run(lambda s: CA.worker(sdf, s), [s for _, s in specs], jobs=a.jobs)
t_fast = time.time() - t0
print("route %s: %d lines; fast: base %.1f s wall (%.1f s cpu, in-process), %d forked runs %.1f s wall, %.1f s cpu"
      " (%.2f s cpu each)" % (a.corner_dir, len(macs), t_base, c_base, len(specs), t_fast, pool.cpu,
                              pool.cpu / max(1, len(specs))))
st = ca_fast.M.stats
print("memo (base run): " + ", ".join("%s %d" % kv for kv in sorted(st.items())))
if a.skip_old:
    sys.exit(0)


OLD_TOOLS = pathlib.Path(os.environ.get("CA_OLD_TOOLS") or TOOLS)   # another checkout's research/tools: the old path


def old(sp):
    env = {k: v for k, v in os.environ.items() if k != "CA_FAST"}
    return subprocess.Popen([sys.executable, str(OLD_TOOLS / "corner_audit.py"), "--_worker", str(sdf), json.dumps(sp)],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)


import resource                    # noqa: E402
ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
todo = [("base", {**spec, "chains": True, "keep_logs": True})] + specs
res, t0 = {}, time.time()
running = []
i = 0
while i < len(todo) or running:
    while i < len(todo) and len(running) < a.old_jobs:
        running.append((todo[i][0], time.time(), old(todo[i][1])))
        i += 1
    name, ts, p = running.pop(0)
    out, err = p.communicate()
    if p.returncode != 0:
        sys.exit("old worker failed on %s:\n%s" % (name, err[-2000:]))
    res[name] = (json.loads(out), time.time() - ts)
ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
cpu_old = (ru1.ru_utime - ru0.ru_utime) + (ru1.ru_stime - ru0.ru_stime)
t_old = time.time() - t0
bad = 0
for (name, _), new in zip([("base", None)] + specs, [base] + fast):
    o, dt = res[name]
    same = o == new
    nd = 0
    if not same:
        bad += 1
        ks = set(o["constraints"]) | set(new["constraints"])
        nd = sum(1 for k in ks if o["constraints"].get(k) != new["constraints"].get(k))
        other = [k for k in set(o) | set(new) if k != "constraints" and o.get(k) != new.get(k)]
    print("%-50s old %6.1f s  %s%s" % (name[:50], dt, "IDENTICAL" if same else "DIFFERENT",
                                       "" if same else " (%d constraint(s) differ; other keys %s)" % (nd, other)))
print("old: %d runs %.1f s wall, %.1f s cpu" % (len(todo), t_old, cpu_old))
print("RESULT %s: %d of %d runs differ" % ("PASS" if not bad else "FAIL", bad, len(todo)))
sys.exit(1 if bad else 0)
