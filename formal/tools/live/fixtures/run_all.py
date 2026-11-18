#!/usr/bin/env python3
"""run_all.py OUTDIR -- live.py and research's ring_tokens.py over every fixture x flow x floor, plus the validation
configurations; writes OUTDIR/results.jsonl, OUTDIR/validation.jsonl, OUTDIR/RESULTS.md, OUTDIR/graphs/*.json.

Each (fixture, flow, floor) runs in its own process (emit.py reads BDC_* at import).  At most LIVE_JOBS (2) at once,
each capped at LIVE_MEM_GB (2.5) of address space and LIVE_TIMEOUT (900) seconds.
"""
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
RS = os.environ.get("LIVE_RS", "/home/user/rs")
FIX = os.environ.get("LIVE_FIXTURES", os.path.join(RS, "cloud/fixtures/frontend"))
JOBS = int(os.environ.get("LIVE_JOBS", "2"))
TIMEOUT = int(os.environ.get("LIVE_TIMEOUT", "420"))
MAXSTATES = os.environ.get("LIVE_MAX_STATES", "2000000")
INV2_MAX = int(os.environ.get("LIVE_INV2_MAX", "100000"))   # run a 2-invocation search when the 1-invocation one is under this
RING = os.path.join(RS, "research/tools/suite/ring_tokens.py")

FLOWS = {"def": {}, "auto": {"BDC_AUTO": "1"}, "autorw": {"BDC_AUTO": "1"}}
FLOORS = {"on": {}, "off": {"BDC_TOKEN_FLOOR": "0"}}


def base_env(extra):
    env = {k: v for k, v in os.environ.items() if not k.startswith("BDC_")}
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["LIVE_BDC_DIR"] = os.path.join(RS, "bdc")
    env.update(extra)
    return env


def run_live(mlir, env, tag, out, inv=1, extra=()):
    cmd = [sys.executable, os.path.join(HERE, "live.py"), mlir, "--inv", str(inv), "--max-states", MAXSTATES,
           "--json-dir", os.path.join(out, "graphs"), "--tag", tag] + list(extra)
    try:
        p = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
        if lines:
            return json.loads(lines[-1])
        return {"verdict": "CRASH", "error": (p.stderr.strip().splitlines() or ["?"])[-1][:300]}
    except subprocess.TimeoutExpired:
        return {"verdict": "TIMEOUT"}


def run_ring(mlir, env):
    try:
        p = subprocess.run([sys.executable, RING, mlir], env=env, capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return "timeout"
    o = p.stdout
    if "walks: every walk holds a token" in o:
        w = "live"
    elif "walks: a walk holds" in o:
        w = "short(" + o.split("walks: a walk holds ")[1].split(" ")[0] + ")"
    else:
        w = "refused" if "EmitError" in p.stderr or "Error" in p.stderr else "?"
    return w


def mlir_for(fix, flow, out):
    src = os.path.join(FIX, fix, "comp", "handshake_transformed.mlir")
    if flow != "autorw":
        return src
    dst = os.path.join(out, "mlir", fix + ".rw.mlir")
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if not os.path.exists(dst):
        subprocess.run([sys.executable, os.path.join(RS, "bdc", "auto.py"), src, dst], env=base_env({}),
                       capture_output=True, text=True)
    return dst


def one(job):
    fix, flow, floor, out = job
    mlir = mlir_for(fix, flow, out)
    if flow == "autorw" and open(mlir, "rb").read() == open(mlir_for(fix, "auto", out), "rb").read():
        r = {"verdict": "SAME-AS-AUTO", "fixture": fix, "flow": flow, "floor": floor, "research": "-"}
        print(f"{fix}.{flow}.{floor}: auto.py rewrote nothing (same MLIR as auto)", flush=True)
        return r
    env = base_env({**FLOWS[flow], **FLOORS[floor]})
    tag = f"{fix}.{flow}.{floor}"
    r = run_live(mlir, env, tag, out)
    if r.get("verdict") in ("BLOWUP", "BLOWUP-MEM", "TIMEOUT"):
        rr = run_live(mlir, env, tag + ".rand", out, extra=["--random", "300", "--steps", "100000"])
        r["exhaustive"] = r.get("verdict")
        r["verdict"] = rr.get("verdict")
        r["walks"] = rr.get("walks")
        r["z_checked"], r["z_traps"] = rr.get("z_checked"), rr.get("z_traps")
        for k in ("trace_choices", "trap"):
            if k in rr:
                r[k] = rr[k]
    if r.get("verdict") == "LIVE" and r.get("states", 1 << 30) < INV2_MAX:
        r2 = run_live(mlir, env, tag + ".inv2", out, inv=2)
        r["inv2"] = r2.get("verdict")
        r["inv2_states"] = r2.get("states")
        if r2.get("verdict") == "DEADLOCK":
            r["inv2_trace"] = r2.get("trace_choices")
            r["inv2_trap"] = r2.get("trap")
    r["research"] = run_ring(mlir, env) if r.get("verdict") not in ("REFUSED",) else "refused"
    r.update(fixture=fix, flow=flow, floor=floor)
    print(f"{tag}: {r.get('verdict')} states={r.get('states')} research={r['research']} inv2={r.get('inv2')}",
          flush=True)
    return r


def main():
    out = os.path.abspath(sys.argv[1])
    os.makedirs(os.path.join(out, "graphs"), exist_ok=True)
    fixtures = sorted(d for d in os.listdir(FIX) if os.path.exists(os.path.join(FIX, d, "comp",
                                                                                 "handshake_transformed.mlir")))
    only = os.environ.get("LIVE_ONLY")
    if only:
        fixtures = [f for f in fixtures if f in only.split(",")]
    done = set()
    if os.path.exists(os.path.join(out, "results.jsonl")):
        for l in open(os.path.join(out, "results.jsonl")):
            d_ = json.loads(l)
            done.add((d_["fixture"], d_["flow"], d_["floor"]))
    jobs = [(f, fl, fo, out) for f in fixtures for fl in FLOWS for fo in FLOORS if (f, fl, fo) not in done]
    res = []
    with ThreadPoolExecutor(JOBS) as ex:
        for r in ex.map(one, jobs):
            res.append(r)
            with open(os.path.join(out, "results.jsonl"), "a") as fh:
                fh.write(json.dumps(r) + "\n")


if __name__ == "__main__":
    main()
