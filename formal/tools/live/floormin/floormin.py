#!/usr/bin/env python3
"""floormin.py OUT.tsv [FIXTURE...] -- is every stage research's token floor adds necessary?

For each fixture x {def, auto}: the links whose depth differs between BDC_TOKEN_FLOOR=1 and =0 (bdc's own Emitter,
../passdiff/depths.py). Then the floor-on design (control: must be LIVE), and once per added stage with that one link one
stage shorter (live.py's LIVE_DEPTH_OVERRIDE, applied to bdc's choice; 0 = unlinked): live.py exhaustively. NECESSARY = that minus-one deadlocks; SPARE = still LIVE (the floor over-asked there, in the model).
Untrusted (live.py's model, MODEL.md); LIVE_RS (default /home/user/rs) is research's tree."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
RS = os.environ.get("LIVE_RS", "/home/user/rs")
FIX = os.path.join(RS, "cloud/fixtures/frontend")
LIVE = os.path.join(HERE, "..", "fixtures", "live.py")
DEPTHS = os.path.join(HERE, "..", "passdiff", "depths.py")
FLOWS = {"def": {}, "auto": {"BDC_AUTO": "1"}}

def env_of(extra):
    env = {k: v for k, v in os.environ.items() if not k.startswith("BDC_")}
    env.update(extra, LIVE_BDC_DIR=os.path.join(RS, "bdc"), PYTHONDONTWRITEBYTECODE="1")
    return env

def depths(mlir, extra):
    p = subprocess.run([sys.executable, DEPTHS, mlir], env=env_of(extra), capture_output=True, text=True)
    return json.loads(p.stdout.strip().splitlines()[-1]) if p.returncode == 0 else None

def live(mlir, extra, maxs=3000000, timeout=1800):
    try:
        p = subprocess.run([sys.executable, LIVE, mlir, "--max-states", str(maxs)], env=env_of(extra),
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"verdict": "TIMEOUT"}
    ls = [l for l in p.stdout.splitlines() if l.startswith("{")]
    return json.loads(ls[-1]) if ls else {"verdict": "CRASH"}

def lname(ssa):
    # bdc's link instance names: %26 -> ulink_n26, %26#1 (key 26__1) -> ulink_n26__1, %trueResult_16 -> ulink_n_trueResult_16
    return "ulink_n" + ssa if ssa[:1].isdigit() else "ulink_n_" + ssa

out = open(sys.argv[1], "w")
fixtures = sys.argv[2:] or sorted(os.listdir(FIX))
fixtures = [f for f in fixtures if f not in os.environ.get("FLOORMIN_SKIP", "").split(",")]
for fx in fixtures:
    mlir = os.path.join(FIX, fx, "comp", "handshake_transformed.mlir")
    if not os.path.exists(mlir):
        continue
    for fl, fenv in FLOWS.items():
        on = depths(mlir, {**fenv})
        off = depths(mlir, {**fenv, "BDC_TOKEN_FLOOR": "0"})
        if on is None or off is None:
            continue
        add = {k: on[k] for k in on if on.get(k, 0) != off.get(k, 0)}
        if not add:
            continue
        pin = lambda d: ",".join(f"{lname(k)}={v}" for k, v in sorted(d.items()))
        ctl = live(mlir, {**fenv})
        row = [fx, fl, "control", pin(add), ctl.get("verdict"), str(ctl.get("states"))]
        print("\t".join(row), file=out, flush=True); print("\t".join(row), flush=True)
        for k in sorted(add):
            d = {k: add[k] - 1}
            r = live(mlir, {**fenv, "LIVE_DEPTH_OVERRIDE": f"{k}={d[k]}"})
            v = r.get("verdict")
            tag = "NECESSARY" if v == "DEADLOCK" else ("SPARE" if v == "LIVE" else "UNDECIDED")
            if ctl.get("verdict") != "LIVE":
                tag = "INVALID(control not LIVE)"
            row = [fx, fl, tag, f"{lname(k)} {add[k]}->{d[k]} (off: {off.get(k, 0)})", v, str(r.get("states"))]
            print("\t".join(row), file=out, flush=True); print("\t".join(row), flush=True)
