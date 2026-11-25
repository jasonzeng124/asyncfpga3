#!/usr/bin/env python3
"""passdiff.py [OUT.tsv] -- for every fixture and flow (def, auto): the links whose depth differs between
BDC_TOKEN_FLOOR_PASS=1 (research's pass-through modes, default) and =0.  Untrusted helper; reads bdc's Emitter."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
RS = os.environ.get("LIVE_RS", "/home/user/rs")
FIX = os.path.join(RS, "cloud/fixtures/frontend")
FLOWS = {"def": {}, "auto": {"BDC_AUTO": "1"}}

def depths(mlir, extra):
    env = {k: v for k, v in os.environ.items() if not k.startswith("BDC_")}
    env.update(extra, LIVE_BDC_DIR=os.path.join(RS, "bdc"), PYTHONDONTWRITEBYTECODE="1")
    p = subprocess.run([sys.executable, os.path.join(HERE, "depths.py"), mlir], env=env, capture_output=True, text=True)
    if p.returncode:
        return None
    return json.loads(p.stdout.strip().splitlines()[-1])

rows = []
for fx in sorted(os.listdir(FIX)):
    mlir = os.path.join(FIX, fx, "comp", "handshake_transformed.mlir")
    if not os.path.exists(mlir):
        continue
    for fl, env in FLOWS.items():
        a = depths(mlir, {**env, "BDC_TOKEN_FLOOR_PASS": "1"})
        b = depths(mlir, {**env, "BDC_TOKEN_FLOOR_PASS": "0"})
        if a is None or b is None:
            rows.append((fx, fl, "refused", ""))
            continue
        d = {k: (b.get(k, 0), a.get(k, 0)) for k in set(a) | set(b) if a.get(k, 0) != b.get(k, 0)}
        rows.append((fx, fl, "same" if not d else "added", " ".join(f"{k}:{x}->{y}" for k, (x, y) in sorted(d.items()))))
out = open(sys.argv[1], "w") if len(sys.argv) > 1 else sys.stdout
for r in rows:
    print("\t".join(r), file=out)
