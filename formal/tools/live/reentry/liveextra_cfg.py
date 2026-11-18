#!/usr/bin/env python3
"""liveextra_cfg.py -- live.py (exhaustive, floor on, default flow) on sweep.EXTRA (fixes and non-fixes of matrix /
stencil_2d); appends to live_cfg.jsonl."""
import json, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep
HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(HERE, "live_cfg.jsonl"), "a") as f:
    for fx, label, ev in sweep.EXTRA:
        mlir = os.path.join(sweep.FIX, fx, "comp", "handshake_transformed.mlir")
        p = subprocess.run([sys.executable, "-B", os.path.join(HERE, "../fixtures/live.py"), mlir, "--inv", "1",
                            "--max-states", "1500000"], env=sweep.env_for(ev), capture_output=True, text=True, timeout=900)
        l = [x for x in p.stdout.splitlines() if x.startswith("{")]
        r = json.loads(l[-1]) if l else {"verdict": "CRASH"}
        r.update(fixture=fx, label=label, env=ev)
        f.write(json.dumps(r) + "\n"); f.flush()
        print(fx, label, r["verdict"], r.get("states"), r.get("trap"), flush=True)
