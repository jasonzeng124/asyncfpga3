#!/usr/bin/env python3
"""flooroff.py OUT.jsonl -- reentry.py with the floor OFF (BDC_TOKEN_FLOOR=0) on every fixture x {def, auto} that
live.py has a floor-off verdict for in fixtures/results.jsonl (a harder test: research's floor not applied)."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep
HERE = os.path.dirname(os.path.abspath(__file__))
with open(sys.argv[1], "a") as f:
    for l in open(os.path.join(HERE, "../fixtures/results.jsonl")):
        v = json.loads(l)
        if v.get("floor") != "off" or v["flow"] not in ("def", "auto") or v["verdict"] in ("REFUSED", "CRASH"):
            continue
        ev = {"BDC_TOKEN_FLOOR": "0"}
        if v["flow"] == "auto":
            ev["BDC_AUTO"] = "1"
        r = sweep.run(v["fixture"], v["flow"], "floor off", ev)
        r["live"] = v["verdict"]
        f.write(json.dumps(r) + "\n"); f.flush()
        print(v["fixture"], v["flow"], r["live"], r["reentry"], "iter" if r.get("iterating_short") else "", flush=True)
