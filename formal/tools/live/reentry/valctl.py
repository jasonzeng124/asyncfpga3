#!/usr/bin/env python3
"""valctl.py OUT.jsonl -- reentry.py on formal's 34 validation configurations (fixtures/validation.jsonl: research's
quadrec / lfsrfind / nested / nest3 rows, floor off and on), next to live.py's verdict there."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep
HERE = os.path.dirname(os.path.abspath(__file__))
with open(sys.argv[1], "a") as f:
    for l in open(os.path.join(HERE, "../fixtures/validation.jsonl")):
        v = json.loads(l)
        fx = v["config"].split()[0]
        r = sweep.run(fx, "auto" if v["env"].get("BDC_AUTO") else "def", v["config"], v["env"])
        r["live"] = v["verdict"]
        f.write(json.dumps(r) + "\n"); f.flush()
        print(v["config"], r["live"], r["reentry"], flush=True)
