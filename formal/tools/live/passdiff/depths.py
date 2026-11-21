#!/usr/bin/env python3
"""depths.py MLIR -- print bdc's linked channels and depths as JSON ({ssa: depth}) for the BDC_* env it runs under.
Reads bdc's own Emitter (LIVE_BDC_DIR, default /home/user/rs/bdc).  Used by passdiff.py."""
import json, os, sys
BDC = os.environ.get("LIVE_BDC_DIR", "/home/user/rs/bdc")
sys.path.insert(0, BDC); sys.dont_write_bytecode = True
import emit  # noqa: E402
from hs import parse  # noqa: E402
func = [f for f in parse.parse_module(open(sys.argv[1]).read(), filename=sys.argv[1]) if not f.is_declaration][0]
e = emit.Emitter(func)
print(json.dumps({s: e.depth.get(s, 1) for s in sorted(e.linked)}))
