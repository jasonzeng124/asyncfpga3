#!/usr/bin/env python3
"""nextpnr --post-route wrapper: run BOTH post-route signoffs on one
routed netlist -- tests/postroute_audit.py (async bundling margins in
the clockless core) and fomu/sync_timing_check.py (48 MHz closure of
the genuinely synchronous logic: USB-CDC core + harness glue, with
false paths through the async core cut). Fails if either fails.
"""
import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
_failed = []
for _script in (os.path.join(_here, "sync_timing_check.py"),
                os.path.join(_here, "..", "tests", "postroute_audit.py")):
    try:
        exec(compile(open(_script).read(), _script, "exec"), {"ctx": ctx})  # noqa: F821
    except SystemExit as e:
        if e.code:
            _failed.append(os.path.basename(_script))
if _failed:
    print(f"  postroute_checks: FAILED ({', '.join(_failed)})")
    sys.exit(1)
print("  postroute_checks: both PASS")
