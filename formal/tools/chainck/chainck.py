#!/usr/bin/env python3
"""Probe C-10o: H_CHAIN_SETTLED rows on a routed design (UNTRUSTED driver).

    python3 formal/tools/chainck/chainck.py BUILD TOP --cells CELLS --out OBL.tc \
        --json META.json --rows ROWS.json [--osc dhk ...]

Reuses formal/tools/tcheck/extract.py UNCHANGED (graph, prjxray arc intervals per variant,
certs): extract.py imports `rules10l` for its --rules10l hook; this driver registers
rulesU.py under that name before calling extract.main(), with --no-hi --rules10k F
(C-10k's Fd rows, for the FASTFALL lines) --rules10l U (rulesU: exact rows + Fu rows).
Then run tcheck on OBL.tc (see run.sh).
"""
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
TCHECK = HERE.parent / "tcheck"
sys.path.insert(0, str(TCHECK))
sys.path.insert(1, str(HERE))

import rulesU                     # noqa: E402
sys.modules["rules10l"] = rulesU  # extract.py's --rules10l hook
import extract                    # noqa: E402

args = sys.argv[1:]
rows = None
if "--rows" in args:
    i = args.index("--rows"); rows = args[i + 1]; del args[i:i + 2]
sys.argv = [str(TCHECK / "extract.py")] + args + ["--no-hi", "--only", "none",
                                                   "--rules10k", "F", "--rules10l", "U"]
extract.main()
if rows:
    json.dump(rulesU.ROWS, open(rows, "w"), indent=1, default=str)
print(f"chainck: {len(rulesU.ROWS)} chains", file=sys.stderr)
