#!/bin/sh
# C-8r drift check: spL in Formal/Net/CapstoneCutSpine.lean equals spinegen.py's output.
cd "$(dirname "$0")"
gen=$(python3 spinegen.py 2>/dev/null)
have=$(sed -n 's/^def spL : List Bool := //p' ../../Formal/Net/CapstoneCutSpine.lean)
if [ "$gen" = "$have" ]; then echo "check_spine: ok"; else echo "check_spine: DRIFT"; exit 1; fi
