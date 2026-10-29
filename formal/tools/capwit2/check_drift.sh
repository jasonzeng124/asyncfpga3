#!/usr/bin/env bash
# C-wit drift check: the generated Lean data must equal what gen_wit.py produces now.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
rc=0
for k in rig xorshift collatz; do python3 "$HERE/gen_wit.py" $k --check || rc=1; done
[ $rc = 0 ] && echo "check_drift: ok" || echo "check_drift: DRIFT"
exit $rc
