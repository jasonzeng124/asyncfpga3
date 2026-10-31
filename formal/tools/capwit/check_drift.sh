#!/usr/bin/env bash
# C-8t drift check: the generated Lean data must equal what the generators produce now.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
rc=0
python3 "$HERE/gen_data.py" --check || rc=1
"$HERE/../../lean/Wip/C8t/gen_run.sh" --check || rc=1
[ $rc = 0 ] && echo "check_drift: ok" || echo "check_drift: DRIFT"
exit $rc
