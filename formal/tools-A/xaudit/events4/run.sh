#!/usr/bin/env bash
# Reproduce A-events4 (gcd_hw R5, seed d): control skeleton, counter-domain analysis at
# slow / fast / mixed prjxray bands, negative control, and the Lean recogniser xevents4.
# Scratch in /tmp/events4 (inputs are decompressed there).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
IN="$HERE/../gcd/inputs"
W=/tmp/events4; mkdir -p $W
for f in net_d bands_d_slow bands_d_fast bands_d_indep; do
  [ -e $W/$f.json ] || xz -dc $IN/$f.json.xz > $W/$f.json
done
for c in slow fast indep; do
  python3 "$HERE/skel.py" $W/net_d.json $W/bands_d_$c.json $W/skel_d.json $W/skel_bands_d_$c.json
  python3 "$HERE/ana.py" $W/skel_d.json $W/skel_bands_d_$c.json --label $c --json $W/sk_$c.json > "$HERE/ana_$c.txt" || true
done
python3 "$HERE/negctl.py" $W/skel_bands_d_slow.json $W/neg_fb.json fb
python3 "$HERE/ana.py" $W/skel_d.json $W/neg_fb.json --label "slow NEG fb+1500" > "$HERE/ana_slow_NEG_fb.txt" || true
python3 "$HERE/report.py" $W/sk_slow.json $W/sk_fast.json $W/sk_indep.json > "$HERE/report.txt"
# Lean recogniser (interpreter; private oleans, no lake build)
L="$(cd "$HERE/../../../lean" && pwd)"; cd "$L"
export XAUDIT_OLEAN=${XAUDIT_OLEAN:-/tmp/events4/olean} PATH=$HOME/.elan/bin:$PATH
../tools-A/xaudit/lean.sh Formal/Core/XAudit/Events4.lean | grep error || true
../tools-A/xaudit/lean.sh Formal/Core/XAudit/Events4Main.lean | grep error || true
../slot.sh lake env bash -c "LEAN_PATH=$XAUDIT_OLEAN:\$LEAN_PATH lean --run Formal/Core/XAudit/Events4Main.lean $W/skel_d.json --bands $W/skel_bands_d_slow.json" > "$HERE/recog_skel_d.txt"
tail -2 "$HERE/recog_skel_d.txt"
