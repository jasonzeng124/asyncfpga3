#!/usr/bin/env bash
# Reproduce formal/notes/A-events2pin.md, ring3/pipe3 part: per-pin race check (xevents2pin)
# on real routes, at the slow, fast and mixed (indep) prjxray corners, against the atomic-LUT
# check (xevents2strict on the same data with the site pin inside the route), plus a negative
# control.  Prerequisite: build.sh ring3 1 2 3 4 ; build.sh pipe3 1 2 3 4  (scratch /tmp/events2pin/build).
# Lean runs in the interpreter on private oleans (/tmp/events2pin/olean; no lake build), through slot.sh.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
L=$(cd "$HERE/../../../lean" && pwd)
B=/tmp/events2pin/build
O=${XAUDIT_OLEAN:-/tmp/events2pin/olean}
R=$HERE/results; mkdir -p "$R"
export PATH=$HOME/.elan/bin:$PATH
cd "$L"
if [ ! -e $O/Formal/Core/XAudit/Events2PinDesign.olean ]; then
  mkdir -p $O; [ -d $O/Formal ] || cp -rs "$L/.lake/build/lib/lean/Formal" "$O/"
  for m in Events2Strict Events2PinDesign; do
    ../slot.sh lake env sh -c "LEAN_PATH=$O:\$LEAN_PATH lean -o $O/Formal/Core/XAudit/$m.olean Formal/Core/XAudit/$m.lean" > /dev/null
  done
fi
lrun() { ../slot.sh lake env sh -c "LEAN_PATH=$O:\$LEAN_PATH lean --run Formal/Core/XAudit/$1.lean \"\$@\"" sh "${@:2}"; }
ENV=${ENV:-0:500}
for D in ring3 pipe3; do
  for S in 1 2 3 4; do
    for C in slow fast indep; do
      n=${D}_s${S}_$C
      python3 -I "$HERE/../pinbands.py" $B/${D}_s${S}_routed.json --xray-arcs $B/${D}_s${S}.arcs.tsv \
        --corner $C --out $B/${D}_s${S}.net.json --bands $B/$n.bands.json --atomic-bands $B/$n.atomic.json \
        --report $R/$n.pinbands.txt > /dev/null || { echo "pinbands failed $n"; continue; }
      lrun Events2Pin $B/${D}_s${S}.net.json --bands $B/$n.bands.json --env $ENV > $R/$n.pin.txt; rp=$?
      lrun Events2MainStrict $B/${D}_s${S}.net.json --bands $B/$n.atomic.json --env $ENV > $R/$n.strict.txt; rs=$?
      echo "$n xevents2pin exit $rp ($(grep -o 'min BackPin margin [-0-9]* ps; min atomic Back margin [-0-9]* ps' $R/$n.pin.txt)); xevents2strict exit $rs"
    done
  done
done | tee $R/summary.txt
# negative control: the feedback pin arc of ring3 seed 1 stage u1 made 2000 ps slower in the
# PIN table only (atomic LUT band and site pins unchanged): the atomic check cannot see it,
# the per-pin check must refuse.
python3 -I - "$B/ring3_s1_slow.bands.json" "$B/ring3_s1_slow_NEG.bands.json" <<'EOF'
import json, sys
b = json.load(open(sys.argv[1]))
b["pins"]["u1.u/I2"][1] += 2000
b["comment"] = "NEGATIVE CONTROL: u1.u/I2 (own feedback pin) pin arc hi + 2000 ps"
json.dump(b, open(sys.argv[2], "w"), indent=1)
EOF
lrun Events2Pin $B/ring3_s1.net.json --bands $B/ring3_s1_slow_NEG.bands.json > $R/ring3_s1_slow_NEG.pin.txt
echo "NEG ring3_s1_slow (u1 feedback pin +2000 ps) xevents2pin exit $? ($(grep -o 'summary.*' $R/ring3_s1_slow_NEG.pin.txt))" | tee -a $R/summary.txt
