#!/usr/bin/env bash
# Probe K2: the A-events7 pipeline (xevents7, Events7.design_verdict7) on the routed collatz_hw.
# Per seed x corner:  events4/skel.py -> events7/cert7.py (untrusted) -> xevents7 (Lean,
# `lean --run Formal/Core/XAudit/Events7Main.lean` on the private overlay $XAUDIT_OLEAN, built by
# mk_k2.sh + lean.sh for Events7{Core,Excl,Cert,Beh}), through formal/slot.sh, at most $J (2) jobs
# at once (parallel runs gave empty outputs before).  --fuel 256 as for xevents5 (64 is shorter
# than collatz's 65/73-element pin paths).
# Negative controls (seed d slow): NEG-fb3000 (+3000 ps on ucontrol_merge0.uarb1.ua2's own feedback)
# and NEG-recog (cert: one node qi := ri).
# Inputs $OUT/<seed>/{net.json,<corner>.bands.json} (bands_k2.sh).  Outputs k2/results/{xe7,cert7}_*.txt
set -u
K2="$(cd "$(dirname "$0")" && pwd)"; X="$K2/.."
LEAN="$(cd "$K2/../../../lean" && pwd)"
OUT=${OUT:-$HOME/k2out}; R=${R:-$K2/results}; J=${J:-2}
OL=${XAUDIT_OLEAN:-$HOME/k2olean}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 PATH=$HOME/.elan/bin:$PATH
xe7() {  # skel bands cert out
  FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" lake env sh -c \
    'LEAN_PATH="$0:$LEAN_PATH" exec lean --run Formal/Core/XAudit/Events7Main.lean "$@"' "$OL" \
    "$1" "$2" "$3" --fuel ${FUEL:-256} 2>&1 | grep -v '^\[slot\]' > "$4"
}
rows=()
for s in ${SEEDS:-d 4 5 6}; do
  [ "$s" = none ] && continue
  D=$OUT/$s
  for c in ${CORNERS:-slow fast indep gb}; do
    python3 "$X/events4/skel.py" $D/net.json $D/$c.bands.json $D/skel.json $D/skel_$c.bands.json > /dev/null
    python3 "$X/events7/cert7.py" $D/skel.json $D/skel_$c.bands.json $D/cert7_$c.json > "$R/cert7_${s}_$c.txt" 2>&1
    rows+=("$D/skel.json $D/skel_$c.bands.json $D/cert7_$c.json $R/xe7_${s}_$c.txt")
  done
done
if [ "${NEG:-1}" = 1 ]; then
  D=$OUT/d
  [ -e $D/skel_slow_NEGfb3000.bands.json ] || python3 "$K2/negctl_k2.py" $D/skel.json $D/skel_slow.bands.json \
      $D/skel_slow_NEGfb3000.bands.json urig.udut.ucontrol_merge0.uarb1.ua2.u 3000
  python3 "$X/events7/cert7.py" $D/skel.json $D/skel_slow_NEGfb3000.bands.json $D/cert7_NEGfb3000.json > "$R/cert7_d_slow_NEGfb3000.txt" 2>&1
  python3 -I - $D/cert7_slow.json $D/cert7_NEGrecog.json <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
n = next(x for x in c["nodes"] if not x["virt"] and not x["mg"])
n["qi"] = n["ri"]
print("NEG-recog:", n["name"])
json.dump(c, open(sys.argv[2], "w"))
PY
  rows+=("$D/skel.json $D/skel_slow_NEGfb3000.bands.json $D/cert7_NEGfb3000.json $R/xe7_d_slow_NEGfb3000.txt")
  rows+=("$D/skel.json $D/skel_slow.bands.json $D/cert7_NEGrecog.json $R/xe7_d_slow_NEGrecog.txt")
fi
for r in "${rows[@]}"; do
  xe7 $r &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done
wait
for r in "${rows[@]}"; do set -- $r; t=$(basename $4 .txt); echo "${t#xe7_}: $(tail -1 $4 | cut -c1-70)"; done
