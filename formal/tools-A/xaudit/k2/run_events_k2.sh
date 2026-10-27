#!/usr/bin/env bash
# Probe K2: the A-events6 pipeline (the strongest event-level checker in the tree, `xevents5`)
# on the routed collatz_hw.  Per seed x corner:
#   events4/skel.py   (control skeleton + its bands; untrusted)
#   events6/cert6.py  (certificate: nodes, pin trees, walk derivations; untrusted)
#   xevents5          (Lean checker: Recog6 + certificate re-check -> CLEAN or RESIDUAL items)
#   events5/ana5.py   (untrusted Python analysis, for comparison only)
# Inputs: $OUT/<seed>/{net.json,<corner>.bands.json} from bands_k2.sh.
# Outputs: k2/results/{xe5,cert6,ana5}_<seed>_<corner>.txt
#
# XE5: the compiled lake exe if it exists, else `lean --run Formal/Core/XAudit/Events5Main.lean`
# (same code, interpreted); either way under formal/slot.sh.
set -u
K2="$(cd "$(dirname "$0")" && pwd)"
X="$K2/.."
LEAN="$(cd "$K2/../../../lean" && pwd)"
OUT=${OUT:-$HOME/k2out}
R=${R:-$K2/results}
mkdir -p "$R"
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 PATH=$HOME/.elan/bin:$PATH
xe5() {
  if [ -x "$LEAN/.lake/build/bin/xevents5" ]; then
    FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" "$LEAN/.lake/build/bin/xevents5" "$@"
  else
    FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" lake env lean --run Formal/Core/XAudit/Events5Main.lean "$@"
  fi
}
for s in ${SEEDS:-d 4 5 6}; do
  D=$OUT/$s
  for c in ${CORNERS:-slow fast indep gb}; do
    python3 "$X/events4/skel.py" $D/net.json $D/$c.bands.json $D/skel.json $D/skel_$c.bands.json > /dev/null
    python3 "$X/events6/cert6.py" $D/skel.json $D/skel_$c.bands.json $D/cert_$c.json > "$R/cert6_${s}_$c.txt" 2>&1
    xe5 $D/skel.json $D/skel_$c.bands.json $D/cert_$c.json > "$R/xe5_${s}_$c.txt" 2>&1
    python3 "$X/events5/ana5.py" $D/skel.json $D/skel_$c.bands.json --label ${s}_$c > "$R/ana5_${s}_$c.txt" 2>&1
    echo "$s $c: xevents5: $(tail -1 $R/xe5_${s}_$c.txt | cut -c1-90) | ana5: $(tail -1 $R/ana5_${s}_$c.txt | cut -c1-70)"
  done
done
# negative control (seed d, slow): +1500 ps on ucontrol_merge0's arbiter ua2 own-feedback arc
if [ "${NEG:-1}" = 1 ]; then
  D=$OUT/d
  python3 "$K2/negctl_k2.py" $D/skel.json $D/skel_slow.bands.json $D/skel_slow_NEGfb.bands.json \
      urig.udut.ucontrol_merge0.uarb1.ua2.u | tee "$R/neg_fb.txt"
  python3 "$X/events6/cert6.py" $D/skel.json $D/skel_slow_NEGfb.bands.json $D/cert_NEGfb.json >> "$R/neg_fb.txt" 2>&1
  xe5 $D/skel.json $D/skel_slow_NEGfb.bands.json $D/cert_NEGfb.json > "$R/xe5_d_slow_NEGfb.txt" 2>&1
  echo "NEG-fb: $(tail -1 $R/xe5_d_slow_NEGfb.txt | cut -c1-90)"
fi
