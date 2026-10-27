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
# --fuel: Recog6 walks a pin path at most FUEL elements; the default 64 is shorter than collatz's
# longest pin paths (65, 73 elements: 4 RECOG-FAIL at 64), so 256 (FUEL).  Any fuel is sound.
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
# All Lean checks of one invocation run inside ONE slot (slot.sh holds the lock for the whole
# batch), so a congested machine costs one wait, not one per run.
XE5=${XEVENTS5:-$LEAN/.lake/build/bin/xevents5}
JOBS=$OUT/xe5_jobs.txt; : > $JOBS
for s in ${SEEDS:-d 4 5 6}; do
  D=$OUT/$s
  for c in ${CORNERS:-slow fast indep gb}; do
    python3 "$X/events4/skel.py" $D/net.json $D/$c.bands.json $D/skel.json $D/skel_$c.bands.json > /dev/null
    python3 "$X/events6/cert6.py" $D/skel.json $D/skel_$c.bands.json $D/cert_$c.json > "$R/cert6_${s}_$c.txt" 2>&1
    python3 "$X/events5/ana5.py" $D/skel.json $D/skel_$c.bands.json --label ${s}_$c > "$R/ana5_${s}_$c.txt" 2>&1
    echo "$D/skel.json $D/skel_$c.bands.json $D/cert_$c.json $R/xe5_${s}_$c.txt" >> $JOBS
  done
done
# negative control (seed d, slow): +1500 ps on ucontrol_merge0's arbiter ua2 own-feedback arc
if [ "${NEG:-1}" = 1 ]; then
  D=$OUT/d
  python3 "$K2/negctl_k2.py" $D/skel.json $D/skel_slow.bands.json $D/skel_slow_NEGfb.bands.json \
      urig.udut.ucontrol_merge0.uarb1.ua2.u | tee "$R/neg_fb.txt"
  python3 "$X/events6/cert6.py" $D/skel.json $D/skel_slow_NEGfb.bands.json $D/cert_NEGfb.json >> "$R/neg_fb.txt" 2>&1
  echo "$D/skel.json $D/skel_slow_NEGfb.bands.json $D/cert_NEGfb.json $R/xe5_d_slow_NEGfb.txt" >> $JOBS
fi
FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" lake env bash -c '
  while read n b c o; do
    if [ -x "$1" ]; then "$1" $n $b $c --fuel $3 > $o 2>&1
    else LEAN_PATH="$2:$LEAN_PATH" lean --run Formal/Core/XAudit/Events5Main.lean $n $b $c --fuel $3 > $o 2>&1; fi
  done < $0' $JOBS "$XE5" "${XAUDIT_OLEAN:-$HOME/k2olean}" "${FUEL:-256}"
while read n b c o; do
  t=$(basename $o .txt); a=$R/ana5_${t#xe5_}.txt
  echo "${t#xe5_}: xevents5: $(tail -1 $o | cut -c1-60) | ana5: $(tail -1 $a 2>/dev/null | cut -c1-60)"
done < $JOBS
