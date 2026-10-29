#!/usr/bin/env bash
# Probe E9Par negative controls on seed d slow (E8Mux corrected bands).  Outputs results/xe9p_d_slow_<TAG>.txt.
#   NOPAR    cert9p.py --no-par        no parallel steps: the E8ArbFix certificate (expected: RESIDUAL 54)
#   NEGlag1  --neg-lag=1               every par line claims a lag 1 ps too small (expected: every par line with
#                                      computed lag >= 1 degrades; its items residual)
#   NEGpair  --neg-pair                grant b paired with the shadow of the other branch (expected: all degrade)
#   NEGrc    --neg-rc                  shadows in reset classes of their own (expected: all degrade)
#   NEGband  the positive certificate with ONE shadow's ctl pin band lowered by 300 ps (mutband.py; expected:
#            exactly the par lines mutband.py lists degrade)
set -u
H="$(cd "$(dirname "$0")" && pwd)"; X="$H/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}; O=${O:-$S/E9Par/out}; export OL=${OL:-$S/E9Par/ov2}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 XA_ARB=fix
i=$W/d/new; B=$i/skel_slow.bands.json; mkdir -p $O/d
for t in NOPAR:--no-par NEGlag1:--neg-lag=1 NEGpair:--neg-pair NEGrc:--neg-rc; do
  tag=${t%%:*}; fl=${t#*:}
  python3 "$H/cert9p.py" $i/skel.json $B $O/d/cert_slow_$tag.json $fl > "$H/results/cert9p_d_slow_$tag.txt" 2>&1
  "$H/xe9p.sh" $i/skel.json $B $O/d/cert_slow_$tag.json 2>&1 | grep -v '^\[slot\]' > "$H/results/xe9p_d_slow_$tag.txt"
done
python3 "$H/mutband.py" $O/d/cert_slow.json $O/d/cert_slow_NEGband.json 'vsh:urig.udut.ucontrol_merge4.uarb1.ustate$LUT5/0' 1 300 \
  > "$H/results/cert9p_d_slow_NEGband.txt"
"$H/xe9p.sh" $i/skel.json $B $O/d/cert_slow_NEGband.json 2>&1 | grep -v '^\[slot\]' > "$H/results/xe9p_d_slow_NEGband.txt"
for tag in NOPAR NEGlag1 NEGpair NEGrc NEGband; do
  f=$H/results/xe9p_d_slow_$tag.txt
  echo "$tag: $(grep -o 'parallel-pair lines.*degraded;' $f) | $(grep -o 'Back pins [0-9/]*' $f) | $(grep -o 'guarded pins [0-9/]*' $f) | $(tail -1 $f | cut -d' ' -f2-4 | sed 's/ (Events9Par.*//')"
done
