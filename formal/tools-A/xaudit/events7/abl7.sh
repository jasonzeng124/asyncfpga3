#!/usr/bin/env bash
# Ablation (seed d, slow): which extension removes which residual items. Each run switches some of
# cert7.py's extensions off (the Lean checker is the same); outputs xe7_d_slow_ABL<tag>.txt.
#   all3 : --no-u3 --no-nary --no-gline  (A-events6's judgements; R3 candidates still all tried)
#   nou3 / nonary / nogline : one extension off
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events7/out}; XE7=${XE7:-$HERE/xe7.sh}
export PYTHONHASHSEED=0
s=d; c=slow
for t in "all3:--no-u3 --no-nary --no-gline" "nou3:--no-u3" "nonary:--no-nary" "nogline:--no-gline"; do
  tag=${t%%:*}; fl=${t#*:}
  python3 "$HERE/cert7.py" $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_${c}_ABL$tag.json $fl > /dev/null 2>&1
  $XE7 $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_${c}_ABL$tag.json > "$HERE/xe7_${s}_${c}_ABL$tag.txt" 2>&1
  echo "$tag: $(grep -c 'RESIDUAL Back' $HERE/xe7_${s}_${c}_ABL$tag.txt) Back, $(grep -c 'RESIDUAL Excl' $HERE/xe7_${s}_${c}_ABL$tag.txt) Excl, $(grep -c 'RESIDUAL Line' $HERE/xe7_${s}_${c}_ABL$tag.txt) Line; $(tail -1 $HERE/xe7_${s}_${c}_ABL$tag.txt | cut -c1-40)"
done
