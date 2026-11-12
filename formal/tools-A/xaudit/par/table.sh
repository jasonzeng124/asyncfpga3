#!/usr/bin/env bash
# Probe E9Par: corrected core WITHOUT parallel-pair lines (arbfix/results/xe9_<s>_<c>_fix.txt, E8ArbFix)
# vs WITH them (par/results/xe9p_<s>_<c>.txt).  The 54 structural items per row (E8ArbFix section 4):
# (a) Back of a grant's ctl pin  `Back arb:...ugrant$LUTk pin1 (virtual)`          18
# (b) Back of a shadow's request pin `Back vsh:... pin0 (virtual)`                   18
# (c) the arbiter acks' guard  `Guard ...uarbN.ua[12].u pinK`                        18
# "certified" = structural in the fix run and not residual in the par run.
H="$(cd "$(dirname "$0")" && pwd)"; X="$H/.."
A='Back arb:urig.udut.ucontrol_merge[0-9]*.uarb[0-9].ugrant\$LUT[56] pin1 \(virtual\)'
B='Back vsh:urig.udut.ucontrol_merge[0-9]*.uarb[0-9].ustate\$LUT5/[01] pin0 \(virtual\)'
C='Guard urig.udut.ucontrol_merge[0-9]*.uarb[0-9].ua[12].u pin[01]'
echo "seed corner | par lines (pass/all) | Back cert | guards cert | structural certified (a)+(b)+(c) of fix-run structural | residual: fix -> par | other residual items (par run)"
for s in d 3 4 5; do for c in slow fast indep gb; do
  f=$X/arbfix/results/xe9_${s}_${c}_fix.txt; p=$H/results/xe9p_${s}_${c}${TAG:-}.txt
  [ -s $p ] || { echo "$s $c | (no run)"; continue; }
  pl=$(grep -o 'parallel-pair lines (par): [0-9]*, [0-9]* pass' $p | awk '{print $5"/"$4}' | tr -d ,)
  bk=$(grep -o 'Back pins [0-9]*/[0-9]*' $p | cut -d' ' -f3); gd=$(grep -o 'guarded pins [0-9]*/[0-9]*' $p | cut -d' ' -f3)
  cnt() { grep '^  RESIDUAL' $1 | grep -cE "$2"; }
  fa=$(cnt $f "$A"); fb=$(cnt $f "$B"); fc=$(cnt $f "$C")
  pa=$(cnt $p "$A"); pb=$(cnt $p "$B"); pc=$(cnt $p "$C")
  fall=$(grep -c '^  RESIDUAL' $f); pall=$(grep -c '^  RESIDUAL' $p)
  oth=$(grep '^  RESIDUAL' $p | grep -vE "$A|$B|$C" | sed 's/^  RESIDUAL //; s/urig.udut.//' | cut -c1-50 | tr '\n' ';')
  echo "$s $c | $pl | $bk | $gd | $((fa-pa))+$((fb-pb))+$((fc-pc)) = $((fa+fb+fc-pa-pb-pc))/$((fa+fb+fc)) | $fall -> $pall ($(tail -1 $p | cut -d' ' -f2-4 | sed 's/ (Events9Par.*//')) | ${oth:-none}"
done; done
