#!/usr/bin/env bash
# Probe E8ArbFix: old core (events9/xe9_<s>_<c>_new.txt, E8Mux corrected bands, HDsub's run) vs
# corrected core (arbfix/results/xe9_<s>_<c>_fix.txt).  "structural" = the residuals that exist only
# because the Events7 log rules cannot certify the corrected core (Back of a virtual pin with no
# certificate; Guard of an arbiter ack A_b with no certificate); "other" = every other residual.
H="$(cd "$(dirname "$0")" && pwd)"; X="$H/.."
echo "seed corner | OLD: verdict | FIX: Back cert, guards cert, residual all = structural + other | other residual items (fix) | other residual items (old)"
for s in d 3 4 5; do for c in slow fast indep gb; do
  o=$X/events9/xe9_${s}_${c}_new.txt; f=$H/results/xe9_${s}_${c}_fix.txt
  ov=$(tail -1 $o | sed 's/ (Events9.*//; s/VERDICT //')
  bk=$(grep -o 'Back pins [0-9]*/[0-9]*' $f | cut -d' ' -f3); gd=$(grep -o 'guarded pins [0-9]*/[0-9]*' $f | cut -d' ' -f3)
  all=$(grep -c '^  RESIDUAL' $f)
  st=$(grep '^  RESIDUAL' $f | grep -cE '\(virtual\): no certificate|Guard urig.udut.ucontrol_merge[0-9]*.uarb[0-9].ua[12].u pin[01]: no certificate')
  oth=$(grep '^  RESIDUAL' $f | grep -vE '\(virtual\): no certificate|Guard urig.udut.ucontrol_merge[0-9]*.uarb[0-9].ua[12].u pin[01]: no certificate' | sed 's/^  RESIDUAL //; s/urig.udut.//' | cut -c1-60 | tr '\n' ';')
  ooth=$(grep '^  RESIDUAL' $o | sed 's/^  RESIDUAL //; s/urig.udut.//' | grep -c .)
  echo "$s $c | $ov | $bk, $gd, $all = $st + $((all-st)) | ${oth:-none} | $ooth"
done; done
