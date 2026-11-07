#!/usr/bin/env bash
# E8Mux: old (committed events8/xe8_<s>_<c>.txt, 99b10a6d bands) vs new (results/xe_<s>_new_<c>.txt) verdicts
HERE="$(cd "$(dirname "$0")" && pwd)"
row() {  # file -> "cert | BACK-G ENTRY EXIT1 EXIT2 | guard/all residual | verdict"
  f=$1; [ -s "$f" ] || { echo "MISSING"; return; }
  g=$(grep -h '^\[xevents8\] guarded pins' $f | sed 's/.*guarded pins \([0-9]*\/[0-9]*\).*BACK-G \([-0-9]*\) ENTRY \([-0-9]*\) EXIT1 \([-0-9]*\) EXIT2 \([-0-9]*\).*/\1 | \2 \/ \3 \/ \4 \/ \5/')
  v=$(tail -1 $f | sed 's/^VERDICT //; s/ (Events8.*//')
  echo "$g | $(grep -c 'RESIDUAL Guard' $f) / $(grep -c '  RESIDUAL ' $f) | $v"
}
echo "| seed | corner | OLD: certified, min BACK-G / ENTRY / EXIT1 / EXIT2, residual guard / all, verdict | NEW: same |"
echo "|---|---|---|---|"
for s in d 3 4 5; do for c in slow fast indep gb; do
  echo "| $s | $c | $(row $HERE/../events8/xe8_${s}_$c.txt) | $(row $HERE/results/xe_${s}_new_$c.txt) |"
done; done
echo
echo "Guard residual items, old -> new (ENTRY/EXIT1 margins as printed):"
for s in d 3 4 5; do for c in slow fast indep gb; do
  a=$(grep 'RESIDUAL Guard' $HERE/../events8/xe8_${s}_$c.txt | sed 's/.*urig.udut.\([^ ]*\) \(pin[0-9]\): .*ENTRY \([-0-9]*\) EXIT1 \([-0-9]*\).*/\1 \2 E\3 X\4/' | sort)
  b=$(grep 'RESIDUAL Guard' $HERE/results/xe_${s}_new_$c.txt 2>/dev/null | sed 's/.*urig.udut.\([^ ]*\) \(pin[0-9]\): .*ENTRY \([-0-9]*\) EXIT1 \([-0-9]*\).*/\1 \2 E\3 X\4/' | sort)
  [ "$a" = "$b" ] && continue
  echo "-- $s $c"; diff <(echo "$a") <(echo "$b") | grep '^[<>]'
done; done
echo
echo "Non-guard RESIDUAL lines identical old vs new?"
for s in d 3 4 5; do for c in slow fast indep gb; do
  if diff <(grep '  RESIDUAL ' $HERE/../events8/xe8_${s}_$c.txt | grep -v 'RESIDUAL Guard') \
          <(grep '  RESIDUAL ' $HERE/results/xe_${s}_new_$c.txt 2>/dev/null | grep -v 'RESIDUAL Guard') > /dev/null; then r=same; else r=DIFFER; fi
  printf "%s %s: %s; " $s $c $r
done; done; echo
