#!/usr/bin/env bash
# WE4g summary table from xe8_<seed>_<corner>.txt (after run8.sh)
HERE="$(cd "$(dirname "$0")" && pwd)"
echo "seed corner | guarded pins certified | min BACK-G ENTRY EXIT1 EXIT2 (ps) | residual guard / all | verdict"
for s in d 3 4 5; do for c in slow fast indep gb; do f="$HERE/xe8_${s}_$c.txt"
  g=$(grep -h '^\[xevents8\] guarded pins' $f | sed 's/.*guarded pins \([0-9]*\/[0-9]*\).*BACK-G \([-0-9]*\) ENTRY \([-0-9]*\) EXIT1 \([-0-9]*\) EXIT2 \([-0-9]*\).*/\1 | \2 \3 \4 \5/')
  echo "$s $c | $g | $(grep -c 'RESIDUAL Guard' $f) / $(grep -c '  RESIDUAL ' $f) | $(tail -1 $f | cut -d"(" -f1)"
done; done
