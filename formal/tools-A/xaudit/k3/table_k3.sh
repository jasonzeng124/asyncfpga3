#!/usr/bin/env bash
# Probe K3: one row per seed x corner from out/<k>/{xe8,xe5,ana5}_*.txt (verdict text as printed).
#   k3/table_k3.sh <kernel> [seeds]   -> stdout (out/<k>/table.txt)
K=$1; R="$(cd "$(dirname "$0")" && pwd)/out/$K"
v() { case "$(tail -1 $1 2>/dev/null)" in "VERDICT CLEAN"*) echo CLEAN;; *RESIDUAL*) echo "RESIDUAL $(tail -1 $1 | grep -o 'RESIDUAL [0-9]*' | cut -d' ' -f2)";;
      *"NOT RECOGNISED"*) echo "NOT RECOGNISED";; "") echo "EMPTY OUTPUT";; *) echo "?";; esac; }
m() { grep -h "$2 pins" $1 2>/dev/null | grep -o 'min margin -\?[0-9]*' | awk '{print $3}'; }
g() { grep -h '^\[xevents8\] guarded pins' $1 2>/dev/null | sed 's/.*guarded pins \([0-9]*\/[0-9]*\).*ENTRY \(-\?[0-9]*\) EXIT1 \(-\?[0-9]*\).*/\1 E\2 X\3/'; }
printf "%-5s %-6s | %-12s %-6s %-6s %-22s | %-12s | %s\n" seed corner xevents8 Back Line "guards(cert ENTRY EXIT1)" xevents5 ana5
for s in ${2:-d 3 4 5}; do for c in slow fast indep gb; do
  f8=$R/xe8_${s}_$c.txt; f5=$R/xe5_${s}_$c.txt
  printf "%-5s %-6s | %-12s %-6s %-6s %-22s | %-12s | %s\n" $s $c "$(v $f8)" "$(m $f8 Back)" "$(m $f8 line)" "$(g $f8)" "$(v $f5)" \
    "$(tail -1 $R/ana5_${s}_$c.txt | cut -c1-40)"
done; done
echo; echo "RESIDUAL items (xevents8):"
for s in ${2:-d 3 4 5}; do for c in slow fast indep gb; do
  grep -h "^  RESIDUAL\|RECOG-FAIL" $R/xe8_${s}_$c.txt 2>/dev/null | sed "s/^/  $s $c: /" | cut -c1-170
done; done
