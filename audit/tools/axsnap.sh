#!/usr/bin/env bash
# snapshot per-module axiom results (survives container loss): axsnap.sh <resdir> <out.txt>
for r in "$1"/*.res; do printf '%s\t%s\n' "$(basename "$r" .res)" "$(cat "$r")"; done | sort > "$2"
echo "$(wc -l < "$2") modules; bad=$(awk -F'bad=' 'NF>1{s+=$2}END{print s+0}' "$2"); noresult=$(grep -c 'NO RESULT' "$2")"
