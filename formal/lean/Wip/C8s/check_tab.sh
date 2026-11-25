#!/usr/bin/env bash
# C-8s drift check: the generated tables in CapstoneWalkTab.lean equal walkgen.py's output now.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"; T="$HERE/../../Formal/Net/CapstoneWalkTab.lean"
tmp=$(mktemp); python3 "$HERE/walkgen.py" "$tmp" 2>/dev/null
for name in spN grpL rhoL adjL alL lcL recs; do
  a=$(grep -m1 "^def $name " "$T"); b=$(grep -m1 "^def $name " "$tmp")
  [ "$a" == "$b" ] || { echo "check_tab: DRIFT in $name"; rm -f "$tmp"; exit 1; }
done
rm -f "$tmp"; echo "check_tab: ok"
