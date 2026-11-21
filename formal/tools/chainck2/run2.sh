#!/usr/bin/env bash
# Probe C-10o2: formal/tools/chainck2/run2.sh [ROUTE...]  (default gcd:d)
# Extraction only (chainck.py = tcheck's extract.py + rulesU with --dump): writes
# build/dump_R.json (chain networks per variant, as data for the Lean checker) and
# build/rows_R.json (chainck's own Python verdicts, for comparison). Then gen_lean.py.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
TCH=$HERE/../tcheck; KC=$HERE/../kcheck
mkdir -p build
for R in ${*:-gcd:d}; do
  k=${R%%:*}; s=${R##*:}; N=${k}_$s
  if [ "$k" = gcd ]; then
    T=$TCH/build/tree_$s; P=$T/cells/build/hw/gcd_hw; TOP=gcd_hw; CELLS=$T/cells; OSC="--osc dhk --osc invhk"
  else
    P=$KC/build/$k/s$s/pnr; TOP=soak; CELLS=$KC/build/$k/src/cells; OSC=""
  fi
  sha256sum "$P/$TOP.fasm" "$P/$TOP.sdf" > build/sha_$N.txt
  python3 chainck.py "$P" $TOP --cells "$CELLS" $OSC --out build/obl_$N.tc --json build/meta_$N.json \
      --rows build/rows_$N.json --dump build/dump_$N.json 2> build/extract_$N.log || { echo "$N: extract FAILED"; tail -3 build/extract_$N.log; continue; }
  rm -f build/obl_$N.tc
  echo "$N: $(tail -1 build/extract_$N.log)"
done
