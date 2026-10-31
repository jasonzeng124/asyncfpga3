#!/usr/bin/env bash
# Probe C-10o:  formal/tools/chainck/run.sh [ROUTE...]
#   ROUTE = gcd:d gcd:2 gcd:3 gcd:4 collatz:1..4 xorshift:1..4 ipow:1..4 (default: all 16)
# Routes are the committed fixtures: gcd_hw = formal/tools/tcheck/build/tree_SEED (C-10e/10m,
# route.sh), kernels = formal/tools/kcheck/build/KERNEL/sSEED (C-10n, route.sh, --freq 100).
# Per route: chainck.py (tcheck's extract.py + rules10k F (Fd) + rulesU (exact rows, Fu))
#   -> build/obl_R.tc, build/rows_R.json; tcheck -> build/t_R.out.  Then summarize.py.
# Two routes at a time (each extract holds ~1 GB).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
TCH=$HERE/../tcheck; KC=$HERE/../kcheck
EXE=$TCH/.lake/build/bin/tcheck
(cd "$TCH" && ./sync.sh --check > /dev/null) || { echo "tcheck sync --check FAILED"; exit 1; }
for t in toy toycert toypair; do
  $EXE $TCH/test/$t.tc 2>/dev/null | diff - $TCH/test/$t.expected > /dev/null || { echo "$t self-test FAILED"; exit 1; }
done
mkdir -p build
ROUTES=${*:-gcd:d gcd:2 gcd:3 gcd:4 collatz:1 collatz:2 collatz:3 collatz:4 xorshift:1 xorshift:2 xorshift:3 xorshift:4 ipow:1 ipow:2 ipow:3 ipow:4}
one() {
  k=${1%%:*}; s=${1##*:}; R=${k}_$s
  if [ "$k" = gcd ]; then
    T=$TCH/build/tree_$s; P=$T/cells/build/hw/gcd_hw; TOP=gcd_hw; CELLS=$T/cells; OSC="--osc dhk --osc invhk"
  else
    P=$KC/build/$k/s$s/pnr; TOP=soak; CELLS=$KC/build/$k/src/cells; OSC=""
  fi
  [ -s "$P/$TOP.sdf" ] || { echo "$R: no route"; return; }
  sha256sum "$P/$TOP.fasm" "$P/$TOP.sdf" > build/sha_$R.txt
  python3 chainck.py "$P" $TOP --cells "$CELLS" $OSC --out build/obl_$R.tc --json build/meta_$R.json \
      --rows build/rows_$R.json 2> build/extract_$R.log || { echo "$R: extract FAILED"; tail -3 build/extract_$R.log; return; }
  $EXE build/obl_$R.tc > build/t_$R.out 2> build/t_$R.err
  gzip -f build/obl_$R.tc
  echo "$R: $(grep '^extract:' build/extract_$R.log | tail -1) / $(tail -1 build/t_$R.err)"
}
set -- $ROUTES
while [ $# -gt 0 ]; do
  one $1 & [ $# -gt 1 ] && one $2 &
  wait; shift; [ $# -gt 0 ] && shift
done
python3 summarize.py build > results.txt
echo "done: results.txt, build/rows_*.json, build/t_*.out"
