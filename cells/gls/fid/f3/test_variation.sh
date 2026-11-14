#!/usr/bin/env bash
# Within-die variation checks on ro_many_top's 128 rings.
#   test_variation.sh RO_WORK     (RO_WORK: routed.json + routed.sdf of ro_many_top)
# 1. the recommended setting (region 0.16 over 10x10 slices + per-wire 0.126)
#    reproduces the 8.5% median ring scatter on record (accept 6.5-10.5%);
# 2. NEGATIVE CONTROL: the same per-wire sigma without the region term must
#    fall short (< 3%), i.e. per-wire scatter alone cannot be what the board
#    shows -- if it did not fall short, check 1 would prove nothing about the
#    correlated term;
# 3. GLS_SCATTER_REGION=0 leaves gen.py's outputs byte-identical.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
W=$1; rc=0
pct() { sed -n 's/.*all \([0-9.]*\)%.*/\1/p'; }
a=$(GLS_SCATTER_REGION=0.16 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire python3 "$HERE/ring_scatter.py" "$W" 8 | tail -1 | pct)
b=$(GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire python3 "$HERE/ring_scatter.py" "$W" 8 | tail -1 | pct)
echo "region 0.16 + wire 0.126: median ring scatter $a%   (target 8.5%)"
echo "wire 0.126 alone        : median ring scatter $b%   (negative control, must be < 3%)"
awk -v a="$a" 'BEGIN{exit !(a >= 6.5 && a <= 10.5)}' || { echo "FAIL 1"; rc=1; }
awk -v b="$b" 'BEGIN{exit !(b < 3)}' || { echo "FAIL 2"; rc=1; }
T=$(mktemp -d); mkdir -p "$T/a" "$T/b"; cp "$W"/routed.* "$T/a/"; cp "$W"/routed.* "$T/b/"
(cd "$T/a" && GLS_WORK=$PWD python3 "$HERE/../../gen.py" >/dev/null 2>&1)
(cd "$T/b" && GLS_WORK=$PWD GLS_SCATTER_REGION=0 python3 "$HERE/../../gen.py" >/dev/null 2>&1)
for f in netlist.v netlist_baked.v annot.sdf; do cmp -s "$T/a/$f" "$T/b/$f" || { echo "FAIL 3 ($f differs)"; rc=1; }; done
[ $rc = 0 ] && echo "test_variation PASS" || echo "test_variation FAIL"
rm -rf "$T"; exit $rc
