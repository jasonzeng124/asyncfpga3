#!/usr/bin/env bash
# tools-B/auto/suite/linescale_x.sh OUT LINE [STEPS] [ND]  (shard B, UNTRUSTED what-if simulation): linescale.sh for a suite
# kernel run by suite/task.sh (OUT = its output dir: OUT/w/m decode, OUT/exp.txt research's C oracle, the kernel's vectors).
# Scales every arc of LINE's chain LUTs (prefix, e.g. bridge_i.udut.udivui0.udly) by s ON THE SAME PLACEMENT (tools-B/preload/
# zeroline.py), bisection on [0, 1] to 1/2^STEPS (default 6); a probe passes when ND (default 4) draws from K0 (default
# research's suite K 10000 + 100 * SEED + 1) and ND slow-carry draws (CARRY4 / F7F8 / FF 0.8-1.0) all return every right
# answer. STRICT=1 also refuses storage-output pulses < 200 ps (NEARMISS). Prints: LINE nLUT s_pass s_fail.
set -uo pipefail
D=$1; L=$2; ST=${3:-6}; ND=${4:-4}; F=$(cd "$(dirname "$0")/../../.." && pwd); H=$F/tools-B/auto; P=$F/tools-B/preload; O=$D/w/m
J=${JOBS:-4}; export TMPDIR=$D
read K S <<< "$(head -1 "$D/summary.txt" | awk '{print $1, $2}')"; K0=${K0:-$((10000 + 100 * S + 1))}
R=${RS:-/home/user/rs}; V=kernels/$K/vec.hex; [ -f "$R/$V" ] || V=research/data/suite/vec/$K.hex
OPS=$(grep -o "operands [^ ]* [^ ]*" "$D/summary.txt" | head -1)
if [ "$(echo "$OPS" | awk '{print ($2 == $3)}')" = 1 ]; then PAIRS=$(awk 'NF>=1{printf "0x%s,0x%s ", $1, $1}' "$R/$V")
else PAIRS=$(awk 'NF>=2{printf "0x%s,0x%s ", $1, $2}' "$R/$V"); fi
RX=$(python3 -c "import re,sys; print('^' + re.escape(sys.argv[1]) + r'\.chain\.g\[[0-9]+\]\.u$')" "$L")
W=$D/lsx${STRICT:-0}_$(echo "$L" | tr -c 'A-Za-z0-9_\n' '_'); mkdir -p "$W"
NL=$(python3 -c "import json,re; c=json.load(open('$O/routed.json'))['modules']['top']['cells']; print(sum(1 for n in c if re.search(r'''$RX''', n)))")
nm() { [ "${STRICT:-0}" = 0 ] && return 0; ! grep -q "nearmiss [1-9]" "$1"/draws.txt 2>/dev/null; }
ok() {
  local s=$1 q=$W/s$1; mkdir -p "$q"; cp "$O/bnd.json" "$q/"
  python3 "$P/zeroline.py" "$O/net.json" "$O/routed.json" "$q/net.json" "$RX" "$s" 2>/dev/null
  for x in "" 0.8,1.0; do k0=$K0; [ -n "$x" ] && k0=$((K0 + 50))
    DRAW_XBAND=$x python3 "$H/xdraws.py" "$D/exp.txt" "$q/net.json" "$q/bnd.json" "$q/d$k0" --kernel "$K" --pairs $PAIRS --draws "$ND" \
      --seed0 "$k0" --jobs "$J" --routed "$O/routed.json" --tmax 400000000 > "$q/d$k0.log" 2>&1
    grep -q "FAIL 0 UNDECIDED 0" "$q/d$k0.log" && nm "$q/d$k0" || { echo "s=$s FAIL $(grep -m1 'seed .* FAIL' "$q/d$k0.log" | cut -c1-160)" >> "$W/log.txt"; return 1; }
  done; echo "s=$s PASS" >> "$W/log.txt"; return 0; }
clean() { rm -rf "$W"/s*/net.json "$W"/s*/d*/net.simx "$W"/s*/d*/simx "$W"/s*/d*/gclass.txt; }
if ok 0; then echo "$L $NL 0 -"; clean; exit 0; fi
lo=0; hi=1; for i in $(seq 1 $ST); do m=$(python3 -c "print(($lo + $hi) / 2)"); if ok $m; then hi=$m; else lo=$m; fi; done
echo "$L $NL $hi $lo"; clean
