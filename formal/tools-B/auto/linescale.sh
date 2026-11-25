#!/usr/bin/env bash
# tools-B/auto/linescale.sh DIR KERNEL LINE [STEPS]  (shard B, UNTRUSTED what-if simulation): how much of one matched-delay
# line's length a decoded route (DIR/m) needs. zeroline.py scales every arc of LINE's chain LUTs (and the routes between them)
# by s ON THE SAME PLACEMENT (not a buildable circuit: a re-placed shorter line routes differently); at each s the probe must
# pass: the kernel's base vectors (research's gate hex) on 8 draws K0..K0+7 and 4 slow-carry draws (CARRY/F7/FF 0.8-1.0),
# and for collatz / collatz64 also the full-range vectors (c32hi / c64hi, 4 draws) and the steps counter preloaded at
# 0x3ffffff0 (ulink_n7, 4 draws); for xorshift the counter preloaded at 0x3ffffff0 (ulink_n6, 4 draws). Bisection of s on
# [0, 1] to 1/2^STEPS (default 3). Prints: LINE nLUT s_pass s_fail. s_pass = 0 means the line is not needed by any probe.
# STRICT (default 1): a probe also fails if any draw shows a storage-LUT output pulse narrower than 200 ps (simx NEARMISS;
# the as-built routes show none; B7's failure was such a pulse). STRICT=0: right answers only.
# Env K0 (default: research's board-item K for the kernel), JOBS (4). PRE="LINE=S LINE=S ...": scale those lines first, in
# every probe (the joint question: how much LINE needs when the others are already shortened).
set -uo pipefail
D=$1; K=$2; L=$3; ST=${4:-3}; F=$(cd "$(dirname "$0")/../.." && pwd); P=$F/tools-B/preload; M=$F/tools/margin; O=$D/m
R=${RS:-/home/user/rs}; G=$R/research/data/eventgraph/gate; J=${JOBS:-4}; export TMPDIR=$D
case $K in
  collatz) K0=${K0:-30601}; V=$G/col18.hex; HV=$P/vec/c32hi.hex; LK=ulink_n7;;
  collatz64) K0=${K0:-30501}; V=$G/c6419.hex; HV=$P/vec/c64hi.hex; LK=ulink_n7;;
  xorshift) K0=${K0:-30801}; V=$G/xor19.hex; HV=; LK=ulink_n6;;
  ipow) K0=${K0:-30201}; V=$G/ipow17.hex; HV=; LK=;;
esac
pairs() { case $K in collatz|collatz64) awk -v z="${2:-}" '(z=="" || $1!="00000001"){printf "0x%s,0x%s ", $1, $1}' "$1";; *) awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' "$1";; esac; }
RX=$(python3 -c "import re,sys; print('^' + re.escape(sys.argv[1]) + r'\.chain\.g\[[0-9]+\]\.u$')" "$L")
W=$D/ls${STRICT:-1}${PRE:+j}_$(echo "$L" | tr -c 'A-Za-z0-9_\n' '_'); mkdir -p "$W"
NL=$(python3 -c "import json,re; c=json.load(open('$O/routed.json'))['modules']['top']['cells']; print(sum(1 for n in c if re.search(r'''$RX''', n)))")
ok() {  # ok S: every probe passes with the line scaled by S
  local s=$1 q=$W/s$1; mkdir -p "$q"; cp "$O/bnd.json" "$q/"; ln -sf "$O/routed.json" "$q/routed.json"
  python3 "$P/zeroline.py" "$O/net.json" "$O/routed.json" "$q/net.json" "$RX" "$s" 2>/dev/null
  for pe in ${PRE:-}; do pl=${pe%=*}; ps=${pe##*=}
    prx=$(python3 -c "import re,sys; print('^' + re.escape(sys.argv[1]) + r'\.chain\.g\[[0-9]+\]\.u$')" "$pl")
    python3 "$P/zeroline.py" "$q/net.json" "$O/routed.json" "$q/net.json" "$prx" "$ps" 2>/dev/null; done
  python3 "$M/draws.py" "$q/net.json" "$q/bnd.json" "$q/a" --kernel $K --pairs $(pairs "$V") --draws 8 --seed0 $K0 --jobs $J --routed "$O/routed.json" --tmax 400000000 2>&1 | grep -q "FAIL 0 UNDECIDED 0" && nm "$q/a" || return 1
  DRAW_XBAND=0.8,1.0 python3 "$M/draws.py" "$q/net.json" "$q/bnd.json" "$q/b" --kernel $K --pairs $(pairs "$V") --draws 4 --seed0 $((K0 + 50)) --jobs $J --routed "$O/routed.json" --tmax 400000000 2>&1 | grep -q "FAIL 0 UNDECIDED 0" && nm "$q/b" || return 1
  if [ -n "$HV" ]; then python3 "$M/draws.py" "$q/net.json" "$q/bnd.json" "$q/c" --kernel $K --pairs $(pairs "$HV") --draws 4 --seed0 $K0 --jobs $J --routed "$O/routed.json" --tmax 400000000 2>&1 | grep -q "FAIL 0 UNDECIDED 0" && nm "$q/c" || return 1; fi
  if [ -n "$LK" ]; then
    if [ $K = xorshift ]; then PP="0x92d68ca2,0x3ffffff1 0x92d68ca2,0x40000000 0x92d68ca2,0x40000001 0x13579bdf,0x40000001 0x9e3779b9,0x40000002"
    else PP="$(pairs "$HV") $(pairs "$V" x)"; fi
    KERNEL=$K "$P/prun.sh" "$q" "$q/p" 0x3ffffff0 $LK "$PP" 4 $K0 $J 2>&1 | grep -q "FAIL 0 UNDECIDED 0" && nm "$q/p" || return 1
  fi; return 0; }
nm() { [ "${STRICT:-1}" = 0 ] && return 0; ! grep -q "nearmiss [1-9]" "$1"/draws.txt 2>/dev/null; }
clean() { rm -rf "$W"/s*/net.json "$W"/s*/*/net.json "$W"/s*/*/net.simx "$W"/s*/*/simx "$W"/s*/*/gclass.txt; }
if ok 0; then echo "$L $NL 0 -"; clean; exit 0; fi
lo=0; hi=1; for i in $(seq 1 $ST); do m=$(python3 -c "print(($lo + $hi) / 2)"); if ok $m; then hi=$m; else lo=$m; fi; done
echo "$L $NL $hi $lo"; clean
