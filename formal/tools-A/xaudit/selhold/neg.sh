#!/usr/bin/env bash
# E8SelC negative controls / sensitivity, seed d slow (inputs built by mkneg.py into $N):
#   NEGhold : stage-pin arc ulink_n_falseResult_77.ctl.u.u/I3 hi + 5000 ps  -> that literal must FAIL (both rows)
#   NEGmap  : bus port of map entry (node 6, pin 0, lit 4) swapped          -> entOK false, that literal FAILs
#   NEGack  : ack of map entry 1 replaced by an unrelated request wire      -> expected to PASS (finding:
#             chainOK does not authenticate the acknowledge; its identity is trusted map data)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
N=${N:-$S/E8SelC}; o=$S/e8mux/w/d/new
python3 -I "$HERE/mkneg.py" $o "$HERE/results/map_d.json" $N
run() {  # tag bands map
  ( cd /home/user/asyncfpga3/formal/lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c \
    'LEAN_PATH="$0:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9SelMain.lean "$@"' \
    "${OL:-$N/ov}" $o/skel.json "$2" $o/cert_slow.json "$3" ) 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xs_d_slow_$1.txt"
  echo "$1: $(grep -h 'RESIDUAL(src)\|RESIDUAL(split)' "$HERE/results/xs_d_slow_$1.txt" | cut -c1-160 | head -4) | $(tail -2 "$HERE/results/xs_d_slow_$1.txt" | tr '\n' ' ')"
}
run NEGhold $N/skel_slow_NEGhold.bands.json "$HERE/results/map_d.json"
run NEGmap $o/skel_slow.bands.json $N/map_d_NEGmap.json
run NEGack $o/skel_slow.bands.json $N/map_d_NEGack.json
