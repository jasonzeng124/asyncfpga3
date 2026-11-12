#!/usr/bin/env bash
# E9SelRun negative controls, seed d slow (inputs from mkneg.py into $N; expected values in notes/A-e9selrun.md §5):
#   NEGack  : E8SelC's NEGack (ack of map entry 1 -> an unrelated request wire); certificate regenerated
#             from the mutated map                                   -> that literal FAILS selL/selT/selJ
#   NEGackS : the same map, the UNMUTATED certificate (stale tree)  -> that literal FAILS (tree root != ack)
#   NEGtok  : entry 1's request walk replaced by a walk with >= 2 tokens -> reqOK false, that literal FAILS
#   NEGhold : E8SelC's NEGhold bands (stage arc ulink_n_falseResult_77.ctl/I3 hi + 5000 ps) -> that literal
#             FAILS selT and selJ (Python: 928 - 5000 = -4072)
#   NEGsib  : a junction row whose sibling arm claims the own arm's lag -> that literal FAILS selJ
#   POSsib  : the same row with the honest (lifted) sibling lag       -> PASSES
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
N=${N:-$S/E9SelRun/neg}; o=$S/e8mux/w/d/new; CD=$S/E9SelRun/w; MAPD="$HERE/../selhold/results"
OL=${OL:-$S/E9SelRun/ov}
export PATH=$HOME/.elan/bin:$PATH PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 XA_ARB=old
mkdir -p $N
python3 "$HERE/mkneg.py" $o $MAPD/map_d.json $CD/sel_d_slow.json $N > $N/mkneg.txt 2>&1 || { cat $N/mkneg.txt; exit 1; }
xl() {  # tag bands cert map
  ( cd /home/user/asyncfpga3/formal/lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c \
    'LEAN_PATH="$0:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9SelLMain.lean "$@"' \
    "$OL" $o/skel.json "$2" "$3" "$4" ) 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xl_d_slow_$1.txt"
  echo "$1: $(grep -h 'selL rows' "$HERE/results/xl_d_slow_$1.txt") | $(tail -3 "$HERE/results/xl_d_slow_$1.txt" | tr '\n' ' ')"
  grep -h 'RESIDUAL' "$HERE/results/xl_d_slow_$1.txt" | grep -v 'RESIDUAL(selL)' | cut -c1-260 | head -4
}
python3 "$HERE/certsel.py" $o/skel.json $o/skel_slow.bands.json $N/map_NEGack.json $N/sel_NEGack.json --ref $o/cert_slow.json > $N/certsel_NEGack.txt 2>&1
xl NEGack $o/skel_slow.bands.json $N/sel_NEGack.json $N/map_NEGack.json
xl NEGackS $o/skel_slow.bands.json $CD/sel_d_slow.json $N/map_NEGack.json
python3 "$HERE/certsel.py" $o/skel.json $o/skel_slow.bands.json $MAPD/map_d.json $N/sel_NEGtok.json --ref $o/cert_slow.json --neg-tok 1 > $N/certsel_NEGtok.txt 2>&1
xl NEGtok $o/skel_slow.bands.json $N/sel_NEGtok.json $MAPD/map_d.json
python3 "$HERE/certsel.py" $o/skel.json $S/E8SelC/skel_slow_NEGhold.bands.json $MAPD/map_d.json $N/sel_NEGhold.json --ref $o/cert_slow.json > $N/certsel_NEGhold.txt 2>&1
xl NEGhold $S/E8SelC/skel_slow_NEGhold.bands.json $N/sel_NEGhold.json $MAPD/map_d.json
xl NEGsib $o/skel_slow.bands.json $N/sel_NEGsib.json $MAPD/map_d.json
xl POSsib $o/skel_slow.bands.json $N/sel_POSsib.json $MAPD/map_d.json
