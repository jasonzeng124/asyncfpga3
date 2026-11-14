#!/usr/bin/env bash
# MODE 1 (hold release) sweep of tb_f3_arbtie: arbtie.md "Hold release".
# loop configs, seeds 1..NSEED, one simulation at a time.  Writes one log per
# run under OUT and prints the SUM lines.
#   cells/gls/fid/f3/arbtie_sweep.sh [OUT]       (NSEED, SLIST from the env)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
GLS=$(cd "$HERE/../.." && pwd)
OUT=${1:-$(mktemp -d)}
NSEED=${NSEED:-8}
SLIST=${SLIST:-"600 1200 3000"}
mkdir -p "$OUT"
# A: slow-max arcs (O6 124, O5 152), feedback wire 300 -> TLOOP 424
# B: fast-min-like arcs (50, 53), feedback wire 150 -> TLOOP 200
cfgA="-Ptb_f3_arbtie.T=124 -Ptb_f3_arbtie.T5D=28 -Ptb_f3_arbtie.TFB=300 -Ptb_f3_arbtie.TW=250 -Ptb_f3_arbtie.WMIN=-200 -Ptb_f3_arbtie.WMAX=824 -Ptb_f3_arbtie.MODE=1"
cfgB="-Ptb_f3_arbtie.T=50 -Ptb_f3_arbtie.T5D=3 -Ptb_f3_arbtie.TFB=150 -Ptb_f3_arbtie.TW=120 -Ptb_f3_arbtie.WMIN=-200 -Ptb_f3_arbtie.WMAX=600 -Ptb_f3_arbtie.MODE=1"
for c in A B; do
    eval cfg=\$cfg$c
    for S in $SLIST; do
        # shellcheck disable=SC2086
        iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I"$GLS" $cfg -Ptb_f3_arbtie.S=$S \
            -o "$OUT/$c.S$S.vvp" "$HERE/tb_f3_arbtie.v" "$GLS/prims.v" || exit 1
        for s in $(seq 1 "$NSEED"); do
            vvp -n "$OUT/$c.S$S.vvp" +META_SEED=$s ${EXTRA:-} > "$OUT/$c.S$S.s$s.log" 2>&1
            echo "$c seed=$s $(grep '^SUM' "$OUT/$c.S$S.s$s.log")"
        done
        rm -f "$OUT/$c.S$S.vvp"
    done
done
