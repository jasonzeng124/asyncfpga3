#!/bin/sh
# run_all.sh -- reproduce every result in formal/notes/A-gls-compare.md.
# Needs iverilog 12 and a copy of the research GLS primitives:
#   mkdir -p /tmp/gls-compare
#   git -C /home/user/asyncfpga3 show origin/claude/research:cells/gls/prims.v > /tmp/gls-compare/prims.v
# Usage: sh run_all.sh [PRIMS_V] [OUTDIR]     (outputs go to OUTDIR, default /tmp/gls-compare)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
P=${1:-/tmp/gls-compare/prims.v}
O=${2:-/tmp/gls-compare}
cd "$O"
run() { tb=$1; name=$2; shift 2; iverilog -gspecify "$@" -o "$name.vvp" "$HERE/$tb" "$P"; vvp -n "$name.vvp" > "$name.out"; }
# (2) runt sweeps
run tb_runt.v gls_direct
run tb_runt.v gls_ic300 -DWIRE=300 -DGLS_TRANSPORT_IC
run tb_runt.v gls_ic300_annot -DWIRE=300
run tb_runt.v tr_direct -DLUTMOD=LUT_TR
run tb_runt.v rf_direct -DLUTMOD=LUT_RF
# (1) bd_c2
run tb_c2.v c2_gls
run tb_c2.v c2_gls_pins -DTA1=100 -DTA2=150
run tb_c2.v c2_gls_pins2 -DTA1=150 -DTA2=100
run tb_c2.v c2_gls_fb -DFB=300 -DGLS_TRANSPORT_IC
run tb_c2.v c2_tr -DLUTMOD=LUT_TRC
run tb_c2.v c2_tr_fb -DLUTMOD=LUT_TRC -DFB=300 -DGLS_TRANSPORT_IC
run tb_c2_saf.v c2_saf
# channel identification and (3) Kleene
python3 -I "$HERE/channel_fit.py" "$P" 60
python3 -I "$HERE/channel_fit.py" "$P" 40 --pins 2
python3 -I "$HERE/channel_fit.py" "$P" 40 --rf 56 124
python3 -I "$HERE/kleene_check.py" "$P" | tail -1
cat c2_saf.out
