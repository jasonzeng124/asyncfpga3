#!/bin/sh
# audit r21 task 1: r18 bench (FB6 added) against wt-r13 fid_core.vh. One sim at a time.
# source ~/audit-tc/openxc7/export.sh first. Usage: run.sh <scratch dir for .vvp>
set -e; R=/home/user/asyncfpga3/audit/r21; V=$1; G=/root/wt-r13/cells/gls
md5sum $G/fid_core.vh $G/prims.v /root/wt-r13/cells/rtl/bd_arb.v $R/tb_arbtie.v
build() { iverilog -g2012 -DGLS_FID -DGLS_TRANSPORT_IC -I $G "$@" $R/tb_arbtie.v $G/prims.v; }
for S in 200 600 700 800 900 905 910 915 920 950 1000 1050 1080 1085 1090 1095 1100 1110 1150 1200 1300 1500 3000; do
  build -Ptb_arbtie.S=$S -Ptb_arbtie.WMIN=200 -Ptb_arbtie.WMAX=460 -Ptb_arbtie.WSTEP=1 -o $V/A_S$S.vvp
  build -Ptb_arbtie.S=$S -Ptb_arbtie.T=50 -Ptb_arbtie.TFB=150 -Ptb_arbtie.TW=120 -Ptb_arbtie.WMIN=-50 -Ptb_arbtie.WMAX=250 -Ptb_arbtie.WSTEP=1 -o $V/B_S$S.vvp
  for c in A B; do for s in $(seq 0 19); do vvp -n $V/${c}_S$S.vvp +META_SEED=$s > $R/logs/${c}_S${S}_s$s.log; done; done
done
for s in $(seq 0 4); do vvp -n $V/A_S600.vvp +META_SEED=$s +META_X=1 > $R/logs/AX_S600_s$s.log; vvp -n $V/A_S600.vvp +META_SEED=$s +META_OFF=1 > $R/logs/AOFF_S600_s$s.log || true; done
python3 -I $R/agg.py "$R/logs/*.log" | sort -t_ -k2 -V > $R/summary.txt; cat $R/summary.txt
