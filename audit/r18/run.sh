#!/bin/sh
# audit r18: bd_arbiter near-tie double-ack sweep under research fid model (wt-r17 efc6538, read-only).
# source ~/audit-tc/openxc7/export.sh first. Max 2 sims at once (xargs -P2).
set -e; cd "$(dirname "$0")"; G=/root/wt-r17/cells/gls
md5sum $G/fid_core.vh $G/prims.v /root/wt-r17/cells/rtl/bd_arb.v
build() { iverilog -g2012 -DGLS_FID -DGLS_TRANSPORT_IC -I $G "$@" tb_arbtie.v $G/prims.v; }
for S in 200 600 1500 3000 7000; do
  build -Ptb_arbtie.S=$S -Ptb_arbtie.WMIN=200 -Ptb_arbtie.WMAX=460 -Ptb_arbtie.WSTEP=1 -o A_S$S.vvp      # T124, TLOOP 424
  build -Ptb_arbtie.S=$S -Ptb_arbtie.T=50 -Ptb_arbtie.TFB=150 -Ptb_arbtie.TW=120 -Ptb_arbtie.WMIN=-50 -Ptb_arbtie.WMAX=250 -Ptb_arbtie.WSTEP=1 -o B_S$S.vvp  # TLOOP 200
done
for S in 200 600 1500 3000 7000; do for c in A B; do for s in $(seq 0 19); do
  echo "vvp -n ${c}_S$S.vvp +META_SEED=$s > logs/${c}_S${S}_s$s.log"; done; done; done | xargs -P2 -I{} sh -c '{}'
for s in $(seq 0 4); do vvp -n A_S600.vvp +META_SEED=$s +META_X=1 > logs/AX_S600_s$s.log; vvp -n A_S600.vvp +META_SEED=$s +META_OFF=1 > logs/AOFF_S600_s$s.log || true; done
for S in 700 800 900 1000 1100 1200 1300; do
  build -Ptb_arbtie.S=$S -Ptb_arbtie.WMIN=200 -Ptb_arbtie.WMAX=460 -Ptb_arbtie.WSTEP=1 -o A_S$S.vvp
  build -Ptb_arbtie.S=$S -Ptb_arbtie.T=50 -Ptb_arbtie.TFB=150 -Ptb_arbtie.TW=120 -Ptb_arbtie.WMIN=-50 -Ptb_arbtie.WMAX=250 -Ptb_arbtie.WSTEP=1 -o B_S$S.vvp; done
for S in 700 800 900 1000 1100 1200 1300; do for c in A B; do for s in $(seq 0 9); do
  echo "vvp -n ${c}_S$S.vvp +META_SEED=$s > logs/${c}_S${S}_s$s.log"; done; done; done | xargs -P2 -I{} sh -c '{}'
rm -f *.vvp
python3 -I agg.py 'logs/*.log' | sort -t_ -k2 -V > summary.txt; cat summary.txt
