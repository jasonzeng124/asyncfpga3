#!/usr/bin/env bash
# T140: as T138 for the August collatz64 (board 117.89, research FAST_MIN 83.04 / SLOW_MAX 237.37) and ipow (board 60.46,
# research 42.20 / 122.53) bitstreams: own HW dirs from research/board/aug/builds, own gate (t138/gate_clk.sh, 100 MHz),
# own vectors (t65/collatz64_14.hex, t65/ipow_17.hex), own fit (fit2.py). Corners FAST_MIN and SLOW_MAX, 2 runs at a time.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t140.log
echo "T140 $(date -u); research $(git -C $R rev-parse --short HEAD)" > $L
for K in collatz64 ipow; do D=${K}_bench_gen; H=aug_$K; B=$R/research/board/aug/builds/$D
  mkdir -p /root/t65/$H; for f in $D.bit $D.sdf ${D}_routed.json $D.fasm; do xz -dc $B/$f.xz > /root/t65/$H/$f; done
  md5sum /root/t65/$H/$D.bit >> $L; done
cd $A/t90
run() { K=$1; c=$2; H=aug_$K; V=$(ls ../t65/${K}_1?.hex)
  HWD=$H GLS_SDF_FIELD=${c##*:} FCLK=10000 TBATCH=3000000 timeout 9000 bash ../t138/gate_clk.sh $K ${c%%:*}
  python3 ../t65/oracle_$K.py check $V /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "$K ${c%%:*}: $(grep agreement /root/t90/${H}_${c%%:*}_oracle.txt)" >> $L
  rm -rf /root/t65/work_${H}_${c%%:*}/*.json /root/t65/work_${H}_${c%%:*}/*.tsv; }
run collatz64 fastmin:min & run collatz64 slowmax:max & wait
run ipow fastmin:min & run ipow slowmax:max & wait
python3 $A/t140/fit2.py collatz64 /root/t90/aug_collatz64_fastmin_oracle.txt /root/t90/aug_collatz64_slowmax_oracle.txt 117.89 83.04 237.37 >> $L 2>&1
python3 $A/t140/fit2.py ipow /root/t90/aug_ipow_fastmin_oracle.txt /root/t90/aug_ipow_slowmax_oracle.txt 60.46 42.20 122.53 >> $L 2>&1
echo DONE >> $L; echo DONE > /root/t140.done
