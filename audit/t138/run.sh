#!/usr/bin/env bash
# T138: research b4f2ce555 / e4d656078 "model error: the simulation at the ring band 0.288 runs 8-10% slower per
# iteration than the board". The corner numbers (collatz FAST_MIN 65.16, SLOW_MAX 188.76 ns/iter; board 92.73) are
# research's simulations. Own check: the August collatz bitstream the board measured (research/board/aug/builds,
# bit 6f62bf4a50fa), own HW dir, own gate script (decode from the .bit), OWN vectors (t65/collatz_13.hex, steps up to
# 350), bench clock 100 MHz as on the board, FAST_MIN and SLOW_MAX; slope of latency on steps by own fit (fit.py).
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t138.log; K=collatz; H=aug_collatz; D=${K}_bench_gen
until [ -f /root/t137.done ]; do sleep 60; done
B=$R/research/board/aug/builds/$D
mkdir -p /root/t65/$H; for f in $D.bit $D.sdf ${D}_routed.json $D.fasm; do xz -dc $B/$f.xz > /root/t65/$H/$f; done
echo "T138 $(date -u); research $(git -C $R rev-parse --short HEAD)" > $L; md5sum /root/t65/$H/$D.bit >> $L
cd $A/t90
for c in fastmin:min slowmax:max; do
  HWD=$H GLS_SDF_FIELD=${c##*:} FCLK=10000 TBATCH=3000000 timeout 7200 bash ../t138/gate_clk.sh $K ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "${c%%:*}: $(grep agreement /root/t90/${H}_${c%%:*}_oracle.txt)" >> $L
  rm -rf /root/t65/work_${H}_${c%%:*}/*.json /root/t65/work_${H}_${c%%:*}/*.tsv
done
python3 $A/t138/fit.py /root/t90/${H}_fastmin_oracle.txt /root/t90/${H}_slowmax_oracle.txt >> $L 2>&1
echo DONE >> $L; echo DONE > /root/t138.done
