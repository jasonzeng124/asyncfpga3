#!/usr/bin/env bash
# T145: owner 0dacc4e0e (research PROGRAM): "fit the LUT-and-routing band and the CARRY / F7 band as two numbers, and say how
# well the five kernels pin each one down". Own check of how much the board-measured quantity (ns per iteration) depends
# on the CARRY4 / F7F8 / FF band, on the August bitstreams themselves (research/board/aug/builds = research/data/board-august,
# byte-identical, T145 note): chains = rest = the own-fitted x (collatz 0.223, collatz64 0.226, ipow 0.230), CARRY/F7/FF
# at 0.20 and at 1.0, own vectors, 100 MHz bench clock, own fit (t140/fit2.py-style slope). If ns/iter barely moves, these
# kernels cannot pin the CARRY band.
set -u
A=/home/user/asyncfpga3/audit; L=/root/t145.log
true  # (T144 done; rerun after the relative-path fix)
echo "T145 $(date -u)" > $L
cd $A/t90
run() { K=$1 X=$2 C=$3; H=aug_$K; V=$(ls $A/t65/${K}_1?.hex); T=cx${C/./}
  HWD=$H GLS_SDF_FIELD=band VECF=$V FCLK=10000 BAND_CHAIN=$X BAND_REST=$X BAND_CELLX=$C TBATCH=3000000 timeout 9000 bash ../t142/gate.sh $K $T
  python3 ../t65/oracle_$K.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$K band $X CARRY $C: $(grep agreement /root/t90/${H}_${T}_oracle.txt)" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
run collatz 0.223 0.20 & run collatz 0.223 1.0 & wait
run collatz64 0.226 0.20 & run collatz64 0.226 1.0 & wait
run ipow 0.230 0.20 & run ipow 0.230 1.0 & wait
for K in collatz collatz64 ipow; do python3 $A/t145/slope.py $K /root/t90/aug_${K}_cx020_oracle.txt /root/t90/aug_${K}_cx10_oracle.txt >> $L 2>&1; done
echo DONE >> $L; echo DONE > /root/t145.done
