#!/bin/bash
# usage: iterate.sh A B tag  -- refine RT orders until the local check passes (or no new order found)
A=$1; B=$2; T=$3; RT=rt_$T.txt
cp ${4:-/home/user/asyncfpga3/formal/tools/huff/out_rt_pairs.txt} $RT
for it in 1 2 3 4 5 6 7 8; do
  python3 run.py prep.txt init_$A,$B.txt $A $B $RT 1 ev_${T}_it$it.txt
  python3 check2.py prep.txt init_$A,$B.txt ev_${T}_it$it.txt $A $B $RT --witness --maxfail 300 --extra-rt new_${T}_it$it.txt > chk_${T}_it$it.txt 2>&1
  grep -E "^pair|^events" chk_${T}_it$it.txt
  if [ ! -s new_${T}_it$it.txt ]; then echo "no new RT orders"; break; fi
  echo "new orders:"; cat new_${T}_it$it.txt
  cat new_${T}_it$it.txt >> $RT; sort -u $RT -o $RT
done
