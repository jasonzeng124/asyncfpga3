#!/bin/bash
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
cd /home/user/wt-formal3/formal/lean
out=/home/user/asyncfpga3/audit/lean/P3/mut/s3/results.txt
: > $out
for f in /home/user/asyncfpga3/audit/lean/P3/mut/s3/m_*.lean; do
  r=$(timeout 900 lake env lean $f 2>&1); rc=$?
  n=$(echo "$r" | grep -c "error")
  first=$(echo "$r" | grep "error" | head -1 | sed 's#.*/##' | cut -c1-160)
  echo "$(basename $f) rc=$rc errors=$n $first" >> $out
done
echo DONE >> $out
