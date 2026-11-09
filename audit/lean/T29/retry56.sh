#!/usr/bin/env bash
while ! grep -q B56DONE /home/user/asyncfpga3/audit/lean/T29/build56.log 2>/dev/null; do sleep 60; done
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH; cd /root/wt-f14/formal/lean
L=/root/retry56.log; echo "START $(date -u +%FT%TZ) HEAD $(git rev-parse --short HEAD)" > $L
for m in Formal.Gen.Compute.PSMap.Ushrsi0.Chk72 Formal.Net.Compute.PS.Ushrsi0; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build -j1 $m > /tmp/r56.log 2>&1; rc=$?
  echo "MOD $m rc=$rc $(tail -1 /tmp/r56.log)" >> $L; [ $rc != 0 ] && grep -i "error\|137" /tmp/r56.log | head -8 >> $L
done; echo R56DONE >> $L
