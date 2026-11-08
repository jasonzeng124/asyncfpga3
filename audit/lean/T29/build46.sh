#!/usr/bin/env bash
# formal 5a2a67e1: C's OccNet, OccNetDec, TimedOcc, TimedOccX, TimedBridge; A's NodeMerge, NodeMergeLut, NodeMergePin
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build46.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
for mod in Formal.Net.OccNet Formal.Net.OccNetDec Formal.Net.TimedOcc Formal.Net.TimedOccX Formal.Net.TimedBridge Formal.Target.NodeMerge Formal.Target.NodeMergeLut Formal.Target.NodeMergePin; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b46_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b46_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b46_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build46.log; echo B46DONE >> /home/user/asyncfpga3/audit/lean/T29/build46.log
