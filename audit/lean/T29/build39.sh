#!/usr/bin/env bash
# formal A CexRunt44 (H_RUNT(20) refutation at kappa 11/25, C's k44w20) + FrontierRunt, one module at a time (resumable)
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build39.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
M="Formal.Target.CexRuntP.RBase $(ls Formal/Target/CexRunt44/L*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Target.CexRunt44.EncR Formal.Target.CexRunt44.Ch $(ls Formal/Target/CexRunt44/X*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Target.CexRunt44.Wit Formal.Target.CexRunt44.Refute Formal.Target.FrontierRunt"
for mod in $M; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b39_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b39_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b39_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build39.log; echo B39DONE >> /home/user/asyncfpga3/audit/lean/T29/build39.log
