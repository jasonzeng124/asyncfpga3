#!/usr/bin/env bash
# formal A CexRunt72 (H_RUNT(20) refutation at kappa 18/25) + FrontierRunt, one module at a time
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build38.log; echo RESUME-after-container-restart >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
M="$(ls Formal/Target/CexRunt72/L*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Target.CexRunt72.EncR Formal.Target.CexRunt72.RBase Formal.Target.CexRunt72.Ch $(ls Formal/Target/CexRunt72/X*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Target.CexRunt72.Wit Formal.Target.CexRunt72.Refute Formal.Target.FrontierRunt"
for mod in $M; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b38_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b38_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b38_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build38.log; echo B38DONE >> /home/user/asyncfpga3/audit/lean/T29/build38.log
