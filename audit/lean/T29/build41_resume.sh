#!/usr/bin/env bash
# after build40: move the formal worktree to the formal head and build CexRuntG (RBase), CexRuntG16 and the new FrontierRunt

export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build41.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo RESUME-after-container-restart >> $L
echo "HEAD $(git rev-parse HEAD)" >> $L
M="Formal.Target.CexRuntG.RBase $(ls Formal/Target/CexRuntG16/L*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Target.CexRuntG16.EncR Formal.Target.CexRuntG16.Ch $(ls Formal/Target/CexRuntG16/X*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Target.CexRuntG16.Wit Formal.Target.CexRuntG16.Refute Formal.Target.FrontierRunt"
for mod in $M; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b41_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b41_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b41_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build41.log; echo B41DONE >> /home/user/asyncfpga3/audit/lean/T29/build41.log
