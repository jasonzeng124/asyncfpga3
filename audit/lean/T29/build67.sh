#!/usr/bin/env bash
# formal head cc1cbfc2: C reset_quiet_all (RIslBnd* blocks, quarters first), one module at a time; disk guard 400 MB
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build67.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean; echo "HEAD $(git rev-parse HEAD)" >> $L
M="Formal.Net.CViewPS.RIslBndDefs $(ls Formal/Net/CViewPS/RIslBnd[0-9][0-9]q[0-9].lean | sort | sed 's#/#.#g; s#\.lean$##') $(ls Formal/Net/CViewPS/RIslBnd[0-9][0-9].lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CViewPS.RIslBndQ Formal.Net.CViewPS.RIslAll"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b67_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b67_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b67_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build67.log; echo B67DONE >> /home/user/asyncfpga3/audit/lean/T29/build67.log
