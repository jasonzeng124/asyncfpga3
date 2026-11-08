#!/usr/bin/env bash
# formal head (after 95f92a9f): A's FormalWit/NM (NodeMerge instance on THE target), one module at a time, disk guard
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build49.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo RESUME-after-container-restart >> $L
echo "HEAD $(git rev-parse HEAD)" >> $L
mods() { for p in $1; do ls FormalWit/NM/$p.lean 2>/dev/null | sort; done | sed 's#/#.#g; s#\.lean$##'; }
M="$(mods 'DB C[0-9]* S[0-9]* L[0-9]* K[0-9]* X[0-9]* All AllX')"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b49_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b49_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b49_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build49.log; echo B49DONE >> /home/user/asyncfpga3/audit/lean/T29/build49.log
