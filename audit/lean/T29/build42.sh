#!/usr/bin/env bash
# after build41 (worktree already at the formal head it fetched): C's CexR44 (+AllR) and CexRg16; B's RaceAllPS, CertRowsPS,
# RaceAllPS2, CertArbPS, ArbServer(PS); one module at a time (lake resolves the order within a directory); disk guard 400 MB
while ! grep -q B41DONE /home/user/asyncfpga3/audit/lean/T29/build41.log 2>/dev/null; do sleep 60; done
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build42.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
dirmods() { ls $1/*.lean | sort | sed 's#/#.#g; s#\.lean$##'; }
M="$(dirmods Formal/Net/CexR44) $(dirmods Formal/Net/CexRg16) $(dirmods Formal/Cells/RaceAllPS) Formal.Cells.RaceAllPS $(dirmods Formal/Cells/CertRowsPS) Formal.Cells.CertRowsPS $(dirmods Formal/Cells/RaceAllPS2) Formal.Cells.RaceAllPS2 $(dirmods Formal/Cells/CertArbPS) Formal.Cells.CertArbPS Formal.Cells.ArbServer Formal.Cells.ArbServerPS"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b42_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b42_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b42_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build42.log; echo B42DONE >> /home/user/asyncfpga3/audit/lean/T29/build42.log
