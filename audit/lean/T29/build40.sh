#!/usr/bin/env bash
# formal B certificates (CertPS, CertMarginPS, CertRaceAll, CertRowsPS2, target_b_switch) + C's Stretch/StretchPS.Smax/Periodic,
# one module at a time, after build39 finishes
while ! grep -q B39DONE /home/user/asyncfpga3/audit/lean/T29/build39.log 2>/dev/null; do sleep 60; done
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build40.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
M="Formal.Cells.CertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll $(ls Formal/Cells/CertRowsPS2/*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Cells.CertRowsPS2 $(grep -rl target_b_switch Formal | sed 's#/#.#g; s#\.lean$##' | tr '\n' ' ') Formal.Net.Stretch Formal.Net.StretchPS.Smax Formal.Net.Periodic"
for mod in $M; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b40_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b40_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b40_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build40.log; echo B40DONE >> /home/user/asyncfpga3/audit/lean/T29/build40.log
