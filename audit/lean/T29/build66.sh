#!/usr/bin/env bash
# formal head e5f31db2: B SliceNetPS/StartBoundPS/ArcTreePS (+CovUpChunk), A CertSpec/CertN1/PlanRPS, C AO Unroll*/TimedUp,
# TimedOccUp, timed uaddi0/uori2/uori3/uselect0. One module at a time; chunk dirs in dependency-friendly order; disk guard 400 MB
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build66.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
dirmods() { for pat in 'Defs' 'Data' '[A-Z][0-9][0-9][0-9]'; do ls $1/$pat.lean 2>/dev/null | sort; done
  for f in $(ls $1/*.lean | sort); do b=$(basename $f .lean); case $b in Defs|Data|[A-Z][0-9][0-9][0-9]) ;; *) echo $f;; esac; done; }
dm() { dirmods $1 | sed 's#/#.#g; s#\.lean$##'; }
M="Formal.Cells.ArcTree $(dm Formal/Cells/ArcTreePS) Formal.Cells.CovUpChunk Formal.Cells.StartBound $(dm Formal/Cells/StartBoundPS) $(dm Formal/Cells/SliceNetPS)
 Formal.Net.TimedOccUp Formal.Net.AO.TimedUp Formal.Net.AO.UnrollClaim Formal.Net.AO.UnrollGlue Formal.Net.AO.UnrollUX
 Formal.Net.Compute.PS.Uaddi0T Formal.Net.Compute.PS.Uori2T Formal.Net.Compute.PS.Uori3T Formal.Net.Compute.PS.Uselect0T
 Formal.Target.CertSpec Formal.Target.CertN1 Formal.Target.PlanRPS"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b66_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b66_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b66_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build66.log; echo B66DONE >> /home/user/asyncfpga3/audit/lean/T29/build66.log
