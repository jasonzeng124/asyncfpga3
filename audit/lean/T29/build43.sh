#!/usr/bin/env bash
# formal head 234e1135: A's CexRunt44/G16 AnyR, CexRuntD60 (w=40, kappa 15/25), FrontierRunt40, FrontierRuntR; B's BigCertPS,
# RaceAllTarget, CertArbPS2-4, ArbServerPS3, ArbOneAck*, LatchHoldCert, CertLatchPS, LatchHoldPS; one module at a time (lake resolves the order within a directory); disk guard 400 MB
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build43.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
git fetch -q origin claude/formal && git checkout -q --detach 234e1135
echo "HEAD $(git rev-parse HEAD)" >> $L
dirmods() { # dependency-friendly order: data (L*), bases, X* chunks, then everything else (Wit, Refute, AllR, ...) last
  for pat in 'L[0-9]*' 'EncR' 'EncK' 'Ch' 'KBase' 'RBase' 'X[0-9]*' 'B[0-9]*'; do ls $1/$pat.lean 2>/dev/null | sort; done
  for f in $(ls $1/*.lean | sort); do b=$(basename $f .lean); case $b in L[0-9]*|EncR|EncK|Ch|KBase|RBase|X[0-9]*|B[0-9]*) ;; *) echo $f;; esac; done | sort -r
} 
dm() { dirmods $1 | sed 's#/#.#g; s#\.lean$##'; }
M="Formal.Target.CexRunt44.AnyR Formal.Target.CexRuntG16.AnyR Formal.Target.CexRuntD.RBase $(dm Formal/Target/CexRuntD60) Formal.Target.FrontierRunt40 Formal.Target.FrontierRuntR $(dm Formal/Cells/BigCertPS) Formal.Cells.BigCertPS Formal.Cells.RaceAllTarget $(dm Formal/Cells/CertArbPS2) Formal.Cells.CertArbPS2 $(dm Formal/Cells/CertArbPS3) Formal.Cells.CertArbPS3 $(dm Formal/Cells/CertArbPS4) Formal.Cells.CertArbPS4 Formal.Cells.ArbServerPS3 Formal.Cells.ArbOneAck Formal.Cells.ArbOneAckPS Formal.Cells.ArbOneAckAllPS Formal.Cells.ArbOneAckAllPS2 Formal.Cells.ArbOneAckAllPS3 Formal.Cells.ArbOneAckAllPS4 Formal.Cells.LatchHoldCert $(dm Formal/Cells/CertLatchPS) Formal.Cells.CertLatchPS $(dm Formal/Cells/LatchHoldPS) Formal.Cells.LatchHoldPS"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b43_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b43_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b43_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build43.log; echo B43DONE >> /home/user/asyncfpga3/audit/lean/T29/build43.log
