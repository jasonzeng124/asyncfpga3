#!/usr/bin/env bash
# formal 86a9ffa0: B latch holds (CertLatchPS2/3, LatchHoldPS2/3, LatchHoldPin, LatchHoldPinPS/2/3: 670 latches, data-pin windows);
# one module at a time (lake resolves the order within
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build44.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
git fetch -q origin claude/formal && git checkout -q --detach 86a9ffa0
echo "HEAD $(git rev-parse HEAD)" >> $L
dirmods() { # dependency-friendly order: data (L*), bases, X* chunks, then everything else (Wit, Refute, AllR, ...) last
  for pat in 'L[0-9]*' 'EncR' 'EncK' 'Ch' 'KBase' 'RBase' 'X[0-9]*' 'B[0-9]*'; do ls $1/$pat.lean 2>/dev/null | sort; done
  for f in $(ls $1/*.lean | sort); do b=$(basename $f .lean); case $b in L[0-9]*|EncR|EncK|Ch|KBase|RBase|X[0-9]*|B[0-9]*) ;; *) echo $f;; esac; done | sort -r
} 
dm() { dirmods $1 | sed 's#/#.#g; s#\.lean$##'; }
M="$(dm Formal/Cells/CertLatchPS2) Formal.Cells.CertLatchPS2 $(dm Formal/Cells/LatchHoldPS2) Formal.Cells.LatchHoldPS2 $(dm Formal/Cells/CertLatchPS3) Formal.Cells.CertLatchPS3 $(dm Formal/Cells/LatchHoldPS3) Formal.Cells.LatchHoldPS3 Formal.Cells.LatchHoldPin $(dm Formal/Cells/LatchHoldPinPS) Formal.Cells.LatchHoldPinPS $(dm Formal/Cells/LatchHoldPinPS2) Formal.Cells.LatchHoldPinPS2 $(dm Formal/Cells/LatchHoldPinPS3) Formal.Cells.LatchHoldPinPS3"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b44_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b44_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b44_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build44.log; echo B44DONE >> /home/user/asyncfpga3/audit/lean/T29/build44.log
