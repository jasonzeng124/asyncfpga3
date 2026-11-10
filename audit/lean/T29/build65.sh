#!/usr/bin/env bash
# formal head: A's CexQ36 + Frontier36 (Lean refutation at kappa 9/25, livelock); one module at a time; disk guard 400 MB
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build65.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
git fetch -q origin claude/formal && git checkout -q --detach origin/claude/formal
echo "HEAD $(git rev-parse HEAD)" >> $L
dirmods() { # dependency-friendly order: data (L*), bases, X* chunks, then everything else (Wit, Refute, AllR, ...) last
  for pat in 'L[0-9]*' 'EncR' 'EncK' 'Ch' 'KBase' 'RBase' 'X[0-9]*' 'B[0-9]*'; do ls $1/$pat.lean 2>/dev/null | sort; done
  for f in $(ls $1/*.lean | sort); do b=$(basename $f .lean); case $b in L[0-9]*|EncR|EncK|Ch|KBase|RBase|X[0-9]*|B[0-9]*) ;; *) echo $f;; esac; done | sort -r
} 
dm() { dirmods $1 | sed 's#/#.#g; s#\.lean$##'; }
M="$(dm Formal/Target/CexQ36) Formal.Target.Frontier36"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b65_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b65_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b65_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build65.log; echo B65DONE >> /home/user/asyncfpga3/audit/lean/T29/build65.log
