#!/usr/bin/env bash
# T30 retry: formal A's RTPS (H_DECODE round trip) and RTPSSel (roundtrip_sel), one module at a time, disk guard 400 MB.
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build45.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
mods() { for p in $2; do ls FormalWit/$1/$p.lean 2>/dev/null | sort; done | sed 's#/#.#g; s#\.lean$##'; }
M="$(mods RTPS 'B[0-9]* C[0-9]* D[0-9]* F[0-9]* O[0-9]* Rows Top OAll All') $(mods RTPSSel 'S[0-9]* N X All Final')"
for mod in $M; do
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b45_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b45_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b45_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build45.log; echo B45DONE >> /home/user/asyncfpga3/audit/lean/T29/build45.log
