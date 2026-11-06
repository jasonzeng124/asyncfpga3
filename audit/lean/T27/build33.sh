#!/usr/bin/env bash
# formal dcaa52b0: B's S3 cell layer (CElemPS 58 chunks, CElemView, LatchView, SpecLatch*, ViewPS)
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build33.log; : > $L
cd /root/wt-f14 || exit 1
git checkout -q --detach dcaa52b0 >> $L 2>&1 || { echo CHECKOUT_FAIL >> $L; exit 1; }
echo "HEAD $(git rev-parse HEAD) status: $(git status --short | wc -l)" >> $L
cd formal/lean
for mod in Formal.Cells.CElemPS.Defs $(ls Formal/Cells/CElemPS/B*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Cells.CElemPS Formal.Cells.SpecLatch Formal.Cells.SpecLatchFact Formal.Cells.SpecLatchWit Formal.Cells.ViewPS Formal.Cells.CElemView Formal.Cells.LatchView; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b33_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b33_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b33_one.log >> $L
done
echo "B33DONE" >> $L
