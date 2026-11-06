#!/usr/bin/env bash
# formal 5a9f9237: new/changed modules since 0be49560 (A: SpecRunt fix, SpecMono, Assembly, AssemblyPS, BoundaryPS; B: SpecCElem*, C: WinInv, Keller)
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build32.log; : > $L
cd /root/wt-f14 || exit 1
git checkout -q --detach 5a9f9237 >> $L 2>&1 || { echo CHECKOUT_FAIL >> $L; exit 1; }
echo "HEAD $(git rev-parse HEAD) status: $(git status --short | wc -l)" >> $L
cd formal/lean
for mod in Formal.Target.SpecRunt Formal.Target.SpecMono Formal.Cells.SpecCElem Formal.Cells.SpecCElemFact Formal.Cells.SpecCElemWit Formal.Net.WinInv Formal.Net.Keller Formal.Target.Assembly Formal.Target.BoundaryPS Formal.Target.AssemblyPS; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b32_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b32_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b32_one.log >> $L
done
echo "B32DONE" >> $L
