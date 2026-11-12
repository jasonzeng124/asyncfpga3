#!/usr/bin/env bash
# C-10j: H_RUNT_ACK on the routed bd_arbiter instances.
#   formal/tools/runtack/check.sh     # extract (~90 s, one process per route) + emit +
#                                     # drift check + Lean (theory + instance verdicts) +
#                                     # axioms + scan + negative control + rule-A replay (~35 s)
# Inputs (read-only): as formal/tools/grantfork/check.sh.  Outputs: build/ here and the
# generated formal/lean/Formal/Timing/RuntAckInst.lean (checked for drift).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$(cd "$HERE/../../lean" && pwd)
mkdir -p "$HERE/build"
python3 -I "$HERE/extract.py" --lean "$HERE/build/RuntAckInst.lean"
cmp "$HERE/build/RuntAckInst.lean" "$LEAN/Formal/Timing/RuntAckInst.lean" \
  || { echo "DRIFT: committed RuntAckInst.lean differs from a fresh extraction"; exit 1; }
python3 -I "$HERE/summarize.py"
cd "$LEAN"; export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
mkdir -p .lake/build/lib/lean/Formal/Timing
[ -f .lake/build/lib/lean/Formal/Timing/GrantFork.olean ] || \
  ../slot.sh lean -o .lake/build/lib/lean/Formal/Timing/GrantFork.olean Formal/Timing/GrantFork.lean
../slot.sh lean -o .lake/build/lib/lean/Formal/Timing/RuntAck.olean Formal/Timing/RuntAck.lean
../slot.sh lean -o .lake/build/lib/lean/Formal/Timing/RuntAckInst.olean Formal/Timing/RuntAckInst.lean
python3 ../scan.py Formal/Timing/RuntAck.lean Formal/Timing/RuntAckInst.lean
cat > "$HERE/build/Axioms.lean" <<'LEANEOF'
import Formal.Timing.RuntAckInst
open Formal.Timing.RuntAck
#print axioms no_extra_ack2
#print axioms no_extra_ack1
#print axioms idx_clean2
#print axioms spurious_ack2_iff
#print axioms spurious_ack1_iff
#print axioms wrong_index2
#print axioms extra_ack2_both
#print axioms inst_no_extra_ack2
#print axioms inst_idx_clean2
#print axioms okAck_exact2
#print axioms cert_bound
#print axioms Formal.Timing.RuntAck.Inst.demo_fast_server
LEANEOF
../slot.sh lean "$HERE/build/Axioms.lean" | tee "$HERE/build/axioms.log"
if grep -v "propext\|Classical.choice\|Quot.sound\|does not depend on any axioms" "$HERE/build/axioms.log" | grep -q "axiom"; then
  echo "UNEXPECTED AXIOM"; exit 1; fi
# negative control: flip one passing verdict; the kernel must refuse it
victim=$(grep -m1 -o 'theorem [A-Za-z0-9_]*_ack : okAck [A-Za-z0-9_]* = true' Formal/Timing/RuntAckInst.lean)
sed "s/${victim}/${victim% true} false/" Formal/Timing/RuntAckInst.lean > "$HERE/build/NegInst.lean"
if ../slot.sh lean "$HERE/build/NegInst.lean" > "$HERE/build/neg.log" 2>&1; then
  echo "NEGATIVE CONTROL DID NOT FAIL"; exit 1; fi
grep -q "proved that the proposition" "$HERE/build/neg.log" && echo "negative control: refused (ok): $victim"
python3 -I "$HERE/rulea.py" > /dev/null
awk -F'\t' 'NR>1 && $3!="True"{bad=1} END{exit bad}' "$HERE/build/rulea.tsv" \
  && echo "rule A: q is a source of every amerge cell's walk ($(($(wc -l < "$HERE/build/rulea.tsv") - 1)) stages)"
echo "C-10j check PASS"
