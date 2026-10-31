#!/usr/bin/env bash
# Negative controls for the network checker: two mutated copies of the generated network must be
# REJECTED by `decide` (expected output: two "Tactic `decide` proved that the proposition ... is false").
#  Neg1: the addi0 join computes subi;  Neg2: the first 2-way mux has its data inputs swapped.
set -uo pipefail
cd "$(dirname "$0")/../.."
python3 - <<'PY'
import re
src=open('Formal/Net/CapstoneNet.lean').read()
src=src.replace("namespace Formal.Net.CapNet.Gcd","namespace Formal.Net.CapNet.Neg").replace("end Formal.Net.CapNet.Gcd","")
tail="\ntheorem neg_ops : ops.all (fun k => decide (OpChk tab k)) = true := by decide +kernel\nend Formal.Net.CapNet.Neg\n"
a="(.bin .addi 32 (.var 0) (.lit 1))"; i=src.index(a)
open('Wip/C8m/Neg1.lean','w').write(src[:i]+a.replace("addi","subi")+src[i+len(a):]+tail)
mm=re.search(r"K\.mux (\d+) (\d+) (\d+) ",src)
open('Wip/C8m/Neg2.lean','w').write(src[:mm.start()]+f"K.mux {mm.group(1)} {mm.group(3)} {mm.group(2)} "+src[mm.end():]+tail)
PY
export PATH=$HOME/.elan/bin:$PATH; export LEAN_PATH=$PWD/.lake/build/lib/lean
for f in Neg1 Neg2; do
  out=$(../slot.sh lean Wip/C8m/$f.lean 2>&1)
  if grep -q "decide. proved that" <<<"$out"; then echo "$f: rejected (control OK)"; else echo "$f: NOT REJECTED (control failed)"; fi
done
rm -f Wip/C8m/Neg1.lean Wip/C8m/Neg2.lean
