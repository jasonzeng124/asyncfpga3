#!/usr/bin/env bash
# C-8y negative controls for the ipow network checker (same as C-8m's for gcd_hw): two mutated
# copies of the generated IpowCapNet must be REJECTED by `decide`.
#  Neg1: the muli1 join (b*b) computes addi;  Neg2: the first 2-way mux has its data inputs swapped.
#  Neg3/Neg4 (H_WALK proof tables, IpowCapWalkTab): the cascade constants point at the wrong
#  control_merge rule (r154 -> rule 20); the walk group of spine channel 28 is wrong (22 -> 23,
#  consistently in grpL, alL and recs, so only the semantic checks can catch it).
#  Each must make a kernel check fail.
set -uo pipefail
cd "$(dirname "$0")/../.."
python3 - <<'PY'
import re
src=open('Formal/Net/IpowCapNet.lean').read()
src=src.replace("namespace Formal.Net.IpowCap\n","namespace Formal.Net.IpowCap.Neg\n").replace("end Formal.Net.IpowCap\n","")
src=src.replace("import Formal.Net.IpowCapNetSound","import Formal.Net.IpowCapNetSound\nopen Formal.Net.IpowCap")
tail="\ntheorem neg_ops : ops.all (fun k => decide (OpChk tab k)) = true := by decide +kernel\nend Formal.Net.IpowCap.Neg\n"
a="(.bin .muli 32 (.var 0) (.var 1)) [(.direct 0"; i=src.index(a)
open('Wip/C8y/Neg1.lean','w').write(src[:i]+a.replace("muli","addi")+src[i+len(a):]+tail)
mm=re.search(r"K\.mux (\d+) (\d+) (\d+) ",src)
open('Wip/C8y/Neg2.lean','w').write(src[:mm.start()]+f"K.mux {mm.group(1)} {mm.group(3)} {mm.group(2)} "+src[mm.end():]+tail)
w=open('Formal/Net/IpowCapWalkTab.lean').read()
a="theorem r154 : rules[19]?"; assert a in w
open('Wip/C8y/Neg3.lean','w').write(w.replace(a,"theorem r154 : rules[20]?"))
b="(28, 22, 0, true, [22])"; assert b in w
import re as _re
w4=w.replace(b,"(28, 23, 0, true, [23])")
def setpos(txt, name, pos, val):
    m=_re.search(r"^(def "+name+r" : [^=]*:= \[)(.*)(\])$", txt, _re.M)
    items=_re.findall(r"\[[^\]]*\]|[^, ]+", m.group(2)); items[pos]=val
    return txt[:m.start(2)]+", ".join(items)+txt[m.end(2):]
w4=setpos(w4,"grpL",28,"23"); w4=setpos(w4,"alL",28,"[23]")
open('Wip/C8y/Neg4.lean','w').write(w4)
PY
export PATH=$HOME/.elan/bin:$PATH
ok=0
for f in Neg1 Neg2 Neg3 Neg4; do
  out=$(FORMAL_SLOT_CWD=$PWD ../slot.sh lake env lean Wip/C8y/$f.lean 2>&1)
  if grep -q "error" <<<"$out" && grep -q -E "decide|kernel" <<<"$out"; then echo "$f: rejected (control OK): $(grep -m1 error <<<"$out" | cut -c1-110)"; ok=$((ok+1));
  else echo "$f: NOT REJECTED (control failed)"; echo "$out" | head -5; fi
done
rm -f Wip/C8y/Neg1.lean Wip/C8y/Neg2.lean Wip/C8y/Neg3.lean Wip/C8y/Neg4.lean
[ $ok -eq 4 ] && echo "[negctl] PASS" || { echo "[negctl] FAIL"; exit 1; }
