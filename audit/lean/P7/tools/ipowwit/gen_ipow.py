# Auditor: emit a Lean witness-data file for the ipow network (IpowCapNet) from the C-8t sim (patched NETF)
import sys, math
sys.path.insert(0, sys.argv[1]); import sim, gen_data
b, e, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
names, ops, out0 = sim.load_net()
assert len(names) == 101 and out0 == 89
tr = sim.simulate(b, e, names, ops)
errs, falls = sim.check(b, e, names, ops, out0, tr)
assert not errs, errs[:5]
rows = gen_data.rows_of(names, ops, tr)
srq = sim.toggles([s[0][2] for s in tr]); assert len(srq) == 2
txt = f'''import Formal.Net.CapstoneWitnessLib
import Formal.Net.IpowCapMain
/-! AUDITOR-GENERATED (audit/lean/P7/tools/ipowwit/gen_ipow.py): unit-delay run of the ipow network, b={b} e={e}. Untrusted data. -/
namespace AuditP7.IpowWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Wit Formal.Net.IpowCap
set_option maxRecDepth 100000
def cds : List CD := [
''' + ",\n".join(rows) + f'''
]
def cdA (c : Fin Formal.Net.IpowCap.NC) : CD := cds.getD c.val ⟨[], [], 0, [], []⟩
def chW : Fin Formal.Net.IpowCap.NC → Handshake.Chan := wch cdA
def startRise : Nat := {srq[0]}
def startFall : Nat := {srq[1]}
def out0Close : Nat := {falls[0]}
end AuditP7.IpowWit
'''
open(out, "w").write(txt); print("wrote", out, "falls", falls, "val", tr[falls[0]][3][out0])
