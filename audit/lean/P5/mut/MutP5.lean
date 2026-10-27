import Formal.Net.CapstoneCut
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd
set_option maxRecDepth 100000
namespace AuditP5M
def firstIdx (p : K NC → Bool) : Nat := (ops.findIdx? p).getD 0
def iMux := firstIdx (fun k => match k with | .mux .. => true | _ => false)
def iLink := firstIdx (fun k => match k with | .link .. => true | _ => false)
def iAm := firstIdx (fun k => match k with | .amerge .. => true | _ => false)
#eval (iMux, iLink, iAm)
#eval repr (opAt ⟨iMux, by decide⟩)
#eval repr (opAt ⟨iLink, by decide⟩)
#eval repr (opAt ⟨iAm, by decide⟩)
-- M1: swap the data inputs of the first mux
def mutMux : K NC := match opAt ⟨iMux, by decide⟩ with
  | .mux c x y z mw => .mux c y x z mw | k => k
-- M2: redirect the first link's input to channel (i+1)
def mutLink : K NC := match opAt ⟨iLink, by decide⟩ with
  | .link i o => .link ⟨(i.val + 1) % NC, Nat.mod_lt _ (by decide)⟩ o | k => k
-- M3: swap the arbiter's two inputs
def mutAm : K NC := match opAt ⟨iAm, by decide⟩ with
  | .amerge x y z w => .amerge y x z w | k => k
#eval (decide (OpChk tab (opAt ⟨iMux, by decide⟩)), decide (OpChk tab mutMux))
#eval (decide (OpChk tab (opAt ⟨iLink, by decide⟩)), decide (OpChk tab mutLink))
#eval (decide (OpChk tab (opAt ⟨iAm, by decide⟩)), decide (OpChk tab mutAm))
theorem m1 : decide (OpChk tab mutMux) = false := by decide +kernel
/-- FINDING (weak per-op check): redirecting link 6->7 to 7->7 PASSES OpChk (descriptor-only). -/
theorem m2_passes : decide (OpChk tab mutLink) = true := by decide +kernel
-- ...but the whole-net consumer check catches it (channel 6 loses its consumer):
def ops' : List (K NC) := ops.set iLink mutLink
theorem m2_net : ((List.range NC).all (fun c =>
    ((ops'.getD (consT.getD c 0).val (K.sink 0)).insC.map Fin.val).contains c)) = false := by decide +kernel
-- M2c: input redirected to a channel with another descriptor (channel 0): OpChk fails
def mutLink0 : K NC := match opAt ⟨iLink, by decide⟩ with
  | .link _ o => .link ⟨0, by decide⟩ o | k => k
theorem m2c : decide (OpChk tab mutLink0) = false := by decide +kernel
theorem m3 : decide (OpChk tab mutAm) = false := by decide +kernel
-- M4: drop one channel from the spine: spine shape check must fail
def spL' : List Bool := spL.set 2 false
def sp' (c : Fin NC) : Bool := spL'.getD c.val false
def SpOK' : K NC → Bool
  | .forkG i os => if sp' i then (os.filter sp').length == 1 else os.all (fun o => !sp' o)
  | .forkH _ os _ _ _ _ => os.all (fun p => !sp' p.1)
  | .join _ o _ _ _ => !sp' o
  | .bjoin ins o _ _ => !sp' o || (match ins with | [c, d] => !sp' c && sp' d | _ => false)
  | .steerC j t f => sp' t == sp' j && sp' f == sp' j && t != f
  | .steerD _ t f _ _ => !sp' t && !sp' f
  | .mux _ _ _ z _ => !sp' z
  | .muxn _ _ _ _ z _ => !sp' z
  | .amerge x y z _ => sp' x && sp' y && sp' z && x != y
  | .link i o => sp' i == sp' o
  | .src z which _ => sp' z == (which == 2) && (which != 2 || z == start)
  | .sink _ => true
/-- M4: removing `start` (channel 2) from the spine breaks the kernel shape check. -/
theorem m4 : ops.all SpOK' = false := by decide +kernel
end AuditP5M
