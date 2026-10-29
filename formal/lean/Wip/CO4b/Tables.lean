import Formal.Net.OpsFork
import Formal.Net.OpsJoin
import Formal.Net.OpsMux
import Formal.Net.OpsMuxNOp
import Formal.Net.OpsLink
open Formal.Net Formal.Net.Ops
open Formal.Cells.LinkHandshake (ctlB)
theorem finv_leaf : ∀ ar aa r k : Bool, Fork.FInv ar aa r k = true → k ≠ r → k = aa := by decide
theorem jinv_leaf : ∀ or oa r k : Bool, Join.JInv or oa r k = true → r = k → r = or := by decide
theorem link_leaf : ∀ e ∈ Link.ltbl, ctlB e.ir e.oa e.c false ≠ e.c → e.orq = e.c := by decide
set_option maxRecDepth 100000 in
theorem mux_leaf0 : ∀ e ∈ Mux.tbl, ∀ v : Bool, v ≠ e.j0 → e.xr = v → (e.cr && !e.s) = v → e.j0 = e.zr := by decide +kernel
set_option maxRecDepth 100000 in
theorem mux_leaf1 : ∀ e ∈ Mux.tbl, ∀ v : Bool, v ≠ e.j1 → e.yr = v → (e.cr && e.s) = v → e.j1 = e.zr := by decide +kernel
def LeafAt (e : MuxN.MS) : Prop := MuxN.mem e = true →
  (∀ v : Bool, v ≠ e.j0 → e.r0 = v → (e.cr && e.s == 0) = v → e.j0 = e.zr) ∧
  (∀ v : Bool, v ≠ e.j1 → e.r1 = v → (e.cr && e.s == 1) = v → e.j1 = e.zr) ∧
  (∀ v : Bool, v ≠ e.j2 → e.r2 = v → (e.cr && e.s == 2) = v → e.j2 = e.zr)
instance (e : MuxN.MS) : Decidable (LeafAt e) := by unfold LeafAt; exact inferInstance
def Leaf (s0 : Nat) : Prop := ∀ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Bool,
    LeafAt ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩
instance (s0 : Nat) : Decidable (Leaf s0) := by unfold Leaf; exact inferInstance
set_option maxRecDepth 100000 in
theorem leaf0 : Leaf 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf3 : Leaf 3 := by decide +kernel
