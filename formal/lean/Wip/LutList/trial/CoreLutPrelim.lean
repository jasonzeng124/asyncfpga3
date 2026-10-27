import Formal.Net.CoreLut
import Formal.Core.LutList

/-!
# Probe 11e: shard C's Core LUT view = shard B's `Formal.Core.LutList`

Porting aid, **to be deleted together with `Formal/Cells/Prelim.lean`**.
It proves that the Core functions shard C now uses (`Formal.Net.CoreLut`) are
shard B's Prelim functions, for every INIT and every pin list, so that no
shard-C statement moved from Prelim to Core lost or changed meaning:

* `lutB_eq_evalL`, `o6B_eq_o6L`, `o5B_eq_o5L` (Boolean; `Bool` is shared);
* `lutK_eq_kevalL` (Kleene, H_KLEENE_LUT): `lutK init (ins.map toP) =
  toP (kevalL init ins)`, via B's `MuxTree.muxTree_eq_lutK` and Core's
  `kevalT` (`muxTree_eq_kevalTL`);
* `toP`/`ofP`: the constructor bijection `zero one X` ↔ `f t x`, with
  `toP_merge` (`merge` = `join`), `toP_kmux` (`kmux` = `K3.mux`), `toP_ofBool`.

Shard A's `Formal.Core.Bridge` (`cells_lutB_eq_eval`, `cells_lutK_eq_keval`)
proves the same on `Fin k` vectors; this file is the list form, and needs only
`Core.Lut`, Prelim and MuxTree.
-/

namespace Formal.Net.CoreLutPrelim
open Formal.Net.CoreLut

abbrev CK := Formal.Core.K3
abbrev PK := Formal.Core.LutList.K3

def toP : CK → PK
  | .zero => .f
  | .one => .t
  | .X => .x

def ofP : PK → CK
  | .f => .zero
  | .t => .one
  | .x => .X

@[simp] theorem toP_ofP (a : PK) : toP (ofP a) = a := by cases a <;> rfl
@[simp] theorem ofP_toP (a : CK) : ofP (toP a) = a := by cases a <;> rfl

@[simp] theorem toP_ofBool (b : Bool) : toP (Formal.Core.K3.ofBool b) = Formal.Core.LutList.K3.ofBool b := by
  cases b <;> rfl

theorem toP_merge (a b : CK) : toP (Formal.Core.K3.merge a b) = Formal.Core.LutList.K3.join (toP a) (toP b) := by
  cases a <;> cases b <;> rfl

theorem toP_kmux (s a b : CK) : toP (kmux s a b) = Formal.Core.LutList.K3.mux (toP s) (toP a) (toP b) := by
  cases s <;> cases a <;> cases b <;> rfl

theorem lutIdx_eq_lsbIdx : ∀ w : List Bool, Formal.Core.LutList.lutIdx w = lsbIdx w
  | [] => rfl
  | b :: w => by cases b <;> simp [Formal.Core.LutList.lutIdx, lsbIdx, lutIdx_eq_lsbIdx w]

/-- **Boolean: Prelim's `lutB` is Core's `Lut.eval`.** -/
theorem lutB_eq_evalL (init : Nat) (ins : List Bool) : Formal.Core.LutList.lutB init ins = evalL init ins := by
  rw [evalL_eq_testBit, Formal.Core.LutList.lutB, lutIdx_eq_lsbIdx]

theorem o6B_eq_o6L (init : Nat) (ins : List Bool) (h : ins.length = 6) :
    Formal.Core.LutList.o6B init ins = o6L init ins := by
  rw [o6L_eq_evalL _ _ h, Formal.Core.LutList.o6B, lutB_eq_evalL]

theorem o5B_eq_o5L (init : Nat) (ins : List Bool) (h : ins.length = 6) :
    Formal.Core.LutList.o5B init ins = o5L init ins := by
  rw [o5L_eq_evalL _ _ h, Formal.Core.LutList.o5B, lutB_eq_evalL]

theorem muxTree_eq_kevalTL : ∀ (t : Nat → Bool) (ins : List CK),
    Formal.Core.LutList.muxTree t (ins.map toP) = toP (kevalTL t ins)
  | t, [] => by simp [Formal.Core.LutList.muxTree, kevalTL_nil]
  | t, a :: as => by
      rw [kevalTL_cons, toP_kmux, ← muxTree_eq_kevalTL _ as, ← muxTree_eq_kevalTL _ as]
      rfl

/-- **Kleene (H_KLEENE_LUT): Prelim's closure `lutK` is Core's `Lut.keval`.** -/
theorem lutK_eq_kevalL (init : Nat) (ins : List CK) :
    Formal.Core.LutList.lutK init (ins.map toP) = toP (kevalL init ins) := by
  rw [← Formal.Core.LutList.muxTree_eq_lutK, muxTree_eq_kevalTL, kevalL_eq_kevalTL]

/-- The same, for a Prelim pin list. -/
theorem lutK_eq_kevalL' (init : Nat) (ins : List PK) :
    Formal.Core.LutList.lutK init ins = toP (kevalL init (ins.map ofP)) := by
  rw [← lutK_eq_kevalL, List.map_map]
  congr 1
  conv => lhs; rw [← List.map_id ins]
  apply List.map_congr_left
  intro a _; simp

end Formal.Net.CoreLutPrelim
