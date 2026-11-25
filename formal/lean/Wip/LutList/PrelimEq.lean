import Formal.Cells.Prelim
import Formal.Core.LutList

/-!
# Wip.LutList.PrelimEq — `Formal.Core.LutList` is `Formal.Cells.Prelim`, name by name

Not claimed (imports `Formal.Cells.Prelim`, which is to be deleted). Every
name of Prelim's list-based LUT API is equal to its `Formal.Core.LutList`
namesake; the non-recursive ones by `rfl`, the recursive ones (`lutIdx`,
`completions`, `muxTree`) by `funext` and list induction, the rest by
rewriting with those (elaborator `rfl` does not unfold the structural
recursion of two distinct constants).
So switching an importer from `Formal.Cells.X` to `Formal.Core.LutList.X`
changes no statement's meaning. See notes/A-lutlist.md.
-/

namespace Wip.LutList.PrelimEq

abbrev P := Formal.Cells.K3
abbrev C := Formal.Core.LutList.K3

theorem K3_eq : C = P := rfl
theorem K3_core : C = Formal.Core.K3 := rfl
theorem f_eq : Formal.Core.LutList.K3.f = Formal.Cells.K3.f := rfl
theorem t_eq : Formal.Core.LutList.K3.t = Formal.Cells.K3.t := rfl
theorem x_eq : Formal.Core.LutList.K3.x = Formal.Cells.K3.x := rfl
theorem ofBool_eq : Formal.Core.LutList.K3.ofBool = Formal.Cells.K3.ofBool := rfl
theorem join_eq : Formal.Core.LutList.K3.join = Formal.Cells.K3.join := rfl
theorem mux_eq : Formal.Core.LutList.K3.mux = Formal.Cells.K3.mux := rfl
theorem not_eq : Formal.Core.LutList.K3.not = Formal.Cells.K3.not := rfl
theorem admits_eq : Formal.Core.LutList.K3.admits = Formal.Cells.K3.admits := rfl
theorem lutIdx_eq : Formal.Core.LutList.lutIdx = Formal.Cells.lutIdx := by
  funext w
  induction w with
  | nil => rfl
  | cons b w ih => simp only [Formal.Core.LutList.lutIdx, Formal.Cells.lutIdx, ih]

theorem lutB_eq : Formal.Core.LutList.lutB = Formal.Cells.lutB := by
  funext init ins
  simp only [Formal.Core.LutList.lutB, Formal.Cells.lutB, lutIdx_eq]

theorem completions_eq : Formal.Core.LutList.completions = Formal.Cells.completions := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [Formal.Core.LutList.completions, Formal.Cells.completions, ih, admits_eq]

theorem muxTree_eq : Formal.Core.LutList.muxTree = Formal.Cells.muxTree := by
  funext g ins
  induction ins generalizing g with
  | nil => rfl
  | cons s ss ih =>
      simp only [Formal.Core.LutList.muxTree, Formal.Cells.muxTree, ih, mux_eq]

theorem lutK_eq : Formal.Core.LutList.lutK = Formal.Cells.lutK := by
  funext init ins
  simp only [Formal.Core.LutList.lutK, Formal.Cells.lutK, muxTree_eq]

theorem o6B_eq : Formal.Core.LutList.o6B = Formal.Cells.o6B := by
  funext i v; simp only [Formal.Core.LutList.o6B, Formal.Cells.o6B, lutB_eq]
theorem o5B_eq : Formal.Core.LutList.o5B = Formal.Cells.o5B := by
  funext i v; simp only [Formal.Core.LutList.o5B, Formal.Cells.o5B, lutB_eq]
theorem o6K_eq : Formal.Core.LutList.o6K = Formal.Cells.o6K := by
  funext i v; simp only [Formal.Core.LutList.o6K, Formal.Cells.o6K, lutK_eq]
theorem o5K_eq : Formal.Core.LutList.o5K = Formal.Cells.o5K := by
  funext i v; simp only [Formal.Core.LutList.o5K, Formal.Cells.o5K, lutK_eq]

/-- Prelim's `lutK` is LutList's mux tree (B's `MuxTree.muxTree_eq_lutK`
reads the same after the switch). -/
theorem lutK_eq_muxTree (init : Nat) (ins : List P) :
    Formal.Cells.lutK init ins = Formal.Core.LutList.muxTree init.testBit ins := by
  rw [← lutK_eq]; rfl

end Wip.LutList.PrelimEq
