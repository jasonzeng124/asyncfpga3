import Formal.Cells.SliceNetPS.Chunks
import Formal.Net.CViewPS.Quiet

/-! # Every listed constant (`constF`) is a constant (k = 0) logic gate of THE target with that value (shard B). -/

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Net.CViewPS

/-- `logicPS` as a Boolean. -/
def logicB (w : Nat) : Bool :=
  decide (w / 2500 < cs.length) && decide (w % 2500 < (cs.getD (w / 2500) []).length) &&
    keepPS (gAt cs 2500 w) && (cpIn (gAt cs 2500 w)).isNone

theorem logicB_iff {w : Nat} : logicB w = true ↔ logicPS w := by
  simp only [logicB, logicPS, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, and_assoc]

theorem constF_sound {s : Nat} {b : Bool} (h : constF s = some b) :
    logicPS s ∧ (gAt cs 2500 s).k = 0 ∧ (gAt cs 2500 s).init.testBit 0 = b := by
  unfold constF constOf at h
  obtain ⟨e, he, hb⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some he
  have hkey : e.1 = s % 2500 := by simpa using List.find?_some he
  have hc : s / 2500 < cs.length := by
    by_contra hc
    have : cl.length = cs.length := rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hmem
    simp at hmem
  have hk := const_ok _ hc
  simp only [constChunkOK, List.all_eq_true] at hk
  have := hk e hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none] at this
  obtain ⟨⟨⟨⟨hlt, hkeep⟩, hcp⟩, hk0⟩, hbit⟩ := this
  rw [hkey] at hlt hkeep hcp hk0 hbit
  subst hb
  exact ⟨⟨hc, hlt, hkeep, hcp⟩, hk0, hbit⟩

end Formal.Cells.SliceNetPS
