/-! Shard C (2026-11-10): a block's bound check from its four quarters (the reset-island blocks are checked in
quarters of 13 members so that each kernel check fits in memory). -/

namespace Formal.Net.CViewPS

theorem all_quarters {β : Type} (f : β → Bool) (l : List β) (hl : l.length ≤ 52)
    (h0 : (l.take 13).all f = true) (h1 : ((l.drop 13).take 13).all f = true)
    (h2 : ((l.drop 26).take 13).all f = true) (h3 : ((l.drop 39).take 13).all f = true) : l.all f = true := by
  have e3 : (l.drop 39).take 13 = l.drop 39 := List.take_of_length_le (by simp; omega)
  rw [e3] at h3
  have e : l = l.take 13 ++ ((l.drop 13).take 13 ++ ((l.drop 26).take 13 ++ l.drop 39)) := by
    have a1 := (List.take_append_drop 13 l).symm
    have a2 := (List.take_append_drop 13 (l.drop 13)).symm
    have a3 := (List.take_append_drop 13 (l.drop 26)).symm
    simp only [List.drop_drop] at a2 a3
    rw [a2] at a1
    rw [a3] at a1
    exact a1
  rw [e]
  simp only [List.all_append, h0, h1, h2, h3, Bool.and_self]

end Formal.Net.CViewPS
