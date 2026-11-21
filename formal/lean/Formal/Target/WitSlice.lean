/-!
# Formal.Target.WitSlice — a list check split into slices

Shard A, 2026-11-01. The witness's per-gate checks are run in slices (one declaration per slice, so
the kernel's per-declaration memory stays bounded); these two lemmas put the slices back together.
-/

namespace Formal.Target.Wit

theorem forall_drop_take {α : Type} (l : List α) (P : α → Prop) (i n : Nat)
    (h1 : ∀ g ∈ (l.drop i).take n, P g) (h2 : ∀ g ∈ l.drop (i + n), P g) : ∀ g ∈ l.drop i, P g := by
  intro g hg
  rw [← List.take_append_drop n (l.drop i)] at hg
  rcases List.mem_append.1 hg with h | h
  · exact h1 g h
  · exact h2 g (by simpa [List.drop_drop, Nat.add_comm] using h)

theorem forall_drop_len {α : Type} (l : List α) (P : α → Prop) (n : Nat) (h : l.length ≤ n) :
    ∀ g ∈ l.drop n, P g := by
  intro g hg; rw [List.drop_eq_nil_of_le h] at hg; cases hg

end Formal.Target.Wit
