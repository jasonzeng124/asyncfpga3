import Formal.Net.HandshakeMuller

/-!
# Track 8a: the hypotheses of `muller_pipeline` are satisfiable by a run that
moves a token

One Muller stage, one token (value 42), source and sink as traces. Every
hypothesis of `muller_pipeline` (n = 1, setup m = 2, hold h = 0) is proved for
these concrete traces, so the theorem is not vacuous, and its conclusion
delivers 42 at the sink's close (step 8) from the source's close (step 6).

Timeline (steps): src req↑ 1, node c↑ 2, sink ack↑ 3, src req↓ 4,
c↓ 6, sink ack↓ 8. Source data 42 until step 6, then 7 (released after the
close: the hold window `[e+1-m, e+h] = [5, 6]`). Latch output 0 until it opens,
42 after.
-/

namespace Formal.Net.Handshake.Witness
open Formal.Net Formal.Net.Handshake

def r0 : Trace := fun t => decide (2 ≤ t ∧ t < 5)
def c : Trace := fun t => decide (2 ≤ t ∧ t < 7) -- MUTANT M7 node rises before req
def a1 : Trace := fun t => decide (4 ≤ t ∧ t < 9)
def d0 : Nat → Nat := fun t => if t < 7 then 42 else 7
def q : Nat → Nat := fun t => if t < 3 then 0 else 42

def ch : Nat → Chan
  | 0 => { req := r0, ack := c, dat := d0 }
  | _ => { req := c, ack := a1, dat := q }

/-- Beyond step 12 every wire is low and constant. -/
theorem late {t : Nat} (h : ¬ t < 12) : r0 t = false ∧ c t = false ∧ a1 t = false := by
  simp only [r0, c, a1]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega

theorem cel_ok : ∀ t, c (t + 1) = c t ∨ c (t + 1) = celN (r0 t) (a1 t) (c t) := by
  intro t
  by_cases ht : t < 12
  · revert t; decide
  · left; rw [(late ht).2.1, (late (show ¬ t + 1 < 12 by omega)).2.1]

theorem rules0 : ∀ t, SendStep (ch 0) t ∧ RecvStep (ch 0) t := by
  intro t
  simp only [ch, SendStep, RecvStep]
  by_cases ht : t < 12
  · revert t; decide
  · have h1 := late ht; have h2 := late (show ¬ t + 1 < 12 by omega)
    rw [h1.1, h1.2.1, h2.1, h2.2.1]; decide

theorem rules1 : ∀ t, SendStep (ch 1) t ∧ RecvStep (ch 1) t := by
  intro t
  simp only [ch, SendStep, RecvStep]
  by_cases ht : t < 12
  · revert t; decide
  · have h1 := late ht; have h2 := late (show ¬ t + 1 < 12 by omega)
    rw [h1.2.1, h1.2.2, h2.2.1, h2.2.2]; decide

theorem c_fall : ∀ e, fallB c e = true → e = 6 := by
  intro e he
  by_cases ht : e < 12
  · have key : ∀ e, e < 12 → fallB c e = true → e = 6 := by decide
    exact key e ht he
  · simp [fallB, (late ht).2.1] at he

theorem stage : MullerStage 2 0 (ch 0) (ch 1) where
  H_NODE := fun _ => rfl
  H_RESET := by decide
  H_CEL_SI := cel_ok
  H_LATCH := by
    intro e he _ s hs _
    have := c_fall e he; subst this
    show q s = d0 6
    have h3 : ¬ s < 3 := by omega
    simp [q, d0, h3]

theorem src_setupHold : SetupHold 2 0 (ch 0) := by
  intro e he s h1 h2
  have := c_fall e he; subst this
  show d0 s = d0 6
  have h3 : s < 7 := by omega
  simp [d0, h3]

/-- The run satisfies every hypothesis of `muller_pipeline`, and the sink's
first close (step 8) carries the source's token 42. -/
theorem witness :
    (∀ j, j ≤ 1 → Protocol (ch j)) ∧
    (∀ k e', TokAt (ch 1) k e' → ∃ e, e < e' ∧ TokAt (ch 0) k e ∧ (ch 1).dat e' = (ch 0).dat e) ∧
    TokAt (ch 1) 0 8 ∧ (ch 1).dat 8 = 42 := by
  have M := muller_pipeline (m := 2) (h := 0) (n := 1) (ch := ch)
    (fun j hj => by rw [show j = 0 by omega]; exact stage)
    (by decide) (by decide)
    (fun t _ => (rules0 t).1) (fun t _ => (rules1 t).2)
    src_setupHold (fun j hj => absurd hj (by omega)) (fun j hj => absurd hj (by omega))
    (by decide)
  exact ⟨M.1, M.2.2, ⟨by decide, by decide⟩, rfl⟩

end Formal.Net.Handshake.Witness
