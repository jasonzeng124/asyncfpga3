import Formal.Net.Muller
import Formal.Net.Handshake

/-!
# Track 8, probe 8c: from reachable-state invariants to traces

`Formal.Net.Muller` certifies, per instance, that every reachable state of the
gate-level chain is `Good` (hazard-free, and every pair of `pairs n` obeys the
follow rule). This file turns that into statements about EXECUTIONS read as
traces (`Formal.Net.Prelim.Trace`, one index per transition, stuttering
allowed so that any interleaving and any amount of idling is covered):

* `run_protocol`: on every execution, every pair of `pairs n` read as a channel
  satisfies `Formal.Net.Handshake.Protocol` (shard C, probe 8a): the
  four-phase order `req↑ ack↑ req↓ ack↓` on every link of the chain, both at
  the ack's driver (`c k`) and at the far end of the ack wire (`w k`).
* `protocol_tog`: on a `Protocol` channel the number of req transitions equals
  the number of ack transitions plus one while req is ahead.
* `run_token_order`: for consecutive stages, `#c_k ≤ #c_{k-1} ≤ #c_k + 1`
  on every execution: the j-th transition (token edge) of stage k happens
  only after the j-th transition of stage k-1, and stage k-1 cannot start the
  (j+1)-th before stage k did the j-th. Tokens move through the chain in order,
  one phase at a time, none lost, none overtaken.
-/

namespace Formal.Net.Muller
open Formal.Net Formal.Net.Handshake

/-- An execution: reset state, then at each index either nothing happens or one
enabled node fires. -/
structure Run (m : Mode) (n : Nat) (σ : Nat → Nat) : Prop where
  init : σ 0 = 0
  step : ∀ t, σ (t + 1) = σ t ∨ Step m n (σ t) (σ (t + 1))

theorem run_reach {m n σ} (hr : Run m n σ) : ∀ t, Reach m n (σ t)
  | 0 => by rw [hr.init]; exact Reach.init
  | t + 1 => by
    rcases hr.step t with h | h
    · rw [h]; exact run_reach hr t
    · exact Reach.step (run_reach hr t) h

theorem get_fire (s y x : Nat) : get (fire s y) x = (get s x ^^ decide (y = x)) := by
  simp [get, fire, Nat.testBit_xor, Nat.testBit_two_pow]

/-- The trace of node `X` along an execution. -/
def nodeTrace (σ : Nat → Nat) (X : Nat) : Trace := fun t => get (σ t) X

/-- Pair `(X, Y)` along an execution, read as a handshake channel. -/
def chanOf (σ : Nat → Nat) (X Y : Nat) : Chan := ⟨nodeTrace σ X, nodeTrace σ Y, fun _ => 0⟩

theorem pairOk_iff {s y : Nat} {p : Nat × Nat} (h : pairOk s y p = true) :
    (y = p.1 → get s p.1 = get s p.2) ∧ (y = p.2 → get s p.2 ≠ get s p.1) := by
  simp only [pairOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rcases h1 with h1 | h1
    · exact absurd hy h1
    · exact h1
  · rcases h2 with h2 | h2
    · exact absurd hy h2
    · exact h2

/-- Four-phase protocol on every pair, on every execution. -/
theorem run_protocol {m n σ} (hgood : ∀ s, Reach m n s → Good m n s) (hr : Run m n σ)
    {X Y : Nat} (hp : (X, Y) ∈ pairs n) : Protocol (chanOf σ X Y) := by
  refine ⟨⟨?_, ?_⟩, fun t => ⟨?_, ?_⟩⟩
  · simp [chanOf, nodeTrace, hr.init, get]
  · simp [chanOf, nodeTrace, hr.init, get]
  · intro hch
    simp only [chanOf, nodeTrace] at hch ⊢
    rcases hr.step t with h | ⟨y, hy, h⟩
    · rw [h] at hch; exact absurd rfl hch
    · rw [h, get_fire] at hch
      have hyX : y = X := by
        cases hd : decide (y = X) <;> simp_all
      exact ((pairOk_iff ((hgood _ (run_reach hr t)).2 y hy _ hp)).1 hyX)
  · intro hch
    simp only [chanOf, nodeTrace] at hch ⊢
    rcases hr.step t with h | ⟨y, hy, h⟩
    · rw [h] at hch; exact absurd rfl hch
    · rw [h, get_fire] at hch
      have hyY : y = Y := by
        cases hd : decide (y = Y) <;> simp_all
      exact ((pairOk_iff ((hgood _ (run_reach hr t)).2 y hy _ hp)).2 hyY)

/-- Number of transitions of a trace before index `t`. -/
def tog (s : Trace) : Nat → Nat
  | 0 => 0
  | t + 1 => tog s t + (if s t = s (t + 1) then 0 else 1)

theorem protocol_tog {c : Chan} (hp : Protocol c) :
    ∀ t, tog c.req t = tog c.ack t + (if c.req t = c.ack t then 0 else 1)
  | 0 => by simp [tog, hp.1.1, hp.1.2]
  | t + 1 => by
    have ih := protocol_tog hp t
    have hs := (hp.2 t).1
    have hrv := (hp.2 t).2
    simp only [SendStep, RecvStep] at hs hrv
    simp only [tog]
    cases h1 : c.req t <;> cases h2 : c.ack t <;> cases h3 : c.req (t + 1) <;>
      cases h4 : c.ack (t + 1) <;> simp_all <;> omega

/-- Token order between consecutive stages, on every execution. -/
theorem run_token_order {m n σ} (hgood : ∀ s, Reach m n s → Good m n s) (hr : Run m n σ)
    {k : Nat} (hk1 : 1 ≤ k) (hkn : k < n) (t : Nat) :
    tog (nodeTrace σ (c k)) t ≤ tog (nodeTrace σ (c (k - 1))) t ∧
    tog (nodeTrace σ (c (k - 1))) t ≤ tog (nodeTrace σ (c k)) t + 1 := by
  have hp : (c (k - 1), c k) ∈ pairs n := by
    simp only [pairs, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
      List.mem_cons, decide_eq_true_eq]
    exact Or.inr ⟨k, ⟨hkn, hk1⟩, Or.inl rfl⟩
  have := protocol_tog (run_protocol hgood hr hp) t
  simp only [chanOf] at this
  by_cases he : nodeTrace σ (c (k - 1)) t = nodeTrace σ (c k) t <;>
    simp only [he, ite_true, ite_false] at this <;> omega

end Formal.Net.Muller
