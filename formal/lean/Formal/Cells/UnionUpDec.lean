import Formal.Cells.UnionUp
import Formal.Net.AO.DecT

/-!
# Formal.Cells.UnionUpDec — a Boolean checker for `ChainUpOK` (shard B, 2026-11-09)

## Problem, plainly
An instance (a certificate for THE target) has thousands of latch claim chains; each link must be justified by a
`Sep` join, an `Up` join or a common-ancestor join (`UnionUp.ChainUpOK`). This file gives a Boolean function over C's
separation / upper-bound tables (`AO.sepL`, `AO.upL`, as in `Formal/Net/AO/DecT.lean`) that a kernel `decide` can
run, and proves it sound.

## Proved (core Lean, no Mathlib)
* `joinB` / `joinB_sound`: one link, any of the three forms (the ancestor form searches the `Up` table for an entry
  `Up e0 e2` and looks up `Sep e0 -> e1`).
* `chainUpB` / `chainUpB_sound`: `chainUpB sl ul c cs = true → ChainUpOK (sepL sl) (upL ul) c cs`.

## Not shown
Any instance. Cost: the ancestor form scans the Up table once per link (a hint field would make it a lookup).
-/

namespace Formal.Cells.UnionUpDec
open Formal.Net.OccNet.TimedX Formal.Net.AO Formal.Cells.UnionUp

variable {α : Type} [DecidableEq α]

section
variable (sl : List (α × Nat × α × Nat × Nat)) (ul : List ((α × Nat) × (α × Nat) × Nat))

/-- One link of a chain, any of the three joins. -/
def joinB (c1 c2 : Claim α) : Bool :=
  match c1.B, c2.A with
  | some e1, some e2 =>
    (match sepL sl e2.1 e2.2 e1.1 e1.2 with
      | some d => decide (c2.a ≤ (c1.b : Int) + d) | none => false) ||
    (match upL ul e1 e2 with
      | some u => decide (1 ≤ c2.a) && decide (c2.a + u ≤ (c1.b : Int)) | none => false) ||
    (ul.any fun q => q.2.1 == e2 && (match upL ul q.1 e2, sepL sl q.1.1 q.1.2 e1.1 e1.2 with
      | some u, some s => decide (1 ≤ c2.a) && decide (c2.a + u ≤ (c1.b : Int) + s)
      | _, _ => false))
  | none, _ => true
  | some _, none => true

def headB (c c1 : Claim α) : Bool :=
  c1.z == c.z && c1.val == c.val && c1.A == c.A && c1.a == c.a

def chainUpB (c : Claim α) : List (Claim α) → Bool
  | [] => false
  | [c1] => headB c c1 && c1.B == c.B && c1.b == c.b
  | c1 :: c2 :: cs => headB c c1 && joinB sl ul c1 c2 &&
      chainUpB ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ (c2 :: cs)

theorem joinB_sound {c1 c2 : Claim α} (h : joinB sl ul c1 c2 = true) :
    (match c1.B, c2.A with
        | some e1, some e2 => ∃ d, sepL sl e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d
        | none, _ => True
        | some _, none => True) ∨
     (match c1.B, c2.A with
        | some e1, some e2 => ∃ u, upL ul e1 e2 = some u ∧ 1 ≤ c2.a ∧ c2.a + u ≤ (c1.b : Int)
        | none, _ => True
        | some _, none => True) ∨
     JoinAnc (sepL sl) (upL ul) c1 c2 := by
  unfold joinB at h
  unfold JoinAnc
  cases hB : c1.B with
  | none => left; trivial
  | some e1 =>
    cases hA : c2.A with
    | none => left; trivial
    | some e2 =>
      rw [hB, hA] at h
      simp only [Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · left
        cases hs : sepL sl e2.1 e2.2 e1.1 e1.2 with
        | none => rw [hs] at h; cases h
        | some d => rw [hs] at h; exact ⟨d, hs, by simpa using h⟩
      · right; left
        cases hu : upL ul e1 e2 with
        | none => rw [hu] at h; cases h
        | some u =>
          rw [hu] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨u, hu, h.1, h.2⟩
      · right; right
        obtain ⟨q, _, hq⟩ := List.any_eq_true.1 h
        simp only [Bool.and_eq_true, beq_iff_eq] at hq
        obtain ⟨_, hm⟩ := hq
        cases hu : upL ul q.1 e2 with
        | none => rw [hu] at hm; cases hm
        | some u =>
          cases hs : sepL sl q.1.1 q.1.2 e1.1 e1.2 with
          | none => rw [hu, hs] at hm; cases hm
          | some s =>
            rw [hu, hs] at hm
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
            exact ⟨q.1, s, u, hs, hu, hm.1, hm.2⟩

theorem chainUpB_sound : ∀ (cs : List (Claim α)) (c : Claim α), chainUpB sl ul c cs = true →
    ChainUpOK (sepL sl) (upL ul) c cs
  | [], _, h => by simp [chainUpB] at h
  | [c1], c, h => by
    simp only [chainUpB, headB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hz, hv⟩, hA⟩, ha⟩, hB⟩, hb⟩ := h
    exact ⟨hz, hv, hA, ha, hB, hb⟩
  | c1 :: c2 :: cs, c, h => by
    simp only [chainUpB, headB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hz, hv⟩, hA⟩, ha⟩, hj⟩, hr⟩ := h
    exact ⟨hz, hv, hA, ha, joinB_sound sl ul hj, chainUpB_sound (c2 :: cs) _ hr⟩

end

/-- A two-link toy: the hold claim starts at the close event `(1, 0)` + 3; the data claim ends at the open event
`(0, 0)` + 50; the close comes at most 20 after the open (`Up`), so they join (3 + 20 ≤ 50), by `decide`. -/
example : ChainUpOK (sepL ([] : List (Nat × Nat × Nat × Nat × Nat))) (upL [((0, 0), (1, 0), 20)])
    ⟨7, true, none, 0, none, 0⟩
    [⟨7, true, none, 0, some (0, 0), 50⟩, ⟨7, true, some (1, 0), 3, none, 0⟩] :=
  chainUpB_sound _ _ _ _ (by decide)

end Formal.Cells.UnionUpDec
