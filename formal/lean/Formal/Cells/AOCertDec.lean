import Formal.Net.AO.Occ

/-!
# Formal.Cells.AOCertDec — Boolean checkers for the AND-OR certificate's time stamps and bounds (shard B, 2026-11-09)

## Problem, plainly
C's AND-OR timed theorems (`AO.timedA_follows`, and B's `CovUpMain.timedA_follows_cu`) take `TmOK CP`, `TmOK CF`
(time stamps increase along events and along every cause of every alternative) and `∀ v, LSound CF (L v)` (reader
bounds sound, via `AO.lsound_of_step` from `AO.LStep`). C has Boolean checkers for these only for the plain (AND)
certificate (`OccNetDec.tmOKB`, `lstepB`). This file gives them for `AO.Cert`.

## Proved (core Lean)
`tmOKA_of_B` (`tmOKAB C U = true → AO.TmOK C`, `U` covering every node with events), `lstepA_of_B`
(`lstepAB C L U W = true → AO.LStep C L`, `W` covering the nodes where `L` may be nonzero), hence `AO.LSound` through
`AO.lsound_of_step`. Not shown: any instance.
-/

namespace Formal.Cells.AOCertDec
open Formal.Net.AO

variable {α : Type} [DecidableEq α]

def tmOKAB (C : Cert α) (U : List α) : Bool :=
  U.all fun u => (List.range (C.len u)).all fun k =>
    (!(decide (k + 1 < C.len u)) || decide (C.tm u k < C.tm u (k + 1))) &&
    (C.causes u k).all fun alt => alt.all fun p => decide (p.2 < C.len p.1) && decide (C.tm p.1 p.2 < C.tm u k)

theorem tmOKA_of_B {C : Cert α} {U : List α} (hcov : ∀ u, 0 < C.len u → u ∈ U) (h : tmOKAB C U = true) :
    TmOK C := by
  unfold tmOKAB at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  refine ⟨fun u k hk => ?_, fun u k hk alt halt p hp => ?_⟩
  · rcases (h u (hcov u (by omega)) k (by omega)).1 with h1 | h1
    · exact absurd hk h1
    · exact h1
  · exact (h u (hcov u (by omega)) k hk).2 alt halt p hp

def lstepAB (C : Cert α) (L : α → Nat → α → Nat) (U W : List α) : Bool :=
  U.all fun u => (List.range (C.len u)).all fun k => W.all fun w =>
    decide (L u k w ≤ (if u = w then k + 1 else 0)) ||
    (decide (0 < k) && decide (L u k w ≤ L u (k - 1) w)) ||
    (C.causes u k).all fun alt => decide (L u k w ≤ altBound L alt w)

theorem lstepA_of_B {C : Cert α} {L : α → Nat → α → Nat} {U W : List α} (hcov : ∀ u, 0 < C.len u → u ∈ U)
    (hW : ∀ u k w, w ∉ W → L u k w = 0) (h : lstepAB C L U W = true) : LStep C L := by
  intro u k w hk
  by_cases hw : w ∈ W
  · unfold lstepAB at h
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h u (hcov u (by omega)) k hk w hw with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · left; rw [hW u k w hw]; exact Nat.zero_le _

theorem lsoundA_of_B {C : Cert α} {L : α → Nat → α → Nat} {U W : List α} (hcov : ∀ u, 0 < C.len u → u ∈ U)
    (hW : ∀ u k w, w ∉ W → L u k w = 0) (hT : tmOKAB C U = true) (h : lstepAB C L U W = true) : LSound C L :=
  lsound_of_step (tmOKA_of_B hcov hT) (lstepA_of_B hcov hW h)

/-- Toy: an OR event `(2, 0)` with alternatives `[(0,0)]`, `[(1,0)]`; time stamps 1, 2, 5. -/
example : TmOK (⟨fun u => if u < 3 then 1 else 0, fun u _ => if u = 2 then [[(0, 0)], [(1, 0)]] else [],
    fun u _ => if u = 2 then 5 else u + 1⟩ : Cert Nat) :=
  tmOKA_of_B (U := [0, 1, 2]) (fun u h => by
    by_cases h3 : u < 3
    · simp; omega
    · simp [h3] at h) (by decide)

end Formal.Cells.AOCertDec
