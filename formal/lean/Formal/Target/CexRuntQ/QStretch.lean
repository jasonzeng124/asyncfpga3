import Formal.Target.CexRuntQ.QBase
import Formal.Target.StutterCodes

/-!
# Stretching an eventually periodic run (any reset length) (shard A, 2026-11-09)

**Problem, plainly.** The livelock witnesses (`CexRuntQ.xQ`: prefix codes, then one period repeated for ever) are
found with a 400 ns reset; `Env` fixes the reset length. Shifting every transition after a quiet instant `t0` by
`Δ` must give the stretched run `Stutter.stutB t0 Δ`, as for finite codes (`StutterCodes.stutB_codes`).

**Proved.** `xQ_shift`: if every periodic transition lies after `t0`, the run with prefix codes shifted by
`StutterCodes.shiftE t0 Δ` and every periodic transition shifted by `Δ` is `stutB t0 Δ` of the original.
`xQ_fin`: a node with no periodic part follows its prefix code (`sigL`). `BTN.allLeaves` / `BTN.get_all`: a property
of every leaf of a period tree holds for every node.
-/

namespace Formal.Target.CexRuntQ
open Formal.Target Formal.Net.CexPS72 Formal.Net.Periodic Formal.Target.Stutter Formal.Target.StutterCodes

theorem pre_shift (t0 Δ : Nat) (e : Option (Bool × List Nat)) :
    pre (shiftE t0 Δ e) = ((pre e).1, (pre e).2.map (sh t0 Δ)) := by
  cases e with
  | none => rfl
  | some p => obtain ⟨b, ts⟩ := p; rfl

theorem cnt1_shift_σ {Q t0 Δ p : Nat} (hp : t0 < p) (t : Nat) : cnt1 Q (p + Δ) t = cnt1 Q p (σ t0 Δ t) := by
  unfold cnt1 σ
  split_ifs <;> first | omega | (congr 2; omega)

theorem sigQ_shift {Q t0 Δ : Nat} (v0 : Bool) (A B : List Nat) (hB : ∀ p ∈ B, t0 < p) (t : Nat) :
    sigQ Q v0 (A.map (sh t0 Δ)) (B.map (· + Δ)) t = sigQ Q v0 A B (σ t0 Δ t) := by
  unfold sigQ
  rw [List.countP_map, List.map_map]
  have e1 : (A.countP ((fun x => decide (x ≤ t)) ∘ sh t0 Δ)) = A.countP fun x => decide (x ≤ σ t0 Δ t) := by
    apply List.countP_congr
    intro θ _
    simp only [Function.comp, decide_eq_true_eq, sh_le_iff]
  have e2 : (B.map ((fun p => cnt1 Q p t) ∘ (· + Δ))) = B.map fun p => cnt1 Q p (σ t0 Δ t) := by
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp]
    exact cnt1_shift_σ (hB p hp) t
  rw [e1, e2]

/-- **The stretched periodic run is `stutB` of the original.** -/
theorem xQ_shift (Q t0 Δ : Nat) (enc : Nat → Option (Bool × List Nat)) (per : Nat → List Nat)
    (hper : ∀ n, ∀ p ∈ per n, t0 < p) :
    xQ Q (fun n => shiftE t0 Δ (enc n)) (fun n => (per n).map (· + Δ)) = stutB t0 Δ (xQ Q enc per) := by
  funext n t
  simp only [xQ, stutB, stut, pre_shift]
  exact sigQ_shift _ _ _ (hper n) t

/-- A node with no periodic part follows its prefix code. -/
theorem xQ_fin {Q : Nat} {enc : Nat → Option (Bool × List Nat)} {per : Nat → List Nat} {n : Nat} (h : per n = []) :
    xQ Q enc per n = sigL (enc n) := by
  funext t
  simp only [xQ, sigQ, h, List.map_nil, List.sum_nil, Nat.add_zero]
  cases e : enc n with
  | none => simp [pre, sigL]
  | some p => obtain ⟨b, ts⟩ := p; simp [pre, sigL]

/-- Every leaf of a period tree satisfies `P`. -/
def BTN.allLeaves (P : List Nat → Bool) : BTN → Bool
  | .lf v => P v
  | .nd l r => BTN.allLeaves P l && BTN.allLeaves P r

theorem BTN.get_all (P : List Nat → Bool) (hn : P [] = true) :
    ∀ (t : BTN) (d i : Nat), BTN.allLeaves P t = true → P (t.get d i) = true
  | .lf v, _, _, h => h
  | .nd _ _, 0, _, _ => hn
  | .nd l r, d + 1, i, h => by
    simp only [BTN.allLeaves, Bool.and_eq_true] at h
    simp only [BTN.get]
    split
    · exact BTN.get_all P hn l d _ h.1
    · exact BTN.get_all P hn r d _ h.2

end Formal.Target.CexRuntQ
