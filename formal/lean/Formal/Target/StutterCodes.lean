import Formal.Target.SpecStutter
import Formal.Net.CexPS72.KBase

/-!
# Formal.Target.StutterCodes — the stutter lemma on coded runs (shard A, 2026-11-07)

Coded signals (`Formal.Net.CexPS72.sigL`: an initial value toggled at listed times) are stretched by shifting every
transition after `t0` by `Δ` (`shiftE`); `sigL_shift` says that is `Stutter.stut`. `quiet_of_codes`: a coded run with
no transition in `(t0 - Q, t0]` is `Stutter.Quiet`. `BTL.allLeaves` / `lookL_all`: a property of every leaf of the
chunk trees holds for every node code. `arbChkE_shift`: an arbiter check on codes survives the shift when no
transition of its nodes lies in `(t0 - T, t0]`.
-/

namespace Formal.Target.StutterCodes
open Formal.Target Formal.Target.Stutter Formal.Net.CexPS72

def sh (t0 Δ θ : Nat) : Nat := if θ ≤ t0 then θ else θ + Δ

def shiftE (t0 Δ : Nat) : Option (Bool × List Nat) → Option (Bool × List Nat)
  | none => none
  | some (b, ts) => some (b, ts.map (sh t0 Δ))

theorem thrL_shift (t0 Δ : Nat) (e : Option (Bool × List Nat)) : thrL (shiftE t0 Δ e) = (thrL e).map (sh t0 Δ) := by
  cases e with
  | none => rfl
  | some p => obtain ⟨b, ts⟩ := p; rfl

theorem sh_le_iff (t0 Δ θ t : Nat) : sh t0 Δ θ ≤ t ↔ θ ≤ σ t0 Δ t := by
  simp only [sh, σ]; split_ifs <;> omega

theorem sigL_shift (t0 Δ : Nat) (e : Option (Bool × List Nat)) (t : Nat) :
    sigL (shiftE t0 Δ e) t = sigL e (σ t0 Δ t) := by
  cases e with
  | none => rfl
  | some p =>
    obtain ⟨b, ts⟩ := p
    simp only [shiftE, sigL, List.countP_map]
    congr 3
    apply List.countP_congr
    intro θ _
    simp only [Function.comp, decide_eq_true_eq, sh_le_iff]

/-- The stretched coded run is `stutB` of the original. -/
theorem stutB_codes (t0 Δ : Nat) (enc : Nat → Option (Bool × List Nat)) :
    (fun n => sigL (shiftE t0 Δ (enc n))) = stutB t0 Δ (fun n => sigL (enc n)) := by
  funext n t
  simp only [stutB, stut, sigL_shift]

theorem quiet_of_codes (enc : Nat → Option (Bool × List Nat)) (t0 Q : Nat)
    (h : ∀ n, ∀ θ ∈ thrL (enc n), θ ≤ t0 - Q ∨ t0 < θ) : Quiet (fun n => sigL (enc n)) t0 Q := by
  intro n u h1 h2
  apply sigL_eq
  intro θ hθ
  rcases h n θ hθ with h3 | h3 <;> omega

/-- Every leaf of a chunk tree satisfies `P`. -/
def BTL.allLeaves (P : Option (Bool × List Nat) → Bool) : BTL → Bool
  | .lf v => P v
  | .nd l r => BTL.allLeaves P l && BTL.allLeaves P r

theorem BTL.get_all (P : Option (Bool × List Nat) → Bool) (hn : P none = true) :
    ∀ (t : BTL) (d i : Nat), BTL.allLeaves P t = true → P (t.get d i) = true
  | .lf v, _, _, h => h
  | .nd _ _, 0, _, _ => hn
  | .nd l r, d + 1, i, h => by
    simp only [BTL.allLeaves, Bool.and_eq_true] at h
    simp only [BTL.get]
    split
    · exact BTL.get_all P hn l d _ h.1
    · exact BTL.get_all P hn r d _ h.2

theorem lookL_all (P : Option (Bool × List Nat) → Bool) (hn : P none = true) (tl : List BTL) (C d : Nat)
    (h : tl.all (BTL.allLeaves P) = true) (n : Nat) : P (lookL tl C d n) = true := by
  unfold lookL
  apply BTL.get_all P hn
  rw [List.getD_eq_getElem?_getD]
  cases h' : tl[n / C]? with
  | none => exact hn
  | some t => exact List.all_eq_true.mp h t (List.mem_of_getElem? h')

/-- A generic arbiter check on codes (shard C's `arbChk`, any code function). -/
def arbChkE (enc : Nat → Option (Bool × List Nat)) (T : Nat) (a : ArbNodes) : Bool :=
  (thrL (enc a.q)).all fun τ => a.ins.any fun n =>
    (thrL (enc n)).any fun θ => decide (τ < θ + T) && decide (θ ≤ τ) && decide (1 ≤ θ)

theorem arbChkE_shift (enc : Nat → Option (Bool × List Nat)) (T t0 Δ : Nat) (a : ArbNodes)
    (h : arbChkE enc T a = true)
    (hq : ∀ n ∈ a.q :: a.ins, ∀ θ ∈ thrL (enc n), θ + T ≤ t0 ∨ t0 < θ) :
    arbChkE (fun n => shiftE t0 Δ (enc n)) T a = true := by
  simp only [arbChkE, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, thrL_shift,
    List.mem_map] at h ⊢
  rintro _ ⟨τ, hτ, rfl⟩
  obtain ⟨n, hn, θ, hθ, ⟨h1, h2⟩, h3⟩ := h τ hτ
  refine ⟨n, hn, sh t0 Δ θ, ⟨θ, hθ, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · have := hq a.q List.mem_cons_self τ hτ
    have := hq n (List.mem_cons_of_mem _ hn) θ hθ
    simp only [sh]; split_ifs <;> omega
  · simp only [sh]; split_ifs <;> omega
  · simp only [sh]; split_ifs <;> omega

theorem incr_shift (t0 Δ : Nat) (ts : List Nat) (h : ts.Pairwise (· < ·)) : (ts.map (sh t0 Δ)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact h.imp fun {a b} hab => by simp only [sh]; split_ifs <;> omega

end Formal.Target.StutterCodes
