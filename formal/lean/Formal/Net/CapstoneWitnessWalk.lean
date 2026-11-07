import Formal.Net.CapstoneCut
import Formal.Net.CapstoneWitnessTok

/-!
# Probe C-8t: a Boolean checker for H_WALK (`WalkOK`)

`walkChk σ om F s` follows the walk from state `s` for at most `F` steps, checks the
arbiter-arrival condition of `WalkOK` at every step, and asks that the walk has ended
(`cur = none`) after them. `walkOK_of`: if it holds from `walk σ 0`, `WalkOK σ om` holds (the
walk is constant once it has ended, so the finitely many checked steps are all of them).
-/

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

def arrOK (om : Nat → Nat → Bool) (s : WS) : Bool :=
  match s.cur with
  | none => true
  | some d => match opAt (consOf d) with
    | .amerge _ y z w => om w (s.W z) == decide (d = y)
    | _ => true

def walkChk (σ : Fin NC → Nat → Nat) (om : Nat → Nat → Bool) : Nat → WS → Bool
  | 0, s => s.cur.isNone
  | f + 1, s => arrOK om s && walkChk σ om f (wstep σ s)

theorem walk_stop (σ : Fin NC → Nat → Nat) {p : Nat} (h : (walk σ p).cur = none) :
    ∀ q, (walk σ (p + q)).cur = none := by
  intro q
  induction q with
  | zero => exact h
  | succ q ih =>
    show (wstep σ (walk σ (p + q))).cur = none
    unfold wstep; rw [ih]; exact ih

theorem walkChk_sound (σ : Fin NC → Nat → Nat) (om : Nat → Nat → Bool) :
    ∀ F p, walkChk σ om F (walk σ p) = true → ∀ q, arrOK om (walk σ (p + q)) = true := by
  intro F
  induction F with
  | zero =>
    intro p h q
    simp only [walkChk, Option.isNone_iff_eq_none] at h
    unfold arrOK; rw [walk_stop σ h q]
  | succ F ih =>
    intro p h q
    simp only [walkChk, Bool.and_eq_true] at h
    cases q with
    | zero => exact h.1
    | succ q =>
      have := ih (p + 1) h.2 q
      rwa [show p + 1 + q = p + (q + 1) by omega] at this

theorem walkOK_of {σ : Fin NC → Nat → Nat} {om : Nat → Nat → Bool} {F : Nat}
    (h : walkChk σ om F (walk σ 0) = true) : WalkOK σ om := by
  intro p d x y z w hc ho
  have := walkChk_sound σ om F 0 h p
  rw [Nat.zero_add] at this
  unfold arrOK at this
  rw [hc] at this
  simp only [ho, beq_iff_eq] at this
  exact this

end Formal.Net.CapNet.Wit
