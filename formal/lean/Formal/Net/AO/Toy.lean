import Formal.Net.AO.Dec

/-!
# A toy instance of the AND-OR timed theorem: an OR gate fed by two inputs at different times (non-vacuity)

Nodes: `0`, `1` environment inputs rising at 10 ps and 12 ps; `2` an OR gate reading both with read delay 1. The OR
fires at 11 ps on the first input; the second input's rise is absorbed. Its event has two alternatives, `[(0,0)]`
and `[(1,0)]`, which an AND-only certificate cannot express. Every hypothesis of `AO.timedA_follows` is discharged.
-/

namespace Formal.Net.AO.Toy
open Formal.Net.AO Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR
  Formal.Net.OccNet.TimedU

def N : TNet Nat := ⟨fun v => v == 2, fun v => if v = 2 then [0, 1] else [], fun _ l => l.getD 0 false || l.getD 1 false,
  fun _ _ => 1, fun _ _ => 1⟩
def dat : Nat → Bool := fun _ => false
def envEn : Nat → (Nat → Bool) → Bool := fun v s => (v == 0 && !(s 0)) || (v == 1 && !(s 1))
def x : Nat → Nat → Bool := fun v t =>
  if v = 0 then decide (10 ≤ t) else if v = 1 then decide (12 ≤ t) else if v = 2 then decide (11 ≤ t) else false
def r : Nat → Nat → Nat → Nat := fun _ _ t => t - 1
def C : Cert Nat := ⟨fun u => if u ≤ 2 then 1 else 0, fun u _ => if u = 2 then [[(0, 0)], [(1, 0)]] else [[]],
  fun u _ => u⟩
def L : Nat → Nat → Nat → Nat → Nat := fun _ a _ b => if a = b ∧ a ≤ 2 then 1 else 0
def D : Nat → List Nat := fun v => if v = 2 then [2, 0, 1] else [v]
def Z : Nat → List Nat := fun _ => []
def Sep : Nat → Nat → Nat → Nat → Option Nat := fun _ _ _ _ => none
def Up : Nat × Nat → Nat × Nat → Option Nat := fun _ _ => none
def cl : List (Claim Nat) := []
def gd : Nat → Nat → List (Guard Nat) := fun _ _ => []

theorem hb : TBehX N dat envEn x r 5 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u s _ h1 h2; simp only [x]; split <;> (try split) <;> (try split) <;> simp <;> omega
  · intro v w t hv hw ht
    simp only [N, beq_iff_eq] at hv; subst hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [N, r] <;> omega
  · intro v w _ _; simp [N]
  · intro v w t t' _ _ _ htt; simp only [r]; omega
  · intro v t hv ht
    simp only [N, beq_iff_eq] at hv; subst hv
    simp only [x, N, r, if_true, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    simp
    by_cases h : 11 ≤ t
    · have : 10 ≤ t - 1 := by omega
      simp [h, this]
    · have : ¬ 10 ≤ t - 1 := by omega
      have h2 : ¬ 12 ≤ t - 1 := by omega
      simp [h, this, h2]
  · intro u t hu _ ht hch
    simp only [envEn]
    by_cases h0 : u = 0
    · subst h0; simp only [x, if_true] at hch ⊢; simp at hch ⊢; omega
    · by_cases h1 : u = 1
      · subst h1; simp only [x] at hch ⊢; simp at hch ⊢; omega
      · exfalso; apply hch
        have h2 : ¬ u = 2 := by intro h; subst h; simp [N] at hu
        simp [x, h0, h1, h2]

theorem hT : TmOK C := by
  refine ⟨fun u k hk => ?_, fun u k hk alt halt p hp => ?_⟩
  · simp only [C] at hk; split at hk <;> omega
  · simp only [C] at hk halt
    by_cases h : u = 2
    · subst h; simp at halt; rcases halt with rfl | rfl <;> simp at hp <;> subst hp <;> simp [C]
    · simp [h] at halt; subst halt; simp at hp

theorem hLs : ∀ v, LSound C (L v) := by
  intro v
  apply lsound_of_step hT
  intro u k w hk
  left
  simp only [L, C] at hk ⊢
  split
  · rename_i h; obtain ⟨rfl, _⟩ := h; simp
  · exact Nat.zero_le _

def Fx : Nat → List Bool → List Bool → Bool := fun v l _ =>
  if v = 2 then ((l.getD 1 false || l.getD 2 false) != l.getD 0 false)
  else if v = 0 ∨ v = 1 then !(l.getD 0 false) else false

theorem hF : ∀ v s, tEn N envEn v s = Fx v ((D v).map s) ((Z v).map s) := by
  intro v s
  by_cases h2 : v = 2
  · subst h2; simp [tEn, N, D, Fx]
  · by_cases h0 : v = 0
    · subst h0; simp [tEn, N, D, Fx, envEn]
    · by_cases h1 : v = 1
      · subst h1; simp [tEn, N, D, Fx, envEn]
      · simp [tEn, N, D, Fx, envEn, h0, h1, h2]

theorem hloc : ∀ v, dat v = false → LCheckXA N dat envEn (fun w => x w 5) C (L v) D cl gd v := by
  intro v _
  have hs0 : (fun w => x w 5) = fun _ => false := by
    funext w; simp only [x]; split <;> (try split) <;> (try split) <;> simp
  rw [hs0]
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ 3 ≤ v := by omega
  rcases hv with rfl | rfl | rfl | hv
  · exact lcheckXA_of_enum N dat envEn _ C cl gd hF 0 (by decide) (by decide) (by decide)
      (by intro k hk alt halt p hp; simp [C] at halt; subst halt; simp at hp) (by decide) (by decide) (by decide)
      (by intro z hz; simp [Z] at hz) (by decide)
  · exact lcheckXA_of_enum N dat envEn _ C cl gd hF 1 (by decide) (by decide) (by decide)
      (by intro k hk alt halt p hp; simp [C] at halt; subst halt; simp at hp) (by decide) (by decide) (by decide)
      (by intro z hz; simp [Z] at hz) (by decide)
  · exact lcheckXA_of_enum N dat envEn _ C cl gd hF 2 (by decide) (by decide) (by decide)
      (by intro k hk alt halt p hp; simp [C] at halt
          rcases halt with rfl | rfl <;> simp at hp <;> subst hp <;> simp [D]) (by decide) (by decide) (by decide)
      (by intro z hz; simp [Z] at hz) (by decide)
  · intro n _ _ _ bb _
    have h0 : ¬ v = 0 := by omega
    have h1 : ¬ v = 1 := by omega
    have h2 : ¬ v = 2 := by omega
    have h3 : ¬ v ≤ 2 := by omega
    rw [hF]
    simp [Fx, h0, h1, h2, Enabled, C, h3]

/-- **Non-vacuity of the AND-OR timed theorem.** -/
theorem toyA_follows : ∀ τ, τ ≤ 30 → Ideal C (fun u => cntE dat x 5 u τ) := by
  have h := timedA_follows (N := N) (dat := dat) (envEn := envEn) (x := x) (r := r) (t0 := 5) (H := 1) (CF := C)
    (CP := C) (L := L) (D := D) (Sep := Sep) (cl := cl) (gd := gd) (Up := Up)
    hb hT hLs (by intro b m a k d h; simp [Sep] at h)
    (by intro v a b k ha hb hab hk hL hlt; exfalso; simp only [L] at hL; split at hL
        · rename_i h; exact hab h.1
        · omega)
    (fun _ _ _ => rfl) hloc (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ g hg => by simp [gd] at hg)
    (by intro e0 e d h; simp [Up] at h) (by intro b m a k d _ h; simp [Sep] at h) hT
    (by intro u k _ altP haltP; exact ⟨altP, haltP, fun p hp => Or.inl hp⟩)
    (by simp [cl]) (by simp [cl]) (by simp [cl]) (fun u h => by simp [dat] at h) 30
  exact h.1

end Formal.Net.AO.Toy
