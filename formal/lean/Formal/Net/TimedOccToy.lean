import Formal.Net.TimedOcc
import Formal.Net.OccNetDec

/-!
# A toy instance of `TimedOcc`: the hypotheses can all hold at once (shard C, non-vacuity)

Two nodes: `0` is the environment (free), it rises once at time 10; `1` is a buffer gate reading node `0` with
read delay exactly 3 (`lo = hi = 3`). The certificate: one event each, `(1, 0)` caused by `(0, 0)`. The behaviour:
`x 0 t = (10 ≤ t)`, `x 1 t = (13 ≤ t)`, reads at `t - 3`, `t0 = 5`, `H = 3`. Every hypothesis of
`Timed.timed_follows` and `Timed.timed_live` is discharged here; the conclusions follow.
-/

namespace Formal.Net.OccNet.TimedToy
open Formal.Net.OccNet Formal.Net.OccNet.Timed

def N : TNet Nat := ⟨fun v => v == 1, fun v => if v = 1 then [0] else [], fun _ l => l.getD 0 false,
  fun _ _ => 3, fun _ _ => 3⟩
def envEn : Nat → (Nat → Bool) → Bool := fun v s => v == 0 && !(s 0)
def x : Nat → Nat → Bool := fun v t => if v = 0 then decide (10 ≤ t) else if v = 1 then decide (13 ≤ t) else false
def r : Nat → Nat → Nat → Nat := fun _ _ t => t - 3
def C : Cert Nat := ⟨fun u => if u ≤ 1 then 1 else 0, fun u _ => if u = 1 then [(0, 0)] else [], fun u _ => u⟩
def L : Nat → Nat → Nat → Nat := fun u _ w => if u = 1 ∧ w = 0 then 1 else if u = w ∧ u ≤ 1 then 1 else 0
def D : Nat → List Nat := fun v => if v = 1 then [1, 0] else [v]
def Sep : Nat → Nat → Nat → Nat → Option Nat := fun b m a k =>
  if b = 0 ∧ m = 0 ∧ a = 1 ∧ k = 0 then some 3 else if b = a ∧ m = k then some 0 else none

theorem hb : TBeh N envEn x r 5 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u s h1 h2; simp only [x]; split <;> (try split) <;> simp <;> omega
  · intro v w t hv hw ht
    simp only [N, beq_iff_eq] at hv; subst hv
    simp only [N, if_true, List.mem_singleton] at hw; subst hw
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [N, r] <;> omega
  · intro v w hv hw; simp [N]
  · intro v w t t' _ _ _ htt; simp only [r]; omega
  · intro v t hv ht
    simp only [N, beq_iff_eq] at hv; subst hv
    simp only [x, N, r, if_true, List.map_cons, List.map_nil, List.getD_cons_zero]
    by_cases h : 13 ≤ t
    · have : 10 ≤ t - 3 := by omega
      simp [h, this]
    · have : ¬ 10 ≤ t - 3 := by omega
      simp [h, this]
  · intro u t hu ht hch
    have hu' : ¬ u = 1 := by simpa [N] using hu
    simp only [envEn]
    by_cases h0 : u = 0
    · subst h0; simp only [x, if_true] at hch ⊢; simp at hch ⊢; omega
    · exfalso; apply hch; simp only [x]
      by_cases h1 : u = 1
      · exact absurd h1 hu'
      · simp [h0, h1]

theorem hT : TmOK C := by
  refine ⟨fun u k hk => ?_, fun u k hk p hp => ?_⟩
  · simp only [C] at hk; split at hk <;> omega
  · simp only [C] at hk hp
    by_cases h : u = 1
    · subst h; simp at hp; subst hp; simp [C]
    · simp [h] at hp

theorem hLs : LSound C L := by
  apply lsound_of_step hT
  intro u k w hk
  simp only [C] at hk
  by_cases hu : u ≤ 1
  · simp only [hu, if_true] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [L, causeBound, C]
    by_cases h1 : u = 1
    · subst h1; by_cases hw : w = 0
      · subst hw; simp
      · by_cases hw1 : w = 1
        · subst hw1; simp
        · simp [hw, hw1, Ne.symm hw, Ne.symm hw1]
    · have : u = 0 := by omega
      subst this; simp
  · simp only [hu, if_false] at hk; omega

theorem hS : SepOK N C Sep := by
  intro b m a k d _ h
  simp only [Sep] at h
  split at h
  · rename_i hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    simp at h; subst h
    right; left
    refine ⟨(0, 0), by simp [C], 0, by simp [Sep], ?_⟩
    simp [lo', reads, N]
  · split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp at h; left; exact ⟨rfl, rfl, h.symm⟩
    · cases h

theorem hTO : TO N C L D Sep := by
  intro v a b k ha hb' hk hL hlt
  by_cases hv : v = 1
  · subst hv
    simp only [D, if_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb'
    simp only [C] at hk
    rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
    · simp [lo', hi', reads, N] at hlt
    · refine ⟨3, ?_, ?_⟩
      · have hk0 : k = 0 := by simp at hk; omega
        subst hk0; simp [Sep, L]
      · simp [lo', hi', reads, N]
    · simp [lo', hi', reads, N] at hlt
    · simp [lo', hi', reads, N] at hlt
  · exfalso
    simp only [D, hv, if_false, List.mem_singleton] at ha hb'
    subst ha; subst hb'
    simp [lo', hi', reads, N, hv] at hlt

def Fl : Nat → List Bool → Bool := fun v l => if v = 1 then (l.getD 1 false != l.getD 0 false)
      else if v = 0 then (l.getD 0 false == false) else false

theorem hloc : ∀ v, LCheck (tEn N envEn) (fun w => x w 5) C L D v := by
  intro v
  have hF : ∀ v s, tEn N envEn v s = Fl v ((D v).map s) := by
    intro v s
    by_cases h1 : v = 1
    · subst h1; simp [tEn, N, D, Fl]
    · by_cases h0 : v = 0
      · subst h0; simp [tEn, N, D, envEn, Fl]
      · simp [tEn, N, D, envEn, Fl, h0, h1]
  have hs0 : (fun w => x w 5) = fun _ => false := by funext w; simp only [x]; split <;> (try split) <;> simp
  rw [hs0]
  by_cases h1 : v = 1
  · subst h1
    exact lcheck_of_enum hF 1 (by decide) (by decide) (by intro k hk p hp; simp [C] at hp; simp [D, hp]) (by decide)
  · by_cases h0 : v = 0
    · subst h0
      exact lcheck_of_enum hF 0 (by decide) (by decide) (by intro k hk p hp; simp [C] at hp) (by decide)
    · intro n _ _
      simp only [hF, h0, h1, if_false]
      simp only [Enabled, C]
      have : ¬ v ≤ 1 := by omega
      simp [this, Fl, h0, h1]

/-- **Non-vacuity:** the toy behaviour meets every hypothesis, so `timed_follows` applies; e.g. at time 20 the
count vector is an ideal and every change was a certified event. -/
theorem toy_follows : (∀ τ, τ ≤ 20 → Ideal C (fun u => cnt x 5 u τ)) ∧
    (∀ v s, 5 < s → s ≤ 20 → x v s ≠ x v (s - 1) → ChangeOK N C x 5 r v s) :=
  timed_follows hb hT hLs hS hTO hloc 20

end Formal.Net.OccNet.TimedToy
