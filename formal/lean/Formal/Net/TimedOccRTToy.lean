import Formal.Net.TimedOccRT
import Formal.Net.OccNetDec

/-!
# A toy instance of `TimedOccRT`: an RT edge justified through a common ancestor (shard C, non-vacuity)

Three nodes: `0` the environment (rises at 10 ps), `1` a buffer of `0` with read delay exactly 1, `2` a buffer of
`0` with read delay exactly 5. The full certificate orders `(1, 0)` before `(2, 0)` although `2` does not read `1`
(an RT edge); the physical certificate does not. The edge is justified by the fourth form of `SepOKR`: from the
common ancestor `(0, 0)`, `(2, 0)` comes at least 5 ps later (`Sep`, physical) and `(1, 0)` at most 1 ps later
(`Up`), so `(1, 0)` precedes `(2, 0)` by at least 4 ps. Every hypothesis of `TimedR.timedR_follows` is discharged.
-/

namespace Formal.Net.OccNet.TimedRToy
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR

def lo0 : Nat → Nat := fun v => if v = 2 then 5 else 1
def N : TNet Nat := ⟨fun v => v == 1 || v == 2, fun v => if v = 1 ∨ v = 2 then [0] else [], fun _ l => l.getD 0 false,
  fun v _ => lo0 v, fun v _ => lo0 v⟩
def dat : Nat → Bool := fun _ => false
def envEn : Nat → (Nat → Bool) → Bool := fun v s => v == 0 && !(s 0)
def x : Nat → Nat → Bool := fun v t =>
  if v = 0 then decide (10 ≤ t) else if v = 1 then decide (11 ≤ t) else if v = 2 then decide (15 ≤ t) else false
def r : Nat → Nat → Nat → Nat := fun v _ t => t - lo0 v
def CP : Cert Nat := ⟨fun u => if u ≤ 2 then 1 else 0, fun u _ => if u = 1 ∨ u = 2 then [(0, 0)] else [], fun u _ => u⟩
def CF : Cert Nat := ⟨fun u => if u ≤ 2 then 1 else 0,
  fun u _ => if u = 1 then [(0, 0)] else if u = 2 then [(0, 0), (1, 0)] else [], fun u _ => u⟩
def L : Nat → Nat → Nat → Nat := fun u _ w =>
  if u ≤ 2 ∧ w = u then 1 else if (u = 1 ∨ u = 2) ∧ w = 0 then 1 else if u = 2 ∧ w = 1 then 1 else 0
def D : Nat → List Nat := fun v => if v = 1 ∨ v = 2 then [v, 0] else [v]
def Sep : Nat → Nat → Nat → Nat → Option Nat := fun b m a k =>
  if b = 0 ∧ m = 0 ∧ a = 2 ∧ k = 0 then some 5 else if b = 1 ∧ m = 0 ∧ a = 2 ∧ k = 0 then some 4
  else if b = a ∧ m = k then some 0 else none
def Up : Nat × Nat → Nat × Nat → Option Nat := fun e0 e =>
  if e0 = (0, 0) ∧ e = (1, 0) then some 1 else if e = e0 then some 0 else none
def cl : List (Claim Nat) := []
def gd : Nat → Nat → List (Guard Nat) := fun _ _ => []

theorem hb : TBehX N dat envEn x r 5 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u s _ h1 h2; simp only [x]; split <;> (try split) <;> (try split) <;> simp <;> omega
  · intro v w t hv hw ht
    simp only [N, Bool.or_eq_true, beq_iff_eq] at hv
    have hw0 : w = 0 := by rcases hv with rfl | rfl <;> simpa [N] using hw
    subst hw0
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [N, r, lo0] <;> split <;> omega
  · intro v w _ _; simp only [N, lo0]; split <;> omega
  · intro v w t t' _ _ _ htt; simp only [r]; omega
  · intro v t hv ht
    simp only [N, Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with rfl | rfl
    · simp only [x, N, r, lo0, List.map_cons, List.map_nil, List.getD_cons_zero]
      by_cases h : 11 ≤ t
      · have : 10 ≤ t - 1 := by omega
        simp [h, this]
      · have : ¬ 10 ≤ t - 1 := by omega
        simp [h, this]
    · simp only [x, N, r, lo0, List.map_cons, List.map_nil, List.getD_cons_zero]
      by_cases h : 15 ≤ t
      · have : 10 ≤ t - 5 := by omega
        simp [h, this]
      · have : ¬ 10 ≤ t - 5 := by omega
        simp [h, this]
  · intro u t hu _ ht hch
    have hu1 : ¬ u = 1 := by intro h; subst h; simp [N] at hu
    have hu2 : ¬ u = 2 := by intro h; subst h; simp [N] at hu
    simp only [envEn]
    by_cases h0 : u = 0
    · subst h0; simp only [x, if_true] at hch ⊢; simp at hch ⊢; omega
    · exfalso; apply hch; simp [x, h0, hu1, hu2]

theorem tm_ok (C : Cert Nat) (hlen : C.len = fun u => if u ≤ 2 then 1 else 0) (htm : C.tm = fun u _ => u)
    (hc : ∀ u k, ∀ p ∈ C.causes u k, p.2 = 0 ∧ p.1 < u ∧ p.1 ≤ 2) : TmOK C := by
  refine ⟨fun u k hk => ?_, fun u k hk p hp => ?_⟩
  · rw [hlen] at hk; simp only at hk; split at hk <;> omega
  · obtain ⟨h1, h2, h3⟩ := hc u k p hp
    rw [hlen, htm]; simp [h1, h2, h3]

theorem hTP : TmOK CP := tm_ok CP rfl rfl (by
  intro u k p hp; simp only [CP] at hp; split at hp
  · rename_i h; simp at hp; subst hp; simp; omega
  · simp at hp)

theorem hTF : TmOK CF := tm_ok CF rfl rfl (by
  intro u k p hp; simp only [CF] at hp
  split at hp
  · rename_i h; subst h; simp at hp; subst hp; simp
  · split at hp
    · rename_i _ h; subst h; simp at hp; rcases hp with rfl | rfl <;> simp
    · simp at hp)

theorem hLs : LSound CF L := by
  apply lsound_of_step hTF
  intro u k w hk
  simp only [CF] at hk
  by_cases hu : u ≤ 2
  · simp only [hu, if_true] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [L, causeBound, CF]
    have : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases this with rfl | rfl | rfl <;>
      (by_cases hw0 : w = 0 <;> by_cases hw1 : w = 1 <;> by_cases hw2 : w = 2 <;> simp_all <;> omega)
  · simp only [hu, if_false] at hk; omega

theorem hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false := fun _ _ _ _ _ _ => rfl

theorem hUp : UpOK N dat CP Up := by
  intro e0 e d h
  simp only [Up] at h
  split at h
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := hc
    simp at h; subst h
    right
    refine ⟨by simp [N], rfl, by simp [CP], fun p hp => ?_, fun h => absurd h (by simp)⟩
    simp [CP] at hp; subst hp
    exact ⟨0, by simp [Up], by simp [hi', reads, N, lo0]⟩
  · split at h
    · rename_i _ hc; left; exact hc
    · cases h

theorem hS : SepOKR N CP Sep Up := by
  intro b m a k d hk h
  simp only [Sep] at h
  split at h
  · rename_i hc; obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    simp at h; subst h
    right; left
    exact ⟨(0, 0), by simp [CP], 0, by simp [Sep], by simp [lo', reads, N, lo0]⟩
  · split at h
    · rename_i _ hc; obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp at h; subst h
      right; right; right
      exact ⟨by omega, (0, 0), 5, 1, by simp [Sep], by simp [Up], by omega, by simp [CP]⟩
    · split at h
      · rename_i _ _ hc; obtain ⟨rfl, rfl⟩ := hc; simp at h; left; exact ⟨rfl, rfl, h.symm⟩
      · cases h

theorem hTO : TO N CF L D Sep := by
  intro v a b k ha hb' hk hL hlt
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ 3 ≤ v := by omega
  rcases hv with rfl | rfl | rfl | hv
  · exfalso; simp [D] at ha hb'; subst ha; subst hb'; simp [lo', hi', reads, N] at hlt
  · exfalso; simp [D] at ha hb'
    rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp [lo', hi', reads, N, lo0] at hlt
  · simp [D] at ha hb'
    simp only [CF] at hk
    rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
    · exfalso; simp [lo', hi', reads, N, lo0] at hlt
    · refine ⟨5, ?_, ?_⟩
      · have hk0 : k = 0 := by simp at hk; omega
        subst hk0; simp [Sep, L]
      · simp [lo', hi', reads, N, lo0]
    · exfalso; simp [L] at hL
    · exfalso; simp [lo', hi', reads, N, lo0] at hlt
  · exfalso
    have h1 : ¬ v = 1 := by omega
    have h2 : ¬ v = 2 := by omega
    simp [D, h1, h2] at ha hb'; subst ha; subst hb'
    simp [lo', hi', reads, N, h1, h2] at hlt

def Fl : Nat → List Bool → Bool := fun v l =>
  if v = 1 ∨ v = 2 then (l.getD 1 false != l.getD 0 false) else if v = 0 then (l.getD 0 false == false) else false

theorem hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w 5) CP L D cl gd v := by
  intro v _
  have hF : ∀ v s, tEn N envEn v s = Fl v ((D v).map s) := by
    intro v s
    by_cases h1 : v = 1
    · subst h1; simp [tEn, N, D, Fl]
    · by_cases h2 : v = 2
      · subst h2; simp [tEn, N, D, Fl]
      · by_cases h0 : v = 0
        · subst h0; simp [tEn, N, D, envEn, Fl]
        · simp [tEn, N, D, envEn, Fl, h0, h1, h2]
  have hs0 : (fun w => x w 5) = fun _ => false := by
    funext w; simp only [x]; split <;> (try split) <;> (try split) <;> simp
  rw [hs0]
  have hL : LCheck (tEn N envEn) (fun _ => false) CP L D v := by
    have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ 3 ≤ v := by omega
    rcases hv with rfl | rfl | rfl | hv
    · exact lcheck_of_enum hF 0 (by decide) (by decide) (by intro k hk p hp; simp [CP] at hp) (by decide)
    · exact lcheck_of_enum hF 1 (by decide) (by decide) (by intro k hk p hp; simp [CP] at hp; simp [D, hp]) (by decide)
    · exact lcheck_of_enum hF 2 (by decide) (by decide) (by intro k hk p hp; simp [CP] at hp; simp [D, hp]) (by decide)
    · intro n _ _
      have h0 : ¬ v = 0 := by omega
      have h1 : ¬ v = 1 := by omega
      have h2 : ¬ v = 2 := by omega
      have h3 : ¬ v ≤ 2 := by omega
      simp [hF, Fl, h0, h1, h2, Enabled, CP, h3]
  intro n hn hc bb _
  have hmix : mix dat (st (fun _ => false) n) bb = st (fun _ => false) n := by funext w; simp [mix, dat]
  rw [hmix]; exact hL n hn hc

/-- **Non-vacuity of the RT extension:** every hypothesis holds, so `timedR_follows` applies. -/
theorem toyR_follows : (∀ τ, τ ≤ 30 → Ideal CF (fun u => cntE dat x 5 u τ)) ∧ SepSound x 5 Sep 30 :=
  have h := timedR_follows (N := N) (dat := dat) (envEn := envEn) (x := x) (r := r) (t0 := 5) (H := 5) (CF := CF) (CP := CP)
    (L := L) (D := D) (Sep := Sep) (cl := cl) (gd := gd) (Up := Up)
    hb hTP hLs hSE hTO (fun _ _ _ => rfl) hloc (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ g hg => by simp [gd] at hg) hUp hS hTF
    (by
      intro u k p hk hp hnp
      simp only [CF] at hk hp
      by_cases h1 : u = 1
      · subst h1; simp [CP] at hp hnp; exact absurd hp hnp
      · by_cases h2 : u = 2
        · subst h2; simp [CP] at hp hnp hk
          have hk0 : k = 0 := by omega
          subst hk0
          rcases hp with rfl | rfl
          · simp at hnp
          · exact ⟨4, by simp [Sep], by omega⟩
        · simp [h1, h2] at hp)
    (by simp [cl]) (by simp [cl]) (by simp [cl]) (fun u h => by simp [dat] at h) 30
  ⟨h.1, h.2.2.2⟩

end Formal.Net.OccNet.TimedRToy
