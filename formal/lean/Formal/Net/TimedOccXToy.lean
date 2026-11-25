import Formal.Net.TimedOccDecX

/-!
# A toy instance of `TimedOccX`: a latch, a data claim and a guarded read (shard C, non-vacuity)

Nodes: `0` the request (environment, rises at 10 ps), `1` the data input (environment, constant true, a claim),
`2` a latch `Q = en ? D : Q` (pins `D`, `en = req`, feedback; read delays 1), `3` a control gate `y = req ∧ Q`
(reads `req` with delay 3, `Q` with delay 1: the data arrives before the request, bundled data). The certificate:
events `(0, 0)` and `(3, 0)` (caused by `(0, 0)`); claims: `D` true for ever, `Q` true from 1 ps after the request;
`y` uses `Q` only once it has read the request (a guard). Every hypothesis of `TimedX.timedX_follows` is
discharged.
-/

namespace Formal.Net.OccNet.TimedXToy
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX

def N : TNet Nat := ⟨fun v => v == 2 || v == 3,
  fun v => if v = 2 then [1, 0, 2] else if v = 3 then [0, 2] else [],
  fun v l => if v = 2 then (if l.getD 1 false then l.getD 0 false else l.getD 2 false)
    else (l.getD 0 false && l.getD 1 false),
  fun v w => if v = 3 ∧ w = 0 then 3 else 1, fun v w => if v = 3 ∧ w = 0 then 3 else 1⟩
def dat : Nat → Bool := fun v => v == 1 || v == 2
def envEn : Nat → (Nat → Bool) → Bool := fun v s => v == 0 && !(s 0)
def x : Nat → Nat → Bool := fun v t =>
  if v = 0 then decide (10 ≤ t) else if v = 1 then true else if v = 2 then decide (11 ≤ t)
  else if v = 3 then decide (13 ≤ t) else false
def r : Nat → Nat → Nat → Nat := fun v w t => if v = 3 ∧ w = 0 then t - 3 else t - 1
def C : Cert Nat := ⟨fun u => if u = 0 ∨ u = 3 then 1 else 0, fun u _ => if u = 3 then [(0, 0)] else [], fun u _ => u⟩
def L : Nat → Nat → Nat → Nat := fun u _ w => if (u = 0 ∨ u = 3) ∧ w = u then 1 else if u = 3 ∧ w = 0 then 1 else 0
def D : Nat → List Nat := fun v => if v = 3 then [3, 0] else if v = 1 ∨ v = 2 then [] else [v]
def Z : Nat → List Nat := fun v => if v = 3 then [2] else if v = 2 then [1, 0, 2] else []
def Sep : Nat → Nat → Nat → Nat → Option Nat := fun b m a k =>
  if b = 0 ∧ m = 0 ∧ a = 3 ∧ k = 0 then some 3 else if b = 0 ∧ m = 1 ∧ a = 0 ∧ k = 1 then some 100
  else if b = a ∧ m = k ∧ (a = 0 ∨ a = 3) then some 0 else none
def cD : Claim Nat := ⟨1, true, none, 0, none, 0⟩
def cQ : Claim Nat := ⟨2, true, some (0, 0), 1, some (0, 1), 0⟩
def cl : List (Claim Nat) := [cD, cQ]
def gd : Nat → Nat → List (Guard Nat) := fun v z => if v = 3 ∧ z = 2 then [⟨1, some (0, 0), some (0, 1)⟩] else []

theorem hb : TBehX N dat envEn x r 5 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u s hu h1 h2
    simp only [dat, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hu
    simp only [x, hu.1, hu.2, if_false]; split <;> (try split) <;> simp <;> omega
  · intro v w t hv hw ht
    simp only [N, Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with rfl | rfl
    · have : w ≠ 0 ∨ True := Or.inr trivial
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [N, r] <;> (try split) <;> omega
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [N, r] <;> (try split) <;> omega
  · intro v w _ _; simp only [N]; split <;> omega
  · intro v w t t' _ _ _ htt; simp only [r]; split <;> omega
  · intro v t hv ht
    simp only [N, Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with rfl | rfl
    · simp only [x, N, r, if_true, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
      simp
      by_cases h : 11 ≤ t
      · have : 10 ≤ t - 1 := by omega
        simp [h, this]
      · have : ¬ 10 ≤ t - 1 := by omega
        have h2 : ¬ 11 ≤ t - 1 := by omega
        simp [h, this, h2]
    · simp only [x, N, r, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
      simp
      by_cases h : 13 ≤ t
      · have : 10 ≤ t - 3 := by omega
        have h2 : 11 ≤ t - 1 := by omega
        simp [h, this, h2]
      · have : ¬ 10 ≤ t - 3 := by omega
        simp [h, this]
  · intro u t hu hdu ht hch
    simp only [envEn]
    by_cases h0 : u = 0
    · subst h0; simp only [x, if_true] at hch ⊢; simp at hch ⊢; omega
    · exfalso; apply hch
      have h2 : ¬ u = 2 := by intro h; subst h; simp [N] at hu
      have h3 : ¬ u = 3 := by intro h; subst h; simp [N] at hu
      have h1 : ¬ u = 1 := by intro h; subst h; simp [dat] at hdu
      simp [x, h0, h1, h2, h3]

theorem hT : TmOK C := by
  refine ⟨fun u k hk => ?_, fun u k hk p hp => ?_⟩
  · simp only [C] at hk; split at hk <;> omega
  · simp only [C] at hk hp
    by_cases h : u = 3
    · subst h; simp at hp; subst hp; simp [C]
    · simp [h] at hp

theorem hLs : LSound C L := by
  apply lsound_of_step hT
  intro u k w hk
  simp only [C] at hk
  by_cases hu : u = 0 ∨ u = 3
  · simp only [hu, if_true] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [L, causeBound, C]
    rcases hu with rfl | rfl <;>
      (by_cases hw0 : w = 0 <;> by_cases hw3 : w = 3 <;> simp_all <;> omega)
  · simp only [hu, if_false] at hk; omega

theorem hS : SepOK N C Sep := by
  intro b m a k d hk h
  simp only [Sep] at h
  split at h
  · rename_i hc; obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    simp at h; subst h
    right; left
    exact ⟨(0, 0), by simp [C], 0, by simp [Sep], by simp [lo', reads, N]⟩
  · split at h
    · rename_i _ hc; obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      exfalso; simp [C] at hk
    · split at h
      · rename_i _ _ hc; obtain ⟨rfl, rfl, _⟩ := hc; simp at h; left; exact ⟨rfl, rfl, h.symm⟩
      · cases h

theorem hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false := by
  intro b m a k d h
  simp only [Sep] at h
  split at h
  · rename_i hc; obtain ⟨_, _, rfl, _⟩ := hc; rfl
  · split at h
    · rename_i _ hc; obtain ⟨_, _, rfl, _⟩ := hc; rfl
    · split at h
      · rename_i _ _ hc
        obtain ⟨rfl, rfl, ha⟩ := hc
        rcases ha with rfl | rfl <;> rfl
      · cases h

theorem hDE : ∀ v u, u ∈ D v → dat u = false := by
  intro v u h
  simp only [D] at h
  split at h
  · simp at h; rcases h with rfl | rfl <;> rfl
  · split at h
    · simp at h
    · rename_i _ hv; simp at h; subst h; simp [dat]; omega

theorem hTO : TO N C L D Sep := by
  intro v a b k ha hb' hk hL hlt
  by_cases hv : v = 3
  · subst hv
    simp [D] at ha hb'
    simp only [C] at hk
    rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
    · exfalso; simp [lo', hi', reads, N] at hlt
    · refine ⟨3, ?_, ?_⟩
      · have hk0 : k = 0 := by simp at hk; omega
        subst hk0; simp [Sep, L]
      · simp [lo', hi', reads, N]
    · exfalso; simp [L] at hL
    · exfalso; simp [lo', hi', reads, N] at hlt
  · exfalso
    simp only [D, hv, if_false] at ha hb'
    split at ha
    · simp at ha
    · simp at ha hb'
      obtain ⟨_, rfl⟩ := hb'
      subst ha
      simp [lo', hi', reads, N, hv] at hlt

def Fx : Nat → List Bool → List Bool → Bool := fun v l z =>
  if v = 3 then ((l.getD 1 false && z.getD 0 false) != l.getD 0 false)
  else if v = 2 then ((if z.getD 1 false then z.getD 0 false else z.getD 2 false) != z.getD 2 false)
  else if v = 0 then !(l.getD 0 false) else false

theorem hF : ∀ v s, tEn N envEn v s = Fx v ((D v).map s) ((Z v).map s) := by
  intro v s
  by_cases h3 : v = 3
  · subst h3; simp [tEn, N, D, Z, Fx]
  · by_cases h2 : v = 2
    · subst h2; simp [tEn, N, D, Z, Fx]
    · by_cases h0 : v = 0
      · subst h0; simp [tEn, N, D, Z, Fx, envEn]
      · simp [tEn, N, D, Z, Fx, envEn, h0, h2, h3]

theorem hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w 5) C L D cl gd v := by
  intro v hv
  by_cases h3 : v = 3
  · subst h3
    exact lcheckX_of_enum N dat envEn _ C cl gd hF 3 (by decide) (by decide) (by decide)
      (by intro k hk p hp; simp [C] at hp; simp [D, hp]) (by decide) (by decide) (by decide)
      (by intro z hz g hg; simp [Z] at hz; subst hz; simp [gd] at hg; subst hg; simp [D]) (by decide)
  · by_cases h0 : v = 0
    · subst h0
      exact lcheckX_of_enum N dat envEn _ C cl gd hF 0 (by decide) (by decide) (by decide)
        (by intro k hk p hp; simp [C] at hp) (by decide) (by decide) (by decide)
        (by intro z hz; simp [Z] at hz) (by decide)
    · have h1 : ¬ v = 1 := by intro h; subst h; simp [dat] at hv
      have h2 : ¬ v = 2 := by intro h; subst h; simp [dat] at hv
      intro n _ _ bb _
      rw [hF]
      simp [Fx, h0, h2, h3, Enabled, C]

theorem hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
    GuardTime N Sep v z c g := by
  intro v z _ _ g hg
  simp only [gd] at hg
  split at hg
  · rename_i h; obtain ⟨rfl, rfl⟩ := h
    simp at hg; subst hg
    refine ⟨cQ, rfl, rfl, ?_, ?_⟩
    · exact ⟨(0, 0), rfl, 0, by simp [Sep], by simp [hi', lo', reads, N, cQ]⟩
    · exact ⟨(0, 1), rfl, 100, by simp [Sep], by simp [hi', lo', reads, N, cQ]⟩
  · simp at hg

def covQ : Nat → Cov := fun u => if u = 1 then .cl 0 else if u = 0 then .ex 1 else .X

theorem hGC : ∀ c ∈ cl, N.gate c.z = true → 0 ≤ c.a ∧ ∃ cov : Nat → Cov, ValOK N (fun w => x w 5) cl c cov ∧
      (∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w 5) cl u (cov u) = some w →
        CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
      (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧
        (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)) := by
  intro c hc hg
  simp only [cl, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp [cD, N] at hg
  · refine ⟨by simp [cQ], covQ, valOK_of_B N cl _ cQ covQ (by decide) (by decide), ?_, ?_⟩
    · intro u hu w hw
      simp [cQ, N] at hu
      rcases hu with rfl | rfl | rfl
      · simp [covQ, covWin, cl] at hw; subst hw
        exact ⟨trivial, trivial⟩
      · simp [covQ, covWin] at hw; subst hw
        refine ⟨⟨(0, 0), rfl, 0, by simp [Sep], by simp [N, cQ]⟩, ⟨(0, 1), rfl, 100, by simp [Sep], by simp [N, cQ]⟩⟩
      · simp [covQ, covWin] at hw
    · intro u hu
      simp [cQ, N] at hu
      rcases hu with rfl | rfl | rfl <;> simp [covQ, cl, cD, dat]
      intro i w hi hw; subst hi; simp at hw; subst hw; rfl

/-- **Non-vacuity of the data layer:** every hypothesis holds, so `timedX_follows` applies. -/
theorem toyX_follows : ∀ c ∈ cl, ∀ s, s ≤ 40 → Holds x 5 5 c s := by
  have h := timedX_follows (N := N) (dat := dat) (envEn := envEn) (x := x) (r := r) (t0 := 5) (H := 5) (C := C)
    (L := L) (D := D) (Sep := Sep) (cl := cl) (gd := gd)
    hb hT hLs hS hSE hTO hDE hloc
    (by intro v z hv; simp only [gd]; split
        · rename_i h; obtain ⟨rfl, _⟩ := h; simp [N] at hv
        · rfl)
    hGd hGC
    (by intro c hc hg s; simp only [cl, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · intro _ _ _; simp [x, cD]
        · simp [cQ, N] at hg)
    (by intro c hc s hs; simp only [cl, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · intro _ _ _; simp [x, cD]
        · intro _ hA _
          simp only [cQ] at hA
          obtain ⟨h0, h1⟩ := hA
          exfalso
          rw [cnt_le_t0 _ _ (by omega)] at h1
          simp at h1)
    (by intro u hu; simp [dat] at hu; rcases hu with rfl | rfl <;> simp [C]) 40
  exact h.2.2

end Formal.Net.OccNet.TimedXToy
