import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Substrate, part 2: the corner model as THE delay model, in ℕ ps

The discrete counterpart of `Formal.Core.Corner` (`Delay/Corner.lean`, ℝ).
Everything here is a natural number, so every check a timing checker makes
is a decidable `≤` between naturals (`decide` / `Nat.decLe`), with no
`native_decide`. The ℝ link is `Substrate/Real.lean`.

## The model (named hypotheses, see `formal/notes/A-substrate.md`)

* **H_ENDPOINTS** (data): each arc `e` has a fast and a slow endpoint
  `F e ≤ S e` in ps (prjxray-db FAST-min-style and SLOW-max-style numbers for
  that arc, after any Elmore term is added) — `CArc`.
* **H_AFFINE**: the nominal delay at corner `c` is the interpolation
  `(1-c)·F + c·S`. In ℕ the corner is a pair of weights `(w0, w1)`,
  `c = w1/(w0+w1)`, and `nom c a = w0·F + w1·S` is the nominal delay scaled
  by `W = w0 + w1` (no division) — `Corner`, `nom`.
* **H_SHARED_CORNER**: one corner for every arc of the die
  (`CornerModel.RealizesAt c`: the same `c` for all arcs).
* **H_SCATTER κ**: each actual delay `d` is within `1 ± κ` of the nominal one,
  `κ = num/den ∈ [0, 1]` (`Kappa`, `Scat`):
  `(den - num)·nom ≤ den·W·d ≤ (den + num)·nom`.

## What is proved

* `scat_band`: an assignment that `Scat`s lies in the per-arc band
  `[bandLo, bandHi]`, the scatter band at the corner rounded OUTWARD
  (floor / ceiling) to whole ps; `band_sub_ind`: that band lies inside the
  corner-independent band `[⌊(1-κ)F⌋, ⌈(1+κ)S⌉]` (`indLo`, `indHi`),
  the ℕ form of `Corner.corner_refines_band`.
* Composition: `nom_add`, `scat_add`, `scat_path`: a path of arcs at one
  corner is an arc (`pathArc`, endpoints summed) whose summed delay `Scat`s
  (`Corner.pathAt_eq_lerp`, `Corner.path_scatter` in ℕ).
* **Endpoint sufficiency** (`bundle_endpoints`, `bundle_paths`,
  `bundle_realizes`): the guarded bundling inequality checked at the fast
  endpoint AND at the slow endpoint (`EndpointOK`, decidable) gives
  `data delay + m ≤ request delay` at every corner, for every scatter
  `≤ κ` (`Corner.bundle_ratio_affine` in ℕ).
* `bundle_band`: the same endpoint check, with one extra ps per arc for the
  outward rounding, gives the band-level inequality
  `Σ bandHi (data) + m ≤ Σ bandLo (request)` at every corner, which is the
  hypothesis of the trace-level bundling lemma `Chan.win_bundle` when every
  arc is a `Win (bandLo) (bandHi)` channel.
* `independent_implies_endpoint`: the independent condition implies the
  endpoint one (the corner model never rejects what the independent model
  accepts).
-/

namespace Formal.Core.Substrate

/-! ## 1. Scatter, arcs, corners -/

/-- Local scatter `κ = num/den`, `0 ≤ κ ≤ 1`. -/
structure Kappa where
  num : ℕ
  den : ℕ
  den_pos : 0 < den
  num_le : num ≤ den
  deriving DecidableEq, Repr

namespace Kappa
/-- `den·(1 - κ)`. -/
def lo (k : Kappa) : ℕ := k.den - k.num
/-- `den·(1 + κ)`. -/
def hi (k : Kappa) : ℕ := k.den + k.num

theorem lo_add (k : Kappa) : k.lo + k.num = k.den := Nat.sub_add_cancel k.num_le
theorem lo_le_den (k : Kappa) : k.lo ≤ k.den := Nat.sub_le _ _
theorem den_le_hi (k : Kappa) : k.den ≤ k.hi := Nat.le_add_right _ _

/-- No scatter. -/
def zero : Kappa := ⟨0, 1, by decide, by decide⟩
end Kappa

/-- One timing arc in the corner model: fast and slow endpoint, ps. -/
structure CArc where
  F : ℕ
  S : ℕ
  F_le_S : F ≤ S
  deriving DecidableEq, Repr

/-- A corner `c = w1 / (w0 + w1) ∈ [0, 1]`, as a pair of weights. -/
structure Corner where
  w0 : ℕ
  w1 : ℕ
  pos : 0 < w0 + w1
  deriving DecidableEq, Repr

namespace Corner
/-- The common denominator `W = w0 + w1`. -/
def W (c : Corner) : ℕ := c.w0 + c.w1
theorem W_pos (c : Corner) : 0 < c.W := c.pos
/-- The fast endpoint `c = 0`. -/
def fast : Corner := ⟨1, 0, by decide⟩
/-- The slow endpoint `c = 1`. -/
def slow : Corner := ⟨0, 1, by decide⟩
end Corner

/-- Nominal delay of arc `a` at corner `c`, times `W`: `w0·F + w1·S`. -/
def nom (c : Corner) (a : CArc) : ℕ := c.w0 * a.F + c.w1 * a.S

theorem nom_ge (c : Corner) (a : CArc) : c.W * a.F ≤ nom c a := by
  unfold nom Corner.W
  have := Nat.mul_le_mul_left c.w1 a.F_le_S
  rw [Nat.add_mul]; omega

theorem nom_le (c : Corner) (a : CArc) : nom c a ≤ c.W * a.S := by
  unfold nom Corner.W
  have := Nat.mul_le_mul_left c.w0 a.F_le_S
  rw [Nat.add_mul]; omega

@[simp] theorem nom_fast (a : CArc) : nom Corner.fast a = a.F := by simp [nom, Corner.fast]
@[simp] theorem nom_slow (a : CArc) : nom Corner.slow a = a.S := by simp [nom, Corner.slow]

/-- **H_SCATTER κ** for one delay `d` (ps) at corner `c`:
`(1-κ)·D(c) ≤ d ≤ (1+κ)·D(c)`, cleared of denominators. Decidable. -/
def Scat (k : Kappa) (c : Corner) (a : CArc) (d : ℕ) : Prop :=
  k.lo * nom c a ≤ k.den * c.W * d ∧ k.den * c.W * d ≤ k.hi * nom c a

instance (k : Kappa) (c : Corner) (a : CArc) (d : ℕ) : Decidable (Scat k c a d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- At the fast endpoint, `Scat` is `(1-κ)F ≤ d ≤ (1+κ)F`. -/
theorem scat_fast_iff {k : Kappa} {a : CArc} {d : ℕ} :
    Scat k Corner.fast a d ↔ k.lo * a.S ≤ k.den * d ∧ k.den * d ≤ k.hi * a.F := by
  simp [Scat, Corner.W, Corner.fast, nom]

theorem scat_slow_iff {k : Kappa} {a : CArc} {d : ℕ} :
    Scat k Corner.slow a d ↔ k.lo * a.S ≤ k.den * d ∧ k.den * d ≤ k.hi * a.S := by
  simp [Scat, Corner.W, Corner.slow, nom]

/-! ## 2. The model and its realisations -/

/-- **The corner model**: an endpoint pair per arc and one scatter bound. -/
structure CornerModel (A : Type) where
  arc : A → CArc
  κ : Kappa

namespace CornerModel
variable {A : Type} (M : CornerModel A)

/-- A delay assignment (one delay per arc, ps) is realised at corner `c`. -/
def RealizesAt (c : Corner) (d : A → ℕ) : Prop := ∀ e, Scat M.κ c (M.arc e) (d e)

/-- **Realizes**: consistent with ONE shared corner and per-arc scatter
`≤ κ` (H_SHARED_CORNER + H_SCATTER). -/
def Realizes (d : A → ℕ) : Prop := ∃ c, M.RealizesAt c d

/-- The same restricted to a finite list of arcs (decidable for given `c`). -/
def RealizesOn (c : Corner) (d : A → ℕ) (l : List A) : Prop :=
  ∀ e ∈ l, Scat M.κ c (M.arc e) (d e)

instance (c : Corner) (d : A → ℕ) (l : List A) : Decidable (M.RealizesOn c d l) :=
  inferInstanceAs (Decidable (∀ e ∈ l, _))

theorem RealizesAt.on {c : Corner} {d : A → ℕ} (h : M.RealizesAt c d) (l : List A) :
    M.RealizesOn c d l := fun e _ => h e

end CornerModel

/-! ## 3. Bands: rounding outward to whole ps -/

/-- Ceiling division `⌈a / b⌉`. -/
def cdiv (a b : ℕ) : ℕ := (a + (b - 1)) / b

theorem cdiv_le_iff {a b n : ℕ} (hb : 0 < b) : cdiv a b ≤ n ↔ a ≤ n * b := by
  unfold cdiv
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hb, Nat.succ_mul]
  omega

theorem le_cdiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ cdiv a b * b :=
  (cdiv_le_iff hb).1 (Nat.le_refl _)

theorem cdiv_mul_le {a b : ℕ} (_hb : 0 < b) : cdiv a b * b ≤ a + (b - 1) := by
  unfold cdiv; exact Nat.div_mul_le_self _ _

theorem div_mul_add_gt {a b : ℕ} (hb : 0 < b) : a < a / b * b + b := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  rw [Nat.mul_comm] at h1; omega

/-- `⌊(1-κ)·D(c)⌋`: the lower end of the arc's band at corner `c`. -/
def bandLo (k : Kappa) (c : Corner) (a : CArc) : ℕ := k.lo * nom c a / (k.den * c.W)

/-- `⌈(1+κ)·D(c)⌉`: the upper end. -/
def bandHi (k : Kappa) (c : Corner) (a : CArc) : ℕ := cdiv (k.hi * nom c a) (k.den * c.W)

/-- Corner-independent band `[⌊(1-κ)F⌋, ⌈(1+κ)S⌉]`. -/
def indLo (k : Kappa) (a : CArc) : ℕ := k.lo * a.F / k.den
def indHi (k : Kappa) (a : CArc) : ℕ := cdiv (k.hi * a.S) k.den

theorem q_pos (k : Kappa) (c : Corner) : 0 < k.den * c.W := Nat.mul_pos k.den_pos c.W_pos

/-- A realised delay lies in its band. -/
theorem scat_band {k : Kappa} {c : Corner} {a : CArc} {d : ℕ} (h : Scat k c a d) :
    bandLo k c a ≤ d ∧ d ≤ bandHi k c a := by
  constructor
  · exact Nat.div_le_of_le_mul h.1
  · have := le_cdiv_mul (a := k.hi * nom c a) (q_pos k c)
    unfold bandHi
    by_contra hc
    have h3 : cdiv (k.hi * nom c a) (k.den * c.W) + 1 ≤ d := by omega
    have h4 := Nat.mul_le_mul_right (k.den * c.W) h3
    have h5 := h.2
    have h6 := q_pos k c
    rw [Nat.mul_comm (k.den * c.W) d] at h5
    rw [Nat.add_mul] at h4
    omega

theorem band_le (k : Kappa) (c : Corner) (a : CArc) : bandLo k c a ≤ bandHi k c a := by
  have hq := q_pos k c
  have h1 : bandLo k c a * (k.den * c.W) ≤ k.lo * nom c a := Nat.div_mul_le_self _ _
  have h2 : k.hi * nom c a ≤ bandHi k c a * (k.den * c.W) := le_cdiv_mul hq
  have h3 : k.lo * nom c a ≤ k.hi * nom c a :=
    Nat.mul_le_mul_right _ (Nat.le_trans k.lo_le_den k.den_le_hi)
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h1 (Nat.le_trans h3 h2)) hq

/-- **The corner band lies inside the independent band** (ℕ form of
`Corner.corner_refines_band`). -/
theorem band_sub_ind (k : Kappa) (c : Corner) (a : CArc) :
    indLo k a ≤ bandLo k c a ∧ bandHi k c a ≤ indHi k a := by
  have hq := q_pos k c
  have hW := c.W_pos
  have hd := k.den_pos
  constructor
  · unfold bandLo
    rw [Nat.le_div_iff_mul_le hq]
    have h1 : indLo k a * k.den ≤ k.lo * a.F := Nat.div_mul_le_self _ _
    have h2 := Nat.mul_le_mul_right c.W h1
    have h3 := Nat.mul_le_mul_left k.lo (nom_ge c a)
    calc indLo k a * (k.den * c.W) = indLo k a * k.den * c.W := by ring
      _ ≤ k.lo * a.F * c.W := h2
      _ = k.lo * (c.W * a.F) := by ring
      _ ≤ k.lo * nom c a := h3
  · unfold bandHi
    rw [cdiv_le_iff hq]
    have h1 : k.hi * a.S ≤ indHi k a * k.den := le_cdiv_mul hd
    have h2 := Nat.mul_le_mul_left k.hi (nom_le c a)
    calc k.hi * nom c a ≤ k.hi * (c.W * a.S) := h2
      _ = k.hi * a.S * c.W := by ring
      _ ≤ indHi k a * k.den * c.W := Nat.mul_le_mul_right _ h1
      _ = indHi k a * (k.den * c.W) := by ring

/-- A realised delay lies in the independent band too. -/
theorem scat_ind {k : Kappa} {c : Corner} {a : CArc} {d : ℕ} (h : Scat k c a d) :
    indLo k a ≤ d ∧ d ≤ indHi k a :=
  ⟨Nat.le_trans (band_sub_ind k c a).1 (scat_band h).1,
    Nat.le_trans (scat_band h).2 (band_sub_ind k c a).2⟩

/-! ## 4. Composition: paths -/

namespace CArc
/-- Two arcs in series. -/
def add (a b : CArc) : CArc := ⟨a.F + b.F, a.S + b.S, Nat.add_le_add a.F_le_S b.F_le_S⟩
/-- The empty path. -/
def zero : CArc := ⟨0, 0, Nat.le_refl 0⟩
end CArc

/-- A path as one arc (endpoints summed; `Corner.pathArc`). -/
def pathArc : List CArc → CArc
  | [] => CArc.zero
  | a :: l => CArc.add a (pathArc l)

theorem nom_add (c : Corner) (a b : CArc) : nom c (CArc.add a b) = nom c a + nom c b := by
  simp only [nom, CArc.add]; ring

theorem nom_zero (c : Corner) : nom c CArc.zero = 0 := by simp [nom, CArc.zero]

/-- Scatter adds (`Corner.path_scatter`): per-arc `Scat` gives path `Scat`. -/
theorem scat_add {k : Kappa} {c : Corner} {a b : CArc} {d d' : ℕ}
    (h : Scat k c a d) (h' : Scat k c b d') : Scat k c (CArc.add a b) (d + d') := by
  unfold Scat at *
  rw [nom_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  omega

theorem scat_zero (k : Kappa) (c : Corner) : Scat k c CArc.zero 0 := by
  simp [Scat, nom_zero]

/-- Path delay of a list of arc ids under an assignment. -/
def pathDelay {A : Type} (d : A → ℕ) (p : List A) : ℕ := (p.map d).sum

/-- The path of arc ids as one arc. -/
def CornerModel.path {A : Type} (M : CornerModel A) (p : List A) : CArc := pathArc (p.map M.arc)

theorem scat_path {A : Type} (M : CornerModel A) {c : Corner} {d : A → ℕ} :
    ∀ p : List A, M.RealizesOn c d p → Scat M.κ c (M.path p) (pathDelay d p)
  | [], _ => by simpa [CornerModel.path, pathArc, pathDelay] using scat_zero M.κ c
  | e :: p, h => by
    have h1 := h e (List.mem_cons_self ..)
    have h2 := scat_path M p (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have := scat_add h1 h2
    simpa [CornerModel.path, pathArc, pathDelay, List.map_cons, List.sum_cons] using this

/-! ## 5. Endpoint sufficiency -/

/-- **The endpoint check** for a bundling pair (data arc/path `D`, request
arc/path `R`, margin `m` ps): `(1+κ)·D + m ≤ (1-κ)·R` at the fast endpoint
AND at the slow endpoint, cleared of denominators. Decidable. -/
def EndpointOK (k : Kappa) (D R : CArc) (m : ℕ) : Prop :=
  k.hi * D.F + k.den * m ≤ k.lo * R.F ∧ k.hi * D.S + k.den * m ≤ k.lo * R.S

instance (k : Kappa) (D R : CArc) (m : ℕ) : Decidable (EndpointOK k D R m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The endpoint check gives the guarded inequality at every corner. -/
theorem endpoint_nom {k : Kappa} {D R : CArc} {m : ℕ} (h : EndpointOK k D R m) (c : Corner) :
    k.hi * nom c D + k.den * c.W * m ≤ k.lo * nom c R := by
  obtain ⟨h0, h1⟩ := h
  have a := Nat.mul_le_mul_left c.w0 h0
  have b := Nat.mul_le_mul_left c.w1 h1
  unfold nom Corner.W
  nlinarith [a, b]

/-- **Endpoint sufficiency (one pair of arcs).** If the endpoint check holds,
then for every corner `c` and all delays within scatter `κ` of their nominal
values at `c`: `data delay + m ≤ request delay`. -/
theorem bundle_endpoints {k : Kappa} {D R : CArc} {m : ℕ} (h : EndpointOK k D R m)
    {c : Corner} {dD dR : ℕ} (hD : Scat k c D dD) (hR : Scat k c R dR) : dD + m ≤ dR := by
  have e := endpoint_nom h c
  have q := q_pos k c
  have h1 := hD.2
  have h2 := hR.1
  have : k.den * c.W * (dD + m) ≤ k.den * c.W * dR := by
    rw [Nat.mul_add]
    have : k.den * c.W * m = k.den * c.W * m := rfl
    omega
  exact Nat.le_of_mul_le_mul_left this q

/-- **Endpoint sufficiency for paths** under one shared corner. -/
theorem bundle_paths {A : Type} (M : CornerModel A) {c : Corner} {d : A → ℕ}
    (P Q : List A) (hP : M.RealizesOn c d P) (hQ : M.RealizesOn c d Q) {m : ℕ}
    (h : EndpointOK M.κ (M.path P) (M.path Q) m) : pathDelay d P + m ≤ pathDelay d Q :=
  bundle_endpoints h (scat_path M P hP) (scat_path M Q hQ)

/-- The same for any realisation (the corner is existential). -/
theorem bundle_realizes {A : Type} (M : CornerModel A) {d : A → ℕ} (hd : M.Realizes d)
    (P Q : List A) {m : ℕ} (h : EndpointOK M.κ (M.path P) (M.path Q) m) :
    pathDelay d P + m ≤ pathDelay d Q := by
  obtain ⟨c, hc⟩ := hd
  exact bundle_paths M P Q (CornerModel.RealizesAt.on M hc P) (CornerModel.RealizesAt.on M hc Q) h

/-- The independent condition `(1+κ)·S_data + m ≤ (1-κ)·F_req` implies the
endpoint check. -/
theorem independent_implies_endpoint {k : Kappa} {D R : CArc} {m : ℕ}
    (h : k.hi * D.S + k.den * m ≤ k.lo * R.F) : EndpointOK k D R m := by
  have a := Nat.mul_le_mul_left k.hi D.F_le_S
  have b := Nat.mul_le_mul_left k.lo R.F_le_S
  exact ⟨by omega, by omega⟩

/-! ## 6. Band level: what the trace-level bundling lemma needs -/

/-- Sum of a per-arc quantity over a path. -/
def sumOver {A : Type} (f : A → ℕ) (p : List A) : ℕ := (p.map f).sum

theorem nom_path {A : Type} (M : CornerModel A) (c : Corner) :
    ∀ p : List A, nom c (M.path p) = sumOver (fun e => nom c (M.arc e)) p
  | [] => by simp [CornerModel.path, pathArc, nom_zero, sumOver]
  | e :: p => by
    have := nom_path M c p
    simp only [CornerModel.path, sumOver, List.map_cons, List.sum_cons, pathArc] at this ⊢
    rw [nom_add, this]

theorem sumOver_mul {A : Type} (f : A → ℕ) (q : ℕ) :
    ∀ p : List A, sumOver f p * q = sumOver (fun e => f e * q) p
  | [] => by simp [sumOver]
  | e :: p => by
    have := sumOver_mul f q p
    simp only [sumOver, List.map_cons, List.sum_cons] at this ⊢
    rw [Nat.add_mul, this]

theorem sumOver_le {A : Type} {f g : A → ℕ} (h : ∀ e, f e ≤ g e) :
    ∀ p : List A, sumOver f p ≤ sumOver g p
  | [] => by simp [sumOver]
  | e :: p => by
    have := sumOver_le h p
    simp only [sumOver, List.map_cons, List.sum_cons] at this ⊢
    exact Nat.add_le_add (h e) this

theorem sumOver_add_const {A : Type} (f : A → ℕ) (q : ℕ) :
    ∀ p : List A, sumOver (fun e => f e + q) p = sumOver f p + p.length * q
  | [] => by simp [sumOver]
  | e :: p => by
    have := sumOver_add_const f q p
    simp only [sumOver, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    rw [this, Nat.succ_mul]; omega

theorem sumOver_mul_left {A : Type} (f : A → ℕ) (q : ℕ) :
    ∀ p : List A, q * sumOver f p = sumOver (fun e => q * f e) p
  | [] => by simp [sumOver]
  | e :: p => by
    have := sumOver_mul_left f q p
    simp only [sumOver, List.map_cons, List.sum_cons] at this ⊢
    rw [Nat.mul_add, this]

/-- **Band-level bundling.** If the endpoint check holds with margin
`m + |P| + |Q|` (one ps of outward rounding per arc), then at EVERY corner
`c` the data path's summed band top plus `m` is at most the request path's
summed band bottom. With each arc a `Win (bandLo) (bandHi)` channel this is
the hypothesis `ts + hiD ≤ loR` of `win_bundle`. -/
theorem bundle_band {A : Type} (M : CornerModel A) (c : Corner) (P Q : List A) {m : ℕ}
    (h : EndpointOK M.κ (M.path P) (M.path Q) (m + P.length + Q.length)) :
    sumOver (fun e => bandHi M.κ c (M.arc e)) P + m ≤
      sumOver (fun e => bandLo M.κ c (M.arc e)) Q := by
  set k := M.κ
  set q := k.den * c.W with hqdef
  have hq : 0 < q := q_pos k c
  have e := endpoint_nom h c
  rw [nom_path, nom_path, ← hqdef] at e
  -- upper: Σ bandHi · q ≤ k.hi · Σ nom + |P| q
  have hu : sumOver (fun e => bandHi k c (M.arc e)) P * q ≤
      k.hi * sumOver (fun e => nom c (M.arc e)) P + P.length * q := by
    rw [sumOver_mul, sumOver_mul_left, ← sumOver_add_const]
    apply sumOver_le
    intro x
    have := cdiv_mul_le (a := k.hi * nom c (M.arc x)) hq
    rw [show bandHi k c (M.arc x) = cdiv (k.hi * nom c (M.arc x)) q from rfl]; omega
  -- lower: k.lo · Σ nom ≤ Σ bandLo · q + |Q| q
  have hl : k.lo * sumOver (fun e => nom c (M.arc e)) Q ≤
      sumOver (fun e => bandLo k c (M.arc e)) Q * q + Q.length * q := by
    rw [sumOver_mul, sumOver_mul_left, ← sumOver_add_const]
    apply sumOver_le
    intro x
    have := div_mul_add_gt (a := k.lo * nom c (M.arc x)) hq
    rw [show bandLo k c (M.arc x) = k.lo * nom c (M.arc x) / q from rfl]; omega
  have key : (sumOver (fun e => bandHi k c (M.arc e)) P + m) * q ≤
      sumOver (fun e => bandLo k c (M.arc e)) Q * q := by
    have e' : k.hi * sumOver (fun e => nom c (M.arc e)) P + q * m + q * P.length +
        q * Q.length ≤ k.lo * sumOver (fun e => nom c (M.arc e)) Q := by
      have : q * (m + P.length + Q.length) = q * m + q * P.length + q * Q.length := by ring
      omega
    rw [Nat.add_mul]
    have c1 : P.length * q = q * P.length := Nat.mul_comm _ _
    have c2 : Q.length * q = q * Q.length := Nat.mul_comm _ _
    have c3 : m * q = q * m := Nat.mul_comm _ _
    omega
  exact Nat.le_of_mul_le_mul_right key hq

/-! ## 7. Non-vacuity and a decidable example -/

/-- **Non-vacuity.** Every corner model is realised: at the fast corner the
fast endpoints themselves are a realisation (any κ). -/
theorem realizes_fast {A : Type} (M : CornerModel A) :
    M.RealizesAt Corner.fast (fun e => (M.arc e).F) := by
  intro e
  rw [scat_fast_iff]
  exact ⟨Nat.mul_le_mul_right _ M.κ.lo_le_den, Nat.mul_le_mul_right _ M.κ.den_le_hi⟩

/-- prjxray's IMUX_L pip (`[38, 138]` ps), κ = 1/5: one IMUX of data against a
two-IMUX matched request passes the endpoint check, while the independent
check fails (`Corner.imux_example` in ℕ, by kernel `decide`). -/
theorem imux_example_nat :
    let κ : Kappa := ⟨1, 5, by decide, by decide⟩
    let imux : CArc := ⟨38, 138, by decide⟩
    EndpointOK κ imux (CArc.add imux imux) 0 ∧
      ¬ (κ.hi * imux.S + κ.den * 0 ≤ κ.lo * (CArc.add imux imux).F) := by
  decide

end Formal.Core.Substrate
