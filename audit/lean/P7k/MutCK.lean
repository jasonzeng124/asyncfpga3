import Formal.Core.Substrate.CornerNat

/-!
# Probe Bk2: the exact corner-model form of B's constraint shapes

Every entry of `formal/out/cell_constraints.json` is a form

    sum over data paths P of arc delays + a  <=  sum over request paths Q of arc delays + b

(`a`, `b`: the margin and any environment / cell_param bound, whole ps; in the
JSON `a = margin_ps + env hi on the data side`, `b = env lo on the request side`).
This file states, under shard A's corner model
(`Formal.Core.Substrate.CornerNat`: H_ENDPOINTS, H_AFFINE, H_SHARED_CORNER,
H_SCATTER κ; all definitions are A's, nothing is copied), exactly when such a
form holds for EVERY admissible realization (every shared corner `c`, every arc
within `κ` of its nominal delay at `c`), and gives the realization that attains
the bound.

## Named hypotheses

* **H_DISJ** (`Disj P Q`): no arc id occurs on both sides. Common arcs (same
  element, same traversal) are removed first: `allOK_cancel` (exact, it is the
  DiffScat situation: only the divergent tails matter).
* **H_DIV** (`DivOK`): the scaled endpoints `κ.hi·F, κ.hi·S` (data arcs) and
  `κ.lo·F, κ.lo·S` (request arcs) are multiples of `κ.den`, i.e. the extreme
  admissible delays are whole ps. Needed only for the ℕ-exact iff; the real
  model (A's `Delay/Corner.lean`) has no rounding.

## Results

1. `allOK_of_gen` (soundness): the closed-form check `GenOK`
   (`EndpointOK` with the constants `a`, `b`) at the FAST and the SLOW endpoint
   implies the form for every realization. `gen_of_endpointOK`: with `b = 0`
   it is exactly A's `EndpointOK`, so `bundle_realizes` is the special case.
2. `worst_realizes`, `worst_P`, `worst_Q` (tightness): under H_DISJ, for each
   endpoint there is a realization (corner = that endpoint, data arcs at
   `⌊(1+κ)·x⌋`, request arcs at `⌈(1-κ)·x⌉`, every other arc at its endpoint)
   attaining the integer worst case `EndpointNat` at that endpoint.
   `endpointNat_of_allOK`: so the form for every realization implies
   `EndpointNat` (necessity).
3. `gen_relaxed_of_endpointNat`: `EndpointNat` implies `GenOK` with
   `(|P| + |Q|)·(den - 1)` extra on the right: the ℕ-exact condition is
   sandwiched between `GenOK a b` and `GenOK` relaxed by less than one ps per arc.
4. `allOK_iff_gen` (exact, H_DISJ + H_DIV): form for every realization
   `↔ GenOK`. `allOK_iff_endpointOK`: the same for A's `EndpointOK`.
5. Counter-examples (by `decide`): `nat_rounding_not_exact` (without H_DIV,
   `EndpointOK` is not necessary: every realization passes, `EndpointOK`
   fails), `endpointNat_not_sufficient` (the rounded endpoint check is NOT
   sufficient: an interior corner `c = 5/6` breaks it), `uncancelled_pessimistic`
   (without cancelling a common arc, `EndpointOK` fails although the form
   holds trivially), `box_unsound_with_kappa` / `one_corner_unsound_with_kappa`
   (the JSON's box and H_ONE_CORNER checks without κ are unsound for κ > 0),
   `slow_only_unsound` (a SLOW-only check misses a FAST failure, κ = 0).
6. `endpointOK_iff_diff`: `EndpointOK` rewritten as the difference form
   `den·(R - D) ≥ num·(R + D) + den·m` at each endpoint (A's DiffLow with
   κd = κ, at the two endpoints).

NOT covered: an ℕ-exact CLOSED form without H_DIV (the exact condition
quantifies over all rational corners; results 2-3 bound it from both sides);
correlated / DiffScat-only hypotheses on the divergent tails (A's `DiffScat`
is ℝ); per-traversal scatter of one arc (a re-used element traversed by two
edges is two arc ids here, so it does NOT cancel).
-/

namespace Formal.Cells.ConstraintsKappa

open Formal.Core.Substrate

variable {A : Type}

/-! ## 0. Endpoint selector -/

/-- The endpoint value of an arc: `false` = FAST (`F`), `true` = SLOW (`S`). -/
def ep (b : Bool) (a : CArc) : ℕ := if b then a.S else a.F

/-- The corner at that endpoint. -/
def epC (b : Bool) : Corner := if b then Corner.slow else Corner.fast

theorem scat_ep {k : Kappa} {a : CArc} {d : ℕ} (b : Bool) :
    Scat k (epC b) a d ↔ k.lo * ep b a ≤ k.den * d ∧ k.den * d ≤ k.hi * ep b a := by
  cases b
  · exact scat_fast_iff (k := k) (a := a) (d := d)
  · exact scat_slow_iff (k := k) (a := a) (d := d)

theorem sumOver_congr {f g : A → ℕ} :
    ∀ p : List A, (∀ e ∈ p, f e = g e) → sumOver f p = sumOver g p
  | [], _ => rfl
  | e :: p, h => by
    have h1 := h e (List.mem_cons_self ..)
    have h2 := sumOver_congr p (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [sumOver, List.map_cons, List.sum_cons] at h2 ⊢
    rw [h1, h2]

theorem path_F (M : CornerModel A) :
    ∀ p : List A, (M.path p).F = sumOver (fun e => (M.arc e).F) p
  | [] => rfl
  | e :: p => by
    show (M.arc e).F + (M.path p).F = (M.arc e).F + sumOver (fun e => (M.arc e).F) p
    rw [path_F M p]

theorem path_S (M : CornerModel A) :
    ∀ p : List A, (M.path p).S = sumOver (fun e => (M.arc e).S) p
  | [] => rfl
  | e :: p => by
    show (M.arc e).S + (M.path p).S = (M.arc e).S + sumOver (fun e => (M.arc e).S) p
    rw [path_S M p]

theorem path_ep (M : CornerModel A) (b : Bool) (p : List A) :
    ep b (M.path p) = sumOver (fun e => ep b (M.arc e)) p := by
  cases b
  · exact path_F M p
  · exact path_S M p

theorem pathDelay_eq (d : A → ℕ) (p : List A) : pathDelay d p = sumOver d p := rfl

/-! ## 1. The generic shape and its closed-form check -/

/-- **The form holds for every admissible realization** (H_SHARED_CORNER +
H_SCATTER κ): `ΣP + a ≤ ΣQ + b`. -/
def AllOK (M : CornerModel A) (P Q : List A) (a b : ℕ) : Prop :=
  ∀ d : A → ℕ, M.Realizes d → pathDelay d P + a ≤ pathDelay d Q + b

/-- **The closed-form check**: at the FAST and at the SLOW endpoint,
`(1+κ)·D + a ≤ (1-κ)·R + b`, cleared of `den`. Decidable. -/
def GenOK (k : Kappa) (D R : CArc) (a b : ℕ) : Prop :=
  k.hi * D.F + k.den * a ≤ k.den * R.F + k.den * b ∧
    k.hi * D.S + k.den * a ≤ k.den * R.S + k.den * b

instance (k : Kappa) (D R : CArc) (a b : ℕ) : Decidable (GenOK k D R a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem genOK_iff_ep {k : Kappa} {D R : CArc} {a b : ℕ} :
    GenOK k D R a b ↔ ∀ s : Bool, k.hi * ep s D + k.den * a ≤ k.lo * ep s R + k.den * b := by
  constructor
  · intro h s; cases s
    · exact h.1
    · exact h.2
  · intro h; exact ⟨h false, h true⟩

/-- With `b = 0`, `GenOK` is A's `EndpointOK`. -/
theorem gen_iff_endpointOK {k : Kappa} {D R : CArc} {m : ℕ} :
    GenOK k D R m 0 ↔ EndpointOK k D R m := by
  unfold GenOK EndpointOK; simp only [Nat.mul_zero, Nat.add_zero]

theorem gen_of_endpointOK {k : Kappa} {D R : CArc} {m : ℕ} (h : EndpointOK k D R m) :
    GenOK k D R m 0 := gen_iff_endpointOK.2 h

/-- The endpoint check gives the guarded inequality at every corner. -/
theorem gen_nom {k : Kappa} {D R : CArc} {a b : ℕ} (h : GenOK k D R a b) (c : Corner) :
    k.hi * nom c D + k.den * c.W * a ≤ k.lo * nom c R + k.den * c.W * b := by
  obtain ⟨h0, h1⟩ := h
  have e0 := Nat.mul_le_mul_left c.w0 h0
  have e1 := Nat.mul_le_mul_left c.w1 h1
  have l1 : k.hi * nom c D = c.w0 * (k.hi * D.F) + c.w1 * (k.hi * D.S) := by
    simp only [nom, Nat.mul_add, Nat.mul_left_comm]
  have l2 : k.lo * nom c R = c.w0 * (k.lo * R.F) + c.w1 * (k.lo * R.S) := by
    simp only [nom, Nat.mul_add, Nat.mul_left_comm]
  have l3 : ∀ x : ℕ, k.den * c.W * x = c.w0 * (k.den * x) + c.w1 * (k.den * x) := by
    intro x; simp only [Corner.W, Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]
  rw [Nat.mul_add, Nat.mul_add] at e0 e1
  rw [l1, l2, l3 a, l3 b]
  omega

/-- **Soundness.** The closed-form check implies the form at every shared
corner, for every per-arc scatter within κ. -/
theorem allOK_of_gen (M : CornerModel A) (P Q : List A) {a b : ℕ}
    (h : GenOK M.κ (M.path P) (M.path Q) a b) : AllOK M P Q a b := by
  intro d ⟨c, hc⟩
  have hP := scat_path M P (CornerModel.RealizesAt.on M hc P)
  have hQ := scat_path M Q (CornerModel.RealizesAt.on M hc Q)
  have e := gen_nom h c
  have q := q_pos M.κ c
  have h1 := hP.2
  have h2 := hQ.1
  have : M.κ.den * c.W * (pathDelay d P + a) ≤ M.κ.den * c.W * (pathDelay d Q + b) := by
    rw [Nat.mul_add, Nat.mul_add]; omega
  exact Nat.le_of_mul_le_mul_left this q

/-! ## 2. The worst realization (tightness) -/

/-- H_DISJ: no arc id on both sides. -/
def Disj (P Q : List A) : Prop := ∀ e ∈ P, e ∉ Q

/-- Largest whole-ps delay within κ of `x`: `⌊(1+κ)x⌋`. -/
def hiV (k : Kappa) (x : ℕ) : ℕ := k.hi * x / k.den
/-- Smallest whole-ps delay within κ of `x`: `⌈(1-κ)x⌉`. -/
def loV (k : Kappa) (x : ℕ) : ℕ := cdiv (k.lo * x) k.den

theorem hiV_adm (k : Kappa) (x : ℕ) : k.lo * x ≤ k.den * hiV k x ∧ k.den * hiV k x ≤ k.hi * x := by
  have hx : x ≤ hiV k x := by
    unfold hiV; rw [Nat.le_div_iff_mul_le k.den_pos, Nat.mul_comm]
    exact Nat.mul_le_mul_right x k.den_le_hi
  refine ⟨?_, Nat.mul_div_le _ _⟩
  calc k.lo * x ≤ k.den * x := Nat.mul_le_mul_right x k.lo_le_den
    _ ≤ k.den * hiV k x := Nat.mul_le_mul_left _ hx

theorem loV_adm (k : Kappa) (x : ℕ) : k.lo * x ≤ k.den * loV k x ∧ k.den * loV k x ≤ k.hi * x := by
  have hx : loV k x ≤ x := by
    unfold loV; rw [cdiv_le_iff k.den_pos, Nat.mul_comm x]
    exact Nat.mul_le_mul_right x k.lo_le_den
  refine ⟨?_, ?_⟩
  · have := le_cdiv_mul (a := k.lo * x) k.den_pos
    unfold loV; rw [Nat.mul_comm k.den]; exact this
  · calc k.den * loV k x ≤ k.den * x := Nat.mul_le_mul_left _ hx
      _ ≤ k.hi * x := Nat.mul_le_mul_right x k.den_le_hi

/-- The worst realization at endpoint `s`: data arcs (in `P`) at `⌊(1+κ)x⌋`,
every other arc at `⌈(1-κ)x⌉`. -/
def worst [DecidableEq A] (M : CornerModel A) (P : List A) (s : Bool) (e : A) : ℕ :=
  if e ∈ P then hiV M.κ (ep s (M.arc e)) else loV M.κ (ep s (M.arc e))

theorem worst_realizes [DecidableEq A] (M : CornerModel A) (P : List A) (s : Bool) :
    M.RealizesAt (epC s) (worst M P s) := by
  intro e
  rw [scat_ep]
  unfold worst
  split
  · exact hiV_adm _ _
  · exact loV_adm _ _

/-- **The integer worst case at both endpoints** (decidable). -/
def EndpointNat (M : CornerModel A) (P Q : List A) (a b : ℕ) : Prop :=
  ∀ s : Bool, sumOver (fun e => hiV M.κ (ep s (M.arc e))) P + a ≤
    sumOver (fun e => loV M.κ (ep s (M.arc e))) Q + b

theorem worst_P [DecidableEq A] (M : CornerModel A) (P : List A) (s : Bool) :
    pathDelay (worst M P s) P = sumOver (fun e => hiV M.κ (ep s (M.arc e))) P :=
  sumOver_congr P (fun e he => by unfold worst; rw [ite_eq_left he])

theorem worst_Q [DecidableEq A] (M : CornerModel A) {P Q : List A} (hd : Disj P Q) (s : Bool) :
    pathDelay (worst M P s) Q = sumOver (fun e => loV M.κ (ep s (M.arc e))) Q :=
  sumOver_congr Q (fun e he => by
    have : e ∉ P := fun hp => hd e hp he
    unfold worst; rw [ite_eq_right this])

/-- **Necessity / tightness.** Under H_DISJ, the form for every realization
implies the integer worst case at both endpoints (the realization `worst`
attains it, `worst_P`, `worst_Q`). -/
theorem endpointNat_of_allOK [DecidableEq A] (M : CornerModel A) {P Q : List A} {a b : ℕ}
    (hd : Disj P Q) (h : AllOK M P Q a b) : EndpointNat M P Q a b := by
  intro s
  have := h (worst M P s) ⟨epC s, worst_realizes M P s⟩
  rwa [worst_P, worst_Q M hd] at this

/-! ## 3. Sandwich: rounding costs less than one ps per arc -/

theorem hiV_round (k : Kappa) (x : ℕ) : k.hi * x ≤ k.den * hiV k x + (k.den - 1) := by
  have := div_mul_add_gt (a := k.hi * x) k.den_pos
  unfold hiV; rw [Nat.mul_comm k.den]; omega

theorem loV_round (k : Kappa) (x : ℕ) : k.den * loV k x ≤ k.lo * x + (k.den - 1) := by
  have := cdiv_mul_le (a := k.lo * x) k.den_pos
  unfold loV; rw [Nat.mul_comm k.den]; exact this

/-- `EndpointNat` implies the closed-form check up to `(|P|+|Q|)(den-1)/den` ps. -/
theorem gen_relaxed_of_endpointNat (M : CornerModel A) {P Q : List A} {a b : ℕ}
    (h : EndpointNat M P Q a b) (s : Bool) :
    M.κ.hi * ep s (M.path P) + M.κ.den * a ≤
      M.κ.lo * ep s (M.path Q) + M.κ.den * b + (P.length + Q.length) * (M.κ.den - 1) := by
  have hs := h s
  have hu : M.κ.hi * sumOver (fun e => ep s (M.arc e)) P ≤
      M.κ.den * sumOver (fun e => hiV M.κ (ep s (M.arc e))) P + P.length * (M.κ.den - 1) := by
    rw [sumOver_mul_left, sumOver_mul_left, ← sumOver_add_const]
    exact sumOver_le (fun e => hiV_round M.κ _) P
  have hl : M.κ.den * sumOver (fun e => loV M.κ (ep s (M.arc e))) Q ≤
      M.κ.lo * sumOver (fun e => ep s (M.arc e)) Q + Q.length * (M.κ.den - 1) := by
    rw [sumOver_mul_left, sumOver_mul_left, ← sumOver_add_const]
    exact sumOver_le (fun e => loV_round M.κ _) Q
  have hm := Nat.mul_le_mul_left M.κ.den hs
  rw [Nat.mul_add, Nat.mul_add] at hm
  rw [path_ep, path_ep, Nat.add_mul]
  omega

/-- The ℕ-exact condition lies between `GenOK a b` (sufficient) and `GenOK`
relaxed by `(|P|+|Q|)(den-1)` (necessary). -/
theorem sandwich [DecidableEq A] (M : CornerModel A) {P Q : List A} {a b : ℕ} (hd : Disj P Q) :
    (GenOK M.κ (M.path P) (M.path Q) a b → AllOK M P Q a b) ∧
    (AllOK M P Q a b → ∀ s : Bool, M.κ.hi * ep s (M.path P) + M.κ.den * a ≤
      M.κ.lo * ep s (M.path Q) + M.κ.den * b + (P.length + Q.length) * (M.κ.den - 1)) :=
  ⟨allOK_of_gen M P Q, fun h => gen_relaxed_of_endpointNat M (endpointNat_of_allOK M hd h)⟩

/-! ## 4. Exact iff when the extremes are whole ps (H_DIV) -/

/-- H_DIV: `den ∣ hi·x` for the endpoints of data arcs, `den ∣ lo·x` for
request arcs. -/
def DivOK (M : CornerModel A) (P Q : List A) : Prop :=
  (∀ e ∈ P, ∀ s : Bool, M.κ.den * hiV M.κ (ep s (M.arc e)) = M.κ.hi * ep s (M.arc e)) ∧
  (∀ e ∈ Q, ∀ s : Bool, M.κ.den * loV M.κ (ep s (M.arc e)) = M.κ.lo * ep s (M.arc e))

theorem gen_of_endpointNat_div (M : CornerModel A) {P Q : List A} {a b : ℕ}
    (hv : DivOK M P Q) (h : EndpointNat M P Q a b) : GenOK M.κ (M.path P) (M.path Q) a b := by
  rw [genOK_iff_ep]
  intro s
  have hs := h s
  have hu : M.κ.den * sumOver (fun e => hiV M.κ (ep s (M.arc e))) P =
      M.κ.hi * sumOver (fun e => ep s (M.arc e)) P := by
    rw [sumOver_mul_left, sumOver_mul_left]
    exact sumOver_congr P (fun e he => hv.1 e he s)
  have hl : M.κ.den * sumOver (fun e => loV M.κ (ep s (M.arc e))) Q =
      M.κ.lo * sumOver (fun e => ep s (M.arc e)) Q := by
    rw [sumOver_mul_left, sumOver_mul_left]
    exact sumOver_congr Q (fun e he => hv.2 e he s)
  have hm := Nat.mul_le_mul_left M.κ.den hs
  rw [Nat.mul_add, Nat.mul_add] at hm
  rw [path_ep, path_ep]
  omega

/-- **Exact check (H_DISJ, H_DIV).** The form holds for every admissible
realization iff the closed-form endpoint check holds. -/
theorem allOK_iff_gen [DecidableEq A] (M : CornerModel A) {P Q : List A} {a b : ℕ}
    (hd : Disj P Q) (hv : DivOK M P Q) :
    AllOK M P Q a b ↔ GenOK M.κ (M.path P) (M.path Q) a b :=
  ⟨fun h => gen_of_endpointNat_div M hv (endpointNat_of_allOK M hd h), allOK_of_gen M P Q⟩

/-- The same for A's `EndpointOK` (margin `m`, no request-side constant). -/
theorem allOK_iff_endpointOK [DecidableEq A] (M : CornerModel A) {P Q : List A} {m : ℕ}
    (hd : Disj P Q) (hv : DivOK M P Q) :
    AllOK M P Q m 0 ↔ EndpointOK M.κ (M.path P) (M.path Q) m := by
  rw [allOK_iff_gen M hd hv, gen_iff_endpointOK]

/-! ## 5. Common arcs cancel (the DiffScat situation) -/

theorem pathDelay_append (d : A → ℕ) (p q : List A) :
    pathDelay d (p ++ q) = pathDelay d p + pathDelay d q := by
  unfold pathDelay; rw [List.map_append, List.sum_append]

/-- **Cancellation is exact**: a common prefix `C` (the same arc ids, so the
same delays in every realization) drops out of the form. -/
theorem allOK_cancel (M : CornerModel A) (C P Q : List A) (a b : ℕ) :
    AllOK M (C ++ P) (C ++ Q) a b ↔ AllOK M P Q a b := by
  unfold AllOK
  constructor
  · intro h d hd; have := h d hd; rw [pathDelay_append, pathDelay_append] at this; omega
  · intro h d hd; have := h d hd; rw [pathDelay_append, pathDelay_append]; omega

/-- `EndpointOK` in difference form: at each endpoint
`den·D + num·(D + R) + den·m ≤ den·R`, i.e. `(R - D) - κ(R + D) ≥ m`:
A's DiffLow with `κd = κ` at the two corner endpoints. -/
theorem endpointOK_iff_diff {k : Kappa} {D R : CArc} {m : ℕ} :
    EndpointOK k D R m ↔ ∀ s : Bool,
      k.den * ep s D + k.num * (ep s D + ep s R) + k.den * m ≤ k.den * ep s R := by
  have key : ∀ x y : ℕ, (k.hi * x + k.den * m ≤ k.lo * y ↔
      k.den * x + k.num * (x + y) + k.den * m ≤ k.den * y) := by
    intro x y
    have h1 : k.hi * x = k.den * x + k.num * x := by
      show (k.den + k.num) * x = _; rw [Nat.add_mul]
    have h2 : k.lo * y + k.num * y = k.den * y := by
      rw [← Nat.add_mul, Kappa.lo_add]
    rw [h1, Nat.mul_add]; omega
  constructor
  · intro h s; cases s
    · exact (key _ _).1 h.1
    · exact (key _ _).1 h.2
  · intro h; exact ⟨(key _ _).2 (h false), (key _ _).2 (h true)⟩

/-! ## 6. Witnesses and counter-examples (concrete, by `decide`) -/

/-- κ = 1/5 (A's `imux_example_nat` value). -/
def k5 : Kappa := ⟨1, 5, by decide, by decide⟩

/-- Two arcs (`false` = data, `true` = request). -/
def M2 (dF dS rF rS : ℕ) (h1 : dF ≤ dS) (h2 : rF ≤ rS) : CornerModel Bool :=
  ⟨fun e => if e then ⟨rF, rS, h2⟩ else ⟨dF, dS, h1⟩, k5⟩

theorem disj_ft : Disj [false] [true] := by
  intro e he; rcases List.mem_singleton.1 he with rfl; decide

/-- **Non-vacuity of `allOK_iff_endpointOK`**: data arc `[40, 140]`, request
arc `[85, 235]` (multiples of 5), κ = 1/5, margin 20: H_DISJ, H_DIV and
`EndpointOK` all hold, with equality at both endpoints (`6·40 + 100 = 4·85`,
`6·140 + 100 = 4·235`); with margin 21 the check fails. The worst realization
at SLOW (data 168, request 188) attains the bound: `168 + 20 = 188`. -/
theorem witness_div :
    let M := M2 40 140 85 235 (by decide) (by decide)
    DivOK M [false] [true] ∧ EndpointOK M.κ (M.path [false]) (M.path [true]) 20 ∧
      ¬ EndpointOK M.κ (M.path [false]) (M.path [true]) 21 ∧
      worst M [false] true false = 168 ∧ worst M [false] true true = 188 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he s; rcases List.mem_singleton.1 he with rfl; cases s <;> decide
  · intro e he s; rcases List.mem_singleton.1 he with rfl; cases s <;> decide
  · decide

theorem witness_exact :
    let M := M2 40 140 85 235 (by decide) (by decide)
    AllOK M [false] [true] 20 0 ∧ ¬ AllOK M [false] [true] 21 0 := by
  intro M
  have hv : DivOK M [false] [true] := by
    refine ⟨?_, ?_⟩
    · intro e he s; rcases List.mem_singleton.1 he with rfl; cases s <;> decide
    · intro e he s; rcases List.mem_singleton.1 he with rfl; cases s <;> decide
  refine ⟨(allOK_iff_endpointOK M disj_ft hv).2 (by decide), fun h => ?_⟩
  have := (allOK_iff_endpointOK M disj_ft hv).1 h
  revert this; decide

/-- **Without H_DIV, `EndpointOK` is not necessary.** Arcs `[1, 1]` on both
sides, κ = 1/5, margin 0: the only whole-ps delay within 20 % of 1 ps is 1, so
every realization gives `1 ≤ 1`; but `EndpointOK` (`6 ≤ 4`) fails. -/
theorem nat_rounding_not_exact :
    let M := M2 1 1 1 1 (by decide) (by decide)
    AllOK M [false] [true] 0 0 ∧ ¬ EndpointOK M.κ (M.path [false]) (M.path [true]) 0 := by
  intro M
  refine ⟨?_, by decide⟩
  intro d ⟨c, hc⟩
  have one : ∀ e, d e = 1 := by
    intro e
    have h := hc e
    have hw := c.W_pos
    have hn : nom c (M.arc e) = c.W := by
      cases e <;> (show c.w0 * 1 + c.w1 * 1 = c.w0 + c.w1; rw [Nat.mul_one, Nat.mul_one])
    unfold Scat at h
    rw [hn] at h
    simp only [M, M2, k5, Kappa.lo, Kappa.hi] at h
    rcases Nat.lt_or_ge (d e) 1 with h0 | h0
    · have : d e = 0 := by omega
      rw [this] at h; omega
    · rcases Nat.lt_or_ge (d e) 2 with h1 | h1
      · omega
      · have : 5 * c.W * 2 ≤ 5 * c.W * d e := Nat.mul_le_mul_left _ h1
        omega
  show ([false].map d).sum + 0 ≤ ([true].map d).sum + 0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one]
  exact Nat.le_refl _

/-- **The rounded endpoint check `EndpointNat` is NOT sufficient**: arcs
`[0, 3]` on both sides, κ = 1/5, margin 0. At FAST `0 ≤ 0`, at SLOW
`⌊18/5⌋ = 3 ≤ ⌈12/5⌉ = 3`; but at the interior corner `c = 5/6`
(nominal 2.5 ps) the delays data 3, request 2 are admissible and `3 > 2`. -/
theorem endpointNat_not_sufficient :
    let M := M2 0 3 0 3 (by decide) (by decide)
    EndpointNat M [false] [true] 0 0 ∧
      M.RealizesAt ⟨1, 5, by decide⟩ (fun e => if e then 2 else 3) ∧
      ¬ (pathDelay (fun e => if e then 2 else 3) [false] + 0 ≤
          pathDelay (fun e : Bool => if e then 2 else 3) [true] + 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro s; cases s <;> decide
  · intro e; cases e <;> decide

/-- **An uncancelled common arc makes `EndpointOK` fail** although the form
holds trivially: the IMUX `[38, 138]` on both sides, κ = 1/5. -/
theorem uncancelled_pessimistic :
    let M : CornerModel Unit := ⟨fun _ => ⟨38, 138, by decide⟩, k5⟩
    AllOK M [()] [()] 0 0 ∧ ¬ EndpointOK M.κ (M.path [()]) (M.path [()]) 0 := by
  intro M
  refine ⟨fun d _ => Nat.le_refl _, by decide⟩

/-- **The JSON's box (every hi at SLOW, every lo at FAST, no κ) is unsound for
κ > 0**: data arc `[10, 10]`, request arc `[10, 10]`, margin 0: box `10 ≤ 10`
passes, the realization at FAST with data 12, request 8 (both within 20 %)
violates the form. The same instance is H_ONE_CORNER (both columns pass). -/
theorem box_unsound_with_kappa :
    let M := M2 10 10 10 10 (by decide) (by decide)
    (10 + 0 ≤ 10) ∧ M.RealizesAt Corner.fast (fun e => if e then 8 else 12) ∧
      ¬ (pathDelay (fun e => if e then 8 else 12) [false] + 0 ≤
          pathDelay (fun e : Bool => if e then 8 else 12) [true] + 0) := by
  refine ⟨by decide, ?_, by decide⟩
  intro e; cases e <;> decide

theorem one_corner_unsound_with_kappa :
    let M := M2 10 10 10 10 (by decide) (by decide)
    EndpointOK Kappa.zero (M.path [false]) (M.path [true]) 0 ∧
      ¬ AllOK M [false] [true] 0 0 := by
  intro M
  refine ⟨by decide, fun h => ?_⟩
  have := h (fun e => if e then 8 else 12) ⟨Corner.fast, by intro e; cases e <;> decide⟩
  revert this; decide

/-- **A SLOW-only check is unsound even at κ = 0**: data `[10, 10]`, request
`[5, 20]`: SLOW `10 ≤ 20` passes, FAST `10 ≤ 5` fails, and the FAST endpoint
realization violates the form. -/
theorem slow_only_unsound :
    let M : CornerModel Bool :=
      ⟨fun e => if e then ⟨5, 20, by decide⟩ else ⟨10, 10, by decide⟩, Kappa.zero⟩
    (10 ≤ 20) ∧ ¬ AllOK M [false] [true] 0 0 := by
  intro M
  refine ⟨by decide, fun h => ?_⟩
  have := h (fun e => if e then 5 else 10) ⟨Corner.fast, by intro e; cases e <;> decide⟩
  revert this; decide

end Formal.Cells.ConstraintsKappa
