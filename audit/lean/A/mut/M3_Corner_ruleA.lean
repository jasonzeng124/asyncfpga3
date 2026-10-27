import Formal.Core.Fidelity
import Formal.Core.Delay.Pure
import Mathlib.Tactic.Ring

/-!
# Corner-correlated delay bounds

Probe A / delay-corner. The independent per-arc band `[fast_min, slow_max]`
(`Formal.Core.Fidelity.DelayBound.ofCorners`) is 3–4× wide, so the bundling
condition of `Formal.Core.DelayPure.bundle_two_wires`, `ts + hiD ≤ loR`, almost
never closes when `hiD` is the data path's slow max and `loR` the request
path's fast min. On a real die every arc sits at **one** PVT point plus local
scatter. This file models that and proves what it buys.

## The model (all hypotheses are explicit arguments)

* **H-affine (nominal delay)**: arc `e` has fast and slow endpoints
  `F e ≤ S e`, and its nominal delay at corner `c ∈ [0,1]` is
  `lerp (F e) (S e) c = (1-c)·F e + c·S e` (`Arc.at`).
* **SharedCorner**: one `c ∈ [0,1]` for every arc of the die. In the trace
  theorems it is the existential `∃ c, 0 ≤ c ∧ c ≤ 1 ∧ …` in the hypothesis.
* **LocalScatter κ**: each real delay `d` satisfies
  `(1-κ)·D(c) ≤ d ≤ (1+κ)·D(c)`, `0 ≤ κ ≤ 1` (`Scat`).
* **Proportional corner** (a special case, used by `cells/verify/skew.py`):
  `D_e(s) = s · P_e`, one shared scale `s > 0`, `P_e` the SDF prediction.

## What is proved

1. Endpoints suffice: `bundle_ratio_affine(_iff)`, and more generally
   `bundle_ratio_chord` (data path below its chord, request above it).
   Monotonicity alone is not enough: `monotone_not_enough`.
   In the proportional case the condition does not depend on `s` at all:
   `bundle_scaled_iff`.
2. Composition: `pathAt_eq_lerp` (a path of affine arcs is affine with
   endpoints `ΣF`, `ΣS`), `path_scatter` (per-arc scatter `κ` ⇒ path scatter
   `κ`), `corner_refines_band` (the corner model is inside the widened
   independent band, so every `Fidelity` result still applies).
3. Trace level: `bundle_corner` instantiates `DelayPure.bundle_two_wires`
   with corner-correlated bands and only the two endpoint checks.
   `independent_implies_corner` and `imux_example` show the corner
   condition is strictly weaker than the independent one.
4. Project rules: `ruleE_sound` (skew.py's `GUARD_LO·t_req > GUARD_HI·t_sel`
   on divergent tails is sound iff `κ ≤ 383/1927 ≈ 0.1988`; tightness
   `ruleE_tight`), `guard_totals_imp_tails` (guarding a shared prefix too is
   only more conservative), `ruleA_sound` (tighten.py's
   `max(0.2·t, 200 ps)` is sound for `κ ≤ 1/22`, `θ ≤ 50 ps`, and
   `ruleA_sound_rel`: with θ = 0 exactly `κ ≤ 1/11`;
   `ruleA_tight`: no `θ = 0` guard of the 20% form survives `κ > 1/11`).
5. Testing κ from rings: `ring_kappa_lower` (two rings on one die bound `κ`
   from below by `(rᵢ - rⱼ)/(rᵢ + rⱼ)`), `guard_refuted_by_7link_rings`.
-/

noncomputable section

namespace Formal.Core.Corner

open Formal.Core.Fidelity Formal.Core.Fidelity.DelayBound Formal.Core.DelayPure

/-! ## 1. Endpoints suffice for affine corners -/

/-- Linear interpolation between the fast (`c = 0`) and slow (`c = 1`)
endpoint. -/
def lerp (F S c : ℝ) : ℝ := (1 - c) * F + c * S

@[simp] theorem lerp_zero (F S : ℝ) : lerp F S 0 = F := by unfold lerp; ring
@[simp] theorem lerp_one (F S : ℝ) : lerp F S 1 = S := by unfold lerp; ring

theorem lerp_add (F S F' S' c : ℝ) : lerp F S c + lerp F' S' c = lerp (F + F') (S + S') c := by
  unfold lerp; ring

theorem lerp_ge_left {F S c : ℝ} (hFS : F ≤ S) (hc0 : 0 ≤ c) : F ≤ lerp F S c := by
  unfold lerp; nlinarith

theorem lerp_le_right {F S c : ℝ} (hFS : F ≤ S) (hc1 : c ≤ 1) : lerp F S c ≤ S := by
  unfold lerp; nlinarith

theorem lerp_nonneg {F S c : ℝ} (hF : 0 ≤ F) (hS : 0 ≤ S) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ lerp F S c := by
  unfold lerp
  have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c) hF
  have := mul_nonneg hc0 hS
  linarith

/-- An affine function of `c` that is `≥ m` at both endpoints is `≥ m` on
`[0,1]`. -/
theorem lerp_ge_of_ends {a b m c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : m ≤ a) (hb : m ≤ b) : m ≤ lerp a b c := by
  unfold lerp
  have h1 := mul_le_mul_of_nonneg_left ha (by linarith : (0:ℝ) ≤ 1 - c)
  have h2 := mul_le_mul_of_nonneg_left hb hc0
  nlinarith

/-- **Theorem 1 (endpoints suffice).** Data path and request path both affine
in the shared corner `c`. If the scatter-guarded bundling condition with margin
`m` holds at the fast endpoint and at the slow endpoint, it holds at every
corner in between. No assumption on `κ` is needed: the guarded difference
`(1-κ)·D_req(c) - (1+κ)·D_data(c)` is itself affine in `c`. -/
theorem bundle_ratio_affine {κ m Fd Sd Fr Sr c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h0 : (1 + κ) * Fd + m ≤ (1 - κ) * Fr) (h1 : (1 + κ) * Sd + m ≤ (1 - κ) * Sr) :
    (1 + κ) * lerp Fd Sd c + m ≤ (1 - κ) * lerp Fr Sr c := by
  have key : (1 - κ) * lerp Fr Sr c - (1 + κ) * lerp Fd Sd c
      = lerp ((1 - κ) * Fr - (1 + κ) * Fd) ((1 - κ) * Sr - (1 + κ) * Sd) c := by
    unfold lerp; ring
  have := lerp_ge_of_ends (m := m) hc0 hc1
    (a := (1 - κ) * Fr - (1 + κ) * Fd) (b := (1 - κ) * Sr - (1 + κ) * Sd)
    (by linarith) (by linarith)
  linarith

/-- The endpoint checks are also necessary, so for affine corners
"for every corner" is exactly "at the fast and at the slow endpoint". -/
theorem bundle_ratio_affine_iff {κ m Fd Sd Fr Sr : ℝ} :
    (∀ c, 0 ≤ c → c ≤ 1 → (1 + κ) * lerp Fd Sd c + m ≤ (1 - κ) * lerp Fr Sr c) ↔
    ((1 + κ) * Fd + m ≤ (1 - κ) * Fr ∧ (1 + κ) * Sd + m ≤ (1 - κ) * Sr) := by
  constructor
  · intro h
    have h0 := h 0 le_rfl (by norm_num)
    have h1 := h 1 (by norm_num) le_rfl
    simp only [lerp_zero, lerp_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ c hc0 hc1
    exact bundle_ratio_affine hc0 hc1 h0 h1

/-- **Generalisation (convexity).** Affinity is more than needed: it is
enough that the data delay lies on or below its chord and the request delay
on or above its chord (data convex, request concave in `c`), with
`κ ≤ 1` and `-1 ≤ κ` so both scatter factors are nonnegative. -/
theorem bundle_ratio_chord {κ m c : ℝ} {Dd Dr : ℝ → ℝ} (hκ : -1 ≤ κ) (hκ1 : κ ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hDd : Dd c ≤ lerp (Dd 0) (Dd 1) c) (hDr : lerp (Dr 0) (Dr 1) c ≤ Dr c)
    (h0 : (1 + κ) * Dd 0 + m ≤ (1 - κ) * Dr 0) (h1 : (1 + κ) * Dd 1 + m ≤ (1 - κ) * Dr 1) :
    (1 + κ) * Dd c + m ≤ (1 - κ) * Dr c := by
  have hA := bundle_ratio_affine hc0 hc1 h0 h1
  have hB := mul_le_mul_of_nonneg_left hDd (by linarith : (0:ℝ) ≤ 1 + κ)
  have hC := mul_le_mul_of_nonneg_left hDr (by linarith : (0:ℝ) ≤ 1 - κ)
  linarith

/-- **Monotonicity alone is not enough.** Two nondecreasing nominal-delay
curves that satisfy the bundling condition at both endpoints (κ = 0, m = 0)
and violate it at `c = 1/2`: the data path jumps to its slow value early,
the request path late. So "nominal monotone in `c`" must be strengthened
(affine, or the chord conditions above) before endpoint checks are sound. -/
theorem monotone_not_enough :
    ∃ Dd Dr : ℝ → ℝ,
      (∀ a b, a ≤ b → Dd a ≤ Dd b) ∧ (∀ a b, a ≤ b → Dr a ≤ Dr b) ∧
      Dd 0 ≤ Dr 0 ∧ Dd 1 ≤ Dr 1 ∧ Dr (1/2) < Dd (1/2) := by
  refine ⟨fun c => if c < 1/2 then 1 else 2, fun c => if c < 9/10 then 3/2 else 3,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | (exfalso; rw [not_lt] at h1; linarith) | norm_num
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | (exfalso; rw [not_lt] at h1; linarith) | norm_num
  · norm_num
  · norm_num
  · norm_num

/-- **Proportional corners.** When every arc scales by one shared factor
`s > 0` from its prediction `P` (the model behind skew.py's remark that "the
common 0.975 cancels"), the guarded condition does not depend on `s`:
one check on the predictions covers every die. -/
theorem bundle_scaled_iff {κ Pd Pr s : ℝ} (hs : 0 < s) :
    (1 + κ) * (s * Pd) ≤ (1 - κ) * (s * Pr) ↔ (1 + κ) * Pd ≤ (1 - κ) * Pr := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have := mul_lt_mul_of_pos_left hc hs
    nlinarith
  · intro h
    have := mul_le_mul_of_nonneg_left h hs.le
    nlinarith

/-! ## 2. Composition: arcs and paths -/

/-- One routed arc in the corner model: fast and slow endpoint of its nominal
delay (for example prjxray's intrinsic fast/slow plus the corner-independent
Elmore term; a constant is affine, so that form is covered). -/
structure Arc where
  F : ℝ
  S : ℝ
  F_nonneg : 0 ≤ F
  F_le_S : F ≤ S

namespace Arc

/-- Nominal delay of the arc at corner `c` (hypothesis H-affine). -/
def at' (a : Arc) (c : ℝ) : ℝ := lerp a.F a.S c

theorem at'_nonneg (a : Arc) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : 0 ≤ a.at' c :=
  lerp_nonneg a.F_nonneg (le_trans a.F_nonneg a.F_le_S) hc0 hc1

/-- The arc's independent band `[F, S]` as a `Fidelity.DelayBound`. -/
def band (a : Arc) : DelayBound := ⟨a.F, a.S, a.F_nonneg, a.F_le_S⟩

end Arc

/-- **LocalScatter κ** for one delay: the real delay `d` is within a factor
`1 ± κ` of the nominal delay `D` at the die's corner. -/
def Scat (κ D d : ℝ) : Prop := (1 - κ) * D ≤ d ∧ d ≤ (1 + κ) * D

/-- Fast endpoint of a path (sum over its arcs). -/
def pathF : List Arc → ℝ
  | [] => 0
  | a :: l => a.F + pathF l

/-- Slow endpoint of a path. -/
def pathS : List Arc → ℝ
  | [] => 0
  | a :: l => a.S + pathS l

/-- Nominal path delay at corner `c`: the sum of the arcs' nominal delays at
the **same** `c` (SharedCorner). -/
def pathAt (c : ℝ) : List Arc → ℝ
  | [] => 0
  | a :: l => a.at' c + pathAt c l

theorem pathF_nonneg : ∀ l : List Arc, 0 ≤ pathF l
  | [] => le_refl _
  | a :: l => by simp only [pathF]; linarith [a.F_nonneg, pathF_nonneg l]

theorem pathF_le_pathS : ∀ l : List Arc, pathF l ≤ pathS l
  | [] => le_refl _
  | a :: l => by simp only [pathF, pathS]; linarith [a.F_le_S, pathF_le_pathS l]

/-- The path as one arc. -/
def pathArc (l : List Arc) : Arc := ⟨pathF l, pathS l, pathF_nonneg l, pathF_le_pathS l⟩

/-- **Theorem 2a (composition keeps the affine form).** Under a shared corner,
a path's nominal delay is the interpolation of its summed endpoints. -/
theorem pathAt_eq_lerp (c : ℝ) : ∀ l : List Arc, pathAt c l = lerp (pathF l) (pathS l) c
  | [] => by simp [pathAt, pathF, pathS, lerp]
  | a :: l => by
    simp only [pathAt, pathF, pathS, Arc.at']
    rw [pathAt_eq_lerp c l, lerp_add]

theorem pathAt_eq_pathArc (c : ℝ) (l : List Arc) : pathAt c l = (pathArc l).at' c :=
  pathAt_eq_lerp c l

/-- **Theorem 2b (scatter composes).** If every arc's real delay is within
`1 ± κ` of its nominal delay at the shared corner, the path's real delay is
within `1 ± κ` of the path's nominal delay. (Worst case: the path scatter
bound does not shrink with length. Averaging of independent ε is a
statistical statement, not a bound.) -/
theorem path_scatter (κ c : ℝ) : ∀ (ds : List ℝ) (l : List Arc),
    Pw (fun d (a : Arc) => Scat κ (a.at' c) d) ds l → Scat κ (pathAt c l) (tsum ds)
  | [], [], _ => by simp [Scat, pathAt, tsum]
  | d :: ds, a :: l, h => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨h4, h5⟩ := path_scatter κ c ds l h3
    simp only [Scat, pathAt, tsum] at *
    constructor <;> nlinarith
  | [], _ :: _, h => absurd h (by simp [Pw])
  | _ :: _, [], h => absurd h (by simp [Pw])

/-- **The corner model refines the independent one.** A delay that satisfies
SharedCorner + LocalScatter κ lies in the widened independent band
`Fidelity.DelayBound.widen (band) κ = [F(1-κ), S(1+κ)]`, so every result
proved for independent bands still applies. -/
theorem corner_refines_band (a : Arc) {κ c d : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd : Scat κ (a.at' c) d) :
    Mem d (widen a.band κ hκ0 hκ1) := by
  obtain ⟨h1, h2⟩ := hd
  have hl := lerp_ge_left a.F_le_S hc0 (c := c)
  have hr := lerp_le_right a.F_le_S hc1 (c := c)
  have hl' := mul_le_mul_of_nonneg_left hl (by linarith : (0:ℝ) ≤ 1 - κ)
  have hr' := mul_le_mul_of_nonneg_left hr (by linarith : (0:ℝ) ≤ 1 + κ)
  refine ⟨?_, ?_⟩
  · show a.F * (1 - κ) ≤ d
    unfold Arc.at' at h1; nlinarith
  · show d ≤ a.S * (1 + κ)
    unfold Arc.at' at h2; nlinarith

/-! ## 3. Trace level: bundled data under a shared corner -/

/-- **Bundled data under SharedCorner + LocalScatter κ.** The data wire and
the request wire are pure-delay channels (`DelayPure.Chan`) whose bands are
the scatter bands around their nominal delays at **one** corner `c` (the
existential is the SharedCorner hypothesis). Only the two endpoint checks are
required; the conclusion is `DelayPure.bundle_two_wires`'s: whenever the
receiver sees the request (before the hold end), the data is the settled
value. -/
theorem bundle_corner {κ ts t0 t1 s : ℝ} {b v : Bool} {D R : Arc}
    {src data reqIn reqOut : DelayPure.Sig} (hκ1 : κ ≤ 1)
    (hcorner : ∃ c, 0 ≤ c ∧ c ≤ 1 ∧
      Chan ((1 - κ) * D.at' c) ((1 + κ) * D.at' c) src data ∧
      Chan ((1 - κ) * R.at' c) ((1 + κ) * R.at' c) reqIn reqOut)
    (hsrc : StableOn src (t0 + ts) t1 v) (hb : StableBefore reqIn t0 b)
    (hfast : ts + (1 + κ) * D.F ≤ (1 - κ) * R.F)
    (hslow : ts + (1 + κ) * D.S ≤ (1 - κ) * R.S)
    (hs : reqOut s ≠ b) (hs1 : s ≤ t1 + (1 - κ) * D.F) : data s = v := by
  obtain ⟨c, hc0, hc1, hD, hR⟩ := hcorner
  have hb' : ts + (1 + κ) * D.at' c ≤ (1 - κ) * R.at' c := by
    have := bundle_ratio_affine (m := ts) hc0 hc1 (by linarith) (by linarith)
      (κ := κ) (Fd := D.F) (Sd := D.S) (Fr := R.F) (Sr := R.S)
    unfold Arc.at'; linarith
  have hhold : s ≤ t1 + (1 - κ) * D.at' c := by
    have := mul_le_mul_of_nonneg_left (lerp_ge_left D.F_le_S hc0 (c := c))
      (by linarith : (0:ℝ) ≤ 1 - κ)
    unfold Arc.at'; linarith
  exact bundle_two_wires hsrc hD hR hb hb' hs hhold

/-- The independent-band condition (data slow max, request fast min) implies
both endpoint checks, so the corner model never loses a design the
independent model accepts. -/
theorem independent_implies_corner {κ ts : ℝ} {D R : Arc} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hind : ts + (1 + κ) * D.S ≤ (1 - κ) * R.F) :
    ts + (1 + κ) * D.F ≤ (1 - κ) * R.F ∧ ts + (1 + κ) * D.S ≤ (1 - κ) * R.S := by
  have h1 := mul_le_mul_of_nonneg_left D.F_le_S (by linarith : (0:ℝ) ≤ 1 + κ)
  have h2 := mul_le_mul_of_nonneg_left R.F_le_S (by linarith : (0:ℝ) ≤ 1 - κ)
  constructor <;> linarith

/-- **Strictly weaker.** prjxray's IMUX_L pip, `[0.038, 0.138]` ns. Data path:
one IMUX; request path: two IMUX in series (a matched delay of 2×), κ = 0.2.
The corner checks hold at both endpoints; the independent condition
`(1+κ)·0.138 ≤ (1-κ)·0.076` fails by a factor 2.7. -/
theorem imux_example :
    let κ : ℝ := 1/5
    ((1 + κ) * 0.038 ≤ (1 - κ) * (2 * 0.038) ∧ (1 + κ) * 0.138 ≤ (1 - κ) * (2 * 0.138)) ∧
    ¬ ((1 + κ) * 0.138 ≤ (1 - κ) * (2 * 0.038)) := by
  norm_num

/-! ## 4. The project's guardbands

Rule E (`cells/verify/skew.py`, select-before-request):
`GUARD_LO * (t_req - t_c) - GUARD_HI * (t_sel - t_c) > 0`, the `t` being SDF
predictions in ps and `t_c` the arrival at the divergence point.
Rule A (`cells/verify/tighten.py`, request is the last thing a cell emits):
`t_req ≥ t_data + max(0.2·t_data, 200 ps)`. -/

/-- `GUARD_LO` in `cells/verify/skew.py`. -/
def guardLo : ℝ := 772 / 1000
/-- `GUARD_HI` in `cells/verify/skew.py`. -/
def guardHi : ℝ := 1155 / 1000

/-- The local scatter the rule-E guardband tolerates under a proportional
shared corner: `(GUARD_HI - GUARD_LO)/(GUARD_HI + GUARD_LO) = 383/1927 ≈
0.1988`. Only the ratio of the two constants matters; their common offset
(the measured mean ratio 0.9636) is the shared scale and cancels. -/
def kappaE : ℝ := 383 / 1927

theorem guard_kappa_iff {κ : ℝ} :
    (1 + κ) * guardLo ≤ (1 - κ) * guardHi ↔ κ ≤ kappaE := by
  unfold guardLo guardHi kappaE
  constructor <;> intro h <;> linarith

/-- **Rule E is sound for κ ≤ 0.1988.** Model: the shared prefix up to the
divergence point is one physical delay `C` (common to both arrivals); each
divergent tail's real delay is `s·P·(1 ± κ)` with one shared scale `s > 0`
(proportional SharedCorner + LocalScatter κ). If skew.py's guarded margin on
the predicted tails is positive, the select really arrives before the
request. -/
theorem ruleE_sound {κ s C Pr Ps ar as_ : ℝ} (hs : 0 < s) (hκ : κ ≤ kappaE)
    (hPs : 0 ≤ Ps)
    (har : Scat κ (s * Pr) ar) (has : Scat κ (s * Ps) as_)
    (hguard : 0 < guardLo * Pr - guardHi * Ps) :
    C + as_ < C + ar := by
  obtain ⟨har1, _⟩ := har
  obtain ⟨_, has2⟩ := has
  have hk := guard_kappa_iff.mpr hκ
  unfold guardLo guardHi at hk hguard
  unfold kappaE at hκ
  -- (1-κ)·Pr > (1+κ)·Ps
  have key : (1 + κ) * Ps < (1 - κ) * Pr := by nlinarith
  have := mul_lt_mul_of_pos_left key hs
  nlinarith

/-- **Tightness of `kappaE`.** For any `κ` with `kappaE < κ < 1` there are
predicted tails that pass rule E and real delays allowed by the model (shared
scale 1, request at `1-κ`, select at `1+κ`) for which the select arrives
strictly after the request. -/
theorem ruleE_tight {κ : ℝ} (hκ : kappaE < κ) (hκ1 : κ < 1) :
    ∃ Pr Ps : ℝ, 0 ≤ Ps ∧ 0 < guardLo * Pr - guardHi * Ps ∧
      (1 - κ) * Pr < (1 + κ) * Ps := by
  refine ⟨guardHi * (1 - κ) + guardLo * (1 + κ), 2 * guardLo * (1 - κ), ?_, ?_, ?_⟩
  · unfold guardLo; nlinarith
  · unfold guardLo guardHi kappaE at *; nlinarith
  · unfold guardLo guardHi kappaE at *; nlinarith

/-- **Guarding the shared prefix too is only more conservative.** Since
`GUARD_LO ≤ GUARD_HI` and a prefix delay is nonnegative, the guard on full
arrivals implies the guard on the divergent tails, which is what
`ruleE_sound` needs (skew.py moved from the former to the latter). -/
theorem guard_totals_imp_tails {C Tr Ts : ℝ} (hC : 0 ≤ C)
    (h : 0 < guardLo * (C + Tr) - guardHi * (C + Ts)) :
    0 < guardLo * Tr - guardHi * Ts := by
  unfold guardLo guardHi at *; nlinarith

/-- **Rule E under affine (non-proportional) corners: check both SDF
endpoints.** When the nominal tails are affine in the corner but not
proportional (e.g. prjxray's corner-independent Elmore term added to a
cornered intrinsic), a single-SDF check is not scale-invariant. Passing
skew.py's guard on the fast-endpoint predictions **and** on the
slow-endpoint predictions makes the select arrive first at every corner
`c ∈ [0,1]`, for local scatter `κ ≤ kappaE`. -/
theorem ruleE_two_corner {κ c C ar as_ : ℝ} {R Sl : Arc} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : κ ≤ kappaE) (har : Scat κ (R.at' c) ar) (has : Scat κ (Sl.at' c) as_)
    (hgF : 0 < guardLo * R.F - guardHi * Sl.F) (hgS : 0 < guardLo * R.S - guardHi * Sl.S) :
    C + as_ < C + ar := by
  have hm : 0 < min (guardLo * R.F - guardHi * Sl.F) (guardLo * R.S - guardHi * Sl.S) :=
    lt_min hgF hgS
  have hl := lerp_ge_of_ends hc0 hc1
    (min_le_left (guardLo * R.F - guardHi * Sl.F) (guardLo * R.S - guardHi * Sl.S))
    (min_le_right (guardLo * R.F - guardHi * Sl.F) (guardLo * R.S - guardHi * Sl.S))
  have key : lerp (guardLo * R.F - guardHi * Sl.F) (guardLo * R.S - guardHi * Sl.S) c
      = guardLo * R.at' c - guardHi * Sl.at' c := by
    unfold Arc.at' lerp; ring
  have hg : 0 < guardLo * R.at' c - guardHi * Sl.at' c := by linarith
  rw [← one_mul (R.at' c)] at har
  rw [← one_mul (Sl.at' c)] at has
  exact ruleE_sound one_pos hκ (Sl.at'_nonneg hc0 hc1) har has hg

/-- **A corner that varies across the die (gradient δ).** If arc `e` sits at
corner `c'` with `|c' - c| ≤ δ` instead of exactly at the shared `c`, its
nominal delay moves by at most `δ·(S - F)`: a spatial gradient becomes an
additive scatter term proportional to the arc's corner spread. -/
theorem near_corner {F S c c' δ : ℝ} (hFS : F ≤ S) (h1 : c' ≤ c + δ) (h2 : c - δ ≤ c') :
    lerp F S c - δ * (S - F) ≤ lerp F S c' ∧ lerp F S c' ≤ lerp F S c + δ * (S - F) := by
  have e : lerp F S c' - lerp F S c = (c' - c) * (S - F) := by unfold lerp; ring
  have hSF : 0 ≤ S - F := by linarith
  constructor <;> nlinarith

/-- **Rule A is sound for κ ≤ 1/22 and an additive scatter θ ≤ 50 ps.**
Model: real delay `s·(P·(1 ± κ) ± θ)`, i.e. a relative scatter κ plus an
absolute one θ (in SDF ps), all under one shared scale `s > 0`. tighten.py's
`t_req ≥ t_data + max(0.2·t_data, 200)` on the predictions then guarantees the
request really arrives no earlier than the data. -/
theorem ruleA_sound {κ θ s Pd Pr ad ar : ℝ} (hs : 0 < s)
    (hκ : κ ≤ 1/22) (hθ : θ ≤ 50) (hPd : 0 ≤ Pd)
    (hruleA : Pd + max (Pd / 5) 200 ≤ Pr)
    (had : ad ≤ s * ((1 + κ) * Pd + θ)) (har : s * ((1 - κ) * Pr - θ) ≤ ar) :
    ad ≤ ar := by
  have key : (1 + κ) * Pd + θ ≤ (1 - κ) * Pr - θ := by
    have hm1 := le_max_left (Pd / 5) 200
    have hm2 := le_max_right (Pd / 5) 200
    set g := max (Pd / 5) 200
    -- (1-κ)·Pr ≥ (1-κ)(Pd+g)
    have h1 := mul_le_mul_of_nonneg_left hruleA (by linarith : (0:ℝ) ≤ 1 - κ)
    -- need 2κ·Pd + 2θ ≤ (1-κ)·g
    have h2 : κ * Pd ≤ Pd / 22 := by nlinarith
    have h3 : κ * g ≤ g / 22 := by nlinarith
    by_cases hP : Pd ≤ 1000
    · nlinarith
    · nlinarith
  have := mul_le_mul_of_nonneg_left key hs.le
  linarith

/-- **Rule A with purely relative scatter: sound exactly up to κ = 1/11.**
With θ = 0, tighten.py's guard covers every local scatter `κ ≤ 1/11 ≈ 9.1 %`
(`ruleA_tight` shows no larger κ is covered). -/
theorem ruleA_sound_rel {κ s Pd Pr ad ar : ℝ} (hs : 0 < s) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1/10) (hPd : 0 ≤ Pd)
    (hruleA : Pd + max (Pd / 5) 200 ≤ Pr)
    (had : ad ≤ s * ((1 + κ) * Pd)) (har : s * ((1 - κ) * Pr) ≤ ar) :
    ad ≤ ar := by
  have key : (1 + κ) * Pd ≤ (1 - κ) * Pr := by
    have hm1 := le_max_left (Pd / 5) 200
    have hm2 := le_max_right (Pd / 5) 200
    set g := max (Pd / 5) 200
    have h1 := mul_le_mul_of_nonneg_left hruleA (by linarith : (0:ℝ) ≤ 1 - κ)
    have h3 : κ * g ≤ g / 11 := by nlinarith
    by_cases hP : Pd ≤ 1000
    · have : κ * Pd ≤ 1000 / 11 := by nlinarith
      nlinarith
    · have : κ * Pd ≤ Pd / 11 := by nlinarith
      nlinarith
  have := mul_le_mul_of_nonneg_left key hs.le
  linarith

/-- **Rule A's 20% term limits κ to 1/11.** For `1/11 < κ`, a data path of
1000 ps with the request exactly at rule A's bound (1200 ps) is violated by
real delays the model allows (request at `1-κ`, data at `1+κ`, θ = 0). -/
theorem ruleA_tight {κ : ℝ} (hκ : 1/11 < κ) :
    (1000:ℝ) + max (1000 / 5) 200 ≤ 1200 ∧ (1 - κ) * 1200 < (1 + κ) * 1000 := by
  refine ⟨by norm_num, by linarith⟩

/-! ## 5. Estimating κ from ring oscillators on one die

A ring is a closed path. On one die (one shared corner, one session) ring `i`
measures `rᵢ = measured/predicted = s·(1 + εᵢ)` with `|εᵢ| ≤ κ` (path-level
LocalScatter, `path_scatter`). The scale `s` is unknown, but any two rings
bound κ from below. -/

/-- Two rings on one die: `κ ≥ (rᵢ - rⱼ)/(rᵢ + rⱼ)`, stated without division. -/
theorem ring_kappa_lower {κ s ri rj : ℝ} (hκ1 : κ ≤ 1) (hκm : -1 ≤ κ)
    (hi : Scat κ s ri) (hj : Scat κ s rj) : ri - rj ≤ κ * (ri + rj) := by
  obtain ⟨_, hi2⟩ := hi
  obtain ⟨hj1, _⟩ := hj
  have a := mul_le_mul_of_nonneg_left hi2 (by linarith : (0:ℝ) ≤ 1 - κ)
  have b := mul_le_mul_of_nonneg_left hj1 (by linarith : (0:ℝ) ≤ 1 + κ)
  nlinarith

/-- The 7-link population of `ro_many_top` (cells/hw/README.md: ratios from
0.773 to 1.470 on one die, one session) is inconsistent with rule E's
`κ = 0.1988` under proportional SharedCorner + path-level LocalScatter:
those two rings alone force `κ ≥ 0.697/2.243 ≈ 0.311`. -/
theorem guard_refuted_by_7link_rings :
    ¬ ∃ s : ℝ, 0 < s ∧ Scat kappaE s (1470/1000) ∧ Scat kappaE s (773/1000) := by
  rintro ⟨s, _, hi, hj⟩
  have := ring_kappa_lower (by unfold kappaE; norm_num) (by unfold kappaE; norm_num) hi hj
  unfold kappaE at this
  norm_num at this

end Formal.Core.Corner

end
