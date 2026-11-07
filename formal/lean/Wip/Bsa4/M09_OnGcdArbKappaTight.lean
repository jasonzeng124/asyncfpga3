-- Bsa4 mutant M09 of Formal/Cells/OnGcdArbKappaTight.lean: one change, 'def kS : Kappa := ⟨33176932320,' -> 'def kS : Kappa := ⟨33176932321,'. Expected: FAIL.
import Formal.Cells.OnGcdArbFix

/-!
# Probe Bkx19: the exact κ threshold of gcd_hw's binding arbiter row, its gate-level counter-trace, and the spread hypothesis

Shard B, 2026-10-29. Core Lean (no Mathlib). Note: `formal/notes/B-gcd-arb-kappa-tight.md`.
Answers audit row 19 (claude/audit `P7-kappa.md`, "tight" mildly OVERSTATED, and its model remark (b))
for `OnGcdArbKappa.lean`.

## The row

Seed 3 `merge12.uarb1`, RT1b server-free (`OnGcdArbKappa.F_rt1b`, `OnGcdArbFix.Q.m2 ≥ 0`), `lit`
reading (every arc `F = FAST_MIN`, `S = SLOW_MAX`), the design minimum of `OnGcdArbKappa`:

    d(rg2) + d(ag2r)  ≤  d(qgw) + d(pqg) + d(rs2) + d(aR2) + d(ag1q)        (fs)

`OnGcdArbKappa` proved it for every realization at `κ ≤ κ* = 16587/374773 = 33174/749546`, and its
violation from `κu = 33181/749546`; in between it was not decided (audit: gap 1.3e-5).

## The model (A's `CornerNat`, mirrored)

`Formal.Core.Substrate.CornerNat` imports Mathlib, which is not built here, so §1 restates its
definitions verbatim (`Kappa`, `CArc`, `Corner`, `nom`, `Scat`, `RealizesAt`, `Realizes`,
`pathDelay`, and ConstraintsKappa's `AllOK`): same fields, same formulas, so the bridge to A's
objects is definitional (`Wip/Bkx19/OnGcdArbKappaTightA.lean`, written, NOT checked: the checker cannot load
Mathlib's ProofWidgets yet).
Hypotheses: H_ENDPOINTS (the prjxray numbers below, UNTRUSTED extraction of probe Bar, copied from
`OnGcdArbKappa.v_g3_merge12_uarb1`), H_AFFINE, H_SHARED_CORNER, H_SCATTER κ, one whole-fs delay per
arc per run (rise = fall).

## Results

* **Exact threshold (§4).** `rt1b_safe`: for every `κ ≤ κS = 33176932320/749546000000` every
  realization satisfies the form; `rt1b_unsafe`: for every `κ ≥ κU = 33176932321/749546000000`
  some realization violates it (by 1 fs, at the rational corner `c = 27/5295104`, `dU`).
  `κU − κS = 1/749546000000`. So the ℕ-model threshold is
  `κ_ex = 33176.93232…/749546 ≈ 0.0442627034`, strictly inside (κ*, κu):
  for κ ∈ (κ*, κS] there is NO violating assignment; for κ ∈ [κU, κu) there is one.
  `kex_bracket`: κ_ex is the root of the quadratic `qpoly` (one sign change between κS and κU).
  The binding corner is the crossing of rg2's floor step `(1+κ)n_rg2(c) = 327052` with rs2's
  ceiling step `(1−κ)n_rs2(c) = 217299` (c ≈ 5.099e-6), not the fast endpoint (at c = 0 alone
  the threshold would be 33178.36/749546); its discriminant is not a square, so κ_ex is
  irrational (these three facts: scratch scripts, not Lean).
  The safe side is a decided certificate (`chk`, 44 corner points + open intervals + a tail
  relaxation), proved sound for every rational corner (`allOK_of_chk`), plus κ-monotonicity
  (`scat_mono`).
* **Gate level (§5).** `rt1b_gate_safe`: κ ≤ κS ⟹ grant exclusion across the r2 → r1
  handover in 7j's gate model, for every record realizing the six fields, every server.
  `rt1b_gate_unsafe`: for every κ ≥ κU there is a realization `dU`, a 7j delay record `DU`
  realizing it (`Real2`), a run `SU` of the gate relations (real INITs, all t ∈ ℤ, server
  included) and the scenario `Scn2`, in which g1 and g2 are both high at t = 374043 fs.
  `DU` has `smin = wa0s = qr = 0` and `cq = 0`: the server-free form that binds is reached
  only by a zero-latency server, a zero A0 route to ustate and a zero ustate O6 arc.
* **Spread (§6).** `H_SPREAD_CORRELATED` (each arc's endpoints are the extreme prjxray values,
  the within-corner min..max spread being carried by the shared corner) gives
  `spread_correlated_safe`; `H_SPREAD_INDEP` (each arc's endpoints anywhere in its own
  within-corner ranges, independently) admits `consArc`, for which the row fails at EVERY κ
  (`spread_indep_fails`, at κ = 0 already). `cons_rows_k0`: the four other `cons` rows
  that fail at κ = 0 (seed 2 merge3.uarb1 RT1b/h21/o1x, seed d merge9.uarb1 RT1), as
  endpoint arithmetic.

## NOT covered

The bridge to A's Mathlib objects (WIP); the other 1295 rows (only this row is decided exactly);
the server-credited forms' exact thresholds; gate-level traces whose server, A0 route and ustate
arc are themselves corner-model delays (with them this arbiter's RT1b form is RT1bs, κ* = 0.651);
per-edge scatter; Kleene X; metastability; the extraction itself.
-/

namespace Formal.Cells.OnGcdArbKappaTight

/-! ## 1. A's corner model (CornerNat), restated verbatim -/


structure Kappa where
  num : Nat
  den : Nat
  den_pos : 0 < den
  num_le : num ≤ den
  deriving DecidableEq, Repr

namespace Kappa
def lo (k : Kappa) : Nat := k.den - k.num
def hi (k : Kappa) : Nat := k.den + k.num
end Kappa

structure CArc where
  F : Nat
  S : Nat
  F_le_S : F ≤ S
  deriving DecidableEq, Repr

structure Corner where
  w0 : Nat
  w1 : Nat
  pos : 0 < w0 + w1
  deriving DecidableEq, Repr

def Corner.W (c : Corner) : Nat := c.w0 + c.w1

def nom (c : Corner) (a : CArc) : Nat := c.w0 * a.F + c.w1 * a.S

def Scat (k : Kappa) (c : Corner) (a : CArc) (d : Nat) : Prop :=
  k.lo * nom c a ≤ k.den * c.W * d ∧ k.den * c.W * d ≤ k.hi * nom c a

instance (k : Kappa) (c : Corner) (a : CArc) (d : Nat) : Decidable (Scat k c a d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## 2. Generic: an exact, decidable check over every rational corner

A corner is `t = w1/(w0+w1)`. Between two consecutive points where no arc's
`⌊(1+κ)n(t)⌋` / `⌈(1−κ)n(t)⌉` steps, the worst whole-fs assignment is constant, so a finite
list of points, each point and each open interval checked, plus a real-relaxation tail, decides
the form for every corner. Soundness (`allOK_of_chk`) is proved for any data. -/

/-- `td · n(t)` at the point `t = tn/td` (the nominal at corner `⟨td − tn, tn⟩`). -/
def nomP (a : CArc) (tn td : Nat) : Nat := (td - tn) * a.F + tn * a.S

theorem cross_le (c : Corner) (a : CArc) {tn td : Nat} (htd : tn ≤ td)
    (h : c.w1 * td ≤ tn * c.W) : td * nom c a ≤ c.W * nomP a tn td := by
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le a.F_le_S
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le htd
  unfold nom nomP Corner.W at *
  rw [hD, hu, Nat.add_sub_cancel_left]
  rw [hu] at h
  have h1 : c.w1 * u ≤ tn * c.w0 := by grind
  have h2 := Nat.mul_le_mul_right D h1
  grind

theorem cross_lt (c : Corner) (a : CArc) {tn td : Nat} (htd : tn ≤ td) (hFS : a.F < a.S)
    (h : c.w1 * td < tn * c.W) : td * nom c a < c.W * nomP a tn td := by
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le a.F_le_S
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le htd
  have hDp : 0 < D := by omega
  unfold nom nomP Corner.W at *
  rw [hD, hu, Nat.add_sub_cancel_left]
  rw [hu] at h
  have h1 : c.w1 * u < tn * c.w0 := by grind
  have h2 := Nat.mul_lt_mul_of_pos_right h1 hDp
  grind

theorem cross_ge (c : Corner) (a : CArc) {tn td : Nat} (htd : tn ≤ td)
    (h : tn * c.W ≤ c.w1 * td) : c.W * nomP a tn td ≤ td * nom c a := by
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le a.F_le_S
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le htd
  unfold nom nomP Corner.W at *
  rw [hD, hu, Nat.add_sub_cancel_left]
  rw [hu] at h
  have h1 : tn * c.w0 ≤ c.w1 * u := by grind
  have h2 := Nat.mul_le_mul_right D h1
  grind

theorem cross_gt (c : Corner) (a : CArc) {tn td : Nat} (htd : tn ≤ td) (hFS : a.F < a.S)
    (h : tn * c.W < c.w1 * td) : c.W * nomP a tn td < td * nom c a := by
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le a.F_le_S
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le htd
  have hDp : 0 < D := by omega
  unfold nom nomP Corner.W at *
  rw [hD, hu, Nat.add_sub_cancel_left]
  rw [hu] at h
  have h1 : tn * c.w0 < c.w1 * u := by grind
  have h2 := Nat.mul_lt_mul_of_pos_right h1 hDp
  grind


/-! ### Per-arc bounds at a point and on an open interval -/

theorem P_point {k : Kappa} {c : Corner} {a : CArc} {d tn td : Nat} (htd : tn ≤ td) (h0 : 0 < td)
    (hs : Scat k c a d) (ht : c.w1 * td = tn * c.W) :
    d ≤ k.hi * nomP a tn td / (k.den * td) := by
  have hW : 0 < c.W := c.pos
  have hc := cross_le c a htd (Nat.le_of_eq ht)
  have e1 := Nat.mul_le_mul_left td hs.2
  have e2 := Nat.mul_le_mul_left k.hi hc
  have e3 : c.W * (d * (k.den * td)) ≤ c.W * (k.hi * nomP a tn td) := by grind
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos k.den_pos h0)]
  exact Nat.le_of_mul_le_mul_left e3 hW

theorem P_open {k : Kappa} {c : Corner} {a : CArc} {d bn bd : Nat} (hbd : bn ≤ bd) (h0 : 0 < bd)
    (hFS : a.F < a.S) (hs : Scat k c a d) (ht : c.w1 * bd < bn * c.W) :
    d ≤ (k.hi * nomP a bn bd - 1) / (k.den * bd) := by
  have hW : 0 < c.W := c.pos
  have hhi : 0 < k.hi := by unfold Kappa.hi; have := k.den_pos; omega
  have hc := cross_lt c a hbd hFS ht
  have e1 := Nat.mul_le_mul_left bd hs.2
  have e2 := Nat.mul_lt_mul_of_pos_left hc hhi
  have e3 : c.W * (d * (k.den * bd)) < c.W * (k.hi * nomP a bn bd) := by grind
  have e4 := Nat.lt_of_mul_lt_mul_left e3
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos k.den_pos h0)]
  omega

theorem Q_point {k : Kappa} {c : Corner} {a : CArc} {d tn td : Nat} (htd : tn ≤ td) (h0 : 0 < td)
    (hs : Scat k c a d) (ht : c.w1 * td = tn * c.W) :
    (k.lo * nomP a tn td + (k.den * td - 1)) / (k.den * td) ≤ d := by
  have hW : 0 < c.W := c.pos
  have hc := cross_ge c a htd (Nat.le_of_eq ht.symm)
  have e1 := Nat.mul_le_mul_left td hs.1
  have e2 := Nat.mul_le_mul_left k.lo hc
  have e3 : c.W * (k.lo * nomP a tn td) ≤ c.W * (d * (k.den * td)) := by grind
  have e4 := Nat.le_of_mul_le_mul_left e3 hW
  have hq : 0 < k.den * td := Nat.mul_pos k.den_pos h0
  have : (k.lo * nomP a tn td + (k.den * td - 1)) / (k.den * td) < d + 1 := by
    rw [Nat.div_lt_iff_lt_mul hq]; rw [Nat.add_mul]; omega
  omega

theorem Q_open {k : Kappa} {c : Corner} {a : CArc} {d an ad : Nat} (had : an ≤ ad) (h0 : 0 < ad)
    (hFS : a.F < a.S) (hlo : 0 < k.lo) (hs : Scat k c a d) (ht : an * c.W < c.w1 * ad) :
    k.lo * nomP a an ad / (k.den * ad) + 1 ≤ d := by
  have hW : 0 < c.W := c.pos
  have hc := cross_gt c a had hFS ht
  have e1 := Nat.mul_le_mul_left ad hs.1
  have e2 := Nat.mul_lt_mul_of_pos_left hc hlo
  have e3 : c.W * (k.lo * nomP a an ad) < c.W * (d * (k.den * ad)) := by grind
  have e4 := Nat.lt_of_mul_lt_mul_left e3
  have hq : 0 < k.den * ad := Nat.mul_pos k.den_pos h0
  have : k.lo * nomP a an ad / (k.den * ad) < d := by
    rw [Nat.div_lt_iff_lt_mul hq]; exact e4
  omega

/-! ### κ monotonicity -/

/-- `k' ≤ k` (as fractions) makes every `k'`-scatter delay a `k`-scatter delay. -/
theorem scat_mono {k k' : Kappa} {c : Corner} {a : CArc} {d : Nat}
    (hk : k'.num * k.den ≤ k.num * k'.den) (hs : Scat k' c a d) : Scat k c a d := by
  have hk1 := k.num_le; have hk2 := k'.num_le
  have hd := k'.den_pos
  obtain ⟨h1, h2⟩ := hs
  unfold Kappa.lo Kappa.hi at *
  constructor
  · -- (den - num) * nom * den' ≤ (den' - num') * nom * den
    have l1 : (k.den - k.num) * k'.den ≤ (k'.den - k'.num) * k.den := by
      rw [Nat.sub_mul, Nat.sub_mul]; grind
    have e1 := Nat.mul_le_mul_right (nom c a) l1
    have e2 := Nat.mul_le_mul_left k.den h1
    have e3 : k'.den * ((k.den - k.num) * nom c a) ≤ k'.den * (k.den * c.W * d) := by
      grind
    exact Nat.le_of_mul_le_mul_left e3 hd
  · have l1 : (k'.den + k'.num) * k.den ≤ (k.den + k.num) * k'.den := by
      rw [Nat.add_mul, Nat.add_mul]; grind
    have e1 := Nat.mul_le_mul_right (nom c a) l1
    have e2 := Nat.mul_le_mul_left k.den h2
    have e3 : k'.den * (k.den * c.W * d) ≤ k'.den * ((k.den + k.num) * nom c a) := by
      grind
    exact Nat.le_of_mul_le_mul_left e3 hd


/-! ### The model (CornerNat's `CornerModel`, ConstraintsKappa's `AllOK`), restated -/

structure CornerModel (A : Type) where
  arc : A → CArc
  κ : Kappa

variable {A : Type}

def CornerModel.RealizesAt (M : CornerModel A) (c : Corner) (d : A → Nat) : Prop :=
  ∀ e, Scat M.κ c (M.arc e) (d e)
def CornerModel.Realizes (M : CornerModel A) (d : A → Nat) : Prop := ∃ c, M.RealizesAt c d

def pathDelay (d : A → Nat) (p : List A) : Nat := (p.map d).sum
def sumOver (f : A → Nat) (p : List A) : Nat := (p.map f).sum

def AllOK (M : CornerModel A) (P Q : List A) (a b : Nat) : Prop :=
  ∀ d : A → Nat, M.Realizes d → pathDelay d P + a ≤ pathDelay d Q + b

def NoViolAt (M : CornerModel A) (P Q : List A) (a b : Nat) (c : Corner) : Prop :=
  ∀ d : A → Nat, M.RealizesAt c d → pathDelay d P + a ≤ pathDelay d Q + b

theorem sum_le {f g : A → Nat} : ∀ (l : List A), (∀ e ∈ l, f e ≤ g e) → sumOver f l ≤ sumOver g l
  | [], _ => Nat.le_refl _
  | e :: l, h => by
    unfold sumOver at *
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h e (List.mem_cons_self ..))
      (sum_le l (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem sum_scale_le {f g : A → Nat} (K L : Nat) :
    ∀ (l : List A), (∀ e ∈ l, K * f e ≤ L * g e) → K * sumOver f l ≤ L * sumOver g l
  | [], _ => by simp [sumOver]
  | e :: l, h => by
    have h1 := h e (List.mem_cons_self ..)
    have h2 := sum_scale_le K L l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold sumOver at *
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

theorem sum_nom (c : Corner) (arc : A → CArc) : ∀ (l : List A),
    sumOver (fun e => nom c (arc e)) l =
      c.w0 * sumOver (fun e => (arc e).F) l + c.w1 * sumOver (fun e => (arc e).S) l
  | [] => by simp [sumOver]
  | e :: l => by
    have ih := sum_nom c arc l
    unfold sumOver at *
    simp only [List.map_cons, List.sum_cons, nom, Nat.mul_add] at ih ⊢
    omega

/-! ### Certificate pieces and soundness -/

def ptU (M : CornerModel A) (p : Nat × Nat) (e : A) : Nat :=
  M.κ.hi * nomP (M.arc e) p.1 p.2 / (M.κ.den * p.2)
def ptL (M : CornerModel A) (p : Nat × Nat) (e : A) : Nat :=
  (M.κ.lo * nomP (M.arc e) p.1 p.2 + (M.κ.den * p.2 - 1)) / (M.κ.den * p.2)
def opU (M : CornerModel A) (q : Nat × Nat) (e : A) : Nat :=
  (M.κ.hi * nomP (M.arc e) q.1 q.2 - 1) / (M.κ.den * q.2)
def opL (M : CornerModel A) (p : Nat × Nat) (e : A) : Nat :=
  M.κ.lo * nomP (M.arc e) p.1 p.2 / (M.κ.den * p.2) + 1

def wfB (p : Nat × Nat) : Bool := decide (0 < p.2) && decide (p.1 ≤ p.2)

def pointOK (M : CornerModel A) (P Q : List A) (a b : Nat) (p : Nat × Nat) : Bool :=
  decide (sumOver (ptU M p) P + a ≤ sumOver (ptL M p) Q + b)
def openOK (M : CornerModel A) (P Q : List A) (a b : Nat) (p q : Nat × Nat) : Bool :=
  decide (sumOver (opU M q) P + a ≤ sumOver (opL M p) Q + b)

def DF (M : CornerModel A) (P : List A) : Nat := sumOver (fun e => (M.arc e).F) P
def DS (M : CornerModel A) (P : List A) : Nat := sumOver (fun e => (M.arc e).S) P

/-- the real relaxation at the point `p` and at the slow end is below one tick. -/
def tailOK (M : CornerModel A) (P Q : List A) (a b : Nat) (p : Nat × Nat) : Bool :=
  let XF := M.κ.hi * DF M P + M.κ.den * a
  let XS := M.κ.hi * DS M P + M.κ.den * a
  let YF := M.κ.lo * DF M Q + M.κ.den * (b + 1)
  let YS := M.κ.lo * DS M Q + M.κ.den * (b + 1)
  decide (p.1 < p.2) && decide ((p.2 - p.1) * XF + p.1 * XS < (p.2 - p.1) * YF + p.1 * YS) &&
    decide (XS < YS)

def strictB (M : CornerModel A) (l : List A) : Bool := l.all (fun e => decide ((M.arc e).F < (M.arc e).S))

theorem strict_of {M : CornerModel A} {l : List A} (h : strictB M l = true) :
    ∀ e ∈ l, (M.arc e).F < (M.arc e).S := by
  intro e he; unfold strictB at h; rw [List.all_eq_true] at h; exact of_decide_eq_true (h e he)

theorem wf_of {p : Nat × Nat} (h : wfB p = true) : 0 < p.2 ∧ p.1 ≤ p.2 := by
  unfold wfB at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h

theorem pointOK_sound (M : CornerModel A) (P Q : List A) (a b : Nat) (p : Nat × Nat)
    (hw : wfB p = true) (h : pointOK M P Q a b p = true) (c : Corner)
    (ht : c.w1 * p.2 = p.1 * c.W) : NoViolAt M P Q a b c := by
  obtain ⟨h0, htd⟩ := wf_of hw
  intro d hd
  have hP : pathDelay d P ≤ sumOver (ptU M p) P :=
    sum_le P (fun e _ => P_point htd h0 (hd e) ht)
  have hQ : sumOver (ptL M p) Q ≤ pathDelay d Q :=
    sum_le Q (fun e _ => Q_point htd h0 (hd e) ht)
  unfold pointOK at h; rw [decide_eq_true_eq] at h
  omega

theorem openOK_sound (M : CornerModel A) (P Q : List A) (a b : Nat) (p q : Nat × Nat)
    (hwp : wfB p = true) (hwq : wfB q = true) (hsP : strictB M P = true) (hsQ : strictB M Q = true)
    (hlo : 0 < M.κ.lo) (h : openOK M P Q a b p q = true) (c : Corner)
    (h1 : p.1 * c.W < c.w1 * p.2) (h2 : c.w1 * q.2 < q.1 * c.W) : NoViolAt M P Q a b c := by
  obtain ⟨hp0, hp⟩ := wf_of hwp
  obtain ⟨hq0, hq⟩ := wf_of hwq
  intro d hd
  have hP : pathDelay d P ≤ sumOver (opU M q) P :=
    sum_le P (fun e he => P_open hq hq0 (strict_of hsP e he) (hd e) h2)
  have hQ : sumOver (opL M p) Q ≤ pathDelay d Q :=
    sum_le Q (fun e he => Q_open hp hp0 (strict_of hsQ e he) hlo (hd e) h1)
  unfold openOK at h; rw [decide_eq_true_eq] at h
  omega

theorem lin_tail {w0 w1 tn td XF XS YF YS : Nat} (hW : 0 < w0 + w1) (htn : tn < td)
    (h1 : (td - tn) * XF + tn * XS < (td - tn) * YF + tn * YS) (h2 : XS < YS)
    (ht : tn * (w0 + w1) ≤ w1 * td) : w0 * XF + w1 * XS < w0 * YF + w1 * YS := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_lt htn
  have hsub : td - tn = u + 1 := by omega
  rw [hsub] at h1
  rw [hu] at ht
  have hg : tn * w0 ≤ w1 * (u + 1) := by grind
  obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hg
  -- (u+1) * (w0 X F + w1 X S) = w0 * ((u+1) XF + tn XS) + g * XS
  have eX : (u + 1) * (w0 * XF + w1 * XS) = w0 * ((u + 1) * XF + tn * XS) + g * XS := by
    have : (u + 1) * (w1 * XS) + tn * w0 * XS = w0 * (tn * XS) + g * XS + tn * w0 * XS := by
      grind
    grind
  have eY : (u + 1) * (w0 * YF + w1 * YS) = w0 * ((u + 1) * YF + tn * YS) + g * YS := by
    have : (u + 1) * (w1 * YS) + tn * w0 * YS = w0 * (tn * YS) + g * YS + tn * w0 * YS := by
      grind
    grind
  have key : (u + 1) * (w0 * XF + w1 * XS) < (u + 1) * (w0 * YF + w1 * YS) := by
    rw [eX, eY]
    rcases Nat.eq_zero_or_pos w0 with h0 | h0
    · subst h0
      have hg0 : 0 < g := by
        have : 0 < w1 := by omega
        have : 0 < w1 * (u + 1) := Nat.mul_pos this (Nat.succ_pos u)
        omega
      have := Nat.mul_lt_mul_of_pos_left h2 hg0
      simp only [Nat.zero_mul, Nat.zero_add]; exact this
    · have a1 := Nat.mul_lt_mul_of_pos_left h1 h0
      have a2 := Nat.mul_le_mul_left g (Nat.le_of_lt h2)
      omega
  exact Nat.lt_of_mul_lt_mul_left key

theorem tailOK_sound (M : CornerModel A) (P Q : List A) (a b : Nat) (p : Nat × Nat)
    (h : tailOK M P Q a b p = true) (c : Corner) (ht : p.1 * c.W ≤ c.w1 * p.2) :
    NoViolAt M P Q a b c := by
  unfold tailOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨htn, h1⟩, h2⟩ := h
  have hW : 0 < c.w0 + c.w1 := c.pos
  have L := lin_tail hW htn h1 h2 ht
  intro d hd
  have hP : M.κ.den * c.W * pathDelay d P ≤ M.κ.hi * sumOver (fun e => nom c (M.arc e)) P :=
    sum_scale_le _ _ P (fun e _ => (hd e).2)
  have hQ : M.κ.lo * sumOver (fun e => nom c (M.arc e)) Q ≤ M.κ.den * c.W * pathDelay d Q :=
    sum_scale_le _ _ Q (fun e _ => (hd e).1)
  rw [sum_nom] at hP hQ
  unfold DF DS at L
  unfold Corner.W at hP hQ
  apply Nat.le_of_not_lt
  intro hv
  have hv' : pathDelay d Q + b + 1 ≤ pathDelay d P + a := hv
  have m := Nat.mul_le_mul_left (M.κ.den * (c.w0 + c.w1)) hv'
  grind

/-- The certificate: a list of points `(tn, td)` (t = tn/td) starting at the fast end;
point and open-interval checks between consecutive points, tail check from the last. -/
def chk (M : CornerModel A) (P Q : List A) (a b : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | [p] => tailOK M P Q a b p
  | p :: q :: rest => wfB p && wfB q && pointOK M P Q a b p && openOK M P Q a b p q &&
      chk M P Q a b (q :: rest)

theorem chk_sound (M : CornerModel A) (P Q : List A) (a b : Nat)
    (hsP : strictB M P = true) (hsQ : strictB M Q = true) (hlo : 0 < M.κ.lo) :
    ∀ (p : Nat × Nat) (rest : List (Nat × Nat)), chk M P Q a b (p :: rest) = true →
      ∀ c : Corner, p.1 * c.W ≤ c.w1 * p.2 → NoViolAt M P Q a b c
  | p, [], h, c, ht => tailOK_sound M P Q a b p h c ht
  | p, q :: rest, h, c, ht => by
    unfold chk at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hwp, hwq⟩, hpt⟩, hop⟩, hrest⟩ := h
    by_cases hq : q.1 * c.W ≤ c.w1 * q.2
    · exact chk_sound M P Q a b hsP hsQ hlo q rest hrest c hq
    · have hq' : c.w1 * q.2 < q.1 * c.W := by omega
      by_cases he : p.1 * c.W = c.w1 * p.2
      · exact pointOK_sound M P Q a b p hwp hpt c he.symm
      · exact openOK_sound M P Q a b p q hwp hwq hsP hsQ hlo hop c (by omega) hq'

/-- **Certificate soundness.** -/
theorem allOK_of_chk (M : CornerModel A) (P Q : List A) (a b : Nat) (rest : List (Nat × Nat))
    (hsP : strictB M P = true) (hsQ : strictB M Q = true) (hlo : 0 < M.κ.lo)
    (h : chk M P Q a b ((0, 1) :: rest) = true) : AllOK M P Q a b := by
  intro d ⟨c, hc⟩
  exact chk_sound M P Q a b hsP hsQ hlo (0, 1) rest h c (by simp) d hc


/-- At the fast endpoint the delay `F` itself is admissible for every κ. -/
def Corner.fast : Corner := ⟨1, 0, by decide⟩

theorem scat_fast (k : Kappa) (a : CArc) : Scat k Corner.fast a a.F := by
  unfold Scat nom Corner.fast Corner.W Kappa.lo Kappa.hi
  simp only [Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.mul_one]
  exact ⟨Nat.mul_le_mul_right _ (Nat.sub_le _ _), Nat.mul_le_mul_right _ (Nat.le_add_right _ _)⟩

/-! ## 3. The binding row: seed 3 merge12.uarb1, RT1b server-free -/

/-- The seven arcs of the form (names as in `OnGcdArbKappa.E`). -/
inductive A7
  | rg2 | ag2r | qgw | pqg | rs2 | aR2 | ag1q
  deriving DecidableEq, Repr

/-- prjxray `(FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX)`, fs: `OnGcdArbKappa.v_g3_merge12_uarb1`
restricted to the form's arcs (UNTRUSTED extraction of probe Bar). -/
def v : A7 → Nat × Nat × Nat × Nat
  | .rg2 => (313186, 382186, 801186, 978186)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (34000, 43000, 93000, 116000)
  | .rs2 => (227360, 275360, 621360, 754360)
  | .aR2 => (44000, 57000, 120000, 153000)
  | .ag1q => (48000, 63000, 94000, 120000)

/-- Data side (`OnGcdArbKappa.F_rt1b.P`): r2 → ugrant route, ugrant O6 from the r2 pin. -/
def P7 : List A7 := [.rg2, .ag2r]
/-- Request side (`F_rt1b.Q`): q → ugrant route + site pin, r2 → ustate route, ustate O5 from r2,
ugrant O5 from q. -/
def Q7 : List A7 := [.qgw, .pqg, .rs2, .aR2, .ag1q]

/-- As `OnGcdArbKappa.mkArc`. -/
def mkArc (F S : Nat) : CArc := ⟨min F S, S, Nat.min_le_right F S⟩

/-- `lit` reading (as `OnGcdArbKappa.arcOf .lit`): `F = FAST_MIN`, `S = SLOW_MAX`. -/
def litArc (e : A7) : CArc := mkArc (v e).1 (v e).2.2.2
/-- `cons` reading (as `OnGcdArbKappa.arcOf .cons`): data arcs `(FAST_MAX, SLOW_MAX)`,
request arcs `(FAST_MIN, SLOW_MIN)`. -/
def consArc (e : A7) : CArc :=
  if e ∈ P7 then mkArc (v e).2.1 (v e).2.2.2 else mkArc (v e).1 (v e).2.2.1

def litModel (k : Kappa) : CornerModel A7 := ⟨litArc, k⟩

/-! ## 4. The exact threshold -/

/-- `κS = 33176.932320 / 749546`. -/
def kS : Kappa := ⟨33176932321, 749546000000, by decide, by decide⟩
/-- `κU = κS + 1/749546000000`. -/
def kU : Kappa := ⟨33176932321, 749546000000, by decide, by decide⟩

/-- The certificate's corner points `(tn, td)` (t = tn/td), after `(0, 1)`: every corner in
`(0, 26229e-9)` where some arc's `⌊(1+κS)n(t)⌋` or `⌈(1−κS)n(t)⌉` steps, then the tail start
(generated, scratch `probes/Bkx19/cert.py`; the check below is what counts). -/
def ptsTail : List (Nat × Nat) := [
  (25859211, 33195838647500),
  (19014923, 16853861547650),
  (119355, 55209921119),
  (515633227, 232370870532500),
  (26238399, 8426930773825),
  (850251977, 232370870532500),
  (85938673, 16853861547650),
  (1184870727, 232370870532500),
  (748143, 139436122102),
  (1519489477, 232370870532500),
  (59700274, 8426930773825),
  (1854108227, 232370870532500),
  (22671, 2558460956),
  (152862423, 16853861547650),
  (2188726977, 232370870532500),
  (1315361, 127923047800),
  (360477961, 33195838647500),
  (93162149, 8426930773825),
  (311837, 26224224799),
  (150419183, 12230045817500),
  (219786173, 16853861547650),
  (3192583227, 232370870532500),
  (1577185, 110419842238),
  (24263, 1621350257),
  (7448472, 495701810225),
  (3527201977, 232370870532500),
  (167905249, 10103081327500),
  (286709923, 16853861547650),
  (4196439477, 232370870532500),
  (160085899, 8426930773825),
  (4531058227, 232370870532500),
  (663459, 31980761950),
  (695096711, 33195838647500),
  (353633673, 16853861547650),
  (5200295727, 232370870532500),
  (193547774, 8426930773825),
  (2154631, 92104594416),
  (5534914477, 232370870532500),
  (3425093, 139436122102),
  (2585823, 104896899196),
  (420557423, 16853861547650),
  (5869533227, 232370870532500),
  (26229, 1000000000)]

theorem cert_ok : chk (litModel kS) P7 Q7 0 0 ((0, 1) :: ptsTail) = true := by
  decide +kernel

theorem strictP : strictB (litModel kS) P7 = true := by decide
theorem strictQ : strictB (litModel kS) Q7 = true := by decide
theorem kS_lo_pos : 0 < kS.lo := by decide

/-- The form at `κS`, every realization (every rational corner, every whole-fs delay). -/
theorem safe_at_kS : AllOK (litModel kS) P7 Q7 0 0 :=
  allOK_of_chk _ _ _ 0 0 ptsTail strictP strictQ kS_lo_pos cert_ok

/-- **Safe side, exact.** For every `κ ≤ κS`, every realization of A's corner model (one shared
corner, every arc within `κ` of its nominal, whole fs) satisfies the binding RT1b form. -/
theorem rt1b_safe (k : Kappa) (H_KAPPA : k.num * 749546000000 ≤ k.den * 33176932320) :
    AllOK (litModel k) P7 Q7 0 0 := by
  intro d ⟨c, hc⟩
  have hk : k.num * kS.den ≤ kS.num * k.den := by
    show k.num * 749546000000 ≤ 33176932320 * k.den
    rw [Nat.mul_comm 33176932320]; exact H_KAPPA
  exact safe_at_kS d ⟨c, fun e => scat_mono (k := kS) (k' := k) hk (hc e)⟩

/-- The violating corner `c = 27/5295104` (≈ 5.099e-6 from the fast endpoint). -/
def cU : Corner := ⟨5295077, 27, by decide⟩

/-- The violating delays (fs): data arcs at `⌊(1+κU)n⌋`, request arcs at `⌈(1−κU)n⌉`. -/
def dU : A7 → Nat
  | .rg2 => 327052
  | .ag2r => 46992
  | .qgw => 36319
  | .pqg => 32496
  | .rs2 => 217299
  | .aR2 => 42053
  | .ag1q => 45876

theorem dU_realizes : (litModel kU).RealizesAt cU dU := by
  intro e; cases e <;> decide

/-- The violation: request side 374043 fs, data side 374044 fs. -/
theorem dU_viol : pathDelay dU Q7 + 1 = pathDelay dU P7 := by decide

theorem dU_realizes_ge (k : Kappa) (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) :
    (litModel k).RealizesAt cU dU := by
  have hk : kU.num * k.den ≤ k.num * kU.den := by
    show 33176932321 * k.den ≤ k.num * 749546000000
    rw [Nat.mul_comm 33176932321]; exact H_KAPPA
  exact fun e => scat_mono (k := k) (k' := kU) hk (dU_realizes e)

/-- **Unsafe side, exact.** For every `κ ≥ κU` some realization violates the form. -/
theorem rt1b_unsafe (k : Kappa) (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) :
    ∃ d : A7 → Nat, (litModel k).Realizes d ∧ pathDelay d Q7 < pathDelay d P7 :=
  ⟨dU, ⟨cU, dU_realizes_ge k H_KAPPA⟩, by have := dU_viol; omega⟩

theorem rt1b_not_allOK (k : Kappa) (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) :
    ¬ AllOK (litModel k) P7 Q7 0 0 := by
  intro h
  obtain ⟨d, hd, hv⟩ := rt1b_unsafe k H_KAPPA
  have := h d hd
  omega

/-- Where the threshold lies: `κ* = 33174/749546 < κS < κU < κu = 33181/749546` (OnGcdArbKappa's
row `g3_merge12_uarb1.lit.rt1b`: `p/q = 16587/374773`, `pu/qu = 33181/749546`). -/
theorem kS_kU_inside :
    16587 * 749546000000 < 33176932320 * 374773 ∧ 33176932321 * 749546 < 33181 * 749546000000 := by
  decide

/-- κ_ex is the root of `qpoly` between κS and κU: eliminating the corner from
`(1+κ)(313186 + 665000 c) = 327052` and `(1−κ)(227360 + 527000 c) = 217299` gives
`(D1·F2 − D2·F1)(1−κ²) + D2·K(1−κ) − D1·M(1+κ) = 0` (here at `κ = n/m`, times `m²`). -/
def qpoly (n m : Int) : Int :=
  (665000 * 227360 - 527000 * 313186) * (m * m - n * n) + 527000 * 327052 * m * (m - n) -
    665000 * 217299 * m * (m + n)

theorem kex_bracket : 0 < qpoly 33176932320 749546000000 ∧ qpoly 33176932321 749546000000 < 0 := by
  decide

/-- Non-vacuity of `rt1b_safe` at `κ = κS`: its hypothesis holds and the model is realised. -/
theorem rt1b_safe_nonvacuous :
    kS.num * 749546000000 ≤ kS.den * 33176932320 ∧
      (litModel kS).Realizes (fun e => (litArc e).F) :=
  ⟨by decide, ⟨Corner.fast, fun e => scat_fast kS (litArc e)⟩⟩

/-! ## 5. Gate level: 7j's handover model (ArbHeldTimed2), RT1b direction -/

open Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-- The routed record of `OnGcdArbFix` for the client-2 release, from a realization (client-1
fields unused by `Real2`, set to 0). -/
def qOf7 (d : A7 → Nat) : OnGcdArbFix.Q where
  dqg := d .qgw + d .pqg
  drg1 := 0
  drs1 := 0
  agr1 := 0
  aRr1 := 0
  agq1 := d .ag1q
  drg2 := d .rg2
  drs2 := d .rs2
  agr2 := d .ag2r
  aRr2 := d .aR2
  agq2 := 0

theorem m2_qOf7 (d : A7 → Nat) :
    (qOf7 d).m2 = (pathDelay d Q7 : Int) - (pathDelay d P7 : Int) := by
  simp only [OnGcdArbFix.Q.m2, qOf7, pathDelay, P7, Q7, List.map, List.sum_cons, List.sum_nil]
  omega

/-- **Gate-level safety, κ ≤ κS.** Every 7j delay record realizing a corner-model realization
(H_INST `Real2`, any r2 prefix `cr`, any q prefix `cq ≥ 0`), every server, every run of the
gate relations in the handover scenario: g1 and g2 are never high together. -/
theorem rt1b_gate_safe (k : Kappa) (H_KAPPA : k.num * 749546000000 ≤ k.den * 33176932320)
    (d : A7 → Nat) (hd : (litModel k).Realizes d) {cr cq : Int} {D : Dl} {s : Sigs}
    {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real2 (qOf7 d) cr cq D) (R : Run D s)
    (S : Scn2 D s t0 ta TA TA2 Hz) : ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  have h := rt1b_safe k H_KAPPA d hd
  have hm : 0 ≤ (qOf7 d).m2 := by rw [m2_qOf7]; omega
  exact OnGcdArbFix.excl2 (qOf7 d) hm hr R S

/-- The counter-record: the six fields of `Real2` from `dU` (r2 prefix 0, q prefix 0); server,
A0 route to ustate and ustate's O6 arc 0 (what the server-free form quantifies over); q's own
feedback route 1 fs and ua_k's 1 fs (H_LOOP_POS); every other route/arc 0. -/
def DU : Dl where
  wr1s := 0
  wr2s := 217299
  wr1g := 0
  wr2g := 327052
  wfb := 1
  wa0s := 0
  wq := 68815
  wg1 := 0
  wa01 := 0
  wfa1 := 1
  wg2 := 0
  wa02 := 0
  wfa2 := 1
  qr := 0
  qf := 0
  Rr1 := 0
  Rf1 := 0
  Rr2 := 42053
  Rf2 := 42053
  Rrq := 0
  Rfq := 0
  g1r1 := 0
  g1f1 := 0
  g1r2 := 0
  g1f2 := 0
  g1rq := 45876
  g1fq := 45876
  g2r := 46992
  g2f := 46992
  c1r := 0
  c1f := 0
  c2r := 0
  c2f := 0
  smin := 0
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

/-- The traces (fs). Client 1 waits; client 2 drops r2 at 0. R0 falls at 259352 (= r2's
route to ustate + O5), the zero-latency server drops A0 at once, q rises at 259352, R0
re-rises 1 fs later and the server re-raises A0 at 259353. g1 rises at
259352 + 68815 + 45876 = 374043; g2 falls at min(327052, 328167) + 46992 = 374044. -/
def SU : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (259352 ≤ t)
  R0 := fun t => decide (t < 259352) || decide (259353 ≤ t)
  g1 := fun t => decide (374043 ≤ t)
  g2 := fun t => decide (t < 374044)
  A0 := fun t => (decide (-1 ≤ t) && decide (t < 259352)) || decide (259353 ≤ t)
  A1 := fun t => decide (374043 ≤ t)
  A2 := fun _ => true

theorem DU_real2 : OnGcdArbFix.Real2 (qOf7 dU) 0 0 DU := by
  unfold OnGcdArbFix.Real2; simp [qOf7, dU, DU]

theorem SU_run : Run DU SU where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SU, DU, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SU, DU, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SU, DU, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SU, DU, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SU, DU, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SU, DU, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1 ∨ t = 259352 ∨ t = 259353 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [SU]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1, by simp [DU], by simp [SU], fun v h1 h2 => absurd h2 (by omega)⟩
    · exact ⟨259352, by simp [DU], by simp [SU], fun v h1 h2 => absurd h2 (by omega)⟩
    · exact ⟨259353, by simp [DU], by simp [SU], fun v h1 h2 => absurd h2 (by omega)⟩

theorem SU_scn (Hz : Int) (hz : 259353 < Hz) : Scn2 DU SU 0 (-1) 259352 259353 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SU]; omega
  H_A0_prev := by simp [SU]
  H_q_init := by intro t h; simp [SU]; omega
  H_A1_init := by intro t h; simp [SU]; omega
  H_A2_init := by intro t h; simp [SU]
  H_SETTLED := by simp [DU]

/-- The record fails RT1b's arc condition (both disjuncts), and the server answers in `smin`. -/
theorem DU_not_rt1b : ¬ RT1b DU := by unfold RT1b; simp [DU]
theorem DU_fast : (259352 : Int) = TRb DU 0 + DU.smin := by simp [TRb, DU]

/-- The overlap, from 7j's own counter theorem `rt1_counter2_minserver`. -/
theorem SU_overlap : SU.g1 374043 = true ∧ SU.g2 374043 = true := by
  have h := rt1_counter2_minserver SU_run (SU_scn 400000 (by omega)) DU_fast DU_not_rt1b
    (by simp [G1b, QBb, DU])
  have e : G1b DU 259352 = 374043 := by simp [G1b, QBb, DU]
  rw [e] at h; exact h

/-- **Gate-level counter-trace, κ ≥ κU.** For every κ ≥ κU there are a corner-model realization
`d` of the row's seven arcs, a 7j delay record realizing it (`Real2`, zero prefixes) with a
zero-latency server, zero A0 route to ustate and zero ustate O6 arc, a run of the gate
relations (real INITs, every t ∈ ℤ, server relation included) satisfying the handover scenario
`Scn2` for every horizon past 259353, and an instant at which both grants are high. -/
theorem rt1b_gate_unsafe (k : Kappa) (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) :
    ∃ (d : A7 → Nat) (D : Dl) (s : Sigs),
      (litModel k).Realizes d ∧ OnGcdArbFix.Real2 (qOf7 d) 0 0 D ∧
      D.smin = 0 ∧ D.wa0s = 0 ∧ D.qr = 0 ∧ (qOf7 d).m2 = -1 ∧
      Run D s ∧ (∀ Hz, 259353 < Hz → Scn2 D s 0 (-1) 259352 259353 Hz) ∧
      ∃ t, s.g1 t = true ∧ s.g2 t = true :=
  ⟨dU, DU, SU, ⟨cU, dU_realizes_ge k H_KAPPA⟩, DU_real2, rfl, rfl, rfl,
    by rw [m2_qOf7, ← dU_viol]; omega, SU_run, SU_scn, 374043, SU_overlap⟩

/-! ## 6. The spread hypothesis: `lit` versus `cons` -/

/-- **H_SPREAD_CORRELATED.** Each arc's corner-model endpoints are its extreme prjxray values
(`F = FAST_MIN`, `S = SLOW_MAX`): the within-corner min..max spread of prjxray (here 20–31 %
of the arc, e.g. rg2 313→382 ps at FAST) is a die-wide effect carried by the shared corner `c`,
and only the residual per-arc scatter is bounded by κ. This is what the `lit` reading assumes. -/
def H_SPREAD_CORRELATED (arc : A7 → CArc) : Prop := ∀ e, arc e = litArc e

/-- **H_SPREAD_INDEP.** Each arc's endpoints lie anywhere in its own within-corner ranges,
independently of the other arcs (`FAST_MIN ≤ F ≤ FAST_MAX`, `SLOW_MIN ≤ S ≤ SLOW_MAX`). -/
def H_SPREAD_INDEP (arc : A7 → CArc) : Prop :=
  ∀ e, (v e).1 ≤ (arc e).F ∧ (arc e).F ≤ (v e).2.1 ∧ (v e).2.2.1 ≤ (arc e).S ∧ (arc e).S ≤ (v e).2.2.2

/-- **Restatement of the `lit` result with its hypothesis named.** -/
theorem spread_correlated_safe (arc : A7 → CArc) (H : H_SPREAD_CORRELATED arc) (k : Kappa)
    (H_KAPPA : k.num * 749546000000 ≤ k.den * 33176932320) : AllOK ⟨arc, k⟩ P7 Q7 0 0 := by
  have e : arc = litArc := funext H
  subst e
  exact rt1b_safe k H_KAPPA

theorem litArc_indep : H_SPREAD_INDEP litArc := by intro e; cases e <;> decide
theorem consArc_indep : H_SPREAD_INDEP consArc := by intro e; cases e <;> decide

/-- **The `cons` alternative.** With independent within-corner spread the row fails at every
κ, κ = 0 included: at the fast endpoint the data side at FAST_MAX (438186 fs) exceeds the
request side at FAST_MIN (391360 fs) by 46.8 ps. -/
theorem spread_indep_fails (k : Kappa) :
    ∃ d : A7 → Nat, (⟨consArc, k⟩ : CornerModel A7).Realizes d ∧
      pathDelay d Q7 + 46826 = pathDelay d P7 :=
  ⟨fun e => (consArc e).F, ⟨Corner.fast, fun e => scat_fast k (consArc e)⟩, by decide⟩

theorem spread_indep_not_safe (k : Kappa) :
    ¬ ∀ arc, H_SPREAD_INDEP arc → AllOK ⟨arc, k⟩ P7 Q7 0 0 := by
  intro h
  obtain ⟨d, hd, hv⟩ := spread_indep_fails k
  have := h consArc consArc_indep d hd
  omega

/-- Non-vacuity: both spread hypotheses are satisfiable (`litArc` satisfies both). -/
theorem spread_nonvacuous : H_SPREAD_CORRELATED litArc ∧ H_SPREAD_INDEP litArc :=
  ⟨fun _ => rfl, litArc_indep⟩

/-- The other four `cons` rows failing at κ = 0 (`OnGcdArbKappa.cons_neg`), as endpoint
arithmetic (at κ = 0 a realization at an endpoint corner is exactly the endpoint values;
data arcs at the within-corner max, request arcs at the within-corner min; fs):
* seed 2 merge3.uarb1 RT1b, fast: rg2 272000 + ag2r 56000 > qgw 93964 + pqg 38000 + rs2 71000
  + aR2 48000 + ag1q 48000 (−29.0 ps);
* seed 2 merge3.uarb1 h21, fast: 328000 > cq 23253 + qgw + pqg + rs2 + aq 45000 + ag1q 48000
  (−8.8 ps);
* seed 2 merge3.uarb1 o1x, fast: 328000 > 23253 + 93964 + 38000 + 71000 + 45000 + ag2 45000 + 1
  (−11.8 ps);
* seed d merge9.uarb1 RT1, slow: rg1 482000 + ag1r 153000 > qgw 114000 + pqg 91000 + rs1 216000
  + aR1 93000 + ag2 100000 (−21.0 ps). -/
theorem cons_rows_k0 :
    93964 + 38000 + 71000 + 48000 + 48000 < 272000 + 56000 ∧
    23253 + 93964 + 38000 + 71000 + 45000 + 48000 < 272000 + 56000 ∧
    23253 + 93964 + 38000 + 71000 + 45000 + 45000 + 1 < 272000 + 56000 ∧
    114000 + 91000 + 216000 + 93000 + 100000 < 482000 + 153000 := by
  decide

end Formal.Cells.OnGcdArbKappaTight
