import Formal.Cells.ConstraintsKappa
import Formal.Cells.OnGcdArbA0
import Formal.Cells.OnGcdArbFix
import Formal.Cells.ArbPin2

/-!
# Probe Bk3: every gcd_hw arbiter condition under shard A's corner model (κ thresholds)

Shard B. Notes: `formal/notes/B-gcd-arb-kappa.md`.

Every routed gcd_hw arbiter result of shard B (OnGcdArbA0: A0 fork + RT2/RT2b;
OnGcdArbFix: RT1/RT1b; ArbPin2: the bare-cell handover / opposite-sense κ
conditions) is safe at each consistent corner and unsafe in the independent
box. This file decides each one under A's model
(`Formal.Core.Substrate.CornerNat`: ONE shared corner, each arc's nominal delay
interpolated between its endpoints, each actual delay within `1 ± κ` of it),
using Bk2's exact check (`ConstraintsKappa.GenOK`, `allOK_of_gen`, `sandwich`).

Each condition is one form `ΣP + a ≤ ΣQ + b` over arc ids `E` (Bar's
extraction elements; a shared prefix, e.g. the A0 prefix `ac` of a fork or the
`r_k` prefix, is one element and cancels; the margins of the source files are
netted, so `Disj P Q` holds). Units: **fs** (Bar's numbers are exact at
0.001 ps, so no data rounding); the gate models are unit-free (one tick = 1 fs).

Two endpoint readings (both are A `CArc`s, cf. Bk1):
* `lit`: `F = FAST_MIN`, `S = SLOW_MAX` for every arc;
* `cons`: data-side arcs `(FAST_MAX, SLOW_MAX)`, request-side `(FAST_MIN, SLOW_MIN)`.
  At κ = 0 this is the within-corner range reading.

Per row (arbiter × reading × condition): `κ* = p/q`, the exact rational
`min_s (R_s + b − D_s − a)/(R_s + D_s)`.
* `row_safe`: κ ≤ κ* ⟹ the form holds for every realization (every corner,
  every per-arc scatter ≤ κ).
* `row_unsafe`: κ ≥ κu = `pu/qu` (κ* + n/(R_s+D_s), n arcs, ≤ 1.8e-5 above κ*)
  ⟹ some realization violates it. Rows with `neg = true` fail already at κ = 0.
* Bridges (§5) turn the forms into the gate-level theorems of the source files.
-/

namespace Formal.Cells.OnGcdArbKappa

open Formal.Core.Substrate
open Formal.Cells.ConstraintsKappa

-- `List.mem_of_getElem? … rfl` on the 1296-row list unfolds deeply.
set_option maxRecDepth 20000

/-! ## 1. Arc ids, data, readings, forms -/

/-- The arc ids: Bar's elements, plus `ag2r` (ugrant O6 read from the r2 pin; same prjxray
numbers as the q-pin arc `ag2`, but a different pin, so a different arc) and `srv`
(H_SERVER_GRAPH: the routed path ustate O5 (R0) → A0 driver output, as one arc). -/
inductive E
  | ac | dS1 | dS2 | d12 | es | e1 | e2 | ps | p1 | p2 | cq | qs | qgw | pqg | rs1 | rg1 | rs2 | rg2 | gw1 | pg1 | gw2 | pg2 | fa1 | fa2 | aq | aRq | aR1 | aR2 | ag1q | ag1r | ag2 | ac1 | ac2 | ag2r | srv
  deriving DecidableEq, Repr

/-- (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX), fs. -/
abbrev Quad := Nat × Nat × Nat × Nat

inductive Rd
  | lit | cons
  deriving DecidableEq, Repr

/-- A form `ΣP + a ≤ ΣQ + b` (fs). -/
structure Form where
  P : List E
  Q : List E
  a : Nat
  b : Nat
  /-- server-free RT1/RT1b form (OnGcdArbFix's "every server"; no A0 branch, no server). -/
  sf : Bool

/-- An arc from its endpoints (`min` makes `F ≤ S` hold by construction; on the data,
`F ≤ S` already, so `min F S = F`). -/
def mkArc (F S : Nat) : CArc := ⟨min F S, S, Nat.min_le_right F S⟩

/-- The arc of `e` in reading `rd` for form `f`. -/
def arcOf (rd : Rd) (f : Form) (v : E → Quad) (e : E) : CArc :=
  match rd with
  | .lit => mkArc (v e).1 (v e).2.2.2
  | .cons => if e ∈ f.P then mkArc (v e).2.1 (v e).2.2.2 else mkArc (v e).1 (v e).2.2.1

/-- A's corner model for one row. -/
def model (k : Kappa) (rd : Rd) (f : Form) (v : E → Quad) : CornerModel E := ⟨arcOf rd f v, k⟩

/-- The data and request paths as arcs (independent of κ). -/
def Dp (rd : Rd) (f : Form) (v : E → Quad) : CArc := pathArc (f.P.map (arcOf rd f v))
def Rq (rd : Rd) (f : Form) (v : E → Quad) : CArc := pathArc (f.Q.map (arcOf rd f v))

theorem path_P (k : Kappa) (rd : Rd) (f : Form) (v : E → Quad) :
    (model k rd f v).path f.P = Dp rd f v := rfl
theorem path_Q (k : Kappa) (rd : Rd) (f : Form) (v : E → Quad) :
    (model k rd f v).path f.Q = Rq rd f v := rfl

/-! ## 2. Rows and their decidable certificates -/

/-- One row: `neg` = fails at κ = 0; `κ* = p/q`; binding endpoint `s`; unsafe from `pu/qu`. -/
structure Row where
  name : String
  rd : Rd
  f : Form
  v : E → Quad
  neg : Bool
  p : Nat
  q : Nat
  s : Bool
  pu : Nat
  qu : Nat

def Row.D (r : Row) : CArc := Dp r.rd r.f r.v
def Row.R (r : Row) : CArc := Rq r.rd r.f r.v
def Row.n (r : Row) : Nat := r.f.P.length + r.f.Q.length

/-- `p/q ≤ (R_s + b − D_s − a)/(R_s + D_s)` at both endpoints, cleared (any form, any data). -/
def certFor (rd : Rd) (f : Form) (v : E → Quad) (p q : Nat) : Bool :=
  decide (p * (ep false (Rq rd f v) + ep false (Dp rd f v)) + q * (ep false (Dp rd f v) + f.a) ≤
      q * (ep false (Rq rd f v) + f.b)) &&
  decide (p * (ep true (Rq rd f v) + ep true (Dp rd f v)) + q * (ep true (Dp rd f v) + f.a) ≤
      q * (ep true (Rq rd f v) + f.b))

def Row.certSafe (r : Row) : Bool := certFor r.rd r.f r.v r.p r.q

/-- `pu/qu ≥ (R_s + b − D_s − a + n)/(R_s + D_s)` at the binding endpoint, cleared. -/
def Row.certUnsafe (r : Row) : Bool :=
  decide (r.qu * (ep r.s r.R + r.f.b + r.n) ≤ r.pu * (ep r.s r.R + ep r.s r.D) + r.qu * (ep r.s r.D + r.f.a))

/-- H_DISJ, decidably. -/
def disjB (f : Form) : Bool := f.P.all (fun e => decide (e ∉ f.Q))

def Row.ok (r : Row) : Bool :=
  decide (0 < r.q) && decide (0 < r.qu) && decide (r.pu ≤ r.qu) && decide (0 < r.n) &&
    (r.neg || (decide (r.p ≤ r.q) && r.certSafe)) && r.certUnsafe && disjB r.f

theorem disj_of (f : Form) (h : disjB f = true) : Disj f.P f.Q := by
  intro e he
  unfold disjB at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h e he)

/-! ## 3. Arithmetic -/

theorem safe_arith {num den p q R D a b : Nat} (hq : 0 < q) (hnd : num ≤ den)
    (hk : num * q ≤ den * p) (hc : p * (R + D) + q * (D + a) ≤ q * (R + b)) :
    (den + num) * D + den * a ≤ (den - num) * R + den * b := by
  have h1 : num * q * (R + D) ≤ den * p * (R + D) := Nat.mul_le_mul_right _ hk
  have h2 : den * (p * (R + D) + q * (D + a)) ≤ den * (q * (R + b)) := Nat.mul_le_mul_left _ hc
  have h3 : q * (num * (R + D) + den * D + den * a) ≤ q * (den * R + den * b) := by
    have e1 : q * (num * (R + D) + den * D + den * a) =
        num * q * (R + D) + den * (q * (D + a)) := by
      simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]; omega
    have e2 : den * (p * (R + D) + q * (D + a)) = den * p * (R + D) + den * (q * (D + a)) := by
      simp only [Nat.mul_add, Nat.mul_assoc]
    have e3 : q * (den * R + den * b) = den * (q * (R + b)) := by
      simp only [Nat.mul_add, Nat.mul_left_comm]
    omega
  have h4 := Nat.le_of_mul_le_mul_left h3 hq
  have h5 : (den - num) * R + num * R = den * R := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hnd]
  rw [Nat.add_mul]
  rw [Nat.mul_add] at h4
  omega

theorem unsafe_arith {num den pu qu R D a b n : Nat} (hq : 0 < qu) (hn : 0 < n) (hd : 0 < den)
    (hnd : num ≤ den) (hk : den * pu ≤ num * qu)
    (hc : qu * (R + b + n) ≤ pu * (R + D) + qu * (D + a)) :
    ¬ ((den + num) * D + den * a ≤ (den - num) * R + den * b + n * (den - 1)) := by
  have h1 : den * pu * (R + D) ≤ num * qu * (R + D) := Nat.mul_le_mul_right _ hk
  have h2 : den * (qu * (R + b + n)) ≤ den * (pu * (R + D) + qu * (D + a)) :=
    Nat.mul_le_mul_left _ hc
  have h3 : qu * (den * (R + b + n)) ≤ qu * (num * (R + D) + den * (D + a)) := by
    have e1 : qu * (den * (R + b + n)) = den * (qu * (R + b + n)) := by
      simp only [Nat.mul_left_comm]
    have e2 : den * (pu * (R + D) + qu * (D + a)) = den * pu * (R + D) + den * (qu * (D + a)) := by
      simp only [Nat.mul_add, Nat.mul_assoc]
    have e3 : qu * (num * (R + D) + den * (D + a)) = num * qu * (R + D) + den * (qu * (D + a)) := by
      simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have h4 := Nat.le_of_mul_le_mul_left h3 hq
  have h5 : (den - num) * R + num * R = den * R := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hnd]
  have h6 : n * (den - 1) + n = n * den := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hd]
  intro h
  rw [Nat.add_mul] at h
  simp only [Nat.mul_add] at h4
  have h7 : n ≤ n * den := Nat.le_mul_of_pos_right n hd
  have h8 : den * n = n * den := Nat.mul_comm _ _
  omega

/-! ## 4. Generic row theorems -/

theorem certFor_sound {rd : Rd} {f : Form} {v : E → Quad} {p q : Nat}
    (h : certFor rd f v p q = true) (s : Bool) :
    p * (ep s (Rq rd f v) + ep s (Dp rd f v)) + q * (ep s (Dp rd f v) + f.a) ≤
      q * (ep s (Rq rd f v) + f.b) := by
  unfold certFor at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases s
  · exact h.1
  · exact h.2

/-- **Safe up to p/q, any form and data with a certificate.** Every realization (one shared
corner, every arc within κ of its nominal) satisfies the form, for every κ ≤ p/q. -/
theorem form_safe {rd : Rd} {f : Form} {v : E → Quad} {p q : Nat} (hq : 0 < q)
    (hc : certFor rd f v p q = true) (k : Kappa) (H_KAPPA : k.num * q ≤ k.den * p) :
    AllOK (model k rd f v) f.P f.Q f.a f.b := by
  apply allOK_of_gen
  rw [path_P, path_Q, genOK_iff_ep]
  intro s
  exact safe_arith hq k.num_le H_KAPPA (certFor_sound hc s)

/-- **Safe up to κ\*.** The row's form holds on every realization for every κ ≤ κ\* = p/q. -/
theorem row_safe (r : Row) (hr : r.ok = true) (hneg : r.neg = false) (k : Kappa)
    (H_KAPPA : k.num * r.q ≤ k.den * r.p) :
    AllOK (model k r.rd r.f r.v) r.f.P r.f.Q r.f.a r.f.b := by
  unfold Row.ok at hr
  simp only [hneg, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨hq, _⟩, _⟩, _⟩, _, hc⟩, _⟩, _⟩ := hr
  exact form_safe hq hc k H_KAPPA

/-- **Unsafe from κu.** For every κ ≥ κu = pu/qu, the form fails on some realization (at the
binding endpoint corner; ConstraintsKappa's `worst` realization witnesses it). -/
theorem row_unsafe (r : Row) (hr : r.ok = true) (k : Kappa)
    (H_KAPPA : k.den * r.pu ≤ k.num * r.qu) :
    ¬ AllOK (model k r.rd r.f r.v) r.f.P r.f.Q r.f.a r.f.b := by
  unfold Row.ok at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨_, hqu⟩, _⟩, hn⟩, _⟩, hcu⟩, hdj⟩ := hr
  intro h
  have hrel := (sandwich (model k r.rd r.f r.v) (disj_of r.f hdj)).2 h r.s
  rw [path_P, path_Q] at hrel
  unfold Row.certUnsafe at hcu
  simp only [decide_eq_true_eq] at hcu
  exact unsafe_arith hqu hn k.den_pos k.num_le H_KAPPA hcu hrel

/-- The violating realization, explicitly existential. -/
theorem row_unsafe_ex (r : Row) (hr : r.ok = true) (k : Kappa)
    (H_KAPPA : k.den * r.pu ≤ k.num * r.qu) :
    ∃ d : E → Nat, (model k r.rd r.f r.v).Realizes d ∧
      pathDelay d r.f.Q + r.f.b < pathDelay d r.f.P + r.f.a :=
  Classical.byContradiction fun hne =>
    row_unsafe r hr k H_KAPPA fun d hd => Nat.le_of_not_lt fun hlt => hne ⟨d, hd, hlt⟩

/-- Non-vacuity of `row_safe` AT κ\*: κ = p/q itself is a scatter bound meeting
`H_KAPPA`, and its model is realised (A's `realizes_fast`). -/
theorem row_safe_nonvacuous (r : Row) (hr : r.ok = true) (hneg : r.neg = false) :
    ∃ k : Kappa, k.num = r.p ∧ k.den = r.q ∧ k.num * r.q ≤ k.den * r.p ∧
      (model k r.rd r.f r.v).Realizes (fun e => ((model k r.rd r.f r.v).arc e).F) := by
  unfold Row.ok at hr
  simp only [hneg, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨hq, _⟩, _⟩, _⟩, hpq, _⟩, _⟩, _⟩ := hr
  let k : Kappa := ⟨r.p, r.q, hq, hpq⟩
  exact ⟨k, rfl, rfl, Nat.le_of_eq (Nat.mul_comm _ _), ⟨_, realizes_fast _⟩⟩

/-- Non-vacuity of `row_unsafe`: κ = pu/qu meets its `H_KAPPA`. -/
theorem row_unsafe_nonvacuous (r : Row) (hr : r.ok = true) :
    ∃ k : Kappa, k.num = r.pu ∧ k.den = r.qu ∧ k.den * r.pu ≤ k.num * r.qu := by
  unfold Row.ok at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨_, hqu⟩, hpu⟩, _⟩, _⟩, _⟩, _⟩ := hr
  exact ⟨⟨r.pu, r.qu, hqu, hpu⟩, rfl, rfl, Nat.le_of_eq (Nat.mul_comm _ _)⟩

/-- Fractions: `κ ≤ m₁/m₂ ≤ p/q` gives `κ ≤ p/q`. -/
theorem frac_trans {kn kd m1 m2 p q : Nat} (hm : 0 < m2) (h1 : kn * m2 ≤ kd * m1)
    (h2 : m1 * q ≤ p * m2) : kn * q ≤ kd * p := by
  have a := Nat.mul_le_mul_right q h1
  have b := Nat.mul_le_mul_left kd h2
  have c : m2 * (kn * q) ≤ m2 * (kd * p) := by
    have e1 : m2 * (kn * q) = kn * m2 * q := by
      rw [Nat.mul_comm m2, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm m2]
    have e2 : kd * m1 * q = kd * (m1 * q) := Nat.mul_assoc _ _ _
    have e3 : kd * (p * m2) = m2 * (kd * p) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (kd * p)]
    omega
  exact Nat.le_of_mul_le_mul_left c hm

/-! ## 5. The forms (netted margins of the source files) -/

def F_fork1 : Form := ⟨[.d12, .e1, .p1], [.dS2, .es, .ps, .cq, .qgw, .pqg, .gw1, .pg1, .aq, .ag1q], 0, 0, false⟩
def F_fork2 : Form := ⟨[.d12, .e2, .p2], [.dS1, .es, .ps, .cq, .qgw, .pqg, .gw2, .pg2, .aq, .ag2], 0, 0, false⟩
def F_mP : Form := ⟨[.fa1, .ac1], [.ac, .dS1, .dS2, .es, .ps, .cq, .qs, .aq, .aRq, .srv], 0, 0, false⟩
def F_mG : Form := ⟨[.rg1, .gw1, .pg1, .fa1, .ag1r, .ac1], [.ac, .ac, .dS1, .dS1, .dS2, .d12, .es, .e1, .ps, .p1, .cq, .qs, .rs1, .aq, .aRq, .aR1, .srv, .srv], 0, 0, false⟩
def F_mA : Form := ⟨[.e1, .p1, .ac1], [.ac, .dS2, .dS2, .es, .e2, .ps, .p2, .cq, .qs, .aq, .aRq, .ac2, .srv], 0, 0, false⟩
def F_mGG : Form := ⟨[.rg1, .gw1, .pg1, .ag1r, .ac1], [.ac, .ac, .dS1, .dS2, .dS2, .d12, .es, .e2, .ps, .p2, .cq, .qs, .rs1, .aq, .aRq, .aR1, .ac2, .srv, .srv], 0, 0, false⟩
def F_nP : Form := ⟨[.fa2, .ac2], [.ac, .dS1, .dS2, .es, .ps, .cq, .qs, .aq, .aRq, .srv], 0, 0, false⟩
def F_nG : Form := ⟨[.rg2, .gw2, .pg2, .fa2, .ac2, .ag2r], [.ac, .ac, .dS1, .dS2, .dS2, .d12, .es, .e2, .ps, .p2, .cq, .qs, .rs2, .aq, .aRq, .aR2, .srv, .srv], 0, 0, false⟩
def F_nA : Form := ⟨[.e2, .p2, .ac2], [.ac, .dS1, .dS1, .es, .e1, .ps, .p1, .cq, .qs, .aq, .aRq, .ac1, .srv], 0, 0, false⟩
def F_nGG : Form := ⟨[.rg2, .gw2, .pg2, .ac2, .ag2r], [.ac, .ac, .dS1, .dS1, .dS2, .d12, .es, .e1, .ps, .p1, .cq, .qs, .rs2, .aq, .aRq, .aR2, .ac1, .srv, .srv], 0, 0, false⟩
def F_rt1 : Form := ⟨[.rg1, .ag1r], [.qgw, .pqg, .rs1, .aR1, .ag2], 0, 0, true⟩
def F_rt1b : Form := ⟨[.rg2, .ag2r], [.qgw, .pqg, .rs2, .aR2, .ag1q], 0, 0, true⟩
def F_rt1s : Form := ⟨[.rg1, .ag1r], [.ac, .dS1, .dS2, .es, .ps, .cq, .qgw, .pqg, .rs1, .aq, .aR1, .ag2, .srv], 0, 0, false⟩
def F_rt1bs : Form := ⟨[.rg2, .ag2r], [.ac, .dS1, .dS2, .es, .ps, .cq, .qgw, .pqg, .rs2, .aq, .aR2, .ag1q, .srv], 0, 0, false⟩
def F_h12 : Form := ⟨[.rg1, .ag1r], [.cq, .qgw, .pqg, .rs1, .aq, .ag2], 0, 0, false⟩
def F_h21 : Form := ⟨[.rg2, .ag2r], [.cq, .qgw, .pqg, .rs2, .aq, .ag1q], 0, 0, false⟩
def F_o1x : Form := ⟨[.rg2, .ag2r], [.cq, .qgw, .pqg, .rs2, .aq, .ag2], 0, 1, false⟩
def F_o2x : Form := ⟨[.rg1, .ag1r], [.cq, .qgw, .pqg, .rs1, .aq, .ag1q], 0, 1, false⟩

/-! ## 6. Data (generated; UNTRUSTED extraction of probe Bar) -/

/-- g2_merge10_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge10_uarb1 : E → Quad
  | .ac => (133514, 151514, 228514, 268514)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (96418, 113418, 252418, 300418)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (155182, 184182, 349182, 419182)
  | .ps => (88000, 144000, 209000, 377000)
  | .p1 => (33000, 42000, 92000, 114000)
  | .p2 => (109000, 136000, 281000, 349000)
  | .cq => (22946, 22946, 22946, 22946)
  | .qs => (69000, 99000, 186000, 275000)
  | .qgw => (95310, 112310, 251310, 299310)
  | .pqg => (172000, 214000, 416000, 516000)
  | .rs1 => (246197, 318197, 558197, 767197)
  | .rg1 => (388353, 467353, 859353, 1045353)
  | .rs2 => (241421, 339421, 557421, 840421)
  | .rg2 => (145000, 180000, 392000, 482000)
  | .gw1 => (174841, 211841, 411841, 524841)
  | .pg1 => (87000, 108000, 227000, 281000)
  | .gw2 => (120071, 139071, 260071, 307071)
  | .pg2 => (34000, 43000, 93000, 116000)
  | .fa1 => (294090, 365090, 711090, 908090)
  | .fa2 => (325255, 394255, 742255, 907255)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (46000, 61000, 120000, 153000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (44000, 56000, 120000, 154000)
  | .ag1r => (43000, 55000, 121000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2311000, 2782000, 5077000, 6198000)

/-- g2_merge11_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge11_uarb1 : E → Quad
  | .ac => (272199, 318199, 529199, 660199)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (400492, 450492, 694492, 805492)
  | .es => (878845, 968845, 1446845, 1653845)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (239608, 283608, 518608, 621608)
  | .ps => (91000, 113000, 244000, 303000)
  | .p1 => (40000, 50000, 107000, 133000)
  | .p2 => (33000, 42000, 92000, 114000)
  | .cq => (27008, 27008, 27008, 27008)
  | .qs => (320750, 386750, 768750, 933750)
  | .qgw => (401251, 453251, 778251, 906251)
  | .pqg => (38000, 48000, 102000, 126000)
  | .rs1 => (734035, 859035, 1514035, 1806035)
  | .rg1 => (271566, 329566, 696566, 847566)
  | .rs2 => (503888, 580888, 1055888, 1246888)
  | .rg2 => (276673, 338673, 669673, 817673)
  | .gw1 => (323903, 388903, 701903, 855903)
  | .pg1 => (89000, 111000, 242000, 300000)
  | .gw2 => (125880, 144880, 265880, 312880)
  | .pg2 => (87000, 108000, 227000, 281000)
  | .fa1 => (312281, 387281, 728281, 899281)
  | .fa2 => (322270, 393270, 739270, 936270)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (43000, 55000, 120000, 153000)
  | .aR1 => (44000, 58000, 121000, 156000)
  | .aR2 => (48000, 61000, 93000, 119000)
  | .ag1q => (48000, 61000, 93000, 119000)
  | .ag1r => (43000, 55000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (4015000, 4636000, 7820000, 9276000)

/-- g2_merge12_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge12_uarb1 : E → Quad
  | .ac => (218342, 234342, 364342, 408342)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (63928, 73928, 126928, 149928)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (41661, 50661, 117661, 141661)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (109000, 136000, 281000, 349000)
  | .p1 => (173000, 215000, 417000, 517000)
  | .p2 => (174000, 216000, 421000, 522000)
  | .cq => (73767, 82767, 136767, 159767)
  | .qs => (209000, 260000, 531000, 656000)
  | .qgw => (52643, 61643, 128643, 152643)
  | .pqg => (34000, 43000, 93000, 116000)
  | .rs1 => (178794, 218794, 460794, 561794)
  | .rg1 => (211661, 262661, 525661, 647661)
  | .rs2 => (298615, 365615, 758615, 924615)
  | .rg2 => (321988, 392988, 767988, 938988)
  | .gw1 => (140409, 166409, 317409, 381409)
  | .pg1 => (33000, 42000, 92000, 114000)
  | .gw2 => (116012, 134012, 255012, 302012)
  | .pg2 => (109000, 136000, 279000, 346000)
  | .fa1 => (155845, 185845, 371845, 449845)
  | .fa2 => (107031, 125031, 241031, 287031)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 56000, 120000, 154000)
  | .aR1 => (44000, 57000, 120000, 153000)
  | .aR2 => (43000, 55000, 121000, 154000)
  | .ag1q => (48000, 63000, 94000, 120000)
  | .ag1r => (43000, 55000, 121000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (682000, 815000, 1521000, 1853000)

/-- g2_merge12_uarb2: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge12_uarb2 : E → Quad
  | .ac => (102717, 120717, 199717, 272717)
  | .dS1 => (153095, 176095, 291095, 343095)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (98388, 117388, 272388, 327388)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (174000, 216000, 413000, 512000)
  | .p1 => (171000, 213000, 417000, 518000)
  | .p2 => (88000, 109000, 229000, 284000)
  | .cq => (22579, 22579, 22579, 22579)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (176000, 219000, 420000, 521000)
  | .rs1 => (218000, 272000, 542000, 669000)
  | .rg1 => (78000, 97000, 221000, 271000)
  | .rs2 => (204964, 249964, 529964, 648964)
  | .rg2 => (264964, 325964, 638964, 783964)
  | .gw1 => (120141, 150141, 295141, 374141)
  | .pg1 => (109000, 136000, 281000, 349000)
  | .gw2 => (262280, 298280, 566280, 663280)
  | .pg2 => (171000, 213000, 410000, 509000)
  | .fa1 => (146734, 176734, 364734, 442734)
  | .fa2 => (103580, 121580, 237580, 283580)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (44000, 58000, 121000, 156000)
  | .aR2 => (43000, 55000, 120000, 153000)
  | .ag1q => (44000, 58000, 121000, 156000)
  | .ag1r => (48000, 61000, 93000, 119000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1618000, 1870000, 3146000, 3740000)

/-- g2_merge2_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge2_uarb1 : E → Quad
  | .ac => (644781, 726781, 1117781, 1329781)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (67282, 77282, 126282, 149282)
  | .es => (90964, 109964, 230964, 277964)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (180000, 225000, 428000, 531000)
  | .p1 => (40000, 50000, 107000, 133000)
  | .p2 => (88000, 144000, 209000, 377000)
  | .cq => (23627, 23627, 23627, 23627)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (90964, 109964, 230964, 277964)
  | .pqg => (38000, 48000, 102000, 126000)
  | .rs1 => (189388, 230388, 516388, 630388)
  | .rg1 => (270964, 334964, 658964, 808964)
  | .rs2 => (307283, 370283, 729283, 921283)
  | .rg2 => (182687, 218687, 444687, 540687)
  | .gw1 => (118141, 148141, 292141, 368141)
  | .pg1 => (89000, 111000, 242000, 300000)
  | .gw2 => (121230, 140230, 261230, 308230)
  | .pg2 => (141000, 219000, 293000, 520000)
  | .fa1 => (312281, 387281, 728281, 899281)
  | .fa2 => (101802, 131802, 218802, 307802)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (46000, 61000, 120000, 153000)
  | .aR2 => (43000, 55000, 120000, 153000)
  | .ag1q => (48000, 61000, 93000, 119000)
  | .ag1r => (44000, 58000, 121000, 156000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2171000, 2584000, 4782000, 5773000)

/-- g2_merge3_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge3_uarb1 : E → Quad
  | .ac => (160380, 188380, 324380, 418380)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (110000, 137000, 283000, 351000)
  | .p1 => (88000, 109000, 229000, 284000)
  | .p2 => (172000, 214000, 408000, 506000)
  | .cq => (23253, 23253, 23253, 23253)
  | .qs => (271388, 332388, 689388, 844388)
  | .qgw => (93964, 112964, 238964, 286964)
  | .pqg => (38000, 48000, 102000, 126000)
  | .rs1 => (209000, 260000, 523000, 645000)
  | .rg1 => (129000, 160000, 358000, 441000)
  | .rs2 => (71000, 89000, 206000, 252000)
  | .rg2 => (218000, 272000, 542000, 669000)
  | .gw1 => (118141, 148141, 292141, 368141)
  | .pg1 => (171000, 213000, 410000, 509000)
  | .gw2 => (71868, 80868, 147868, 171868)
  | .pg2 => (176000, 219000, 420000, 521000)
  | .fa1 => (95910, 113910, 229910, 275910)
  | .fa2 => (330554, 399554, 750554, 914554)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 56000, 120000, 154000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (48000, 63000, 94000, 120000)
  | .ag1q => (48000, 61000, 93000, 119000)
  | .ag1r => (46000, 61000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1521000, 1818000, 3384000, 4128000)

/-- g2_merge4_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge4_uarb1 : E → Quad
  | .ac => (187724, 219724, 366724, 438724)
  | .dS1 => (209482, 228482, 342482, 387482)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (50813, 59813, 126813, 150813)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (331712, 372712, 619712, 718712)
  | .ps => (107000, 133000, 278000, 344000)
  | .p1 => (173000, 215000, 417000, 517000)
  | .p2 => (34000, 43000, 93000, 116000)
  | .cq => (21407, 21407, 21407, 21407)
  | .qs => (85643, 103643, 219643, 264643)
  | .qgw => (97843, 114843, 241843, 286843)
  | .pqg => (174000, 216000, 413000, 512000)
  | .rs1 => (250964, 309964, 633964, 776964)
  | .rg1 => (190141, 232141, 485141, 593141)
  | .rs2 => (194123, 235123, 478123, 581123)
  | .rg2 => (119964, 146964, 327964, 396964)
  | .gw1 => (179603, 217603, 418603, 515603)
  | .pg1 => (33000, 42000, 92000, 114000)
  | .gw2 => (216658, 248658, 445658, 523658)
  | .pg2 => (170000, 212000, 408000, 506000)
  | .fa1 => (150713, 180713, 366713, 444713)
  | .fa2 => (324987, 393987, 741987, 906987)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 57000, 120000, 153000)
  | .ag1q => (44000, 57000, 118000, 157000)
  | .ag1r => (46000, 61000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2170000, 2621000, 4627000, 5819000)

/-- g2_merge6_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge6_uarb1 : E → Quad
  | .ac => (0, 0, 0, 0)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (168850, 199850, 331850, 429850)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (49210, 58210, 125210, 149210)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (86000, 107000, 229000, 284000)
  | .p1 => (88000, 109000, 229000, 284000)
  | .p2 => (114000, 141000, 298000, 370000)
  | .cq => (21407, 21407, 21407, 21407)
  | .qs => (71000, 89000, 205000, 250000)
  | .qgw => (90964, 109964, 230964, 277964)
  | .pqg => (141000, 219000, 293000, 520000)
  | .rs1 => (210000, 261000, 530000, 654000)
  | .rg1 => (126000, 191000, 323000, 515000)
  | .rs2 => (145000, 180000, 392000, 482000)
  | .rg2 => (183000, 273000, 419000, 678000)
  | .gw1 => (233742, 276742, 551742, 662742)
  | .pg1 => (109000, 136000, 279000, 346000)
  | .gw2 => (70802, 79802, 146802, 170802)
  | .pg2 => (175000, 218000, 420000, 521000)
  | .fa1 => (95101, 113101, 229101, 275101)
  | .fa2 => (172308, 203308, 400308, 482308)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (44000, 56000, 120000, 154000)
  | .aR2 => (42000, 53000, 120000, 153000)
  | .ag1q => (44000, 57000, 118000, 157000)
  | .ag1r => (43000, 55000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1824000, 2206000, 4157000, 5119000)

/-- g2_merge9_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g2_merge9_uarb1 : E → Quad
  | .ac => (0, 0, 0, 0)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (104488, 122488, 199488, 240488)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (59720, 68720, 135720, 159720)
  | .e2 => (98150, 115150, 239150, 284150)
  | .ps => (86000, 107000, 228000, 282000)
  | .p1 => (33000, 42000, 92000, 114000)
  | .p2 => (172000, 214000, 416000, 516000)
  | .cq => (21466, 21466, 21466, 21466)
  | .qs => (207388, 253388, 553388, 676388)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (86000, 107000, 229000, 284000)
  | .rs1 => (208000, 259000, 522000, 644000)
  | .rg1 => (208000, 259000, 523000, 645000)
  | .rs2 => (209000, 260000, 531000, 656000)
  | .rg2 => (210000, 261000, 530000, 654000)
  | .gw1 => (114292, 141292, 291292, 381292)
  | .pg1 => (87000, 108000, 227000, 281000)
  | .gw2 => (120565, 137565, 263565, 308565)
  | .pg2 => (170000, 212000, 409000, 507000)
  | .fa1 => (312319, 383319, 729319, 926319)
  | .fa2 => (92407, 110407, 226407, 271407)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (42000, 53000, 120000, 153000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 56000, 120000, 154000)
  | .ag1q => (44000, 57000, 120000, 153000)
  | .ag1r => (43000, 55000, 121000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1647000, 1954000, 3529000, 4254000)

/-- g3_merge10_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge10_uarb1 : E → Quad
  | .ac => (197437, 229437, 374437, 446437)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (104975, 124975, 246975, 295975)
  | .e1 => (141139, 166139, 363139, 432139)
  | .e2 => (82964, 99964, 223964, 268964)
  | .ps => (174000, 216000, 413000, 512000)
  | .p1 => (88000, 109000, 229000, 284000)
  | .p2 => (172000, 214000, 416000, 516000)
  | .cq => (23627, 23627, 23627, 23627)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (103230, 120230, 246230, 291230)
  | .pqg => (172000, 214000, 416000, 516000)
  | .rs1 => (210421, 254421, 552421, 672421)
  | .rg1 => (134982, 164982, 353982, 432982)
  | .rs2 => (218000, 272000, 542000, 669000)
  | .rg2 => (338576, 407576, 781576, 947576)
  | .gw1 => (114292, 141292, 291292, 381292)
  | .pg1 => (171000, 213000, 410000, 509000)
  | .gw2 => (242053, 279053, 509053, 600053)
  | .pg2 => (86000, 107000, 229000, 284000)
  | .fa1 => (92720, 110720, 226720, 272720)
  | .fa2 => (101687, 119687, 235687, 280687)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (43000, 55000, 120000, 153000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (44000, 56000, 120000, 154000)
  | .ag1r => (44000, 57000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1775000, 2112000, 3908000, 4724000)

/-- g3_merge11_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge11_uarb1 : E → Quad
  | .ac => (0, 0, 0, 0)
  | .dS1 => (33817, 33817, 33817, 33817)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (153186, 182186, 390186, 468186)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (129343, 156343, 301343, 366343)
  | .ps => (171000, 213000, 410000, 509000)
  | .p1 => (175000, 218000, 420000, 521000)
  | .p2 => (170000, 212000, 408000, 506000)
  | .cq => (21720, 21720, 21720, 21720)
  | .qs => (71000, 89000, 205000, 251000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (33000, 42000, 92000, 114000)
  | .rs1 => (212000, 263000, 535000, 660000)
  | .rg1 => (211000, 262000, 531000, 655000)
  | .rs2 => (147000, 183000, 393000, 484000)
  | .rg2 => (148000, 184000, 397000, 489000)
  | .gw1 => (117090, 145090, 293090, 384090)
  | .pg1 => (114000, 141000, 298000, 370000)
  | .gw2 => (132851, 151851, 306851, 361851)
  | .pg2 => (34000, 43000, 93000, 116000)
  | .fa1 => (149720, 180720, 377720, 459720)
  | .fa2 => (310837, 379837, 727837, 892837)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (44000, 56000, 120000, 154000)
  | .aR2 => (42000, 53000, 120000, 153000)
  | .ag1q => (48000, 63000, 94000, 120000)
  | .ag1r => (44000, 56000, 120000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (4476000, 5126000, 8424000, 10002000)

/-- g3_merge12_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge12_uarb1 : E → Quad
  | .ac => (36750, 36750, 36750, 36750)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (158111, 180111, 309111, 361111)
  | .d12 => (0, 0, 0, 0)
  | .es => (90964, 108964, 229964, 276964)
  | .e1 => (97141, 116141, 232141, 279141)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (110000, 137000, 283000, 351000)
  | .p1 => (86000, 107000, 228000, 282000)
  | .p2 => (86000, 107000, 229000, 284000)
  | .cq => (82778, 92778, 180778, 211778)
  | .qs => (211000, 262000, 531000, 655000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (34000, 43000, 93000, 116000)
  | .rs1 => (263964, 324964, 640964, 785964)
  | .rg1 => (199964, 245964, 511964, 626964)
  | .rs2 => (227360, 275360, 621360, 754360)
  | .rg2 => (313186, 382186, 801186, 978186)
  | .gw1 => (333441, 391441, 772441, 922441)
  | .pg1 => (109000, 136000, 281000, 349000)
  | .gw2 => (123037, 142037, 297037, 352037)
  | .pg2 => (107000, 133000, 278000, 344000)
  | .fa1 => (312175, 381175, 729175, 894175)
  | .fa2 => (105700, 123700, 239700, 284700)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 56000, 120000, 154000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 57000, 120000, 153000)
  | .ag1q => (48000, 63000, 94000, 120000)
  | .ag1r => (42000, 53000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (871000, 1054000, 2067000, 2570000)

/-- g3_merge12_uarb2: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge12_uarb2 : E → Quad
  | .ac => (47522, 47522, 47522, 47522)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (149935, 167935, 288935, 335935)
  | .e2 => (309539, 341539, 526539, 604539)
  | .ps => (86000, 107000, 229000, 284000)
  | .p1 => (109000, 136000, 281000, 349000)
  | .p2 => (173000, 215000, 417000, 517000)
  | .cq => (21407, 21407, 21407, 21407)
  | .qs => (71000, 89000, 205000, 250000)
  | .qgw => (90964, 109964, 230964, 277964)
  | .pqg => (33000, 42000, 91000, 112000)
  | .rs1 => (327832, 396832, 769832, 935832)
  | .rg1 => (203421, 246421, 530421, 644421)
  | .rs2 => (210000, 261000, 530000, 654000)
  | .rg2 => (262964, 323964, 646964, 793964)
  | .gw1 => (265202, 312202, 600202, 744202)
  | .pg1 => (170000, 212000, 408000, 506000)
  | .gw2 => (441015, 494015, 791015, 917015)
  | .pg2 => (110000, 137000, 283000, 351000)
  | .fa1 => (160750, 190750, 378750, 456750)
  | .fa2 => (136210, 166210, 352210, 430210)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 56000, 120000, 154000)
  | .ag1q => (48000, 63000, 94000, 120000)
  | .ag1r => (42000, 53000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1403000, 1629000, 2797000, 3356000)

/-- g3_merge2_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge2_uarb1 : E → Quad
  | .ac => (470778, 544778, 894778, 1059778)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (149574, 171574, 309574, 363574)
  | .d12 => (0, 0, 0, 0)
  | .es => (96625, 115625, 235625, 282625)
  | .e1 => (205321, 241321, 485321, 578321)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (170000, 212000, 408000, 506000)
  | .p1 => (174000, 216000, 421000, 522000)
  | .p2 => (174000, 216000, 421000, 522000)
  | .cq => (21667, 21667, 21667, 21667)
  | .qs => (125830, 155830, 343830, 421830)
  | .qgw => (48982, 57982, 124982, 148982)
  | .pqg => (86000, 107000, 229000, 284000)
  | .rs1 => (147000, 183000, 395000, 487000)
  | .rg1 => (157813, 192813, 404813, 494813)
  | .rs2 => (86643, 104643, 221643, 268643)
  | .rg2 => (85643, 103643, 219643, 264643)
  | .gw1 => (257811, 309811, 581811, 727811)
  | .pg1 => (88000, 109000, 229000, 284000)
  | .gw2 => (115321, 134321, 254321, 301321)
  | .pg2 => (171000, 213000, 410000, 509000)
  | .fa1 => (108724, 126724, 242724, 288724)
  | .fa2 => (103580, 121580, 237580, 283580)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 57000, 120000, 153000)
  | .aR1 => (42000, 53000, 120000, 153000)
  | .aR2 => (48000, 63000, 94000, 120000)
  | .ag1q => (44000, 57000, 120000, 153000)
  | .ag1r => (42000, 53000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2275000, 2749000, 4901000, 6066000)

/-- g3_merge3_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge3_uarb1 : E → Quad
  | .ac => (372313, 428313, 711313, 869313)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (50813, 59813, 126813, 150813)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (107000, 133000, 278000, 344000)
  | .p1 => (109000, 136000, 281000, 349000)
  | .p2 => (174000, 216000, 421000, 522000)
  | .cq => (21407, 21407, 21407, 21407)
  | .qs => (85643, 103643, 219643, 264643)
  | .qgw => (90964, 109964, 230964, 277964)
  | .pqg => (33000, 42000, 92000, 114000)
  | .rs1 => (208000, 259000, 523000, 645000)
  | .rg1 => (211000, 262000, 531000, 655000)
  | .rs2 => (219152, 270152, 539152, 663152)
  | .rg2 => (148000, 184000, 397000, 489000)
  | .gw1 => (117090, 145090, 293090, 384090)
  | .pg1 => (34000, 43000, 93000, 116000)
  | .gw2 => (72670, 81670, 148670, 172670)
  | .pg2 => (171000, 213000, 410000, 509000)
  | .fa1 => (148850, 178850, 366850, 444850)
  | .fa2 => (130443, 148443, 264443, 310443)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 56000, 120000, 154000)
  | .ag1q => (48000, 63000, 94000, 120000)
  | .ag1r => (44000, 56000, 120000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1839000, 2208000, 4061000, 5005000)

/-- g3_merge4_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge4_uarb1 : E → Quad
  | .ac => (118562, 132562, 201562, 232562)
  | .dS1 => (277989, 306989, 491989, 562989)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (250416, 293416, 570416, 679416)
  | .ps => (180000, 225000, 428000, 531000)
  | .p1 => (175000, 218000, 420000, 521000)
  | .p2 => (172000, 214000, 416000, 516000)
  | .cq => (23627, 23627, 23627, 23627)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (81964, 98964, 225964, 270964)
  | .pqg => (170000, 212000, 409000, 507000)
  | .rs1 => (330459, 399459, 786459, 956459)
  | .rg1 => (215963, 256963, 494963, 593963)
  | .rs2 => (272564, 314564, 566564, 673564)
  | .rg2 => (297882, 340882, 612882, 723882)
  | .gw1 => (159583, 194583, 404583, 515583)
  | .pg1 => (172000, 214000, 406000, 504000)
  | .gw2 => (370124, 413124, 738124, 854124)
  | .pg2 => (86000, 107000, 229000, 284000)
  | .fa1 => (138860, 169860, 366860, 448860)
  | .fa2 => (102636, 120636, 236636, 281636)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (44000, 57000, 118000, 157000)
  | .aR2 => (46000, 61000, 120000, 153000)
  | .ag1q => (43000, 55000, 121000, 154000)
  | .ag1r => (48000, 63000, 94000, 120000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2303000, 2733000, 4970000, 6031000)

/-- g3_merge6_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge6_uarb1 : E → Quad
  | .ac => (0, 0, 0, 0)
  | .dS1 => (166996, 194996, 341996, 437996)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (109057, 126057, 266057, 314057)
  | .ps => (114000, 141000, 300000, 372000)
  | .p1 => (109000, 136000, 281000, 349000)
  | .p2 => (171000, 213000, 410000, 509000)
  | .cq => (82856, 92856, 180856, 211856)
  | .qs => (212000, 263000, 527000, 650000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (171000, 213000, 409000, 507000)
  | .rs1 => (119964, 146964, 327964, 396964)
  | .rg1 => (115141, 141141, 331141, 401141)
  | .rs2 => (218000, 272000, 542000, 669000)
  | .rg2 => (148000, 184000, 397000, 489000)
  | .gw1 => (117090, 145090, 293090, 384090)
  | .pg1 => (34000, 43000, 93000, 116000)
  | .gw2 => (61524, 70524, 137524, 161524)
  | .pg2 => (88000, 109000, 229000, 284000)
  | .fa1 => (146734, 176734, 364734, 442734)
  | .fa2 => (81860, 99860, 215860, 261860)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 57000, 118000, 157000)
  | .aR1 => (48000, 61000, 93000, 119000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (43000, 55000, 121000, 154000)
  | .ag1r => (48000, 63000, 94000, 120000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2114000, 2484000, 4393000, 5333000)

/-- g3_merge9_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g3_merge9_uarb1 : E → Quad
  | .ac => (368295, 428295, 704295, 832295)
  | .dS1 => (135284, 158284, 286284, 339284)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (47152, 56152, 123152, 147152)
  | .e1 => (45321, 54321, 121321, 145321)
  | .e2 => (135953, 161953, 355953, 426953)
  | .ps => (172000, 214000, 416000, 516000)
  | .p1 => (171000, 213000, 409000, 507000)
  | .p2 => (34000, 43000, 93000, 116000)
  | .cq => (22357, 22357, 22357, 22357)
  | .qs => (270999, 325999, 679999, 823999)
  | .qgw => (103777, 122777, 243777, 290777)
  | .pqg => (107000, 133000, 278000, 344000)
  | .rs1 => (177946, 215946, 464946, 564946)
  | .rg1 => (231742, 279742, 582742, 705742)
  | .rs2 => (85643, 103643, 219643, 264643)
  | .rg2 => (219152, 270152, 539152, 663152)
  | .gw1 => (177903, 214903, 416903, 529903)
  | .pg1 => (87000, 108000, 227000, 281000)
  | .gw2 => (180118, 209118, 381118, 451118)
  | .pg2 => (109000, 136000, 281000, 349000)
  | .fa1 => (313230, 384230, 730230, 927230)
  | .fa2 => (325255, 394255, 742255, 907255)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (42000, 53000, 120000, 153000)
  | .aR1 => (44000, 57000, 120000, 153000)
  | .aR2 => (48000, 63000, 94000, 120000)
  | .ag1q => (42000, 53000, 120000, 153000)
  | .ag1r => (44000, 57000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (3115000, 3662000, 6388000, 7669000)

/-- g4_merge10_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge10_uarb1 : E → Quad
  | .ac => (417840, 487840, 817840, 974840)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (98388, 117388, 272388, 327388)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (174000, 216000, 413000, 512000)
  | .p1 => (88000, 144000, 209000, 377000)
  | .p2 => (174000, 216000, 421000, 522000)
  | .cq => (23627, 23627, 23627, 23627)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (159027, 186027, 365027, 433027)
  | .pqg => (172000, 214000, 416000, 516000)
  | .rs1 => (181964, 222964, 474964, 580964)
  | .rg1 => (191292, 229292, 491292, 594292)
  | .rs2 => (354942, 426942, 773942, 941942)
  | .rg2 => (227038, 270038, 542038, 653038)
  | .gw1 => (175461, 210461, 419461, 530461)
  | .pg1 => (141000, 219000, 293000, 520000)
  | .gw2 => (183606, 209606, 390606, 458606)
  | .pg2 => (109000, 136000, 279000, 346000)
  | .fa1 => (91883, 121883, 208883, 297883)
  | .fa2 => (81860, 99860, 215860, 261860)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (46000, 61000, 120000, 153000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (44000, 56000, 120000, 154000)
  | .ag1r => (44000, 57000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2422000, 2905000, 5442000, 6515000)

/-- g4_merge11_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge11_uarb1 : E → Quad
  | .ac => (298553, 332553, 477553, 581553)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (139284, 163284, 285284, 339284)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (157426, 184426, 363426, 431426)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (42000, 52000, 111000, 137000)
  | .p1 => (33000, 42000, 92000, 114000)
  | .p2 => (173000, 215000, 417000, 517000)
  | .cq => (21720, 21720, 21720, 21720)
  | .qs => (128000, 159000, 356000, 438000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (91000, 113000, 244000, 303000)
  | .rs1 => (213000, 265000, 534000, 659000)
  | .rg1 => (218000, 272000, 542000, 669000)
  | .rs2 => (152000, 188000, 412000, 508000)
  | .rg2 => (152000, 188000, 414000, 510000)
  | .gw1 => (241379, 289379, 558379, 681379)
  | .pg1 => (87000, 108000, 227000, 281000)
  | .gw2 => (132146, 151146, 306146, 361146)
  | .pg2 => (171000, 213000, 409000, 507000)
  | .fa1 => (311580, 382580, 728580, 925580)
  | .fa2 => (300814, 360814, 677814, 851814)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (46000, 61000, 120000, 153000)
  | .aR1 => (44000, 58000, 121000, 156000)
  | .aR2 => (43000, 55000, 120000, 153000)
  | .ag1q => (46000, 61000, 120000, 153000)
  | .ag1r => (44000, 58000, 121000, 156000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (5230000, 5958000, 9501000, 11247000)

/-- g4_merge12_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge12_uarb1 : E → Quad
  | .ac => (46921, 46921, 46921, 46921)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (141997, 166997, 349997, 415997)
  | .e1 => (90964, 109964, 230964, 277964)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (90000, 112000, 242000, 300000)
  | .p1 => (171000, 213000, 410000, 509000)
  | .p2 => (88000, 109000, 229000, 284000)
  | .cq => (23798, 23798, 23798, 23798)
  | .qs => (265964, 326964, 649964, 797964)
  | .qgw => (97141, 116141, 232141, 279141)
  | .pqg => (170000, 212000, 408000, 506000)
  | .rs1 => (220320, 264320, 519320, 626320)
  | .rg1 => (320978, 386978, 755978, 917978)
  | .rs2 => (264964, 325964, 637964, 782964)
  | .rg2 => (319760, 390760, 765760, 936760)
  | .gw1 => (257653, 307653, 582653, 700653)
  | .pg1 => (88000, 109000, 229000, 284000)
  | .gw2 => (246933, 286933, 521933, 617933)
  | .pg2 => (171000, 213000, 410000, 509000)
  | .fa1 => (93728, 111728, 227728, 273728)
  | .fa2 => (93790, 111790, 227790, 273790)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 58000, 121000, 156000)
  | .aR1 => (48000, 61000, 93000, 119000)
  | .aR2 => (44000, 57000, 118000, 157000)
  | .ag1q => (43000, 55000, 121000, 154000)
  | .ag1r => (42000, 53000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (588000, 714000, 1374000, 1683000)

/-- g4_merge12_uarb2: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge12_uarb2 : E → Quad
  | .ac => (0, 0, 0, 0)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (105957, 123957, 200957, 241957)
  | .es => (59720, 68720, 135720, 159720)
  | .e1 => (80141, 97141, 236141, 284141)
  | .e2 => (160330, 187330, 362330, 430330)
  | .ps => (33000, 42000, 92000, 114000)
  | .p1 => (173000, 215000, 417000, 517000)
  | .p2 => (172000, 214000, 408000, 506000)
  | .cq => (23316, 23316, 23316, 23316)
  | .qs => (271388, 332388, 689388, 844388)
  | .qgw => (98819, 115819, 255819, 303819)
  | .pqg => (89000, 111000, 242000, 300000)
  | .rs1 => (208649, 252649, 537649, 653649)
  | .rg1 => (78000, 97000, 221000, 271000)
  | .rs2 => (244598, 292598, 610598, 736598)
  | .rg2 => (264964, 325964, 638964, 783964)
  | .gw1 => (281224, 337224, 657224, 801224)
  | .pg1 => (33000, 42000, 92000, 114000)
  | .gw2 => (197720, 226720, 396720, 466720)
  | .pg2 => (89000, 111000, 242000, 300000)
  | .fa1 => (171921, 201921, 387921, 465921)
  | .fa2 => (350264, 425264, 766264, 937264)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 56000, 120000, 154000)
  | .aR1 => (42000, 53000, 120000, 153000)
  | .aR2 => (44000, 57000, 120000, 153000)
  | .ag1q => (46000, 61000, 120000, 153000)
  | .ag1r => (48000, 61000, 93000, 119000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (995000, 1173000, 2144000, 2600000)

/-- g4_merge2_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge2_uarb1 : E → Quad
  | .ac => (235022, 273022, 454022, 540022)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (241675, 268675, 443675, 511675)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (109000, 136000, 279000, 346000)
  | .p1 => (89000, 111000, 242000, 300000)
  | .p2 => (90000, 112000, 242000, 300000)
  | .cq => (22728, 22728, 22728, 22728)
  | .qs => (83813, 101813, 217813, 263813)
  | .qgw => (241468, 269468, 452468, 521468)
  | .pqg => (87000, 108000, 227000, 281000)
  | .rs1 => (269564, 309564, 547564, 649564)
  | .rg1 => (131002, 157002, 333002, 400002)
  | .rs2 => (212000, 263000, 535000, 660000)
  | .rg2 => (415616, 485616, 862616, 1030616)
  | .gw1 => (171362, 209362, 411362, 525362)
  | .pg1 => (113000, 140000, 297000, 368000)
  | .gw2 => (126389, 145389, 271389, 319389)
  | .pg2 => (42000, 52000, 111000, 137000)
  | .fa1 => (312281, 387281, 728281, 899281)
  | .fa2 => (350025, 420025, 766025, 932025)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (44000, 57000, 120000, 153000)
  | .aR2 => (44000, 56000, 120000, 154000)
  | .ag1q => (44000, 57000, 120000, 153000)
  | .ag1r => (48000, 63000, 94000, 120000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1893000, 2235000, 4116000, 4950000)

/-- g4_merge3_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge3_uarb1 : E → Quad
  | .ac => (247005, 286005, 478005, 565005)
  | .dS1 => (68282, 78282, 127282, 150282)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (48982, 57982, 124982, 148982)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (220773, 245773, 443773, 512773)
  | .ps => (86000, 107000, 229000, 284000)
  | .p1 => (170000, 212000, 409000, 507000)
  | .p2 => (73000, 118000, 176000, 317000)
  | .cq => (21407, 21407, 21407, 21407)
  | .qs => (85643, 103643, 219643, 264643)
  | .qgw => (226213, 251213, 437213, 503213)
  | .pqg => (171000, 213000, 410000, 509000)
  | .rs1 => (157813, 192813, 404813, 494813)
  | .rg1 => (357564, 419564, 746564, 896564)
  | .rs2 => (392058, 459058, 855058, 1022058)
  | .rg2 => (178964, 218964, 459964, 561964)
  | .gw1 => (264042, 301042, 506042, 594042)
  | .pg1 => (86000, 107000, 229000, 284000)
  | .gw2 => (123726, 142726, 263726, 310726)
  | .pg2 => (88000, 144000, 209000, 377000)
  | .fa1 => (94463, 112463, 228463, 273463)
  | .fa2 => (90868, 120868, 207868, 296868)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (42000, 53000, 120000, 153000)
  | .aR2 => (43000, 55000, 121000, 154000)
  | .ag1q => (43000, 55000, 121000, 154000)
  | .ag1r => (44000, 56000, 120000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1683000, 2000000, 3732000, 4555000)

/-- g4_merge4_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge4_uarb1 : E → Quad
  | .ac => (294579, 328579, 474579, 578579)
  | .dS1 => (126574, 146574, 287574, 341574)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (224225, 249225, 437225, 503225)
  | .ps => (109000, 136000, 279000, 346000)
  | .p1 => (172000, 214000, 416000, 516000)
  | .p2 => (34000, 43000, 93000, 116000)
  | .cq => (21518, 21518, 21518, 21518)
  | .qs => (83813, 101813, 217813, 263813)
  | .qgw => (109370, 128370, 283370, 338370)
  | .pqg => (86000, 107000, 229000, 284000)
  | .rs1 => (261964, 322964, 640964, 786964)
  | .rg1 => (275116, 336116, 664116, 812116)
  | .rs2 => (186388, 226388, 501388, 611388)
  | .rg2 => (208000, 259000, 523000, 645000)
  | .gw1 => (171583, 208583, 417583, 531583)
  | .pg1 => (107000, 133000, 278000, 344000)
  | .gw2 => (216338, 236338, 358338, 407338)
  | .pg2 => (86000, 107000, 228000, 282000)
  | .fa1 => (81229, 99229, 215229, 260229)
  | .fa2 => (326675, 395675, 743675, 908675)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 57000, 120000, 153000)
  | .ag1q => (44000, 57000, 120000, 153000)
  | .ag1r => (44000, 56000, 120000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2028000, 2398000, 4427000, 5324000)

/-- g4_merge6_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge6_uarb1 : E → Quad
  | .ac => (33568, 33568, 33568, 33568)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (68112, 78112, 127112, 150112)
  | .d12 => (0, 0, 0, 0)
  | .es => (98388, 117388, 272388, 327388)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (33000, 42000, 92000, 114000)
  | .p1 => (86000, 107000, 229000, 284000)
  | .p2 => (174000, 216000, 421000, 522000)
  | .cq => (23253, 23253, 23253, 23253)
  | .qs => (208388, 254388, 555388, 678388)
  | .qgw => (147760, 176760, 356760, 427760)
  | .pqg => (110000, 137000, 283000, 351000)
  | .rs1 => (314953, 383953, 762953, 930953)
  | .rg1 => (254964, 313964, 642964, 787964)
  | .rs2 => (125000, 155000, 341000, 419000)
  | .rg2 => (183141, 223141, 458141, 559141)
  | .gw1 => (233584, 281584, 570584, 715584)
  | .pg1 => (107000, 133000, 278000, 344000)
  | .gw2 => (228735, 265735, 494735, 587735)
  | .pg2 => (88000, 109000, 229000, 284000)
  | .fa1 => (81229, 99229, 215229, 260229)
  | .fa2 => (104588, 122588, 238588, 284588)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (42000, 53000, 120000, 153000)
  | .aR1 => (44000, 56000, 120000, 154000)
  | .aR2 => (44000, 57000, 120000, 153000)
  | .ag1q => (42000, 53000, 120000, 153000)
  | .ag1r => (44000, 56000, 120000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1712000, 2040000, 3784000, 4597000)

/-- g4_merge9_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_g4_merge9_uarb1 : E → Quad
  | .ac => (168869, 192869, 313869, 367869)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (84352, 97352, 166352, 195352)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (172000, 214000, 406000, 504000)
  | .p1 => (86000, 107000, 229000, 284000)
  | .p2 => (174000, 216000, 421000, 522000)
  | .cq => (22589, 22589, 22589, 22589)
  | .qs => (191850, 229850, 470850, 566850)
  | .qgw => (98388, 117388, 272388, 327388)
  | .pqg => (114000, 141000, 300000, 372000)
  | .rs1 => (128000, 159000, 356000, 438000)
  | .rg1 => (129000, 160000, 358000, 441000)
  | .rs2 => (213000, 265000, 534000, 659000)
  | .rg2 => (218000, 272000, 542000, 669000)
  | .gw1 => (175417, 215417, 418417, 518417)
  | .pg1 => (107000, 133000, 278000, 344000)
  | .gw2 => (125880, 144880, 265880, 312880)
  | .pg2 => (88000, 109000, 229000, 284000)
  | .fa1 => (92466, 110466, 226466, 271466)
  | .fa2 => (114440, 132440, 248440, 294440)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (46000, 61000, 120000, 153000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (43000, 55000, 120000, 153000)
  | .ag1r => (46000, 61000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1196000, 1436000, 2604000, 3193000)

/-- gd_merge10_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge10_uarb1 : E → Quad
  | .ac => (156791, 176791, 284791, 331791)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (98150, 115150, 239150, 284150)
  | .ps => (141000, 219000, 293000, 520000)
  | .p1 => (113000, 140000, 297000, 368000)
  | .p2 => (109000, 136000, 279000, 346000)
  | .cq => (21868, 21868, 21868, 21868)
  | .qs => (69000, 99000, 186000, 275000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (180000, 225000, 428000, 531000)
  | .rs1 => (243388, 343388, 577388, 867388)
  | .rg1 => (129000, 160000, 358000, 441000)
  | .rs2 => (282792, 373792, 643792, 929792)
  | .rg2 => (166309, 193309, 375309, 444309)
  | .gw1 => (118141, 148141, 292141, 368141)
  | .pg1 => (89000, 111000, 242000, 300000)
  | .gw2 => (143718, 160718, 297718, 344718)
  | .pg2 => (33000, 42000, 91000, 113000)
  | .fa1 => (313674, 388674, 729674, 900674)
  | .fa2 => (376854, 443854, 846854, 1016854)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (44000, 58000, 121000, 156000)
  | .aR2 => (43000, 55000, 120000, 153000)
  | .ag1q => (44000, 58000, 121000, 156000)
  | .ag1r => (46000, 61000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1956000, 2372000, 4437000, 5427000)

/-- gd_merge11_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge11_uarb1 : E → Quad
  | .ac => (123058, 136058, 202058, 231058)
  | .dS1 => (219982, 242982, 359982, 411982)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (97141, 117141, 238141, 286141)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (227578, 255578, 437578, 507578)
  | .ps => (174000, 216000, 413000, 512000)
  | .p1 => (86000, 107000, 228000, 282000)
  | .p2 => (34000, 43000, 93000, 116000)
  | .cq => (23691, 23691, 23691, 23691)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (99141, 119141, 241141, 290141)
  | .pqg => (174000, 216000, 413000, 512000)
  | .rs1 => (270964, 333964, 657964, 807964)
  | .rg1 => (322639, 392639, 780639, 949639)
  | .rs2 => (211141, 258141, 538141, 658141)
  | .rg2 => (152000, 188000, 414000, 510000)
  | .gw1 => (175417, 215417, 418417, 518417)
  | .pg1 => (109000, 136000, 281000, 349000)
  | .gw2 => (185228, 212228, 402228, 472228)
  | .pg2 => (109000, 136000, 281000, 349000)
  | .fa1 => (312175, 381175, 729175, 894175)
  | .fa2 => (330911, 399911, 747911, 912911)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (44000, 58000, 121000, 156000)
  | .aR2 => (43000, 55000, 120000, 153000)
  | .ag1q => (44000, 57000, 118000, 157000)
  | .ag1r => (44000, 58000, 121000, 156000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1858000, 2208000, 4104000, 4956000)

/-- gd_merge12_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge12_uarb1 : E → Quad
  | .ac => (175907, 203907, 331907, 395907)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (124600, 140600, 254600, 296600)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (97141, 116141, 234141, 281141)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (180000, 225000, 428000, 531000)
  | .p1 => (90000, 112000, 242000, 300000)
  | .p2 => (109000, 136000, 279000, 346000)
  | .cq => (23627, 23627, 23627, 23627)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (90964, 109964, 230964, 277964)
  | .pqg => (172000, 214000, 416000, 516000)
  | .rs1 => (152000, 188000, 414000, 510000)
  | .rg1 => (145000, 180000, 392000, 482000)
  | .rs2 => (129000, 160000, 358000, 441000)
  | .rg2 => (208000, 259000, 523000, 645000)
  | .gw1 => (286329, 339329, 658329, 813329)
  | .pg1 => (114000, 141000, 298000, 370000)
  | .gw2 => (61463, 70463, 137463, 161463)
  | .pg2 => (174000, 216000, 421000, 522000)
  | .fa1 => (289762, 350762, 673762, 821762)
  | .fa2 => (81860, 99860, 215860, 261860)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (43000, 55000, 120000, 153000)
  | .aR2 => (46000, 61000, 120000, 153000)
  | .ag1q => (44000, 56000, 120000, 154000)
  | .ag1r => (42000, 53000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (694000, 874000, 1642000, 2125000)

/-- gd_merge12_uarb2: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge12_uarb2 : E → Quad
  | .ac => (34670, 34670, 34670, 34670)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (61928, 70928, 124928, 147928)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (86000, 107000, 229000, 284000)
  | .p1 => (88000, 109000, 229000, 284000)
  | .p2 => (173000, 215000, 417000, 517000)
  | .cq => (21407, 21407, 21407, 21407)
  | .qs => (71000, 89000, 205000, 250000)
  | .qgw => (151186, 180186, 389186, 467186)
  | .pqg => (31000, 52000, 72000, 137000)
  | .rs1 => (364194, 439194, 836194, 1015194)
  | .rg1 => (240085, 321085, 585085, 822085)
  | .rs2 => (252964, 311964, 634964, 777964)
  | .rg2 => (278953, 386953, 659953, 965953)
  | .gw1 => (234434, 280434, 549434, 664434)
  | .pg1 => (33000, 42000, 91000, 113000)
  | .gw2 => (138579, 157579, 274579, 321579)
  | .pg2 => (110000, 137000, 283000, 351000)
  | .fa1 => (305840, 368840, 709840, 864840)
  | .fa2 => (176631, 206631, 392631, 470631)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 63000, 94000, 120000)
  | .aR1 => (44000, 56000, 120000, 154000)
  | .aR2 => (43000, 55000, 121000, 154000)
  | .ag1q => (48000, 61000, 93000, 119000)
  | .ag1r => (43000, 55000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1508000, 1748000, 2998000, 3586000)

/-- gd_merge2_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge2_uarb1 : E → Quad
  | .ac => (635570, 737570, 1244570, 1476570)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (114000, 141000, 298000, 370000)
  | .p1 => (145000, 226000, 305000, 540000)
  | .p2 => (40000, 50000, 107000, 133000)
  | .cq => (21720, 21720, 21720, 21720)
  | .qs => (128000, 159000, 356000, 438000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (91000, 113000, 244000, 303000)
  | .rs1 => (213000, 265000, 534000, 659000)
  | .rg1 => (218000, 272000, 542000, 669000)
  | .rs2 => (210000, 261000, 520000, 642000)
  | .rg2 => (212000, 263000, 527000, 650000)
  | .gw1 => (118141, 148141, 292141, 368141)
  | .pg1 => (73000, 118000, 176000, 317000)
  | .gw2 => (121230, 140230, 261230, 308230)
  | .pg2 => (176000, 219000, 420000, 521000)
  | .fa1 => (79934, 109934, 196934, 285934)
  | .fa2 => (159421, 190421, 388421, 470421)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (46000, 61000, 120000, 153000)
  | .aR1 => (44000, 58000, 121000, 156000)
  | .aR2 => (44000, 57000, 118000, 157000)
  | .ag1q => (46000, 61000, 120000, 153000)
  | .ag1r => (44000, 58000, 121000, 156000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2252000, 2685000, 4904000, 5930000)

/-- gd_merge3_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge3_uarb1 : E → Quad
  | .ac => (181795, 206795, 334795, 390795)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (98388, 117388, 272388, 327388)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (91000, 113000, 244000, 303000)
  | .p1 => (141000, 219000, 293000, 520000)
  | .p2 => (172000, 214000, 416000, 516000)
  | .cq => (22370, 22370, 22370, 22370)
  | .qs => (76000, 95000, 216000, 264000)
  | .qgw => (98388, 117388, 272388, 327388)
  | .pqg => (171000, 213000, 409000, 507000)
  | .rs1 => (212000, 263000, 527000, 650000)
  | .rg1 => (282676, 346676, 684676, 837676)
  | .rs2 => (218000, 272000, 542000, 669000)
  | .rg2 => (148000, 184000, 397000, 489000)
  | .gw1 => (171362, 209362, 411362, 525362)
  | .pg1 => (88000, 144000, 209000, 377000)
  | .gw2 => (218854, 253854, 497854, 587854)
  | .pg2 => (86000, 107000, 229000, 284000)
  | .fa1 => (79934, 109934, 196934, 285934)
  | .fa2 => (318902, 381902, 731902, 918902)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (48000, 61000, 93000, 119000)
  | .aR1 => (44000, 57000, 118000, 157000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (43000, 55000, 121000, 154000)
  | .ag1r => (44000, 56000, 120000, 154000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2067000, 2477000, 4571000, 5548000)

/-- gd_merge4_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge4_uarb1 : E → Quad
  | .ac => (404350, 457350, 708350, 826350)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (71776, 81776, 169776, 200776)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (39830, 48830, 115830, 139830)
  | .e2 => (38000, 47000, 114000, 138000)
  | .ps => (110000, 137000, 283000, 351000)
  | .p1 => (86000, 107000, 228000, 282000)
  | .p2 => (171000, 213000, 410000, 509000)
  | .cq => (22212, 22212, 22212, 22212)
  | .qs => (125000, 155000, 341000, 419000)
  | .qgw => (98388, 117388, 272388, 327388)
  | .pqg => (174000, 216000, 421000, 522000)
  | .rs1 => (71000, 89000, 206000, 252000)
  | .rg1 => (126000, 156000, 343000, 422000)
  | .rs2 => (211000, 262000, 531000, 655000)
  | .rg2 => (258935, 303935, 567935, 681935)
  | .gw1 => (122751, 148751, 299751, 363751)
  | .pg1 => (170000, 212000, 408000, 506000)
  | .gw2 => (71588, 80588, 147588, 171588)
  | .pg2 => (109000, 136000, 279000, 346000)
  | .fa1 => (319591, 388591, 736591, 901591)
  | .fa2 => (128261, 146261, 262261, 308261)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 57000, 120000, 153000)
  | .aR1 => (48000, 63000, 94000, 120000)
  | .aR2 => (44000, 56000, 120000, 154000)
  | .ag1q => (44000, 56000, 120000, 154000)
  | .ag1r => (44000, 57000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2304000, 2754000, 5042000, 6219000)

/-- gd_merge6_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge6_uarb1 : E → Quad
  | .ac => (0, 0, 0, 0)
  | .dS1 => (0, 0, 0, 0)
  | .dS2 => (106072, 124072, 201072, 241072)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (173475, 198475, 382475, 448475)
  | .e2 => (159320, 190320, 385320, 461320)
  | .ps => (33000, 42000, 92000, 114000)
  | .p1 => (174000, 216000, 421000, 522000)
  | .p2 => (89000, 111000, 242000, 300000)
  | .cq => (22212, 22212, 22212, 22212)
  | .qs => (125000, 155000, 341000, 419000)
  | .qgw => (98388, 117388, 272388, 327388)
  | .pqg => (175000, 218000, 420000, 521000)
  | .rs1 => (209000, 260000, 523000, 645000)
  | .rg1 => (128000, 159000, 356000, 438000)
  | .rs2 => (211000, 262000, 531000, 655000)
  | .rg2 => (80000, 99000, 225000, 275000)
  | .gw1 => (202021, 239021, 447021, 537021)
  | .pg1 => (33000, 42000, 91000, 113000)
  | .gw2 => (189299, 219299, 415299, 491299)
  | .pg2 => (176000, 219000, 420000, 521000)
  | .fa1 => (308592, 371592, 712592, 867592)
  | .fa2 => (331839, 400839, 751839, 915839)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (44000, 57000, 120000, 153000)
  | .aR1 => (43000, 55000, 121000, 154000)
  | .aR2 => (44000, 56000, 120000, 154000)
  | .ag1q => (44000, 58000, 121000, 156000)
  | .ag1r => (46000, 61000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (1641000, 1953000, 3643000, 4451000)

/-- gd_merge9_uarb1: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) per arc, fs. -/
def v_gd_merge9_uarb1 : E → Quad
  | .ac => (1422352, 1552352, 2211352, 2503352)
  | .dS1 => (444287, 498287, 796287, 921287)
  | .dS2 => (0, 0, 0, 0)
  | .d12 => (0, 0, 0, 0)
  | .es => (38000, 47000, 114000, 138000)
  | .e1 => (38000, 47000, 114000, 138000)
  | .e2 => (176434, 208434, 404434, 481434)
  | .ps => (91000, 113000, 244000, 303000)
  | .p1 => (170000, 212000, 408000, 506000)
  | .p2 => (86000, 107000, 229000, 284000)
  | .cq => (133974, 152974, 267974, 313974)
  | .qs => (152000, 188000, 414000, 510000)
  | .qgw => (38000, 47000, 114000, 138000)
  | .pqg => (33000, 42000, 91000, 112000)
  | .rs1 => (76000, 95000, 216000, 264000)
  | .rg1 => (145000, 180000, 392000, 482000)
  | .rs2 => (218000, 272000, 542000, 669000)
  | .rg2 => (210000, 261000, 530000, 654000)
  | .gw1 => (174415, 211415, 449415, 570415)
  | .pg1 => (34000, 43000, 93000, 116000)
  | .gw2 => (243912, 280912, 522912, 616912)
  | .pg2 => (33000, 42000, 91000, 112000)
  | .fa1 => (310837, 379837, 727837, 892837)
  | .fa2 => (367865, 434865, 834865, 1003865)
  | .aq => (45000, 56000, 100000, 124000)
  | .aRq => (43000, 55000, 120000, 153000)
  | .aR1 => (48000, 61000, 93000, 119000)
  | .aR2 => (44000, 58000, 121000, 156000)
  | .ag1q => (48000, 63000, 94000, 120000)
  | .ag1r => (42000, 53000, 120000, 153000)
  | .ag2 => (45000, 56000, 100000, 124000)
  | .ac1 => (45000, 56000, 100000, 124000)
  | .ac2 => (45000, 56000, 100000, 124000)
  | .ag2r => (45000, 56000, 100000, 124000)
  | .srv => (2601000, 3065000, 5033000, 6147000)

def R_g2_merge2_uarb1_cons_rt1 : Row :=
  ⟨"g2_merge2_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge2_uarb1, false, 4097, 200579, false, 16395, 802316⟩
def R_g2_merge3_uarb1_lit_h21 : Row :=
  ⟨"g2_merge3_uarb1.lit.h21", .lit, F_h21, v_g2_merge3_uarb1, false, 138217, 1724217, true, 46075, 574739⟩
def R_g2_merge3_uarb1_cons_rt1b : Row :=
  ⟨"g2_merge3_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge3_uarb1, true, 0, 1, false, 0, 1⟩
def R_g2_merge3_uarb1_cons_h21 : Row :=
  ⟨"g2_merge3_uarb1.cons.h21", .cons, F_h21, v_g2_merge3_uarb1, true, 0, 1, true, 0, 1⟩
def R_g2_merge3_uarb1_cons_o1x : Row :=
  ⟨"g2_merge3_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge3_uarb1, true, 0, 1, false, 0, 1⟩
def R_g3_merge12_uarb1_lit_rt1b : Row :=
  ⟨"g3_merge12_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge12_uarb1, false, 16587, 374773, false, 33181, 749546⟩
def R_g3_merge12_uarb1_cons_rt1b : Row :=
  ⟨"g3_merge12_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge12_uarb1, true, 0, 1, false, 0, 1⟩
def R_gd_merge9_uarb1_cons_rt1 : Row :=
  ⟨"gd_merge9_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge9_uarb1, true, 0, 1, true, 0, 1⟩

/-- The rows of seed 2: 9 arbiters × 2 readings × 18 conditions. -/
def rows_g2 : List Row := [
  ⟨"g2_merge10_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge10_uarb1, false, 52167, 63367, true, 2347528, 2851515⟩,
  ⟨"g2_merge10_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge10_uarb1, false, 454563, 982927, false, 454576, 982927⟩,
  ⟨"g2_merge10_uarb1.lit.mP", .lit, F_mP, v_g2_merge10_uarb1, false, 554399, 726414, true, 92400, 121069⟩,
  ⟨"g2_merge10_uarb1.lit.mG", .lit, F_mG, v_g2_merge10_uarb1, false, 1365145, 2040097, true, 4095443, 6120291⟩,
  ⟨"g2_merge10_uarb1.lit.mA", .lit, F_mA, v_g2_merge10_uarb1, false, 410053, 447653, true, 2050269, 2238265⟩,
  ⟨"g2_merge10_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge10_uarb1, false, 13834577, 18092965, true, 1257691, 1644815⟩,
  ⟨"g2_merge10_uarb1.lit.nP", .lit, F_nP, v_g2_merge10_uarb1, false, 6653623, 8716133, true, 6653635, 8716133⟩,
  ⟨"g2_merge10_uarb1.lit.nG", .lit, F_nG, v_g2_merge10_uarb1, false, 13855669, 17976321, true, 13855693, 17976321⟩,
  ⟨"g2_merge10_uarb1.lit.nA", .lit, F_nA, v_g2_merge10_uarb1, false, 1792174, 2238265, true, 1792178, 2238265⟩,
  ⟨"g2_merge10_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge10_uarb1, false, 7185371, 8338442, true, 7185383, 8338442⟩,
  ⟨"g2_merge10_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge10_uarb1, false, 86577, 517930, false, 173161, 1035860⟩,
  ⟨"g2_merge10_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge10_uarb1, false, 406731, 786731, false, 406738, 786731⟩,
  ⟨"g2_merge10_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge10_uarb1, false, 3975516, 5174869, true, 7951047, 10349738⟩,
  ⟨"g2_merge10_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge10_uarb1, false, 8650609, 9862609, true, 8650624, 9862609⟩,
  ⟨"g2_merge10_uarb1.lit.h12", .lit, F_h12, v_g2_merge10_uarb1, false, 97550, 528903, false, 32518, 176301⟩,
  ⟨"g2_merge10_uarb1.lit.h21", .lit, F_h21, v_g2_merge10_uarb1, false, 1350677, 2562677, true, 1350685, 2562677⟩,
  ⟨"g2_merge10_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge10_uarb1, false, 1320678, 2532677, true, 1320686, 2532677⟩,
  ⟨"g2_merge10_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge10_uarb1, false, 194101, 1056806, false, 194109, 1056806⟩,
  ⟨"g2_merge10_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge10_uarb1, false, 351703, 452503, true, 1758528, 2262515⟩,
  ⟨"g2_merge10_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge10_uarb1, false, 17671, 46659, true, 312192, 824309⟩,
  ⟨"g2_merge10_uarb1.cons.mP", .cons, F_mP, v_g2_merge10_uarb1, false, 1284197, 1800242, true, 642100, 900121⟩,
  ⟨"g2_merge10_uarb1.cons.mG", .cons, F_mG, v_g2_merge10_uarb1, false, 9321305, 15395873, true, 9321329, 15395873⟩,
  ⟨"g2_merge10_uarb1.cons.mA", .cons, F_mA, v_g2_merge10_uarb1, false, 326153, 363753, true, 1630769, 1818765⟩,
  ⟨"g2_merge10_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge10_uarb1, false, 10753577, 15011965, true, 10753601, 15011965⟩,
  ⟨"g2_merge10_uarb1.cons.nP", .cons, F_nP, v_g2_merge10_uarb1, false, 5137623, 7200133, true, 5137635, 7200133⟩,
  ⟨"g2_merge10_uarb1.cons.nG", .cons, F_nG, v_g2_merge10_uarb1, false, 10722669, 14843321, true, 10722693, 14843321⟩,
  ⟨"g2_merge10_uarb1.cons.nA", .cons, F_nA, v_g2_merge10_uarb1, false, 1395674, 1841765, true, 1395678, 1841765⟩,
  ⟨"g2_merge10_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge10_uarb1, false, 5652871, 6805942, true, 5652883, 6805942⟩,
  ⟨"g2_merge10_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge10_uarb1, false, 41077, 563430, false, 27387, 375620⟩,
  ⟨"g2_merge10_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge10_uarb1, false, 286577, 690577, true, 859738, 2071731⟩,
  ⟨"g2_merge10_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge10_uarb1, false, 3068016, 4267369, true, 6136047, 8534738⟩,
  ⟨"g2_merge10_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge10_uarb1, false, 6749609, 7961609, true, 6749624, 7961609⟩,
  ⟨"g2_merge10_uarb1.cons.h12", .cons, F_h12, v_g2_merge10_uarb1, false, 52050, 574403, false, 52054, 574403⟩,
  ⟨"g2_merge10_uarb1.cons.h21", .cons, F_h21, v_g2_merge10_uarb1, false, 861677, 2073677, true, 861685, 2073677⟩,
  ⟨"g2_merge10_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge10_uarb1, false, 841678, 2053677, true, 280562, 684559⟩,
  ⟨"g2_merge10_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge10_uarb1, false, 34367, 382602, false, 103109, 1147806⟩,
  ⟨"g2_merge11_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge11_uarb1, false, 1463515, 2420499, false, 1463528, 2420499⟩,
  ⟨"g2_merge11_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge11_uarb1, false, 579221, 1349771, true, 2316897, 5399084⟩,
  ⟨"g2_merge11_uarb1.lit.mP", .lit, F_mP, v_g2_merge11_uarb1, false, 12107521, 14154083, true, 12107533, 14154083⟩,
  ⟨"g2_merge11_uarb1.lit.mG", .lit, F_mG, v_g2_merge11_uarb1, false, 11462889, 14642639, true, 11462901, 14642639⟩,
  ⟨"g2_merge11_uarb1.lit.mA", .lit, F_mA, v_g2_merge11_uarb1, false, 1359541, 1438541, true, 522901, 553285⟩,
  ⟨"g2_merge11_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge11_uarb1, false, 24413667, 28974605, true, 24413691, 28974605⟩,
  ⟨"g2_merge11_uarb1.lit.nP", .lit, F_nP, v_g2_merge11_uarb1, false, 3017633, 3547768, true, 754409, 886942⟩,
  ⟨"g2_merge11_uarb1.lit.nG", .lit, F_nG, v_g2_merge11_uarb1, false, 11689083, 14284906, true, 11689095, 14284906⟩,
  ⟨"g2_merge11_uarb1.lit.nA", .lit, F_nA, v_g2_merge11_uarb1, false, 6333097, 7192705, true, 1266621, 1438541⟩,
  ⟨"g2_merge11_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge11_uarb1, false, 11986914, 13646467, true, 11986926, 13646467⟩,
  ⟨"g2_merge11_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge11_uarb1, false, 529430, 1029713, true, 2117727, 4118852⟩,
  ⟨"g2_merge11_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge11_uarb1, false, 787733, 1729406, true, 1575473, 3458812⟩,
  ⟨"g2_merge11_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge11_uarb1, false, 3540443, 4040726, true, 14161787, 16162904⟩,
  ⟨"g2_merge11_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge11_uarb1, false, 6809759, 7751432, true, 13619533, 15502864⟩,
  ⟨"g2_merge11_uarb1.lit.h12", .lit, F_h12, v_g2_merge11_uarb1, false, 528182, 1028465, true, 528184, 1028465⟩,
  ⟨"g2_merge11_uarb1.lit.h21", .lit, F_h21, v_g2_merge11_uarb1, false, 803737, 1745410, true, 803741, 1745410⟩,
  ⟨"g2_merge11_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge11_uarb1, false, 322495, 699164, true, 1612483, 3495820⟩,
  ⟨"g2_merge11_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge11_uarb1, false, 2107729, 4108860, true, 234193, 456540⟩,
  ⟨"g2_merge11_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge11_uarb1, false, 2658515, 4811499, true, 295392, 534611⟩,
  ⟨"g2_merge11_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge11_uarb1, false, 437471, 1208021, true, 1749897, 4832084⟩,
  ⟨"g2_merge11_uarb1.cons.mP", .cons, F_mP, v_g2_merge11_uarb1, false, 10032521, 12079083, true, 10032533, 12079083⟩,
  ⟨"g2_merge11_uarb1.cons.mG", .cons, F_mG, v_g2_merge11_uarb1, false, 1341127, 1795377, true, 9387901, 12567639⟩,
  ⟨"g2_merge11_uarb1.cons.mA", .cons, F_mA, v_g2_merge11_uarb1, false, 1137141, 1216141, true, 5685713, 6080705⟩,
  ⟨"g2_merge11_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge11_uarb1, false, 20164667, 24725605, true, 20164691, 24725605⟩,
  ⟨"g2_merge11_uarb1.cons.nP", .cons, F_nP, v_g2_merge11_uarb1, false, 2498883, 3029018, true, 1249443, 1514509⟩,
  ⟨"g2_merge11_uarb1.cons.nG", .cons, F_nG, v_g2_merge11_uarb1, false, 9631583, 12227406, true, 9631595, 12227406⟩,
  ⟨"g2_merge11_uarb1.cons.nA", .cons, F_nA, v_g2_merge11_uarb1, false, 5258597, 6118205, true, 1051721, 1223641⟩,
  ⟨"g2_merge11_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge11_uarb1, false, 9954914, 11614467, true, 9954926, 11614467⟩,
  ⟨"g2_merge11_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge11_uarb1, false, 134560, 301321, true, 1614727, 3615852⟩,
  ⟨"g2_merge11_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge11_uarb1, false, 590233, 1531906, true, 1180473, 3063812⟩,
  ⟨"g2_merge11_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge11_uarb1, false, 2945443, 3445726, true, 11781787, 13782904⟩,
  ⟨"g2_merge11_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge11_uarb1, false, 1891253, 2205144, true, 140093, 163344⟩,
  ⟨"g2_merge11_uarb1.cons.h12", .cons, F_h12, v_g2_merge11_uarb1, false, 405182, 905465, true, 405184, 905465⟩,
  ⟨"g2_merge11_uarb1.cons.h21", .cons, F_h21, v_g2_merge11_uarb1, false, 607237, 1548910, true, 607241, 1548910⟩,
  ⟨"g2_merge11_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge11_uarb1, false, 244295, 620964, true, 8663, 22020⟩,
  ⟨"g2_merge11_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge11_uarb1, false, 1613729, 3614860, true, 1613737, 3614860⟩,
  ⟨"g2_merge12_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge12_uarb1, false, 423115, 1231704, true, 94027, 273712⟩,
  ⟨"g2_merge12_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge12_uarb1, false, 500747, 1310675, true, 1001507, 2621350⟩,
  ⟨"g2_merge12_uarb1.lit.mP", .lit, F_mP, v_g2_merge12_uarb1, false, 1634132, 2207977, true, 1634138, 2207977⟩,
  ⟨"g2_merge12_uarb1.lit.mG", .lit, F_mG, v_g2_merge12_uarb1, false, 5755919, 9497749, true, 5755943, 9497749⟩,
  ⟨"g2_merge12_uarb1.lit.mA", .lit, F_mA, v_g2_merge12_uarb1, false, 1921724, 2704385, true, 1921732, 2704385⟩,
  ⟨"g2_merge12_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge12_uarb1, false, 6331103, 9173243, true, 6331127, 9173243⟩,
  ⟨"g2_merge12_uarb1.lit.nP", .lit, F_nP, v_g2_merge12_uarb1, false, 37267, 46210, false, 126709, 157114⟩,
  ⟨"g2_merge12_uarb1.lit.nG", .lit, F_nG, v_g2_merge12_uarb1, false, 5869963, 10114025, true, 5869987, 10114025⟩,
  ⟨"g2_merge12_uarb1.lit.nA", .lit, F_nA, v_g2_merge12_uarb1, false, 384077, 540877, true, 1920393, 2704385⟩,
  ⟨"g2_merge12_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge12_uarb1, false, 1255931, 1989931, true, 6279679, 9949655⟩,
  ⟨"g2_merge12_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge12_uarb1, false, 152888, 954549, true, 305783, 1909098⟩,
  ⟨"g2_merge12_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge12_uarb1, false, 54635, 421623, false, 109277, 843246⟩,
  ⟨"g2_merge12_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge12_uarb1, false, 3337885, 4941207, true, 3337900, 4941207⟩,
  ⟨"g2_merge12_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge12_uarb1, false, 3436379, 5562355, true, 3436394, 5562355⟩,
  ⟨"g2_merge12_uarb1.lit.h12", .lit, F_h12, v_g2_merge12_uarb1, false, 436543, 2039865, true, 145517, 679955⟩,
  ⟨"g2_merge12_uarb1.lit.h21", .lit, F_h21, v_g2_merge12_uarb1, false, 534037, 2660013, true, 178015, 886671⟩,
  ⟨"g2_merge12_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge12_uarb1, false, 182038, 916013, false, 182046, 916013⟩,
  ⟨"g2_merge12_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge12_uarb1, false, 432544, 2035865, true, 432552, 2035865⟩,
  ⟨"g2_merge12_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge12_uarb1, false, 274115, 1082704, true, 548243, 2165408⟩,
  ⟨"g2_merge12_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge12_uarb1, false, 338747, 1148675, true, 677507, 2297350⟩,
  ⟨"g2_merge12_uarb1.cons.mP", .cons, F_mP, v_g2_merge12_uarb1, false, 1297132, 1870977, true, 1297138, 1870977⟩,
  ⟨"g2_merge12_uarb1.cons.mG", .cons, F_mG, v_g2_merge12_uarb1, false, 4424919, 8166749, true, 4424943, 8166749⟩,
  ⟨"g2_merge12_uarb1.cons.mA", .cons, F_mA, v_g2_merge12_uarb1, false, 503408, 764295, true, 1510232, 2292885⟩,
  ⟨"g2_merge12_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge12_uarb1, false, 710729, 1116749, true, 4975127, 7817243⟩,
  ⟨"g2_merge12_uarb1.cons.nP", .cons, F_nP, v_g2_merge12_uarb1, false, 1378539, 1789570, true, 275709, 357914⟩,
  ⟨"g2_merge12_uarb1.cons.nG", .cons, F_nG, v_g2_merge12_uarb1, false, 4472963, 8717025, true, 4472987, 8717025⟩,
  ⟨"g2_merge12_uarb1.cons.nA", .cons, F_nA, v_g2_merge12_uarb1, false, 301877, 458677, true, 1509393, 2293385⟩,
  ⟨"g2_merge12_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge12_uarb1, false, 971931, 1705931, true, 4859679, 8529655⟩,
  ⟨"g2_merge12_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge12_uarb1, false, 18388, 336049, false, 603, 11018⟩,
  ⟨"g2_merge12_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge12_uarb1, false, 13635, 462623, false, 27277, 925246⟩,
  ⟨"g2_merge12_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge12_uarb1, false, 2617885, 4221207, true, 2617900, 4221207⟩,
  ⟨"g2_merge12_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge12_uarb1, false, 2649379, 4775355, true, 2649394, 4775355⟩,
  ⟨"g2_merge12_uarb1.cons.h12", .cons, F_h12, v_g2_merge12_uarb1, false, 217543, 1820865, true, 72517, 606955⟩,
  ⟨"g2_merge12_uarb1.cons.h21", .cons, F_h21, v_g2_merge12_uarb1, false, 103037, 1001013, false, 103045, 1001013⟩,
  ⟨"g2_merge12_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge12_uarb1, false, 33346, 332671, false, 100046, 998013⟩,
  ⟨"g2_merge12_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge12_uarb1, false, 211544, 1814865, true, 211552, 1814865⟩,
  ⟨"g2_merge12_uarb2.lit.fork1", .lit, F_fork1, v_g2_merge12_uarb2, false, 467027, 795027, true, 622707, 1060036⟩,
  ⟨"g2_merge12_uarb2.lit.fork2", .lit, F_fork2, v_g2_merge12_uarb2, false, 1431171, 1853171, true, 2862355, 3706342⟩,
  ⟨"g2_merge12_uarb2.lit.mP", .lit, F_mP, v_g2_merge12_uarb2, false, 5158045, 6291513, true, 5158057, 6291513⟩,
  ⟨"g2_merge12_uarb2.lit.mG", .lit, F_mG, v_g2_merge12_uarb2, false, 4940858, 6620733, true, 4940870, 6620733⟩,
  ⟨"g2_merge12_uarb2.lit.mA", .lit, F_mA, v_g2_merge12_uarb2, false, 1286921, 1676921, true, 1286925, 1676921⟩,
  ⟨"g2_merge12_uarb2.lit.mGG", .lit, F_mGG, v_g2_merge12_uarb2, false, 9871355, 12345637, true, 9871379, 12345637⟩,
  ⟨"g2_merge12_uarb2.lit.nP", .lit, F_nP, v_g2_merge12_uarb2, false, 5317199, 6132359, true, 5317211, 6132359⟩,
  ⟨"g2_merge12_uarb2.lit.nG", .lit, F_nG, v_g2_merge12_uarb2, false, 2118409, 3362321, true, 2118415, 3362321⟩,
  ⟨"g2_merge12_uarb2.lit.nA", .lit, F_nA, v_g2_merge12_uarb2, false, 3150937, 3696937, true, 3150945, 3696937⟩,
  ⟨"g2_merge12_uarb2.lit.nGG", .lit, F_nGG, v_g2_merge12_uarb2, false, 9458311, 13866799, true, 9458335, 13866799⟩,
  ⟨"g2_merge12_uarb2.lit.rt1", .lit, F_rt1, v_g2_merge12_uarb2, false, 203, 333, true, 1218007, 1998000⟩,
  ⟨"g2_merge12_uarb2.lit.rt1b", .lit, F_rt1b, v_g2_merge12_uarb2, false, 24500, 101991, false, 196007, 815928⟩,
  ⟨"g2_merge12_uarb2.lit.rt1s", .lit, F_rt1s, v_g2_merge12_uarb2, false, 2186593, 2446593, true, 728866, 815531⟩,
  ⟨"g2_merge12_uarb2.lit.rt1bs", .lit, F_rt1bs, v_g2_merge12_uarb2, false, 6050779, 7866707, true, 6050794, 7866707⟩,
  ⟨"g2_merge12_uarb2.lit.h12", .lit, F_h12, v_g2_merge12_uarb2, false, 1208579, 1988579, true, 1208587, 1988579⟩,
  ⟨"g2_merge12_uarb2.lit.h21", .lit, F_h21, v_g2_merge12_uarb2, false, 220579, 840507, false, 73529, 280169⟩,
  ⟨"g2_merge12_uarb2.lit.o1x", .lit, F_o1x, v_g2_merge12_uarb2, false, 221580, 841507, false, 221588, 841507⟩,
  ⟨"g2_merge12_uarb2.lit.o2x", .lit, F_o2x, v_g2_merge12_uarb2, false, 112780, 183689, true, 1240588, 2020579⟩,
  ⟨"g2_merge12_uarb2.cons.fork1", .cons, F_fork1, v_g2_merge12_uarb2, false, 345777, 673777, true, 1383121, 2695108⟩,
  ⟨"g2_merge12_uarb2.cons.fork2", .cons, F_fork2, v_g2_merge12_uarb2, false, 1143671, 1565671, true, 2287355, 3131342⟩,
  ⟨"g2_merge12_uarb2.cons.mP", .cons, F_mP, v_g2_merge12_uarb2, false, 4187045, 5320513, true, 4187057, 5320513⟩,
  ⟨"g2_merge12_uarb2.cons.mG", .cons, F_mG, v_g2_merge12_uarb2, false, 3952358, 5632233, true, 3952370, 5632233⟩,
  ⟨"g2_merge12_uarb2.cons.mA", .cons, F_mA, v_g2_merge12_uarb2, false, 343807, 473807, true, 1031425, 1421421⟩,
  ⟨"g2_merge12_uarb2.cons.mGG", .cons, F_mGG, v_g2_merge12_uarb2, false, 7968355, 10442637, true, 7968379, 10442637⟩,
  ⟨"g2_merge12_uarb2.cons.nP", .cons, F_nP, v_g2_merge12_uarb2, false, 1448733, 1720453, true, 1448737, 1720453⟩,
  ⟨"g2_merge12_uarb2.cons.nG", .cons, F_nG, v_g2_merge12_uarb2, false, 1651159, 2895071, true, 1651165, 2895071⟩,
  ⟨"g2_merge12_uarb2.cons.nA", .cons, F_nA, v_g2_merge12_uarb2, false, 854979, 1036979, true, 2564945, 3110937⟩,
  ⟨"g2_merge12_uarb2.cons.nGG", .cons, F_nGG, v_g2_merge12_uarb2, false, 7467311, 11875799, true, 7467335, 11875799⟩,
  ⟨"g2_merge12_uarb2.cons.rt1", .cons, F_rt1, v_g2_merge12_uarb2, false, 363, 679, false, 363007, 679000⟩,
  ⟨"g2_merge12_uarb2.cons.rt1b", .cons, F_rt1b, v_g2_merge12_uarb2, false, 15500, 110991, false, 124007, 887928⟩,
  ⟨"g2_merge12_uarb2.cons.rt1s", .cons, F_rt1s, v_g2_merge12_uarb2, false, 5351779, 6131779, true, 5351794, 6131779⟩,
  ⟨"g2_merge12_uarb2.cons.rt1bs", .cons, F_rt1bs, v_g2_merge12_uarb2, false, 4841779, 6657707, true, 4841794, 6657707⟩,
  ⟨"g2_merge12_uarb2.cons.h12", .cons, F_h12, v_g2_merge12_uarb2, false, 908579, 1688579, true, 908587, 1688579⟩,
  ⟨"g2_merge12_uarb2.cons.h21", .cons, F_h21, v_g2_merge12_uarb2, false, 148579, 912507, false, 49529, 304169⟩,
  ⟨"g2_merge12_uarb2.cons.o1x", .cons, F_o1x, v_g2_merge12_uarb2, false, 149580, 913507, false, 149588, 913507⟩,
  ⟨"g2_merge12_uarb2.cons.o2x", .cons, F_o2x, v_g2_merge12_uarb2, false, 929580, 1709579, true, 929588, 1709579⟩,
  ⟨"g2_merge2_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge2_uarb1, false, 289207, 434489, false, 578427, 868978⟩,
  ⟨"g2_merge2_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge2_uarb1, false, 1648503, 2977067, true, 1648516, 2977067⟩,
  ⟨"g2_merge2_uarb1.lit.mP", .lit, F_mP, v_g2_merge2_uarb1, false, 7419091, 9465653, true, 7419103, 9465653⟩,
  ⟨"g2_merge2_uarb1.lit.mG", .lit, F_mG, v_g2_merge2_uarb1, false, 4697479, 6468403, true, 4697487, 6468403⟩,
  ⟨"g2_merge2_uarb1.lit.mA", .lit, F_mA, v_g2_merge2_uarb1, false, 2171593, 2369093, true, 2171597, 2369093⟩,
  ⟨"g2_merge2_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge2_uarb1, false, 7679859, 9436964, true, 7679871, 9436964⟩,
  ⟨"g2_merge2_uarb1.lit.nP", .lit, F_nP, v_g2_merge2_uarb1, false, 1335095, 1479029, true, 1335097, 1479029⟩,
  ⟨"g2_merge2_uarb1.lit.nG", .lit, F_nG, v_g2_merge2_uarb1, false, 15358999, 19208437, true, 15359023, 19208437⟩,
  ⟨"g2_merge2_uarb1.lit.nA", .lit, F_nA, v_g2_merge2_uarb1, false, 2049593, 2369093, true, 2049597, 2369093⟩,
  ⟨"g2_merge2_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge2_uarb1, false, 15546801, 18780635, true, 3109365, 3756127⟩,
  ⟨"g2_merge2_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge2_uarb1, false, 23597, 181079, false, 94395, 724316⟩,
  ⟨"g2_merge2_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge2_uarb1, false, 149780, 377467, false, 299567, 754934⟩,
  ⟨"g2_merge2_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge2_uarb1, false, 95520, 117451, true, 8405775, 10335688⟩,
  ⟨"g2_merge2_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge2_uarb1, false, 4495966, 5160653, true, 8991947, 10321306⟩,
  ⟨"g2_merge2_uarb1.lit.h12", .lit, F_h12, v_g2_merge2_uarb1, false, 1415, 9423, true, 341023, 2270943⟩,
  ⟨"g2_merge2_uarb1.lit.h21", .lit, F_h21, v_g2_merge2_uarb1, false, 927187, 2256561, true, 309065, 752187⟩,
  ⟨"g2_merge2_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge2_uarb1, false, 932188, 2261561, true, 932196, 2261561⟩,
  ⟨"g2_merge2_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge2_uarb1, false, 336016, 2265943, true, 336024, 2265943⟩,
  ⟨"g2_merge2_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge2_uarb1, false, 661207, 1081489, true, 1322427, 2162978⟩,
  ⟨"g2_merge2_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge2_uarb1, false, 1105503, 2434067, true, 1105516, 2434067⟩,
  ⟨"g2_merge2_uarb1.cons.mP", .cons, F_mP, v_g2_merge2_uarb1, false, 5968091, 8014653, true, 5968103, 8014653⟩,
  ⟨"g2_merge2_uarb1.cons.mG", .cons, F_mG, v_g2_merge2_uarb1, false, 1246493, 1836801, true, 3739487, 5510403⟩,
  ⟨"g2_merge2_uarb1.cons.mA", .cons, F_mA, v_g2_merge2_uarb1, false, 1754843, 1952343, true, 194983, 216927⟩,
  ⟨"g2_merge2_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge2_uarb1, false, 6159859, 7916964, true, 166483, 213972⟩,
  ⟨"g2_merge2_uarb1.cons.nP", .cons, F_nP, v_g2_merge2_uarb1, false, 3279785, 3711587, true, 3279791, 3711587⟩,
  ⟨"g2_merge2_uarb1.cons.nG", .cons, F_nG, v_g2_merge2_uarb1, false, 4088333, 5371479, true, 4088341, 5371479⟩,
  ⟨"g2_merge2_uarb1.cons.nA", .cons, F_nA, v_g2_merge2_uarb1, false, 1668343, 1987843, true, 1668347, 1987843⟩,
  ⟨"g2_merge2_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge2_uarb1, false, 12570801, 15804635, true, 2514165, 3160927⟩,
  R_g2_merge2_uarb1_cons_rt1,
  ⟨"g2_merge2_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge2_uarb1, false, 305280, 969967, true, 610567, 1939934⟩,
  ⟨"g2_merge2_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge2_uarb1, false, 848345, 1089586, true, 6786775, 8716688⟩,
  ⟨"g2_merge2_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge2_uarb1, false, 3646466, 4311153, true, 7292947, 8622306⟩,
  ⟨"g2_merge2_uarb1.cons.h12", .cons, F_h12, v_g2_merge2_uarb1, false, 13005, 274981, false, 39023, 824943⟩,
  ⟨"g2_merge2_uarb1.cons.h21", .cons, F_h21, v_g2_merge2_uarb1, false, 614187, 1943561, true, 614195, 1943561⟩,
  ⟨"g2_merge2_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge2_uarb1, false, 621188, 1950561, true, 621196, 1950561⟩,
  ⟨"g2_merge2_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge2_uarb1, false, 33672, 676981, true, 101024, 2030943⟩,
  ⟨"g2_merge3_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge3_uarb1, false, 811679, 1233679, true, 1623371, 2467358⟩,
  ⟨"g2_merge3_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge3_uarb1, false, 244417, 502017, true, 407366, 836695⟩,
  ⟨"g2_merge3_uarb1.lit.mP", .lit, F_mP, v_g2_merge3_uarb1, false, 825873, 940133, true, 5781123, 6580931⟩,
  ⟨"g2_merge3_uarb1.lit.mG", .lit, F_mG, v_g2_merge3_uarb1, false, 5038675, 6909726, true, 5038687, 6909726⟩,
  ⟨"g2_merge3_uarb1.lit.mA", .lit, F_mA, v_g2_merge3_uarb1, false, 6403021, 7495021, true, 6403037, 7495021⟩,
  ⟨"g2_merge3_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge3_uarb1, false, 5349630, 6944771, true, 5349642, 6944771⟩,
  ⟨"g2_merge3_uarb1.lit.nP", .lit, F_nP, v_g2_merge3_uarb1, false, 1837467, 2588575, false, 1837479, 2588575⟩,
  ⟨"g2_merge3_uarb1.lit.nG", .lit, F_nG, v_g2_merge3_uarb1, false, 3072993, 4755941, true, 3073001, 4755941⟩,
  ⟨"g2_merge3_uarb1.lit.nA", .lit, F_nA, v_g2_merge3_uarb1, false, 5959021, 7495021, true, 5959037, 7495021⟩,
  ⟨"g2_merge3_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge3_uarb1, false, 10035533, 13255269, true, 10035557, 13255269⟩,
  ⟨"g2_merge3_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge3_uarb1, false, 185491, 482491, true, 741971, 1929964⟩,
  ⟨"g2_merge3_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge3_uarb1, false, 8991, 140491, false, 2767, 43228⟩,
  ⟨"g2_merge3_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge3_uarb1, false, 5924597, 7112597, true, 5924612, 7112597⟩,
  ⟨"g2_merge3_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge3_uarb1, false, 5293597, 6879597, true, 5293612, 6879597⟩,
  ⟨"g2_merge3_uarb1.lit.h12", .lit, F_h12, v_g2_merge3_uarb1, false, 735217, 1923217, true, 735225, 1923217⟩,
  R_g2_merge3_uarb1_lit_h21,
  ⟨"g2_merge3_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge3_uarb1, false, 143218, 1729217, true, 143226, 1729217⟩,
  ⟨"g2_merge3_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge3_uarb1, false, 730218, 1918217, true, 104318, 274031⟩,
  ⟨"g2_merge3_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge3_uarb1, false, 617179, 1039179, true, 411457, 692786⟩,
  ⟨"g2_merge3_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge3_uarb1, false, 177017, 434617, true, 885098, 2173085⟩,
  ⟨"g2_merge3_uarb1.cons.mP", .cons, F_mP, v_g2_merge3_uarb1, false, 4638111, 5437931, true, 4638123, 5437931⟩,
  ⟨"g2_merge3_uarb1.cons.mG", .cons, F_mG, v_g2_merge3_uarb1, false, 3931175, 5802226, true, 3931187, 5802226⟩,
  ⟨"g2_merge3_uarb1.cons.mA", .cons, F_mA, v_g2_merge3_uarb1, false, 5114021, 6206021, true, 5114037, 6206021⟩,
  ⟨"g2_merge3_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge3_uarb1, false, 4208630, 5803771, true, 4208642, 5803771⟩,
  ⟨"g2_merge3_uarb1.cons.nP", .cons, F_nP, v_g2_merge3_uarb1, false, 3999467, 6076575, true, 3999479, 6076575⟩,
  ⟨"g2_merge3_uarb1.cons.nG", .cons, F_nG, v_g2_merge3_uarb1, false, 2347993, 4030941, true, 782667, 1343647⟩,
  ⟨"g2_merge3_uarb1.cons.nA", .cons, F_nA, v_g2_merge3_uarb1, false, 1571007, 2083007, true, 4713037, 6249021⟩,
  ⟨"g2_merge3_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge3_uarb1, false, 7879533, 11099269, true, 7879557, 11099269⟩,
  ⟨"g2_merge3_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge3_uarb1, false, 122741, 419741, true, 490971, 1678964⟩,
  R_g2_merge3_uarb1_cons_rt1b,
  ⟨"g2_merge3_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge3_uarb1, false, 1573199, 1969199, true, 1573204, 1969199⟩,
  ⟨"g2_merge3_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge3_uarb1, false, 4169597, 5755597, true, 4169612, 5755597⟩,
  ⟨"g2_merge3_uarb1.cons.h12", .cons, F_h12, v_g2_merge3_uarb1, false, 493217, 1681217, true, 493225, 1681217⟩,
  R_g2_merge3_uarb1_cons_h21,
  R_g2_merge3_uarb1_cons_o1x,
  ⟨"g2_merge3_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge3_uarb1, false, 486218, 1674217, true, 486226, 1674217⟩,
  ⟨"g2_merge4_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge4_uarb1, false, 785333, 1440333, true, 1570679, 2880666⟩,
  ⟨"g2_merge4_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge4_uarb1, false, 771491, 1502915, false, 771504, 1502915⟩,
  ⟨"g2_merge4_uarb1.lit.mP", .lit, F_mP, v_g2_merge4_uarb1, false, 3550678, 4119391, true, 3550684, 4119391⟩,
  ⟨"g2_merge4_uarb1.lit.mG", .lit, F_mG, v_g2_merge4_uarb1, false, 6978391, 8922848, true, 6978403, 8922848⟩,
  ⟨"g2_merge4_uarb1.lit.mA", .lit, F_mA, v_g2_merge4_uarb1, false, 7462299, 9020299, true, 7462315, 9020299⟩,
  ⟨"g2_merge4_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge4_uarb1, false, 14317725, 17317213, true, 14317749, 17317213⟩,
  ⟨"g2_merge4_uarb1.lit.nP", .lit, F_nP, v_g2_merge4_uarb1, false, 3319541, 4350528, true, 474221, 621504⟩,
  ⟨"g2_merge4_uarb1.lit.nG", .lit, F_nG, v_g2_merge4_uarb1, false, 12915019, 18078237, true, 12915043, 18078237⟩,
  ⟨"g2_merge4_uarb1.lit.nA", .lit, F_nA, v_g2_merge4_uarb1, false, 2979839, 3801263, false, 2979855, 3801263⟩,
  ⟨"g2_merge4_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge4_uarb1, false, 3538444, 4375755, true, 707690, 875151⟩,
  ⟨"g2_merge4_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge4_uarb1, false, 553833, 1299974, true, 1107673, 2599948⟩,
  ⟨"g2_merge4_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge4_uarb1, false, 584501, 1105465, true, 1169009, 2210930⟩,
  ⟨"g2_merge4_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge4_uarb1, false, 4196546, 4942687, true, 8393107, 9885374⟩,
  ⟨"g2_merge4_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge4_uarb1, false, 2113607, 2374089, true, 8454443, 9496356⟩,
  ⟨"g2_merge4_uarb1.lit.h12", .lit, F_h12, v_g2_merge4_uarb1, false, 1099073, 2591355, true, 1099081, 2591355⟩,
  ⟨"g2_merge4_uarb1.lit.h21", .lit, F_h21, v_g2_merge4_uarb1, false, 1161409, 2203337, true, 1161417, 2203337⟩,
  ⟨"g2_merge4_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge4_uarb1, false, 1128410, 2170337, true, 1128418, 2170337⟩,
  ⟨"g2_merge4_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge4_uarb1, false, 125786, 291595, true, 1132082, 2624355⟩,
  ⟨"g2_merge4_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge4_uarb1, false, 577333, 1232333, true, 1154679, 2464666⟩,
  ⟨"g2_merge4_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge4_uarb1, false, 721491, 1552915, false, 103072, 221845⟩,
  ⟨"g2_merge4_uarb1.cons.mP", .cons, F_mP, v_g2_merge4_uarb1, false, 2803678, 3372391, true, 2803684, 3372391⟩,
  ⟨"g2_merge4_uarb1.cons.mG", .cons, F_mG, v_g2_merge4_uarb1, false, 5426891, 7371348, true, 5426903, 7371348⟩,
  ⟨"g2_merge4_uarb1.cons.mA", .cons, F_mA, v_g2_merge4_uarb1, false, 5867299, 7425299, true, 5867315, 7425299⟩,
  ⟨"g2_merge4_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge4_uarb1, false, 11237725, 14237213, true, 11237749, 14237213⟩,
  ⟨"g2_merge4_uarb1.cons.nP", .cons, F_nP, v_g2_merge4_uarb1, false, 2572541, 3603528, true, 2572547, 3603528⟩,
  ⟨"g2_merge4_uarb1.cons.nG", .cons, F_nG, v_g2_merge4_uarb1, false, 9899019, 15062237, true, 9899043, 15062237⟩,
  ⟨"g2_merge4_uarb1.cons.nA", .cons, F_nA, v_g2_merge4_uarb1, false, 2918839, 3862263, false, 2918855, 3862263⟩,
  ⟨"g2_merge4_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge4_uarb1, false, 2766694, 3604005, true, 553340, 720801⟩,
  ⟨"g2_merge4_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge4_uarb1, false, 381833, 1127974, true, 763673, 2255948⟩,
  ⟨"g2_merge4_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge4_uarb1, false, 425001, 945965, true, 850009, 1891930⟩,
  ⟨"g2_merge4_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge4_uarb1, false, 301186, 369017, true, 6626107, 8118374⟩,
  ⟨"g2_merge4_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge4_uarb1, false, 1678107, 1938589, true, 6712443, 7754356⟩,
  ⟨"g2_merge4_uarb1.cons.h12", .cons, F_h12, v_g2_merge4_uarb1, false, 764073, 2256355, true, 764081, 2256355⟩,
  ⟨"g2_merge4_uarb1.cons.h21", .cons, F_h21, v_g2_merge4_uarb1, false, 851409, 1893337, true, 851417, 1893337⟩,
  ⟨"g2_merge4_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge4_uarb1, false, 833410, 1875337, true, 833418, 1875337⟩,
  ⟨"g2_merge4_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge4_uarb1, false, 782074, 2274355, true, 782082, 2274355⟩,
  ⟨"g2_merge6_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge6_uarb1, false, 2527753, 3394173, true, 2527766, 3394173⟩,
  ⟨"g2_merge6_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge6_uarb1, false, 1673173, 2689173, true, 1673186, 2689173⟩,
  ⟨"g2_merge6_uarb1.lit.mP", .lit, F_mP, v_g2_merge6_uarb1, false, 3043578, 3442679, true, 3043584, 3442679⟩,
  ⟨"g2_merge6_uarb1.lit.mG", .lit, F_mG, v_g2_merge6_uarb1, false, 5385312, 7461155, true, 5385324, 7461155⟩,
  ⟨"g2_merge6_uarb1.lit.mA", .lit, F_mA, v_g2_merge6_uarb1, false, 6990897, 8105317, true, 6990913, 8105317⟩,
  ⟨"g2_merge6_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge6_uarb1, false, 11674365, 15275849, true, 11674389, 15275849⟩,
  ⟨"g2_merge6_uarb1.lit.nP", .lit, F_nP, v_g2_merge6_uarb1, false, 694983, 839855, false, 694987, 839855⟩,
  ⟨"g2_merge6_uarb1.lit.nG", .lit, F_nG, v_g2_merge6_uarb1, false, 11077997, 15278217, true, 11078021, 15278217⟩,
  ⟨"g2_merge6_uarb1.lit.nA", .lit, F_nA, v_g2_merge6_uarb1, false, 5981617, 7245617, true, 5981633, 7245617⟩,
  ⟨"g2_merge6_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge6_uarb1, false, 11179665, 14415269, true, 11179689, 14415269⟩,
  ⟨"g2_merge6_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge6_uarb1, false, 265491, 599491, true, 1061971, 2397964⟩,
  ⟨"g2_merge6_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge6_uarb1, false, 196991, 597991, true, 787971, 2391964⟩,
  ⟨"g2_merge6_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge6_uarb1, false, 7178221, 8514221, true, 7178236, 8514221⟩,
  ⟨"g2_merge6_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge6_uarb1, false, 6904221, 8508221, true, 6904236, 8508221⟩,
  ⟨"g2_merge6_uarb1.lit.h12", .lit, F_h12, v_g2_merge6_uarb1, false, 1053371, 2389371, true, 1053379, 2389371⟩,
  ⟨"g2_merge6_uarb1.lit.h21", .lit, F_h21, v_g2_merge6_uarb1, false, 780371, 2384371, true, 780379, 2384371⟩,
  ⟨"g2_merge6_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge6_uarb1, false, 747372, 2351371, true, 747380, 2351371⟩,
  ⟨"g2_merge6_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge6_uarb1, false, 51732, 115351, true, 1086380, 2422371⟩,
  ⟨"g2_merge6_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge6_uarb1, false, 1835753, 2702173, true, 1835766, 2702173⟩,
  ⟨"g2_merge6_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge6_uarb1, false, 1147173, 2163173, true, 1147186, 2163173⟩,
  ⟨"g2_merge6_uarb1.cons.mP", .cons, F_mP, v_g2_merge6_uarb1, false, 2426578, 2825679, true, 2426584, 2825679⟩,
  ⟨"g2_merge6_uarb1.cons.mG", .cons, F_mG, v_g2_merge6_uarb1, false, 4168812, 6244655, true, 4168824, 6244655⟩,
  ⟨"g2_merge6_uarb1.cons.mA", .cons, F_mA, v_g2_merge6_uarb1, false, 5538897, 6653317, true, 5538913, 6653317⟩,
  ⟨"g2_merge6_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge6_uarb1, false, 9102365, 12703849, true, 9102389, 12703849⟩,
  ⟨"g2_merge6_uarb1.cons.nP", .cons, F_nP, v_g2_merge6_uarb1, false, 4645949, 5858565, true, 4645961, 5858565⟩,
  ⟨"g2_merge6_uarb1.cons.nG", .cons, F_nG, v_g2_merge6_uarb1, false, 8564997, 12765217, true, 8565021, 12765217⟩,
  ⟨"g2_merge6_uarb1.cons.nA", .cons, F_nA, v_g2_merge6_uarb1, false, 4742617, 6006617, true, 4742633, 6006617⟩,
  ⟨"g2_merge6_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge6_uarb1, false, 8757665, 11993269, true, 8757689, 11993269⟩,
  ⟨"g2_merge6_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge6_uarb1, false, 151491, 485491, true, 605971, 1941964⟩,
  ⟨"g2_merge6_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge6_uarb1, false, 33491, 197991, false, 44657, 263988⟩,
  ⟨"g2_merge6_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge6_uarb1, false, 5559221, 6895221, true, 5559236, 6895221⟩,
  ⟨"g2_merge6_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge6_uarb1, false, 5305221, 6909221, true, 5305236, 6909221⟩,
  ⟨"g2_merge6_uarb1.cons.h12", .cons, F_h12, v_g2_merge6_uarb1, false, 607371, 1943371, true, 607379, 1943371⟩,
  ⟨"g2_merge6_uarb1.cons.h21", .cons, F_h21, v_g2_merge6_uarb1, false, 353371, 1957371, true, 9061, 50189⟩,
  ⟨"g2_merge6_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge6_uarb1, false, 335372, 1939371, true, 335380, 1939371⟩,
  ⟨"g2_merge6_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge6_uarb1, false, 625372, 1961371, true, 625380, 1961371⟩,
  ⟨"g2_merge9_uarb1.lit.fork1", .lit, F_fork1, v_g2_merge9_uarb1, false, 285763, 378483, false, 190513, 252322⟩,
  ⟨"g2_merge9_uarb1.lit.fork2", .lit, F_fork2, v_g2_merge9_uarb1, false, 126627, 306727, false, 379894, 920181⟩,
  ⟨"g2_merge9_uarb1.lit.mP", .lit, F_mP, v_g2_merge9_uarb1, false, 4839023, 6939661, true, 4839035, 6939661⟩,
  ⟨"g2_merge9_uarb1.lit.mG", .lit, F_mG, v_g2_merge9_uarb1, false, 8703451, 13726673, true, 8703475, 13726673⟩,
  ⟨"g2_merge9_uarb1.lit.mA", .lit, F_mA, v_g2_merge9_uarb1, false, 332813, 372585, true, 1664069, 1862925⟩,
  ⟨"g2_merge9_uarb1.lit.mGG", .lit, F_mGG, v_g2_merge9_uarb1, false, 1315086, 1711409, true, 1315089, 1711409⟩,
  ⟨"g2_merge9_uarb1.lit.nP", .lit, F_nP, v_g2_merge9_uarb1, false, 5493935, 6284749, true, 5493947, 6284749⟩,
  ⟨"g2_merge9_uarb1.lit.nG", .lit, F_nG, v_g2_merge9_uarb1, false, 1250626, 1747869, true, 1250629, 1747869⟩,
  ⟨"g2_merge9_uarb1.lit.nA", .lit, F_nA, v_g2_merge9_uarb1, false, 1280606, 1742681, true, 1280610, 1742681⟩,
  ⟨"g2_merge9_uarb1.lit.nGG", .lit, F_nGG, v_g2_merge9_uarb1, false, 9633497, 13068627, true, 9633521, 13068627⟩,
  ⟨"g2_merge9_uarb1.lit.rt1", .lit, F_rt1, v_g2_merge9_uarb1, false, 169, 671, false, 169007, 671000⟩,
  ⟨"g2_merge9_uarb1.lit.rt1b", .lit, F_rt1b, v_g2_merge9_uarb1, false, 83, 338, false, 166007, 676000⟩,
  ⟨"g2_merge9_uarb1.lit.rt1s", .lit, F_rt1s, v_g2_merge9_uarb1, false, 2802477, 3601477, true, 5604969, 7202954⟩,
  ⟨"g2_merge9_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g2_merge9_uarb1, false, 2833477, 3611477, true, 5666969, 7222954⟩,
  ⟨"g2_merge9_uarb1.lit.h12", .lit, F_h12, v_g2_merge9_uarb1, false, 268233, 1067233, true, 268237, 1067233⟩,
  ⟨"g2_merge9_uarb1.lit.h21", .lit, F_h21, v_g2_merge9_uarb1, false, 31411, 116411, false, 94237, 349233⟩,
  ⟨"g2_merge9_uarb1.lit.o1x", .lit, F_o1x, v_g2_merge9_uarb1, false, 569467, 2125466, true, 569475, 2125466⟩,
  ⟨"g2_merge9_uarb1.lit.o2x", .lit, F_o2x, v_g2_merge9_uarb1, false, 565467, 2163466, true, 565475, 2163466⟩,
  ⟨"g2_merge9_uarb1.cons.fork1", .cons, F_fork1, v_g2_merge9_uarb1, false, 276763, 387483, false, 184513, 258322⟩,
  ⟨"g2_merge9_uarb1.cons.fork2", .cons, F_fork2, v_g2_merge9_uarb1, false, 778881, 2379181, true, 778894, 2379181⟩,
  ⟨"g2_merge9_uarb1.cons.mP", .cons, F_mP, v_g2_merge9_uarb1, false, 3815023, 5915661, true, 3815035, 5915661⟩,
  ⟨"g2_merge9_uarb1.cons.mG", .cons, F_mG, v_g2_merge9_uarb1, false, 6753451, 11776673, true, 6753475, 11776673⟩,
  ⟨"g2_merge9_uarb1.cons.mA", .cons, F_mA, v_g2_merge9_uarb1, false, 271113, 310885, true, 1355569, 1554425⟩,
  ⟨"g2_merge9_uarb1.cons.mGG", .cons, F_mGG, v_g2_merge9_uarb1, false, 1050836, 1447159, true, 1050839, 1447159⟩,
  ⟨"g2_merge9_uarb1.cons.nP", .cons, F_nP, v_g2_merge9_uarb1, false, 4469935, 5260749, true, 4469947, 5260749⟩,
  ⟨"g2_merge9_uarb1.cons.nG", .cons, F_nG, v_g2_merge9_uarb1, false, 988876, 1486119, true, 988879, 1486119⟩,
  ⟨"g2_merge9_uarb1.cons.nA", .cons, F_nA, v_g2_merge9_uarb1, false, 1017356, 1479431, true, 1017360, 1479431⟩,
  ⟨"g2_merge9_uarb1.cons.nGG", .cons, F_nGG, v_g2_merge9_uarb1, false, 7655497, 11090627, true, 7655521, 11090627⟩,
  ⟨"g2_merge9_uarb1.cons.rt1", .cons, F_rt1, v_g2_merge9_uarb1, false, 53, 367, false, 106007, 734000⟩,
  ⟨"g2_merge9_uarb1.cons.rt1b", .cons, F_rt1b, v_g2_merge9_uarb1, false, 52, 369, false, 34669, 246000⟩,
  ⟨"g2_merge9_uarb1.cons.rt1s", .cons, F_rt1s, v_g2_merge9_uarb1, false, 2239477, 3038477, true, 4478969, 6076954⟩,
  ⟨"g2_merge9_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g2_merge9_uarb1, false, 2263977, 3041977, true, 4527969, 6083954⟩,
  ⟨"g2_merge9_uarb1.cons.h12", .cons, F_h12, v_g2_merge9_uarb1, false, 143733, 942733, true, 13067, 85703⟩,
  ⟨"g2_merge9_uarb1.cons.h21", .cons, F_h21, v_g2_merge9_uarb1, false, 63233, 380233, false, 63237, 380233⟩,
  ⟨"g2_merge9_uarb1.cons.o1x", .cons, F_o1x, v_g2_merge9_uarb1, false, 42489, 253822, false, 127475, 761466⟩,
  ⟨"g2_merge9_uarb1.cons.o2x", .cons, F_o2x, v_g2_merge9_uarb1, false, 307467, 1905466, true, 307475, 1905466⟩
]

/-- The rows of seed 3: 9 arbiters × 2 readings × 18 conditions. -/
def rows_g3 : List Row := [
  ⟨"g3_merge10_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge10_uarb1, false, 696995, 1174421, true, 2090998, 3523263⟩,
  ⟨"g3_merge10_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge10_uarb1, false, 1985921, 3555849, true, 661978, 1185283⟩,
  ⟨"g3_merge10_uarb1.lit.mP", .lit, F_mP, v_g3_merge10_uarb1, false, 321701, 363461, true, 6112331, 6905759⟩,
  ⟨"g3_merge10_uarb1.lit.mG", .lit, F_mG, v_g3_merge10_uarb1, false, 5674021, 7547015, true, 5674033, 7547015⟩,
  ⟨"g3_merge10_uarb1.lit.mA", .lit, F_mA, v_g3_merge10_uarb1, false, 3288932, 4129071, true, 3288940, 4129071⟩,
  ⟨"g3_merge10_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge10_uarb1, false, 11813587, 15014135, true, 11813611, 15014135⟩,
  ⟨"g3_merge10_uarb1.lit.nP", .lit, F_nP, v_g3_merge10_uarb1, false, 3052176, 3456863, true, 3052182, 3456863⟩,
  ⟨"g3_merge10_uarb1.lit.nG", .lit, F_nG, v_g3_merge10_uarb1, false, 2732281, 3912439, true, 2732287, 3912439⟩,
  ⟨"g3_merge10_uarb1.lit.nA", .lit, F_nA, v_g3_merge10_uarb1, false, 1073369, 1376357, true, 3220115, 4129071⟩,
  ⟨"g3_merge10_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge10_uarb1, false, 5632493, 7712122, true, 5632505, 7712122⟩,
  ⟨"g3_merge10_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge10_uarb1, false, 1170669, 2342633, true, 1170676, 2342633⟩,
  ⟨"g3_merge10_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge10_uarb1, false, 98827, 482403, false, 65887, 321602⟩,
  ⟨"g3_merge10_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge10_uarb1, false, 1824177, 2117168, true, 7296723, 8468672⟩,
  ⟨"g3_merge10_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge10_uarb1, false, 253359, 332735, true, 2280236, 2994615⟩,
  ⟨"g3_merge10_uarb1.lit.h12", .lit, F_h12, v_g3_merge10_uarb1, false, 291324, 584315, true, 291326, 584315⟩,
  ⟨"g3_merge10_uarb1.lit.h21", .lit, F_h21, v_g3_merge10_uarb1, false, 222281, 989433, false, 222289, 989433⟩,
  ⟨"g3_merge10_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge10_uarb1, false, 223282, 990433, false, 223290, 990433⟩,
  ⟨"g3_merge10_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge10_uarb1, false, 1195297, 2367260, true, 239061, 473452⟩,
  ⟨"g3_merge10_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge10_uarb1, false, 516995, 994421, true, 1550998, 2983263⟩,
  ⟨"g3_merge10_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge10_uarb1, false, 1498921, 3068849, true, 1498934, 3068849⟩,
  ⟨"g3_merge10_uarb1.cons.mP", .cons, F_mP, v_g3_merge10_uarb1, false, 4978319, 5771759, true, 4978331, 5771759⟩,
  ⟨"g3_merge10_uarb1.cons.mG", .cons, F_mG, v_g3_merge10_uarb1, false, 4524521, 6397515, true, 4524533, 6397515⟩,
  ⟨"g3_merge10_uarb1.cons.mA", .cons, F_mA, v_g3_merge10_uarb1, false, 2637432, 3477571, true, 2637440, 3477571⟩,
  ⟨"g3_merge10_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge10_uarb1, false, 9469587, 12670135, true, 9469611, 12670135⟩,
  ⟨"g3_merge10_uarb1.cons.nP", .cons, F_nP, v_g3_merge10_uarb1, false, 2485176, 2889863, true, 2485182, 2889863⟩,
  ⟨"g3_merge10_uarb1.cons.nG", .cons, F_nG, v_g3_merge10_uarb1, false, 716677, 1110063, true, 238893, 370021⟩,
  ⟨"g3_merge10_uarb1.cons.nA", .cons, F_nA, v_g3_merge10_uarb1, false, 2579107, 3488071, true, 2579115, 3488071⟩,
  ⟨"g3_merge10_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge10_uarb1, false, 4466493, 6546122, true, 4466505, 6546122⟩,
  ⟨"g3_merge10_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge10_uarb1, false, 848669, 2020633, true, 848676, 2020633⟩,
  ⟨"g3_merge10_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge10_uarb1, false, 58827, 522403, false, 117661, 1044806⟩,
  ⟨"g3_merge10_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge10_uarb1, false, 1478677, 1771668, true, 5914723, 7086672⟩,
  ⟨"g3_merge10_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge10_uarb1, false, 1813231, 2527615, true, 1813236, 2527615⟩,
  ⟨"g3_merge10_uarb1.cons.h12", .cons, F_h12, v_g3_merge10_uarb1, false, 213074, 506065, true, 213076, 506065⟩,
  ⟨"g3_merge10_uarb1.cons.h21", .cons, F_h21, v_g3_merge10_uarb1, false, 142281, 1069433, false, 142289, 1069433⟩,
  ⟨"g3_merge10_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge10_uarb1, false, 143282, 1070433, false, 20470, 152919⟩,
  ⟨"g3_merge10_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge10_uarb1, false, 872297, 2044260, true, 174461, 408852⟩,
  ⟨"g3_merge11_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge11_uarb1, false, 397499, 726999, true, 530003, 969332⟩,
  ⟨"g3_merge11_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge11_uarb1, false, 1138231, 2882917, true, 1138244, 2882917⟩,
  ⟨"g3_merge11_uarb1.lit.mP", .lit, F_mP, v_g3_merge11_uarb1, false, 10946003, 12113443, true, 10946015, 12113443⟩,
  ⟨"g3_merge11_uarb1.lit.mG", .lit, F_mG, v_g3_merge11_uarb1, false, 2089173, 2518535, true, 10445877, 12592675⟩,
  ⟨"g3_merge11_uarb1.lit.mA", .lit, F_mA, v_g3_merge11_uarb1, false, 3903083, 4425083, true, 11709265, 13275249⟩,
  ⟨"g3_merge11_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge11_uarb1, false, 5413744, 6257289, true, 5413750, 6257289⟩,
  ⟨"g3_merge11_uarb1.lit.nP", .lit, F_nP, v_g3_merge11_uarb1, false, 5256443, 6273280, true, 5256449, 6273280⟩,
  ⟨"g3_merge11_uarb1.lit.nG", .lit, F_nG, v_g3_merge11_uarb1, false, 10466689, 12574377, true, 10466701, 12574377⟩,
  ⟨"g3_merge11_uarb1.lit.nA", .lit, F_nA, v_g3_merge11_uarb1, false, 11350197, 13342883, true, 11350213, 13342883⟩,
  ⟨"g3_merge11_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge11_uarb1, false, 21770689, 24200391, true, 21770713, 24200391⟩,
  ⟨"g3_merge11_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge11_uarb1, false, 39, 209, false, 10637, 57000⟩,
  ⟨"g3_merge11_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge11_uarb1, false, 115, 501, false, 115007, 501000⟩,
  ⟨"g3_merge11_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge11_uarb1, false, 11539723, 13157723, true, 11539738, 13157723⟩,
  ⟨"g3_merge11_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge11_uarb1, false, 11554723, 12780723, true, 11554738, 12780723⟩,
  ⟨"g3_merge11_uarb1.lit.h12", .lit, F_h12, v_g3_merge11_uarb1, false, 4659, 24884, true, 46591, 248840⟩,
  ⟨"g3_merge11_uarb1.lit.h21", .lit, F_h21, v_g3_merge11_uarb1, false, 4859, 20184, true, 16197, 67280⟩,
  ⟨"g3_merge11_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge11_uarb1, false, 392721, 1618720, true, 392729, 1618720⟩,
  ⟨"g3_merge11_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge11_uarb1, false, 122907, 662240, true, 368729, 1986720⟩,
  ⟨"g3_merge11_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge11_uarb1, false, 288499, 617999, true, 1154009, 2471996⟩,
  ⟨"g3_merge11_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge11_uarb1, false, 263077, 844639, true, 789244, 2533917⟩,
  ⟨"g3_merge11_uarb1.cons.mP", .cons, F_mP, v_g3_merge11_uarb1, false, 9095003, 10262443, true, 9095015, 10262443⟩,
  ⟨"g3_merge11_uarb1.cons.mG", .cons, F_mG, v_g3_merge11_uarb1, false, 1717873, 2147235, true, 8589377, 10736175⟩,
  ⟨"g3_merge11_uarb1.cons.mA", .cons, F_mA, v_g3_merge11_uarb1, false, 9671249, 11237249, true, 9671265, 11237249⟩,
  ⟨"g3_merge11_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge11_uarb1, false, 4469994, 5313539, true, 4470000, 5313539⟩,
  ⟨"g3_merge11_uarb1.cons.nP", .cons, F_nP, v_g3_merge11_uarb1, false, 4330943, 5347780, true, 4330949, 5347780⟩,
  ⟨"g3_merge11_uarb1.cons.nG", .cons, F_nG, v_g3_merge11_uarb1, false, 8608689, 10716377, true, 8608701, 10716377⟩,
  ⟨"g3_merge11_uarb1.cons.nA", .cons, F_nA, v_g3_merge11_uarb1, false, 9350197, 11342883, true, 9350213, 11342883⟩,
  ⟨"g3_merge11_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge11_uarb1, false, 18068689, 20498391, true, 110851, 125757⟩,
  ⟨"g3_merge11_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge11_uarb1, false, 9, 115, false, 54007, 690000⟩,
  ⟨"g3_merge11_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge11_uarb1, false, 17, 137, false, 68007, 548000⟩,
  ⟨"g3_merge11_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge11_uarb1, false, 9531723, 11149723, true, 9531738, 11149723⟩,
  ⟨"g3_merge11_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge11_uarb1, false, 9579723, 10805723, true, 9579738, 10805723⟩,
  ⟨"g3_merge11_uarb1.cons.h12", .cons, F_h12, v_g3_merge11_uarb1, false, 3843, 44293, true, 19216, 221465⟩,
  ⟨"g3_merge11_uarb1.cons.h21", .cons, F_h21, v_g3_merge11_uarb1, false, 5043, 35693, true, 25216, 178465⟩,
  ⟨"g3_merge11_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge11_uarb1, false, 207721, 1433720, true, 207729, 1433720⟩,
  ⟨"g3_merge11_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge11_uarb1, false, 147721, 1765720, true, 147729, 1765720⟩,
  ⟨"g3_merge12_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge12_uarb1, false, 803051, 1177145, true, 2409166, 3531435⟩,
  ⟨"g3_merge12_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge12_uarb1, false, 1615779, 2459779, true, 1615792, 2459779⟩,
  ⟨"g3_merge12_uarb1.lit.mP", .lit, F_mP, v_g3_merge12_uarb1, false, 646214, 1003389, false, 646220, 1003389⟩,
  ⟨"g3_merge12_uarb1.lit.mG", .lit, F_mG, v_g3_merge12_uarb1, false, 2889439, 5959019, true, 2889451, 5959019⟩,
  ⟨"g3_merge12_uarb1.lit.mA", .lit, F_mA, v_g3_merge12_uarb1, false, 4962573, 6332855, true, 4962589, 6332855⟩,
  ⟨"g3_merge12_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge12_uarb1, false, 7019023, 11369833, true, 7019047, 11369833⟩,
  ⟨"g3_merge12_uarb1.lit.nP", .lit, F_nP, v_g3_merge12_uarb1, false, 1498903, 1800303, false, 1498915, 1800303⟩,
  ⟨"g3_merge12_uarb1.lit.nG", .lit, F_nG, v_g3_merge12_uarb1, false, 2276967, 3748249, true, 2276975, 3748249⟩,
  ⟨"g3_merge12_uarb1.lit.nA", .lit, F_nA, v_g3_merge12_uarb1, false, 215173, 267173, true, 4518649, 5610633⟩,
  ⟨"g3_merge12_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge12_uarb1, false, 7017631, 10862077, true, 7017655, 10862077⟩,
  ⟨"g3_merge12_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge12_uarb1, false, 67250, 262241, true, 538007, 2097928⟩,
  R_g3_merge12_uarb1_lit_rt1b,
  ⟨"g3_merge12_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge12_uarb1, false, 4469603, 6029531, true, 4469618, 6029531⟩,
  ⟨"g3_merge12_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge12_uarb1, false, 4110777, 6315149, true, 4110792, 6315149⟩,
  ⟨"g3_merge12_uarb1.lit.h12", .lit, F_h12, v_g3_merge12_uarb1, false, 119963, 379951, true, 359893, 1139853⟩,
  ⟨"g3_merge12_uarb1.lit.h21", .lit, F_h21, v_g3_merge12_uarb1, false, 29238, 208331, false, 29240, 208331⟩,
  ⟨"g3_merge12_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge12_uarb1, false, 113953, 830324, false, 113961, 830324⟩,
  ⟨"g3_merge12_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge12_uarb1, false, 715779, 2275706, true, 37673, 119774⟩,
  ⟨"g3_merge12_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge12_uarb1, false, 90293, 143735, true, 1896166, 3018435⟩,
  ⟨"g3_merge12_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge12_uarb1, false, 1253779, 2097779, true, 1253792, 2097779⟩,
  ⟨"g3_merge12_uarb1.cons.mP", .cons, F_mP, v_g3_merge12_uarb1, false, 606214, 1043389, false, 606220, 1043389⟩,
  ⟨"g3_merge12_uarb1.cons.mG", .cons, F_mG, v_g3_merge12_uarb1, false, 2056939, 5126519, true, 2056951, 5126519⟩,
  ⟨"g3_merge12_uarb1.cons.mA", .cons, F_mA, v_g3_merge12_uarb1, false, 3924573, 5294855, true, 3924589, 5294855⟩,
  ⟨"g3_merge12_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge12_uarb1, false, 5300023, 9650833, true, 5300047, 9650833⟩,
  ⟨"g3_merge12_uarb1.cons.nP", .cons, F_nP, v_g3_merge12_uarb1, false, 1469903, 1829303, false, 1469915, 1829303⟩,
  ⟨"g3_merge12_uarb1.cons.nG", .cons, F_nG, v_g3_merge12_uarb1, false, 1715967, 3187249, true, 1715975, 3187249⟩,
  ⟨"g3_merge12_uarb1.cons.nA", .cons, F_nA, v_g3_merge12_uarb1, false, 3562633, 4654633, true, 3562649, 4654633⟩,
  ⟨"g3_merge12_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge12_uarb1, false, 5340631, 9185077, true, 5340655, 9185077⟩,
  ⟨"g3_merge12_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge12_uarb1, false, 36125, 231116, true, 289007, 1848928⟩,
  R_g3_merge12_uarb1_cons_rt1b,
  ⟨"g3_merge12_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge12_uarb1, false, 1165201, 1685177, true, 1165206, 1685177⟩,
  ⟨"g3_merge12_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge12_uarb1, false, 3146777, 5351149, true, 3146792, 5351149⟩,
  ⟨"g3_merge12_uarb1.cons.h12", .cons, F_h12, v_g3_merge12_uarb1, false, 224389, 1004353, true, 224393, 1004353⟩,
  ⟨"g3_merge12_uarb1.cons.h21", .cons, F_h21, v_g3_merge12_uarb1, false, 9238, 228331, false, 9240, 228331⟩,
  ⟨"g3_merge12_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge12_uarb1, false, 33953, 910324, false, 33961, 910324⟩,
  ⟨"g3_merge12_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge12_uarb1, false, 442779, 2002706, true, 442787, 2002706⟩,
  ⟨"g3_merge12_uarb2.lit.fork1", .lit, F_fork1, v_g3_merge12_uarb2, false, 269319, 528254, false, 538651, 1056508⟩,
  ⟨"g3_merge12_uarb2.lit.fork2", .lit, F_fork2, v_g3_merge12_uarb2, false, 427847, 1392925, false, 85572, 278585⟩,
  ⟨"g3_merge12_uarb2.lit.mP", .lit, F_mP, v_g3_merge12_uarb2, false, 3760179, 4921679, true, 3760191, 4921679⟩,
  ⟨"g3_merge12_uarb2.lit.mG", .lit, F_mG, v_g3_merge12_uarb2, false, 6890845, 12147591, true, 6890869, 12147591⟩,
  ⟨"g3_merge12_uarb2.lit.mA", .lit, F_mA, v_g3_merge12_uarb2, false, 1592511, 2131801, true, 682507, 913629⟩,
  ⟨"g3_merge12_uarb2.lit.mGG", .lit, F_mGG, v_g3_merge12_uarb2, false, 7908199, 12251445, true, 7908223, 12251445⟩,
  ⟨"g3_merge12_uarb2.lit.nP", .lit, F_nP, v_g3_merge12_uarb2, false, 3786719, 4895139, true, 3786731, 4895139⟩,
  ⟨"g3_merge12_uarb2.lit.nG", .lit, F_nG, v_g3_merge12_uarb2, false, 6933801, 12414179, true, 6933825, 12414179⟩,
  ⟨"g3_merge12_uarb2.lit.nA", .lit, F_nA, v_g3_merge12_uarb2, false, 1536325, 2591403, false, 1536341, 2591403⟩,
  ⟨"g3_merge12_uarb2.lit.nGG", .lit, F_nGG, v_g3_merge12_uarb2, false, 2350469, 3890455, true, 2350477, 3890455⟩,
  ⟨"g3_merge12_uarb2.lit.rt1", .lit, F_rt1, v_g3_merge12_uarb2, false, 806375, 2401217, true, 806382, 2401217⟩,
  ⟨"g3_merge12_uarb2.lit.rt1b", .lit, F_rt1b, v_g3_merge12_uarb2, false, 14750, 91741, false, 118007, 733928⟩,
  ⟨"g3_merge12_uarb2.lit.rt1s", .lit, F_rt1s, v_g3_merge12_uarb2, false, 2388652, 3186073, true, 4777319, 6372146⟩,
  ⟨"g3_merge12_uarb2.lit.rt1bs", .lit, F_rt1bs, v_g3_merge12_uarb2, false, 4370929, 6206857, true, 4370944, 6206857⟩,
  ⟨"g3_merge12_uarb2.lit.h12", .lit, F_h12, v_g3_merge12_uarb2, false, 398891, 1196312, true, 398895, 1196312⟩,
  ⟨"g3_merge12_uarb2.lit.h21", .lit, F_h21, v_g3_merge12_uarb2, false, 130469, 742445, true, 78283, 445467⟩,
  ⟨"g3_merge12_uarb2.lit.o1x", .lit, F_o1x, v_g3_merge12_uarb2, false, 395408, 2231335, true, 395416, 2231335⟩,
  ⟨"g3_merge12_uarb2.lit.o2x", .lit, F_o2x, v_g3_merge12_uarb2, false, 793783, 2388624, true, 264597, 796208⟩,
  ⟨"g3_merge12_uarb2.cons.fork1", .cons, F_fork1, v_g3_merge12_uarb2, false, 246819, 550754, false, 493651, 1101508⟩,
  ⟨"g3_merge12_uarb2.cons.fork2", .cons, F_fork2, v_g3_merge12_uarb2, false, 117949, 488975, false, 70772, 293385⟩,
  ⟨"g3_merge12_uarb2.cons.mP", .cons, F_mP, v_g3_merge12_uarb2, false, 3027179, 4188679, true, 3027191, 4188679⟩,
  ⟨"g3_merge12_uarb2.cons.mG", .cons, F_mG, v_g3_merge12_uarb2, false, 5284845, 10541591, true, 5284869, 10541591⟩,
  ⟨"g3_merge12_uarb2.cons.mA", .cons, F_mA, v_g3_merge12_uarb2, false, 3842533, 5460403, true, 3842549, 5460403⟩,
  ⟨"g3_merge12_uarb2.cons.mGG", .cons, F_mGG, v_g3_merge12_uarb2, false, 6215199, 10558445, true, 6215223, 10558445⟩,
  ⟨"g3_merge12_uarb2.cons.nP", .cons, F_nP, v_g3_merge12_uarb2, false, 3053719, 4162139, true, 3053731, 4162139⟩,
  ⟨"g3_merge12_uarb2.cons.nG", .cons, F_nG, v_g3_merge12_uarb2, false, 5305801, 10786179, true, 5305825, 10786179⟩,
  ⟨"g3_merge12_uarb2.cons.nA", .cons, F_nA, v_g3_merge12_uarb2, false, 1451325, 2676403, false, 1451341, 2676403⟩,
  ⟨"g3_merge12_uarb2.cons.nGG", .cons, F_nGG, v_g3_merge12_uarb2, false, 5462407, 10082365, true, 5462431, 10082365⟩,
  ⟨"g3_merge12_uarb2.cons.rt1", .cons, F_rt1, v_g3_merge12_uarb2, false, 515375, 2110217, true, 515382, 2110217⟩,
  ⟨"g3_merge12_uarb2.cons.rt1b", .cons, F_rt1b, v_g3_merge12_uarb2, false, 5750, 100741, false, 46007, 805928⟩,
  ⟨"g3_merge12_uarb2.cons.rt1s", .cons, F_rt1s, v_g3_merge12_uarb2, false, 637384, 903191, true, 1274773, 1806382⟩,
  ⟨"g3_merge12_uarb2.cons.rt1bs", .cons, F_rt1bs, v_g3_merge12_uarb2, false, 3456929, 5292857, true, 3456944, 5292857⟩,
  ⟨"g3_merge12_uarb2.cons.h12", .cons, F_h12, v_g3_merge12_uarb2, false, 257891, 1055312, true, 257895, 1055312⟩,
  ⟨"g3_merge12_uarb2.cons.h21", .cons, F_h21, v_g3_merge12_uarb2, false, 149407, 1985335, true, 29883, 397067⟩,
  ⟨"g3_merge12_uarb2.cons.o1x", .cons, F_o1x, v_g3_merge12_uarb2, false, 155408, 1991335, true, 155416, 1991335⟩,
  ⟨"g3_merge12_uarb2.cons.o2x", .cons, F_o2x, v_g3_merge12_uarb2, false, 509783, 2104624, true, 509791, 2104624⟩,
  ⟨"g3_merge2_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge2_uarb1, false, 897669, 1997990, true, 1795351, 3995980⟩,
  ⟨"g3_merge2_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge2_uarb1, false, 328319, 592319, true, 1641608, 2961595⟩,
  ⟨"g3_merge2_uarb1.lit.mP", .lit, F_mP, v_g3_merge2_uarb1, false, 4292875, 4705599, true, 4292881, 4705599⟩,
  ⟨"g3_merge2_uarb1.lit.mG", .lit, F_mG, v_g3_merge2_uarb1, false, 15792225, 19936921, true, 15792249, 19936921⟩,
  ⟨"g3_merge2_uarb1.lit.mA", .lit, F_mA, v_g3_merge2_uarb1, false, 2973909, 3790123, true, 8921743, 11370369⟩,
  ⟨"g3_merge2_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge2_uarb1, false, 8064101, 9847725, true, 8064113, 9847725⟩,
  ⟨"g3_merge2_uarb1.lit.nP", .lit, F_nP, v_g3_merge2_uarb1, false, 4295447, 4703027, true, 4295453, 4703027⟩,
  ⟨"g3_merge2_uarb1.lit.nG", .lit, F_nG, v_g3_merge2_uarb1, false, 15929925, 19143013, true, 15929949, 19143013⟩,
  ⟨"g3_merge2_uarb1.lit.nA", .lit, F_nA, v_g3_merge2_uarb1, false, 9075221, 10643221, true, 9075237, 10643221⟩,
  ⟨"g3_merge2_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge2_uarb1, false, 4103563, 4765045, true, 4103569, 4765045⟩,
  ⟨"g3_merge2_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge2_uarb1, false, 169169, 568795, false, 169176, 568795⟩,
  ⟨"g3_merge2_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge2_uarb1, false, 91491, 222134, false, 182989, 444268⟩,
  ⟨"g3_merge2_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge2_uarb1, false, 8972813, 10268439, true, 8972828, 10268439⟩,
  ⟨"g3_merge2_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge2_uarb1, false, 4504813, 4893456, true, 9009641, 9786912⟩,
  ⟨"g3_merge2_uarb1.lit.h12", .lit, F_h12, v_g3_merge2_uarb1, false, 270918, 918731, true, 270922, 918731⟩,
  ⟨"g3_merge2_uarb1.lit.h21", .lit, F_h21, v_g3_merge2_uarb1, false, 201649, 462935, false, 201657, 462935⟩,
  ⟨"g3_merge2_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge2_uarb1, false, 116530, 271987, true, 582658, 1359935⟩,
  ⟨"g3_merge2_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge2_uarb1, false, 190279, 622154, true, 570845, 1866462⟩,
  ⟨"g3_merge2_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge2_uarb1, false, 629669, 1729990, true, 1259351, 3459980⟩,
  ⟨"g3_merge2_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge2_uarb1, false, 81573, 169573, true, 1223608, 2543595⟩,
  ⟨"g3_merge2_uarb1.cons.mP", .cons, F_mP, v_g3_merge2_uarb1, false, 3460875, 3873599, true, 3460881, 3873599⟩,
  ⟨"g3_merge2_uarb1.cons.mG", .cons, F_mG, v_g3_merge2_uarb1, false, 12479225, 16623921, true, 12479249, 16623921⟩,
  ⟨"g3_merge2_uarb1.cons.mA", .cons, F_mA, v_g3_merge2_uarb1, false, 7054727, 9503369, true, 7054743, 9503369⟩,
  ⟨"g3_merge2_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge2_uarb1, false, 6403101, 8186725, true, 6403113, 8186725⟩,
  ⟨"g3_merge2_uarb1.cons.nP", .cons, F_nP, v_g3_merge2_uarb1, false, 3463447, 3871027, true, 3463453, 3871027⟩,
  ⟨"g3_merge2_uarb1.cons.nG", .cons, F_nG, v_g3_merge2_uarb1, false, 12683925, 15897013, true, 12683949, 15897013⟩,
  ⟨"g3_merge2_uarb1.cons.nA", .cons, F_nA, v_g3_merge2_uarb1, false, 7247221, 8815221, true, 7247237, 8815221⟩,
  ⟨"g3_merge2_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge2_uarb1, false, 3282313, 3943795, true, 3282319, 3943795⟩,
  ⟨"g3_merge2_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge2_uarb1, false, 321169, 1616795, true, 321176, 1616795⟩,
  ⟨"g3_merge2_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge2_uarb1, false, 76991, 236634, false, 153989, 473268⟩,
  ⟨"g3_merge2_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge2_uarb1, false, 7191813, 8487439, true, 7191828, 8487439⟩,
  ⟨"g3_merge2_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge2_uarb1, false, 3635813, 4024456, true, 7271641, 8048912⟩,
  ⟨"g3_merge2_uarb1.cons.h12", .cons, F_h12, v_g3_merge2_uarb1, false, 161418, 809231, true, 161422, 809231⟩,
  ⟨"g3_merge2_uarb1.cons.h21", .cons, F_h21, v_g3_merge2_uarb1, false, 172649, 491935, false, 172657, 491935⟩,
  ⟨"g3_merge2_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge2_uarb1, false, 81730, 237187, true, 408658, 1185935⟩,
  ⟨"g3_merge2_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge2_uarb1, false, 114279, 546154, true, 342845, 1638462⟩,
  ⟨"g3_merge3_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge3_uarb1, false, 582637, 1069637, true, 1165287, 2139274⟩,
  ⟨"g3_merge3_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge3_uarb1, false, 196309, 416309, true, 61993, 131466⟩,
  ⟨"g3_merge3_uarb1.lit.mP", .lit, F_mP, v_g3_merge3_uarb1, false, 3165163, 3734013, true, 3165169, 3734013⟩,
  ⟨"g3_merge3_uarb1.lit.mG", .lit, F_mG, v_g3_merge3_uarb1, false, 12181549, 15937429, true, 12181573, 15937429⟩,
  ⟨"g3_merge3_uarb1.lit.mA", .lit, F_mA, v_g3_merge3_uarb1, false, 442011, 518386, true, 221006, 259193⟩,
  ⟨"g3_merge3_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge3_uarb1, false, 12923399, 15789579, true, 145207, 177411⟩,
  ⟨"g3_merge3_uarb1.lit.nP", .lit, F_nP, v_g3_merge3_uarb1, false, 797911, 914873, false, 797915, 914873⟩,
  ⟨"g3_merge3_uarb1.lit.nG", .lit, F_nG, v_g3_merge3_uarb1, false, 6260764, 7989877, true, 6260776, 7989877⟩,
  ⟨"g3_merge3_uarb1.lit.nA", .lit, F_nA, v_g3_merge3_uarb1, false, 210193, 259193, true, 38217, 47126⟩,
  ⟨"g3_merge3_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge3_uarb1, false, 12782971, 15620311, true, 12782995, 15620311⟩,
  ⟨"g3_merge3_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge3_uarb1, false, 126491, 530991, true, 56219, 235996⟩,
  ⟨"g3_merge3_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge3_uarb1, false, 179029, 485529, true, 716123, 1942116⟩,
  ⟨"g3_merge3_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge3_uarb1, false, 7020497, 8638497, true, 7020512, 8638497⟩,
  ⟨"g3_merge3_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge3_uarb1, false, 7230649, 8456649, true, 7230664, 8456649⟩,
  ⟨"g3_merge3_uarb1.lit.h12", .lit, F_h12, v_g3_merge3_uarb1, false, 497371, 2115371, true, 497379, 2115371⟩,
  ⟨"g3_merge3_uarb1.lit.h21", .lit, F_h21, v_g3_merge3_uarb1, false, 707523, 1933523, true, 707531, 1933523⟩,
  ⟨"g3_merge3_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge3_uarb1, false, 711524, 1937523, true, 711532, 1937523⟩,
  ⟨"g3_merge3_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge3_uarb1, false, 493372, 2111371, true, 493380, 2111371⟩,
  ⟨"g3_merge3_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge3_uarb1, false, 421137, 908137, true, 842287, 1816274⟩,
  ⟨"g3_merge3_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge3_uarb1, false, 141309, 361309, true, 847867, 2167854⟩,
  ⟨"g3_merge3_uarb1.cons.mP", .cons, F_mP, v_g3_merge3_uarb1, false, 2521663, 3090513, true, 2521669, 3090513⟩,
  ⟨"g3_merge3_uarb1.cons.mG", .cons, F_mG, v_g3_merge3_uarb1, false, 9545549, 13301429, true, 9545573, 13301429⟩,
  ⟨"g3_merge3_uarb1.cons.mA", .cons, F_mA, v_g3_merge3_uarb1, false, 27097, 32972, true, 176131, 214318⟩,
  ⟨"g3_merge3_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge3_uarb1, false, 10230399, 13096579, true, 10230423, 13096579⟩,
  ⟨"g3_merge3_uarb1.cons.nP", .cons, F_nP, v_g3_merge3_uarb1, false, 2364733, 2773619, false, 2364745, 2773619⟩,
  ⟨"g3_merge3_uarb1.cons.nG", .cons, F_nG, v_g3_merge3_uarb1, false, 1641588, 2217959, true, 1641592, 2217959⟩,
  ⟨"g3_merge3_uarb1.cons.nA", .cons, F_nA, v_g3_merge3_uarb1, false, 665397, 861397, true, 665399, 861397⟩,
  ⟨"g3_merge3_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge3_uarb1, false, 10119971, 12957311, true, 10119995, 12957311⟩,
  ⟨"g3_merge3_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge3_uarb1, false, 64491, 468991, true, 257971, 1875964⟩,
  ⟨"g3_merge3_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge3_uarb1, false, 115779, 422279, true, 463123, 1689116⟩,
  ⟨"g3_merge3_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge3_uarb1, false, 5556497, 7174497, true, 5556512, 7174497⟩,
  ⟨"g3_merge3_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge3_uarb1, false, 5761649, 6987649, true, 5761664, 6987649⟩,
  ⟨"g3_merge3_uarb1.cons.h12", .cons, F_h12, v_g3_merge3_uarb1, false, 258371, 1876371, true, 258379, 1876371⟩,
  ⟨"g3_merge3_uarb1.cons.h21", .cons, F_h21, v_g3_merge3_uarb1, false, 464523, 1690523, true, 20197, 73501⟩,
  ⟨"g3_merge3_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge3_uarb1, false, 470524, 1696523, true, 470532, 1696523⟩,
  ⟨"g3_merge3_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge3_uarb1, false, 84124, 623457, true, 252380, 1870371⟩,
  ⟨"g3_merge4_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge4_uarb1, false, 1054587, 1713587, true, 2109187, 3427174⟩,
  ⟨"g3_merge4_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge4_uarb1, false, 139018, 288445, true, 2224301, 4615120⟩,
  ⟨"g3_merge4_uarb1.lit.mP", .lit, F_mP, v_g3_merge4_uarb1, false, 3726659, 4299519, true, 3726665, 4299519⟩,
  ⟨"g3_merge4_uarb1.lit.mG", .lit, F_mG, v_g3_merge4_uarb1, false, 7159391, 9465797, true, 7159403, 9465797⟩,
  ⟨"g3_merge4_uarb1.lit.mA", .lit, F_mA, v_g3_merge4_uarb1, false, 177769, 212569, true, 1142803, 1366515⟩,
  ⟨"g3_merge4_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge4_uarb1, false, 4955023, 6193387, true, 4955031, 6193387⟩,
  ⟨"g3_merge4_uarb1.lit.nP", .lit, F_nP, v_g3_merge4_uarb1, false, 3810271, 4215907, true, 3810277, 4215907⟩,
  ⟨"g3_merge4_uarb1.lit.nG", .lit, F_nG, v_g3_merge4_uarb1, false, 2663039, 3609681, false, 2663051, 3609681⟩,
  ⟨"g3_merge4_uarb1.lit.nA", .lit, F_nA, v_g3_merge4_uarb1, false, 1150393, 1527369, true, 8052767, 10691583⟩,
  ⟨"g3_merge4_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge4_uarb1, false, 5542287, 7230299, false, 5542311, 7230299⟩,
  ⟨"g3_merge4_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge4_uarb1, false, 203730, 467693, false, 407467, 935386⟩,
  ⟨"g3_merge4_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge4_uarb1, false, 135323, 478205, false, 270653, 956410⟩,
  ⟨"g3_merge4_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge4_uarb1, false, 4472319, 5186282, true, 8944653, 10372564⟩,
  ⟨"g3_merge4_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge4_uarb1, false, 271402, 328549, false, 1085613, 1314196⟩,
  ⟨"g3_merge4_uarb1.lit.h12", .lit, F_h12, v_g3_merge4_uarb1, false, 432087, 960013, false, 432095, 960013⟩,
  ⟨"g3_merge4_uarb1.lit.h21", .lit, F_h21, v_g3_merge4_uarb1, false, 293273, 979037, false, 293281, 979037⟩,
  ⟨"g3_merge4_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge4_uarb1, false, 295274, 981037, false, 295282, 981037⟩,
  ⟨"g3_merge4_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge4_uarb1, false, 430088, 958013, false, 430096, 958013⟩,
  ⟨"g3_merge4_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge4_uarb1, false, 786587, 1445587, true, 143017, 262834⟩,
  ⟨"g3_merge4_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge4_uarb1, false, 104018, 253445, true, 1664301, 4055120⟩,
  ⟨"g3_merge4_uarb1.cons.mP", .cons, F_mP, v_g3_merge4_uarb1, false, 3032659, 3605519, true, 3032665, 3605519⟩,
  ⟨"g3_merge4_uarb1.cons.mG", .cons, F_mG, v_g3_merge4_uarb1, false, 5716891, 8023297, true, 248561, 348839⟩,
  ⟨"g3_merge4_uarb1.cons.mA", .cons, F_mA, v_g3_merge4_uarb1, false, 1289921, 1603121, true, 6449621, 8015605⟩,
  ⟨"g3_merge4_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge4_uarb1, false, 3981023, 5219387, true, 3981031, 5219387⟩,
  ⟨"g3_merge4_uarb1.cons.nP", .cons, F_nP, v_g3_merge4_uarb1, false, 1038757, 1173969, true, 346253, 391323⟩,
  ⟨"g3_merge4_uarb1.cons.nG", .cons, F_nG, v_g3_merge4_uarb1, false, 616171, 881909, true, 1848517, 2645727⟩,
  ⟨"g3_merge4_uarb1.cons.nA", .cons, F_nA, v_g3_merge4_uarb1, false, 6444751, 9083583, true, 6444767, 9083583⟩,
  ⟨"g3_merge4_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge4_uarb1, false, 11512287, 15732299, true, 11512311, 15732299⟩,
  ⟨"g3_merge4_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge4_uarb1, false, 175730, 495693, false, 351467, 991386⟩,
  ⟨"g3_merge4_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge4_uarb1, false, 108323, 505205, false, 216653, 1010410⟩,
  ⟨"g3_merge4_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge4_uarb1, false, 3627319, 4341282, true, 7254653, 8682564⟩,
  ⟨"g3_merge4_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge4_uarb1, false, 266902, 333049, false, 1067613, 1332196⟩,
  ⟨"g3_merge4_uarb1.cons.h12", .cons, F_h12, v_g3_merge4_uarb1, false, 376087, 1016013, false, 125365, 338671⟩,
  ⟨"g3_merge4_uarb1.cons.h21", .cons, F_h21, v_g3_merge4_uarb1, false, 239273, 1033037, false, 239281, 1033037⟩,
  ⟨"g3_merge4_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge4_uarb1, false, 241274, 1035037, false, 241282, 1035037⟩,
  ⟨"g3_merge4_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge4_uarb1, false, 2616, 7091, false, 374096, 1014013⟩,
  ⟨"g3_merge6_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge6_uarb1, false, 828973, 1315973, true, 1657959, 2631946⟩,
  ⟨"g3_merge6_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge6_uarb1, false, 1675319, 3321433, true, 1675332, 3321433⟩,
  ⟨"g3_merge6_uarb1.lit.mP", .lit, F_mP, v_g3_merge6_uarb1, false, 3428559, 3995293, true, 3428565, 3995293⟩,
  ⟨"g3_merge6_uarb1.lit.mG", .lit, F_mG, v_g3_merge6_uarb1, false, 12609847, 15785777, true, 12609871, 15785777⟩,
  ⟨"g3_merge6_uarb1.lit.mA", .lit, F_mA, v_g3_merge6_uarb1, false, 7321913, 8543913, true, 2440643, 2847971⟩,
  ⟨"g3_merge6_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge6_uarb1, false, 6537321, 7682552, true, 152031, 178664⟩,
  ⟨"g3_merge6_uarb1.lit.nP", .lit, F_nP, v_g3_merge6_uarb1, false, 14911, 16546, true, 1759501, 1952428⟩,
  ⟨"g3_merge6_uarb1.lit.nG", .lit, F_nG, v_g3_merge6_uarb1, false, 12960525, 15849293, true, 12960549, 15849293⟩,
  ⟨"g3_merge6_uarb1.lit.nA", .lit, F_nA, v_g3_merge6_uarb1, false, 7525791, 9419905, true, 7525807, 9419905⟩,
  ⟨"g3_merge6_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge6_uarb1, false, 3362081, 3953343, true, 3362087, 3953343⟩,
  ⟨"g3_merge6_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge6_uarb1, false, 763823, 1806105, true, 50922, 120407⟩,
  ⟨"g3_merge6_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge6_uarb1, false, 1011, 2237, true, 1011007, 2237000⟩,
  ⟨"g3_merge6_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge6_uarb1, false, 7380675, 8422957, true, 7380690, 8422957⟩,
  ⟨"g3_merge6_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge6_uarb1, false, 1906963, 2213463, true, 7627867, 8853852⟩,
  ⟨"g3_merge6_uarb1.lit.h12", .lit, F_h12, v_g3_merge6_uarb1, false, 980679, 2022961, true, 980687, 2022961⟩,
  ⟨"g3_merge6_uarb1.lit.h21", .lit, F_h21, v_g3_merge6_uarb1, false, 148857, 302107, true, 148858, 302107⟩,
  ⟨"g3_merge6_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge6_uarb1, false, 1160857, 2386856, true, 1160865, 2386856⟩,
  ⟨"g3_merge6_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge6_uarb1, false, 1010680, 2052961, true, 1010688, 2052961⟩,
  ⟨"g3_merge6_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge6_uarb1, false, 618973, 1105973, true, 1237959, 2211946⟩,
  ⟨"g3_merge6_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge6_uarb1, false, 1203319, 2849433, true, 1203332, 2849433⟩,
  ⟨"g3_merge6_uarb1.cons.mP", .cons, F_mP, v_g3_merge6_uarb1, false, 393437, 474399, true, 2754065, 3320793⟩,
  ⟨"g3_merge6_uarb1.cons.mG", .cons, F_mG, v_g3_merge6_uarb1, false, 10037847, 13213777, true, 590463, 777281⟩,
  ⟨"g3_merge6_uarb1.cons.mA", .cons, F_mA, v_g3_merge6_uarb1, false, 5897913, 7119913, true, 5897929, 7119913⟩,
  ⟨"g3_merge6_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge6_uarb1, false, 5259821, 6405052, true, 5259833, 6405052⟩,
  ⟨"g3_merge6_uarb1.cons.nP", .cons, F_nP, v_g3_merge6_uarb1, false, 711124, 807589, true, 1422251, 1615178⟩,
  ⟨"g3_merge6_uarb1.cons.nG", .cons, F_nG, v_g3_merge6_uarb1, false, 10362525, 13251293, true, 10362549, 13251293⟩,
  ⟨"g3_merge6_uarb1.cons.nA", .cons, F_nA, v_g3_merge6_uarb1, false, 5964791, 7858905, true, 1988269, 2619635⟩,
  ⟨"g3_merge6_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge6_uarb1, false, 2696331, 3287593, true, 2696337, 3287593⟩,
  ⟨"g3_merge6_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge6_uarb1, false, 522823, 1565105, true, 104566, 313021⟩,
  ⟨"g3_merge6_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge6_uarb1, false, 347, 960, true, 694007, 1920000⟩,
  ⟨"g3_merge6_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge6_uarb1, false, 5952675, 6994957, true, 5952690, 6994957⟩,
  ⟨"g3_merge6_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge6_uarb1, false, 1530963, 1837463, true, 6123867, 7349852⟩,
  ⟨"g3_merge6_uarb1.cons.h12", .cons, F_h12, v_g3_merge6_uarb1, false, 710679, 1752961, true, 710687, 1752961⟩,
  ⟨"g3_merge6_uarb1.cons.h21", .cons, F_h21, v_g3_merge6_uarb1, false, 53366, 129991, true, 106733, 259982⟩,
  ⟨"g3_merge6_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge6_uarb1, false, 832857, 2058856, true, 832865, 2058856⟩,
  ⟨"g3_merge6_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge6_uarb1, false, 731680, 1773961, true, 731688, 1773961⟩,
  ⟨"g3_merge9_uarb1.lit.fork1", .lit, F_fork1, v_g3_merge9_uarb1, false, 877934, 1530255, true, 1755881, 3060510⟩,
  ⟨"g3_merge9_uarb1.lit.fork2", .lit, F_fork2, v_g3_merge9_uarb1, false, 2164735, 3250641, true, 2164748, 3250641⟩,
  ⟨"g3_merge9_uarb1.lit.mP", .lit, F_mP, v_g3_merge9_uarb1, false, 9575857, 11678317, true, 9575869, 11678317⟩,
  ⟨"g3_merge9_uarb1.lit.mG", .lit, F_mG, v_g3_merge9_uarb1, false, 9058529, 11779404, true, 9058541, 11779404⟩,
  ⟨"g3_merge9_uarb1.lit.mA", .lit, F_mA, v_g3_merge9_uarb1, false, 10178435, 11731077, true, 1130939, 1303453⟩,
  ⟨"g3_merge9_uarb1.lit.mGG", .lit, F_mGG, v_g3_merge9_uarb1, false, 9359818, 11153463, true, 9359830, 11153463⟩,
  ⟨"g3_merge9_uarb1.lit.nP", .lit, F_nP, v_g3_merge9_uarb1, false, 4797916, 5829171, true, 4797922, 5829171⟩,
  ⟨"g3_merge9_uarb1.lit.nG", .lit, F_nG, v_g3_merge9_uarb1, false, 17437453, 22674503, true, 17437477, 22674503⟩,
  ⟨"g3_merge9_uarb1.lit.nA", .lit, F_nA, v_g3_merge9_uarb1, false, 11075739, 12409645, true, 2215151, 2481929⟩,
  ⟨"g3_merge9_uarb1.lit.nGG", .lit, F_nGG, v_g3_merge9_uarb1, false, 85988, 101545, true, 4729346, 5584975⟩,
  ⟨"g3_merge9_uarb1.lit.rt1", .lit, F_rt1, v_g3_merge9_uarb1, false, 617981, 2335465, true, 617988, 2335465⟩,
  ⟨"g3_merge9_uarb1.lit.rt1b", .lit, F_rt1b, v_g3_merge9_uarb1, false, 30567, 162643, false, 122275, 650572⟩,
  ⟨"g3_merge9_uarb1.lit.rt1s", .lit, F_rt1s, v_g3_merge9_uarb1, false, 73871, 86227, true, 10268084, 11985553⟩,
  ⟨"g3_merge9_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g3_merge9_uarb1, false, 2508839, 2902415, true, 50429, 58340⟩,
  ⟨"g3_merge9_uarb1.lit.h12", .lit, F_h12, v_g3_merge9_uarb1, false, 305669, 1164411, true, 101891, 388137⟩,
  ⟨"g3_merge9_uarb1.lit.h21", .lit, F_h21, v_g3_merge9_uarb1, false, 411625, 1985929, true, 411633, 1985929⟩,
  ⟨"g3_merge9_uarb1.lit.o1x", .lit, F_o1x, v_g3_merge9_uarb1, false, 382626, 1956929, true, 382634, 1956929⟩,
  ⟨"g3_merge9_uarb1.lit.o2x", .lit, F_o2x, v_g3_merge9_uarb1, false, 640339, 2357822, true, 640347, 2357822⟩,
  ⟨"g3_merge9_uarb1.cons.fork1", .cons, F_fork1, v_g3_merge9_uarb1, false, 647434, 1299755, true, 1294881, 2599510⟩,
  ⟨"g3_merge9_uarb1.cons.fork2", .cons, F_fork2, v_g3_merge9_uarb1, false, 1688735, 2774641, true, 1688748, 2774641⟩,
  ⟨"g3_merge9_uarb1.cons.mP", .cons, F_mP, v_g3_merge9_uarb1, false, 7788857, 9891317, true, 7788869, 9891317⟩,
  ⟨"g3_merge9_uarb1.cons.mG", .cons, F_mG, v_g3_merge9_uarb1, false, 7306529, 10027404, true, 7306541, 10027404⟩,
  ⟨"g3_merge9_uarb1.cons.mA", .cons, F_mA, v_g3_merge9_uarb1, false, 640495, 759929, true, 8326451, 9879077⟩,
  ⟨"g3_merge9_uarb1.cons.mGG", .cons, F_mGG, v_g3_merge9_uarb1, false, 7636318, 9429963, true, 7636330, 9429963⟩,
  ⟨"g3_merge9_uarb1.cons.nP", .cons, F_nP, v_g3_merge9_uarb1, false, 3904416, 4935671, true, 3904422, 4935671⟩,
  ⟨"g3_merge9_uarb1.cons.nG", .cons, F_nG, v_g3_merge9_uarb1, false, 14076453, 19313503, true, 14076477, 19313503⟩,
  ⟨"g3_merge9_uarb1.cons.nA", .cons, F_nA, v_g3_merge9_uarb1, false, 9089739, 10423645, true, 1817951, 2084729⟩,
  ⟨"g3_merge9_uarb1.cons.nGG", .cons, F_nGG, v_g3_merge9_uarb1, false, 772568, 943695, true, 3862846, 4718475⟩,
  ⟨"g3_merge9_uarb1.cons.rt1", .cons, F_rt1, v_g3_merge9_uarb1, false, 347981, 2065465, true, 347988, 2065465⟩,
  ⟨"g3_merge9_uarb1.cons.rt1b", .cons, F_rt1b, v_g3_merge9_uarb1, false, 15067, 178143, false, 60275, 712572⟩,
  ⟨"g3_merge9_uarb1.cons.rt1s", .cons, F_rt1s, v_g3_merge9_uarb1, false, 8388069, 10105553, true, 8388084, 10105553⟩,
  ⟨"g3_merge9_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g3_merge9_uarb1, false, 2052089, 2445665, true, 8208371, 9782660⟩,
  ⟨"g3_merge9_uarb1.cons.h12", .cons, F_h12, v_g3_merge9_uarb1, false, 175169, 1033911, true, 58391, 344637⟩,
  ⟨"g3_merge9_uarb1.cons.h21", .cons, F_h21, v_g3_merge9_uarb1, false, 79625, 731929, false, 79633, 731929⟩,
  ⟨"g3_merge9_uarb1.cons.o1x", .cons, F_o1x, v_g3_merge9_uarb1, false, 176626, 1750929, true, 58878, 583643⟩,
  ⟨"g3_merge9_uarb1.cons.o2x", .cons, F_o2x, v_g3_merge9_uarb1, false, 370339, 2087822, true, 370347, 2087822⟩
]

/-- The rows of seed 4: 9 arbiters × 2 readings × 18 conditions. -/
def rows_g4 : List Row := [
  ⟨"g4_merge10_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge10_uarb1, false, 748909, 1218501, true, 2246740, 3655503⟩,
  ⟨"g4_merge10_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge10_uarb1, false, 100763, 166763, true, 106067, 175540⟩,
  ⟨"g4_merge10_uarb1.lit.mP", .lit, F_mP, v_g4_merge10_uarb1, false, 4124292, 4546175, true, 4124298, 4546175⟩,
  ⟨"g4_merge10_uarb1.lit.mG", .lit, F_mG, v_g4_merge10_uarb1, false, 15379023, 19818295, true, 15379047, 19818295⟩,
  ⟨"g4_merge10_uarb1.lit.mA", .lit, F_mA, v_g4_merge10_uarb1, false, 784189, 934805, true, 1725219, 2056571⟩,
  ⟨"g4_merge10_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge10_uarb1, false, 7878259, 9800012, true, 7878271, 9800012⟩,
  ⟨"g4_merge10_uarb1.lit.nP", .lit, F_nP, v_g4_merge10_uarb1, false, 8284607, 9056327, true, 1183517, 1293761⟩,
  ⟨"g4_merge10_uarb1.lit.nG", .lit, F_nG, v_g4_merge10_uarb1, false, 15950745, 19885753, true, 15950769, 19885753⟩,
  ⟨"g4_merge10_uarb1.lit.nA", .lit, F_nA, v_g4_merge10_uarb1, false, 1742971, 2056571, true, 792261, 934805⟩,
  ⟨"g4_merge10_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge10_uarb1, false, 5460331, 6597427, true, 5460339, 6597427⟩,
  ⟨"g4_merge10_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge10_uarb1, false, 1059699, 2554283, true, 1059706, 2554283⟩,
  ⟨"g4_merge10_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge10_uarb1, false, 1423931, 2978007, true, 474646, 992669⟩,
  ⟨"g4_merge10_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge10_uarb1, false, 4673583, 5420875, true, 9347181, 10841750⟩,
  ⟨"g4_merge10_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge10_uarb1, false, 4855699, 5632737, true, 9711413, 11265474⟩,
  ⟨"g4_merge10_uarb1.lit.h12", .lit, F_h12, v_g4_merge10_uarb1, false, 5793, 14005, true, 527167, 1274455⟩,
  ⟨"g4_merge10_uarb1.lit.h21", .lit, F_h21, v_g4_merge10_uarb1, false, 707779, 1484817, true, 707783, 1484817⟩,
  ⟨"g4_merge10_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge10_uarb1, false, 153951, 326626, true, 1385567, 2939634⟩,
  ⟨"g4_merge10_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge10_uarb1, false, 1084327, 2578910, true, 216867, 515782⟩,
  ⟨"g4_merge10_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge10_uarb1, false, 519909, 989501, true, 1559740, 2968503⟩,
  ⟨"g4_merge10_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge10_uarb1, false, 77063, 143063, true, 1541273, 2861260⟩,
  ⟨"g4_merge10_uarb1.cons.mP", .cons, F_mP, v_g4_merge10_uarb1, false, 3398792, 3820675, true, 3398798, 3820675⟩,
  ⟨"g4_merge10_uarb1.cons.mG", .cons, F_mG, v_g4_merge10_uarb1, false, 12336023, 16775295, true, 12336047, 16775295⟩,
  ⟨"g4_merge10_uarb1.cons.mA", .cons, F_mA, v_g4_merge10_uarb1, false, 7026079, 8682855, true, 1405219, 1736571⟩,
  ⟨"g4_merge10_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge10_uarb1, false, 6393759, 8315512, true, 6393771, 8315512⟩,
  ⟨"g4_merge10_uarb1.cons.nP", .cons, F_nP, v_g4_merge10_uarb1, false, 2277869, 2535109, true, 2277873, 2535109⟩,
  ⟨"g4_merge10_uarb1.cons.nG", .cons, F_nG, v_g4_merge10_uarb1, false, 12941745, 16876753, true, 12941769, 16876753⟩,
  ⟨"g4_merge10_uarb1.cons.nA", .cons, F_nA, v_g4_merge10_uarb1, false, 1403371, 1716971, true, 7016871, 8584855⟩,
  ⟨"g4_merge10_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge10_uarb1, false, 13249993, 16661281, true, 13250017, 16661281⟩,
  ⟨"g4_merge10_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge10_uarb1, false, 728699, 2223283, true, 728706, 2223283⟩,
  ⟨"g4_merge10_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge10_uarb1, false, 1018931, 2573007, true, 339646, 857669⟩,
  ⟨"g4_merge10_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge10_uarb1, false, 3819583, 4566875, true, 7639181, 9133750⟩,
  ⟨"g4_merge10_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge10_uarb1, false, 3964699, 4741737, true, 7929413, 9483474⟩,
  ⟨"g4_merge10_uarb1.cons.h12", .cons, F_h12, v_g4_merge10_uarb1, false, 52309, 159065, true, 366167, 1113455⟩,
  ⟨"g4_merge10_uarb1.cons.h21", .cons, F_h21, v_g4_merge10_uarb1, false, 510779, 1287817, true, 510783, 1287817⟩,
  ⟨"g4_merge10_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge10_uarb1, false, 333853, 851878, true, 1001567, 2555634⟩,
  ⟨"g4_merge10_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge10_uarb1, false, 752327, 2246910, true, 150467, 449382⟩,
  ⟨"g4_merge11_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge11_uarb1, false, 598957, 979809, false, 598970, 979809⟩,
  ⟨"g4_merge11_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge11_uarb1, false, 599433, 1254433, true, 1198879, 2508866⟩,
  ⟨"g4_merge11_uarb1.lit.mP", .lit, F_mP, v_g4_merge11_uarb1, false, 12129977, 14229137, true, 12129989, 14229137⟩,
  ⟨"g4_merge11_uarb1.lit.mG", .lit, F_mG, v_g4_merge11_uarb1, false, 7843859, 9735165, true, 110477, 137115⟩,
  ⟨"g4_merge11_uarb1.lit.mA", .lit, F_mA, v_g4_merge11_uarb1, false, 4542805, 4989089, true, 13628431, 14967267⟩,
  ⟨"g4_merge11_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge11_uarb1, false, 25030015, 28852773, true, 25030039, 28852773⟩,
  ⟨"g4_merge11_uarb1.lit.nP", .lit, F_nP, v_g4_merge11_uarb1, false, 12203743, 14155371, true, 12203755, 14155371⟩,
  ⟨"g4_merge11_uarb1.lit.nG", .lit, F_nG, v_g4_merge11_uarb1, false, 12092717, 14570677, true, 1099339, 1324607⟩,
  ⟨"g4_merge11_uarb1.lit.nA", .lit, F_nA, v_g4_merge11_uarb1, false, 12730699, 14288699, true, 12730715, 14288699⟩,
  ⟨"g4_merge11_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge11_uarb1, false, 12356195, 13982341, true, 12356207, 13982341⟩,
  ⟨"g4_merge11_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge11_uarb1, false, 169, 693, false, 169007, 693000⟩,
  ⟨"g4_merge11_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge11_uarb1, false, 173, 567, false, 19223, 63000⟩,
  ⟨"g4_merge11_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge11_uarb1, false, 13143557, 14793557, true, 13143572, 14793557⟩,
  ⟨"g4_merge11_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge11_uarb1, false, 13209557, 14477557, true, 13209572, 14477557⟩,
  ⟨"g4_merge11_uarb1.lit.h12", .lit, F_h12, v_g4_merge11_uarb1, false, 619, 2494, true, 68091, 274340⟩,
  ⟨"g4_merge11_uarb1.lit.h21", .lit, F_h21, v_g4_merge11_uarb1, false, 15343, 47043, true, 8524, 26135⟩,
  ⟨"g4_merge11_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge11_uarb1, false, 584721, 1852720, true, 584729, 1852720⟩,
  ⟨"g4_merge11_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge11_uarb1, false, 573721, 2223720, true, 191243, 741240⟩,
  ⟨"g4_merge11_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge11_uarb1, false, 192851, 348687, true, 26470, 47859⟩,
  ⟨"g4_merge11_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge11_uarb1, false, 432433, 1087433, true, 864879, 2174866⟩,
  ⟨"g4_merge11_uarb1.cons.mP", .cons, F_mP, v_g4_merge11_uarb1, false, 3345659, 4045379, true, 3345663, 4045379⟩,
  ⟨"g4_merge11_uarb1.cons.mG", .cons, F_mG, v_g4_merge11_uarb1, false, 19338577, 25012495, true, 19338601, 25012495⟩,
  ⟨"g4_merge11_uarb1.cons.mA", .cons, F_mA, v_g4_merge11_uarb1, false, 3777805, 4224089, true, 11333431, 12672267⟩,
  ⟨"g4_merge11_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge11_uarb1, false, 20725015, 24547773, true, 20725039, 24547773⟩,
  ⟨"g4_merge11_uarb1.cons.nP", .cons, F_nP, v_g4_merge11_uarb1, false, 10110743, 12062371, true, 10110755, 12062371⟩,
  ⟨"g4_merge11_uarb1.cons.nG", .cons, F_nG, v_g4_merge11_uarb1, false, 9967717, 12445677, true, 9967729, 12445677⟩,
  ⟨"g4_merge11_uarb1.cons.nA", .cons, F_nA, v_g4_merge11_uarb1, false, 556721, 638721, true, 3525905, 4045233⟩,
  ⟨"g4_merge11_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge11_uarb1, false, 10263195, 11889341, true, 10263207, 11889341⟩,
  ⟨"g4_merge11_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge11_uarb1, false, 101, 761, false, 101007, 761000⟩,
  ⟨"g4_merge11_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge11_uarb1, false, 63, 307, false, 126007, 614000⟩,
  ⟨"g4_merge11_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge11_uarb1, false, 10898557, 12548557, true, 10898572, 12548557⟩,
  ⟨"g4_merge11_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge11_uarb1, false, 10986557, 12254557, true, 10986572, 12254557⟩,
  ⟨"g4_merge11_uarb1.cons.h12", .cons, F_h12, v_g4_merge11_uarb1, false, 1203, 8078, true, 36091, 242340⟩,
  ⟨"g4_merge11_uarb1.cons.h21", .cons, F_h21, v_g4_merge11_uarb1, false, 9443, 41143, true, 47216, 205715⟩,
  ⟨"g4_merge11_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge11_uarb1, false, 357721, 1625720, true, 357729, 1625720⟩,
  ⟨"g4_merge11_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge11_uarb1, false, 308721, 1958720, true, 308729, 1958720⟩,
  ⟨"g4_merge12_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge12_uarb1, false, 2000625, 3574553, true, 10366, 18521⟩,
  ⟨"g4_merge12_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge12_uarb1, false, 2477869, 3321869, true, 2477882, 3321869⟩,
  ⟨"g4_merge12_uarb1.lit.mP", .lit, F_mP, v_g4_merge12_uarb1, false, 16406, 20549, true, 262497, 328784⟩,
  ⟨"g4_merge12_uarb1.lit.mG", .lit, F_mG, v_g4_merge12_uarb1, false, 2178263, 4631622, true, 2178275, 4631622⟩,
  ⟨"g4_merge12_uarb1.lit.mA", .lit, F_mA, v_g4_merge12_uarb1, false, 795679, 1251161, true, 795683, 1251161⟩,
  ⟨"g4_merge12_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge12_uarb1, false, 2194645, 4374276, true, 2194657, 4374276⟩,
  ⟨"g4_merge12_uarb1.lit.nP", .lit, F_nP, v_g4_merge12_uarb1, false, 314989, 394547, true, 1574951, 1972735⟩,
  ⟨"g4_merge12_uarb1.lit.nG", .lit, F_nG, v_g4_merge12_uarb1, false, 77449, 179836, false, 232351, 539508⟩,
  ⟨"g4_merge12_uarb1.lit.nA", .lit, F_nA, v_g4_merge12_uarb1, false, 978161, 1251161, true, 978165, 1251161⟩,
  ⟨"g4_merge12_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge12_uarb1, false, 834418, 1662111, false, 834430, 1662111⟩,
  ⟨"g4_merge12_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge12_uarb1, false, 583483, 2725439, true, 583490, 2725439⟩,
  ⟨"g4_merge12_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge12_uarb1, false, 50869, 196773, false, 84784, 327955⟩,
  ⟨"g4_merge12_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge12_uarb1, false, 3177199, 5319155, true, 3177214, 5319155⟩,
  ⟨"g4_merge12_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge12_uarb1, false, 3412061, 5533581, true, 3412076, 5533581⟩,
  ⟨"g4_merge12_uarb1.lit.h12", .lit, F_h12, v_g4_merge12_uarb1, false, 612281, 2754237, true, 612289, 2754237⟩,
  ⟨"g4_merge12_uarb1.lit.h21", .lit, F_h21, v_g4_merge12_uarb1, false, 809143, 2930663, true, 809151, 2930663⟩,
  ⟨"g4_merge12_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge12_uarb1, false, 779144, 2900663, true, 779152, 2900663⟩,
  ⟨"g4_merge12_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge12_uarb1, false, 214094, 928079, true, 642290, 2784237⟩,
  ⟨"g4_merge12_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge12_uarb1, false, 1501625, 3075553, true, 1501638, 3075553⟩,
  ⟨"g4_merge12_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge12_uarb1, false, 1965869, 2809869, true, 655294, 936623⟩,
  ⟨"g4_merge12_uarb1.cons.mP", .cons, F_mP, v_g4_merge12_uarb1, false, 39218, 51647, true, 627491, 826352⟩,
  ⟨"g4_merge12_uarb1.cons.mG", .cons, F_mG, v_g4_merge12_uarb1, false, 1564263, 4017622, true, 1564275, 4017622⟩,
  ⟨"g4_merge12_uarb1.cons.mA", .cons, F_mA, v_g4_merge12_uarb1, false, 609929, 1065411, true, 203311, 355137⟩,
  ⟨"g4_merge12_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge12_uarb1, false, 1602145, 3781776, true, 1602157, 3781776⟩,
  ⟨"g4_merge12_uarb1.cons.nP", .cons, F_nP, v_g4_merge12_uarb1, false, 250989, 330547, true, 1254951, 1652735⟩,
  ⟨"g4_merge12_uarb1.cons.nG", .cons, F_nG, v_g4_merge12_uarb1, false, 600541, 1715024, false, 600553, 1715024⟩,
  ⟨"g4_merge12_uarb1.cons.nA", .cons, F_nA, v_g4_merge12_uarb1, false, 775661, 1048661, true, 775665, 1048661⟩,
  ⟨"g4_merge12_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge12_uarb1, false, 746918, 1749611, false, 746930, 1749611⟩,
  ⟨"g4_merge12_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge12_uarb1, false, 281483, 2423439, true, 93830, 807813⟩,
  ⟨"g4_merge12_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge12_uarb1, false, 34469, 213173, false, 172352, 1065865⟩,
  ⟨"g4_merge12_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge12_uarb1, false, 2418199, 4560155, true, 2418214, 4560155⟩,
  ⟨"g4_merge12_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge12_uarb1, false, 2593061, 4714581, true, 2593076, 4714581⟩,
  ⟨"g4_merge12_uarb1.cons.h12", .cons, F_h12, v_g4_merge12_uarb1, false, 312281, 2454237, true, 312289, 2454237⟩,
  ⟨"g4_merge12_uarb1.cons.h21", .cons, F_h21, v_g4_merge12_uarb1, false, 462143, 2583663, true, 462151, 2583663⟩,
  ⟨"g4_merge12_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge12_uarb1, false, 147048, 854221, true, 441152, 2562663⟩,
  ⟨"g4_merge12_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge12_uarb1, false, 111094, 825079, true, 333290, 2475237⟩,
  ⟨"g4_merge12_uarb2.lit.fork1", .lit, F_fork1, v_g4_merge12_uarb2, false, 349981, 1068177, false, 349994, 1068177⟩,
  ⟨"g4_merge12_uarb2.lit.fork2", .lit, F_fork2, v_g4_merge12_uarb2, false, 121144, 559431, false, 80767, 372954⟩,
  ⟨"g4_merge12_uarb2.lit.mP", .lit, F_mP, v_g4_merge12_uarb2, false, 1254503, 1688345, false, 250903, 337669⟩,
  ⟨"g4_merge12_uarb2.lit.mG", .lit, F_mG, v_g4_merge12_uarb2, false, 1095671, 1727386, true, 1095675, 1727386⟩,
  ⟨"g4_merge12_uarb2.lit.mA", .lit, F_mA, v_g4_merge12_uarb2, false, 4154613, 6004895, true, 4154629, 6004895⟩,
  ⟨"g4_merge12_uarb2.lit.mGG", .lit, F_mGG, v_g4_merge12_uarb2, false, 14716, 20479, true, 912395, 1269698⟩,
  ⟨"g4_merge12_uarb2.lit.nP", .lit, F_nP, v_g4_merge12_uarb2, false, 16815, 29167, false, 269043, 466672⟩,
  ⟨"g4_merge12_uarb2.lit.nG", .lit, F_nG, v_g4_merge12_uarb2, false, 5951361, 11423257, true, 5951385, 11423257⟩,
  ⟨"g4_merge12_uarb2.lit.nA", .lit, F_nA, v_g4_merge12_uarb2, false, 776847, 1200979, true, 3884251, 6004895⟩,
  ⟨"g4_merge12_uarb2.lit.nGG", .lit, F_nGG, v_g4_merge12_uarb2, false, 1719359, 2618701, true, 1719365, 2618701⟩,
  ⟨"g4_merge12_uarb2.lit.rt1", .lit, F_rt1, v_g4_merge12_uarb2, false, 29789, 50789, false, 357475, 609468⟩,
  ⟨"g4_merge12_uarb2.lit.rt1b", .lit, F_rt1b, v_g4_merge12_uarb2, false, 212453, 832381, false, 212460, 832381⟩,
  ⟨"g4_merge12_uarb2.lit.rt1s", .lit, F_rt1s, v_g4_merge12_uarb2, false, 130172, 154547, true, 4165519, 4945504⟩,
  ⟨"g4_merge12_uarb2.lit.rt1bs", .lit, F_rt1bs, v_g4_merge12_uarb2, false, 3759489, 5575417, true, 3759504, 5575417⟩,
  ⟨"g4_merge12_uarb2.lit.h12", .lit, F_h12, v_g4_merge12_uarb2, false, 35587, 59962, true, 142349, 239848⟩,
  ⟨"g4_merge12_uarb2.lit.h21", .lit, F_h21, v_g4_merge12_uarb2, false, 236769, 856697, false, 236777, 856697⟩,
  ⟨"g4_merge12_uarb2.lit.o1x", .lit, F_o1x, v_g4_merge12_uarb2, false, 235770, 855697, false, 235778, 855697⟩,
  ⟨"g4_merge12_uarb2.lit.o2x", .lit, F_o2x, v_g4_merge12_uarb2, false, 1167785, 1947784, true, 1167793, 1947784⟩,
  ⟨"g4_merge12_uarb2.cons.fork1", .cons, F_fork1, v_g4_merge12_uarb2, false, 272981, 1145177, false, 272994, 1145177⟩,
  ⟨"g4_merge12_uarb2.cons.fork2", .cons, F_fork2, v_g4_merge12_uarb2, false, 11092, 86133, false, 51767, 401954⟩,
  ⟨"g4_merge12_uarb2.cons.mP", .cons, F_mP, v_g4_merge12_uarb2, false, 2714503, 3894345, true, 542903, 778869⟩,
  ⟨"g4_merge12_uarb2.cons.mG", .cons, F_mG, v_g4_merge12_uarb2, false, 844171, 1475886, true, 844175, 1475886⟩,
  ⟨"g4_merge12_uarb2.cons.mA", .cons, F_mA, v_g4_merge12_uarb2, false, 3249613, 5099895, true, 3249629, 5099895⟩,
  ⟨"g4_merge12_uarb2.cons.mGG", .cons, F_mGG, v_g4_merge12_uarb2, false, 718517, 1075823, true, 718520, 1075823⟩,
  ⟨"g4_merge12_uarb2.cons.nP", .cons, F_nP, v_g4_merge12_uarb2, false, 61885, 122043, false, 247543, 488172⟩,
  ⟨"g4_merge12_uarb2.cons.nG", .cons, F_nG, v_g4_merge12_uarb2, false, 4414361, 9886257, true, 4414385, 9886257⟩,
  ⟨"g4_merge12_uarb2.cons.nA", .cons, F_nA, v_g4_merge12_uarb2, false, 599447, 1023579, true, 2997251, 5117895⟩,
  ⟨"g4_merge12_uarb2.cons.nGG", .cons, F_nGG, v_g4_merge12_uarb2, false, 1333609, 2232951, true, 1333615, 2232951⟩,
  ⟨"g4_merge12_uarb2.cons.rt1", .cons, F_rt1, v_g4_merge12_uarb2, false, 81367, 160367, false, 325475, 641468⟩,
  ⟨"g4_merge12_uarb2.cons.rt1b", .cons, F_rt1b, v_g4_merge12_uarb2, false, 140453, 904381, false, 140460, 904381⟩,
  ⟨"g4_merge12_uarb2.cons.rt1s", .cons, F_rt1s, v_g4_merge12_uarb2, false, 140021, 172521, true, 373391, 460056⟩,
  ⟨"g4_merge12_uarb2.cons.rt1bs", .cons, F_rt1bs, v_g4_merge12_uarb2, false, 2935489, 4751417, true, 266864, 431947⟩,
  ⟨"g4_merge12_uarb2.cons.h12", .cons, F_h12, v_g4_merge12_uarb2, false, 43973, 83473, false, 43974, 83473⟩,
  ⟨"g4_merge12_uarb2.cons.h21", .cons, F_h21, v_g4_merge12_uarb2, false, 14979, 84427, false, 164777, 928697⟩,
  ⟨"g4_merge12_uarb2.cons.o1x", .cons, F_o1x, v_g4_merge12_uarb2, false, 163770, 927697, false, 163778, 927697⟩,
  ⟨"g4_merge12_uarb2.cons.o2x", .cons, F_o2x, v_g4_merge12_uarb2, false, 117595, 222928, false, 352793, 668784⟩,
  ⟨"g4_merge2_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge2_uarb1, false, 2415233, 3291233, true, 2415246, 3291233⟩,
  ⟨"g4_merge2_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge2_uarb1, false, 97463, 141263, true, 1949273, 2825260⟩,
  ⟨"g4_merge2_uarb1.lit.mP", .lit, F_mP, v_g4_merge2_uarb1, false, 5854957, 7901519, true, 5854969, 7901519⟩,
  ⟨"g4_merge2_uarb1.lit.mG", .lit, F_mG, v_g4_merge2_uarb1, false, 11172179, 16045469, true, 11172203, 16045469⟩,
  ⟨"g4_merge2_uarb1.lit.mA", .lit, F_mA, v_g4_merge2_uarb1, false, 3439119, 4001119, true, 3439127, 4001119⟩,
  ⟨"g4_merge2_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge2_uarb1, false, 3048865, 3817547, true, 3048871, 3817547⟩,
  ⟨"g4_merge2_uarb1.lit.nP", .lit, F_nP, v_g4_merge2_uarb1, false, 5822213, 7934263, true, 5822225, 7934263⟩,
  ⟨"g4_merge2_uarb1.lit.nG", .lit, F_nG, v_g4_merge2_uarb1, false, 416623, 621429, false, 2083127, 3107145⟩,
  ⟨"g4_merge2_uarb1.lit.nA", .lit, F_nA, v_g4_merge2_uarb1, false, 3439119, 4001119, true, 3439127, 4001119⟩,
  ⟨"g4_merge2_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge2_uarb1, false, 912051, 1181653, false, 4560279, 5908265⟩,
  ⟨"g4_merge2_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge2_uarb1, false, 201505, 374839, true, 1209037, 2249034⟩,
  ⟨"g4_merge2_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge2_uarb1, false, 41963, 272271, false, 55953, 363028⟩,
  ⟨"g4_merge2_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge2_uarb1, false, 7703455, 8743459, true, 7703470, 8743459⟩,
  ⟨"g4_merge2_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge2_uarb1, false, 2714277, 3635509, false, 2714292, 3635509⟩,
  ⟨"g4_merge2_uarb1.lit.h12", .lit, F_h12, v_g4_merge2_uarb1, false, 601379, 1121381, true, 601383, 1121381⟩,
  ⟨"g4_merge2_uarb1.lit.h21", .lit, F_h21, v_g4_merge2_uarb1, false, 465, 2701, false, 47897, 278203⟩,
  ⟨"g4_merge2_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge2_uarb1, false, 192581, 1113812, false, 192589, 1113812⟩,
  ⟨"g4_merge2_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge2_uarb1, false, 1231759, 2271762, true, 136863, 252418⟩,
  ⟨"g4_merge2_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge2_uarb1, false, 638411, 930411, true, 1915246, 2791233⟩,
  ⟨"g4_merge2_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge2_uarb1, false, 78463, 122263, true, 1569273, 2445260⟩,
  ⟨"g4_merge2_uarb1.cons.mP", .cons, F_mP, v_g4_merge2_uarb1, false, 4703957, 6750519, true, 4703969, 6750519⟩,
  ⟨"g4_merge2_uarb1.cons.mG", .cons, F_mG, v_g4_merge2_uarb1, false, 2961393, 4585823, true, 2961401, 4585823⟩,
  ⟨"g4_merge2_uarb1.cons.mA", .cons, F_mA, v_g4_merge2_uarb1, false, 2810619, 3372619, true, 2810627, 3372619⟩,
  ⟨"g4_merge2_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge2_uarb1, false, 2470865, 3239547, true, 2470871, 3239547⟩,
  ⟨"g4_merge2_uarb1.cons.nP", .cons, F_nP, v_g4_merge2_uarb1, false, 4671213, 6783263, true, 4671225, 6783263⟩,
  ⟨"g4_merge2_uarb1.cons.nG", .cons, F_nG, v_g4_merge2_uarb1, false, 288041, 465843, true, 1440209, 2329215⟩,
  ⟨"g4_merge2_uarb1.cons.nA", .cons, F_nA, v_g4_merge2_uarb1, false, 2810619, 3372619, true, 2810627, 3372619⟩,
  ⟨"g4_merge2_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge2_uarb1, false, 1934651, 2628653, true, 9673279, 13143265⟩,
  ⟨"g4_merge2_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge2_uarb1, false, 154505, 327839, true, 927037, 1967034⟩,
  ⟨"g4_merge2_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge2_uarb1, false, 21713, 292521, false, 28953, 390028⟩,
  ⟨"g4_merge2_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge2_uarb1, false, 906065, 1054637, true, 6342470, 7382459⟩,
  ⟨"g4_merge2_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge2_uarb1, false, 2633277, 3716509, false, 2633292, 3716509⟩,
  ⟨"g4_merge2_uarb1.cons.h12", .cons, F_h12, v_g4_merge2_uarb1, false, 464879, 984881, true, 464883, 984881⟩,
  ⟨"g4_merge2_uarb1.cons.h21", .cons, F_h21, v_g4_merge2_uarb1, false, 27645, 298453, false, 27647, 298453⟩,
  ⟨"g4_merge2_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge2_uarb1, false, 111581, 1194812, false, 111589, 1194812⟩,
  ⟨"g4_merge2_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge2_uarb1, false, 949759, 1989762, true, 316589, 663254⟩,
  ⟨"g4_merge3_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge3_uarb1, false, 494411, 816911, true, 1977657, 3267644⟩,
  ⟨"g4_merge3_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge3_uarb1, false, 574279, 1127461, true, 1722850, 3382383⟩,
  ⟨"g4_merge3_uarb1.lit.mP", .lit, F_mP, v_g4_merge3_uarb1, false, 2917928, 3315391, true, 2917934, 3315391⟩,
  ⟨"g4_merge3_uarb1.lit.mG", .lit, F_mG, v_g4_merge3_uarb1, false, 1924175, 2815244, false, 1924187, 2815244⟩,
  ⟨"g4_merge3_uarb1.lit.mA", .lit, F_mA, v_g4_merge3_uarb1, false, 626781, 780581, true, 3133913, 3902905⟩,
  ⟨"g4_merge3_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge3_uarb1, false, 1001326, 1399629, false, 1001332, 1399629⟩,
  ⟨"g4_merge3_uarb1.lit.nP", .lit, F_nP, v_g4_merge3_uarb1, false, 5812451, 6654187, true, 5812463, 6654187⟩,
  ⟨"g4_merge3_uarb1.lit.nG", .lit, F_nG, v_g4_merge3_uarb1, false, 11564597, 15153713, true, 11564621, 15153713⟩,
  ⟨"g4_merge3_uarb1.lit.nA", .lit, F_nA, v_g4_merge3_uarb1, false, 3099414, 4053187, true, 3099422, 4053187⟩,
  ⟨"g4_merge3_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge3_uarb1, false, 663943, 830353, true, 1991833, 2491059⟩,
  ⟨"g4_merge3_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge3_uarb1, false, 120231, 521795, false, 240469, 1043590⟩,
  ⟨"g4_merge3_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge3_uarb1, false, 1656307, 3028235, true, 1656314, 3028235⟩,
  ⟨"g4_merge3_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge3_uarb1, false, 1220069, 1621633, false, 2440153, 3243266⟩,
  ⟨"g4_merge3_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge3_uarb1, false, 7504983, 8876911, true, 7504998, 8876911⟩,
  ⟨"g4_merge3_uarb1.lit.h12", .lit, F_h12, v_g4_merge3_uarb1, false, 264869, 1067997, false, 264877, 1067997⟩,
  ⟨"g4_merge3_uarb1.lit.h21", .lit, F_h21, v_g4_merge3_uarb1, false, 823857, 1509821, true, 823861, 1509821⟩,
  ⟨"g4_merge3_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge3_uarb1, false, 1617715, 2989642, true, 1617723, 2989642⟩,
  ⟨"g4_merge3_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge3_uarb1, false, 262870, 1065997, false, 262878, 1065997⟩,
  ⟨"g4_merge3_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge3_uarb1, false, 383411, 705911, true, 1533657, 2823644⟩,
  ⟨"g4_merge3_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge3_uarb1, false, 1192837, 2852383, true, 1192850, 2852383⟩,
  ⟨"g4_merge3_uarb1.cons.mP", .cons, F_mP, v_g4_merge3_uarb1, false, 214948, 251081, true, 2364434, 2761891⟩,
  ⟨"g4_merge3_uarb1.cons.mG", .cons, F_mG, v_g4_merge3_uarb1, false, 1843675, 2895744, false, 1843687, 2895744⟩,
  ⟨"g4_merge3_uarb1.cons.mA", .cons, F_mA, v_g4_merge3_uarb1, false, 494981, 648781, true, 353559, 463415⟩,
  ⟨"g4_merge3_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge3_uarb1, false, 965576, 1435379, false, 965582, 1435379⟩,
  ⟨"g4_merge3_uarb1.cons.nP", .cons, F_nP, v_g4_merge3_uarb1, false, 4705451, 5547187, true, 4705463, 5547187⟩,
  ⟨"g4_merge3_uarb1.cons.nG", .cons, F_nG, v_g4_merge3_uarb1, false, 9137597, 12726713, true, 9137621, 12726713⟩,
  ⟨"g4_merge3_uarb1.cons.nA", .cons, F_nA, v_g4_merge3_uarb1, false, 2461414, 3415187, true, 2461422, 3415187⟩,
  ⟨"g4_merge3_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge3_uarb1, false, 4782487, 6280177, true, 4782499, 6280177⟩,
  ⟨"g4_merge3_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge3_uarb1, false, 83231, 558795, false, 166469, 1117590⟩,
  ⟨"g4_merge3_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge3_uarb1, false, 1258307, 2630235, true, 419438, 876745⟩,
  ⟨"g4_merge3_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge3_uarb1, false, 1183069, 1658633, false, 2366153, 3317266⟩,
  ⟨"g4_merge3_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge3_uarb1, false, 6070983, 7442911, true, 6070998, 7442911⟩,
  ⟨"g4_merge3_uarb1.cons.h12", .cons, F_h12, v_g4_merge3_uarb1, false, 190869, 1141997, false, 190877, 1141997⟩,
  ⟨"g4_merge3_uarb1.cons.h21", .cons, F_h21, v_g4_merge3_uarb1, false, 629357, 1315321, true, 629361, 1315321⟩,
  ⟨"g4_merge3_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge3_uarb1, false, 1237715, 2609642, true, 1237723, 2609642⟩,
  ⟨"g4_merge3_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge3_uarb1, false, 188870, 1139997, false, 188878, 1139997⟩,
  ⟨"g4_merge4_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge4_uarb1, false, 521471, 941471, false, 521484, 941471⟩,
  ⟨"g4_merge4_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge4_uarb1, false, 24983, 45641, false, 624588, 1141025⟩,
  ⟨"g4_merge4_uarb1.lit.mP", .lit, F_mP, v_g4_merge4_uarb1, false, 6873255, 7641713, true, 6873267, 7641713⟩,
  ⟨"g4_merge4_uarb1.lit.mG", .lit, F_mG, v_g4_merge4_uarb1, false, 12870673, 17322529, true, 1838671, 2474647⟩,
  ⟨"g4_merge4_uarb1.lit.mA", .lit, F_mA, v_g4_merge4_uarb1, false, 1376227, 1687427, true, 6881151, 8437135⟩,
  ⟨"g4_merge4_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge4_uarb1, false, 116023, 151441, true, 4292859, 5603317⟩,
  ⟨"g4_merge4_uarb1.lit.nP", .lit, F_nP, v_g4_merge4_uarb1, false, 6224809, 8290159, true, 6224821, 8290159⟩,
  ⟨"g4_merge4_uarb1.lit.nG", .lit, F_nG, v_g4_merge4_uarb1, false, 1721809, 2433527, true, 12052687, 17034689⟩,
  ⟨"g4_merge4_uarb1.lit.nA", .lit, F_nA, v_g4_merge4_uarb1, false, 957611, 1159761, false, 2872849, 3479283⟩,
  ⟨"g4_merge4_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge4_uarb1, false, 4487229, 5542121, true, 4487237, 5542121⟩,
  ⟨"g4_merge4_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge4_uarb1, false, 37703, 144075, false, 9049, 34578⟩,
  ⟨"g4_merge4_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge4_uarb1, false, 108379, 361379, false, 216765, 722758⟩,
  ⟨"g4_merge4_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge4_uarb1, false, 7594889, 9527121, true, 7594904, 9527121⟩,
  ⟨"g4_merge4_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge4_uarb1, false, 7644429, 9182429, true, 7644444, 9182429⟩,
  ⟨"g4_merge4_uarb1.lit.h12", .lit, F_h12, v_g4_merge4_uarb1, false, 89092, 330621, true, 89093, 330621⟩,
  ⟨"g4_merge4_uarb1.lit.h21", .lit, F_h21, v_g4_merge4_uarb1, false, 59819, 186319, false, 59821, 186319⟩,
  ⟨"g4_merge4_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge4_uarb1, false, 240277, 746276, false, 240285, 746276⟩,
  ⟨"g4_merge4_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge4_uarb1, false, 741737, 2673968, true, 741745, 2673968⟩,
  ⟨"g4_merge4_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge4_uarb1, false, 470471, 992471, false, 470484, 992471⟩,
  ⟨"g4_merge4_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge4_uarb1, false, 23623, 47001, false, 590588, 1175025⟩,
  ⟨"g4_merge4_uarb1.cons.mP", .cons, F_mP, v_g4_merge4_uarb1, false, 5631255, 6399713, true, 5631267, 6399713⟩,
  ⟨"g4_merge4_uarb1.cons.mG", .cons, F_mG, v_g4_merge4_uarb1, false, 10270673, 14722529, true, 10270697, 14722529⟩,
  ⟨"g4_merge4_uarb1.cons.mA", .cons, F_mA, v_g4_merge4_uarb1, false, 1116027, 1427227, true, 5580151, 7136135⟩,
  ⟨"g4_merge4_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge4_uarb1, false, 3447851, 4758317, true, 3447859, 4758317⟩,
  ⟨"g4_merge4_uarb1.cons.nP", .cons, F_nP, v_g4_merge4_uarb1, false, 4982809, 7048159, true, 4982821, 7048159⟩,
  ⟨"g4_merge4_uarb1.cons.nG", .cons, F_nG, v_g4_merge4_uarb1, false, 9577663, 14559689, true, 9577687, 14559689⟩,
  ⟨"g4_merge4_uarb1.cons.nA", .cons, F_nA, v_g4_merge4_uarb1, false, 942611, 1174761, false, 2827849, 3524283⟩,
  ⟨"g4_merge4_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge4_uarb1, false, 10873687, 14038363, true, 10873711, 14038363⟩,
  ⟨"g4_merge4_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge4_uarb1, false, 76609, 468725, false, 6129, 37498⟩,
  ⟨"g4_merge4_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge4_uarb1, false, 25793, 130793, false, 11905, 60366⟩,
  ⟨"g4_merge4_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge4_uarb1, false, 6111889, 8044121, true, 6111904, 8044121⟩,
  ⟨"g4_merge4_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge4_uarb1, false, 6188429, 7726429, true, 6188444, 7726429⟩,
  ⟨"g4_merge4_uarb1.cons.h12", .cons, F_h12, v_g4_merge4_uarb1, false, 51092, 292621, true, 7299, 41803⟩,
  ⟨"g4_merge4_uarb1.cons.h21", .cons, F_h21, v_g4_merge4_uarb1, false, 14773, 67273, false, 44321, 201819⟩,
  ⟨"g4_merge4_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge4_uarb1, false, 178277, 808276, false, 178285, 808276⟩,
  ⟨"g4_merge4_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge4_uarb1, false, 428737, 2360968, true, 428745, 2360968⟩,
  ⟨"g4_merge6_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge6_uarb1, false, 2308097, 3152097, true, 26530, 36231⟩,
  ⟨"g4_merge6_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge6_uarb1, false, 17741, 31491, true, 1703149, 3023136⟩,
  ⟨"g4_merge6_uarb1.lit.mP", .lit, F_mP, v_g4_merge6_uarb1, false, 2908240, 3292469, true, 2908246, 3292469⟩,
  ⟨"g4_merge6_uarb1.lit.mG", .lit, F_mG, v_g4_merge6_uarb1, false, 9952453, 14724007, true, 9952477, 14724007⟩,
  ⟨"g4_merge6_uarb1.lit.mA", .lit, F_mA, v_g4_merge6_uarb1, false, 6588821, 7680821, true, 6588837, 7680821⟩,
  ⟨"g4_merge6_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge6_uarb1, false, 5362397, 7487945, true, 5362409, 7487945⟩,
  ⟨"g4_merge6_uarb1.lit.nP", .lit, F_nP, v_g4_merge6_uarb1, false, 2114121, 2413297, false, 2114133, 2413297⟩,
  ⟨"g4_merge6_uarb1.lit.nG", .lit, F_nG, v_g4_merge6_uarb1, false, 10249925, 14176853, true, 10249949, 14176853⟩,
  ⟨"g4_merge6_uarb1.lit.nA", .lit, F_nA, v_g4_merge6_uarb1, false, 830371, 1054371, true, 5812613, 7380597⟩,
  ⟨"g4_merge6_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge6_uarb1, false, 10270401, 13628153, true, 933675, 1238923⟩,
  ⟨"g4_merge6_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge6_uarb1, false, 348583, 976559, true, 1045756, 2929677⟩,
  ⟨"g4_merge6_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge6_uarb1, false, 240619, 696901, false, 240626, 696901⟩,
  ⟨"g4_merge6_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge6_uarb1, false, 3207535, 4149499, true, 6415085, 8298998⟩,
  ⟨"g4_merge6_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge6_uarb1, false, 3094970, 3778111, true, 6189955, 7556222⟩,
  ⟨"g4_merge6_uarb1.lit.h12", .lit, F_h12, v_g4_merge6_uarb1, false, 173167, 487155, true, 103901, 292293⟩,
  ⟨"g4_merge6_uarb1.lit.h21", .lit, F_h21, v_g4_merge6_uarb1, false, 132436, 360577, false, 18920, 51511⟩,
  ⟨"g4_merge6_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge6_uarb1, false, 785873, 2152154, true, 785881, 2152154⟩,
  ⟨"g4_merge6_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge6_uarb1, false, 1068003, 2951930, true, 1068011, 2951930⟩,
  ⟨"g4_merge6_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge6_uarb1, false, 1801097, 2645097, true, 600370, 881699⟩,
  ⟨"g4_merge6_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge6_uarb1, false, 1834, 3709, true, 1291149, 2611136⟩,
  ⟨"g4_merge6_uarb1.cons.mP", .cons, F_mP, v_g4_merge6_uarb1, false, 2361740, 2745969, true, 2361746, 2745969⟩,
  ⟨"g4_merge6_uarb1.cons.mG", .cons, F_mG, v_g4_merge6_uarb1, false, 7765453, 12537007, true, 7765477, 12537007⟩,
  ⟨"g4_merge6_uarb1.cons.mA", .cons, F_mA, v_g4_merge6_uarb1, false, 1774607, 2138607, true, 5323837, 6415821⟩,
  ⟨"g4_merge6_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge6_uarb1, false, 4222397, 6347945, true, 4222409, 6347945⟩,
  ⟨"g4_merge6_uarb1.cons.nP", .cons, F_nP, v_g4_merge6_uarb1, false, 4699121, 5516297, true, 4699133, 5516297⟩,
  ⟨"g4_merge6_uarb1.cons.nG", .cons, F_nG, v_g4_merge6_uarb1, false, 2694975, 4003951, true, 2694983, 4003951⟩,
  ⟨"g4_merge6_uarb1.cons.nA", .cons, F_nA, v_g4_merge6_uarb1, false, 4639597, 6207597, true, 421783, 564327⟩,
  ⟨"g4_merge6_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge6_uarb1, false, 8150401, 11508153, true, 8150425, 11508153⟩,
  ⟨"g4_merge6_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge6_uarb1, false, 680749, 2564677, true, 680756, 2564677⟩,
  ⟨"g4_merge6_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge6_uarb1, false, 189619, 747901, false, 189626, 747901⟩,
  ⟨"g4_merge6_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge6_uarb1, false, 2556535, 3498499, true, 5113085, 6996998⟩,
  ⟨"g4_merge6_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge6_uarb1, false, 57790, 73677, true, 4969955, 6336222⟩,
  ⟨"g4_merge6_uarb1.cons.h12", .cons, F_h12, v_g4_merge6_uarb1, false, 342001, 1283965, true, 68401, 256793⟩,
  ⟨"g4_merge6_uarb1.cons.h21", .cons, F_h21, v_g4_merge6_uarb1, false, 106936, 386077, false, 106940, 386077⟩,
  ⟨"g4_merge6_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge6_uarb1, false, 520873, 1887154, true, 520881, 1887154⟩,
  ⟨"g4_merge6_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge6_uarb1, false, 704003, 2587930, true, 704011, 2587930⟩,
  ⟨"g4_merge9_uarb1.lit.fork1", .lit, F_fork1, v_g4_merge9_uarb1, false, 1138373, 1560373, true, 2276759, 3120746⟩,
  ⟨"g4_merge9_uarb1.lit.fork2", .lit, F_fork2, v_g4_merge9_uarb1, false, 1548857, 2868857, true, 1548870, 2868857⟩,
  ⟨"g4_merge9_uarb1.lit.mP", .lit, F_mP, v_g4_merge9_uarb1, false, 2417597, 2813063, true, 2417603, 2813063⟩,
  ⟨"g4_merge9_uarb1.lit.mG", .lit, F_mG, v_g4_merge9_uarb1, false, 3976323, 5828206, true, 3976335, 5828206⟩,
  ⟨"g4_merge9_uarb1.lit.mA", .lit, F_mA, v_g4_merge9_uarb1, false, 472001, 563001, true, 1416007, 1689003⟩,
  ⟨"g4_merge9_uarb1.lit.mGG", .lit, F_mGG, v_g4_merge9_uarb1, false, 4390732, 5971149, true, 4390744, 5971149⟩,
  ⟨"g4_merge9_uarb1.lit.nP", .lit, F_nP, v_g4_merge9_uarb1, false, 90361, 106305, false, 451808, 531525⟩,
  ⟨"g4_merge9_uarb1.lit.nG", .lit, F_nG, v_g4_merge9_uarb1, false, 8653561, 12270201, true, 8653585, 12270201⟩,
  ⟨"g4_merge9_uarb1.lit.nA", .lit, F_nA, v_g4_merge9_uarb1, false, 1199327, 1591327, true, 1199331, 1591327⟩,
  ⟨"g4_merge9_uarb1.lit.nGG", .lit, F_nGG, v_g4_merge9_uarb1, false, 8638649, 11666409, true, 8638673, 11666409⟩,
  ⟨"g4_merge9_uarb1.lit.rt1", .lit, F_rt1, v_g4_merge9_uarb1, false, 205097, 502097, true, 820395, 2008388⟩,
  ⟨"g4_merge9_uarb1.lit.rt1b", .lit, F_rt1b, v_g4_merge9_uarb1, false, 62347, 193847, false, 249395, 775388⟩,
  ⟨"g4_merge9_uarb1.lit.rt1s", .lit, F_rt1s, v_g4_merge9_uarb1, false, 2682599, 3276599, true, 5365213, 6553198⟩,
  ⟨"g4_merge9_uarb1.lit.rt1bs", .lit, F_rt1bs, v_g4_merge9_uarb1, false, 2709599, 3502599, true, 5419213, 7005198⟩,
  ⟨"g4_merge9_uarb1.lit.h12", .lit, F_h12, v_g4_merge9_uarb1, false, 813977, 2001977, true, 813985, 2001977⟩,
  ⟨"g4_merge9_uarb1.lit.h21", .lit, F_h21, v_g4_merge9_uarb1, false, 272977, 798977, false, 272985, 798977⟩,
  ⟨"g4_merge9_uarb1.lit.o1x", .lit, F_o1x, v_g4_merge9_uarb1, false, 274978, 800977, false, 274986, 800977⟩,
  ⟨"g4_merge9_uarb1.lit.o2x", .lit, F_o2x, v_g4_merge9_uarb1, false, 842978, 2030977, true, 842986, 2030977⟩,
  ⟨"g4_merge9_uarb1.cons.fork1", .cons, F_fork1, v_g4_merge9_uarb1, false, 887873, 1309873, true, 1775759, 2619746⟩,
  ⟨"g4_merge9_uarb1.cons.fork2", .cons, F_fork2, v_g4_merge9_uarb1, false, 1149857, 2469857, true, 1149870, 2469857⟩,
  ⟨"g4_merge9_uarb1.cons.mP", .cons, F_mP, v_g4_merge9_uarb1, false, 649199, 781021, true, 649201, 781021⟩,
  ⟨"g4_merge9_uarb1.cons.mG", .cons, F_mG, v_g4_merge9_uarb1, false, 3087823, 4939706, true, 3087835, 4939706⟩,
  ⟨"g4_merge9_uarb1.cons.mA", .cons, F_mA, v_g4_merge9_uarb1, false, 1136503, 1409503, true, 1136507, 1409503⟩,
  ⟨"g4_merge9_uarb1.cons.mGG", .cons, F_mGG, v_g4_merge9_uarb1, false, 3452732, 5033149, true, 3452744, 5033149⟩,
  ⟨"g4_merge9_uarb1.cons.nP", .cons, F_nP, v_g4_merge9_uarb1, false, 5867, 7135, true, 322686, 392425⟩,
  ⟨"g4_merge9_uarb1.cons.nG", .cons, F_nG, v_g4_merge9_uarb1, false, 6756561, 10373201, true, 6756585, 10373201⟩,
  ⟨"g4_merge9_uarb1.cons.nA", .cons, F_nA, v_g4_merge9_uarb1, false, 945827, 1337827, true, 945831, 1337827⟩,
  ⟨"g4_merge9_uarb1.cons.nGG", .cons, F_nGG, v_g4_merge9_uarb1, false, 6792649, 9820409, true, 6792673, 9820409⟩,
  ⟨"g4_merge9_uarb1.cons.rt1", .cons, F_rt1, v_g4_merge9_uarb1, false, 46199, 145199, true, 554395, 1742388⟩,
  ⟨"g4_merge9_uarb1.cons.rt1b", .cons, F_rt1b, v_g4_merge9_uarb1, false, 46097, 210097, false, 184395, 840388⟩,
  ⟨"g4_merge9_uarb1.cons.rt1s", .cons, F_rt1s, v_g4_merge9_uarb1, false, 713533, 911533, true, 1427071, 1823066⟩,
  ⟨"g4_merge9_uarb1.cons.rt1bs", .cons, F_rt1bs, v_g4_merge9_uarb1, false, 2140599, 2933599, true, 4281213, 5867198⟩,
  ⟨"g4_merge9_uarb1.cons.h12", .cons, F_h12, v_g4_merge9_uarb1, false, 185659, 581659, true, 42845, 134229⟩,
  ⟨"g4_merge9_uarb1.cons.h21", .cons, F_h21, v_g4_merge9_uarb1, false, 207977, 863977, false, 207985, 863977⟩,
  ⟨"g4_merge9_uarb1.cons.o1x", .cons, F_o1x, v_g4_merge9_uarb1, false, 209978, 865977, false, 29998, 123711⟩,
  ⟨"g4_merge9_uarb1.cons.o2x", .cons, F_o2x, v_g4_merge9_uarb1, false, 576978, 1764977, true, 576986, 1764977⟩
]

/-- The rows of seed d: 9 arbiters × 2 readings × 18 conditions. -/
def rows_gd : List Row := [
  ⟨"gd_merge10_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge10_uarb1, false, 162819, 254819, true, 48406, 75757⟩,
  ⟨"gd_merge10_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge10_uarb1, false, 118703, 223728, true, 18031, 33984⟩,
  ⟨"gd_merge10_uarb1.lit.mP", .lit, F_mP, v_gd_merge10_uarb1, false, 5931985, 7981333, true, 5931997, 7981333⟩,
  ⟨"gd_merge10_uarb1.lit.mG", .lit, F_mG, v_gd_merge10_uarb1, false, 11958023, 16531653, true, 11958047, 16531653⟩,
  ⟨"gd_merge10_uarb1.lit.mA", .lit, F_mA, v_gd_merge10_uarb1, false, 7080809, 8340809, true, 7080825, 8340809⟩,
  ⟨"gd_merge10_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge10_uarb1, false, 4368949, 5293043, true, 4368957, 5293043⟩,
  ⟨"gd_merge10_uarb1.lit.nP", .lit, F_nP, v_gd_merge10_uarb1, false, 2053805, 2897513, false, 2053817, 2897513⟩,
  ⟨"gd_merge10_uarb1.lit.nG", .lit, F_nG, v_gd_merge10_uarb1, false, 4311511, 5931273, false, 4311535, 5931273⟩,
  ⟨"gd_merge10_uarb1.lit.nA", .lit, F_nA, v_gd_merge10_uarb1, false, 6832509, 8340809, true, 6832525, 8340809⟩,
  ⟨"gd_merge10_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge10_uarb1, false, 4677215, 5543269, false, 4677239, 5543269⟩,
  ⟨"gd_merge10_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge10_uarb1, false, 305597, 602597, true, 1222395, 2410388⟩,
  ⟨"gd_merge10_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge10_uarb1, false, 376483, 799101, false, 376490, 799101⟩,
  ⟨"gd_merge10_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge10_uarb1, false, 7785047, 8973047, true, 7785062, 8973047⟩,
  ⟨"gd_merge10_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge10_uarb1, false, 1367571, 1578880, false, 2735157, 3157760⟩,
  ⟨"gd_merge10_uarb1.lit.h12", .lit, F_h12, v_gd_merge10_uarb1, false, 37883, 75008, true, 151533, 300032⟩,
  ⟨"gd_merge10_uarb1.lit.h21", .lit, F_h21, v_gd_merge10_uarb1, false, 57193, 117567, false, 133453, 274323⟩,
  ⟨"gd_merge10_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge10_uarb1, false, 401352, 823969, false, 401360, 823969⟩,
  ⟨"gd_merge10_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge10_uarb1, false, 1244257, 2432256, true, 414755, 810752⟩,
  ⟨"gd_merge10_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge10_uarb1, false, 1220009, 2232009, true, 45186, 82667⟩,
  ⟨"gd_merge10_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge10_uarb1, false, 77453, 182478, true, 929449, 2189736⟩,
  ⟨"gd_merge10_uarb1.cons.mP", .cons, F_mP, v_gd_merge10_uarb1, false, 4504985, 6554333, true, 4504997, 6554333⟩,
  ⟨"gd_merge10_uarb1.cons.mG", .cons, F_mG, v_gd_merge10_uarb1, false, 9074023, 13647653, true, 9074047, 13647653⟩,
  ⟨"gd_merge10_uarb1.cons.mA", .cons, F_mA, v_gd_merge10_uarb1, false, 5517809, 6777809, true, 5517825, 6777809⟩,
  ⟨"gd_merge10_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge10_uarb1, false, 147563, 187741, true, 3393957, 4318043⟩,
  ⟨"gd_merge10_uarb1.cons.nP", .cons, F_nP, v_gd_merge10_uarb1, false, 4388805, 6670513, true, 4388817, 6670513⟩,
  ⟨"gd_merge10_uarb1.cons.nG", .cons, F_nG, v_gd_merge10_uarb1, false, 9366511, 13700273, true, 9366535, 13700273⟩,
  ⟨"gd_merge10_uarb1.cons.nA", .cons, F_nA, v_gd_merge10_uarb1, false, 5286509, 6794809, true, 5286525, 6794809⟩,
  ⟨"gd_merge10_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge10_uarb1, false, 10376215, 12676269, true, 10376239, 12676269⟩,
  ⟨"gd_merge10_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge10_uarb1, false, 6911, 17911, true, 746395, 1934388⟩,
  ⟨"gd_merge10_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge10_uarb1, false, 338483, 837101, false, 338490, 837101⟩,
  ⟨"gd_merge10_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge10_uarb1, false, 5997047, 7185047, true, 5997062, 7185047⟩,
  ⟨"gd_merge10_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge10_uarb1, false, 3054571, 3622880, true, 6109157, 7245760⟩,
  ⟨"gd_merge10_uarb1.cons.h12", .cons, F_h12, v_gd_merge10_uarb1, false, 93407, 241907, true, 93408, 241907⟩,
  ⟨"gd_merge10_uarb1.cons.h21", .cons, F_h21, v_gd_merge10_uarb1, false, 362351, 860969, false, 362359, 860969⟩,
  ⟨"gd_merge10_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge10_uarb1, false, 363352, 861969, false, 121120, 287323⟩,
  ⟨"gd_merge10_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge10_uarb1, false, 768257, 1956256, true, 768265, 1956256⟩,
  ⟨"gd_merge11_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge11_uarb1, false, 78413, 106413, true, 2352403, 3192390⟩,
  ⟨"gd_merge11_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge11_uarb1, false, 910605, 1433761, false, 910618, 1433761⟩,
  ⟨"gd_merge11_uarb1.lit.mP", .lit, F_mP, v_gd_merge11_uarb1, false, 5909697, 7946047, true, 5909709, 7946047⟩,
  ⟨"gd_merge11_uarb1.lit.mG", .lit, F_mG, v_gd_merge11_uarb1, false, 10919645, 16902107, true, 10919669, 16902107⟩,
  ⟨"gd_merge11_uarb1.lit.mA", .lit, F_mA, v_gd_merge11_uarb1, false, 1679867, 1951867, true, 1679871, 1951867⟩,
  ⟨"gd_merge11_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge11_uarb1, false, 1466177, 1990441, true, 1466180, 1990441⟩,
  ⟨"gd_merge11_uarb1.lit.nP", .lit, F_nP, v_gd_merge11_uarb1, false, 5890961, 7964783, true, 5890973, 7964783⟩,
  ⟨"gd_merge11_uarb1.lit.nG", .lit, F_nG, v_gd_merge11_uarb1, false, 5528755, 8020894, true, 5528767, 8020894⟩,
  ⟨"gd_merge11_uarb1.lit.nA", .lit, F_nA, v_gd_merge11_uarb1, false, 686819, 840108, false, 228941, 280036⟩,
  ⟨"gd_merge11_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge11_uarb1, false, 12302825, 15461281, true, 12302849, 15461281⟩,
  ⟨"gd_merge11_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge11_uarb1, false, 392233, 1497872, true, 784473, 2995744⟩,
  ⟨"gd_merge11_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge11_uarb1, false, 568141, 1202141, true, 1136289, 2404282⟩,
  ⟨"gd_merge11_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge11_uarb1, false, 3664669, 4770308, true, 7329353, 9540616⟩,
  ⟨"gd_merge11_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge11_uarb1, false, 3840577, 4474577, true, 7681169, 8949154⟩,
  ⟨"gd_merge11_uarb1.lit.h12", .lit, F_h12, v_gd_merge11_uarb1, false, 776157, 2987435, true, 155233, 597487⟩,
  ⟨"gd_merge11_uarb1.lit.h21", .lit, F_h21, v_gd_merge11_uarb1, false, 1130973, 2398973, true, 1130981, 2398973⟩,
  ⟨"gd_merge11_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge11_uarb1, false, 1097974, 2365973, true, 1097982, 2365973⟩,
  ⟨"gd_merge11_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge11_uarb1, false, 809158, 3020435, true, 809166, 3020435⟩,
  ⟨"gd_merge11_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge11_uarb1, false, 182639, 266639, true, 1826403, 2666390⟩,
  ⟨"gd_merge11_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge11_uarb1, false, 873605, 1470761, false, 873618, 1470761⟩,
  ⟨"gd_merge11_uarb1.cons.mP", .cons, F_mP, v_gd_merge11_uarb1, false, 4731697, 6768047, true, 4731709, 6768047⟩,
  ⟨"gd_merge11_uarb1.cons.mG", .cons, F_mG, v_gd_merge11_uarb1, false, 8545645, 14528107, true, 776879, 1320737⟩,
  ⟨"gd_merge11_uarb1.cons.mA", .cons, F_mA, v_gd_merge11_uarb1, false, 1369117, 1641117, true, 1369121, 1641117⟩,
  ⟨"gd_merge11_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge11_uarb1, false, 292763, 423829, true, 1171055, 1695316⟩,
  ⟨"gd_merge11_uarb1.cons.nP", .cons, F_nP, v_gd_merge11_uarb1, false, 1570987, 2262261, true, 1570991, 2262261⟩,
  ⟨"gd_merge11_uarb1.cons.nG", .cons, F_nG, v_gd_merge11_uarb1, false, 336635, 528338, true, 4376267, 6868394⟩,
  ⟨"gd_merge11_uarb1.cons.nA", .cons, F_nA, v_gd_merge11_uarb1, false, 674819, 852108, false, 224941, 284036⟩,
  ⟨"gd_merge11_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge11_uarb1, false, 9936825, 13095281, true, 9936849, 13095281⟩,
  ⟨"gd_merge11_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge11_uarb1, false, 213733, 1319372, true, 427473, 2638744⟩,
  ⟨"gd_merge11_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge11_uarb1, false, 398141, 1032141, true, 796289, 2064282⟩,
  ⟨"gd_merge11_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge11_uarb1, false, 2934169, 4039808, true, 5868353, 8079616⟩,
  ⟨"gd_merge11_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge11_uarb1, false, 3118577, 3752577, true, 6237169, 7505154⟩,
  ⟨"gd_merge11_uarb1.cons.h12", .cons, F_h12, v_gd_merge11_uarb1, false, 430157, 2641435, true, 86033, 528287⟩,
  ⟨"gd_merge11_uarb1.cons.h21", .cons, F_h21, v_gd_merge11_uarb1, false, 799973, 2067973, true, 799981, 2067973⟩,
  ⟨"gd_merge11_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge11_uarb1, false, 781974, 2049973, true, 781982, 2049973⟩,
  ⟨"gd_merge11_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge11_uarb1, false, 448158, 2659435, true, 448166, 2659435⟩,
  ⟨"gd_merge12_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge12_uarb1, false, 2663379, 3825661, true, 2663392, 3825661⟩,
  ⟨"gd_merge12_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge12_uarb1, false, 967027, 1451027, true, 1934067, 2902054⟩,
  ⟨"gd_merge12_uarb1.lit.mP", .lit, F_mP, v_gd_merge12_uarb1, false, 267593, 434974, false, 133798, 217487⟩,
  ⟨"gd_merge12_uarb1.lit.mG", .lit, F_mG, v_gd_merge12_uarb1, false, 5018091, 10546273, true, 5018115, 10546273⟩,
  ⟨"gd_merge12_uarb1.lit.mA", .lit, F_mA, v_gd_merge12_uarb1, false, 1405531, 1875625, true, 4216609, 5626875⟩,
  ⟨"gd_merge12_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge12_uarb1, false, 3081656, 5023985, true, 3081668, 5023985⟩,
  ⟨"gd_merge12_uarb1.lit.nP", .lit, F_nP, v_gd_merge12_uarb1, false, 1815637, 2201497, true, 1815643, 2201497⟩,
  ⟨"gd_merge12_uarb1.lit.nG", .lit, F_nG, v_gd_merge12_uarb1, false, 3037159, 4875482, true, 3037171, 4875482⟩,
  ⟨"gd_merge12_uarb1.lit.nA", .lit, F_nA, v_gd_merge12_uarb1, false, 152707, 201347, true, 3817691, 5033675⟩,
  ⟨"gd_merge12_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge12_uarb1, false, 6260719, 9413645, true, 6260743, 9413645⟩,
  ⟨"gd_merge12_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge12_uarb1, false, 236491, 553991, true, 945971, 2215964⟩,
  ⟨"gd_merge12_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge12_uarb1, false, 57241, 183741, false, 228971, 734964⟩,
  ⟨"gd_merge12_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge12_uarb1, false, 2290049, 2925049, true, 4580113, 5850098⟩,
  ⟨"gd_merge12_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge12_uarb1, false, 2203549, 2972549, true, 4407113, 5945098⟩,
  ⟨"gd_merge12_uarb1.lit.h12", .lit, F_h12, v_gd_merge12_uarb1, false, 940591, 2210591, true, 940599, 2210591⟩,
  ⟨"gd_merge12_uarb1.lit.h21", .lit, F_h21, v_gd_merge12_uarb1, false, 251591, 757591, false, 251599, 757591⟩,
  ⟨"gd_merge12_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge12_uarb1, false, 737592, 2275591, true, 737600, 2275591⟩,
  ⟨"gd_merge12_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge12_uarb1, false, 970592, 2240591, true, 42200, 97417⟩,
  ⟨"gd_merge12_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge12_uarb1, false, 187489, 293151, true, 687464, 1074887⟩,
  ⟨"gd_merge12_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge12_uarb1, false, 743527, 1227527, true, 1487067, 2455054⟩,
  ⟨"gd_merge12_uarb1.cons.mP", .cons, F_mP, v_gd_merge12_uarb1, false, 564343, 1037224, true, 282173, 518612⟩,
  ⟨"gd_merge12_uarb1.cons.mG", .cons, F_mG, v_gd_merge12_uarb1, false, 3423091, 8951273, true, 3423115, 8951273⟩,
  ⟨"gd_merge12_uarb1.cons.mA", .cons, F_mA, v_gd_merge12_uarb1, false, 3245593, 4655875, true, 3245609, 4655875⟩,
  ⟨"gd_merge12_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge12_uarb1, false, 2258156, 4200485, true, 2258168, 4200485⟩,
  ⟨"gd_merge12_uarb1.cons.nP", .cons, F_nP, v_gd_merge12_uarb1, false, 1408637, 1794497, true, 1408643, 1794497⟩,
  ⟨"gd_merge12_uarb1.cons.nG", .cons, F_nG, v_gd_merge12_uarb1, false, 2232159, 4070482, true, 47493, 86606⟩,
  ⟨"gd_merge12_uarb1.cons.nA", .cons, F_nA, v_gd_merge12_uarb1, false, 116667, 165307, true, 2916691, 4132675⟩,
  ⟨"gd_merge12_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge12_uarb1, false, 4654719, 7807645, true, 4654743, 7807645⟩,
  ⟨"gd_merge12_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge12_uarb1, false, 161491, 478991, true, 645971, 1915964⟩,
  ⟨"gd_merge12_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge12_uarb1, false, 5963, 28463, false, 23853, 113852⟩,
  ⟨"gd_merge12_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge12_uarb1, false, 1770049, 2405049, true, 3540113, 4810098⟩,
  ⟨"gd_merge12_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge12_uarb1, false, 1685049, 2454049, true, 3370113, 4908098⟩,
  ⟨"gd_merge12_uarb1.cons.h12", .cons, F_h12, v_gd_merge12_uarb1, false, 649591, 1919591, true, 649599, 1919591⟩,
  ⟨"gd_merge12_uarb1.cons.h21", .cons, F_h21, v_gd_merge12_uarb1, false, 63197, 273197, false, 189599, 819591⟩,
  ⟨"gd_merge12_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge12_uarb1, false, 459592, 1997591, true, 459600, 1997591⟩,
  ⟨"gd_merge12_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge12_uarb1, false, 669592, 1939591, true, 669600, 1939591⟩,
  ⟨"gd_merge12_uarb2.lit.fork1", .lit, F_fork1, v_gd_merge12_uarb2, false, 358791, 527591, true, 1793968, 2637955⟩,
  ⟨"gd_merge12_uarb2.lit.fork2", .lit, F_fork2, v_gd_merge12_uarb2, false, 328293, 655793, true, 1313185, 2623172⟩,
  ⟨"gd_merge12_uarb2.lit.mP", .lit, F_mP, v_gd_merge12_uarb2, false, 743433, 1138969, true, 3717177, 5694845⟩,
  ⟨"gd_merge12_uarb2.lit.mG", .lit, F_mG, v_gd_merge12_uarb2, false, 3588255, 6329614, true, 3588267, 6329614⟩,
  ⟨"gd_merge12_uarb2.lit.mA", .lit, F_mA, v_gd_merge12_uarb2, false, 5086933, 6178933, true, 5086949, 6178933⟩,
  ⟨"gd_merge12_uarb2.lit.mGG", .lit, F_mGG, v_gd_merge12_uarb2, false, 4273139, 6149658, true, 4273151, 6149658⟩,
  ⟨"gd_merge12_uarb2.lit.nP", .lit, F_nP, v_gd_merge12_uarb2, false, 2055687, 2650318, true, 2055693, 2650318⟩,
  ⟨"gd_merge12_uarb2.lit.nG", .lit, F_nG, v_gd_merge12_uarb2, false, 3852202, 6209365, true, 3852214, 6209365⟩,
  ⟨"gd_merge12_uarb2.lit.nA", .lit, F_nA, v_gd_merge12_uarb2, false, 4325077, 5883077, true, 4325093, 5883077⟩,
  ⟨"gd_merge12_uarb2.lit.nGG", .lit, F_nGG, v_gd_merge12_uarb2, false, 2639369, 3897057, true, 2639377, 3897057⟩,
  ⟨"gd_merge12_uarb2.lit.rt1", .lit, F_rt1, v_gd_merge12_uarb2, false, 184459, 574493, true, 922302, 2872465⟩,
  ⟨"gd_merge12_uarb2.lit.rt1b", .lit, F_rt1b, v_gd_merge12_uarb2, false, 565197, 2745103, true, 565204, 2745103⟩,
  ⟨"gd_merge12_uarb2.lit.rt1s", .lit, F_rt1s, v_gd_merge12_uarb2, false, 525830, 720847, true, 1051663, 1441694⟩,
  ⟨"gd_merge12_uarb2.lit.rt1bs", .lit, F_rt1bs, v_gd_merge12_uarb2, false, 2450601, 3540554, true, 4901217, 7081108⟩,
  ⟨"gd_merge12_uarb2.lit.h12", .lit, F_h12, v_gd_merge12_uarb2, false, 456851, 1431936, true, 152285, 477312⟩,
  ⟨"gd_merge12_uarb2.lit.h21", .lit, F_h21, v_gd_merge12_uarb2, false, 278302, 1368255, true, 39758, 195465⟩,
  ⟨"gd_merge12_uarb2.lit.o1x", .lit, F_o1x, v_gd_merge12_uarb2, false, 112321, 548302, true, 561613, 2741510⟩,
  ⟨"gd_merge12_uarb2.lit.o2x", .lit, F_o2x, v_gd_merge12_uarb2, false, 908703, 2858872, true, 908711, 2858872⟩,
  ⟨"gd_merge12_uarb2.cons.fork1", .cons, F_fork1, v_gd_merge12_uarb2, false, 272391, 441191, true, 1361968, 2205955⟩,
  ⟨"gd_merge12_uarb2.cons.fork2", .cons, F_fork2, v_gd_merge12_uarb2, false, 232043, 559543, true, 928185, 2238172⟩,
  ⟨"gd_merge12_uarb2.cons.mP", .cons, F_mP, v_gd_merge12_uarb2, false, 586433, 981969, true, 2932177, 4909845⟩,
  ⟨"gd_merge12_uarb2.cons.mG", .cons, F_mG, v_gd_merge12_uarb2, false, 2755755, 5497114, true, 393681, 785302⟩,
  ⟨"gd_merge12_uarb2.cons.mA", .cons, F_mA, v_gd_merge12_uarb2, false, 4130933, 5222933, true, 4130949, 5222933⟩,
  ⟨"gd_merge12_uarb2.cons.mGG", .cons, F_mGG, v_gd_merge12_uarb2, false, 3394639, 5271158, true, 3394651, 5271158⟩,
  ⟨"gd_merge12_uarb2.cons.nP", .cons, F_nP, v_gd_merge12_uarb2, false, 1663187, 2257818, true, 1663193, 2257818⟩,
  ⟨"gd_merge12_uarb2.cons.nG", .cons, F_nG, v_gd_merge12_uarb2, false, 3004202, 5361365, true, 3004214, 5361365⟩,
  ⟨"gd_merge12_uarb2.cons.nA", .cons, F_nA, v_gd_merge12_uarb2, false, 3460077, 5018077, true, 3460093, 5018077⟩,
  ⟨"gd_merge12_uarb2.cons.nGG", .cons, F_nGG, v_gd_merge12_uarb2, false, 6266107, 10039171, true, 6266131, 10039171⟩,
  ⟨"gd_merge12_uarb2.cons.rt1", .cons, F_rt1, v_gd_merge12_uarb2, false, 108459, 498493, true, 542302, 2492465⟩,
  ⟨"gd_merge12_uarb2.cons.rt1b", .cons, F_rt1b, v_gd_merge12_uarb2, false, 83197, 969103, false, 83204, 969103⟩,
  ⟨"gd_merge12_uarb2.cons.rt1s", .cons, F_rt1s, v_gd_merge12_uarb2, false, 416430, 611447, true, 832863, 1222894⟩,
  ⟨"gd_merge12_uarb2.cons.rt1bs", .cons, F_rt1bs, v_gd_merge12_uarb2, false, 1921101, 3011054, true, 3842217, 6022108⟩,
  ⟨"gd_merge12_uarb2.cons.h12", .cons, F_h12, v_gd_merge12_uarb2, false, 271851, 1246936, true, 271855, 1246936⟩,
  ⟨"gd_merge12_uarb2.cons.h21", .cons, F_h21, v_gd_merge12_uarb2, false, 110302, 1200255, true, 15758, 171465⟩,
  ⟨"gd_merge12_uarb2.cons.o1x", .cons, F_o1x, v_gd_merge12_uarb2, false, 6503, 68786, true, 227613, 2407510⟩,
  ⟨"gd_merge12_uarb2.cons.o2x", .cons, F_o2x, v_gd_merge12_uarb2, false, 536703, 2486872, true, 536711, 2486872⟩,
  ⟨"gd_merge2_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge2_uarb1, false, 418287, 870287, true, 1254874, 2610861⟩,
  ⟨"gd_merge2_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge2_uarb1, false, 35539, 46379, true, 1776963, 2318950⟩,
  ⟨"gd_merge2_uarb1.lit.mP", .lit, F_mP, v_gd_merge2_uarb1, false, 43837, 48198, true, 1030171, 1132653⟩,
  ⟨"gd_merge2_uarb1.lit.mG", .lit, F_mG, v_gd_merge2_uarb1, false, 3126157, 3894187, true, 15630809, 19470935⟩,
  ⟨"gd_merge2_uarb1.lit.mA", .lit, F_mA, v_gd_merge2_uarb1, false, 824429, 984829, true, 4122153, 4924145⟩,
  ⟨"gd_merge2_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge2_uarb1, false, 15633719, 18902001, true, 15633743, 18902001⟩,
  ⟨"gd_merge2_uarb1.lit.nP", .lit, F_nP, v_gd_merge2_uarb1, false, 8056869, 9245711, true, 8056881, 9245711⟩,
  ⟨"gd_merge2_uarb1.lit.nG", .lit, F_nG, v_gd_merge2_uarb1, false, 14930209, 19325511, true, 14930233, 19325511⟩,
  ⟨"gd_merge2_uarb1.lit.nA", .lit, F_nA, v_gd_merge2_uarb1, false, 905829, 984829, true, 4529153, 4924145⟩,
  ⟨"gd_merge2_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge2_uarb1, false, 1593163, 1938609, true, 7965827, 9693045⟩,
  ⟨"gd_merge2_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge2_uarb1, false, 169, 693, false, 169007, 693000⟩,
  ⟨"gd_merge2_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge2_uarb1, false, 86, 343, false, 172007, 686000⟩,
  ⟨"gd_merge2_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge2_uarb1, false, 861529, 1026529, true, 1723061, 2053058⟩,
  ⟨"gd_merge2_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge2_uarb1, false, 867929, 1022729, true, 1735861, 2045458⟩,
  ⟨"gd_merge2_uarb1.lit.h12", .lit, F_h12, v_gd_merge2_uarb1, false, 619, 2494, true, 68091, 274340⟩,
  ⟨"gd_merge2_uarb1.lit.h21", .lit, F_h21, v_gd_merge2_uarb1, false, 2434, 8859, false, 24341, 88590⟩,
  ⟨"gd_merge2_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge2_uarb1, false, 578721, 2126720, true, 578729, 2126720⟩,
  ⟨"gd_merge2_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge2_uarb1, false, 573721, 2223720, true, 191243, 741240⟩,
  ⟨"gd_merge2_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge2_uarb1, false, 311861, 857861, false, 311874, 857861⟩,
  ⟨"gd_merge2_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge2_uarb1, false, 28039, 38879, true, 1401963, 1943950⟩,
  ⟨"gd_merge2_uarb1.cons.mP", .cons, F_mP, v_gd_merge2_uarb1, false, 1687089, 1892056, true, 421773, 473014⟩,
  ⟨"gd_merge2_uarb1.cons.mG", .cons, F_mG, v_gd_merge2_uarb1, false, 830719, 1086729, true, 4153603, 5433645⟩,
  ⟨"gd_merge2_uarb1.cons.mA", .cons, F_mA, v_gd_merge2_uarb1, false, 667729, 828129, true, 3338653, 4140645⟩,
  ⟨"gd_merge2_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge2_uarb1, false, 12648719, 15917001, true, 12648743, 15917001⟩,
  ⟨"gd_merge2_uarb1.cons.nP", .cons, F_nP, v_gd_merge2_uarb1, false, 6563869, 7752711, true, 6563881, 7752711⟩,
  ⟨"gd_merge2_uarb1.cons.nG", .cons, F_nG, v_gd_merge2_uarb1, false, 11968209, 16363511, true, 11968233, 16363511⟩,
  ⟨"gd_merge2_uarb1.cons.nA", .cons, F_nA, v_gd_merge2_uarb1, false, 728229, 807229, true, 3641153, 4036145⟩,
  ⟨"gd_merge2_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge2_uarb1, false, 1273663, 1619109, true, 6368327, 8095545⟩,
  ⟨"gd_merge2_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge2_uarb1, false, 101, 761, false, 101007, 761000⟩,
  ⟨"gd_merge2_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge2_uarb1, false, 5, 34, false, 6471, 44000⟩,
  ⟨"gd_merge2_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge2_uarb1, false, 232343, 287343, true, 464687, 574686⟩,
  ⟨"gd_merge2_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge2_uarb1, false, 234143, 285743, true, 468287, 571486⟩,
  ⟨"gd_merge2_uarb1.cons.h12", .cons, F_h12, v_gd_merge2_uarb1, false, 1203, 8078, true, 36091, 242340⟩,
  ⟨"gd_merge2_uarb1.cons.h21", .cons, F_h21, v_gd_merge2_uarb1, false, 1659, 9634, false, 16591, 96340⟩,
  ⟨"gd_merge2_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge2_uarb1, false, 131721, 769720, false, 131729, 769720⟩,
  ⟨"gd_merge2_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge2_uarb1, false, 308721, 1958720, true, 308729, 1958720⟩,
  ⟨"gd_merge3_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge3_uarb1, false, 502377, 831377, true, 2009521, 3325508⟩,
  ⟨"gd_merge3_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge3_uarb1, false, 651, 1087, true, 1953013, 3261000⟩,
  ⟨"gd_merge3_uarb1.lit.mP", .lit, F_mP, v_gd_merge3_uarb1, false, 955517, 1072641, true, 6688631, 7508487⟩,
  ⟨"gd_merge3_uarb1.lit.mG", .lit, F_mG, v_gd_merge3_uarb1, false, 1524797, 2100790, true, 152480, 210079⟩,
  ⟨"gd_merge3_uarb1.lit.mA", .lit, F_mA, v_gd_merge3_uarb1, false, 7094553, 8658553, true, 7094569, 8658553⟩,
  ⟨"gd_merge3_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge3_uarb1, false, 6302155, 8320193, true, 6302167, 8320193⟩,
  ⟨"gd_merge3_uarb1.lit.nP", .lit, F_nP, v_gd_merge3_uarb1, false, 865093, 1163065, true, 6055663, 8141455⟩,
  ⟨"gd_merge3_uarb1.lit.nG", .lit, F_nG, v_gd_merge3_uarb1, false, 19462, 27669, true, 1498577, 2130513⟩,
  ⟨"gd_merge3_uarb1.lit.nA", .lit, F_nA, v_gd_merge3_uarb1, false, 7102553, 8658553, true, 7102569, 8658553⟩,
  ⟨"gd_merge3_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge3_uarb1, false, 6517747, 8126601, true, 6517759, 8126601⟩,
  ⟨"gd_merge3_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge3_uarb1, false, 4352, 16019, false, 34817, 128152⟩,
  ⟨"gd_merge3_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge3_uarb1, false, 300097, 606597, true, 1200395, 2426388⟩,
  ⟨"gd_merge3_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge3_uarb1, false, 1069895, 1353231, true, 7489280, 9472617⟩,
  ⟨"gd_merge3_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge3_uarb1, false, 7915941, 9141941, true, 7915956, 9141941⟩,
  ⟨"gd_merge3_uarb1.lit.h12", .lit, F_h12, v_gd_merge3_uarb1, false, 381541, 1373217, true, 381545, 1373217⟩,
  ⟨"gd_merge3_uarb1.lit.h21", .lit, F_h21, v_gd_merge3_uarb1, false, 595379, 1208379, true, 198461, 402793⟩,
  ⟨"gd_merge3_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge3_uarb1, false, 1160759, 2386758, true, 1160767, 2386758⟩,
  ⟨"gd_merge3_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge3_uarb1, false, 264361, 925478, true, 793091, 2776434⟩,
  ⟨"gd_merge3_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge3_uarb1, false, 140627, 273627, false, 187507, 364836⟩,
  ⟨"gd_merge3_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge3_uarb1, false, 1493, 2801, true, 1493013, 2801000⟩,
  ⟨"gd_merge3_uarb1.cons.mP", .cons, F_mP, v_gd_merge3_uarb1, false, 5443619, 6263487, true, 5443631, 6263487⟩,
  ⟨"gd_merge3_uarb1.cons.mG", .cons, F_mG, v_gd_merge3_uarb1, false, 1188422, 1764415, true, 237685, 352883⟩,
  ⟨"gd_merge3_uarb1.cons.mA", .cons, F_mA, v_gd_merge3_uarb1, false, 5701553, 7265553, true, 1900523, 2421851⟩,
  ⟨"gd_merge3_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge3_uarb1, false, 5008155, 7026193, true, 5008167, 7026193⟩,
  ⟨"gd_merge3_uarb1.cons.nP", .cons, F_nP, v_gd_merge3_uarb1, false, 4810651, 6896455, true, 4810663, 6896455⟩,
  ⟨"gd_merge3_uarb1.cons.nG", .cons, F_nG, v_gd_merge3_uarb1, false, 1178074, 1810013, true, 1178077, 1810013⟩,
  ⟨"gd_merge3_uarb1.cons.nA", .cons, F_nA, v_gd_merge3_uarb1, false, 5582553, 7138553, true, 5582569, 7138553⟩,
  ⟨"gd_merge3_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge3_uarb1, false, 5160247, 6769101, true, 5160259, 6769101⟩,
  ⟨"gd_merge3_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge3_uarb1, false, 20964, 121633, false, 167719, 973064⟩,
  ⟨"gd_merge3_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge3_uarb1, false, 213097, 519597, true, 852395, 2078388⟩,
  ⟨"gd_merge3_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge3_uarb1, false, 5979265, 7962617, true, 5979280, 7962617⟩,
  ⟨"gd_merge3_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge3_uarb1, false, 6396941, 7622941, true, 6396956, 7622941⟩,
  ⟨"gd_merge3_uarb1.cons.h12", .cons, F_h12, v_gd_merge3_uarb1, false, 31363, 173031, true, 219545, 1211217⟩,
  ⟨"gd_merge3_uarb1.cons.h21", .cons, F_h21, v_gd_merge3_uarb1, false, 426879, 1039879, true, 426883, 1039879⟩,
  ⟨"gd_merge3_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge3_uarb1, false, 832759, 2058758, true, 64059, 158366⟩,
  ⟨"gd_merge3_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge3_uarb1, false, 153361, 814478, true, 460091, 2443434⟩,
  ⟨"gd_merge4_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge4_uarb1, false, 2287297, 3130957, true, 2287310, 3130957⟩,
  ⟨"gd_merge4_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge4_uarb1, false, 369797, 693297, true, 493067, 924396⟩,
  ⟨"gd_merge4_uarb1.lit.mP", .lit, F_mP, v_gd_merge4_uarb1, false, 7427747, 9478929, true, 7427759, 9478929⟩,
  ⟨"gd_merge4_uarb1.lit.mG", .lit, F_mG, v_gd_merge4_uarb1, false, 3455544, 4690715, true, 691110, 938143⟩,
  ⟨"gd_merge4_uarb1.lit.mA", .lit, F_mA, v_gd_merge4_uarb1, false, 2219821, 2492736, true, 2219825, 2492736⟩,
  ⟨"gd_merge4_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge4_uarb1, false, 15273713, 18411215, true, 15273737, 18411215⟩,
  ⟨"gd_merge4_uarb1.lit.nP", .lit, F_nP, v_gd_merge4_uarb1, false, 2991077, 3337599, false, 2991089, 3337599⟩,
  ⟨"gd_merge4_uarb1.lit.nG", .lit, F_nG, v_gd_merge4_uarb1, false, 718835, 883281, false, 718838, 883281⟩,
  ⟨"gd_merge4_uarb1.lit.nA", .lit, F_nA, v_gd_merge4_uarb1, false, 501712, 598087, true, 501713, 598087⟩,
  ⟨"gd_merge4_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge4_uarb1, false, 1400545, 1663731, true, 15406019, 18301041⟩,
  ⟨"gd_merge4_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge4_uarb1, false, 192597, 480097, true, 770395, 1920388⟩,
  ⟨"gd_merge4_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge4_uarb1, false, 267453, 875323, false, 267460, 875323⟩,
  ⟨"gd_merge4_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge4_uarb1, false, 188081, 213081, true, 8651741, 9801726⟩,
  ⟨"gd_merge4_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge4_uarb1, false, 3262791, 3870661, false, 3262806, 3870661⟩,
  ⟨"gd_merge4_uarb1.lit.h12", .lit, F_h12, v_gd_merge4_uarb1, false, 3983, 9733, true, 99576, 243325⟩,
  ⟨"gd_merge4_uarb1.lit.h21", .lit, F_h21, v_gd_merge4_uarb1, false, 58133, 179707, false, 290673, 898535⟩,
  ⟨"gd_merge4_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge4_uarb1, false, 97222, 299845, false, 291674, 899535⟩,
  ⟨"gd_merge4_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge4_uarb1, false, 826601, 1976600, true, 826609, 1976600⟩,
  ⟨"gd_merge4_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge4_uarb1, false, 596099, 877319, true, 1788310, 2631957⟩,
  ⟨"gd_merge4_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge4_uarb1, false, 273047, 596547, true, 364067, 795396⟩,
  ⟨"gd_merge4_uarb1.cons.mP", .cons, F_mP, v_gd_merge4_uarb1, false, 5874747, 7925929, true, 534069, 720539⟩,
  ⟨"gd_merge4_uarb1.cons.mG", .cons, F_mG, v_gd_merge4_uarb1, false, 2706044, 3941215, true, 541210, 788243⟩,
  ⟨"gd_merge4_uarb1.cons.mA", .cons, F_mA, v_gd_merge4_uarb1, false, 1787071, 2059986, true, 1787075, 2059986⟩,
  ⟨"gd_merge4_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge4_uarb1, false, 4058571, 5104405, true, 4058579, 5104405⟩,
  ⟨"gd_merge4_uarb1.cons.nP", .cons, F_nP, v_gd_merge4_uarb1, false, 2962077, 3366599, false, 2962089, 3366599⟩,
  ⟨"gd_merge4_uarb1.cons.nG", .cons, F_nG, v_gd_merge4_uarb1, false, 764980, 984453, true, 1529963, 1968906⟩,
  ⟨"gd_merge4_uarb1.cons.nA", .cons, F_nA, v_gd_merge4_uarb1, false, 133404, 165529, true, 400213, 496587⟩,
  ⟨"gd_merge4_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge4_uarb1, false, 12297995, 15193041, true, 12298019, 15193041⟩,
  ⟨"gd_merge4_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge4_uarb1, false, 129597, 417097, true, 518395, 1668388⟩,
  ⟨"gd_merge4_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge4_uarb1, false, 211453, 931323, false, 211460, 931323⟩,
  ⟨"gd_merge4_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge4_uarb1, false, 3478863, 4053863, true, 6957741, 8107726⟩,
  ⟨"gd_merge4_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge4_uarb1, false, 7097791, 8709661, true, 417518, 512333⟩,
  ⟨"gd_merge4_uarb1.cons.h12", .cons, F_h12, v_gd_merge4_uarb1, false, 2733, 8483, true, 68326, 212075⟩,
  ⟨"gd_merge4_uarb1.cons.h21", .cons, F_h21, v_gd_merge4_uarb1, false, 46933, 190907, false, 234673, 954535⟩,
  ⟨"gd_merge4_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge4_uarb1, false, 235666, 955535, false, 235674, 955535⟩,
  ⟨"gd_merge4_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge4_uarb1, false, 188867, 572200, true, 566609, 1716600⟩,
  ⟨"gd_merge6_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge6_uarb1, false, 224609, 572084, false, 449231, 1144168⟩,
  ⟨"gd_merge6_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge6_uarb1, false, 1621579, 3144219, true, 1621592, 3144219⟩,
  ⟨"gd_merge6_uarb1.lit.mP", .lit, F_mP, v_gd_merge6_uarb1, false, 1167673, 1663469, true, 1167676, 1663469⟩,
  ⟨"gd_merge6_uarb1.lit.mG", .lit, F_mG, v_gd_merge6_uarb1, false, 4825073, 7057686, true, 4825085, 7057686⟩,
  ⟨"gd_merge6_uarb1.lit.mA", .lit, F_mA, v_gd_merge6_uarb1, false, 1898067, 2627717, true, 5694217, 7883151⟩,
  ⟨"gd_merge6_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge6_uarb1, false, 3557885, 4467899, true, 3557893, 4467899⟩,
  ⟨"gd_merge6_uarb1.lit.nP", .lit, F_nP, v_gd_merge6_uarb1, false, 1540815, 2234041, true, 1540819, 2234041⟩,
  ⟨"gd_merge6_uarb1.lit.nG", .lit, F_nG, v_gd_merge6_uarb1, false, 1578923, 2395969, true, 1578927, 2395969⟩,
  ⟨"gd_merge6_uarb1.lit.nA", .lit, F_nA, v_gd_merge6_uarb1, false, 5630367, 7401007, true, 5630383, 7401007⟩,
  ⟨"gd_merge6_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge6_uarb1, false, 5240730, 6776029, true, 403134, 521233⟩,
  ⟨"gd_merge6_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge6_uarb1, false, 295097, 590597, true, 69435, 138964⟩,
  ⟨"gd_merge6_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge6_uarb1, false, 353597, 553097, true, 1414395, 2212388⟩,
  ⟨"gd_merge6_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge6_uarb1, false, 130639, 155264, true, 2090229, 2484224⟩,
  ⟨"gd_merge6_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge6_uarb1, false, 135514, 152139, true, 722743, 811408⟩,
  ⟨"gd_merge6_uarb1.lit.h12", .lit, F_h12, v_gd_merge6_uarb1, false, 5863, 11773, true, 146576, 294325⟩,
  ⟨"gd_merge6_uarb1.lit.h21", .lit, F_h21, v_gd_merge6_uarb1, false, 7033, 11023, true, 175826, 275575⟩,
  ⟨"gd_merge6_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge6_uarb1, false, 1374601, 2172600, true, 458203, 724200⟩,
  ⟨"gd_merge6_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge6_uarb1, false, 1204601, 2386600, true, 1204609, 2386600⟩,
  ⟨"gd_merge6_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge6_uarb1, false, 191109, 605584, false, 382231, 1211168⟩,
  ⟨"gd_merge6_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge6_uarb1, false, 1194579, 2717219, true, 1194592, 2717219⟩,
  ⟨"gd_merge6_uarb1.cons.mP", .cons, F_mP, v_gd_merge6_uarb1, false, 910423, 1406219, true, 910426, 1406219⟩,
  ⟨"gd_merge6_uarb1.cons.mG", .cons, F_mG, v_gd_merge6_uarb1, false, 3745573, 5978186, true, 3745585, 5978186⟩,
  ⟨"gd_merge6_uarb1.cons.mA", .cons, F_mA, v_gd_merge6_uarb1, false, 1489067, 2218717, true, 4467217, 6656151⟩,
  ⟨"gd_merge6_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge6_uarb1, false, 2827885, 3737899, true, 2827893, 3737899⟩,
  ⟨"gd_merge6_uarb1.cons.nP", .cons, F_nP, v_gd_merge6_uarb1, false, 1197815, 1891041, true, 399273, 630347⟩,
  ⟨"gd_merge6_uarb1.cons.nG", .cons, F_nG, v_gd_merge6_uarb1, false, 1217423, 2034469, true, 1217427, 2034469⟩,
  ⟨"gd_merge6_uarb1.cons.nA", .cons, F_nA, v_gd_merge6_uarb1, false, 4450367, 6221007, true, 494487, 691223⟩,
  ⟨"gd_merge6_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge6_uarb1, false, 4147730, 5683029, true, 4147742, 5683029⟩,
  ⟨"gd_merge6_uarb1.cons.rt1", .cons, F_rt1, v_gd_merge6_uarb1, false, 70449, 168949, true, 845395, 2027388⟩,
  ⟨"gd_merge6_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge6_uarb1, false, 266347, 465847, true, 1065395, 1863388⟩,
  ⟨"gd_merge6_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge6_uarb1, false, 627209, 774959, true, 5017687, 6199672⟩,
  ⟨"gd_merge6_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge6_uarb1, false, 654709, 754459, true, 5237687, 6035672⟩,
  ⟨"gd_merge6_uarb1.cons.h12", .cons, F_h12, v_gd_merge6_uarb1, false, 1411, 3381, true, 15118, 36225⟩,
  ⟨"gd_merge6_uarb1.cons.h21", .cons, F_h21, v_gd_merge6_uarb1, false, 2669, 4664, true, 133451, 233200⟩,
  ⟨"gd_merge6_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge6_uarb1, false, 1046601, 1844600, true, 1046609, 1844600⟩,
  ⟨"gd_merge6_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge6_uarb1, false, 123943, 292800, true, 289203, 683200⟩,
  ⟨"gd_merge9_uarb1.lit.fork1", .lit, F_fork1, v_gd_merge9_uarb1, false, 1291389, 2579389, true, 1291402, 2579389⟩,
  ⟨"gd_merge9_uarb1.lit.fork2", .lit, F_fork2, v_gd_merge9_uarb1, false, 2137739, 3668607, true, 237528, 407623⟩,
  ⟨"gd_merge9_uarb1.lit.mP", .lit, F_mP, v_gd_merge9_uarb1, false, 5048388, 6065225, true, 5048394, 6065225⟩,
  ⟨"gd_merge9_uarb1.lit.mG", .lit, F_mG, v_gd_merge9_uarb1, false, 2421750, 3006313, true, 2421753, 3006313⟩,
  ⟨"gd_merge9_uarb1.lit.mA", .lit, F_mA, v_gd_merge9_uarb1, false, 21487, 24687, true, 644611, 740610⟩,
  ⟨"gd_merge9_uarb1.lit.mGG", .lit, F_mGG, v_gd_merge9_uarb1, false, 3265164, 3746969, true, 3265168, 3746969⟩,
  ⟨"gd_merge9_uarb1.lit.nP", .lit, F_nP, v_gd_merge9_uarb1, false, 4992874, 6120739, true, 4992880, 6120739⟩,
  ⟨"gd_merge9_uarb1.lit.nG", .lit, F_nG, v_gd_merge9_uarb1, false, 1039979, 1332732, true, 3119941, 3998196⟩,
  ⟨"gd_merge9_uarb1.lit.nA", .lit, F_nA, v_gd_merge9_uarb1, false, 5956733, 6846167, true, 5956741, 6846167⟩,
  ⟨"gd_merge9_uarb1.lit.nGG", .lit, F_nGG, v_gd_merge9_uarb1, false, 5161835, 5977291, true, 5161841, 5977291⟩,
  ⟨"gd_merge9_uarb1.lit.rt1", .lit, F_rt1, v_gd_merge9_uarb1, false, 61, 696, true, 40669, 464000⟩,
  ⟨"gd_merge9_uarb1.lit.rt1b", .lit, F_rt1b, v_gd_merge9_uarb1, false, 21, 106, false, 126007, 636000⟩,
  ⟨"gd_merge9_uarb1.lit.rt1s", .lit, F_rt1s, v_gd_merge9_uarb1, false, 10572613, 11842613, true, 10572628, 11842613⟩,
  ⟨"gd_merge9_uarb1.lit.rt1bs", .lit, F_rt1bs, v_gd_merge9_uarb1, false, 10867613, 12423613, true, 10867628, 12423613⟩,
  ⟨"gd_merge9_uarb1.lit.h12", .lit, F_h12, v_gd_merge9_uarb1, false, 220487, 855487, true, 220491, 855487⟩,
  ⟨"gd_merge9_uarb1.lit.h21", .lit, F_h21, v_gd_merge9_uarb1, false, 349487, 1127487, true, 116497, 375829⟩,
  ⟨"gd_merge9_uarb1.lit.o1x", .lit, F_o1x, v_gd_merge9_uarb1, false, 702975, 2258974, true, 702983, 2258974⟩,
  ⟨"gd_merge9_uarb1.lit.o2x", .lit, F_o2x, v_gd_merge9_uarb1, false, 436975, 1706974, true, 436983, 1706974⟩,
  ⟨"gd_merge9_uarb1.cons.fork1", .cons, F_fork1, v_gd_merge9_uarb1, false, 923389, 2211389, true, 923402, 2211389⟩,
  ⟨"gd_merge9_uarb1.cons.fork2", .cons, F_fork2, v_gd_merge9_uarb1, false, 1675739, 3206607, true, 558584, 1068869⟩,
  ⟨"gd_merge9_uarb1.cons.mP", .cons, F_mP, v_gd_merge9_uarb1, false, 4141888, 5158725, true, 4141894, 5158725⟩,
  ⟨"gd_merge9_uarb1.cons.mG", .cons, F_mG, v_gd_merge9_uarb1, false, 282750, 366259, true, 1979253, 2563813⟩,
  ⟨"gd_merge9_uarb1.cons.mA", .cons, F_mA, v_gd_merge9_uarb1, false, 6617, 7817, true, 529361, 625360⟩,
  ⟨"gd_merge9_uarb1.cons.mGG", .cons, F_mGG, v_gd_merge9_uarb1, false, 8070992, 9516407, true, 8071004, 9516407⟩,
  ⟨"gd_merge9_uarb1.cons.nP", .cons, F_nP, v_gd_merge9_uarb1, false, 4086374, 5214239, true, 4086380, 5214239⟩,
  ⟨"gd_merge9_uarb1.cons.nG", .cons, F_nG, v_gd_merge9_uarb1, false, 2534437, 3412696, true, 362063, 487528⟩,
  ⟨"gd_merge9_uarb1.cons.nA", .cons, F_nA, v_gd_merge9_uarb1, false, 4914733, 5804167, true, 4914741, 5804167⟩,
  ⟨"gd_merge9_uarb1.cons.nGG", .cons, F_nGG, v_gd_merge9_uarb1, false, 4248835, 5064291, true, 4248841, 5064291⟩,
  R_gd_merge9_uarb1_cons_rt1,
  ⟨"gd_merge9_uarb1.cons.rt1b", .cons, F_rt1b, v_gd_merge9_uarb1, false, 32, 349, false, 64007, 698000⟩,
  ⟨"gd_merge9_uarb1.cons.rt1s", .cons, F_rt1s, v_gd_merge9_uarb1, false, 8745613, 10015613, true, 8745628, 10015613⟩,
  ⟨"gd_merge9_uarb1.cons.rt1bs", .cons, F_rt1bs, v_gd_merge9_uarb1, false, 8950613, 10506613, true, 8950628, 10506613⟩,
  ⟨"gd_merge9_uarb1.cons.h12", .cons, F_h12, v_gd_merge9_uarb1, false, 126987, 761987, true, 126991, 761987⟩,
  ⟨"gd_merge9_uarb1.cons.h21", .cons, F_h21, v_gd_merge9_uarb1, false, 215487, 993487, true, 215491, 993487⟩,
  ⟨"gd_merge9_uarb1.cons.o1x", .cons, F_o1x, v_gd_merge9_uarb1, false, 436975, 1992974, true, 436983, 1992974⟩,
  ⟨"gd_merge9_uarb1.cons.o2x", .cons, F_o2x, v_gd_merge9_uarb1, false, 247975, 1517974, true, 247983, 1517974⟩
]


/-! ## 7. Every row decided -/

/-- All 1296 rows: 36 arbiters × {lit, cons} × 18 conditions. -/
def rows : List Row := rows_g2 ++ rows_g3 ++ rows_g4 ++ rows_gd

theorem rows_g2_ok : rows_g2.all Row.ok = true := by decide +kernel
theorem rows_g3_ok : rows_g3.all Row.ok = true := by decide +kernel
theorem rows_g4_ok : rows_g4.all Row.ok = true := by decide +kernel
theorem rows_gd_ok : rows_gd.all Row.ok = true := by decide +kernel

theorem rows_length : rows.length = 1296 := by decide +kernel

/-- **Every row's certificates check** (κ\* safe side, κu unsafe side, H_DISJ). -/
theorem rows_ok : ∀ r ∈ rows, r.ok = true := by
  intro r hr
  simp only [rows, List.mem_append] at hr
  rcases hr with ((h | h) | h) | h
  · exact List.all_eq_true.1 rows_g2_ok r h
  · exact List.all_eq_true.1 rows_g3_ok r h
  · exact List.all_eq_true.1 rows_g4_ok r h
  · exact List.all_eq_true.1 rows_gd_ok r h

/-- The headline per row: safe for κ ≤ κ\*, unsafe for κ ≥ κu (≤ 1.8e-5 above κ\*). -/
theorem row_verdict (r : Row) (hr : r ∈ rows) :
    (r.neg = false → ∀ k : Kappa, k.num * r.q ≤ k.den * r.p →
        AllOK (model k r.rd r.f r.v) r.f.P r.f.Q r.f.a r.f.b) ∧
    (∀ k : Kappa, k.den * r.pu ≤ k.num * r.qu →
        ∃ d : E → Nat, (model k r.rd r.f r.v).Realizes d ∧
          pathDelay d r.f.Q + r.f.b < pathDelay d r.f.P + r.f.a) :=
  ⟨fun hn k hk => row_safe r (rows_ok r hr) hn k hk,
   fun k hk => row_unsafe_ex r (rows_ok r hr) k hk⟩

/-- The gap κu − κ\* is below 10⁻⁴ on every row that passes at κ = 0 (it is ≤ 1.8e-5). -/
theorem rows_gap : rows.all (fun r => r.neg || decide (r.pu * r.q * 10000 ≤ r.p * r.qu * 10000 + r.q * r.qu)) = true := by
  decide +kernel

/-! ## 8. The design minimum -/

/-- `lit` reading, every condition: no row fails at κ = 0, and every κ\* is at least
16587/374773 (attained by g3_merge12_uarb1.lit.rt1b). -/
theorem lit_min : rows.all (fun r => r.rd != .lit ||
    (!r.neg && decide (16587 * r.q ≤ r.p * 374773))) = true := by decide +kernel

/-- `lit`, the conditions with the server credited (RT1/RT1b with H_SERVER_GRAPH and the
A0 branch, i.e. without the server-free `rt1`/`rt1b` forms): every κ\* ≥
138217/1724217 (attained by g2_merge3_uarb1.lit.h21). -/
theorem lit_srv_min : rows.all (fun r => r.rd != .lit || r.f.sf ||
    (!r.neg && decide (138217 * r.q ≤ r.p * 1724217))) = true := by decide +kernel

theorem mem_of_all {l : List Row} {P : Row → Bool} (h : l.all P = true) {r : Row} (hr : r ∈ l) :
    P r = true := List.all_eq_true.1 h r hr

/-- **Design headline (lit).** For every κ ≤ 16587/374773 ≈ 0.0443, every gcd_hw
arbiter condition in this file (both forks, RT2/RT2b with H_SERVER_GRAPH, RT1/RT1b server-free,
the ArbPin2 handover / opposite-sense margins) holds on every realization of A's model. -/
theorem design_lit_safe (k : Kappa) (H_KAPPA : k.num * 374773 ≤ k.den * 16587) :
    ∀ r ∈ rows, r.rd = .lit → AllOK (model k r.rd r.f r.v) r.f.P r.f.Q r.f.a r.f.b := by
  intro r hr hl
  have h := mem_of_all lit_min hr
  simp only [hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  exact row_safe r (rows_ok r hr) h.1 k (frac_trans (by decide) H_KAPPA h.2)

/-- **And it is tight**: the minimising row fails from its κu on. -/
theorem design_lit_tight :
    R_g3_merge12_uarb1_lit_rt1b ∈ rows ∧ R_g3_merge12_uarb1_lit_rt1b.rd = .lit ∧ R_g3_merge12_uarb1_lit_rt1b.p = 16587 ∧
      R_g3_merge12_uarb1_lit_rt1b.q = 374773 ∧
    ∀ k : Kappa, k.den * R_g3_merge12_uarb1_lit_rt1b.pu ≤ k.num * R_g3_merge12_uarb1_lit_rt1b.qu →
      ¬ AllOK (model k .lit R_g3_merge12_uarb1_lit_rt1b.f R_g3_merge12_uarb1_lit_rt1b.v) R_g3_merge12_uarb1_lit_rt1b.f.P
        R_g3_merge12_uarb1_lit_rt1b.f.Q R_g3_merge12_uarb1_lit_rt1b.f.a R_g3_merge12_uarb1_lit_rt1b.f.b := by
  have hm : R_g3_merge12_uarb1_lit_rt1b ∈ rows := List.mem_of_getElem? (i := 407) rfl
  exact ⟨hm, rfl, rfl, rfl, fun k hk => row_unsafe _ (rows_ok _ hm) k hk⟩

/-- **cons reading: 5 rows fail already at κ = 0** (within-corner ranges), so they fail
at every κ. -/
theorem cons_neg : ∀ r ∈ [R_g2_merge3_uarb1_cons_rt1b, R_g2_merge3_uarb1_cons_h21, R_g2_merge3_uarb1_cons_o1x, R_g3_merge12_uarb1_cons_rt1b, R_gd_merge9_uarb1_cons_rt1], r ∈ rows ∧ r.rd = .cons ∧ r.neg = true ∧
    ∀ k : Kappa, ∃ d : E → Nat, (model k r.rd r.f r.v).Realizes d ∧
      pathDelay d r.f.Q + r.f.b < pathDelay d r.f.P + r.f.a := by
  intro r hr
  have hm : r.rd = .cons ∧ r.neg = true ∧ r.pu = 0 := by
    revert r; decide +kernel
  have hmem : r ∈ rows := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h <;> subst h
    · exact List.mem_of_getElem? (i := 209) rfl
    · exact List.mem_of_getElem? (i := 213) rfl
    · exact List.mem_of_getElem? (i := 214) rfl
    · exact List.mem_of_getElem? (i := 425) rfl
    · exact List.mem_of_getElem? (i := 1288) rfl
  refine ⟨hmem, hm.1, hm.2.1, fun k => row_unsafe_ex r (rows_ok r hmem) k ?_⟩
  rw [hm.2.2, Nat.mul_zero]; exact Nat.zero_le _

/-! ## 9. Bridges to the gate-level theorems (lit: ONE corner model per arbiter)

In the `lit` reading an arc's endpoints do not depend on the form, so one realization `d` of
`litModel k v` (one shared corner, every arc within κ) is a delay assignment for ALL of the
arbiter's conditions at once. Each bridge turns a form that holds at `d` into the source
file's gate-level theorem on the record built from `d`. -/

/-- The `lit` reading as one corner model per arbiter. -/
def litModel (k : Kappa) (v : E → Quad) : CornerModel E := ⟨fun e => mkArc (v e).1 (v e).2.2.2, k⟩

theorem model_lit (k : Kappa) (f : Form) (v : E → Quad) : model k .lit f v = litModel k v := rfl

/-- The form at one assignment. -/
def holds (d : E → Nat) (f : Form) : Prop := pathDelay d f.P + f.a ≤ pathDelay d f.Q + f.b

/-- Bar's record (`OnGcdArbA0.X`) of an assignment; `ag2` is ugrant O6 read from the q pin. -/
def xOf (d : E → Nat) : OnGcdArbA0.X :=
  { ac := d .ac, dS1 := d .dS1, dS2 := d .dS2, d12 := d .d12, es := d .es, e1 := d .e1,
    e2 := d .e2, ps := d .ps, p1 := d .p1, p2 := d .p2, cq := d .cq, qs := d .qs, qgw := d .qgw,
    pqg := d .pqg, rs1 := d .rs1, rg1 := d .rg1, rs2 := d .rs2, rg2 := d .rg2, gw1 := d .gw1,
    pg1 := d .pg1, gw2 := d .gw2, pg2 := d .pg2, fa1 := d .fa1, fa2 := d .fa2, aq := d .aq,
    aRq := d .aRq, aR1 := d .aR1, aR2 := d .aR2, ag1q := d .ag1q, ag1r := d .ag1r, ag2 := d .ag2,
    ac1 := d .ac1, ac2 := d .ac2 }

/-- The same with ugrant's O6 at its r2-pin delay (`Real7` has one flat O6 arc; RT2b's margins
read only the r2 pin of O6). -/
def xOfB (d : E → Nat) : OnGcdArbA0.X := { xOf d with ag2 := d .ag2r }

theorem xle_refl (x : OnGcdArbA0.X) : x.le x := by
  unfold OnGcdArbA0.X.le; omega

/-! ### A0 fork (OnGcdArbA0, 7g exact) -/

theorem fork1_gate (d : E → Nat) (h : holds d F_fork1)
    (H_LOOP_ST : 0 < d .aq + d .cq + d .qs) (H_LOOP_UA : 0 < d .ac1 + d .fa1) :
    OnGcdArbA0.Safe1 (xOf d) := by
  have hm : 0 ≤ OnGcdArbA0.fm1 (xOf d) (xOf d) := by
    simp only [holds, F_fork1, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
    simp only [OnGcdArbA0.fm1, OnGcdArbA0.early1, OnGcdArbA0.late1, xOf]; omega
  exact (OnGcdArbA0.fork1_box_iff (xOf d) (xOf d) (xle_refl _) H_LOOP_ST H_LOOP_UA).2 hm (xOf d)
    ⟨xle_refl _, xle_refl _⟩

theorem fork2_gate (d : E → Nat) (h : holds d F_fork2)
    (H_LOOP_ST : 0 < d .aq + d .cq + d .qs) (H_LOOP_UA : 0 < d .ac2 + d .fa2) :
    OnGcdArbA0.Safe2 (xOf d) := by
  have hm : 0 ≤ OnGcdArbA0.fm2 (xOf d) (xOf d) := by
    simp only [holds, F_fork2, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
    simp only [OnGcdArbA0.fm2, OnGcdArbA0.early2, OnGcdArbA0.late2, xOf]; omega
  exact (OnGcdArbA0.fork2_box_iff (xOf d) (xOf d) (xle_refl _) H_LOOP_ST H_LOOP_UA).2 hm (xOf d)
    ⟨xle_refl _, xle_refl _⟩

/-! ### RT2 / RT2b (OnGcdArbA0, 7h/7j arc form) with H_SERVER_GRAPH as the arc `srv` -/

/-- Ack exclusion across a client-1 release for every 7h record realising `xOf d` whose server
answers no faster than the realised server path (`d srv ≤ smin`, H_SERVER_GRAPH). -/
theorem rt2_gate (d : E → Nat) (hP : holds d F_mP) (hG : holds d F_mG) (hA : holds d F_mA)
    (hGG : holds d F_mGG) (hF : holds d F_fork2) {D : ArbHeldTimed.Dl} {s : ArbHeldTimed.Sigs}
    {t0 ta TA TA2 Hz : Int} (h : OnGcdArbA0.Real7 (xOf d) D)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin) (R : ArbHeldTimed.Run D s)
    (S : ArbHeldTimed.Scn D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  simp only [holds, F_mP, F_mG, F_mA, F_mGG, F_fork2, pathDelay, List.map, List.sum_cons,
    List.sum_nil] at hP hG hA hGG hF
  have e : 0 ≤ OnGcdArbA0.mP (xOf d) + D.smin ∧ 0 ≤ OnGcdArbA0.mG (xOf d) + 2 * D.smin ∧
      0 ≤ OnGcdArbA0.mA (xOf d) + D.smin ∧ 0 ≤ OnGcdArbA0.mGG (xOf d) + 2 * D.smin := by
    simp only [OnGcdArbA0.mP, OnGcdArbA0.mG, OnGcdArbA0.mA, OnGcdArbA0.mGG, OnGcdArbA0.Rsrv,
      OnGcdArbA0.As, OnGcdArbA0.A1r, OnGcdArbA0.A2r, xOf]
    omega
  have f : 0 ≤ OnGcdArbA0.mF (xOf d) := by
    simp only [OnGcdArbA0.mF, OnGcdArbA0.As, OnGcdArbA0.A2r, xOf]; omega
  exact ArbHeldTimed.rt2_exclusion_arcs R S ((OnGcdArbA0.rt2_iff _ D h).2 e)
    ((OnGcdArbA0.a0fork_iff _ D h).2 f)

/-- Ack exclusion across a client-2 release (7j), same hypotheses. -/
theorem rt2b_gate (d : E → Nat) (hP : holds d F_nP) (hG : holds d F_nG) (hA : holds d F_nA)
    (hGG : holds d F_nGG) (hF : holds d F_fork1) {D : ArbHeldTimed.Dl} {s : ArbHeldTimed.Sigs}
    {t0 ta TA TA2 Hz : Int} (h : OnGcdArbA0.Real7 (xOfB d) D)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin) (R : ArbHeldTimed.Run D s)
    (S : ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  simp only [holds, F_nP, F_nG, F_nA, F_nGG, F_fork1, pathDelay, List.map, List.sum_cons,
    List.sum_nil] at hP hG hA hGG hF
  have e : 0 ≤ OnGcdArbA0.nP (xOfB d) + D.smin ∧ 0 ≤ OnGcdArbA0.nG (xOfB d) + 2 * D.smin ∧
      0 ≤ OnGcdArbA0.nA (xOfB d) + D.smin ∧ 0 ≤ OnGcdArbA0.nGG (xOfB d) + 2 * D.smin := by
    simp only [OnGcdArbA0.nP, OnGcdArbA0.nG, OnGcdArbA0.nA, OnGcdArbA0.nGG, OnGcdArbA0.Rsrv,
      OnGcdArbA0.As, OnGcdArbA0.A1r, OnGcdArbA0.A2r, xOfB, xOf]
    omega
  have f : 0 ≤ OnGcdArbA0.nF (xOfB d) := by
    simp only [OnGcdArbA0.nF, OnGcdArbA0.As, OnGcdArbA0.A1r, xOfB, xOf]; omega
  exact ArbHeldTimed2.rt2_exclusion2_arcs R S ((OnGcdArbA0.rt2b_iff _ D h).2 e)
    ((OnGcdArbA0.a0fork2_iff _ D h).2 f)

/-! ### RT1 / RT1b (OnGcdArbFix, 7h/7j) -/

/-- Bag's record (`OnGcdArbFix.Q`) of an assignment. -/
def qOf (d : E → Nat) : OnGcdArbFix.Q :=
  ⟨(d .qgw + d .pqg : Nat), d .rg1, d .rs1, d .ag1r, d .aR1, d .ag1q, d .rg2, d .rs2, d .ag2r,
    d .aR2, d .ag2⟩

/-- Grant exclusion across a client-1 release, every server, any A0 branch (server-free form). -/
theorem rt1_gate (d : E → Nat) (h : holds d F_rt1) {cr cq : Int} {D : ArbHeldTimed.Dl}
    {s : ArbHeldTimed.Sigs} {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real1 (qOf d) cr cq D)
    (R : ArbHeldTimed.Run D s) (S : ArbHeldTimed.Scn D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  simp only [holds, F_rt1, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  have hn := D.H_NONNEG; have hrf := D.H_RISE_LE_FALL; have hc := hr.1
  refine ArbHeldTimed.rt1_exclusion R S ((OnGcdArbFix.rt1_iff _ cr cq D hr).2 (Or.inl ?_))
  simp only [OnGcdArbFix.Q.m1, qOf]; omega

theorem rt1b_gate (d : E → Nat) (h : holds d F_rt1b) {cr cq : Int} {D : ArbHeldTimed.Dl}
    {s : ArbHeldTimed.Sigs} {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real2 (qOf d) cr cq D)
    (R : ArbHeldTimed.Run D s) (S : ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  simp only [holds, F_rt1b, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  have hn := D.H_NONNEG; have hrf := D.H_RISE_LE_FALL; have hc := hr.1
  refine ArbHeldTimed2.rt1_exclusion2 R S ((OnGcdArbFix.rt1b_iff _ cr cq D hr).2 (Or.inl ?_))
  simp only [OnGcdArbFix.Q.m2, qOf]; omega

/-- RT1 with the A0 branch and the server credited: the record's A0 route to ustate, ustate's
O6 fall arc and q prefix are the realised ones, and the server answers no faster than the
realised `srv` path (H_SERVER_GRAPH). -/
theorem rt1s_gate (d : E → Nat) (h : holds d F_rt1s) {cr : Int} {D : ArbHeldTimed.Dl}
    {s : ArbHeldTimed.Sigs} {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real1 (qOf d) cr (d .cq) D)
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps) (hq : D.qf = d .aq)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin)
    (R : ArbHeldTimed.Run D s) (S : ArbHeldTimed.Scn D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  simp only [holds, F_rt1s, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  refine ArbHeldTimed.rt1_exclusion R S ((OnGcdArbFix.rt1_iff _ cr _ D hr).2 (Or.inl ?_))
  simp only [OnGcdArbFix.Q.m1, qOf]; rw [hA, hq]; omega

theorem rt1bs_gate (d : E → Nat) (h : holds d F_rt1bs) {cr : Int} {D : ArbHeldTimed.Dl}
    {s : ArbHeldTimed.Sigs} {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real2 (qOf d) cr (d .cq) D)
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps) (hq : D.qr = d .aq)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin)
    (R : ArbHeldTimed.Run D s) (S : ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  simp only [holds, F_rt1bs, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  refine ArbHeldTimed2.rt1_exclusion2 R S ((OnGcdArbFix.rt1b_iff _ cr _ D hr).2 (Or.inl ?_))
  simp only [OnGcdArbFix.Q.m2, qOf]; rw [hA, hq]; omega

/-! ### ArbPin2: the bare-cell race on the point box of one realization -/

/-- ArbPin's box of one realization (every window of width 0: fixed delays). -/
def boxOf (d : E → Nat) : ArbPin.Box :=
  let a1 : Int := d .rs1 + d .aq
  let a2 : Int := d .rs2 + d .aq
  let l : Int := d .cq + d .qs + d .aq
  let b1 : Int := d .rg1 + d .ag1r
  let b2 : Int := d .rg2 + d .ag2r
  let c5 : Int := d .cq + d .qgw + d .pqg + d .ag1q
  let c6 : Int := d .cq + d .qgw + d .pqg + d .ag2
  ⟨a1, a1, a2, a2, l, l, b1, b1, b2, b2, c5, c5, c6, c6⟩

theorem boxOf_ok (d : E → Nat) (H_LOOP_Q : 0 < d .cq + d .qs + d .aq) : (boxOf d).Ok := by
  simp only [ArbPin.Box.Ok, boxOf]; omega

theorem h12_gate (d : E → Nat) (h : holds d F_h12) (H_LOOP_Q : 0 < d .cq + d .qs + d .aq)
    {f : Int} (hf : 0 ≤ f) : ∀ c : ArbPin.Cell (boxOf d) true (ArbPin.dn f) ArbPin.hi1, ArbPin.Excl c := by
  simp only [holds, F_h12, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  exact ArbPin2.h12_kappa (boxOf_ok d H_LOOP_Q) (by simp only [boxOf]; omega) hf

theorem h21_gate (d : E → Nat) (h : holds d F_h21) (H_LOOP_Q : 0 < d .cq + d .qs + d .aq)
    {f : Int} (hf : 0 ≤ f) : ∀ c : ArbPin.Cell (boxOf d) false ArbPin.hi1 (ArbPin.dn f), ArbPin.Excl c := by
  simp only [holds, F_h21, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  exact ArbPin2.h21_kappa (boxOf_ok d H_LOOP_Q) (by simp only [boxOf]; omega) hf

theorem o1_gate (d : E → Nat) (h5 : holds d F_h21) (h6 : holds d F_o1x)
    (H_LOOP_Q : 0 < d .cq + d .qs + d .aq) {e1 e2 : Int} (he1 : 0 ≤ e1) :
    ∀ c : ArbPin.Cell (boxOf d) false (ArbPin.up e1) (ArbPin.dn e2), ArbPin.Excl c := by
  simp only [holds, F_h21, F_o1x, pathDelay, List.map, List.sum_cons, List.sum_nil] at h5 h6
  exact ArbPin2.o1_kappa (boxOf_ok d H_LOOP_Q) (by simp only [boxOf]; omega)
    (by simp only [boxOf]; omega) he1

theorem o2_gate (d : E → Nat) (h6 : holds d F_h12) (h5 : holds d F_o2x)
    (H_LOOP_Q : 0 < d .cq + d .qs + d .aq) {e1 e2 : Int} (he2 : 0 ≤ e2) :
    ∀ c : ArbPin.Cell (boxOf d) true (ArbPin.dn e1) (ArbPin.up e2), ArbPin.Excl c := by
  simp only [holds, F_h12, F_o2x, pathDelay, List.map, List.sum_cons, List.sum_nil] at h5 h6
  exact ArbPin2.o2_kappa (boxOf_ok d H_LOOP_Q) (by simp only [boxOf]; omega)
    (by simp only [boxOf]; omega) he2

/-! ## 10. Design corollary at the gate level (lit) -/

/-- The 36 routed gcd_hw arbiters. -/
def arbs : List (E → Quad) := [v_g2_merge10_uarb1, v_g2_merge11_uarb1, v_g2_merge12_uarb1, v_g2_merge12_uarb2, v_g2_merge2_uarb1, v_g2_merge3_uarb1, v_g2_merge4_uarb1, v_g2_merge6_uarb1, v_g2_merge9_uarb1, v_g3_merge10_uarb1, v_g3_merge11_uarb1, v_g3_merge12_uarb1, v_g3_merge12_uarb2, v_g3_merge2_uarb1, v_g3_merge3_uarb1, v_g3_merge4_uarb1, v_g3_merge6_uarb1, v_g3_merge9_uarb1, v_g4_merge10_uarb1, v_g4_merge11_uarb1, v_g4_merge12_uarb1, v_g4_merge12_uarb2, v_g4_merge2_uarb1, v_g4_merge3_uarb1, v_g4_merge4_uarb1, v_g4_merge6_uarb1, v_g4_merge9_uarb1, v_gd_merge10_uarb1, v_gd_merge11_uarb1, v_gd_merge12_uarb1, v_gd_merge12_uarb2, v_gd_merge2_uarb1, v_gd_merge3_uarb1, v_gd_merge4_uarb1, v_gd_merge6_uarb1, v_gd_merge9_uarb1]

/-- All 18 conditions; `formsSrv` drops the server-free `rt1`/`rt1b` (RT1 then via `rt1s`). -/
def forms : List Form := [F_fork1, F_fork2, F_mP, F_mG, F_mA, F_mGG, F_nP, F_nG, F_nA, F_nGG,
  F_rt1, F_rt1b, F_rt1s, F_rt1bs, F_h12, F_h21, F_o1x, F_o2x]

/-- The design minimum certifies every (arbiter, condition) pair directly (lit). -/
theorem arbs_cert : arbs.all (fun v => forms.all (fun f =>
    certFor .lit f v 16587 374773)) = true := by decide +kernel

theorem arbs_cert_srv : arbs.all (fun v => forms.all (fun f => f.sf ||
    certFor .lit f v 138217 1724217)) = true := by decide +kernel

theorem arbs_length : arbs.length = 36 := rfl

theorem lit_holds {v : E → Quad} (hv : v ∈ arbs) {f : Form} (hf : f ∈ forms) (k : Kappa)
    (H_KAPPA : k.num * 374773 ≤ k.den * 16587) {d : E → Nat}
    (hd : (litModel k v).Realizes d) : holds d f := by
  have hc := List.all_eq_true.1 (List.all_eq_true.1 arbs_cert v hv) f hf
  exact form_safe (by decide) hc k H_KAPPA d hd

theorem lit_holds_srv {v : E → Quad} (hv : v ∈ arbs) {f : Form} (hf : f ∈ forms)
    (hs : f.sf = false) (k : Kappa) (H_KAPPA : k.num * 1724217 ≤ k.den * 138217)
    {d : E → Nat} (hd : (litModel k v).Realizes d) : holds d f := by
  have hc := List.all_eq_true.1 (List.all_eq_true.1 arbs_cert_srv v hv) f hf
  rw [hs, Bool.false_or] at hc
  exact form_safe (by decide) hc k H_KAPPA d hd

/-- **Gate-level design headline (lit, κ ≤ 16587/374773 ≈ 0.0443).** On every
routed gcd_hw arbiter, for every realization `d` of A's corner model (one shared corner, each
arc within κ): both A0 forks are safe on every 7g run; A1/A2 are exclusive across both
handovers (7h/7j) for every server no faster than the realised `srv` path; g1/g2 are exclusive
across both releases for every server and A0 branch (RT1/RT1b, 7h/7j); and the bare cell
(ArbPin) is exclusive for every per-pin behaviour of the point box in all four request
scenarios. Hypotheses: positive loops (H_LOOP_*), and the record-realisation hypotheses of
the source files (`Real7`, `Real1`/`Real2`). -/
theorem design_gate_lit {v : E → Quad} (hv : v ∈ arbs) (k : Kappa)
    (H_KAPPA : k.num * 374773 ≤ k.den * 16587) {d : E → Nat}
    (hd : (litModel k v).Realizes d)
    (H_LOOP_ST : 0 < d .aq + d .cq + d .qs) (H_LOOP_UA1 : 0 < d .ac1 + d .fa1)
    (H_LOOP_UA2 : 0 < d .ac2 + d .fa2) :
    (OnGcdArbA0.Safe1 (xOf d) ∧ OnGcdArbA0.Safe2 (xOf d)) ∧
    (∀ (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbA0.Real7 (xOf d) D → (d .srv : Int) ≤ D.smin → ArbHeldTimed.Run D s →
      ArbHeldTimed.Scn D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbA0.Real7 (xOfB d) D → (d .srv : Int) ≤ D.smin → ArbHeldTimed.Run D s →
      ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr cq : Int) (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbFix.Real1 (qOf d) cr cq D → ArbHeldTimed.Run D s →
      ArbHeldTimed.Scn D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ (cr cq : Int) (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbFix.Real2 (qOf d) cr cq D → ArbHeldTimed.Run D s →
      ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ f : Int, 0 ≤ f → ∀ c : ArbPin.Cell (boxOf d) true (ArbPin.dn f) ArbPin.hi1, ArbPin.Excl c) ∧
    (∀ f : Int, 0 ≤ f → ∀ c : ArbPin.Cell (boxOf d) false ArbPin.hi1 (ArbPin.dn f), ArbPin.Excl c) ∧
    (∀ e1 e2 : Int, 0 ≤ e1 →
      ∀ c : ArbPin.Cell (boxOf d) false (ArbPin.up e1) (ArbPin.dn e2), ArbPin.Excl c) ∧
    (∀ e1 e2 : Int, 0 ≤ e2 →
      ∀ c : ArbPin.Cell (boxOf d) true (ArbPin.dn e1) (ArbPin.up e2), ArbPin.Excl c) := by
  have H : ∀ f ∈ forms, holds d f := fun f hf => lit_holds hv hf k H_KAPPA hd
  have m : ∀ {f : Form}, f ∈ forms → holds d f := fun hf => H _ hf
  have HL : 0 < d .cq + d .qs + d .aq := by omega
  refine ⟨⟨fork1_gate d (m (by simp [forms])) H_LOOP_ST H_LOOP_UA1,
      fork2_gate d (m (by simp [forms])) H_LOOP_ST H_LOOP_UA2⟩,
    fun D s t0 ta TA TA2 Hz h hs R S => rt2_gate d (m (by simp [forms])) (m (by simp [forms]))
      (m (by simp [forms])) (m (by simp [forms])) (m (by simp [forms])) h hs R S,
    fun D s t0 ta TA TA2 Hz h hs R S => rt2b_gate d (m (by simp [forms])) (m (by simp [forms]))
      (m (by simp [forms])) (m (by simp [forms])) (m (by simp [forms])) h hs R S,
    fun cr cq D s t0 ta TA TA2 Hz h R S => rt1_gate d (m (by simp [forms])) h R S,
    fun cr cq D s t0 ta TA TA2 Hz h R S => rt1b_gate d (m (by simp [forms])) h R S,
    fun f hf => h12_gate d (m (by simp [forms])) HL hf,
    fun f hf => h21_gate d (m (by simp [forms])) HL hf,
    fun e1 e2 he => o1_gate d (m (by simp [forms])) (m (by simp [forms])) HL he,
    fun e1 e2 he => o2_gate d (m (by simp [forms])) (m (by simp [forms])) HL he⟩

/-- Non-vacuity of `design_gate_lit`'s scatter/realization hypotheses: κ = 0 and the fast
endpoints realise every arbiter's model (A's `realizes_fast`), and the loop hypotheses hold
there on every arbiter (decided). -/
theorem design_gate_nonvacuous :
    (arbs.all fun v => decide (0 < (v .aq).1 + (v .cq).1 + (v .qs).1) &&
      decide (0 < (v .ac1).1 + (v .fa1).1) && decide (0 < (v .ac2).1 + (v .fa2).1)) = true ∧
    ∀ v : E → Quad, (litModel Kappa.zero v).Realizes (fun e => ((litModel Kappa.zero v).arc e).F) :=
  ⟨by decide +kernel, fun v => ⟨_, realizes_fast _⟩⟩

end Formal.Cells.OnGcdArbKappa
