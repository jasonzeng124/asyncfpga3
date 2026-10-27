import Formal.Cells.Prelim

/-!
# Probe 7g: the A0 isochronic-fork obligation of `bd_arbiter` (H_A0_FORK)

Probe 7b (`ArbKleene.lean`, scenarios `sc_a0_fall_skewed` / `sc_a0_fall_ordered`)
found that the ack-hold fix of `bd_arbiter` (cells/rtl/bd_arb.v) relies on an
ordering of the two branches of the A0 net. This file settles it exactly in a
discrete-time transport-delay model.

Scenario (client 2): client 1 has been served and has returned its request to
zero (`r1 = 0`), client 2 is waiting (`r2 = 1`), `rst = 0`, the state node is
held at `q = 1` by `A0 = 1`, and the server now drops `A0` at time `T0`. The
state LUT `ustate` re-evaluates (reset: `q -> 0`), the grant LUT `ugrant`
raises `g2 = r2 . ~q` (O6), and `ua2 = C(g2, A0)` must see A0 low before it sees
g2 high. Scenario (client 1): the mirror image (`r1 = 1`, `r2 = 0`, `q` held at
0, set `q -> 1`, `g1 = r1 . q` on O5, `ua1 = C(g1, A0)`).

Every gate is the REAL INIT of the RTL evaluated with `lutB`/`o5B`/`o6B` from
`Prelim`:
* `ustate` LUT6_2 INIT 64'hFFF0_FFB2_ACAC_ACAC, pins I0 r1, I1 r2, I2 q, I3 rst,
  I4 A0, I5 1; O6 = q.
* `ugrant` LUT6_2 INIT 64'h0C0C_0C0C_A0A0_A0A0, pins I0 r1, I1 r2, I2 q, I3 0,
  I4 0, I5 1; O5 = g1, O6 = g2.
* `ua1`/`ua2` = `bd_c2`, LUT6 INIT 64'h00E8_00E8_00E8_00E8, pins I0 g (a),
  I1 A0 (b), I2 own output, I3 rst, I4 0, I5 0.

## Timing model (gate relations, structure `Run`)

Time is `Nat` (1 tick = 1 ps intended). A LUT is modelled per pin: the value
the function sees on pin `i` at time `t` is the driving net delayed by the
pin's route (`w..`) plus the pin's site-pin / input-buffer delay (`p..`,
prjxray-db `tile_type_CLBLL_*.json`, A1 slow ... A6 fast), and the output
follows the function with the cell's output arc (`a..`). All are fixed
transport delays. In this scenario every net makes AT MOST ONE transition
(proved: `q_trace`, `g_trace`, and the A0 step), so a per-edge (rise/fall)
delay is exactly a fixed delay whose value is the delay of the edge this
scenario exercises; the doc comment of each field names that edge.
(prjxray gives no rise/fall split: its two IOPATH triples are the FAST and SLOW
corners of one arc, `prjxray/utils/makesdf.py:63`. The notes' earlier reading of
O6 56/124 as rise/fall was withdrawn after the audit; consistent-corner arc
values for this condition, and the corner sign changes, are in
`ArbCorners.ruleJ_arcs`, `ArbCorners.client2_corner_flip`,
`ArbCorners.client1_corner_flip`.)

The relevant delays are collected in `Dl`; `early` and `late` are

    late  = wAC + pAC                              (A0 branch into ua_k, past the split)
    early = wSt + pSt + aSt                        (A0 branch into ustate, its arc)
          + wQG + pQG + aG                         (q route, ugrant's pin and arc)
          + wGC + pGC                              (grant route, ua_k's grant pin)

The shared prefix `c` of the A0 route and ua_k's own output arc `aC` appear on
both sides and cancel; the theorems show they do not enter the condition.

## Main results

* `no_early_ack_iff` (both directions, for every run satisfying the gate
  relations): `A_k` never rises  <->  `late <= early`.
* `early_ack_at`: if `early < late`, `A_k` is high at exactly the computable
  instant `T0 + aC + c + early` (the counter-trace).
* `early_ack_latches`: if `late >= early + ua_k's loop delay` (overlap at least
  one C-element loop), `A_k` rises and stays high forever: the false
  acknowledge is latched, not a glitch. Shorter overlaps give a runt (C-element
  behaviour; see `CElemTiming.runt_*`).
* `run_exists`: the gate relations are satisfiable for every parameter set, so
  the universally quantified statements are not vacuous.
* `box_safe_iff`: with every delay only known to lie in an interval
  `[lo, hi]` (the hypotheses), the ordering holds for EVERY choice in the box
  iff `hi.late <= lo.early` (max of the late branch below min of the early
  chain). Both directions; `c` and `aC` drop out.
* All of the above for client 2 (`F2`, `G2` = O6) and client 1 (`F1`, `G1` = O5).

Core Lean only; proofs are `omega`, strong induction, and `decide` on the
INIT tables.
-/

namespace Formal.Cells.ArbA0Fork

open Formal.Cells

/-! ## INITs and the cells as seen in this scenario -/

def ST_INIT : Nat := 0xFFF0FFB2ACACACAC
def GR_INIT : Nat := 0x0C0C0C0CA0A0A0A0
def C2_INIT : Nat := 0x00E800E800E800E8

/-- `bd_c2` with `rst = 0`: I0 = grant, I1 = A0, I2 = own output (feedback). -/
def cel (g a fb : Bool) : Bool := lutB C2_INIT [g, a, fb, false, false, false]

theorem cel_eq : ∀ g a fb : Bool, cel g a fb = ((g && a) || (g && fb) || (a && fb)) := by
  decide

/-- `ustate` O6 with client 2's inputs: `r1 = 0`, `r2 = 1`, `rst = 0`. -/
def F2 (qfb a0 : Bool) : Bool := o6B ST_INIT [false, true, qfb, false, a0, true]
/-- `ugrant` O6 = g2 with `r1 = 0`, `r2 = 1`. -/
def G2 (q : Bool) : Bool := o6B GR_INIT [false, true, q, false, false, true]
/-- `ustate` O6 with client 1's inputs: `r1 = 1`, `r2 = 0`, `rst = 0`. -/
def F1 (qfb a0 : Bool) : Bool := o6B ST_INIT [true, false, qfb, false, a0, true]
/-- `ugrant` O5 = g1 with `r1 = 1`, `r2 = 0`. -/
def G1 (q : Bool) : Bool := o5B GR_INIT [true, false, q, false, false, true]

/-- With A0 high the state node holds (client 2's inputs). -/
theorem F2_hold : ∀ b, F2 b true = b := by decide
/-- With A0 low and only client 2 asking, q resets to 0. -/
theorem F2_go : ∀ b, F2 b false = false := by decide
theorem G2_vals : G2 true = false ∧ G2 false = true := by decide
theorem F1_hold : ∀ b, F1 b true = b := by decide
/-- With A0 low and only client 1 asking, q sets to 1. -/
theorem F1_go : ∀ b, F1 b false = true := by decide
theorem G1_vals : G1 false = false ∧ G1 true = true := by decide

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]
theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem dite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a : c → α) (b : ¬ c → α) :
    dite c a b = a h := by simp [h]

/-! ## Delays and gate relations -/

/-- The delays of one client's handover path. Each field is a NAMED timing
hypothesis: a fixed transport delay (ps) of one wire or arc, for the edge this
scenario puts on it. Physical source and test for each: routed SDF / prjxray. -/
structure Dl where
  /-- H_A0_SHARED: delay of the part of A0's route shared by both branches
  (driver to the divergence point). Test: route tree in `*_routed.json`. -/
  c : Nat
  /-- H_W_A0_ST: A0 route from the divergence point to ustate's A0 pin (falling edge). -/
  wSt : Nat
  /-- H_P_A0_ST: site-pin (input buffer) delay of the physical pin A0 lands on at ustate. -/
  pSt : Nat
  /-- H_ARC_ST: ustate output arc to O6 (falling for client 2, rising for client 1). -/
  aSt : Nat
  /-- H_W_QFB: q feedback route ustate.O6 -> ustate q pin. -/
  wQf : Nat
  /-- H_P_QFB: site-pin delay of ustate's q pin. -/
  pQf : Nat
  /-- H_W_QG: q route ustate.O6 -> ugrant q pin. -/
  wQG : Nat
  /-- H_P_QG: site-pin delay of ugrant's q pin. -/
  pQG : Nat
  /-- H_ARC_G: ugrant output arc, RISING (O6 for g2, O5 for g1). -/
  aG : Nat
  /-- H_W_GC: grant route ugrant -> ua_k grant pin (rising edge). -/
  wGC : Nat
  /-- H_P_GC: site-pin delay of ua_k's grant pin. -/
  pGC : Nat
  /-- H_W_A0_C: A0 route from the divergence point to ua_k's A0 pin (falling edge). -/
  wAC : Nat
  /-- H_P_A0_C: site-pin delay of ua_k's A0 pin. -/
  pAC : Nat
  /-- H_ARC_C: ua_k output arc (common to every input of ua_k). -/
  aC : Nat
  /-- H_W_CFB: ua_k feedback route. -/
  wCf : Nat
  /-- H_P_CFB: site-pin delay of ua_k's feedback pin. -/
  pCf : Nat

/-- A0's fall to q's edge at ustate's output, from the A0 driver. -/
def Dl.dS (p : Dl) : Nat := p.aSt + p.c + p.wSt + p.pSt
/-- ustate's loop delay. -/
def Dl.dQf (p : Dl) : Nat := p.aSt + p.wQf + p.pQf
/-- q's edge to the grant edge at ugrant's output. -/
def Dl.dG (p : Dl) : Nat := p.aG + p.wQG + p.pQG
/-- Delay from the grant net to the value ua_k's function sees (incl. its arc). -/
def Dl.dGC (p : Dl) : Nat := p.aC + p.wGC + p.pGC
/-- Delay from the A0 driver to the value ua_k's function sees (incl. its arc). -/
def Dl.dAC (p : Dl) : Nat := p.aC + p.c + p.wAC + p.pAC
/-- ua_k's loop delay. -/
def Dl.dCf (p : Dl) : Nat := p.aC + p.wCf + p.pCf

/-- The late branch, past the shared prefix and excluding ua_k's common arc. -/
def Dl.late (p : Dl) : Nat := p.wAC + p.pAC
/-- The early chain, past the shared prefix and excluding ua_k's common arc. -/
def Dl.early (p : Dl) : Nat :=
  p.wSt + p.pSt + p.aSt + p.wQG + p.pQG + p.aG + p.wGC + p.pGC

/-- The gate relations of one handover (all transport, per pin). `F`, `G` are
the state and grant LUTs with the requests fixed (instantiated below with the
real INITs), `q0` the held state before A0 falls.

Prose hypothesis H_REQ_STEADY: r1, r2, rst are constant from before A0 falls
until after the window (client k keeps asking until acknowledged, the other
client stays low because it cannot re-request before its own ack falls; rst
inactive). It is what lets the requests be folded into `F`, `G`. -/
structure Run (F : Bool → Bool → Bool) (G : Bool → Bool) (q0 : Bool) (p : Dl) (T0 : Nat)
    (a0 q g A : Nat → Bool) : Prop where
  /-- H_A0_FALL: the server drops A0 once, at `T0 > 0`, and keeps it low. -/
  H_A0_FALL : ∀ t, a0 t = decide (t < T0)
  H_T0 : 0 < T0
  /-- H_USTATE: ustate's O6 as a per-pin transport-delay LUT. -/
  H_USTATE : ∀ t, q t = F (q (t - p.dQf)) (a0 (t - p.dS))
  /-- H_UGRANT: ugrant's output for client k. -/
  H_UGRANT : ∀ t, g t = G (q (t - p.dG))
  /-- H_UA: ua_k = bd_c2 (rst = 0) on (grant, A0, own feedback). -/
  H_UA : ∀ t, A t = cel (g (t - p.dGC)) (a0 (t - p.dAC)) (A (t - p.dCf))
  /-- H_Q_INIT: the state node holds `q0` (the previous winner) while A0 is high. -/
  H_Q_INIT : q 0 = q0
  /-- H_A_INIT: client k's ack is low before the handover. -/
  H_A_INIT : A 0 = false
  /-- H_LOOP_ST: ustate's loop delay is positive (a routed wire). -/
  H_LOOP_ST : 0 < p.dQf
  /-- H_LOOP_UA: ua_k's loop delay is positive. -/
  H_LOOP_UA : 0 < p.dCf

/-! ## Generic proofs (any `F`, `G` with the hold / go / grant shape) -/

section Generic

variable {F : Bool → Bool → Bool} {G : Bool → Bool} {v : Bool} {p : Dl} {T0 : Nat}
  {a0 q g A : Nat → Bool}

/-- q holds `!v` until A0's fall has reached ustate's function, then is `v`. -/
theorem q_trace (R : Run F G (!v) p T0 a0 q g A)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v) :
    ∀ t, q t = if t < T0 + p.dS then !v else v := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    have hL := R.H_LOOP_ST
    have hT := R.H_T0
    by_cases h : t < T0 + p.dS
    · rw [ite_t h]
      have ha : a0 (t - p.dS) = true := by
        rw [R.H_A0_FALL]; exact decide_eq_true (by omega)
      rw [R.H_USTATE t, ha, hF]
      by_cases t0 : t = 0
      · subst t0; rw [Nat.zero_sub]; exact R.H_Q_INIT
      · rw [ih (t - p.dQf) (by omega), ite_t (by omega)]
    · rw [ite_f h]
      have ha : a0 (t - p.dS) = false := by
        rw [R.H_A0_FALL]; exact decide_eq_false (by omega)
      rw [R.H_USTATE t, ha, hFv]

/-- The grant rises once, at `T0 + dS + dG`. -/
theorem g_trace (R : Run F G (!v) p T0 a0 q g A)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v)
    (hG0 : G (!v) = false) (hG1 : G v = true) :
    ∀ t, g t = decide (T0 + p.dS + p.dG ≤ t) := by
  intro t
  have hT := R.H_T0
  rw [R.H_UGRANT t, q_trace R hF hFv]
  by_cases h : t - p.dG < T0 + p.dS
  · rw [ite_t h, hG0]; exact (decide_eq_false (by omega)).symm
  · rw [ite_f h, hG1]; exact (decide_eq_true (by omega)).symm

theorem early_unfold (p : Dl) :
    p.dS + p.dG + p.dGC = p.aC + p.c + p.early := by
  unfold Dl.dS Dl.dG Dl.dGC Dl.early; omega

theorem late_unfold (p : Dl) : p.dAC = p.aC + p.c + p.late := by
  unfold Dl.dAC Dl.late; omega

/-- **The exact condition, both directions.** For every run of the gate
relations: client k's ack never rises iff `late ≤ early`. -/
theorem no_early_ack_iff (R : Run F G (!v) p T0 a0 q g A)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v)
    (hG0 : G (!v) = false) (hG1 : G v = true) :
    (∀ t, A t = false) ↔ p.late ≤ p.early := by
  have gt := g_trace R hF hFv hG0 hG1
  have he := early_unfold p
  have hl := late_unfold p
  have hT := R.H_T0
  constructor
  · intro hs
    apply Classical.byContradiction
    intro hlt
    have hA := hs (T0 + p.dS + p.dG + p.dGC)
    rw [R.H_UA, gt, R.H_A0_FALL, cel_eq] at hA
    have e1 : decide (T0 + p.dS + p.dG ≤ T0 + p.dS + p.dG + p.dGC - p.dGC) = true :=
      decide_eq_true (by omega)
    have e2 : decide (T0 + p.dS + p.dG + p.dGC - p.dAC < T0) = true :=
      decide_eq_true (by omega)
    rw [e1, e2] at hA
    simp at hA
  · intro hle t
    have hLA := R.H_LOOP_UA
    induction t using Nat.strongRecOn with
    | _ t ih =>
      by_cases t0 : t = 0
      · subst t0; exact R.H_A_INIT
      · rw [R.H_UA t, ih (t - p.dCf) (by omega), gt, R.H_A0_FALL, cel_eq]
        by_cases h1 : T0 + p.dS + p.dG ≤ t - p.dGC
        · have : decide (t - p.dAC < T0) = false := decide_eq_false (by omega)
          rw [this]; simp
        · have : decide (T0 + p.dS + p.dG ≤ t - p.dGC) = false := decide_eq_false h1
          rw [this]; simp

/-- **Counter-trace.** If the late branch is slower, the ack is high at the
instant the grant reaches ua_k's function, `T0 + aC + c + early`. -/
theorem early_ack_at (R : Run F G (!v) p T0 a0 q g A)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v)
    (hG0 : G (!v) = false) (hG1 : G v = true) (hlt : p.early < p.late) :
    A (T0 + p.aC + p.c + p.early) = true := by
  have gt := g_trace R hF hFv hG0 hG1
  have he := early_unfold p
  have hl := late_unfold p
  have hT := R.H_T0
  rw [R.H_UA, gt, R.H_A0_FALL, cel_eq]
  have e1 : decide (T0 + p.dS + p.dG ≤ T0 + p.aC + p.c + p.early - p.dGC) = true :=
    decide_eq_true (by omega)
  have e2 : decide (T0 + p.aC + p.c + p.early - p.dAC < T0) = true :=
    decide_eq_true (by omega)
  rw [e1, e2]; simp

/-- **The false ack latches** when the overlap of (grant high, stale A0 high)
at ua_k lasts at least ua_k's loop delay: from `T0 + aC + c + early` on, A_k
is high forever (as long as the grant stays up, which H_REQ_STEADY gives). -/
theorem early_ack_latches (R : Run F G (!v) p T0 a0 q g A)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v)
    (hG0 : G (!v) = false) (hG1 : G v = true) (hov : p.early + p.dCf ≤ p.late) :
    ∀ t, T0 + p.aC + p.c + p.early ≤ t → A t = true := by
  have gt := g_trace R hF hFv hG0 hG1
  have he := early_unfold p
  have hl := late_unfold p
  have hLA := R.H_LOOP_UA
  have hT := R.H_T0
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    rw [R.H_UA t, gt, R.H_A0_FALL, cel_eq]
    have e1 : decide (T0 + p.dS + p.dG ≤ t - p.dGC) = true := decide_eq_true (by omega)
    rw [e1]
    by_cases h2 : t - p.dAC < T0
    · rw [decide_eq_true h2]; simp
    · rw [ih (t - p.dCf) (by omega) (by omega)]; simp

end Generic

/-! ## Existence: the gate relations are satisfiable for every parameter set -/

set_option linter.unusedVariables false in
/-- ua_k's output trace, built by recursion on time. -/
def ATr (gv av : Nat → Bool) (L : Nat) (t : Nat) : Bool :=
  if h : 0 < L ∧ 0 < t then cel (gv t) (av t) (ATr gv av L (t - L)) else false
termination_by t
decreasing_by have := h.1; have := h.2; omega

theorem ATr_eq (gv av : Nat → Bool) (L : Nat) (hL : 0 < L) (h0 : (gv 0 && av 0) = false) :
    ∀ t, ATr gv av L t = cel (gv t) (av t) (ATr gv av L (t - L)) := by
  intro t
  by_cases t0 : t = 0
  · subst t0
    have : ATr gv av L 0 = false := by rw [ATr]; simp
    rw [Nat.zero_sub, this, cel_eq]; simpa using h0
  · conv => lhs; rw [ATr]
    rw [dite_t ⟨hL, by omega⟩]

theorem run_exists (F : Bool → Bool → Bool) (G : Bool → Bool) (v : Bool) (p : Dl) (T0 : Nat)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v) (hG0 : G (!v) = false)
    (hT : 0 < T0) (hq : 0 < p.dQf) (hc : 0 < p.dCf) :
    ∃ a0 q g A, Run F G (!v) p T0 a0 q g A := by
  let a0 : Nat → Bool := fun t => decide (t < T0)
  let q : Nat → Bool := fun t => if t < T0 + p.dS then !v else v
  let g : Nat → Bool := fun t => G (q (t - p.dG))
  let gv : Nat → Bool := fun t => g (t - p.dGC)
  let av : Nat → Bool := fun t => a0 (t - p.dAC)
  refine ⟨a0, q, g, ATr gv av p.dCf, ?_⟩
  have hg0 : gv 0 = false := by
    show G (if 0 - p.dGC - p.dG < T0 + p.dS then !v else v) = false
    rw [ite_t (by omega)]; exact hG0
  refine ⟨fun _ => rfl, hT, ?_, fun _ => rfl, ?_, ?_, ?_, hq, hc⟩
  · intro t
    show (if t < T0 + p.dS then !v else v) =
      F (if t - p.dQf < T0 + p.dS then !v else v) (decide (t - p.dS < T0))
    by_cases h : t < T0 + p.dS
    · rw [ite_t h, ite_t (by omega), decide_eq_true (by omega), hF]
    · rw [ite_f h, decide_eq_false (by omega), hFv]
  · exact ATr_eq gv av p.dCf hc (by rw [hg0]; rfl)
  · show (if 0 < T0 + p.dS then !v else v) = !v
    exact ite_t (by omega) _ _
  · have : ATr gv av p.dCf 0 = false := by rw [ATr]; simp
    exact this

/-! ## Interval (named-hypothesis) form -/

/-- Componentwise `≤` on delay records. -/
def Dl.le (p r : Dl) : Prop :=
  p.c ≤ r.c ∧ p.wSt ≤ r.wSt ∧ p.pSt ≤ r.pSt ∧ p.aSt ≤ r.aSt ∧ p.wQf ≤ r.wQf ∧
  p.pQf ≤ r.pQf ∧ p.wQG ≤ r.wQG ∧ p.pQG ≤ r.pQG ∧ p.aG ≤ r.aG ∧ p.wGC ≤ r.wGC ∧
  p.pGC ≤ r.pGC ∧ p.wAC ≤ r.wAC ∧ p.pAC ≤ r.pAC ∧ p.aC ≤ r.aC ∧ p.wCf ≤ r.wCf ∧
  p.pCf ≤ r.pCf

/-- No early ack on any run with delays `p` (any A0 fall time). -/
def Safe (F : Bool → Bool → Bool) (G : Bool → Bool) (q0 : Bool) (p : Dl) : Prop :=
  ∀ T0 a0 q g A, Run F G q0 p T0 a0 q g A → ∀ t, A t = false

/-- The worst corner of the box: late branch at `hi`, everything else at `lo`. -/
def worst (lo hi : Dl) : Dl := { lo with wAC := hi.wAC, pAC := hi.pAC }

/-- **Interval form, both directions.** With every delay only known to lie in
`[lo, hi]` (H_DELAY_BOX; prjxray fast-min / slow-max, or the routed SDF times a
guardband), and both loops positive at `lo`: the handover never acknowledges
early for ANY delays in the box iff `hi.late ≤ lo.early`. -/
theorem box_safe_iff (F : Bool → Bool → Bool) (G : Bool → Bool) (v : Bool) (lo hi : Dl)
    (hF : ∀ b, F b true = b) (hFv : ∀ b, F b false = v)
    (hG0 : G (!v) = false) (hG1 : G v = true)
    (hbox : lo.le hi) (hq : 0 < lo.dQf) (hc : 0 < lo.dCf) :
    (∀ p, lo.le p → p.le hi → Safe F G (!v) p) ↔ hi.late ≤ lo.early := by
  constructor
  · intro hs
    have hb := hbox
    unfold Dl.le at hb
    have hw1 : lo.le (worst lo hi) := by
      unfold Dl.le worst; simp only; omega
    have hw2 : (worst lo hi).le hi := by
      unfold Dl.le worst; simp only; omega
    have hq' : 0 < (worst lo hi).dQf := by unfold Dl.dQf worst at *; simpa using hq
    have hc' : 0 < (worst lo hi).dCf := by unfold Dl.dCf worst at *; simpa using hc
    obtain ⟨a0, q, g, A, R⟩ := run_exists F G v (worst lo hi) 1 hF hFv hG0 (by omega) hq' hc'
    have := (no_early_ack_iff R hF hFv hG0 hG1).1 (hs _ hw1 hw2 1 a0 q g A R)
    unfold Dl.late Dl.early worst at this
    unfold Dl.late Dl.early
    simpa using this
  · intro hle p h1 h2 T0 a0 q g A R
    apply (no_early_ack_iff R hF hFv hG0 hG1).2
    unfold Dl.le at h1 h2
    unfold Dl.late Dl.early at *
    omega

/-! ## The two clients of `bd_arbiter`, on the real INITs -/

/-- Client 2 (A0 falls, r1 = 0, r2 = 1, q held at 1, g2 on ugrant.O6): exact. -/
theorem client2_iff {p : Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : Run F2 G2 true p T0 a0 q g A) : (∀ t, A t = false) ↔ p.late ≤ p.early :=
  no_early_ack_iff (v := false) R F2_hold F2_go G2_vals.1 G2_vals.2

theorem client2_counter {p : Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : Run F2 G2 true p T0 a0 q g A) (h : p.early < p.late) :
    A (T0 + p.aC + p.c + p.early) = true :=
  early_ack_at (v := false) R F2_hold F2_go G2_vals.1 G2_vals.2 h

theorem client2_latches {p : Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : Run F2 G2 true p T0 a0 q g A) (h : p.early + p.dCf ≤ p.late) :
    ∀ t, T0 + p.aC + p.c + p.early ≤ t → A t = true :=
  early_ack_latches (v := false) R F2_hold F2_go G2_vals.1 G2_vals.2 h

theorem client2_box (lo hi : Dl) (hbox : lo.le hi) (hq : 0 < lo.dQf) (hc : 0 < lo.dCf) :
    (∀ p, lo.le p → p.le hi → Safe F2 G2 true p) ↔ hi.late ≤ lo.early :=
  box_safe_iff F2 G2 false lo hi F2_hold F2_go G2_vals.1 G2_vals.2 hbox hq hc

/-- Client 1 (A0 falls, r1 = 1, r2 = 0, q held at 0, g1 on ugrant.O5): exact. -/
theorem client1_iff {p : Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : Run F1 G1 false p T0 a0 q g A) : (∀ t, A t = false) ↔ p.late ≤ p.early :=
  no_early_ack_iff (v := true) R F1_hold F1_go G1_vals.1 G1_vals.2

theorem client1_counter {p : Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : Run F1 G1 false p T0 a0 q g A) (h : p.early < p.late) :
    A (T0 + p.aC + p.c + p.early) = true :=
  early_ack_at (v := true) R F1_hold F1_go G1_vals.1 G1_vals.2 h

theorem client1_latches {p : Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : Run F1 G1 false p T0 a0 q g A) (h : p.early + p.dCf ≤ p.late) :
    ∀ t, T0 + p.aC + p.c + p.early ≤ t → A t = true :=
  early_ack_latches (v := true) R F1_hold F1_go G1_vals.1 G1_vals.2 h

theorem client1_box (lo hi : Dl) (hbox : lo.le hi) (hq : 0 < lo.dQf) (hc : 0 < lo.dCf) :
    (∀ p, lo.le p → p.le hi → Safe F1 G1 false p) ↔ hi.late ≤ lo.early :=
  box_safe_iff F1 G1 true lo hi F1_hold F1_go G1_vals.1 G1_vals.2 hbox hq hc


end Formal.Cells.ArbA0Fork
