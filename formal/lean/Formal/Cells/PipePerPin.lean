import Formal.Cells.FifoFidelity
import Formal.Cells.PipeTimedN

/-!
# Track 6, probe 6g: the N-stage timed pipe with PER-PIN controller LUTs

Probe 6f (`PipeTimedN`) proved the `N`-stage `bd_pipe` (clean control, every
token delivered, live) ASSUMING each controller LUT is a FIFO read of its
pin-level excitation (`PipeTimed.Ctl.H_LUT_FIFO`). Probe Bq (`FifoFidelity`)
showed that this assumption is false for a real LUT whose pins reach the mux
tree through different site-pin buffers (`ce_not_fifo`), and gave the per-pin
model `PinLut` with the one-phase select-level result `sel_phase` under the
ordering condition `H_SEL_ORDER`.

This file removes `H_LUT_FIFO` from the pipe theorem. Every controller is a
`PinLut` (each pin read through its OWN FIFO site-pin map `pr pa pq ps`, the
real `bd_c2n` INIT evaluated at the selects, then one FIFO output map `out`)
plus 5b's feedback window wire. The event times are re-derived with the
per-pin maps (`PP.tt`); the per-stage obligation is

    H_SELORD i :  wh i + pq_i.hi ≤ ER i + pr_i.lo   ∧   wh i + pq_i.hi ≤ EA i + pa_i.lo

with `ER`, `EA` the DERIVED round trips (per-pin versions of 6f's), i.e. an
inequality over routed pin delays only.

Proved for every `N ≥ 1`:
* `pipe_ctl`, `nodes_clean`, `pins_clean`: select-level excitation, node and
  every internal pin are clean, one edge per phase;
* `token`, `pipe_forward`: every stage latches every token, the last delivers;
* `live`: node edges strictly increase (no extra hypothesis);
* `ctl_pinlut`: every controller IS a `FifoFidelity.PinLut`;
* `Wit.witness`, `Wit.witness_data`: a unit-delay run with UNEQUAL pin delays
  (request 1, acknowledge 2, feedback 3, reset 1) satisfies everything;
* `ce_violates`: the Bq counterexample's numbers violate `H_SELORD`.

Why `sel_phase` is not applied verbatim: its feedback hypothesis covers the
whole phase, which is the result being proved (the feedback is the node
itself). `selx_phase` is `sel_phase` with that circularity closed by strong
induction on time (as 6e's `exc_phase` does for the lumped model); the case
analysis is the same (`c2n_set`, `c2n_hold`).

Core Lean only.
-/

namespace Formal.Cells.PipePerPin
open Formal.Cells Formal.Cells.PipeTimed

abbrev exSel := FifoFidelity.exSel
abbrev fmin := PipeTimedN.fmin
abbrev fmax := PipeTimedN.fmax
abbrev orAll := PipeTimedN.orAll

/-! ## 1. One per-pin controller -/

/-- **Gate relations of one per-pin controller** (`bd_link_ctl` = `bd_c2n`,
real INIT `0x00B2…`).
* `H_OUT`: `FifoFidelity.PinLut`'s relation. **H_PIN_FIFO**: each pin
  (I0 req, I1 ack, I2 feedback, I3 rst) reaches its mux-tree select through
  its own FIFO map `pr pa pq ps` (site-pin input buffer of the PHYSICAL pin
  the router chose; prjxray A1 ≈ 0.42–0.52 ns … A6 ≈ 0.005 ns at slow).
  **H_TREE_FIFO**: tree + output stage are ONE FIFO map `out` of the
  select-level function (contains the single-select static-hazard assumption
  of B-muxtree-fidelity). Test: GLS with per-pin transport delays placed
  BEFORE the LUT function.
* `H_FB`: the feedback wire `O → I2`, 5b's window channel (non-FIFO allowed).
* `H_LOOP_POS`: the loop (output, wire, feedback pin) has positive delay. -/
structure CtlP (req ack rst O qp : Trace) (pr pa pq ps out : Ret) (wl wh : Nat) : Prop where
  H_OUT : ∀ t, out.hi ≤ t → O t = exSel pr pa pq ps req ack qp rst (out.σ t)
  H_FB : CElemTiming.WinDelay wl wh O qp
  H_LOOP_POS : 1 ≤ out.lo + wl + pq.lo

/-- A `CtlP` controller is exactly Bq's `PinLut` (same maps, same relation). -/
def CtlP.pinLut {req ack rst O qp : Trace} {pr pa pq ps out : Ret} {wl wh : Nat}
    (C : CtlP req ack rst O qp pr pa pq ps out wl wh) : FifoFidelity.PinLut req ack rst O qp :=
  ⟨pr, pa, pq, ps, out, C.H_OUT⟩

theorem win_le {wl wh : Nat} {x y : Trace} (h : CElemTiming.WinDelay wl wh x y) : wl ≤ wh := by
  obtain ⟨s, h1, h2, _⟩ := h (wh + wl) (by omega); omega

section one
variable {req ack rst O qp : Trace} {pr pa pq ps out : Ret} {wl wh : Nat}

/-- **The select-level phase, with the feedback derived.** Phase target `v`.
Request `v` on `[ρ, ρ')`, acknowledge `!v` on `[α, α')` at the PINS. Let
`S = max (pr.fst ρ) (pa.fst α)` (both at their selects) and `τ = out.fst S`
(the node edge). If the node's new value, through the feedback wire and the
feedback pin, reaches its select no later than the first departure reaches
its own select (**H_SEL_ORDER**: `τ + wh + pq.hi ≤ min (pr.fst ρ') (pa.fst α')`),
the select-level excitation is `v` on all of `[S, max (pr.fst ρ') (pa.fst α'))`.
This is Bq's `sel_phase` without its `hqp`/`H_SEL_KEEP` premises (which
assume the result): they are discharged by strong induction on time. -/
theorem selx_phase (C : CtlP req ack rst O qp pr pa pq ps out wl wh) (v : Bool) (ρ ρ' α α' : Nat)
    (hreq : ∀ t, ρ ≤ t → t < ρ' → req t = v)
    (hack : ∀ t, α ≤ t → t < α' → ack t = !v)
    (hrst : ∀ s, max (pr.fst ρ) (pa.fst α) ≤ s → rst (ps.σ s) = false)
    (hpos : 1 ≤ max (pr.fst ρ) (pa.fst α))
    (hbig : out.hi ≤ out.fst (max (pr.fst ρ) (pa.fst α)))
    (H_SEL_ORDER : out.fst (max (pr.fst ρ) (pa.fst α)) + wh + pq.hi ≤ min (pr.fst ρ') (pa.fst α')) :
    ∀ s, max (pr.fst ρ) (pa.fst α) ≤ s → s < max (pr.fst ρ') (pa.fst α') →
      exSel pr pa pq ps req ack qp rst s = v := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h1 h2
    have hq : min (pr.fst ρ') (pa.fst α') ≤ s → qp (pq.σ s) = v := by
      intro hd
      have g1 := pq.ge s; have g2 := pq.le s
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB (pq.σ s) (by omega)
      have hp := C.H_LOOP_POS
      have o1 := out.le u
      have o2 : max (pr.fst ρ) (pa.fst α) ≤ out.σ u := out.fst_after (by omega)
      rw [e, C.H_OUT u (by omega)]
      exact ih (out.σ u) (by omega) o2 (by omega)
    have hr := hrst s h1
    show CElemTiming.exc CElemTiming.INIT_c2n (req (pr.σ s)) (ack (pa.σ s)) (qp (pq.σ s))
      (rst (ps.σ s)) = v
    rw [hr]
    by_cases c1 : s < pr.fst ρ'
    · have rq : req (pr.σ s) = v := hreq _ (pr.fst_after (by omega)) (pr.fst_before c1)
      by_cases c2 : s < pa.fst α'
      · have ak : ack (pa.σ s) = !v := hack _ (pa.fst_after (by omega)) (pa.fst_before c2)
        rw [rq, ak]; exact FifoFidelity.c2n_set v _
      · rw [hq (by omega)]; exact FifoFidelity.c2n_hold v _ _ (Or.inl rq)
    · have c2 : s < pa.fst α' := by omega
      have ak : ack (pa.σ s) = !v := hack _ (pa.fst_after (by omega)) (pa.fst_before c2)
      rw [hq (by omega)]; exact FifoFidelity.c2n_hold v _ _ (Or.inr ak)

/-- **Before the first request reaches its select.** Reset high on `[0, R)`;
the request pin low on `[R0, F)`. If the request select and the feedback loop
have been flushed by the time reset releases at ITS select
(`R0 + pr.hi ≤ R + ps.lo`, `out.hi + wh + pq.hi ≤ R + ps.lo`), the
select-level excitation is 0 on `[0, pr.fst F)`. -/
theorem selx_pre (C : CtlP req ack rst O qp pr pa pq ps out wl wh) (R R0 F : Nat)
    (hrst : ∀ t, t < R → rst t = true) (hreq : ∀ t, R0 ≤ t → t < F → req t = false)
    (hR : 1 ≤ R) (h1 : R0 + pr.hi ≤ R + ps.lo) (h2 : out.hi + wh + pq.hi ≤ R + ps.lo) :
    ∀ s, s < pr.fst F → exSel pr pa pq ps req ack qp rst s = false := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro hs
    show CElemTiming.exc CElemTiming.INIT_c2n (req (pr.σ s)) (ack (pa.σ s)) (qp (pq.σ s))
      (rst (ps.σ s)) = false
    cases hr : rst (ps.σ s) with
    | true => exact FifoFidelity.c2n_reset _ _ _
    | false =>
      have hge : R ≤ ps.σ s := by
        apply Classical.byContradiction; intro hc
        rw [hrst _ (by omega)] at hr; exact Bool.noConfusion hr
      have l1 := ps.le s
      have g1 := pr.ge s
      have rq : req (pr.σ s) = false := hreq _ (by omega) (pr.fst_before hs)
      have g2 := pq.ge s; have g3 := pq.le s
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB (pq.σ s) (by omega)
      have hp := C.H_LOOP_POS
      have o1 := out.le u
      have hq : qp (pq.σ s) = false := by
        rw [e, C.H_OUT u (by omega)]
        exact ih (out.σ u) (by omega) (by omega)
      rw [rq, hq]
      exact FifoFidelity.c2n_stay true false _ (Or.inl rfl)

end one

/-! ## 2. Delay realisation and derived event times -/

/-- Delay realisation of one run of an `N`-stage pipe with per-pin
controllers. Stage `i < N`; boundary `b = i + 1` between stages `i`, `i+1`. -/
structure PP where
  N : Nat
  /-- reset released (at the rst PIN) at `R` -/
  R : Nat
  /-- every pin holds its power-up-flushed initial value from `R0` on -/
  R0 : Nat
  /-- stage `i`'s site-pin maps: request (I0), acknowledge (I1), feedback
  (I2), reset (I3); and its tree + output map -/
  pr : Nat → Ret
  pa : Nat → Ret
  pq : Nat → Ret
  ps : Nat → Ret
  out : Nat → Ret
  /-- boundary `b`'s request line -/
  Rq : Nat → Ret
  /-- boundary `b`'s DACK line: OR of `m b + 1` FIFO copies (`fastrise_or`) -/
  m : Nat → Nat
  Ap : Nat → Nat → Ret
  Ag : Nat → Nat
  /-- environment edge times at `r[0]` and `a[N]` -/
  ρ : Nat → Nat
  γ : Nat → Nat

namespace PP

/-- The 6f realisation sharing the lines (used only for its DACK-line
bookkeeping `ackT`, `alo`, `ahi`, `aslow`; its `L` is unused). -/
def toPN (P : PP) : PipeTimedN.PN :=
  ⟨P.N, P.R, P.out, P.Rq, P.m, P.Ap, P.Ag, P.ρ, P.γ⟩

def ackT (P : PP) (b j τ : Nat) : Nat := P.toPN.ackT b j τ
def alo (P : PP) (b : Nat) : Nat := P.toPN.alo b
def ahi (P : PP) (b : Nat) : Nat := P.toPN.ahi b
def aslow (P : PP) (b : Nat) : Nat := P.toPN.aslow b

/-- Both of stage `i`'s inputs have reached their SELECTS. -/
def sel (P : PP) (i ρ α : Nat) : Nat := max ((P.pr i).fst ρ) ((P.pa i).fst α)
/-- Stage `i`'s node edge for pin arrivals `ρ`, `α`. -/
def node (P : PP) (i ρ α : Nat) : Nat := (P.out i).fst (P.sel i ρ α)

/-- Node edges of phase `j`, ascending in the stage, given acknowledge pin
arrivals `α`. -/
def row (P : PP) (j : Nat) (α : Nat → Nat) : Nat → Nat
  | 0 => P.node 0 (P.ρ j) (α 0)
  | i + 1 => P.node (i + 1) ((P.Rq (i + 1)).fst (row P j α i)) (α (i + 1))

def ackIn (P : PP) (j : Nat) (τn : Nat → Nat) (i : Nat) : Nat :=
  if i + 1 < P.N then P.ackT (i + 1) j (τn (i + 1)) else P.γ j

/-- All node edges: outer recursion on the phase. -/
def tt (P : PP) : Nat → Nat → Nat
  | 0 => P.row 0 (fun _ => P.R0)
  | j + 1 => P.row (j + 1) (P.ackIn j (tt P j))

/-- Stage `i`'s node makes its `j`-th edge. -/
def τ (P : PP) (i j : Nat) : Nat := P.tt j i
/-- Stage `i`'s request PIN makes its `j`-th edge. -/
def Rin (P : PP) : Nat → Nat → Nat
  | 0, j => P.ρ j
  | i + 1, j => (P.Rq (i + 1)).fst (P.τ i j)
/-- Stage `i`'s acknowledge PIN reaches phase `j`'s level. -/
def Ain (P : PP) (i : Nat) : Nat → Nat
  | 0 => P.R0
  | j + 1 => P.ackIn j (fun k => P.τ k j) i
/-- Phase `j` of stage `i` starts AT THE SELECTS. -/
def S (P : PP) (i j : Nat) : Nat := P.sel i (P.Rin i j) (P.Ain i j)

theorem τ_eq (P : PP) (i j : Nat) : P.τ i j = (P.out i).fst (P.S i j) := by
  cases i <;> cases j <;> rfl

/-- Request-side round trip (node edge of stage `i` → its request PIN's next
edge): the sender's `Es` at stage 0; inside, the DACK fast path, stage
`i-1`'s ACK PIN, its tree, the request line. -/
def ER (P : PP) (Es : Nat) : Nat → Nat
  | 0 => Es
  | i + 1 => P.alo (i + 1) + (P.pa i).lo + (P.out i).lo + (P.Rq (i + 1)).lo

/-- Acknowledge-side round trip: the request line, stage `i+1`'s REQUEST PIN
and tree, the DACK fast path; the receiver's `Er` at the last stage. -/
def EA (P : PP) (Er i : Nat) : Nat :=
  if i + 1 < P.N then (P.Rq (i + 1)).lo + (P.pr (i + 1)).lo + (P.out (i + 1)).lo + P.alo (i + 1)
  else Er

/-- Minimum spacing of stage `i`'s node edges. -/
def Won (P : PP) (Es Er i : Nat) : Nat :=
  (P.out i).lo + max (P.ER Es i + (P.pr i).lo) (P.EA Er i + (P.pa i).lo)

theorem Ain_in (P : PP) (i j : Nat) (h : i + 1 < P.N) :
    P.Ain i (j + 1) = P.ackT (i + 1) j (P.τ (i + 1) j) := by
  simp only [Ain, ackIn, h, ite_true]

theorem Ain_last (P : PP) (i j : Nat) (h : ¬ i + 1 < P.N) : P.Ain i (j + 1) = P.γ j := by
  simp only [Ain, ackIn, h, ite_false]

theorem EA_in (P : PP) (Er i : Nat) (h : i + 1 < P.N) :
    P.EA Er i = (P.Rq (i + 1)).lo + (P.pr (i + 1)).lo + (P.out (i + 1)).lo + P.alo (i + 1) := by
  simp only [EA, h, ite_true]

theorem EA_last (P : PP) (Er i : Nat) (h : ¬ i + 1 < P.N) : P.EA Er i = Er := by
  simp only [EA, h, ite_false]

theorem ackT_ge (P : PP) (b j τ : Nat) (h : 1 ≤ τ) : τ + P.alo b ≤ P.ackT b j τ :=
  P.toPN.ackT_ge b j τ h
theorem ackT_ge' (P : PP) (b j τ : Nat) : τ ≤ P.ackT b j τ := P.toPN.ackT_ge' b j τ
theorem ackT_odd (P : PP) (b j τ : Nat) (hj : j % 2 = 1) (h : 1 ≤ τ) :
    τ + P.aslow b ≤ P.ackT b j τ := P.toPN.ackT_odd b j τ hj h

end PP

/-! ## 3. Gate relations, environment, per-stage obligations -/

/-- **Gate relations of the per-pin `N`-stage pipe.** As 6f's `GatesN`, with
6e's lumped `Ctl` (which assumes `H_LUT_FIFO`) replaced by the per-pin
`CtlP`. -/
structure GatesP (P : PP) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) : Prop where
  /-- **H_RST**: `rst` (at its pin) high on `[0, R)`, low after. -/
  H_RST : ∀ t, rst t = decide (t < P.R)
  /-- **H_CTL_PIN i**: each controller is a per-pin LUT (`CtlP`). -/
  H_CTL : ∀ i, i < P.N →
    CtlP (r i) (a i) rst (O i) (q i) (P.pr i) (P.pa i) (P.pq i) (P.ps i) (P.out i) (wl i) (wh i)
  /-- **H_REQ_LINE b** (FIFO), as 6f. -/
  H_REQ_LINE : ∀ i, i + 1 < P.N → ∀ t, (P.Rq (i + 1)).hi ≤ t →
    r (i + 1) t = O i ((P.Rq (i + 1)).σ t)
  /-- **H_ACK_LINE b**: OR of FIFO copies, a theorem for the real chain
  (`PipeTimedN.fastrise_or`), as 6f. -/
  H_ACK_LINE : ∀ i, i + 1 < P.N → ∀ t, P.Ag (i + 1) ≤ t →
    a i t = orAll (fun k => O (i + 1) ((P.Ap (i + 1) k).σ t)) (P.m (i + 1))

/-- **The environment** (6f's `EnvN`; the initial-low stretches start at the
flush time `R0` instead of `R`). -/
structure EnvP (P : PP) (r0 aN : Trace) (Es Er : Nat) : Prop where
  H_REQ_LOW0 : ∀ t, P.R0 ≤ t → t < P.ρ 0 → r0 t = false
  H_REQ : ∀ j t, P.ρ j ≤ t → t < P.ρ (j + 1) → r0 t = Vph j
  H_ACK_LOW0 : ∀ t, P.R0 ≤ t → t < P.γ 0 → aN t = false
  H_ACK : ∀ j t, P.γ j ≤ t → t < P.γ (j + 1) → aN t = Vph j
  /-- **H_SND**: sender answers at least `Es` after stage 0's node edge. -/
  H_SND : ∀ j, P.τ 0 j + Es ≤ P.ρ (j + 1)
  /-- **H_RCV**: receiver answers at least `Er` after the last node edge. -/
  H_RCV : ∀ j, P.τ (P.N - 1) j + Er ≤ P.γ j
  H_RST_EARLY : P.R ≤ P.ρ 0

/-- **Control-side obligations of the per-pin pipe.** Every field is an
inequality over routed delays (site-pin bands, LUT arcs, wires, the
environment's latencies): nothing refers to a trace. -/
structure TimingP (P : PP) (wh : Nat → Nat) (Es Er : Nat) : Prop where
  H_N_POS : 1 ≤ P.N
  H_R0_POS : 1 ≤ P.R0
  H_R0_LE : P.R0 ≤ P.R
  /-- **H_RST_SEL i** (startup, per stage; replaces 6f's `H_RST_LONG`):
  (a) the request select reads flushed values once reset releases at the rst
  select; (b) the loop (tree, feedback wire, feedback pin) is flushed by then;
  (c) reset has released at its select before the first request reaches its
  select; (d) the acknowledge select is flushed by then too. -/
  H_RST_SEL : ∀ i, i < P.N →
    P.R0 + (P.pr i).hi ≤ P.R + (P.ps i).lo ∧
    (P.out i).hi + wh i + (P.pq i).hi ≤ P.R + (P.ps i).lo ∧
    P.R + (P.ps i).hi ≤ P.ρ 0 + (P.pr i).lo ∧
    P.R0 + (P.pa i).hi ≤ P.ρ 0 + (P.pr i).lo
  /-- **H_FLUSH b**: both lines of boundary `b` carry the initial node values
  from `R0` on (6f's `H_RST_LINES` against `R0`). -/
  H_FLUSH : ∀ i, i + 1 < P.N →
    (P.out i).hi + (P.Rq (i + 1)).hi ≤ P.R0 ∧ (P.out (i + 1)).hi + P.ahi (i + 1) ≤ P.R0 ∧
    P.Ag (i + 1) ≤ P.R0
  /-- **H_SELORD i** (Bq's `H_SEL_ORDER`, per stage, every phase, final form):
  the feedback's slowest arrival at ITS select (wire `wh` + feedback site pin
  `pq.hi`, counted from the node edge) is no later than the earliest
  departure of the request at ITS select (round trip `ER` + request site pin
  `pr.lo`), and of the acknowledge (`EA` + `pa.lo`). `ER`, `EA` are DERIVED
  round trips; at the ends they are the environment's `Es`, `Er`. This
  replaces BOTH 6f's `H_LAT` and the assumption `H_LUT_FIFO`. -/
  H_SELORD : ∀ i, i < P.N →
    wh i + (P.pq i).hi ≤ P.ER Es i + (P.pr i).lo ∧ wh i + (P.pq i).hi ≤ P.EA Er i + (P.pa i).lo
  /-- **H_ACK_FLUSH b**: as 6f, with the per-pin `Won`. -/
  H_ACK_FLUSH : ∀ i, i + 1 < P.N →
    P.ahi (i + 1) ≤ P.Won Es Er (i + 1) + P.alo (i + 1)

/-! ## 4. Derived timing -/

section chain
variable {P : PP} {r0 aN : Trace} {wh : Nat → Nat} {Es Er : Nat}
variable (E : EnvP P r0 aN Es Er) (T : TimingP P wh Es Er)
include E T

omit E in
theorem R_pos : 1 ≤ P.R := by have := T.H_R0_POS; have := T.H_R0_LE; omega

omit E T in
theorem S_ge_r (i j : Nat) : P.Rin i j ≤ P.S i j := by
  have := (P.pr i).fst_ge (P.Rin i j); unfold PP.S PP.sel; omega

omit E T in
theorem tau_ge (i j : Nat) : P.S i j ≤ P.τ i j := by
  rw [P.τ_eq]; exact (P.out i).fst_ge _

omit T in
/-- The sender's request edges are monotone. -/
theorem rho_mono : ∀ j, P.ρ 0 ≤ P.ρ j := by
  intro j; induction j with
  | zero => omega
  | succ j ih =>
    have := E.H_SND j; have := S_ge_r (P := P) 0 j; have := tau_ge (P := P) 0 j
    simp only [PP.Rin] at *; omega

omit T in
/-- Every request pin edge is at or after the first environment request. -/
theorem rho0_Rin (j : Nat) : ∀ i, P.ρ 0 ≤ P.Rin i j := by
  intro i; induction i with
  | zero => exact rho_mono E j
  | succ i ih =>
    have := S_ge_r (P := P) i j; have := tau_ge (P := P) i j
    have := (P.Rq (i + 1)).fst_ge (P.τ i j); simp only [PP.Rin]; omega

theorem Rin_pos (i j : Nat) : 1 ≤ P.Rin i j := by
  have := rho0_Rin E j i; have := E.H_RST_EARLY; have := R_pos T; omega

theorem S_lo_r (i j : Nat) : P.Rin i j + (P.pr i).lo ≤ P.S i j := by
  have := (P.pr i).fst_lo (Rin_pos E T i j); unfold PP.S PP.sel; omega

theorem S_pos (i j : Nat) : 1 ≤ P.S i j := by
  have := S_lo_r E T i j; have := Rin_pos E T i j; omega

theorem tau_lo (i j : Nat) : P.S i j + (P.out i).lo ≤ P.τ i j := by
  rw [P.τ_eq]; exact (P.out i).fst_lo (S_pos E T i j)

theorem tau_pos (i j : Nat) : 1 ≤ P.τ i j := by
  have := tau_lo E T i j; have := S_pos E T i j; omega

theorem Ain_pos (i j : Nat) : 1 ≤ P.Ain i j := by
  cases j with
  | zero => have := T.H_R0_POS; simp only [PP.Ain]; omega
  | succ j =>
    by_cases h : i + 1 < P.N
    · rw [P.Ain_in i j h]; have := P.ackT_ge' (i + 1) j (P.τ (i + 1) j)
      have := tau_pos E T (i + 1) j; omega
    · rw [P.Ain_last i j h]; have := E.H_RCV j; have := tau_pos E T (P.N - 1) j; omega

theorem S_lo_a (i j : Nat) : P.Ain i j + (P.pa i).lo ≤ P.S i j := by
  have := (P.pa i).fst_lo (Ain_pos E T i j); unfold PP.S PP.sel; omega

theorem Rin_lo (i j : Nat) : P.τ i j + (P.Rq (i + 1)).lo ≤ P.Rin (i + 1) j :=
  (P.Rq (i + 1)).fst_lo (tau_pos E T i j)

theorem Ain_lo (i j : Nat) (h : i + 1 < P.N) : P.τ (i + 1) j + P.alo (i + 1) ≤ P.Ain i (j + 1) := by
  rw [P.Ain_in i j h]; exact P.ackT_ge _ _ _ (tau_pos E T _ _)

/-- **Request-side departure, DERIVED.** -/
theorem depR (i j : Nat) (hi : i < P.N) : P.τ i j + P.ER Es i ≤ P.Rin i (j + 1) := by
  cases i with
  | zero => exact E.H_SND j
  | succ i =>
    have h1 := Rin_lo E T i (j + 1); have h2 := tau_lo E T i (j + 1)
    have h3 := S_lo_a E T i (j + 1); have h4 := Ain_lo E T i j hi
    simp only [PP.ER]; omega

/-- **Acknowledge-side departure, DERIVED.** -/
theorem depA (i j : Nat) (hi : i < P.N) : P.τ i j + P.EA Er i ≤ P.Ain i (j + 1) := by
  by_cases h : i + 1 < P.N
  · rw [P.EA_in Er i h]
    have h1 := Ain_lo E T i j h; have h2 := tau_lo E T (i + 1) j
    have h3 := S_lo_r E T (i + 1) j; have h4 := Rin_lo E T i j
    omega
  · rw [P.EA_last Er i h, P.Ain_last i j h]
    have e : i = P.N - 1 := by omega
    subst e; exact E.H_RCV j

/-- Stage `i`'s node edges are at least `Won i` apart. -/
theorem gap (i j : Nat) (hi : i < P.N) : P.τ i j + P.Won Es Er i ≤ P.τ i (j + 1) := by
  have := depR E T i j hi; have := depA E T i j hi; have := tau_lo E T i (j + 1)
  have := S_lo_r E T i (j + 1); have := S_lo_a E T i (j + 1); unfold PP.Won; omega

theorem fwd (i j : Nat) :
    P.τ i j + (P.Rq (i + 1)).lo + (P.pr (i + 1)).lo + (P.out (i + 1)).lo ≤ P.τ (i + 1) j := by
  have := Rin_lo E T i j; have := tau_lo E T (i + 1) j; have := S_lo_r E T (i + 1) j; omega

/-- Stage `i`'s rise after stage `i+1`'s fall comes through the SLOW DACK
path, then stage `i`'s acknowledge pin and tree. -/
theorem back_odd (i j : Nat) (h : i + 1 < P.N) (hj : j % 2 = 1) :
    P.τ (i + 1) j + P.aslow (i + 1) + (P.pa i).lo + (P.out i).lo ≤ P.τ i (j + 1) := by
  have h1 := tau_lo E T i (j + 1); have h2 := S_lo_a E T i (j + 1)
  have h3 := P.ackT_odd (i + 1) j (P.τ (i + 1) j) hj (tau_pos E T _ _)
  rw [P.Ain_in i j h] at h2; omega

theorem rho_le (j : Nat) : P.ρ j + (P.pr 0).lo + (P.out 0).lo ≤ P.τ 0 j := by
  have := tau_lo E T 0 j; have := S_lo_r E T 0 j; simp only [PP.Rin] at this; omega

theorem gam_le (j : Nat) :
    P.γ j + (P.pa (P.N - 1)).lo + (P.out (P.N - 1)).lo ≤ P.τ (P.N - 1) (j + 1) := by
  have := tau_lo E T (P.N - 1) (j + 1); have := S_lo_a E T (P.N - 1) (j + 1)
  have hn := T.H_N_POS
  rw [P.Ain_last _ j (by omega)] at this; omega

/-- The first phase starts at the request's arrival at its select. -/
theorem S0_eq (i : Nat) (hi : i < P.N) : P.S i 0 = (P.pr i).fst (P.Rin i 0) := by
  have ⟨_, _, _, hd⟩ := T.H_RST_SEL i hi
  have := (P.pa i).fst_le P.R0; have := (P.pr i).fst_lo (Rin_pos E T i 0)
  have := rho0_Rin E 0 i
  unfold PP.S PP.sel; simp only [PP.Ain]; omega

/-- Reset has released at the rst select by every phase start. -/
theorem rst_sel (i j : Nat) (hi : i < P.N) : ∀ s, P.S i j ≤ s → P.R ≤ (P.ps i).σ s := by
  intro s hs
  have ⟨_, _, hc, _⟩ := T.H_RST_SEL i hi
  have := S_lo_r E T i j; have := rho0_Rin E j i; have := (P.ps i).ge s; omega

end chain

/-! ## 5. Every select-level excitation, node and internal pin is clean -/

section ctl
variable {P : PP} {rst : Trace} {r a O q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesP P rst r a O q wl wh) (E : EnvP P (r 0) (a (P.N - 1)) Es Er)
  (T : TimingP P wh Es Er)
include G E T

/-- The select-level excitation of stage `i`. -/
abbrev xs (i : Nat) : Trace :=
  exSel (P.pr i) (P.pa i) (P.pq i) (P.ps i) (r i) (a i) (q i) rst

omit E T in
theorem rst_hi : ∀ t, t < P.R → rst t = true := by
  intro t h; rw [G.H_RST]; simp [h]

omit E T in
theorem rst_lo : ∀ t, P.R ≤ t → rst t = false := by
  intro t h; rw [G.H_RST]; simp; omega

/-- **Before the first phase, every stage**: the select-level excitation is 0
before the phase-0 start `S i 0`, and the node is low from `out.hi` to its
first edge. Induction on the stage. -/
theorem pre : ∀ i, i < P.N →
    (∀ s, s < P.S i 0 → xs (P := P) (r := r) (a := a) (q := q) (rst := rst) i s = false) ∧
    (∀ t, (P.out i).hi ≤ t → t < P.τ i 0 → O i t = false) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have ⟨h1, h2, _, _⟩ := T.H_RST_SEL 0 hi
    have hx : ∀ s, s < P.S 0 0 → xs (P := P) (r := r) (a := a) (q := q) (rst := rst) 0 s = false := by
      rw [S0_eq E T 0 hi]
      exact selx_pre (G.H_CTL 0 hi) P.R P.R0 (P.Rin 0 0) (rst_hi G) E.H_REQ_LOW0 (R_pos T) h1 h2
    refine ⟨hx, fun t t1 t2 => ?_⟩
    rw [(G.H_CTL 0 hi).H_OUT t t1]; rw [P.τ_eq] at t2; exact hx _ ((P.out 0).fst_before t2)
  | succ i ih =>
    intro hi
    have hprev := (ih (by omega)).2
    have ⟨h1, h2, _, _⟩ := T.H_RST_SEL (i + 1) hi
    have hreq : ∀ t, P.R0 ≤ t → t < P.Rin (i + 1) 0 → r (i + 1) t = false := by
      intro t t1 t2
      have hf := (T.H_FLUSH i hi).1; have g := (P.Rq (i + 1)).ge t
      rw [G.H_REQ_LINE i hi t (by omega)]
      exact hprev _ (by omega) ((P.Rq (i + 1)).fst_before t2)
    have hx : ∀ s, s < P.S (i + 1) 0 →
        xs (P := P) (r := r) (a := a) (q := q) (rst := rst) (i + 1) s = false := by
      rw [S0_eq E T (i + 1) hi]
      exact selx_pre (G.H_CTL (i + 1) hi) P.R P.R0 (P.Rin (i + 1) 0) (rst_hi G) hreq (R_pos T) h1 h2
    refine ⟨hx, fun t t1 t2 => ?_⟩
    rw [(G.H_CTL (i + 1) hi).H_OUT t t1]; rw [P.τ_eq] at t2
    exact hx _ ((P.out (i + 1)).fst_before t2)

/-- Stage `i`, phase `j`, from clean pins: `selx_phase` with the DERIVED
departures and `H_SELORD`. -/
theorem phase_of (i j : Nat) (hi : i < P.N)
    (hreq : ∀ t, P.Rin i j ≤ t → t < P.Rin i (j + 1) → r i t = Vph j)
    (hack : ∀ t, P.Ain i j ≤ t → t < P.Ain i (j + 1) → a i t = !Vph j) :
    ∀ s, P.S i j ≤ s → s < P.S i (j + 1) →
      xs (P := P) (r := r) (a := a) (q := q) (rst := rst) i s = Vph j := by
  have ⟨_, hb, _, _⟩ := T.H_RST_SEL i hi
  have ⟨o1, o2⟩ := T.H_SELORD i hi
  have dr := depR E T i j hi; have da := depA E T i j hi
  have e1 := (P.pr i).fst_lo (Rin_pos E T i (j + 1))
  have e2 := (P.pa i).fst_lo (Ain_pos E T i (j + 1))
  have hτ := P.τ_eq i j
  have hS := tau_ge (P := P) i j
  have hrs := rst_sel E T i j hi
  have hpl := (P.ps i).lo_le_hi
  have ⟨_, _, hc, _⟩ := T.H_RST_SEL i hi
  have hS2 := S_lo_r E T i j; have hr0 := rho0_Rin E j i
  exact selx_phase (G.H_CTL i hi) (Vph j) (P.Rin i j) (P.Rin i (j + 1)) (P.Ain i j) (P.Ain i (j + 1))
    hreq hack (fun s hs => rst_lo G _ (hrs s hs)) (S_pos E T i j)
    (by show (P.out i).hi ≤ (P.out i).fst (P.S i j); omega)
    (by show (P.out i).fst (P.S i j) + wh i + (P.pq i).hi ≤
          min ((P.pr i).fst (P.Rin i (j + 1))) ((P.pa i).fst (P.Ain i (j + 1))); omega)

/-- A node is `Vph j` between its `j`-th and `(j+1)`-th edges. -/
theorem node_of (i j : Nat) (hi : i < P.N)
    (h : ∀ s, P.S i j ≤ s → s < P.S i (j + 1) →
      xs (P := P) (r := r) (a := a) (q := q) (rst := rst) i s = Vph j) :
    ∀ t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j := by
  intro t t1 t2
  have ⟨_, hb, hc, _⟩ := T.H_RST_SEL i hi
  have := S_lo_r E T i j; have := rho0_Rin E j i; have hg := tau_ge (P := P) i j
  have := (P.ps i).lo_le_hi
  rw [P.τ_eq i j] at t1 hg; rw [P.τ_eq i (j + 1)] at t2
  exact fifo_hold (P.out i) (G.H_CTL i hi).H_OUT h t t1 t2 (by omega)

theorem req_of (i j : Nat) (hi : i + 1 < P.N)
    (h : ∀ s, P.S i j ≤ s → s < P.S i (j + 1) →
      xs (P := P) (r := r) (a := a) (q := q) (rst := rst) i s = Vph j) :
    ∀ t, P.Rin (i + 1) j ≤ t → t < P.Rin (i + 1) (j + 1) → r (i + 1) t = Vph j := by
  have hO := node_of G E T i j (by omega) h
  intro t t1 t2
  have := Rin_lo E T i j; have := (T.H_FLUSH i hi).1
  have := rho0_Rin E j (i + 1); have := E.H_RST_EARLY; have := T.H_R0_LE
  exact fifo_hold (P.Rq (i + 1)) (G.H_REQ_LINE i hi) hO t t1 t2 (by omega)

omit G in
theorem ack_last (j : Nat) :
    ∀ t, P.Ain (P.N - 1) j ≤ t → t < P.Ain (P.N - 1) (j + 1) → a (P.N - 1) t = !Vph j := by
  have hn := T.H_N_POS
  intro t t1 t2
  rw [P.Ain_last _ j (by omega)] at t2
  cases j with
  | zero => simp only [PP.Ain] at t1; rw [E.H_ACK_LOW0 t t1 t2]; rfl
  | succ j =>
    rw [P.Ain_last _ j (by omega)] at t1
    rw [E.H_ACK j t t1 t2, Vph_succ, Bool.not_not]

theorem ack_zero (i : Nat) (hi : i + 1 < P.N) :
    ∀ t, P.Ain i 0 ≤ t → t < P.Ain i 1 → a i t = !Vph 0 := by
  intro t t1 t2
  rw [P.Ain_in i 0 hi] at t2
  simp only [PP.Ain] at t1
  simp only [PP.ackT, PipeTimedN.PN.ackT, show (0 : Nat) % 2 = 0 from rfl, ite_true] at t2
  have hl := T.H_FLUSH i hi
  have f1 := PipeTimedN.fmax_le (fun k => (P.Ap (i + 1) k).fst (P.out (i + 1)).hi)
    ((P.out (i + 1)).hi + P.ahi (i + 1)) (P.m (i + 1)) (P.toPN.fst_hi_all (i + 1) _)
  have := PipeTimedN.orn_hold_false (P.Ap (i + 1)) (P.m (i + 1)) (P.Ag (i + 1)) (G.H_ACK_LINE i hi)
    (a := (P.out (i + 1)).hi) (b := P.τ (i + 1) 0)
    (fun s h1 h2 => (pre G E T (i + 1) hi).2 s h1 h2) t (by omega) t2
    (by omega)
  rw [this]; rfl

theorem ack_succ (i j : Nat) (hi : i + 1 < P.N)
    (h : ∀ s, P.S (i + 1) j ≤ s → s < P.S (i + 1) (j + 1) →
      xs (P := P) (r := r) (a := a) (q := q) (rst := rst) (i + 1) s = Vph j) :
    ∀ t, P.Ain i (j + 1) ≤ t → t < P.Ain i (j + 1 + 1) → a i t = !Vph (j + 1) := by
  have hO := node_of G E T (i + 1) j hi h
  have hl := T.H_FLUSH i hi
  have hR0 := Ain_pos E T i (j + 1)
  have ht := tau_pos E T (i + 1) j
  have hge := P.ackT_ge' (i + 1) j (P.τ (i + 1) j)
  have hS := tau_ge (P := P) (i + 1) j
  have hS2 := S_lo_r E T (i + 1) j; have hr0 := rho0_Rin E j (i + 1)
  have := E.H_RST_EARLY; have := T.H_R0_LE
  rw [Vph_succ, Bool.not_not]
  intro t t1 t2
  rw [P.Ain_in i j hi] at t1; rw [P.Ain_in i (j + 1) hi] at t2
  have hgd : P.Ag (i + 1) ≤ t := by omega
  simp only [PP.ackT, PipeTimedN.PN.ackT] at t1 t2
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hv : Vph j = true := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [hj, ite_true] at t1
    simp only [show ¬ ((j + 1) % 2 = 0) by omega, ite_false] at t2
    have g := gap E T (i + 1) j hi; have fl := T.H_ACK_FLUSH i hi
    have a1 := PipeTimedN.fmax_le (fun k => (P.Ap (i + 1) k).fst (P.τ (i + 1) j))
      (P.τ (i + 1) j + P.ahi (i + 1)) (P.m (i + 1)) (P.toPN.fst_hi_all (i + 1) _)
    have a2 := PipeTimedN.le_fmin (fun k => (P.Ap (i + 1) k).fst (P.τ (i + 1) (j + 1)))
      (P.τ (i + 1) (j + 1) + P.alo (i + 1)) (P.m (i + 1))
      (P.toPN.fst_lo_all (i + 1) _ (tau_pos E T (i + 1) (j + 1)))
    exact PipeTimedN.orn_hold_true (P.Ap (i + 1)) (P.m (i + 1)) (P.Ag (i + 1)) (G.H_ACK_LINE i hi) hO
      (by unfold PP.ahi PP.alo at *; omega) t t1 t2 hgd
  · have hv : Vph j = false := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [show ¬ (j % 2 = 0) by omega, ite_false] at t1
    simp only [show (j + 1) % 2 = 0 by omega, ite_true] at t2
    exact PipeTimedN.orn_hold_false (P.Ap (i + 1)) (P.m (i + 1)) (P.Ag (i + 1)) (G.H_ACK_LINE i hi) hO
      t t1 t2 hgd

/-- The select-level excitation of stage `i` is `Vph j` over phase `j`. -/
def PhaseOK (i j : Nat) : Prop :=
  ∀ s, P.S i j ≤ s → s < P.S i (j + 1) → xs (P := P) (r := r) (a := a) (q := q) (rst := rst) i s = Vph j

/-- **(1) Clean control of the per-pin `N`-stage pipe.** For every phase `j`
and stage `i < N`, the excitation AT THE MUX-TREE SELECTS (each pin through its
own site-pin delay) equals `Vph j` on `[S i j, S i (j+1))`. No `H_LUT_FIFO`:
the controllers are `PinLut`s under `H_SELORD`. Same `2j + i` induction as 6f. -/
theorem pipe_ctl : ∀ j i, i < P.N → PhaseOK (P := P) (r := r) (a := a) (q := q) (rst := rst) i j := by
  intro j
  induction j with
  | zero =>
    intro i
    induction i with
    | zero =>
      intro hi
      apply phase_of G E T 0 0 hi (E.H_REQ 0)
      by_cases hl : 0 + 1 < P.N
      · exact ack_zero G E T 0 hl
      · have e : P.N - 1 = 0 := by omega
        have := ack_last E T 0; rw [e] at this; exact this
    | succ i ih =>
      intro hi
      apply phase_of G E T (i + 1) 0 hi (req_of G E T i 0 hi (ih (by omega)))
      by_cases hl : i + 1 + 1 < P.N
      · exact ack_zero G E T (i + 1) hl
      · have e : P.N - 1 = i + 1 := by omega
        have := ack_last E T 0; rw [e] at this; exact this
  | succ j ihj =>
    intro i
    induction i with
    | zero =>
      intro hi
      apply phase_of G E T 0 (j + 1) hi (E.H_REQ (j + 1))
      by_cases hl : 0 + 1 < P.N
      · exact ack_succ G E T 0 j hl (ihj 1 hl)
      · have e : P.N - 1 = 0 := by omega
        have := ack_last E T (j + 1); rw [e] at this; exact this
    | succ i ih =>
      intro hi
      apply phase_of G E T (i + 1) (j + 1) hi (req_of G E T i (j + 1) hi (ih (by omega)))
      by_cases hl : i + 1 + 1 < P.N
      · exact ack_succ G E T (i + 1) j hl (ihj (i + 1 + 1) hl)
      · have e : P.N - 1 = i + 1 := by omega
        have := ack_last E T (j + 1); rw [e] at this; exact this

/-- **(1') Every node is a clean step signal.** -/
theorem nodes_clean (i : Nat) (hi : i < P.N) :
    (∀ t, (P.out i).hi ≤ t → t < P.τ i 0 → O i t = false) ∧
    (∀ j t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j) :=
  ⟨(pre G E T i hi).2, fun j => node_of G E T i j hi (pipe_ctl G E T j i hi)⟩

/-- **(1'') Every internal pin is a clean four-phase signal.** -/
theorem pins_clean (i : Nat) (hi : i + 1 < P.N) :
    (∀ j t, P.Rin (i + 1) j ≤ t → t < P.Rin (i + 1) (j + 1) → r (i + 1) t = Vph j) ∧
    (∀ j t, P.Ain i j ≤ t → t < P.Ain i (j + 1) → a i t = !Vph j) := by
  refine ⟨fun j => req_of G E T i j hi (pipe_ctl G E T j i (by omega)), fun j => ?_⟩
  cases j with
  | zero => exact ack_zero G E T i hi
  | succ j => exact ack_succ G E T i j hi (pipe_ctl G E T j (i + 1) hi)

/-- **Liveness**: every node's edges strictly increase. No hypothesis beyond
the contract: `H_SELORD` and the loop's positive delay give `Won ≥ 1`. -/
theorem live (i j : Nat) (hi : i < P.N) : P.τ i j < P.τ i (j + 1) := by
  have g := gap E T i j hi; have ⟨o1, _⟩ := T.H_SELORD i hi
  have C := G.H_CTL i hi
  have := C.H_LOOP_POS; have := win_le C.H_FB; have := (P.pq i).lo_le_hi
  unfold PP.Won at g; omega

/-! ### Corollary: when does the 6e/6f assumption `H_LUT_FIFO` itself hold?

The pipe theorem above needs no `H_LUT_FIFO`. Bq's `pinlut_fifo_of_edges`
turns the proved select-level phases into `H_LUT_FIFO`, run by run, but only
if the PIN-level excitation `ex` is also clean, which needs the PIN-level
ordering `wh ≤ ER`, `wh ≤ EA` (6f's `H_LAT` without the LUT spread). That
condition is NOT implied by `H_SELORD` (it fails when the request pin is
slower than the feedback pin by more than the margin), so `H_LUT_FIFO` is
strictly stronger than what the circuit needs: a route can violate it and
still be clean. -/

/-- Pin-level phase start (6f's `c`). -/
def PP.cP (P : PP) (i j : Nat) : Nat := max (P.Rin i j) (P.Ain i j)

/-- The two input pins of stage `i` in phase `j` (from `pipe_ctl`). -/
theorem pins_of (i j : Nat) (hi : i < P.N) :
    (∀ t, P.Rin i j ≤ t → t < P.Rin i (j + 1) → r i t = Vph j) ∧
    (∀ t, P.Ain i j ≤ t → t < P.Ain i (j + 1) → a i t = !Vph j) := by
  constructor
  · cases i with
    | zero => exact E.H_REQ j
    | succ i => exact (pins_clean G E T i hi).1 j
  · by_cases h : i + 1 < P.N
    · exact (pins_clean G E T i h).2 j
    · have e : i = P.N - 1 := by omega
      subst e; exact ack_last E T j

/-- **`H_LUT_FIFO` recovered (run by run), under the extra PIN-level
ordering.** With `hpin : wh ≤ ER ∧ wh ≤ EA` (feedback reaches its PIN before
either departure reaches its PIN) and `hR : out.hi + wh ≤ R`, stage `i`'s node
is a FIFO read of its pin-level excitation `ex` (6e's `Ctl.H_LUT_FIFO`) with
band `[out.lo, max pr.hi pa.hi + out.hi]` (the pin share of the lower bound
is lost: Bq's lemma anchors both edge sequences at 0, which forces its `lo`
to 0). Proof: the
pin-level phases (here) and the select-level phases (`pipe_ctl`) are matched
edge by edge and fed to Bq's `pinlut_fifo_of_edges`. -/
theorem ctl_lut_fifo (i : Nat) (hi : i < P.N)
    (hpin : wh i ≤ P.ER Es i ∧ wh i ≤ P.EA Er i) (hR : (P.out i).hi + wh i ≤ P.R)
    (hpos : 1 ≤ (P.out i).lo + wl i) :
    ∃ L : Ret, L.lo = 0 + (P.out i).lo ∧
      L.hi = max (P.pr i).hi (P.pa i).hi + (P.out i).hi ∧
      ∀ t, L.hi ≤ t → O i t = ex (r i) (a i) (q i) rst (L.σ t) := by
  have C := G.H_CTL i hi
  have hRR := E.H_RST_EARLY; have hR0 := T.H_R0_LE
  have nc := nodes_clean G E T i hi
  -- pin-level phases
  have hph : ∀ j s, P.cP i j ≤ s → s < P.cP i (j + 1) → ex (r i) (a i) (q i) rst s = Vph j := by
    intro j s h1 h2
    have ⟨hreq, hack⟩ := pins_of G E T i j hi
    have dr := depR E T i j hi; have da := depA E T i j hi
    have r0 := rho0_Rin E j i
    have s1 := S_lo_r E T i (j + 1); have s2 := S_lo_a E T i (j + 1)
    have tg := tau_ge (P := P) i (j + 1)
    unfold PP.cP at h1 h2
    have hq : (P.Rin i (j + 1) ≤ s ∨ P.Ain i (j + 1) ≤ s) → q i s = Vph j := by
      intro hd
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      rw [e]; exact nc.2 j u (by omega) (by omega)
    unfold ex; rw [rst_lo G s (by omega)]
    by_cases c1 : s < P.Rin i (j + 1)
    · by_cases c2 : s < P.Ain i (j + 1)
      · rw [hreq s (by omega) c1, hack s (by omega) c2]; exact FifoFidelity.c2n_set _ _
      · rw [hq (Or.inr (by omega))]
        exact FifoFidelity.c2n_hold _ _ _ (Or.inl (hreq s (by omega) c1))
    · rw [hq (Or.inl (by omega))]
      exact FifoFidelity.c2n_hold _ _ _ (Or.inr (hack s (by omega) (by omega)))
  -- pin-level pre-phase
  have hreq0 : ∀ t, P.R0 ≤ t → t < P.Rin i 0 → r i t = false := by
    cases i with
    | zero => exact E.H_REQ_LOW0
    | succ i =>
      intro t t1 t2
      have hf := (T.H_FLUSH i hi).1; have g := (P.Rq (i + 1)).ge t
      rw [G.H_REQ_LINE i hi t (by omega)]
      exact (nodes_clean G E T i (by omega)).1 _ (by omega) ((P.Rq (i + 1)).fst_before t2)
  have hc0 : P.cP i 0 = P.Rin i 0 := by
    have := rho0_Rin E 0 i; unfold PP.cP; simp only [PP.Ain]; omega
  have hpre : ∀ s, s < P.cP i 0 → ex (r i) (a i) (q i) rst s = false := by
    intro s hs
    rw [hc0] at hs
    unfold ex
    by_cases h : s < P.R
    · rw [rst_hi G s h]; exact FifoFidelity.c2n_reset _ _ _
    · have s0 := S_ge_r (P := P) i 0; have tg := tau_ge (P := P) i 0
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      rw [rst_lo G s (by omega), hreq0 s (by omega) hs, e, nc.1 u (by omega) (by omega)]
      exact FifoFidelity.c2n_stay true false _ (Or.inl rfl)
  -- edge matching
  let c : Nat → Nat := fun j => match j with | 0 => 0 | j + 1 => P.cP i j
  let e : Nat → Nat := fun j => match j with | 0 => 0 | j + 1 => P.S i j
  let val : Nat → Bool := fun j => match j with | 0 => false | j + 1 => Vph j
  have cpos : ∀ j, 1 ≤ P.cP i j := fun j => by
    have := Rin_pos E T i j; unfold PP.cP; omega
  have cstep : ∀ j, P.cP i j < P.cP i (j + 1) := fun j => by
    have dr := depR E T i j hi; have tl := tau_lo E T i j; have s1 := S_ge_r (P := P) i j
    have s2 : P.Ain i j ≤ P.S i j := by
      have := (P.pa i).fst_ge (P.Ain i j); unfold PP.S PP.sel; omega
    have := win_le C.H_FB
    unfold PP.cP; omega
  have estep : ∀ j, P.S i j < P.S i (j + 1) := fun j => by
    have dr := depR E T i j hi; have tl := tau_lo E T i j
    have s1 := S_lo_r E T i (j + 1); have ⟨o1, _⟩ := T.H_SELORD i hi
    have := C.H_LOOP_POS; have := win_le C.H_FB; have := (P.pq i).lo_le_hi
    omega
  have chain : ∀ (f : Nat → Nat), (∀ j, f j < f (j + 1)) → ∀ a b, a < b → f a < f b := by
    intro f hf a b hab
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_or_ge a b with h | h
      · have := ih h; have := hf b; omega
      · have : a = b := by omega
        subst this; exact hf a
  have hce : ∀ a b, a < b → c a < c b := by
    apply chain; intro j; cases j with
    | zero => exact cpos 0
    | succ j => exact cstep j
  have hmono : ∀ a b, a < b → e a < e b := by
    apply chain; intro j; cases j with
    | zero => exact S_pos E T i 0
    | succ j => exact estep j
  have hlo : ∀ j, c j + 0 ≤ e j := by
    intro j; cases j with
    | zero => exact Nat.le_refl _
    | succ j =>
      show P.cP i j + 0 ≤ P.S i j
      have := S_ge_r (P := P) i j; have := (P.pa i).fst_ge (P.Ain i j)
      unfold PP.cP; unfold PP.S PP.sel at *; omega
  have hhi : ∀ j, e j ≤ c j + max (P.pr i).hi (P.pa i).hi := by
    intro j; cases j with
    | zero => exact Nat.zero_le _
    | succ j =>
      show P.S i j ≤ P.cP i j + max (P.pr i).hi (P.pa i).hi
      have := (P.pa i).fst_le (P.Ain i j); have := (P.pr i).fst_le (P.Rin i j)
      unfold PP.cP PP.S PP.sel; omega
  have hx : ∀ j s, c j ≤ s → s < c (j + 1) → ex (r i) (a i) (q i) rst s = val j := by
    intro j s h1 h2; cases j with
    | zero => exact hpre s h2
    | succ j => exact hph j s h1 h2
  have hy : ∀ j t, e j ≤ t → t < e (j + 1) →
      exSel (P.pr i) (P.pa i) (P.pq i) (P.ps i) (r i) (a i) (q i) rst t = val j := by
    intro j t h1 h2; cases j with
    | zero => exact (pre G E T i hi).1 t h2
    | succ j => exact pipe_ctl G E T j i hi t h1 h2
  obtain ⟨L, hl, hh, hL⟩ := FifoFidelity.pinlut_fifo_of_edges C.pinLut c e 0
    (max (P.pr i).hi (P.pa i).hi) (Nat.zero_le _) val rfl rfl hce hmono hlo hhi hx hy
  exact ⟨L, by rw [hl]; rfl, by rw [hh]; rfl, hL⟩

end ctl

/-! ## 6. The data path: every token through every stage

As 6f, with each boundary's credit `Rq.lo + L.lo` replaced by the per-pin
`Rq.lo + pr.lo + out.lo` (the request reaches stage `b`'s node through its
REQUEST site pin) and the DACK credit followed by stage `b-1`'s ACK site pin. -/

def Dl (P : PP) (V : Nat → Win) (Sdr Lag : Nat) : Nat → Nat → Int
  | 0, b => max ((V 0).ehi b : Int) ((Lag : Int) - Sdr - (P.pr 0).lo - (P.out 0).lo + (V 0).dhi b)
  | i + 1, b => max ((V (i + 1)).ehi b : Int)
      (Dl P V Sdr Lag i b - (P.Rq (i + 1)).lo - (P.pr (i + 1)).lo - (P.out (i + 1)).lo + (V (i + 1)).dhi b)

def PP.Sx (P : PP) (V : Nat → Win) (dS : Nat → Nat) (k b : Nat) : Nat → Nat
  | 0 => max (P.τ 0 (2 * k) + (V 0).ehi b) (dS k + (V 0).dhi b)
  | i + 1 => max (P.τ (i + 1) (2 * k) + (V (i + 1)).ehi b) (PP.Sx P V dS k b i + (V (i + 1)).dhi b)

/-- **Data-path hypotheses and obligations** (6f's `DataN`, per-pin credits). -/
structure DataP (P : PP) (O : Nat → Trace) (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig)
    (val : Nat → Nat → Bool) (dS dE : Nat → Nat) (V : Nat → Win)
    (W Es Er Erel Sdr Lag : Nat) : Prop where
  /-- **H_LATCH i**: 6c's Kleene latch over pin windows, enable = node. -/
  H_LATCH : ∀ i b, i < P.N → b < W → Bundling.LatchRel (PipeTimedN.din d x i b) (O i) (x i b)
    ((V i).dlo b) ((V i).dhi b) ((V i).elo b) ((V i).ehi b) ((V i).flo b) ((V i).fhi b)
  H_WIN : ∀ i b, i < P.N → b < W → (V i).dlo b ≤ (V i).dhi b ∧ (V i).elo b ≤ (V i).ehi b ∧
    (V i).flo b ≤ (V i).fhi b ∧ 1 ≤ (V i).flo b
  H_DATA_VALID : ∀ k b t, b < W → dS k ≤ t → t < dE k → d b t = val k b
  /-- **H_DATA_LEAD** (rule A at the input). -/
  H_DATA_LEAD : ∀ k, dS k + Sdr ≤ P.ρ (2 * k) + Lag
  H_DATA_REL : ∀ k, P.τ 0 (2 * k + 1) + Erel ≤ dE k
  /-- **H_HOLD0** (rule H at the input). -/
  H_HOLD0 : ∀ b, b < W → (V 0).ehi b ≤ Erel + (V 0).dlo b
  /-- **H_PW i** (no rule). -/
  H_PW : ∀ i b, i < P.N → b < W → (V i).ehi b + (V i).fhi b ≤ P.Won Es Er i + (V i).elo b
  /-- **H_SETUP0** (rule I at the input). -/
  H_SETUP0 : ∀ b, b < W →
    (V 0).dhi b + (V 0).fhi b + Lag ≤ Sdr + (P.pr 0).lo + (P.out 0).lo + P.Won Es Er 0 + (V 0).elo b
  /-- **H_I b** (rule I at boundary `b = i + 1`), per-pin credit. -/
  H_I : ∀ i b, i + 1 < P.N → b < W →
    Dl P V Sdr Lag i b + (V (i + 1)).dhi b + (V (i + 1)).fhi b ≤
      ((P.Won Es Er i + (P.Rq (i + 1)).lo + (P.pr (i + 1)).lo + (P.out (i + 1)).lo +
        (V (i + 1)).elo b : Nat) : Int)
  /-- **H_H b** (rule H at boundary `b = i + 1`): DACK slow-path credit, then
  stage `i`'s ACK site pin and tree. -/
  H_H : ∀ i b, i + 1 < P.N → b < W →
    (V (i + 1)).ehi b ≤ P.aslow (i + 1) + (P.pa i).lo + (P.out i).lo + (V i).elo b +
      (V (i + 1)).dlo b

section data
variable {P : PP} {rst : Trace} {r a O q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
  {d : Nat → Bundling.Sig} {x : Nat → Nat → Bundling.Sig} {val : Nat → Nat → Bool}
  {dS dE : Nat → Nat} {V : Nat → Win} {W Erel Sdr Lag : Nat}

theorem Sx_le (E : EnvP P (r 0) (a (P.N - 1)) Es Er) (T : TimingP P wh Es Er)
    (hlead : ∀ k, dS k + Sdr ≤ P.ρ (2 * k) + Lag) (k b : Nat) :
    ∀ i, (P.Sx V dS k b i : Int) ≤ (P.τ i (2 * k) : Int) + Dl P V Sdr Lag i b := by
  intro i
  induction i with
  | zero =>
    have := rho_le E T (2 * k); have := hlead k
    simp only [PP.Sx, Dl]; omega
  | succ i ih =>
    have := fwd E T i (2 * k)
    simp only [PP.Sx, Dl] at ih ⊢; omega

variable (G : GatesP P rst r a O q wl wh) (E : EnvP P (r 0) (a (P.N - 1)) Es Er)
  (T : TimingP P wh Es Er) (D : DataP P O d x val dS dE V W Es Er Erel Sdr Lag)
include G E T D

/-- **(2) Every stage latches every token, every bit.** -/
theorem token (k b : Nat) (hb : b < W) : ∀ i, i < P.N →
    ∀ t, P.Sx V dS k b i ≤ t → t < P.τ i (2 * k + 1 + 1) + (V i).elo b → x i b t = val k b := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hn := (nodes_clean G E T 0 hi).2
    have hon : ∀ t, P.τ 0 (2 * k) ≤ t → t < P.τ 0 (2 * k + 1) → O 0 t = true := by
      intro t u v; have := hn (2 * k) t u v; rwa [Vph_even] at this
    have hoff : ∀ t, P.τ 0 (2 * k + 1) ≤ t → t < P.τ 0 (2 * k + 1 + 1) → O 0 t = false := by
      intro t u v; have := hn (2 * k + 1) t u v; rwa [Vph_odd] at this
    have ⟨hdw, hew, hfw, hpos⟩ := D.H_WIN 0 b hi hb
    have g := gap E T 0 (2 * k) hi; have rl := rho_le E T (2 * k); have l := D.H_DATA_LEAD k
    have pw := D.H_PW 0 b hi hb; have su := D.H_SETUP0 b hb
    have rel := D.H_DATA_REL k; have ho := D.H_HOLD0 b hb
    exact Bundling.capture (d b) (O 0) (x 0 b) _ _ _ _ _ _ (D.H_LATCH 0 b hi hb) hdw hew hfw hpos
      (P.τ 0 (2 * k)) (P.τ 0 (2 * k + 1)) (P.τ 0 (2 * k + 1 + 1)) (dS k) (dE k) (val k b)
      hon hoff (fun t h1 h2 => D.H_DATA_VALID k b t hb h1 h2) (by omega) (by omega)
  | succ i ih =>
    intro hi
    have hn := (nodes_clean G E T (i + 1) hi).2
    have hon : ∀ t, P.τ (i + 1) (2 * k) ≤ t → t < P.τ (i + 1) (2 * k + 1) → O (i + 1) t = true := by
      intro t u v; have := hn (2 * k) t u v; rwa [Vph_even] at this
    have hoff : ∀ t, P.τ (i + 1) (2 * k + 1) ≤ t → t < P.τ (i + 1) (2 * k + 1 + 1) →
        O (i + 1) t = false := by
      intro t u v; have := hn (2 * k + 1) t u v; rwa [Vph_odd] at this
    have ⟨hdw, hew, hfw, hpos⟩ := D.H_WIN (i + 1) b hi hb
    have g1 := gap E T (i + 1) (2 * k) hi; have g0 := gap E T i (2 * k) (by omega)
    have f := fwd E T i (2 * k + 1)
    have sl := Sx_le (V := V) E T D.H_DATA_LEAD k b i
    have bo := back_odd E T i (2 * k + 1) hi (by omega)
    have pw := D.H_PW (i + 1) b hi hb; have iI := D.H_I i b hi hb
    have hH := D.H_H i b hi hb
    exact Bundling.capture (x i b) (O (i + 1)) (x (i + 1) b) _ _ _ _ _ _
      (D.H_LATCH (i + 1) b hi hb) hdw hew hfw hpos
      (P.τ (i + 1) (2 * k)) (P.τ (i + 1) (2 * k + 1)) (P.τ (i + 1) (2 * k + 1 + 1))
      (P.Sx V dS k b i) (P.τ i (2 * k + 1 + 1) + (V i).elo b) (val k b)
      hon hoff (ih (by omega)) (by omega) (by omega)

/-- **(3) The per-pin pipe delivers every token.** -/
theorem pipe_forward (k b : Nat) (hb : b < W) :
    (∀ t, P.Sx V dS k b (P.N - 1) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b) ∧
    (Dl P V Sdr Lag (P.N - 1) b ≤ (Er : Int) →
      ∀ t, P.γ (2 * k) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b) := by
  have hn := T.H_N_POS
  have g := gam_le E T (2 * k + 1)
  have rc := E.H_RCV (2 * k)
  have sl := Sx_le (V := V) E T D.H_DATA_LEAD k b (P.N - 1)
  refine ⟨fun t h1 h2 => token G E T D k b hb (P.N - 1) (by omega) t h1 (by omega),
    fun o t h1 h2 => token G E T D k b hb (P.N - 1) (by omega) t (by omega) (by omega)⟩

end data

/-! ## 7. Non-vacuity for every `N ≥ 1`, with UNEQUAL pin delays

Per stage: request pin (I0) 1 tick, acknowledge pin (I1) 2, **feedback pin
(I2) 3** (the slowest: Bq's unfavourable placement, feedback on the slow
site pin), reset pin 1, tree + output 1; feedback wire 1; request and DACK
lines 1 (`DACK = 1`). Reset released at 4, pins flushed from 2. Sender
latency 6, receiver 4. Every phase lasts 8 ticks; stage `i`'s phase `j`
starts at its selects at `8 + 3i + 8j` and its node edge is at
`τ i j = 9 + 3i + 8j` (`tt_w`, solved from the recursion, not stated).

At the selects the acknowledge arrives one tick BEFORE the request and
departs one tick before it, so for one tick per phase the excitation is held
by the feedback alone (`c2n_hold`): the feedback ordering is exercised. The
feedback reaches its select 4 ticks after the node edge (`wh + pq.hi`), the
first departure (acknowledge) 6 ticks after: `H_SELORD` holds with margin 2. -/

namespace Wit
open PipeTimed.Wit

/-- Square wave of half-period 8: low before `o`, then 8 high, 8 low, … -/
def sq8 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 16 < 8)

theorem sq8_pre (o t : Nat) (h : t < o) : sq8 o t = false := by unfold sq8; simp; omega

theorem sq8_shift (o d t : Nat) : sq8 (o + d) (t + d) = sq8 o t := by
  unfold sq8
  have e : t + d - (o + d) = t - o := by omega
  rw [e]
  by_cases h : o ≤ t
  · simp [h, show o + d ≤ t + d by omega]
  · simp [h, show ¬ (o + d ≤ t + d) by omega]

theorem sq8_sub (o d t : Nat) (ho : 1 ≤ o) : sq8 (o + d) t = sq8 o (t - d) := by
  by_cases h : d ≤ t
  · have := sq8_shift o d (t - d); rw [Nat.sub_add_cancel h] at this; exact this
  · rw [sq8_pre _ _ (by omega), sq8_pre _ _ (by omega)]

theorem sq8_phase (o j t : Nat) (h1 : o + 8 * j ≤ t) (h2 : t < o + 8 * (j + 1)) :
    sq8 o t = Vph j := by
  unfold sq8 Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 16 < 8 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 16 < 8) := by omega
    simp [hj, this]


/-- **The real `bd_c2n` INIT at the selects** of the witness: request select
`sq8 o`, acknowledge select `sq8 (o+7)` (one tick early), feedback select
`sq8 (o+5)`: the excitation is the request select itself, including the
one-tick hold phases (`(s - o) % 16 = 7` and `= 15`). -/
theorem key8 (o s : Nat) (ho : 8 ≤ o) :
    CElemTiming.exc CElemTiming.INIT_c2n (sq8 o s) (sq8 (o + 7) s) (sq8 (o + 5) s) (rstW (s - 1))
      = sq8 o s := by
  rw [CElemTiming.c2n_eq]
  by_cases h0 : s < o
  · rw [sq8_pre o s h0, sq8_pre (o + 5) s (by omega)]
    cases rstW (s - 1) <;> cases sq8 (o + 7) s <;> rfl
  · have hr : rstW (s - 1) = false := by unfold rstW; simp; omega
    rw [hr]
    have hm : (s - o) % 16 < 16 := Nat.mod_lt _ (by omega)
    by_cases hA : (s - o) % 16 < 7
    · have e1 : sq8 o s = true := by unfold sq8; simp; omega
      have e2 : sq8 (o + 7) s = false := by unfold sq8; simp; omega
      rw [e1, e2]; cases sq8 (o + 5) s <;> rfl
    · by_cases hB : (s - o) % 16 = 7
      · have e1 : sq8 o s = true := by unfold sq8; simp; omega
        have e2 : sq8 (o + 7) s = true := by unfold sq8; simp; omega
        have e3 : sq8 (o + 5) s = true := by unfold sq8; simp; omega
        rw [e1, e2, e3]; rfl
      · by_cases hC : (s - o) % 16 < 15
        · have e1 : sq8 o s = false := by unfold sq8; simp; omega
          have e2 : sq8 (o + 7) s = true := by unfold sq8; simp; omega
          rw [e1, e2]; cases sq8 (o + 5) s <;> rfl
        · have e1 : sq8 o s = false := by unfold sq8; simp; omega
          have e2 : sq8 (o + 7) s = false := by unfold sq8; simp; omega
          have e3 : sq8 (o + 5) s = false := by unfold sq8; simp; omega
          rw [e1, e2, e3]; rfl

/-- The witness realisation with `N` stages. -/
def Pw (N : Nat) : PP where
  N := N
  R := 4
  R0 := 2
  pr _ := Ret.shift 1
  pa _ := Ret.shift 2
  pq _ := Ret.shift 3
  ps _ := Ret.shift 1
  out _ := Ret.shift 1
  Rq _ := Ret.shift 1
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ j := 7 + 8 * j
  γ j := 13 + 3 * (N - 1) + 8 * j

theorem fstd (d c : Nat) (h : 1 ≤ c) : (Ret.shift d).fst c = c + d := Ret.fst_shift d c h

theorem ackT_w (N b j τ : Nat) (h : 1 ≤ τ) : (Pw N).ackT b j τ = τ + 1 := by
  show (if j % 2 = 0 then (Ret.shift 1).fst τ else (Ret.shift 1).fst τ) = _
  rw [fstd 1 τ h]; split <;> rfl

theorem row_w (N j : Nat) (α : Nat → Nat) (hα : ∀ i, 1 ≤ α i ∧ α i + 2 ≤ 8 + 3 * i + 8 * j) :
    ∀ i, (Pw N).row j α i = 9 + 3 * i + 8 * j := by
  intro i
  induction i with
  | zero =>
    show (Ret.shift 1).fst (max ((Ret.shift 1).fst (7 + 8 * j)) ((Ret.shift 2).fst (α 0))) = _
    have := hα 0
    rw [fstd 1 (7 + 8 * j) (by omega), fstd 2 _ this.1, fstd 1 _ (by omega)]; omega
  | succ i ih =>
    show (Ret.shift 1).fst (max ((Ret.shift 1).fst ((Ret.shift 1).fst ((Pw N).row j α i)))
      ((Ret.shift 2).fst (α (i + 1)))) = _
    have := hα (i + 1)
    rw [ih, fstd 1 (9 + 3 * i + 8 * j) (by omega), fstd 1 (9 + 3 * i + 8 * j + 1) (by omega),
      fstd 2 _ this.1, fstd 1 _ (by omega)]; omega

/-- The event-time recursion, solved: `τ i j = 9 + 3i + 8j`. -/
theorem tt_w (N : Nat) : ∀ j i, (Pw N).tt j i = 9 + 3 * i + 8 * j := by
  intro j
  induction j with
  | zero => exact row_w N 0 (fun _ => 2) (fun i => by omega)
  | succ j ih =>
    apply row_w
    intro i
    show 1 ≤ (if i + 1 < N then (Pw N).ackT (i + 1) j ((Pw N).tt j (i + 1))
      else 13 + 3 * (N - 1) + 8 * j) ∧
      (if i + 1 < N then (Pw N).ackT (i + 1) j ((Pw N).tt j (i + 1))
      else 13 + 3 * (N - 1) + 8 * j) + 2 ≤ _
    split
    · rw [ih, ackT_w N _ _ _ (by omega)]; omega
    · omega

theorem τ_w (N i j : Nat) : (Pw N).τ i j = 9 + 3 * i + 8 * j := tt_w N j i

def rW (i : Nat) : Trace := sq8 (7 + 3 * i)
def aW (i : Nat) : Trace := sq8 (13 + 3 * i)
def OW (i : Nat) : Trace := sq8 (9 + 3 * i)
def qW (i : Nat) : Trace := sq8 (10 + 3 * i)

/-- One per-pin controller of the witness: every gate relation, every instant. -/
theorem ctl_w (i : Nat) :
    CtlP (rW i) (aW i) rstW (OW i) (qW i) (Ret.shift 1) (Ret.shift 2) (Ret.shift 3) (Ret.shift 1)
      (Ret.shift 1) 1 1 where
  H_OUT t ht := by
    show sq8 (9 + 3 * i) t = CElemTiming.exc CElemTiming.INIT_c2n (sq8 (7 + 3 * i) (t - 1 - 1))
      (sq8 (13 + 3 * i) (t - 1 - 2)) (sq8 (10 + 3 * i) (t - 1 - 3)) (rstW (t - 1 - 1))
    rw [show 9 + 3 * i = (8 + 3 * i) + 1 by omega, sq8_sub _ 1 t (by omega),
      show 7 + 3 * i = (8 + 3 * i) - 1 by omega,
      ← sq8_sub ((8 + 3 * i) - 1) 1 (t - 1) (by omega),
      show 13 + 3 * i = (8 + 3 * i + 7) - 2 by omega,
      ← sq8_sub (8 + 3 * i + 7 - 2) 2 (t - 1) (by omega),
      show 10 + 3 * i = (8 + 3 * i + 5) - 3 by omega,
      ← sq8_sub (8 + 3 * i + 5 - 3) 3 (t - 1) (by omega)]
    rw [show 8 + 3 * i - 1 + 1 = 8 + 3 * i by omega, show 8 + 3 * i + 7 - 2 + 2 = 8 + 3 * i + 7 by omega,
      show 8 + 3 * i + 5 - 3 + 3 = 8 + 3 * i + 5 by omega]
    exact (key8 (8 + 3 * i) (t - 1) (by omega)).symm
  H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
    (fun t => by show sq8 (10 + 3 * i) (t + 1) = sq8 (9 + 3 * i) t
                 rw [show 10 + 3 * i = 9 + 3 * i + 1 by omega]; exact sq8_shift _ 1 t)
  H_LOOP_POS := by decide

theorem gates_w (N : Nat) : GatesP (Pw N) rstW rW aW OW qW (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i _ := ctl_w i
  H_REQ_LINE i _ t _ := by
    show sq8 (7 + 3 * (i + 1)) t = sq8 (9 + 3 * i) (t - 1)
    rw [show 7 + 3 * (i + 1) = 9 + 3 * i + 1 by omega]; exact sq8_sub _ 1 t (by omega)
  H_ACK_LINE i _ t _ := by
    show sq8 (13 + 3 * i) t = sq8 (9 + 3 * (i + 1)) (t - 1)
    rw [show 13 + 3 * i = 9 + 3 * (i + 1) + 1 by omega]; exact sq8_sub _ 1 t (by omega)

theorem env_w (N : Nat) (_hN : 1 ≤ N) : EnvP (Pw N) (rW 0) (aW ((Pw N).N - 1)) 6 4 where
  H_REQ_LOW0 t _ h2 := sq8_pre _ t (by simp only [Pw] at h2; omega)
  H_REQ j t h1 h2 := sq8_phase _ j t (by simp only [Pw] at h1; omega) (by simp only [Pw] at h2; omega)
  H_ACK_LOW0 t _ h2 := sq8_pre _ t (by simp only [Pw] at h2 ⊢; omega)
  H_ACK j t h1 h2 := by
    show sq8 (13 + 3 * (N - 1)) t = Vph j
    exact sq8_phase _ j t (by simp only [Pw] at h1; omega) (by simp only [Pw] at h2; omega)
  H_SND j := by rw [τ_w]; show 9 + 3 * 0 + 8 * j + 6 ≤ 7 + 8 * (j + 1); omega
  H_RCV j := by rw [τ_w]; show 9 + 3 * (N - 1) + 8 * j + 4 ≤ 13 + 3 * (N - 1) + 8 * j; omega
  H_RST_EARLY := by show 4 ≤ 7 + 8 * 0; omega

theorem alo_w (N b : Nat) : (Pw N).alo b = 1 := rfl
theorem ahi_w (N b : Nat) : (Pw N).ahi b = 1 := rfl
theorem aslow_w (N b : Nat) : (Pw N).aslow b = 1 := rfl

theorem ER_w (N i : Nat) : 5 ≤ (Pw N).ER 6 i := by
  cases i with
  | zero => show 5 ≤ 6; omega
  | succ i => show 5 ≤ 1 + 2 + 1 + 1; omega

theorem EA_w (N i : Nat) : (Pw N).EA 4 i = 4 := by
  unfold PP.EA; split <;> rfl

theorem Won_w (N i : Nat) : 7 ≤ (Pw N).Won 6 4 i := by
  have := ER_w N i
  unfold PP.Won; rw [EA_w]; show 7 ≤ 1 + max ((Pw N).ER 6 i + 1) (4 + 2); omega

theorem timing_w (N : Nat) (hN : 1 ≤ N) : TimingP (Pw N) (fun _ => 1) 6 4 where
  H_N_POS := hN
  H_R0_POS := by show 1 ≤ 2; omega
  H_R0_LE := by show 2 ≤ 4; omega
  H_RST_SEL _ _ := by show 2 + 1 ≤ 4 + 1 ∧ 1 + 1 + 3 ≤ 4 + 1 ∧ 4 + 1 ≤ 7 + 8 * 0 + 1 ∧
    2 + 2 ≤ 7 + 8 * 0 + 1; omega
  H_FLUSH _ _ := by show 1 + 1 ≤ 2 ∧ 1 + 1 ≤ 2 ∧ 1 ≤ 2; omega
  H_SELORD i _ := by
    have := ER_w N i; rw [EA_w]; show 1 + 3 ≤ (Pw N).ER 6 i + 1 ∧ 1 + 3 ≤ 4 + 2; omega
  H_ACK_FLUSH i _ := by have := Won_w N (i + 1); rw [ahi_w, alo_w]; omega

/-- **Non-vacuity of the per-pin control contract, every `N ≥ 1`, unequal
pin delays.** The run satisfies every field of `GatesP`, `EnvP`, `TimingP`
at every instant; its pin maps differ (`pr ≠ pa ≠ pq` in delay, the feedback
pin slowest), and every node alternates every 8 ticks. -/
theorem witness (N : Nat) (hN : 1 ≤ N) :
    GatesP (Pw N) rstW rW aW OW qW (fun _ => 1) (fun _ => 1) ∧
    EnvP (Pw N) (rW 0) (aW ((Pw N).N - 1)) 6 4 ∧ TimingP (Pw N) (fun _ => 1) 6 4 ∧
    (∀ i, ((Pw N).pr i).hi = 1 ∧ ((Pw N).pa i).hi = 2 ∧ ((Pw N).pq i).hi = 3) ∧
    (∀ i j, (Pw N).τ i j = 9 + 3 * i + 8 * j) ∧
    (∀ i, OW i (9 + 3 * i) = true ∧ OW i (17 + 3 * i) = false) := by
  refine ⟨gates_w N, env_w N hN, timing_w N hN, fun _ => ⟨rfl, rfl, rfl⟩, τ_w N,
    fun i => ⟨?_, ?_⟩⟩ <;> (unfold OW sq8; simp <;> omega)

/-! ### Data path of the witness: one bit, alternating tokens, ODD latches -/

def dW8 (t : Nat) : Bool := decide ((t - 2) % 32 < 16)
def dSW8 (k : Nat) : Nat := 2 + 16 * k
def dEW8 (k : Nat) : Nat := 18 + 16 * k
/-- Stage `i`'s latch output: token `m` on `[10 + 3i + 16m, 26 + 3i + 16m)`. -/
def xW (i t : Nat) : Bool := decide (10 + 3 * i ≤ t ∧ (t - (10 + 3 * i)) % 32 < 16)
def VWn : Nat → Win := fun _ => VW

theorem xW_rel0 (t : Nat) : xW 0 t = (if OW 0 (t - 1) then dW8 (t - 1) else xW 0 (t - 1)) := by
  unfold OW
  split
  · next h => unfold sq8 at h; simp at h; unfold xW dW8; simp only [decide_eq_decide]; omega
  · next h => unfold sq8 at h; simp at h; unfold xW; simp only [decide_eq_decide]; omega

theorem xW_rel (i t : Nat) :
    xW (i + 1) t = (if OW (i + 1) (t - 1) then xW i (t - 1) else xW (i + 1) (t - 1)) := by
  unfold OW
  split
  · next h => unfold sq8 at h; simp at h; unfold xW; simp only [decide_eq_decide]; omega
  · next h => unfold sq8 at h; simp at h; unfold xW; simp only [decide_eq_decide]; omega

theorem Dl_w (N : Nat) : ∀ i b, Dl (Pw N) VWn 2 0 i b = 1 := by
  intro i b
  induction i with
  | zero => show max ((1 : Nat) : Int) (((0 : Nat) : Int) - ((2 : Nat) : Int) - ((1 : Nat) : Int)
      - ((1 : Nat) : Int) + ((1 : Nat) : Int)) = 1; decide
  | succ i ih =>
    show max ((1 : Nat) : Int) (Dl (Pw N) VWn 2 0 i b - ((1 : Nat) : Int) - ((1 : Nat) : Int)
      - ((1 : Nat) : Int) + ((1 : Nat) : Int)) = 1
    rw [ih]; decide

theorem data_w (N : Nat) : DataP (Pw N) OW (fun _ => dW8) (fun i _ => xW i)
    valW dSW8 dEW8 VWn 1 6 4 1 2 0 where
  H_LATCH i _ _ _ := by
    cases i with
    | zero => exact latch_of dW8 (OW 0) (xW 0) xW_rel0
    | succ i => exact latch_of (xW i) (OW (i + 1)) (xW (i + 1)) (xW_rel i)
  H_WIN _ _ _ _ := by simp [VWn, VW]
  H_DATA_VALID k _ t _ h1 h2 := by
    unfold dSW8 at h1; unfold dEW8 at h2; unfold dW8 valW
    simp only [decide_eq_decide]; omega
  H_DATA_LEAD k := by show 2 + 16 * k + 2 ≤ 7 + 8 * (2 * k) + 0; omega
  H_DATA_REL k := by rw [τ_w]; show 9 + 3 * 0 + 8 * (2 * k + 1) + 1 ≤ 18 + 16 * k; omega
  H_HOLD0 _ _ := by simp [VWn, VW]
  H_PW i _ _ _ := by have := Won_w N i; simp only [VWn, VW]; omega
  H_SETUP0 _ _ := by have := Won_w N 0; simp only [VWn, VW, Pw, Ret.shift]; omega
  H_I i b _ _ := by
    have := Won_w N i; rw [Dl_w]; simp only [VWn, VW, Pw, Ret.shift]; omega
  H_H _ _ _ _ := by rw [aslow_w]; simp only [VWn, VW, Pw, Ret.shift]; omega

/-- **Non-vacuity, data side, every `N ≥ 1`**: `pipe_forward` applies to the
unequal-pin run; the last stage delivers every token, values alternate. -/
theorem witness_data (N : Nat) (hN : 1 ≤ N) :
    DataP (Pw N) OW (fun _ => dW8) (fun i _ => xW i) valW dSW8 dEW8 VWn 1 6 4 1 2 0 ∧
    (∀ k t, (Pw N).γ (2 * k) ≤ t → t < (Pw N).γ (2 * k + 1) →
      xW (N - 1) t = decide (k % 2 = 0)) ∧
    xW (N - 1) ((Pw N).γ 0) = true ∧ xW (N - 1) ((Pw N).γ 2) = false := by
  refine ⟨data_w N, fun k t h1 h2 => ?_, ?_, ?_⟩
  · exact (pipe_forward (gates_w N) (env_w N hN) (timing_w N hN) (data_w N) k 0 (by omega)).2
      (by rw [Dl_w]; decide) t h1 h2
  · show decide (10 + 3 * (N - 1) ≤ 13 + 3 * (N - 1) + 8 * 0 ∧
      (13 + 3 * (N - 1) + 8 * 0 - (10 + 3 * (N - 1))) % 32 < 16) = true
    rw [decide_eq_true_iff]; omega
  · show decide (10 + 3 * (N - 1) ≤ 13 + 3 * (N - 1) + 8 * 2 ∧
      (13 + 3 * (N - 1) + 8 * 2 - (10 + 3 * (N - 1))) % 32 < 16) = false
    rw [decide_eq_false_iff_not]; omega

end Wit

/-! ## 8. The Bq counterexample violates `H_SELORD`, and only it

Bq's run (`FifoFidelity.ceLut`): request pin 1, acknowledge pin 1, feedback
pin **6**, reset pin 1, tree 2, feedback wire 1; the upstream stage withdraws
the request 3 ticks after the node edge (node rises at 13, request falls at
16), so the request-side round trip is `ER = 3`. It IS a `CtlP` controller
(`ce_ctlp`: every gate relation of this file's model holds at every
instant). Its numbers violate the per-stage obligation
`wh + pq.hi ≤ ER + pr.lo` (`1 + 6 > 3 + 1`), and the node glitches
(`ce_node`: rises at 13, drops at 19, rises at 22, then oscillates). The same
environment with the feedback on a 1-tick pin (`cjLut`) satisfies it
(`1 + 1 ≤ 3 + 1`) and is clean (`cj_clean`). -/

open FifoFidelity in
/-- Bq's counterexample run is a behaviour of the per-pin controller model. -/
theorem ce_ctlp : CtlP reqC zeroT zeroT OC qpC (Ret.shift 1) (Ret.shift 1) (Ret.shift 6) (Ret.shift 1)
    (Ret.shift 2) 1 1 where
  H_OUT := ceLut.H_OUT
  H_FB := ce_fb
  H_LOOP_POS := by decide

open FifoFidelity in
/-- **The counterexample violates `H_SELORD`; its fast-feedback twin
satisfies it.** With `ER = 3` (request withdrawn 3 ticks after the node edge),
`wh = 1`: slow feedback pin `1 + 6 > 3 + 1` and the node makes a runt;
1-tick feedback pin `1 + 1 ≤ 3 + 1` and the node makes one edge. -/
theorem ce_violates :
    ¬ (1 + (Ret.shift 6).hi ≤ 3 + (Ret.shift 1).lo) ∧
    (OC 13 = true ∧ OC 19 = false ∧ OC 22 = true) ∧
    (1 + (Ret.shift 1).hi ≤ 3 + (Ret.shift 1).lo) ∧
    (∀ t, OJ t = decide (13 ≤ t)) := by
  refine ⟨by decide, ⟨ce_node.2.1, ce_node.2.2.2.1, ce_node.2.2.2.2⟩, by decide, cj_clean⟩

end Formal.Cells.PipePerPin
