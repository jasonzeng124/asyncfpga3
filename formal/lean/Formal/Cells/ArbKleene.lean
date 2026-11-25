import Formal.Core.LutList
open Formal.Core.LutList

/-!
# Probe 7b: the arbiter in Kleene three-valued logic

Cells: `bd_arbcell` and `bd_arbiter` (`cells/rtl/bd_arb.v`), with the ack
C-elements `bd_c2` (`cells/rtl/bd_ce.v`). Every output below is evaluated with
`lutK`/`o5K`/`o6K` on the REAL INIT constants and the REAL pin maps of the
RTL; nothing is a hand-written equation except where a lemma proves the INIT
equal to one.

Hypotheses used (all of them; nothing else is assumed):

* **H_KLEENE_LUT** (from `Prelim`): a LUT's Kleene output is the closure of
  its INIT over all Boolean completions of its inputs. Physical fact: the
  pass-transistor mux tree passes a definite level when every leg the
  intermediate selects can reach carries it. Test: GLS / board injection of a
  slow edge on one pin with the other legs equal. Every theorem here that
  mentions `lutK`/`o5K`/`o6K` is a statement under this hypothesis; the
  binary lemmas (`lutB`) need nothing.
* **H_TERNARY_SIM** (only for the scenario section, stated in prose, NOT used
  as a Lean hypothesis because the scenarios are concrete computations): that
  Eichelberger's two-phase ternary simulation (phase A: changing inputs set
  to `x`, iterate to a fixed point; phase B: final values, iterate) with
  unit-delay Jacobi iteration over-approximates every bounded-delay binary
  behaviour of the network (Brzozowski–Seger). Not proved here. Test: GLS of
  the same scenarios with swept route delays; every definite ternary value
  must be the value every GLS run settles to.
* **H_A0_FORK** (only `sc_a0_fall_ordered` / `sc_a0_fall_runt`, encoded in
  the input sequence, which gives the two A0 branches separate pins): A0's
  falling edge reaches the ack C-elements `ua1`/`ua2` before it reaches the
  state node's I4. Physical fact: routed delay of A0 to ua2 < routed delay of
  A0 to ustate + q feedback + ugrant + g2 wire. Test: read the four arcs from
  the routed SDF; or GLS with the A0->ua2 branch delayed by a sweep;
  `sc_a0_fall_skewed` shows what happens without it.

Pin maps (from the RTL):
* `bd_arbiter.ustate` LUT6_2 INIT 64'hFFF0_FFB2_ACAC_ACAC,
  I0=r1 I1=r2 I2=q I3=rst I4=A0 I5=1, O6=q (fed back to I2), O5=R0.
* `ugrant` LUT6_2 INIT 64'h0C0C_0C0C_A0A0_A0A0,
  I0=r1 I1=r2 I2=q I3=0 I4=0 I5=1, O5=g1, O6=g2.
* `bd_arbcell.ustate` = `bd_c2n_set`, LUT6 INIT 64'hFFB2_FFB2_FFB2_FFB2,
  I0=r1 I1=r2 I2=q I3=rst I4=0 I5=0.
* `bd_c2` LUT6 INIT 64'h00E8_00E8_00E8_00E8, I0=a I1=b I2=q I3=rst I4=0 I5=0.
-/

namespace Formal.Cells.ArbKleene
open Formal.Cells
open Formal.Core.LutList.K3

/-! ## INITs and cells -/

def ST_INIT : Nat := 0xFFF0FFB2ACACACAC
def GR_INIT : Nat := 0x0C0C0C0CA0A0A0A0
def CS_INIT : Nat := 0xFFB2FFB2FFB2FFB2
def C2_INIT : Nat := 0x00E800E800E800E8

/-- `g1` = O5 of `ugrant`. -/
def g1K (r1 r2 q : K3) : K3 := o5K GR_INIT [r1, r2, q, f, f, t]
/-- `g2` = O6 of `ugrant`. -/
def g2K (r1 r2 q : K3) : K3 := o6K GR_INIT [r1, r2, q, f, f, t]
/-- Next value of the held state node of `bd_arbiter` (O6 of `ustate`). -/
def qArbK (r1 r2 q rst a0 : K3) : K3 := o6K ST_INIT [r1, r2, q, rst, a0, t]
/-- `R0` of `bd_arbiter` (O5 of `ustate`). -/
def r0K (r1 r2 q rst a0 : K3) : K3 := o5K ST_INIT [r1, r2, q, rst, a0, t]
/-- Next value of the state node of `bd_arbcell` (`bd_c2n_set`). -/
def qCellK (r1 r2 q rst : K3) : K3 := lutK CS_INIT [r1, r2, q, rst, f, f]
/-- Next value of a `bd_c2` C-element. -/
def cK (a b q rst : K3) : K3 := lutK C2_INIT [a, b, q, rst, f, f]

/-- Kleene AND / OR (strong Kleene), for stating equation lemmas. -/
def kand : K3 → K3 → K3
  | f, _ => f
  | _, f => f
  | t, t => t
  | _, _ => x
def kor : K3 → K3 → K3
  | t, _ => t
  | _, t => t
  | f, f => f
  | _, _ => x

/-! ## Binary sanity: the INITs are the equations the header states -/

theorem g1_bin (r1 r2 q : Bool) :
    o5B GR_INIT [r1, r2, q, false, false, true] = (r1 && q) := by
  cases r1 <;> cases r2 <;> cases q <;> decide
theorem g2_bin (r1 r2 q : Bool) :
    o6B GR_INIT [r1, r2, q, false, false, true] = (r2 && !q) := by
  cases r1 <;> cases r2 <;> cases q <;> decide
theorem r0_bin (r1 r2 q rst a0 : Bool) :
    o5B ST_INIT [r1, r2, q, rst, a0, true] = ((r1 && q) || (r2 && !q)) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rst <;> cases a0 <;> decide
/-- Held state node: `rst` forces 1; `A0` high holds; else `C(r1, ~r2)`. -/
theorem qArb_bin (r1 r2 q rst a0 : Bool) :
    o6B ST_INIT [r1, r2, q, rst, a0, true] =
      (rst || (if a0 then q else ((r1 && !r2) || (q && (r1 || !r2))))) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rst <;> cases a0 <;> decide
theorem c2_bin (a b q rst : Bool) :
    lutB C2_INIT [a, b, q, rst, false, false] =
      (!rst && ((a && b) || (q && (a || b)))) := by
  cases a <;> cases b <;> cases q <;> cases rst <;> decide

/-! ## Kleene equation lemmas: the grant LUT is exactly Kleene AND -/

theorem g1K_eq (r1 r2 q : K3) : g1K r1 r2 q = kand r1 q := by
  cases r1 <;> cases r2 <;> cases q <;> decide
theorem g2K_eq (r1 r2 q : K3) : g2K r1 r2 q = kand r2 (K3.not q) := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-! ## (1) An `x` on `q` reaches a grant exactly when that grant's request is not 0 -/

theorem g1_qx (r1 r2 : K3) : g1K r1 r2 x = (if r1 = f then f else x) := by
  cases r1 <;> cases r2 <;> decide
theorem g2_qx (r1 r2 : K3) : g2K r1 r2 x = (if r2 = f then f else x) := by
  cases r1 <;> cases r2 <;> decide

/-- Both grants are `x` exactly when `q = x` and neither request is a definite 0. -/
theorem both_grants_x_iff (r1 r2 q : K3) :
    (g1K r1 r2 q = x ∧ g2K r1 r2 q = x) ↔ (q = x ∧ r1 ≠ f ∧ r2 ≠ f) := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-! ## (2) Kleene exclusion -/

/-- Never both grants definite 1, for ANY ternary inputs. -/
theorem kleene_exclusion (r1 r2 q : K3) : ¬ (g1K r1 r2 q = t ∧ g2K r1 r2 q = t) := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-- Stronger: a definite grant forces the other grant to a definite 0. -/
theorem g1_t_forces (r1 r2 q : K3) (h : g1K r1 r2 q = t) : g2K r1 r2 q = f := by
  revert h; cases r1 <;> cases r2 <;> cases q <;> decide
theorem g2_t_forces (r1 r2 q : K3) (h : g2K r1 r2 q = t) : g1K r1 r2 q = f := by
  revert h; cases r1 <;> cases r2 <;> cases q <;> decide

/-- The complete set of grant pairs reachable from any ternary input. In
particular `(t,x)`, `(x,t)` and `(t,t)` never occur. -/
theorem grant_pairs (r1 r2 q : K3) :
    (g1K r1 r2 q, g2K r1 r2 q) ∈
      [(f, f), (t, f), (f, t), (x, f), (f, x), (x, x)] := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-! ## (3) Downstream: R0 and the ack C-elements -/

/-- With `q = x` (and `rst = 0`), `R0` is definite exactly when the two
requests agree: `R0 = r1.q + r2.~q` is one LUT, so it computes the closure of
the whole sum and the `q` cancels. -/
theorem r0_qx (r1 r2 a0 : K3) :
    r0K r1 r2 x f a0 =
      (if r1 = f ∧ r2 = f then f else if r1 = t ∧ r2 = t then t else x) := by
  cases r1 <;> cases r2 <;> cases a0 <;> decide

/-- `R0` is never less definite than the Kleene OR of the two grants, and it
is strictly more definite in exactly one input class: `r1 = r2 = 1`, `q = x`,
where both grants are `x` but `R0` is a definite 1. -/
theorem r0_vs_or (r1 r2 q a0 : K3) :
    r0K r1 r2 q f a0 = kor (g1K r1 r2 q) (g2K r1 r2 q) ∨
      (r1 = t ∧ r2 = t ∧ q = x ∧ r0K r1 r2 q f a0 = t ∧
        kor (g1K r1 r2 q) (g2K r1 r2 q) = x) := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> decide

/-- A C-element with an `x` on one input: it stays definite iff its held
value already equals its other (definite) input; otherwise it goes `x`. -/
theorem c_x_left (b q : K3) : cK x b q f = (if q = b ∧ b ≠ x then q else x) := by
  cases b <;> cases q <;> decide
theorem c_x_right (a q : K3) : cK a x q f = (if q = a ∧ a ≠ x then q else x) := by
  cases a <;> cases q <;> decide

/-- `x` is absorbing in the C-element loop: from `q = x` the next value is
definite only when both inputs are definite and equal. -/
theorem c_restore_iff (a b : K3) : cK a b x f ≠ x ↔ (a = b ∧ a ≠ x) := by
  cases a <;> cases b <;> decide

/-- Kleene fixed points of the C-element loop (`rst = 0`), listed per input
pair. `fixC a b` is the list of `q` with `cK a b q f = q`. -/
def fixC (a b : K3) : List K3 := [f, t, x].filter (fun q => cK a b q f = q)

theorem c_fixpoints :
    fixC f f = [f] ∧ fixC t t = [t] ∧ fixC x x = [x] ∧
    fixC f t = [f, t, x] ∧ fixC t f = [f, t, x] ∧
    fixC x f = [f, x] ∧ fixC f x = [f, x] ∧
    fixC x t = [t, x] ∧ fixC t x = [t, x] := by decide

/-- `rst = 1` forces the C-element to 0 whatever else is `x`. -/
theorem c_rst (a b q : K3) : cK a b q t = f := by
  cases a <;> cases b <;> cases q <;> decide

/-- The ack `A1 = C(g1, A0)` composed through the grant LUT computes the
closure of the composite Boolean function (no Kleene pessimism from the
composition: `g1` is read once). Function form, `rst = 0`. -/
def cloK (fn : List Bool → Bool) (ins : List K3) : K3 :=
  let vs := (completions ins).map fn
  if vs.all id then .t else if vs.all (!·) then .f else .x

theorem a1_is_closure (r1 r2 q a0 a1 : K3) :
    cK (g1K r1 r2 q) a0 a1 f =
      cloK (fun v => match v with
        | [b1, _, bq, ba0, ba1] => lutB C2_INIT [b1 && bq, ba0, ba1, false, false, false]
        | _ => false) [r1, r2, q, a0, a1] := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> cases a1 <;> decide

/-! ## (4) When the state node's own loop restores a definite `q` from `q = x` -/

/-- `bd_arbiter`: from `q = x`, the next state is definite iff `rst = 1`;
or `A0 = 0` and the set condition r1.~r2 is definite (then q = 1 whatever
`rst` is, since `rst` also pushes to 1); or `rst = 0`, `A0 = 0` and the reset
condition ~r1.r2 is definite (then q = 0). -/
theorem arb_restore_iff (r1 r2 rst a0 : K3) :
    qArbK r1 r2 x rst a0 ≠ x ↔
      (rst = t ∨ (a0 = f ∧ r1 = t ∧ r2 = f) ∨
        (rst = f ∧ a0 = f ∧ r1 = f ∧ r2 = t)) := by
  cases r1 <;> cases r2 <;> cases rst <;> cases a0 <;> decide

theorem arb_restore_values :
    qArbK t f x f f = t ∧ qArbK f t x f f = f ∧
    (∀ r1 r2 a0 : K3, qArbK r1 r2 x t a0 = t) := by
  refine ⟨by decide, by decide, ?_⟩
  intro r1 r2 a0; cases r1 <;> cases r2 <;> cases a0 <;> decide

/-- `bd_arbcell` (no hold): from `q = x`, definite iff `rst = 1`, or the
set condition is definite, or `rst = 0` and the reset condition is. -/
theorem cell_restore_iff (r1 r2 rst : K3) :
    qCellK r1 r2 x rst ≠ x ↔
      (rst = t ∨ (r1 = t ∧ r2 = f) ∨ (rst = f ∧ r1 = f ∧ r2 = t)) := by
  cases r1 <;> cases r2 <;> cases rst <;> decide

/-- `x` is a fixed point of the state loop on every hold input (tie, or
`A0 = 1`): nothing in the Kleene model ever resolves it. This is the logical
shadow of metastability: the ternary model says "unbounded", the analog
model (probe 7c/7d) gives the e^(-t/τ) rate. -/
theorem arb_x_held (r1 r2 : K3) (a0 : K3) (h : a0 = t ∨ (r1 = r2)) :
    qArbK r1 r2 x f a0 = x := by
  revert h; cases r1 <;> cases r2 <;> cases a0 <;> decide

/-- An `x` on `A0` can corrupt a definite `q` (and only `A0`, `r1`, `r2`
can: `rst = 0`): whenever the unheld node would move. -/
theorem a0_x_corrupts :
    qArbK t f f f x = x ∧ qArbK f t t f x = x ∧
    qArbK t f t f x = t ∧ qArbK f t f f x = f ∧ qArbK t t f f x = f := by decide

/-- With `A0 = 1` the held node ignores any `x` on the requests. -/
theorem hold_shields (r1 r2 q : K3) (hq : q ≠ x) : qArbK r1 r2 q f t = q := by
  revert hq; cases r1 <;> cases r2 <;> cases q <;> decide

set_option maxRecDepth 20000

/-! ## (5) Ternary simulation of `bd_arbiter` (Eichelberger A/B, unit delay)

The network state is every LUT output; one `step` re-evaluates every LUT from
the previous outputs (Jacobi, unit delay on every LUT, feedback wires
included). `settle` runs a fixed number of steps; each scenario theorem also
proves that the end state is a fixed point, so the number of steps is not a
fudge. Phase A sets every changing input to `x` (the window in which the edge
is in flight, in any order and with any skew); phase B gives the final
values. -/

structure Net where
  q : K3
  g1 : K3
  g2 : K3
  r0 : K3
  a1 : K3
  a2 : K3
  deriving DecidableEq, Repr

/-- Inputs. `a0` is A0 as the state node's pin I4 sees it, `a0c` is A0 as
the two ack C-elements see it: two branches of one routed fork, which may
arrive at different times. -/
structure Inp where
  r1 : K3
  r2 : K3
  a0 : K3
  a0c : K3
  rst : K3
  deriving DecidableEq, Repr

/-- An input vector with both A0 branches equal (no claim about fork skew:
phase A puts `x` on both, which already covers every skew). -/
def I (r1 r2 a0 rst : K3) : Inp := ⟨r1, r2, a0, a0, rst⟩

def step (i : Inp) (s : Net) : Net where
  q := qArbK i.r1 i.r2 s.q i.rst i.a0
  r0 := r0K i.r1 i.r2 s.q i.rst i.a0
  g1 := g1K i.r1 i.r2 s.q
  g2 := g2K i.r1 i.r2 s.q
  a1 := cK s.g1 i.a0c s.a1 i.rst
  a2 := cK s.g2 i.a0c s.a2 i.rst

def settle : Nat → Inp → Net → Net
  | 0, _, s => s
  | n + 1, i, s => settle n i (step i s)

/-- Run a list of input vectors, settling `k` steps after each. -/
def run (k : Nat) : List Inp → Net → Net
  | [], s => s
  | i :: is, s => run k is (settle k i s)

/-- Idle, client 1 was the last winner: q = 1, r1 = r2 = 0, A0 = 0. -/
def idle1 : Net := ⟨t, f, f, f, f, f⟩
/-- Client 1 holding a request, server not yet acking. -/
def own1 : Net := ⟨t, t, f, t, f, f⟩
/-- Client 1 being served: A0 = 1, A1 = 1. -/
def served1 : Net := ⟨t, t, f, t, t, f⟩
/-- Client 1 has dropped r1, R0 = 0, server still has A0 = 1, A1 = 1. -/
def done1 : Net := ⟨t, f, f, f, t, f⟩

/-- Reset dominates: all-`x` power-up with `rst = 1` and definite low inputs
gives a definite state (q = 1, everything else 0). -/
theorem sc_reset :
    settle 4 (I f f f t) ⟨x, x, x, x, x, x⟩ = idle1 ∧
    step (I f f f t) idle1 = idle1 := by decide

/-- THE RUNT ASKED FOR: r1 falling while r2 rises, server idle (`A0 = 0`),
both requests `x` during the window.
Window: q, g1, g2, R0 all go `x` (both grants `x` at once); A1, A2 stay 0
because A0 = 0 holds them (C-element whose held value equals its other input).
After: the reset condition r2.~r1 is definite, so the state loop is forced
and EVERYTHING returns definite: q = 0, g2 = 1. In the Kleene model this
direction is self-healing. -/
theorem sc_runt_opposite :
    settle 3 (I x x f f) own1 = ⟨x, x, x, x, f, f⟩ ∧
    step (I x x f f) ⟨x, x, x, x, f, f⟩ = ⟨x, x, x, x, f, f⟩ ∧
    settle 3 (I f t f f) ⟨x, x, x, x, f, f⟩ = ⟨f, f, t, t, f, f⟩ ∧
    step (I f t f f) ⟨f, f, t, t, f, f⟩ = ⟨f, f, t, t, f, f⟩ := by decide

/-- Same window while the server acknowledges client 1 (`A0 = 1`, A1 = 1):
the hold shields q, so only g1 (and R0) follow r1 into `x`; g2 stays a
definite 0 and A1 = C(x, 1) with A1 = 1 stays 1. -/
theorem sc_runt_held :
    settle 3 (I x x t f) served1 = ⟨t, x, f, x, t, f⟩ ∧
    step (I x x t f) ⟨t, x, f, x, t, f⟩ = ⟨t, x, f, x, t, f⟩ := by decide

/-- Near-tie from idle, both requests RISING within one window: ends on a
tie (hold) with q = x, which nothing in the model resolves. Both grants `x`
forever, R0 a DEFINITE 1 (closure of r1.q + r2.~q), so the server is asked;
A1/A2 stay 0 while A0 = 0. -/
theorem sc_tie_rising :
    settle 3 (I x x f f) idle1 = ⟨x, x, x, x, f, f⟩ ∧
    settle 3 (I t t f f) ⟨x, x, x, x, f, f⟩ = ⟨x, x, x, t, f, f⟩ ∧
    step (I t t f f) ⟨x, x, x, t, f, f⟩ = ⟨x, x, x, t, f, f⟩ := by decide

/-- ...then the server answers R0 = 1 with A0 = 1: the hold freezes q = x
and both ack C-elements latch the `x`: A1 = A2 = x, a fixed point. In the
ternary model the `x` reaches both clients' acknowledges as soon as the
(definite) server acks. -/
theorem sc_tie_acked :
    run 3 [I x x f f, I t t f f, I t t x f, I t t t f] idle1 = ⟨x, x, x, t, x, x⟩ ∧
    step (I t t t f) ⟨x, x, x, t, x, x⟩ = ⟨x, x, x, t, x, x⟩ := by decide

/-- A0-fall with client 2 waiting and client 1 NOT re-requesting, but with
the A0 fork's skew unconstrained (both branches `x` together): q is restored
(definite reset r2.~r1 once A0 = 0) but A2 = C(g2, A0) ends `x`. This is a
genuine binary hazard, not Kleene pessimism: if the A0 branch to `ua2` lags
the path A0 -> ustate -> q -> ugrant -> g2, A2 sees g2 = 1 while its A0 is
still 1 and fires for a transaction the server never began (the header's
early-ack defect, reopened by fork skew). See `sc_a0_fall_ordered`. -/
theorem sc_a0_fall_skewed :
    run 3 [I f t x f, I f t f f] done1 = ⟨f, f, t, t, f, x⟩ ∧
    step (I f t f f) ⟨f, f, t, t, f, x⟩ = ⟨f, f, t, t, f, x⟩ := by decide

/-- The same A0-fall under the ordering hypothesis H_A0_FORK (A0's fall
reaches both ack C-elements before it reaches the state node's I4, i.e.
before g2 can rise): fully definite, A2 stays 0 until the server acks. -/
theorem sc_a0_fall_ordered :
    run 3 [⟨f, t, t, x, f⟩, ⟨f, t, t, f, f⟩, ⟨f, t, x, f, f⟩, ⟨f, t, f, f, f⟩] done1
      = ⟨f, f, t, t, f, f⟩ ∧
    step ⟨f, t, f, f, f⟩ ⟨f, f, t, t, f, f⟩ = ⟨f, f, t, t, f, f⟩ := by decide

/-- The header's "aperture" case, with the fork ordered as above: client 1
re-requests (legally, after A1 fell) on the edge where the state node sees
A0 fall. q goes `x` and the inputs end on a tie with A0 = 0, so q stays `x`;
grants both `x`, R0 a definite 1; A1, A2 stay 0 until the server acks, and
then both latch `x` (as in `sc_tie_acked`). -/
theorem sc_a0_fall_runt :
    run 3 [⟨f, t, t, x, f⟩, ⟨f, t, t, f, f⟩, ⟨x, t, x, f, f⟩, ⟨t, t, f, f, f⟩] done1
      = ⟨x, x, x, t, f, f⟩ ∧
    step ⟨t, t, f, f, f⟩ ⟨x, x, x, t, f, f⟩ = ⟨x, x, x, t, f, f⟩ ∧
    run 3 [I t t x f, I t t t f] ⟨x, x, x, t, f, f⟩ = ⟨x, x, x, t, x, x⟩ := by decide

end Formal.Cells.ArbKleene
