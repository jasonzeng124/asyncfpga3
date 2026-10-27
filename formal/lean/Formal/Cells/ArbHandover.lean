import Formal.Cells.Prelim

/-!
# Probe 7e: the handover-ordering claim and the A0 hold (`cells/rtl/bd_arb.v`)

Two models, both evaluated on the REAL INIT constants and pin maps of the RTL
with `lutB`/`o5B`/`o6B` (no hand-written gate equations; where an equation is
used it is proved equal to the INIT first).

## Part 1: timed, the bare `bd_arbcell`, one handover

Discrete time `ℤ` (1 unit = 1 ps). Each LUT output is the **rise-fast
asymmetric pure-delay channel** `LutOut3`: for pins `a b c` with per-pin
rise arcs `dr` and fall arcs `df` (`dr ≤ df` on every pin),

    o t = f (a (t-dr_a)) (b (t-dr_b)) (c (t-dr_c))  ||  f (a (t-df_a)) (b (t-df_b)) (c (t-df_c)).

For an isolated edge on one pin this puts the output's rising edge exactly
`dr` after the input edge and its falling edge exactly `df` after; that is the
iverilog `specify` behaviour of `cells/sim/bd_prims_sim.v` for isolated edges.
It is pulse-STRETCHING for high pulses by `df - dr` (transport, no inertial
rejection). ARBITER.md's "+68 ps stretch each O6 LUT adds to a positive pulse"
is this with 68 = 124 − 56, which is prjxray's SLOW_MAX − FAST_MAX of ONE O6
arc (makesdf.py:63), a corner mix, not a measured rise/fall asymmetry; at one
consistent corner `df = dr` and the stretch is 0 (consistent-corner values:
`ArbCorners`; see the audit correction below). In the handover scenarios below every LUT sees at most one edge
per pin that changes its function, so the choice of multi-edge semantics does
not enter.

Named hypotheses (structure `Arcs`, fields `H_...`), each a measurable arc:
* `qr`, `qf`   : state LUT (`bd_c2n_set`, a LUT6 on O6) rise/fall arc, any pin
                 (the 56/124 once quoted here is prjxray FAST_MAX/SLOW_MAX of
                 one O6 arc, not rise/fall; see the audit correction below).
* `w`          : routing delay of the q net from the state LUT output to the
                 grant LUT's I2 pin ("feedback routing", 0 in the arc-only sim).
* `wfb`        : routing delay of q back to the state LUT's own I2 (enters
                 only through `H_init`, not the result).
* `g1r_q`, `g1f_q`, `g1r_r1`, `g1f_r1` : grant LUT O5 arcs from pins I2 (q)
                 and I0 (r1) (per-pin pairs I2 52/150, I0 55/152: again
                 FAST_MAX/SLOW_MAX, not rise/fall).
* `g2r`, `g2f` : grant LUT O6 arcs, any pin (56/124, FAST_MAX/SLOW_MAX).
* `H_REQ_ISO`  : requests reach both LUTs at the same instant (encoded by
                 giving both LUTs the same `r1`/`r2` traces). Test: read the
                 two `r2` routes in the SDF; a skew `s` shifts the formula by
                 `s` (not proved here).

**Audit correction (claude/audit REPORT rows 10, 24; findings B #10).** The
pairs 56/124 (O6), 52/150 (O5 I2) and 55/152 (O5 I0/I1) of
`cells/sim/bd_prims_sim.v` are prjxray's FAST_MAX and SLOW_MAX of ONE arc
(`prjxray/utils/makesdf.py:63` writes `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`,
each for both edges), not rise and fall. prjxray has no edge split. The general
theorems of Part 1 (any `Arcs`, rise = fall included) stand, but every numeric
instance below (`prjArcs`, `simArcs`: the 16 ps header overlap, the 28 + w
reverse margin, the 72/94 ps skew caps, ARBITER.md's "+68 ps" = 124 − 56) mixes
corners (`ArbCorners.prjArcs_is_mix`, `ArbCorners.simArcs_is_mix`). Corrected:
`ArbCorners.overlap_C`/`corner_no_overlap` (overlap `max 0 (d6 − o5q − w)` = 0 at
every consistent corner, every w ≥ 0), `ArbCorners.header_needs_asym`,
`ArbCorners.sim_overlap_C`, `ArbCorners.r1_to_r2_margins` (96 + w SLOW_MAX,
46 + w FAST_MIN), `ArbCorners.caps_are` (caps 0/26 ps SLOW_MAX, 3/0 ps
FAST_MIN), `ArbCorners.box_overlap_le`/`box_caps` (box: 37 − w, caps 82/105).
Rise/fall asymmetry is the unmeasured `ArbCorners.RF` (H_RF_ASYM).

## Part 2: untimed, `bd_arbiter`, every interleaving

Speed-independent (unbounded gate delay, zero wire delay) interleaving model
of `bd_arbiter` with a four-phase server and two four-phase, always-hungry
clients. Exhaustive reachability, discharged as an inductive invariant (a
literal bitmask) checked by the kernel (`decide +kernel`).
The hidden timing assumptions are listed in `formal/notes/B-arb-handover.md`.
-/

namespace Formal.Cells.ArbHandover
open Formal.Cells

/-! ## INIT constants (copied from `cells/rtl/bd_arb.v`, `cells/rtl/bd_ce.v`) -/

/-- `bd_c2n_set` (bd_arbcell's state node): LUT6, I0=r1 I1=r2 I2=q I3=rst I4=0 I5=0. -/
def INIT_C2N_SET : Nat := 0xFFB2FFB2FFB2FFB2
/-- `ugrant`: LUT6_2, I0=r1 I1=r2 I2=q I3=0 I4=0 I5=1, O5=g1, O6=g2. -/
def INIT_GRANTS : Nat := 0x0C0C0C0CA0A0A0A0
/-- `bd_arbiter.ustate` as shipped (held): I0=r1 I1=r2 I2=q I3=rst I4=A0 I5=1, O6=q, O5=R0. -/
def INIT_HELD : Nat := 0xFFF0FFB2ACACACAC
/-- The unheld state node: `ARB_STATE_R0` of `cells/verify/inits.py`
(O6 = rst + C(r1,~r2), O5 = r1.q + r2.~q, I4 ignored). Derived there from the
spec; here only its content is used (see `unheld_q_eqn`). -/
def INIT_UNHELD : Nat := 0xFFB2FFB2ACACACAC
/-- `bd_c2`: LUT6, I0=a I1=b I2=q I3=rst I4=0 I5=0. -/
def INIT_C2_RST : Nat := 0x00E800E800E800E8

/-! ### The INITs equal the header's equations (all 2^n rows) -/

/-- The cell's state node with rst low. -/
def stateF (r1 r2 q : Bool) : Bool := lutB INIT_C2N_SET [r1, r2, q, false, false, false]
/-- g1 = O5 of `ugrant`. -/
def g1F (r1 r2 q : Bool) : Bool := o5B INIT_GRANTS [r1, r2, q, false, false]
/-- g2 = O6 of `ugrant`. -/
def g2F (r1 r2 q : Bool) : Bool := o6B INIT_GRANTS [r1, r2, q, false, false, true]

theorem stateF_eqn (r1 r2 q : Bool) :
    stateF r1 r2 q = ((r1 && !r2) || (r1 && q) || (!r2 && q)) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

theorem g1F_eqn (r1 r2 q : Bool) : g1F r1 r2 q = (r1 && q) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

theorem g2F_eqn (r1 r2 q : Bool) : g2F r1 r2 q = (r2 && !q) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- Held node, O6: q = rst + (A0 ? q : C(r1,~r2)). -/
theorem held_q_eqn (r1 r2 q rst a0 : Bool) :
    o6B INIT_HELD [r1, r2, q, rst, a0, true]
      = (rst || (if a0 then q else ((r1 && !r2) || (r1 && q) || (!r2 && q)))) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rst <;> cases a0 <;> rfl

/-- Unheld node, O6: q = rst + C(r1,~r2), A0 ignored. -/
theorem unheld_q_eqn (r1 r2 q rst a0 : Bool) :
    o6B INIT_UNHELD [r1, r2, q, rst, a0, true]
      = (rst || ((r1 && !r2) || (r1 && q) || (!r2 && q))) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rst <;> cases a0 <;> rfl

/-- Both nodes, O5: R0 = r1.q + r2.~q, independent of rst and A0. -/
theorem r0_eqn (init : Nat) (h : init = INIT_HELD ∨ init = INIT_UNHELD)
    (r1 r2 q rst a0 : Bool) :
    o5B init [r1, r2, q, rst, a0] = ((r1 && q) || (r2 && !q)) := by
  rcases h with h | h <;> subst h <;>
    cases r1 <;> cases r2 <;> cases q <;> cases rst <;> cases a0 <;> rfl

/-- The ack C-element with rst low. -/
theorem c2_eqn (a b q : Bool) :
    lutB INIT_C2_RST [a, b, q, false, false, false] = ((a && b) || (a && q) || (b && q)) := by
  cases a <;> cases b <;> cases q <;> rfl

/-- Reset: rst high drives the held q to 1 and the ack C-elements to 0 whatever
the other pins carry (so the reset state of Part 2 is the one rst produces). -/
theorem reset_values (r1 r2 q a0 a b : Bool) :
    o6B INIT_HELD [r1, r2, q, true, a0, true] = true ∧
    lutB INIT_C2_RST [a, b, q, true, false, false] = false := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> cases a <;> cases b <;> decide

/-! ## Part 1: timed handover of the bare cell -/

/-- A signal: a Boolean trace over integer picoseconds. -/
abbrev Sig := Int → Bool

/-- Rise-fast asymmetric pure-delay LUT output over three live pins. -/
def LutOut3 (f : Bool → Bool → Bool → Bool) (a b c : Sig)
    (ra rb rc fa fb fc : Int) (o : Sig) : Prop :=
  ∀ t, o t = (f (a (t - ra)) (b (t - rb)) (c (t - rc)) || f (a (t - fa)) (b (t - fb)) (c (t - fc)))

/-- The arc parameters (all named; see the module doc for the physical meaning). -/
structure Arcs where
  /-- state LUT O6 rise / fall arc (pin-independent). -/
  qr : Int
  qf : Int
  /-- routing of q to the grant LUT's I2 (the "feedback routing" of the header). -/
  w : Int
  /-- routing of q back to the state LUT's own I2. -/
  wfb : Int
  /-- grant LUT O5 (g1) arcs, from pin I2 (q) and pin I0 (r1). -/
  g1r_q : Int
  g1f_q : Int
  g1r_r1 : Int
  g1f_r1 : Int
  /-- grant LUT O6 (g2) arcs (pin-independent). -/
  g2r : Int
  g2f : Int
  /-- H_ARC_NONNEG: causality, every arc and wire is non-negative. -/
  H_nonneg : 0 ≤ qr ∧ 0 ≤ w ∧ 0 ≤ wfb ∧ 0 ≤ g1r_q ∧ 0 ≤ g1r_r1 ∧ 0 ≤ g2r
  /-- H_RISE_LE_FALL: each output rises no slower than it falls, per pin. This
  is what makes `LutOut3` the rise-fast channel. (The pairs 56/124, 52/150,
  55/152 once quoted here as prjxray rise/fall are FAST_MAX/SLOW_MAX of one arc,
  makesdf.py:63; the consistent instance is rise = fall, `ArbCorners.RF.sym`.) -/
  H_rise_le_fall : qr ≤ qf ∧ g1r_q ≤ g1f_q ∧ g1r_r1 ≤ g1f_r1 ∧ g2r ≤ g2f

/-- The bare cell under the arcs: q from the state LUT reading the routed-back
q (`wfb`), the grants from `ugrant` reading q after routing `w`. rst is low. -/
structure Cell (A : Arcs) (r1 r2 q g1 g2 : Sig) : Prop where
  H_state : LutOut3 stateF r1 r2 (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q
  H_g1 : LutOut3 g1F r1 r2 (fun s => q (s - A.w)) A.g1r_r1 A.g1r_r1 A.g1r_q A.g1f_r1 A.g1f_r1 A.g1f_q g1
  H_g2 : LutOut3 g2F r1 r2 (fun s => q (s - A.w)) A.g2r A.g2r A.g2r A.g2f A.g2f A.g2f g2

/-! ### r2 → r1 handover: r1 waiting, r2 (the holder) drops at `t0`. -/

/-- In the r2-to-r1 handover, q rises exactly `qr` after r2 falls. -/
theorem q_rises (A : Arcs) (t0 : Int) (r1 r2 q : Sig)
    (Hs : LutOut3 stateF r1 r2 (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, q t = decide (t0 + A.qr ≤ t) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  intro t
  rw [Hs t, H_r1, H_r1, H_r2, H_r2]
  simp only [stateF_eqn]
  by_cases ht : t0 + A.qr ≤ t
  · have : ¬ (t - A.qr < t0) := by omega
    simp [this, ht]
  · have e1 : t - A.qr < t0 := by omega
    have e2 : t - A.qf < t0 := by omega
    rw [H_init (t - A.qr - A.wfb) (by omega), H_init (t - A.qf - A.wfb) (by omega)]
    simp [e1, e2, ht]

/-- g1 rises exactly `qr + w + g1r_q` after r2 falls. -/
theorem g1_rises (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig) (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, g1 t = decide (t0 + (A.qr + A.w + A.g1r_q) ≤ t) := by
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hq := q_rises A t0 r1 r2 q C.H_state H_r1 H_r2 H_init
  intro t
  rw [C.H_g1 t]
  simp only [H_r1, hq, g1F_eqn, Bool.true_and]
  by_cases ht : t0 + (A.qr + A.w + A.g1r_q) ≤ t
  · have : t0 + A.qr ≤ t - A.g1r_q - A.w := by omega
    simp [this, ht]
  · have e1 : ¬ (t0 + A.qr ≤ t - A.g1r_q - A.w) := by omega
    have e2 : ¬ (t0 + A.qr ≤ t - A.g1f_q - A.w) := by omega
    simp [e1, e2, ht]

/-- g2 falls exactly `g2f` after r2 falls (through the r2 pin, not through q). -/
theorem g2_falls (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig) (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, g2 t = decide (t < t0 + A.g2f) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hq := q_rises A t0 r1 r2 q C.H_state H_r1 H_r2 H_init
  intro t
  rw [C.H_g2 t]
  simp only [H_r2, hq, g2F_eqn]
  by_cases ht : t < t0 + A.g2f
  · have e2 : t - A.g2f < t0 := by omega
    have e3 : ¬ (t0 + A.qr ≤ t - A.g2f - A.w) := by omega
    simp [e2, e3, ht]
  · have e1 : ¬ (t - A.g2r < t0) := by omega
    have e2 : ¬ (t - A.g2f < t0) := by omega
    simp [e1, e2, ht]

/-- **The handover-ordering claim, r2 → r1, exactly.** Both grants are high at
`t` iff `t0 + (qr + w + g1r_q) ≤ t < t0 + g2f`: the overlap is the interval
from the rising grant's two-arc path to the falling grant's one fall arc. -/
theorem overlap_r2_to_r1 (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, (g1 t && g2 t) = true ↔ (t0 + (A.qr + A.w + A.g1r_q) ≤ t ∧ t < t0 + A.g2f) := by
  intro t
  rw [g1_rises A t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init t,
      g2_falls A t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init t]
  simp

/-- Number of instants `a, a+1, …, a+n-1` at which `p` holds (the duration, in ps). -/
def countTrue (p : Int → Bool) (a : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => countTrue p a n + (if p (a + n) then 1 else 0)

theorem countTrue_interval (p : Int → Bool) (a lo hi : Int)
    (hp : ∀ t, p t = true ↔ (lo ≤ t ∧ t < hi)) (ha : a ≤ lo) :
    ∀ n : Nat, (countTrue p a n : Int) = max 0 (min hi (a + n) - lo) := by
  intro n
  induction n with
  | zero => simp [countTrue]; omega
  | succ n ih =>
    by_cases h : lo ≤ a + n ∧ a + n < hi
    · have : p (a + n) = true := (hp _).2 h
      simp only [countTrue, this, ↓reduceIte]
      omega
    · have : p (a + n) = false := by
        cases hq : p (a + n)
        · rfl
        · exact absurd ((hp _).1 hq) h
      simp only [countTrue, this, Bool.false_eq_true, ↓reduceIte]
      omega

/-- **Overlap duration, r2 → r1.** Counted from r2's fall over any window that
covers the falling grant, the number of picoseconds with both grants high is
`max 0 (g2f - (qr + w + g1r_q))`. -/
theorem overlap_duration_r2_to_r1 (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false)
    (n : Nat) (hn : A.g2f ≤ n) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int)
      = max 0 (A.g2f - (A.qr + A.w + A.g1r_q)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  have hov := overlap_r2_to_r1 A t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init
  rw [countTrue_interval _ t0 _ _ hov (by omega) n]
  omega

/-- **No overlap** iff the q routing covers the arc deficit. -/
theorem no_overlap_r2_to_r1 (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false)
    (H_route : A.g2f ≤ A.qr + A.w + A.g1r_q) :
    ∀ t, (g1 t && g2 t) = false := by
  intro t
  have h := overlap_r2_to_r1 A t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init t
  cases hc : (g1 t && g2 t)
  · rfl
  · exact absurd (h.1 hc) (by omega)

/-- The overlap EXISTS whenever the deficit is positive: at `t0 + qr + w + g1r_q`
both grants are high. -/
theorem overlap_exists_r2_to_r1 (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false)
    (H_deficit : A.qr + A.w + A.g1r_q < A.g2f) :
    g1 (t0 + (A.qr + A.w + A.g1r_q)) = true ∧ g2 (t0 + (A.qr + A.w + A.g1r_q)) = true := by
  have h := (overlap_r2_to_r1 A t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init
    (t0 + (A.qr + A.w + A.g1r_q))).2 ⟨Int.le_refl _, by omega⟩
  simpa using h

/-! ### r1 → r2 handover: r2 waiting, r1 (the holder) drops at `t0`. -/

theorem q_falls (A : Arcs) (t0 : Int) (r1 r2 q : Sig)
    (Hs : LutOut3 stateF r1 r2 (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q)
    (H_r2 : ∀ t, r2 t = true) (H_r1 : ∀ t, r1 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = true) :
    ∀ t, q t = decide (t < t0 + A.qf) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  intro t
  rw [Hs t, H_r2, H_r2, H_r1, H_r1]
  simp only [stateF_eqn]
  by_cases ht : t < t0 + A.qf
  · have e2 : t - A.qf < t0 := by omega
    rw [H_init (t - A.qf - A.wfb) (by omega)]
    simp [e2, ht]
  · have e1 : ¬ (t - A.qr < t0) := by omega
    have e2 : ¬ (t - A.qf < t0) := by omega
    simp [e1, e2, ht]

/-- **The other direction, r1 → r2, exactly.** g1 falls through its r1 pin
(O5 I0 fall arc) and g2 rises through q (state fall arc, routing, O6 rise arc).
Hypothesis `H_g1_by_r1`: the r1 path is the one that lowers g1 (its fall arc
is no later than q's fall reaching the pin), true for the prjxray numbers. -/
theorem overlap_r1_to_r2 (A : Arcs) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1 : ∀ t, r1 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = true)
    (H_g1_by_r1 : A.g1f_r1 ≤ A.qf + A.w + A.g1f_q) :
    ∀ t, (g1 t && g2 t) = true ↔ (t0 + (A.qf + A.w + A.g2r) ≤ t ∧ t < t0 + A.g1f_r1) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hq := q_falls A t0 r1 r2 q C.H_state H_r2 H_r1 H_init
  intro t
  have hg1 : g1 t = decide (t < t0 + A.g1f_r1) := by
    rw [C.H_g1 t]
    simp only [H_r1, hq, g1F_eqn]
    by_cases ht : t < t0 + A.g1f_r1
    · have e1 : t - A.g1f_r1 < t0 := by omega
      have e2 : t - A.g1f_q - A.w < t0 + A.qf := by omega
      simp [e1, e2, ht]
    · have e1 : ¬ (t - A.g1r_r1 < t0) := by omega
      have e2 : ¬ (t - A.g1f_r1 < t0) := by omega
      simp [e1, e2, ht]
  have hg2 : g2 t = decide (t0 + (A.qf + A.w + A.g2r) ≤ t) := by
    rw [C.H_g2 t]
    simp only [H_r2, hq, g2F_eqn, Bool.true_and]
    by_cases ht : t0 + (A.qf + A.w + A.g2r) ≤ t
    · have e1 : ¬ (t - A.g2r - A.w < t0 + A.qf) := by omega
      simp [e1, ht]
    · have e1 : t - A.g2r - A.w < t0 + A.qf := by omega
      have e2 : t - A.g2f - A.w < t0 + A.qf := by omega
      simp [e1, e2, ht]
  rw [hg1, hg2]
  simp
  omega

/-! ### The header's numbers

All numbers in this section use the arcs of `cells/sim/bd_prims_sim.v`, which
read prjxray's FAST_MAX/SLOW_MAX of one arc (makesdf.py:63) as rise/fall. They
are exact in that simulator's arc model only, and mix corners. Corrected values:
`ArbCorners` §1 (see the audit correction in the module header). -/

/-- Cell arcs of cells/sim/bd_prims_sim.v (corner-mixed: "rise" = FAST_MAX,
"fall" = SLOW_MAX; `ArbCorners.prjArcs_is_mix`), q routing `w`, every other
wire 0. -/
def prjArcs (w : Int) (hw : 0 ≤ w) : Arcs where
  qr := 56
  qf := 124
  w := w
  wfb := 0
  g1r_q := 52
  g1f_q := 150
  g1r_r1 := 55
  g1f_r1 := 152
  g2r := 56
  g2f := 124
  H_nonneg := by omega
  H_rise_le_fall := by omega

/-- **Header claim, zero routing:** r2 → r1 overlap is exactly 108..124 ps after
r2 falls, i.e. 16 ps, with the corner-mixed `prjArcs`. 16 = SLOW_MAX(124) −
FAST_MAX(56) − FAST_MAX(52). At one consistent corner the overlap is 0:
`ArbCorners.slow_header`, `ArbCorners.fast_header`, `ArbCorners.mix_header_16`. -/
theorem header_16ps (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (prjArcs 0 (by omega)) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    (∀ t, (g1 t && g2 t) = true ↔ (t0 + 108 ≤ t ∧ t < t0 + 124)) ∧
    countTrue (fun t => g1 t && g2 t) t0 124 = 16 := by
  refine ⟨fun t => ?_, ?_⟩
  · have := overlap_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init t
    simpa [prjArcs] using this
  · have := overlap_duration_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init 124
      (by simp [prjArcs])
    simp [prjArcs] at this
    omega

/-- **Header claim, routed:** with at least 16 ps of q routing, no overlap
(corner-mixed arcs; at a consistent corner every w ≥ 0 suffices:
`ArbCorners.corner_no_overlap`). -/
theorem header_routed (w : Int) (hw : 16 ≤ w) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (prjArcs w (by omega)) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, (g1 t && g2 t) = false :=
  no_overlap_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init (by simp [prjArcs]; omega)

/-- **Reverse direction with the header's numbers:** never an overlap, for any
q routing (margin 180 + w - 152 = 28 + w ps, corner-mixed; consistent-corner
margins 96 + w at SLOW_MAX, 46 + w at FAST_MIN: `ArbCorners.r1_to_r2_margins`). -/
theorem header_r1_to_r2 (w : Int) (hw : 0 ≤ w) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (prjArcs w hw) r1 r2 q g1 g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1 : ∀ t, r1 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = true) :
    ∀ t, (g1 t && g2 t) = false := by
  intro t
  have h := overlap_r1_to_r2 _ t0 r1 r2 q g1 g2 C H_r2 H_r1 H_init
    (by simp [prjArcs]; omega) t
  cases hc : (g1 t && g2 t)
  · rfl
  · have := h.1 hc; simp [prjArcs] at this; omega

/-- The simulator's `BD_ROUTE_PS = R` adds `R` to EVERY arc (bd_prims_sim.v),
not only to the q wire. Then the r2 → r1 overlap is `max 0 (16 - R)` ps. The 16
is the simulator's corner mix (`ArbCorners.simArcs_is_mix`); with consistent
arcs the overlap is 0 for every R (`ArbCorners.sim_overlap_C`). -/
def simArcs (R : Int) (hR : 0 ≤ R) : Arcs where
  qr := 56 + R
  qf := 124 + R
  w := 0
  wfb := 0
  g1r_q := 52 + R
  g1f_q := 150 + R
  g1r_r1 := 55 + R
  g1f_r1 := 152 + R
  g2r := 56 + R
  g2f := 124 + R
  H_nonneg := by omega
  H_rise_le_fall := by omega

theorem sim_overlap (R : Int) (hR : 0 ≤ R) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (simArcs R hR) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false)
    (n : Nat) (hn : 124 + R ≤ n) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) = max 0 (16 - R) := by
  have := overlap_duration_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init n
    (by simp [simArcs]; omega)
  simp [simArcs] at this
  rw [this]; omega

/-! ### Request-fork skew: the overlap is capped by the grant LUT's own arcs

Drop `H_REQ_ISO`: the dropping request reaches the state LUT at `t0` and the
grant LUT at `t0 + σ` (`σ` of either sign: a routing skew on the request fork).
Then the overlap is no longer a routing question in one direction only, but it
is CAPPED, for every skew and every q routing, by `g2f - g1r_q` (r2 → r1;
72 ps with the corner-mixed `prjArcs`) and `g1f_q - g2r` (r1 → r2; 94 ps).
At a consistent corner the caps are 0/26 ps (SLOW_MAX) and 3/0 ps (FAST_MIN):
`ArbCorners.corner_caps`, `ArbCorners.caps_are`; box 82/105: `ArbCorners.box_caps`. -/

theorem overlap_skew_r2_to_r1 (A : Arcs) (t0 σ : Int) (r1 r2s r2g q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1 r2s (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q)
    (H_g1 : LutOut3 g1F r1 r2g (fun s => q (s - A.w)) A.g1r_r1 A.g1r_r1 A.g1r_q
      A.g1f_r1 A.g1f_r1 A.g1f_q g1)
    (H_g2 : LutOut3 g2F r1 r2g (fun s => q (s - A.w)) A.g2r A.g2r A.g2r A.g2f A.g2f A.g2f g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2s : ∀ t, r2s t = decide (t < t0))
    (H_r2g : ∀ t, r2g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, (g1 t && g2 t) = true ↔
      (t0 + (A.qr + A.w + A.g1r_q) ≤ t ∧ t < t0 + min σ (A.qr + A.w) + A.g2f) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hq := q_rises A t0 r1 r2s q Hs H_r1 H_r2s H_init
  intro t
  rw [H_g1 t, H_g2 t]
  simp only [H_r1, H_r2g, hq, g1F_eqn, g2F_eqn, Bool.true_and]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  omega

theorem overlap_skew_r2_to_r1_le (A : Arcs) (t0 σ : Int) (r1 r2s r2g q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1 r2s (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q)
    (H_g1 : LutOut3 g1F r1 r2g (fun s => q (s - A.w)) A.g1r_r1 A.g1r_r1 A.g1r_q
      A.g1f_r1 A.g1f_r1 A.g1f_q g1)
    (H_g2 : LutOut3 g2F r1 r2g (fun s => q (s - A.w)) A.g2r A.g2r A.g2r A.g2f A.g2f A.g2f g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2s : ∀ t, r2s t = decide (t < t0))
    (H_r2g : ∀ t, r2g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = false) (n : Nat) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int)
      = max 0 (min (min σ (A.qr + A.w) + A.g2f) n - (A.qr + A.w + A.g1r_q)) ∧
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) ≤ max 0 (A.g2f - A.g1r_q) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hov := overlap_skew_r2_to_r1 A t0 σ r1 r2s r2g q g1 g2 Hs H_g1 H_g2 H_r1 H_r2s H_r2g H_init
  have := countTrue_interval _ t0 _ _ hov (by omega) n
  constructor <;> omega

theorem overlap_skew_r1_to_r2 (A : Arcs) (t0 σ : Int) (r1s r1g r2 q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1s r2 (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q)
    (H_g1 : LutOut3 g1F r1g r2 (fun s => q (s - A.w)) A.g1r_r1 A.g1r_r1 A.g1r_q
      A.g1f_r1 A.g1f_r1 A.g1f_q g1)
    (H_g2 : LutOut3 g2F r1g r2 (fun s => q (s - A.w)) A.g2r A.g2r A.g2r A.g2f A.g2f A.g2f g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1s : ∀ t, r1s t = decide (t < t0))
    (H_r1g : ∀ t, r1g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = true) :
    ∀ t, (g1 t && g2 t) = true ↔
      (t0 + (A.qf + A.w + A.g2r) ≤ t ∧ t < t0 + min (σ + A.g1f_r1) (A.qf + A.w + A.g1f_q)) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hq := q_falls A t0 r1s r2 q Hs H_r2 H_r1s H_init
  intro t
  rw [H_g1 t, H_g2 t]
  simp only [H_r2, H_r1g, hq, g1F_eqn, g2F_eqn, Bool.true_and]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  omega

theorem overlap_skew_r1_to_r2_le (A : Arcs) (t0 σ : Int) (r1s r1g r2 q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1s r2 (fun s => q (s - A.wfb)) A.qr A.qr A.qr A.qf A.qf A.qf q)
    (H_g1 : LutOut3 g1F r1g r2 (fun s => q (s - A.w)) A.g1r_r1 A.g1r_r1 A.g1r_q
      A.g1f_r1 A.g1f_r1 A.g1f_q g1)
    (H_g2 : LutOut3 g2F r1g r2 (fun s => q (s - A.w)) A.g2r A.g2r A.g2r A.g2f A.g2f A.g2f g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1s : ∀ t, r1s t = decide (t < t0))
    (H_r1g : ∀ t, r1g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = true) (n : Nat) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) ≤ max 0 (A.g1f_q - A.g2r) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := A.H_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := A.H_rise_le_fall
  have hov := overlap_skew_r1_to_r2 A t0 σ r1s r1g r2 q g1 g2 Hs H_g1 H_g2 H_r2 H_r1s H_r1g H_init
  have := countTrue_interval _ t0 _ _ hov (by omega) n
  omega

/-- With the corner-mixed `prjArcs` (FAST_MAX "rise", SLOW_MAX "fall",
makesdf.py:63): whatever the request-fork skew and q routing, an isolated
handover overlaps the grants for at most 72 ps (r2 → r1) or 94 ps (r1 → r2).
Consistent-corner caps: `ArbCorners.caps_are` (0/26 SLOW_MAX, 3/0 FAST_MIN). -/
theorem prj_overlap_caps (w : Int) (hw : 0 ≤ w) :
    (prjArcs w hw).g2f - (prjArcs w hw).g1r_q = 72 ∧
    (prjArcs w hw).g1f_q - (prjArcs w hw).g2r = 94 := by
  simp [prjArcs]

/-! ## Part 2: `bd_arbiter`, speed-independent interleaving model

State: the nine wires of `bd_arbiter` plus two monitor bits.
* `c` (credit): set when A0 rises (the server began a transaction), cleared
  when a client ack A1/A2 rises (that transaction was delivered).
* `z` (return-to-zero seen): set when R0 falls, cleared when a client ack rises.

Gates (each fires, atomically, only when excited = output differs from its
function of the CURRENT wire values; any excited gate may fire next):
* `q`  = O6 of `ustate` (INIT `st`, pins r1 r2 q rst=0 A0 1), `R0` = its O5;
* `g1`, `g2` = O5/O6 of `ugrant`;
* `A1` = `bd_c2`(g1, A0), `A2` = `bd_c2`(g2, A0);
* server: A0 follows R0 (four-phase: rises on R0 high, falls on R0 low);
* client i: r_i rises when A_i is low, falls when A_i is high (always hungry).
-/

structure St where
  r1 : Bool
  r2 : Bool
  a0 : Bool
  q : Bool
  r0 : Bool
  g1 : Bool
  g2 : Bool
  a1 : Bool
  a2 : Bool
  c : Bool
  z : Bool
deriving DecidableEq, Repr

inductive Gate
  | r1 | r2 | a0 | q | r0 | g1 | g2 | a1 | a2
deriving DecidableEq, Repr

def Gate.all : List Gate := [.r1, .r2, .a0, .q, .r0, .g1, .g2, .a1, .a2]

theorem Gate.mem_all (x : Gate) : x ∈ Gate.all := by cases x <;> simp [Gate.all]

def St.get (s : St) : Gate → Bool
  | .r1 => s.r1 | .r2 => s.r2 | .a0 => s.a0 | .q => s.q | .r0 => s.r0
  | .g1 => s.g1 | .g2 => s.g2 | .a1 => s.a1 | .a2 => s.a2

/-- What each gate (or environment process) is driving towards. -/
def target (st : Nat) (s : St) : Gate → Bool
  | .q  => o6B st [s.r1, s.r2, s.q, false, s.a0, true]
  | .r0 => o5B st [s.r1, s.r2, s.q, false, s.a0]
  | .g1 => o5B INIT_GRANTS [s.r1, s.r2, s.q, false, false]
  | .g2 => o6B INIT_GRANTS [s.r1, s.r2, s.q, false, false, true]
  | .a1 => lutB INIT_C2_RST [s.g1, s.a0, s.a1, false, false, false]
  | .a2 => lutB INIT_C2_RST [s.g2, s.a0, s.a2, false, false, false]
  | .a0 => s.r0
  | .r1 => !s.a1
  | .r2 => !s.a2

def enabled (st : Nat) (s : St) (x : Gate) : Bool := s.get x != target st s x

/-- Fire gate `x` (flip it) and update the monitors. -/
def fire (s : St) : Gate → St
  | .r1 => { s with r1 := !s.r1 }
  | .r2 => { s with r2 := !s.r2 }
  | .a0 => { s with a0 := !s.a0, c := s.c || !s.a0 }
  | .q  => { s with q := !s.q }
  | .r0 => { s with r0 := !s.r0, z := s.z || s.r0 }
  | .g1 => { s with g1 := !s.g1 }
  | .g2 => { s with g2 := !s.g2 }
  | .a1 => { s with a1 := !s.a1, c := s.c && s.a1, z := s.z && s.a1 }
  | .a2 => { s with a2 := !s.a2, c := s.c && s.a2, z := s.z && s.a2 }

/-- The merge's obligation, as a property of each transition: a client ack may
rise only against a server transaction not yet delivered (`c`) and only after
R0 has returned to zero since the previous client ack (`z`); A0 may rise only
when the previous transaction has been delivered. -/
def okTrans (s : St) : Gate → Bool
  | .a0 => s.a0 || !s.c
  | .a1 => s.a1 || (s.c && s.z)
  | .a2 => s.a2 || (s.c && s.z)
  | _ => true

/-- The state after reset is released (see `reset_values`): q = 1, all else 0,
no credit, R0 "has returned to zero". -/
def init0 : St := ⟨false, false, false, true, false, false, false, false, false, false, true⟩

/-- Reachability in the interleaving model with state-node INIT `st`. -/
inductive Reach (st : Nat) : St → Prop
  | init : Reach st init0
  | step {s : St} (x : Gate) : Reach st s → enabled st s x = true → Reach st (fire s x)

/-! ### Exhaustive check, as a kernel-checked inductive invariant -/

def bitN (b : Bool) : Nat := if b then 1 else 0

def enc (s : St) : Nat :=
  bitN s.r1 + 2 * bitN s.r2 + 4 * bitN s.a0 + 8 * bitN s.q + 16 * bitN s.r0 +
  32 * bitN s.g1 + 64 * bitN s.g2 + 128 * bitN s.a1 + 256 * bitN s.a2 +
  512 * bitN s.c + 1024 * bitN s.z

def dec (n : Nat) : St :=
  ⟨n % 2 == 1, n / 2 % 2 == 1, n / 4 % 2 == 1, n / 8 % 2 == 1, n / 16 % 2 == 1,
   n / 32 % 2 == 1, n / 64 % 2 == 1, n / 128 % 2 == 1, n / 256 % 2 == 1,
   n / 512 % 2 == 1, n / 1024 % 2 == 1⟩

theorem bitN_le (b : Bool) : bitN b ≤ 1 := by cases b <;> decide

theorem bitN_one_iff (b : Bool) : b = true ↔ bitN b = 1 := by cases b <;> decide

theorem dec_enc (s : St) : dec (enc s) = s := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := s
  have := bitN_le a; have := bitN_le b; have := bitN_le c; have := bitN_le d
  have := bitN_le e; have := bitN_le f; have := bitN_le g; have := bitN_le h
  have := bitN_le i; have := bitN_le j; have := bitN_le k
  simp only [dec, enc, St.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [Bool.eq_iff_iff, beq_iff_eq, bitN_one_iff]; omega)

theorem enc_lt (s : St) : enc s < 2048 := by
  have := bitN_le s.r1; have := bitN_le s.r2; have := bitN_le s.a0; have := bitN_le s.q
  have := bitN_le s.r0; have := bitN_le s.g1; have := bitN_le s.g2; have := bitN_le s.a1
  have := bitN_le s.a2; have := bitN_le s.c; have := bitN_le s.z
  simp only [enc]; omega

/-- The 112 reachable states of the HELD arbiter, as a bitmask over `enc`.
Computed outside Lean; it is NOT trusted: `held_closed` checks it is closed
under every enabled transition, and `held_inv` that it contains `init0`. -/
def MASK : Nat := 11871393150362666783950811786315465875007793460696261645537014654512117011370948901386230683939222689017613462664486964660675556157099357540443003469288285701391512724607515736177846497463062927642621069469764768423692469515441551907099520482023116816121190277482835242731491983118485174945560964763263144246032566610532659212253178809129802788525241402722681421236409469898300046934639532623051710342789755359966342036854961029987798858571465846688736163731558313398722921859479301199128477506013433810512199826125777731375190195524532702584444150808590387641387342602774249472

def inv (s : St) : Bool := MASK.testBit (enc s)

def closedAt (st : Nat) (n : Nat) : Bool :=
  !(MASK.testBit n) ||
    (Gate.all.any (enabled st (dec n)) &&
     Gate.all.all (fun x => !(enabled st (dec n) x) ||
       (inv (fire (dec n) x) && okTrans (dec n) x)))

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

theorem allBelow_sound (p : Nat → Bool) : ∀ n, allBelow p n = true → ∀ k, k < n → p k = true := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro h k hk
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact ih h.1 k hk
    · subst hk; exact h.2

theorem held_closed : allBelow (closedAt INIT_HELD) 2048 = true := by decide +kernel

theorem held_closedAt (s : St) : closedAt INIT_HELD (enc s) = true :=
  allBelow_sound _ 2048 held_closed _ (enc_lt s)

theorem closedAt_spec (st n : Nat) (h : closedAt st n = true) (hm : MASK.testBit n = true) :
    (∃ x, enabled st (dec n) x = true) ∧
    ∀ x, enabled st (dec n) x = true → inv (fire (dec n) x) = true ∧ okTrans (dec n) x = true := by
  simp only [closedAt, hm, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨x, _, hx⟩, hall⟩ := h
  refine ⟨⟨x, hx⟩, fun y hy => ?_⟩
  rcases hall y (Gate.mem_all y) with h0 | h0
  · rw [h0] at hy; cases hy
  · exact h0

theorem held_spec (s : St) (hi : inv s = true) :
    (∃ x, enabled INIT_HELD s x = true) ∧
    ∀ x, enabled INIT_HELD s x = true → inv (fire s x) = true ∧ okTrans s x = true := by
  have := closedAt_spec INIT_HELD (enc s) (held_closedAt s) hi
  rw [dec_enc] at this
  exact this

theorem held_inv (s : St) (h : Reach INIT_HELD s) : inv s = true := by
  induction h with
  | init => decide +kernel
  | step x _ hen ih => exact ((held_spec _ ih).2 x hen).1

/-- **Held arbiter, the merge's protocol obligation, every interleaving.**
In every reachable state, every enabled transition respects `okTrans`:
a client ack rises only against an undelivered server transaction and only
after R0 has returned to zero since the previous client ack; A0 rises only once
the previous transaction was delivered. So client acks and server transactions
alternate one-for-one.

Scope (claude/audit REPORT row 21): this is a speed-independent model with
ZERO wire delay, so the A0 fork is isochronic (both branches of A0 seen at
once). With wire delay the property depends on the A0-fork ordering
(H_A0_FORK; `ArbA0Fork.no_early_ack_iff`,
`TernaryPhases.arb_a0_fall_skewed_early_ack`). -/
theorem held_protocol (s : St) (h : Reach INIT_HELD s) (x : Gate)
    (hen : enabled INIT_HELD s x = true) : okTrans s x = true :=
  ((held_spec s (held_inv s h)).2 x hen).2

/-- The plain-English corollary: A2 cannot rise while A0 is still high from a
transaction already delivered to client 1 (or to anyone): it needs `c`. -/
theorem held_no_phantom_ack (s : St) (h : Reach INIT_HELD s)
    (hen : enabled INIT_HELD s .a2 = true) (hlow : s.a2 = false) :
    s.c = true ∧ s.z = true := by
  have := held_protocol s h .a2 hen
  simp [okTrans, hlow] at this
  exact this

/-- No reachable deadlock: some gate or process is always excited. -/
theorem held_live (s : St) (h : Reach INIT_HELD s) :
    ∃ x, enabled INIT_HELD s x = true :=
  (held_spec s (held_inv s h)).1

/-! ### Explicit traces (witnesses) -/

def run (st : Nat) : St → List Gate → Option St
  | s, [] => some s
  | s, x :: xs => if enabled st s x then run st (fire s x) xs else none

theorem run_reach (st : Nat) : ∀ (l : List Gate) (s s' : St), Reach st s →
    run st s l = some s' → Reach st s' := by
  intro l
  induction l with
  | nil => intro s s' hs h; simp [run] at h; subst h; exact hs
  | cons x xs ih =>
    intro s s' hs h
    simp only [run] at h
    split at h
    · exact ih _ _ (Reach.step x hs (by assumption)) h
    · cases h

def checkTrace (st : Nat) (l : List Gate) (p : St → Bool) : Bool :=
  match run st init0 l with
  | some s => p s
  | none => false

theorem checkTrace_sound (st : Nat) (l : List Gate) (p : St → Bool)
    (h : checkTrace st l p = true) : ∃ s, Reach st s ∧ p s = true := by
  unfold checkTrace at h
  split at h
  · exact ⟨_, run_reach st l _ _ Reach.init (by assumption), h⟩
  · cases h

/-- **The unheld arbiter's protocol violation (the header's trace).**
r1 wins, R0 and A0 rise, A1 acks, r1 starts its return-to-zero, r2 asks, q
flips with A0 still high, g2 rises, and A2 is now excited to rise with no
server transaction behind it and with R0 never having returned to zero. -/
theorem unheld_violation : ∃ s, Reach INIT_UNHELD s ∧
    (enabled INIT_UNHELD s .a2 && !s.a2 && s.a0 && !s.c && !s.z && s.r0) = true :=
  checkTrace_sound _ [.r1, .r0, .g1, .a0, .a1, .r1, .r2, .q, .g2] _ (by decide +kernel)

/-- ... and the ack actually fires: `okTrans` is violated on a reachable step. -/
theorem unheld_not_protocol : ∃ s, Reach INIT_UNHELD s ∧
    enabled INIT_UNHELD s .a2 = true ∧ okTrans s .a2 = false := by
  obtain ⟨s, hs, h⟩ := unheld_violation
  refine ⟨s, hs, ?_, ?_⟩ <;> simp_all [okTrans]

/-- **What the hold does NOT give in the untimed model: grant exclusion.**
r1 drops while g1's own fall is still pending; R0 (computed from r1, r2, q,
not from the grants) falls, the server drops A0, the hold releases, r2 asks,
q flips and g2 rises while g1 is still high. Exclusion during handover in
`bd_arbiter` is therefore a relative-timing fact (g1's one fall arc beats the
R0 → server → q → g2 round trip), not a speed-independent one. -/
theorem held_grant_overlap_untimed : ∃ s, Reach INIT_HELD s ∧ (s.g1 && s.g2) = true :=
  checkTrace_sound _ [.r1, .r0, .g1, .a0, .a1, .r1, .r0, .a0, .r2, .q, .g2] _ (by decide +kernel)

/-- Likewise both acks high at once: A1's fall (pending since A0 fell) is
overtaken by the next A0 rise. Not a phantom ack (`held_protocol` still holds:
A1 never rose a second time), but `viol = A1.A2` of hw/arb_prot.v is reachable
untimed, so its observed 0/96 is evidence for the timing assumptions too. -/
theorem held_ack_overlap_untimed : ∃ s, Reach INIT_HELD s ∧ (s.a1 && s.a2) = true :=
  checkTrace_sound _ [.r1, .r0, .g1, .a0, .a1, .r1, .r0, .a0, .r2, .q, .r0, .g2, .a0, .a2] _
    (by decide +kernel)

/-- The arbitration race itself (the metastability tier), as non-persistence:
r2 asks alone, q is excited to fall, r1 asks before q has moved, and q's
excitation is withdrawn. In silicon that is a runt on q. -/
theorem held_q_runt : ∃ s, Reach INIT_HELD s ∧
    (enabled INIT_HELD s .q && enabled INIT_HELD s .r1 &&
      !enabled INIT_HELD (fire s .r1) .q) = true :=
  checkTrace_sound _ [.r2] _ (by decide +kernel)

/-- A1's pending fall withdrawn by A0 rising again (the same race as
`held_ack_overlap_untimed`, seen as non-persistence). -/
theorem held_a1_runt : ∃ s, Reach INIT_HELD s ∧
    (enabled INIT_HELD s .a1 && enabled INIT_HELD s .a0 &&
      !enabled INIT_HELD (fire s .a0) .a1) = true :=
  checkTrace_sound _ [.r1, .r2, .r0, .a0, .g1, .a1, .r1, .r0, .a0, .q, .r0, .g1] _
    (by decide +kernel)

end Formal.Cells.ArbHandover
