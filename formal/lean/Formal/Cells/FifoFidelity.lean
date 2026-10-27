import Formal.Cells.PipeTimed
import Formal.Core.Delay.SAF

/-!
# Probe Bq: fidelity of `H_LUT_FIFO` (the controller LUT as a FIFO channel)

`PipeTimed`/`PipeTimedN` assume (`Ctl.H_LUT_FIFO`) that the `bd_link_ctl`
LUT's output is its pin-level excitation `ex` (the LUT's Boolean function of
its pins *at one instant*) read through ONE monotone read-time map `L.σ`.
This file asks which other delay models imply that, and where a real LUT,
whose pins reach the mux tree through DIFFERENT site-pin delays, breaks it.

Sections:
1. Bridges: shard A's discrete transport channel and the GLS's SAF channel
   give a `Ret` (FIFO read) directly (`fifo_of_transport`, `saf_fifo`,
   `gls_lut_fifo`, `gls_lut_fifo_spaced`).
2. The real `bd_c2n` INIT: the request/acknowledge pair is order-free
   (`c2n_set`, `c2n_hold`, `c2n_stay`); only the feedback pin's order matters.
3. The per-pin model `PinLut` (each pin read through its own FIFO map into a
   zero-time function at the mux-tree selects, then one FIFO output stage):
   equal pin maps give `H_LUT_FIFO` (`equal_pins_fifo`); the select-level phase
   theorem under the exact ordering condition `H_SEL_ORDER` (`sel_phase`);
   the arithmetic form of that condition (`sel_order_of_lat`); the edge-time
   band (`sel_edge_lo`, `sel_edge_hi`); the runt (`sel_runt`).
4. A concrete counterexample with the real INIT (`ce_*`): moving only the
   feedback pin from a fast to a slow site pin turns a clean run into an
   oscillating one that NO FIFO read of the pin-level excitation reproduces
   (`ce_not_fifo`), while the same environment with equal pin delays is clean
   and satisfies `H_LUT_FIFO` (`cj_fifo`, `cj_clean`).
5. Events to FIFO (`ret_of_edges`): an output that makes exactly the input's
   edges, in order, each delayed within `[lo, hi]`, is a FIFO read. With
   section 3 this turns the per-phase select-level result into `H_LUT_FIFO`.

Time is ℕ ticks, as in `PipeTimed`. Core Lean only.
-/

namespace Formal.Cells.FifoFidelity
open Formal.Cells
open Formal.Cells.PipeTimed

/-! ## 1. Single-input channel models that give a FIFO read -/

/-- Shard A's discrete warp (`Formal.Core.TraceDiscrete.Warp`) IS a `Ret`. -/
def retOfWarp {lo hi : Nat} {f : Nat → Nat} (w : Formal.Core.TraceDiscrete.Warp lo hi f) : Ret where
  σ := f
  lo := lo
  hi := hi
  mono := w.mono
  ge := w.early_le
  le := w.le_late

/-- **Transport ⇒ FIFO.** Shard A's discrete bounded transport channel
(the ℕ form of `Core/Delay/Pure.lean`'s `Chan`) is a FIFO read with the same
band, valid at every instant. -/
theorem fifo_of_transport {lo hi : Nat} {x y : Nat → Bool}
    (h : Formal.Core.TraceDiscrete.Transport lo hi x y) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, y t = x (r.σ t) := by
  obtain ⟨f, w, e⟩ := h
  exact ⟨retOfWarp w, rfl, rfl, e⟩

/-- **SAF ⇒ FIFO, band `[1, d]`.** The research GLS's LUT channel
(sample at fire, `Core/Delay/SAF.lean`) with delay `d` is a FIFO read of its
zero-time input with band `[1, d]`: never reordering, but with lower bound one
tick, not `d` (A's `saf_not_transport`). -/
theorem saf_fifo {d : Nat} (hd : 1 ≤ d) (x : Nat → Bool) :
    ∃ r : Ret, r.lo = 1 ∧ r.hi = d ∧ ∀ t, Formal.Core.DelaySAF.saf d x t = x (r.σ t) :=
  fifo_of_transport (Formal.Core.DelaySAF.saf_transport x hd)

/-- **A GLS controller LUT always satisfies `H_LUT_FIFO`, with band `[1, d]`.**
The GLS evaluates the LUT's function on the pin values *at one instant* (a
zero-time mux tree) and delays the result through one specify path. So the
input of its channel is exactly `ex`, and the channel is FIFO. Consequence:
a GLS run can never exhibit a violation of `H_LUT_FIFO`'s "no static glitch,
no reorder" part; it can only lose the lower bound. -/
theorem gls_lut_fifo {d : Nat} (hd : 1 ≤ d) (req ack qp rst : Trace) :
    ∃ L : Ret, L.lo = 1 ∧ L.hi = d ∧
      ∀ t, L.hi ≤ t → Formal.Core.DelaySAF.saf d (ex req ack qp rst) t = ex req ack qp rst (L.σ t) := by
  obtain ⟨r, h1, h2, h3⟩ := saf_fifo hd (ex req ack qp rst)
  exact ⟨r, h1, h2, fun t _ => h3 t⟩

/-- **The full band `[d, d]` when the excitation is spaced.** If `ex` never
changes twice within `d` ticks (true in a handshake: one excitation edge per
phase, phases longer than `d`), the GLS LUT is the fixed delay `d`. -/
theorem gls_lut_fifo_spaced {d : Nat} (hd : 1 ≤ d) (req ack qp rst : Trace)
    (hs : Formal.Core.DelaySAF.Spaced d (ex req ack qp rst)) :
    ∀ t, (Ret.shift d).hi ≤ t →
      Formal.Core.DelaySAF.saf d (ex req ack qp rst) t = ex req ack qp rst ((Ret.shift d).σ t) := by
  intro t _
  rw [Formal.Core.DelaySAF.saf_eq_delay_of_spaced hd hs]
  rfl

/-! ## 2. The real `bd_c2n` INIT: which pin orders matter

`CElemTiming.exc INIT_c2n a b q r` with `a = req` (I0), `b = ack = c_next`
(I1), `q` the feedback (I2), `r = rst` (I3). Phase target `v`: the request
moves to `v`, the acknowledge to `!v`. -/

/-- Both inputs at the target: the excitation is `v` whatever the feedback. -/
theorem c2n_set (v q : Bool) : CElemTiming.exc CElemTiming.INIT_c2n v (!v) q false = v := by
  rw [CElemTiming.c2n_eq]; cases v <;> cases q <;> rfl

/-- Feedback at `v` and at least one input still at the target: `v` (hold). -/
theorem c2n_hold (v a b : Bool) (h : a = v ∨ b = !v) :
    CElemTiming.exc CElemTiming.INIT_c2n a b v false = v := by
  rw [CElemTiming.c2n_eq]
  cases v <;> cases a <;> cases b <;> simp_all

/-- Feedback at `!v` and at least one input not yet at the target: `!v`.
With `c2n_set` this is **order-freedom of the (req, c_next) pair**: in a
phase both move toward the target once; whichever arrives first at the mux
tree, the excitation stays `!v` until the later one arrives, then becomes
`v`. No static glitch and no reorder can come from this pair. -/
theorem c2n_stay (v a b : Bool) (h : a = !v ∨ b = v) :
    CElemTiming.exc CElemTiming.INIT_c2n a b (!v) false = !v := by
  rw [CElemTiming.c2n_eq]
  cases v <;> cases a <;> cases b <;> simp_all

/-- Reset forces 0 from any pin values. -/
theorem c2n_reset (a b q : Bool) : CElemTiming.exc CElemTiming.INIT_c2n a b q true = false := by
  rw [CElemTiming.c2n_eq]; rfl

/-! ## 3. The per-pin model -/

/-- The excitation seen at the mux-tree selects: each pin read through its
own map. -/
def exSel (pr pa pq ps : Ret) (req ack qp rst : Trace) : Trace := fun t =>
  CElemTiming.exc CElemTiming.INIT_c2n (req (pr.σ t)) (ack (pa.σ t)) (qp (pq.σ t)) (rst (ps.σ t))

/-- **The per-pin LUT model** of `bd_c2n`.
* `pr pa pq ps`: **H_PIN_FIFO**, the path from each LUT pin (I0 req, I1 ack,
  I2 feedback, I3 rst) to its mux-tree select: site-pin input buffer, a
  single-input chain of CMOS stages, FIFO by A's `Pure` argument. Their bands
  are the prjxray site-pin delays of the PHYSICAL pin the router chose
  (A6 ≈ 0.005 ns … A1 ≈ 0.516 ns at slow max; nextpnr's SDF charges a flat
  25 ps). Test: GLS with per-pin site delays BEFORE the function (not as
  specify paths after it); board: the counterexample of section 4 with
  LOCK_PINS placing the feedback on A1 and the request on A5.
* `out`, **H_TREE_FIFO**: the mux tree plus output stage, as ONE FIFO read of
  the Boolean function of the select vector. This contains the residual
  static-hazard assumption: one select switching between equal leaves gives
  no output glitch (B-muxtree-fidelity: plausible, unverified). -/
structure PinLut (req ack rst O qp : Trace) where
  pr : Ret
  pa : Ret
  pq : Ret
  ps : Ret
  out : Ret
  H_OUT : ∀ t, out.hi ≤ t → O t = exSel pr pa pq ps req ack qp rst (out.σ t)

/-- **Equal pin maps give `H_LUT_FIFO`.** If all four pins reach the selects
through the same map `p`, the per-pin model is exactly the lumped model of
`PipeTimed.Ctl` with `L = p ; out`. -/
theorem equal_pins_fifo {req ack rst O qp : Trace} (P : PinLut req ack rst O qp) (p : Ret)
    (hr : P.pr = p) (ha : P.pa = p) (hq : P.pq = p) (hs : P.ps = p) :
    ∀ t, (Ret.comp p P.out).hi ≤ t → O t = ex req ack qp rst ((Ret.comp p P.out).σ t) := by
  intro t ht
  have h : P.out.hi ≤ t := by
    have : (Ret.comp p P.out).hi = p.hi + P.out.hi := rfl
    omega
  rw [P.H_OUT t h]
  unfold exSel; rw [hr, ha, hq, hs]; rfl

section perpin
variable {req ack rst O qp : Trace}

/-- **Select-level phase theorem.** Phase target `v`. At the pins: request
`v` on `[ρ, ρ')`, acknowledge `!v` on `[α, α')`, feedback `v` on `[κ, κ')`,
reset low from `R`. If the feedback's new value reaches its select no later
than the FIRST departure reaches its select (**H_SEL_ORDER**), and keeps it
until the last departure (`H_SEL_KEEP`), then the select-level excitation is
exactly `v` from the LATER of the two arrivals to the later departure. The
arrival order of req and ack does not matter (section 2). -/
theorem sel_phase (P : PinLut req ack rst O qp) (v : Bool) (ρ ρ' α α' κ κ' R : Nat)
    (hreq : ∀ s, ρ ≤ s → s < ρ' → req s = v)
    (hack : ∀ s, α ≤ s → s < α' → ack s = !v)
    (hqp : ∀ s, κ ≤ s → s < κ' → qp s = v)
    (hrst : ∀ s, R ≤ s → rst s = false)
    (H_SEL_ORDER : P.pq.fst κ ≤ min (P.pr.fst ρ') (P.pa.fst α'))
    (H_SEL_KEEP : max (P.pr.fst ρ') (P.pa.fst α') ≤ P.pq.fst κ') :
    ∀ t, max (P.pr.fst ρ) (P.pa.fst α) ≤ t → t < max (P.pr.fst ρ') (P.pa.fst α') →
      P.ps.fst R ≤ t → exSel P.pr P.pa P.pq P.ps req ack qp rst t = v := by
  intro t h1 h2 h3
  have er : rst (P.ps.σ t) = false := hrst _ (P.ps.fst_after h3)
  unfold exSel; rw [er]
  by_cases c1 : t < P.pr.fst ρ'
  · have rq : req (P.pr.σ t) = v :=
      hreq _ (P.pr.fst_after (by omega)) (P.pr.fst_before c1)
    by_cases c2 : t < P.pa.fst α'
    · have ak : ack (P.pa.σ t) = !v :=
        hack _ (P.pa.fst_after (by omega)) (P.pa.fst_before c2)
      rw [rq, ak]; exact c2n_set v _
    · have q : qp (P.pq.σ t) = v :=
        hqp _ (P.pq.fst_after (by omega)) (P.pq.fst_before (by omega))
      rw [q]; exact c2n_hold v _ _ (Or.inl rq)
  · have c2 : t < P.pa.fst α' := by omega
    have ak : ack (P.pa.σ t) = !v :=
      hack _ (P.pa.fst_after (by omega)) (P.pa.fst_before c2)
    have q : qp (P.pq.σ t) = v :=
      hqp _ (P.pq.fst_after (by omega)) (P.pq.fst_before (by omega))
    rw [q]; exact c2n_hold v _ _ (Or.inr ak)

/-- **The runt.** If at the selects the request has already left the target
while the acknowledge is still there and the feedback has not yet arrived, the
excitation is back at the OLD value: the phase's `v` (from `sel_phase`'s first
part) is followed by `!v`, a glitch that no FIFO read of a single-edge `ex`
can produce. This is what `H_SEL_ORDER` excludes. -/
theorem sel_runt (P : PinLut req ack rst O qp) (v : Bool) (t : Nat)
    (hr : req (P.pr.σ t) = !v) (hq : qp (P.pq.σ t) = !v) (hs : rst (P.ps.σ t) = false) :
    exSel P.pr P.pa P.pq P.ps req ack qp rst t = !v := by
  unfold exSel; rw [hr, hq, hs]; exact c2n_stay v _ _ (Or.inl rfl)

/-- **H_SEL_ORDER in arithmetic form.** If the feedback reaches its PIN by
`K`, both departures leave their PINS no earlier than `D ≥ 1`, and
`K + pq.hi ≤ D + min pr.lo pa.lo`, then `H_SEL_ORDER` holds. In words: the
feedback's latest pin arrival plus the slowest feedback site-pin delay is no
later than the environment's earliest departure plus the fastest departing
pin's site-pin delay. -/
theorem sel_order_of_lat (P : PinLut req ack rst O qp) {κ ρ' α' K D : Nat}
    (hk : κ ≤ K) (hD : 1 ≤ D) (hr : D ≤ ρ') (ha : D ≤ α')
    (hlat : K + P.pq.hi ≤ D + min P.pr.lo P.pa.lo) :
    P.pq.fst κ ≤ min (P.pr.fst ρ') (P.pa.fst α') := by
  have e1 := P.pq.fst_le κ
  have e2 := P.pr.fst_lo (c := ρ') (by omega)
  have e3 := P.pa.fst_lo (c := α') (by omega)
  have : min P.pr.lo P.pa.lo ≤ P.pr.lo := Nat.min_le_left _ _
  have : min P.pr.lo P.pa.lo ≤ P.pa.lo := Nat.min_le_right _ _
  omega

/-- The select-level edge comes no earlier than the pin-level phase start plus
the FASTEST of the two pins. -/
theorem sel_edge_lo (P : PinLut req ack rst O qp) {ρ α : Nat} (h1 : 1 ≤ ρ) (h2 : 1 ≤ α) :
    max ρ α + min P.pr.lo P.pa.lo ≤ max (P.pr.fst ρ) (P.pa.fst α) := by
  have e2 := P.pr.fst_lo h1
  have e3 := P.pa.fst_lo h2
  have : min P.pr.lo P.pa.lo ≤ P.pr.lo := Nat.min_le_left _ _
  have : min P.pr.lo P.pa.lo ≤ P.pa.lo := Nat.min_le_right _ _
  omega

/-- … and no later than the phase start plus the SLOWEST. So a lumped band
for the LUT must span the per-pin spread: `L.lo ≤ out.lo + min pin lo`,
`L.hi ≥ out.hi + max pin hi`. -/
theorem sel_edge_hi (P : PinLut req ack rst O qp) (ρ α : Nat) :
    max (P.pr.fst ρ) (P.pa.fst α) ≤ max ρ α + max P.pr.hi P.pa.hi := by
  have e2 := P.pr.fst_le ρ
  have e3 := P.pa.fst_le α
  have : P.pr.hi ≤ max P.pr.hi P.pa.hi := Nat.le_max_left _ _
  have : P.pa.hi ≤ max P.pr.hi P.pa.hi := Nat.le_max_right _ _
  omega

end perpin

/-! ## 4. Counterexample with the real INIT

Pins: req (I0) through 1 tick, ack (I1) 1, feedback (I2) **6**, rst (I3) 1;
mux tree + output 2 ticks; feedback wire `O → I2` 1 tick. The request rises
at 10 and the upstream stage withdraws it at 16, 3 ticks after the node rose
(13); the acknowledge stays low (the downstream stage is slow). The feedback
reaches its select at 20, the withdrawn request at 17: `H_SEL_ORDER` fails
(20 > 17). The select-level excitation drops at 17 and the loop, now a
buffer (req = 0, ack = 0), recirculates the 3-tick hole forever: period 9.

With every pin at 1 tick (what nextpnr's flat 25 ps per pin shows) the same
environment gives one clean edge (`cj_*`), and the lumped 5b inequality
`L.hi + wh ≤ L.lo + E` holds with `L = [3,3]`, `wh = 1`, `E = 3`. With the
true band `L = [3, 8]` it fails (`9 > 6`). -/

def zeroT : Trace := fun _ => false
/-- The request at the pin: high on `[10, 16)`. -/
def reqC : Trace := fun t => decide (10 ≤ t ∧ t < 16)
/-- The select-level excitation of the run (closed form). -/
def eI : Trace := fun t => decide (11 ≤ t ∧ t < 17) || decide (17 ≤ t ∧ 3 ≤ (t - 17) % 9)
/-- The node: `eI` 2 ticks later. -/
def OC : Trace := fun t => eI (t - 2)
/-- The feedback at its pin: the node 1 tick later. -/
def qpC : Trace := fun t => OC (t - 1)

theorem eI_small : ∀ s, s < 40 →
    eI s = CElemTiming.exc CElemTiming.INIT_c2n (reqC (s - 1)) false (eI (s - 9)) false := by
  decide

theorem eI_period (s : Nat) (h : 26 ≤ s) : eI s = eI (s - 9) := by
  have e : (s - 17) % 9 = (s - 9 - 17) % 9 := by omega
  simp only [eI, e]
  have a1 : ¬ (11 ≤ s ∧ s < 17) := by omega
  have a2 : ¬ (11 ≤ s - 9 ∧ s - 9 < 17) := by omega
  have a3 : 17 ≤ s := by omega
  have a4 : 17 ≤ s - 9 := by omega
  simp [a1, a2, a3, a4]

theorem eI_loop (s : Nat) :
    eI s = CElemTiming.exc CElemTiming.INIT_c2n (reqC (s - 1)) false (eI (s - 9)) false := by
  by_cases h : s < 40
  · exact eI_small s h
  · have r : reqC (s - 1) = false := by simp only [reqC]; apply decide_eq_false; omega
    rw [r, CElemTiming.c2n_eq, eI_period s (by omega)]
    cases eI (s - 9) <;> rfl

/-- The run's per-pin model: it IS a behaviour of `PinLut` (every gate
relation holds at every instant). -/
def ceLut : PinLut reqC zeroT zeroT OC qpC where
  pr := Ret.shift 1
  pa := Ret.shift 1
  pq := Ret.shift 6
  ps := Ret.shift 1
  out := Ret.shift 2
  H_OUT := by
    intro t _
    show eI (t - 2) = CElemTiming.exc CElemTiming.INIT_c2n (reqC (t - 2 - 1)) false
      (OC (t - 2 - 6 - 1)) false
    have e : OC (t - 2 - 6 - 1) = eI (t - 2 - 9) := by
      simp only [OC]; congr 1
    rw [e]; exact eI_loop _

/-- The feedback wire is a fixed 1-tick delay (5b's window channel). -/
theorem ce_fb : CElemTiming.WinDelay 1 1 OC qpC := by
  intro t ht; exact ⟨t - 1, by omega, by omega, rfl⟩

/-- The pin-level excitation of the run is 1 on `[10, 20)` and 0 before 10:
it has ONE rising edge in `[0, 20)`. -/
theorem ce_ex_lo : ∀ t, t < 10 → ex reqC zeroT qpC zeroT t = false := by decide
theorem ce_ex_hi : ∀ t, t < 20 → 10 ≤ t → ex reqC zeroT qpC zeroT t = true := by decide

/-- The node rises at 13 and drops back at 19: a runt (it rises again at 22,
and keeps oscillating). -/
theorem ce_node : OC 12 = false ∧ OC 13 = true ∧ OC 18 = true ∧ OC 19 = false ∧ OC 22 = true := by
  decide

/-- **No FIFO read of the pin-level excitation reproduces this node**, for any
band with `hi ≤ 18` (the physical band here is `[3, 8]`): `H_LUT_FIFO` FAILS
for a LUT whose feedback pin is 5 ticks slower than its request pin, in a
handshake that satisfies the lumped 5b inequality computed with equal pin
delays. -/
theorem ce_not_fifo (L : Ret) (hL : L.hi ≤ 18) :
    ¬ (∀ t, L.hi ≤ t → OC t = ex reqC zeroT qpC zeroT (L.σ t)) := by
  intro h
  have h18 := h 18 (by omega)
  have h19 := h 19 (by omega)
  have n := ce_node
  have s18 : 10 ≤ L.σ 18 := by
    apply Classical.byContradiction; intro hc
    have := ce_ex_lo (L.σ 18) (by omega)
    rw [n.2.2.1] at h18; rw [this] at h18; exact Bool.noConfusion h18
  have m := L.mono 18 19 (by omega)
  have le := L.le 19
  have := ce_ex_hi (L.σ 19) (by omega) (by omega)
  rw [n.2.2.2.1, this] at h19; exact Bool.noConfusion h19

/-! The same environment with all pins at 1 tick: clean. -/

def eJ : Trace := fun t => decide (11 ≤ t)
def OJ : Trace := fun t => eJ (t - 2)
def qpJ : Trace := fun t => OJ (t - 1)

theorem eJ_loop (s : Nat) :
    eJ s = CElemTiming.exc CElemTiming.INIT_c2n (reqC (s - 1)) false (eJ (s - 4)) false := by
  by_cases h : s < 40
  · revert s; decide
  · have r : reqC (s - 1) = false := by simp only [reqC]; apply decide_eq_false; omega
    have e1 : eJ s = true := by simp only [eJ]; apply decide_eq_true; omega
    have e2 : eJ (s - 4) = true := by simp only [eJ]; apply decide_eq_true; omega
    rw [r, e1, e2]; rfl

def cjLut : PinLut reqC zeroT zeroT OJ qpJ where
  pr := Ret.shift 1
  pa := Ret.shift 1
  pq := Ret.shift 1
  ps := Ret.shift 1
  out := Ret.shift 2
  H_OUT := by
    intro t _
    show eJ (t - 2) = CElemTiming.exc CElemTiming.INIT_c2n (reqC (t - 2 - 1)) false
      (OJ (t - 2 - 1 - 1)) false
    have e : OJ (t - 2 - 1 - 1) = eJ (t - 2 - 4) := by
      simp only [OJ]; congr 1
    rw [e]; exact eJ_loop _

/-- Equal pins: `H_LUT_FIFO` holds for the clean run (by `equal_pins_fifo`). -/
theorem cj_fifo :
    ∀ t, (Ret.comp (Ret.shift 1) (Ret.shift 2)).hi ≤ t →
      OJ t = ex reqC zeroT qpJ zeroT ((Ret.comp (Ret.shift 1) (Ret.shift 2)).σ t) :=
  equal_pins_fifo cjLut (Ret.shift 1) rfl rfl rfl rfl

/-- … and the node makes exactly one edge, at 13. -/
theorem cj_clean (t : Nat) : OJ t = decide (13 ≤ t) := by
  simp only [OJ, eJ]
  by_cases h : 13 ≤ t
  · rw [decide_eq_true h]; apply decide_eq_true; omega
  · rw [decide_eq_false h]; apply decide_eq_false; omega

/-! ## 5. Events to FIFO

The phases of a clean four-phase signal: `c 0 = 0`, `c` strictly increasing;
`x` has value `val j` on `[c j, c (j+1))`. If `y` has the SAME values on
`[e j, e (j+1))`, with `e 0 = 0` and each edge delayed within `[lo, hi]`, then
`y` is a FIFO read of `x` (from `hi` on). This is the ℕ, alternating-signal
case of A's open `Wip.events_adequate`. -/

/-- Largest `j ≤ n` with `e j ≤ t` (0 if none beyond 0). -/
def lastLe (e : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if e (n + 1) ≤ t then n + 1 else lastLe e t n

theorem lastLe_le (e : Nat → Nat) (t : Nat) : ∀ n, lastLe e t n ≤ n := by
  intro n; induction n with
  | zero => simp [lastLe]
  | succ n ih => simp only [lastLe]; split <;> omega

theorem lastLe_spec (e : Nat → Nat) (t : Nat) (he0 : e 0 = 0) :
    ∀ n, e (lastLe e t n) ≤ t := by
  intro n; induction n with
  | zero => simp [lastLe, he0]
  | succ n ih => simp only [lastLe]; split <;> assumption

/-- Under strict monotonicity, every `j ≤ n` with `e j ≤ t` is at most `lastLe`. -/
theorem lastLe_max (e : Nat → Nat) (t : Nat) :
    ∀ n j, j ≤ n → e j ≤ t → j ≤ lastLe e t n := by
  intro n; induction n with
  | zero => intro j hj _; omega
  | succ n ih =>
    intro j hj hjt
    simp only [lastLe]
    split
    · exact hj
    · rename_i hn
      by_cases hjn : j = n + 1
      · subst hjn; exact absurd hjt hn
      · exact ih j (by omega) hjt

/-- `e j ≥ j` for a strictly increasing sequence. -/
theorem ge_idx (e : Nat → Nat) (hmono : ∀ i j, i < j → e i < e j) : ∀ j, j ≤ e j := by
  intro j; induction j with
  | zero => omega
  | succ j ih => have := hmono j (j + 1) (by omega); omega

/-- The phase index of `y` at `t`. -/
def idx (e : Nat → Nat) (t : Nat) : Nat := lastLe e t t

theorem idx_spec (e : Nat → Nat) (he0 : e 0 = 0) (hmono : ∀ i j, i < j → e i < e j) (t : Nat) :
    e (idx e t) ≤ t ∧ t < e (idx e t + 1) := by
  refine ⟨lastLe_spec e t he0 t, ?_⟩
  apply Classical.byContradiction; intro h
  have h' : e (idx e t + 1) ≤ t := by omega
  have g := ge_idx e hmono (idx e t + 1)
  have := lastLe_max e t t (idx e t + 1) (by omega) h'
  unfold idx at this; omega

theorem idx_mono (e : Nat → Nat) (he0 : e 0 = 0) (hmono : ∀ i j, i < j → e i < e j)
    {a b : Nat} (hab : a ≤ b) : idx e a ≤ idx e b := by
  have ha := idx_spec e he0 hmono a
  have g := ge_idx e hmono (idx e a)
  exact lastLe_max e b b (idx e a) (by omega) (by omega)

/-- **Edge matching gives a FIFO read.** -/
def retOfEdges (c e : Nat → Nat) (lo hi : Nat) (hlh : lo ≤ hi) (he0 : e 0 = 0)
    (hce : ∀ i j, i < j → c i ≤ c j) (hmono : ∀ i j, i < j → e i < e j)
    (hlo : ∀ j, c j + lo ≤ e j) : Ret where
  σ t := max (c (idx e t)) (t - hi)
  lo := lo
  hi := hi
  mono a b h := by
    have i1 := idx_mono e he0 hmono h
    have : c (idx e a) ≤ c (idx e b) := by
      rcases Nat.lt_or_ge (idx e a) (idx e b) with h' | h'
      · exact hce _ _ h'
      · exact Nat.le_of_eq (congrArg c (by omega))
    omega
  ge t := Nat.le_max_right _ _
  le t := by
    have s := idx_spec e he0 hmono t
    have := hlo (idx e t)
    have := hlh
    omega

theorem ret_of_edges (c e : Nat → Nat) (lo hi : Nat) (hlh : lo ≤ hi) (val : Nat → Bool) {x y : Trace}
    (hc0 : c 0 = 0) (he0 : e 0 = 0)
    (hce : ∀ i j, i < j → c i < c j) (hmono : ∀ i j, i < j → e i < e j)
    (hlo : ∀ j, c j + lo ≤ e j) (hhi : ∀ j, e j ≤ c j + hi)
    (hx : ∀ j s, c j ≤ s → s < c (j + 1) → x s = val j)
    (hy : ∀ j t, e j ≤ t → t < e (j + 1) → y t = val j) :
    ∃ L : Ret, L.lo = lo ∧ L.hi = hi ∧ ∀ t, hi ≤ t → y t = x (L.σ t) := by
  refine ⟨retOfEdges c e lo hi hlh he0 (fun i j h => Nat.le_of_lt (hce i j h)) hmono hlo, rfl, rfl, ?_⟩
  intro t _
  have s := idx_spec e he0 hmono t
  have k1 := hlo (idx e t)
  have k2 := hhi (idx e t + 1)
  have _ := hc0
  have k3 := hce (idx e t) (idx e t + 1) (by omega)
  show y t = x (max (c (idx e t)) (t - hi))
  rw [hy (idx e t) t s.1 s.2]
  exact (hx (idx e t) _ (Nat.le_max_left _ _) (by omega)).symm

/-- **Per-pin model ⇒ `H_LUT_FIFO`, run by run.** If the pin-level excitation
`ex` is a clean phase sequence (edges `c j`), and the select-level excitation
is the same phase sequence with each edge delayed within `[lo, hi]` (which
`sel_phase`, `sel_edge_lo/hi` give phase by phase under `H_SEL_ORDER`), then
the node satisfies exactly `PipeTimed.Ctl.H_LUT_FIFO` with band
`[lo + out.lo, hi + out.hi]`. -/
theorem pinlut_fifo_of_edges {req ack rst O qp : Trace} (P : PinLut req ack rst O qp)
    (c e : Nat → Nat) (lo hi : Nat) (hlh : lo ≤ hi) (val : Nat → Bool)
    (hc0 : c 0 = 0) (he0 : e 0 = 0)
    (hce : ∀ i j, i < j → c i < c j) (hmono : ∀ i j, i < j → e i < e j)
    (hlo : ∀ j, c j + lo ≤ e j) (hhi : ∀ j, e j ≤ c j + hi)
    (hx : ∀ j s, c j ≤ s → s < c (j + 1) → ex req ack qp rst s = val j)
    (hy : ∀ j t, e j ≤ t → t < e (j + 1) →
      exSel P.pr P.pa P.pq P.ps req ack qp rst t = val j) :
    ∃ L : Ret, L.lo = lo + P.out.lo ∧ L.hi = hi + P.out.hi ∧
      ∀ t, L.hi ≤ t → O t = ex req ack qp rst (L.σ t) := by
  obtain ⟨r, hl, hh, hr⟩ := ret_of_edges c e lo hi hlh val hc0 he0 hce hmono hlo hhi hx hy
  refine ⟨Ret.comp r P.out, by simp [Ret.comp, hl], by simp [Ret.comp, hh], ?_⟩
  intro t ht
  have ht' : r.hi + P.out.hi ≤ t := ht
  have g := P.out.ge t
  rw [P.H_OUT t (by omega)]
  exact hr _ (by omega)

end Formal.Cells.FifoFidelity
