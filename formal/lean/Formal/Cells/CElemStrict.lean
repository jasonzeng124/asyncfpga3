import Formal.Cells.CElemFn
import Formal.Cells.Latch
open Formal.Core.LutList

/-!
# The C-element's own-feedback race must be STRICT in a per-pin mux-tree LUT

Contradiction X2 of `formal/out/gcd_hw_hypotheses.md`. Shard B states the
race `H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E` (`CElemTiming.c2_four_phase`)
with `≤`. That is sound only under the atomic-LUT reading (all pins of the
LUT sampled at one instant, A's H_ATOMIC_LUT). C-8g
(`Net.MullerTimedCx.boundary_function_hazard`) and C-12c (inertial bound
strict) say equality is not safe in a mux-tree LUT. This file decides the
question in B's per-mux Kleene model on the REAL INIT and pin map.

## Model (discrete time, one tick = 1 ps)

* **H_TREE** (per-pin mux tree, Kleene): the tree's root value `G t` is the
  Kleene function of the values the pins' SELECTS carry at `t`:
  `G t = F (i t) (qp t)` with `F` the real INIT read by `lutK`
  (`CElemFn.c2K`: I0 = a, I1 = b, I2 = q (feedback), I3 = rst = 0, I4 = I5
  = 0). `lutK` IS the tree of Kleene 2:1 muxes (`Prelim.lutK`), and by
  `MuxTree.Tree.evalK_order_indep` any pin order of the tree gives the same
  value, so the result does not depend on which pin sits at the root. Each
  pin is its own trace, so each pin has its own arrival time at its select;
  any pin-to-select buffer delay is part of that trace.
* **H_MUX_KLEENE** (the per-mux hypothesis of `MuxTree`, used here in
  time): while a select moves it reads `x` (it is neither rail). A pin edge
  is therefore `old` before its start `s`, `x` on `[s, s + w)`, `new` from
  `s + w`; `w` is the X window. `w = 0` is an instantaneous (binary) select.
* **H_FB_PURE**: the feedback pin is a pure delay `D ≥ 1` of the root:
  `qp t = G (t - D)` for `t ≥ D`, the settled old value `v` before. `D` is
  the loop: the LUT root-to-O path plus the routed `O -> I2` wire plus the
  I2 buffer (`dl + dw` in `CElemTiming`). The output `O` is `G` delayed by
  `dl`, so a hazard on `G` is a hazard on `O`.
* **H_IN_PHASES** (the environment): the inputs (a vector of pins, `ι`) pass
  through five phases: `I0` before `tb`; `IX` (the follow pin's select
  moving) on `[tb, tb + wb)`; `I1` (the inputs agree, the cell must follow
  to `n`) on `[tb + wb, s)`; `RX` (the release pin's select moving) on
  `[s, s + wa)`; `R1` (inputs disagree, the cell must HOLD `n`) from
  `s + wa`. H_ACK_ORDER: `tb + wb ≤ s` (the release comes after the follow).

The spec (`Spec`): `G` is ONE clean edge `v → n`: `v` before `tb`, `x` only
during the follow pin's own window `[tb, tb + wb)`, `n` from `tb + wb` on,
forever. Anything else is a hazard (a return to `v`, or an `x` after
`tb + wb`).

## Results (generic in `F`, instantiated on the real `bd_c2` INIT)

* `clean`: if `tb + D + wb ≤ s` (the release pin starts moving no earlier
  than the tick the feedback pin has settled) the output is the clean edge.
* `hazard`: if `s < tb + D + wb`, then `G s ≠ n` while the spec says `n`:
  an X (window overlap) or a full binary glitch back to `v`.
* `clean_iff`: exact, `Spec ↔ tb + D + wb ≤ s`.
* `box_iff`: over every `D ∈ [Dlo, Dhi]` and every release start `s ≥ slo`,
  the spec holds for every behaviour iff `tb + Dhi + wb ≤ slo`.
* `env_latency_iff`: the same in B's binary-edge terms (`c = tb + wb` is
  B's phase start `c k`, the release pin's binary edge is `s + wa ≥ c + dlmin
  + E`): universally safe iff `dlmax + dwmax + wa ≤ dlmin + E`.
  With `wa ≥ 1` (H_MUX_KLEENE, one tick) this is B's `H_ENV_LATENCY` made
  strict by `wa`; at `wa = 1`: `dlmax + dwmax < dlmin + E`.
  With `wa = 0` (instantaneous select, the binary/atomic reading) B's `≤` is
  exact: equality is safe exactly when the release pin's select has no X
  window, which is C-12c's closed transport bound; with any X window it is
  unsafe, C-12c's strict inertial bound and C-8g's function hazard.
* `c2_all`: the facts the generic proof needs hold on the real INIT for all
  eight bd_c2 cycles (rising/falling × follow pin a/b × release pin a/b);
  `c2n_c8g`: also for C-8g's bd_c2n transition (1,0,0) → (1,1,1);
  `latch_facts`: also for the bd_latch odd bit (data edge, then enable fall).
* `boundary_x` / `boundary_x_c2n`: concrete equality traces on the real
  INITs: with B's `≤` met with equality (`wa = wb = 1`, D = 420), `G` reads
  `n` one tick before and `x` at the release tick (bd_c2), and for bd_c2n
  `G` reads `x` at the release tick.

Core Lean only; `decide` on finite facts, `omega` and induction elsewhere.
-/

namespace Formal.Cells
namespace CElemStrict

open Formal.Cells.CElemFn

/-! ## Waveforms -/

/-- The input vector's five phases (H_IN_PHASES). -/
def phase {ι : Type} (I0 IX I1 RX R1 : ι) (tb wb s wa t : Nat) : ι :=
  if t < tb then I0 else if t < tb + wb then IX else if t < s then I1
  else if t < s + wa then RX else R1

/-- One clean edge `v → n` with X window `[tb, tb + wb)` (the spec). -/
def edge (v n : Bool) (tb wb t : Nat) : K3 :=
  if t < tb then K3.ofBool v else if t < tb + wb then K3.x else K3.ofBool n

/-- The loop's gate relations (H_TREE, H_FB_PURE, H_IN_PHASES). -/
structure Loop {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : Bool)
    (tb wb s wa D : Nat) (i : Nat → ι) (qp G : Nat → K3) : Prop where
  H_TREE : ∀ t, G t = F (i t) (qp t)
  H_FB_PURE : ∀ t, qp t = if t < D then K3.ofBool v else G (t - D)
  H_IN_PHASES : ∀ t, i t = phase I0 IX I1 RX R1 tb wb s wa t

/-- The Kleene facts of the cell's function the race proof uses. `v` is the
held value before, `n` the value the cell must follow to and then hold. -/
structure Facts {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v n : Bool) : Prop where
  ne : v ≠ n
  init : F I0 (K3.ofBool v) = K3.ofBool v
  win_v : F IX (K3.ofBool v) = K3.x
  win_x : F IX K3.x = K3.x
  follow : ∀ k, F I1 k = K3.ofBool n
  holdX : F RX (K3.ofBool n) = K3.ofBool n
  hold1 : F R1 (K3.ofBool n) = K3.ofBool n
  -- the hazard side
  hzXX : F RX K3.x = K3.x
  hz1X : F R1 K3.x = K3.x
  hzXv : F RX (K3.ofBool v) = K3.x
  hz1v : F R1 (K3.ofBool v) = K3.ofBool v

def Spec (v n : Bool) (tb wb : Nat) (G : Nat → K3) : Prop :=
  ∀ t, G t = edge v n tb wb t

section generic
variable {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
  {tb wb s wa D : Nat} {i : Nat → ι} {qp G : Nat → K3}

theorem ofBool_ne_x (b : Bool) : K3.ofBool b ≠ K3.x := by cases b <;> decide

theorem ofBool_inj {b c : Bool} (h : K3.ofBool b = K3.ofBool c) : b = c := by
  cases b <;> cases c <;> first | rfl | exact absurd h (by decide)

/-- Before the release starts the output is the clean edge, whatever the
race (needs only `D ≥ 1`). -/
theorem prefix_ok (L : Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) :
    ∀ t, t < s → G t = edge v n tb wb t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hts
    rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_PURE]
    unfold phase edge
    by_cases h1 : t < tb
    · simp only [h1, ↓reduceIte]
      by_cases h2 : t < D
      · simp only [h2, ↓reduceIte]; exact H.init
      · simp only [h2, ↓reduceIte]
        rw [ih (t - D) (by omega) (by omega)]
        simp only [edge, show t - D < tb by omega, ↓reduceIte]; exact H.init
    · simp only [h1, ↓reduceIte]
      by_cases h2 : t < tb + wb
      · simp only [h2, ↓reduceIte]
        by_cases h3 : t < D
        · simp only [h3, ↓reduceIte]; exact H.win_v
        · simp only [h3, ↓reduceIte]
          rw [ih (t - D) (by omega) (by omega)]
          unfold edge
          by_cases h4 : t - D < tb
          · simp only [h4, ↓reduceIte]; exact H.win_v
          · simp only [h4, ↓reduceIte, show t - D < tb + wb by omega, ↓reduceIte]; exact H.win_x
      · simp only [h2, ↓reduceIte, hts, ↓reduceIte]; exact H.follow _

/-- **Strict race: follow and hold, no hazard.** If the release pin starts
moving no earlier than the tick the feedback pin carries `n`
(`tb + D + wb ≤ s`), the output is exactly one clean edge. -/
theorem clean (L : Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hrace : tb + D + wb ≤ s) :
    Spec v n tb wb G := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    by_cases hts : t < s
    · exact prefix_ok L H hD t hts
    · rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_PURE]
      have hq : G (t - D) = K3.ofBool n := by
        rw [ih (t - D) (by omega)]
        simp only [edge, show ¬ t - D < tb by omega, show ¬ t - D < tb + wb by omega, ↓reduceIte]
      simp only [phase, edge, show ¬ t < D by omega, show ¬ t < tb by omega,
        show ¬ t < tb + wb by omega, hts, ↓reduceIte, hq]
      by_cases h5 : t < s + wa
      · simp only [h5, ↓reduceIte]; exact H.holdX
      · simp only [h5, ↓reduceIte]; exact H.hold1

/-- **Race not strict: hazard.** If the release pin starts moving before the
feedback pin has settled (`s < tb + D + wb`), the root at the release tick
`s` is not `n`, although the spec (and the inputs, which agreed since
`tb + wb ≤ s`) require `n`: it is `x`, or (when the release pin's select is
instantaneous and the feedback has not started) a binary glitch to `v`. -/
theorem hazard (L : Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hord : tb + wb ≤ s)
    (hrace : s < tb + D + wb) :
    G s ≠ K3.ofBool n ∧ edge v n tb wb s = K3.ofBool n := by
  have hspec : edge v n tb wb s = K3.ofBool n := by
    simp only [edge, show ¬ s < tb by omega, show ¬ s < tb + wb by omega, ↓reduceIte]
  refine ⟨?_, hspec⟩
  rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_PURE]
  simp only [phase, show ¬ s < tb by omega, show ¬ s < tb + wb by omega,
    Nat.lt_irrefl, ↓reduceIte]
  -- the feedback pin at s
  have hq : (if s < D then K3.ofBool v else G (s - D)) = K3.ofBool v ∨
      (if s < D then K3.ofBool v else G (s - D)) = K3.x := by
    by_cases h : s < D
    · simp only [h, ↓reduceIte]; simp
    · simp only [h, ↓reduceIte]
      rw [prefix_ok L H hD (s - D) (by omega)]
      unfold edge
      by_cases h4 : s - D < tb
      · simp only [h4, ↓reduceIte]; simp
      · simp only [h4, ↓reduceIte, show s - D < tb + wb by omega, ↓reduceIte]; simp
  have hn : K3.ofBool v ≠ K3.ofBool n := fun h => H.ne (ofBool_inj h)
  by_cases h5 : s < s + wa
  · simp only [h5, ↓reduceIte]
    rcases hq with h | h <;> rw [h]
    · rw [H.hzXv]; exact (ofBool_ne_x n).symm
    · rw [H.hzXX]; exact (ofBool_ne_x n).symm
  · simp only [h5, ↓reduceIte]
    rcases hq with h | h <;> rw [h]
    · rw [H.hz1v]; exact hn
    · rw [H.hz1X]; exact (ofBool_ne_x n).symm

/-- **Exactness.** Under H_ACK_ORDER, the spec holds iff the race is met
with the feedback pin's X window fully before the release pin's. -/
theorem clean_iff (L : Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    Spec v n tb wb G ↔ tb + D + wb ≤ s := by
  constructor
  · intro hs
    apply Classical.byContradiction; intro hlt
    have ⟨h1, h2⟩ := hazard L H hD hord (by omega)
    exact h1 (by rw [hs s]; exact h2)
  · exact clean L H hD

end generic

/-! ## Non-vacuity: every parameter choice has a behaviour (a simulator) -/

section sim
variable {ι : Type} (F : ι → K3 → K3) (inp : Nat → ι) (v : Bool) (d : Nat)

/-- The root of the loop with pure feedback delay `d + 1`. -/
def simG : Nat → K3
  | t => F (inp t) (if h : t < d + 1 then K3.ofBool v else simG (t - (d + 1)))
termination_by t => t
decreasing_by omega

def simQ (t : Nat) : K3 := if t < d + 1 then K3.ofBool v else simG F inp v d (t - (d + 1))

theorem sim_loop {I0 IX I1 RX R1 : ι} {tb wb s wa : Nat}
    (hi : ∀ t, inp t = phase I0 IX I1 RX R1 tb wb s wa t) :
    Loop F I0 IX I1 RX R1 v tb wb s wa (d + 1) inp (simQ F inp v d) (simG F inp v d) where
  H_TREE := by
    intro t; rw [simG]; unfold simQ
    by_cases h : t < d + 1 <;> simp [h]
  H_FB_PURE := fun _ => rfl
  H_IN_PHASES := hi

end sim

theorem loop_exists {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : Bool)
    (tb wb s wa D : Nat) (hD : 1 ≤ D) :
    ∃ i qp G, Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  exact ⟨_, _, _, sim_loop F (phase I0 IX I1 RX R1 tb wb s wa) v d (fun _ => rfl)⟩

/-! ## Box form and B's binary-edge form -/

/-- Universally safe over a delay box: for every `D ∈ [Dlo, Dhi]`, every
release start `s ≥ slo` and every behaviour. -/
def SafeBox {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v n : Bool)
    (tb wb wa Dlo Dhi slo : Nat) : Prop :=
  ∀ D s, Dlo ≤ D → D ≤ Dhi → slo ≤ s →
    ∀ i qp G, Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G → Spec v n tb wb G

theorem box_iff {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {tb wb wa Dlo Dhi slo : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ Dhi) (hord : tb + wb ≤ slo) :
    SafeBox F I0 IX I1 RX R1 v n tb wb wa Dlo Dhi slo ↔ tb + Dhi + wb ≤ slo := by
  constructor
  · intro hs
    obtain ⟨i, qp, G, L⟩ := loop_exists F I0 IX I1 RX R1 v tb wb slo wa Dhi (by omega)
    exact (clean_iff L H (by omega) hord).1 (hs Dhi slo hbox (Nat.le_refl _) (Nat.le_refl _) i qp G L)
  · intro hr D s h1 h2 h3 i qp G L
    exact clean L H (by omega) (by omega)

/-- **B's race, per-pin Kleene form.** `c = tb + wb` is B's phase start (the
follow pin's binary edge, both inputs agree). The loop delay `D = dl + dw`
ranges over `[Dlo, dlmax + dwmax]`. B's `H_ACK` with latency `E` lets the
release pin's BINARY edge `s + wa` be as early as `c + dlmin + E`, i.e. its
select starts moving at `s = c + dlmin + E - wa`. Universally safe iff
`dlmax + dwmax + wa ≤ dlmin + E`. (`wa ≤ dlmin + E`: the earliest release
cannot start before the phase.) -/
theorem env_latency_iff {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {tb wb wa Dlo dlmin dlmax dwmax E : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (hwa : wa ≤ dlmin + E) :
    SafeBox F I0 IX I1 RX R1 v n tb wb wa Dlo (dlmax + dwmax) (tb + wb + dlmin + E - wa) ↔
      dlmax + dwmax + wa ≤ dlmin + E := by
  rw [box_iff H hlo hbox (by omega)]; omega

/-- At `wa = 1` (one tick of X on the release pin's select): B's
`H_ENV_LATENCY` must be strict. -/
theorem env_latency_strict {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {tb wb Dlo dlmin dlmax dwmax E : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (hE : 1 ≤ dlmin + E) :
    SafeBox F I0 IX I1 RX R1 v n tb wb 1 Dlo (dlmax + dwmax) (tb + wb + dlmin + E - 1) ↔
      dlmax + dwmax < dlmin + E := by
  rw [env_latency_iff H hlo hbox hE]; omega

/-- At `wa = 0` (instantaneous select: the atomic/binary reading) B's `≤`
is exact. -/
theorem env_latency_atomic {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {tb wb Dlo dlmin dlmax dwmax E : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) :
    SafeBox F I0 IX I1 RX R1 v n tb wb 0 Dlo (dlmax + dwmax) (tb + wb + dlmin + E - 0) ↔
      dlmax + dwmax ≤ dlmin + E := by
  rw [env_latency_iff H hlo hbox (Nat.zero_le _)]; omega

/-! ## The real cells -/

/-- bd_c2 (INIT 64'h00E8_00E8_00E8_00E8), pins I0 = a, I1 = b, I2 = q, I3 =
rst held 0, I4 = I5 = 0 (`CElemFn.c2K`). -/
def c2F (ab : K3 × K3) (q : K3) : K3 := c2K ab.1 ab.2 q K3.f

/-- bd_c2n (INIT 64'h00B2_00B2_00B2_00B2), same pin map. -/
def c2nF (ab : K3 × K3) (q : K3) : K3 := c2nK ab.1 ab.2 q K3.f

instance : DecidableEq (K3 × K3) := inferInstance

def kb (b : Bool) : K3 := K3.ofBool b

/-- Rising/falling (`v`), follow pin a or b, release pin a or b: all eight
four-phase cycles of bd_c2. `u` = the value both inputs reach (`n = u`),
the follow pin moves `!u → u`, the release pin moves `u → !u`. -/
def c2Cycle (v : Bool) (followA releaseA : Bool) :
    (K3 × K3) × (K3 × K3) × (K3 × K3) × (K3 × K3) × (K3 × K3) :=
  let u := !v
  let pr (x y : K3) : K3 × K3 := (x, y)
  -- the static pin holds u from the start; the follow pin goes !u -> u
  let I0 := if followA then pr (kb v) (kb u) else pr (kb u) (kb v)
  let IX := if followA then pr K3.x (kb u) else pr (kb u) K3.x
  let I1 := pr (kb u) (kb u)
  let RX := if releaseA then pr K3.x (kb u) else pr (kb u) K3.x
  let R1 := if releaseA then pr (kb v) (kb u) else pr (kb u) (kb v)
  (I0, IX, I1, RX, R1)

theorem c2_facts_dec (v fA rA : Bool) :
    let c := c2Cycle v fA rA
    v ≠ !v ∧
    c2F c.1 (kb v) = kb v ∧ c2F c.2.1 (kb v) = K3.x ∧ c2F c.2.1 K3.x = K3.x ∧
    c2F c.2.2.1 K3.f = kb (!v) ∧ c2F c.2.2.1 K3.t = kb (!v) ∧ c2F c.2.2.1 K3.x = kb (!v) ∧
    c2F c.2.2.2.1 (kb (!v)) = kb (!v) ∧ c2F c.2.2.2.2 (kb (!v)) = kb (!v) ∧
    c2F c.2.2.2.1 K3.x = K3.x ∧ c2F c.2.2.2.2 K3.x = K3.x ∧
    c2F c.2.2.2.1 (kb v) = K3.x ∧ c2F c.2.2.2.2 (kb v) = kb v := by
  cases v <;> cases fA <;> cases rA <;> decide

theorem facts_of {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (h0 : v ≠ n) (h1 : F I0 (kb v) = kb v) (h2 : F IX (kb v) = K3.x) (h3 : F IX K3.x = K3.x)
    (h4f : F I1 K3.f = kb n) (h4t : F I1 K3.t = kb n) (h4x : F I1 K3.x = kb n)
    (h5 : F RX (kb n) = kb n) (h6 : F R1 (kb n) = kb n) (h7 : F RX K3.x = K3.x)
    (h8 : F R1 K3.x = K3.x) (h9 : F RX (kb v) = K3.x) (h10 : F R1 (kb v) = kb v) :
    Facts F I0 IX I1 RX R1 v n :=
  { ne := h0, init := h1, win_v := h2, win_x := h3,
    follow := fun k => by cases k; exact h4f; exact h4t; exact h4x,
    holdX := h5, hold1 := h6, hzXX := h7, hz1X := h8, hzXv := h9, hz1v := h10 }

/-- **All eight bd_c2 cycles satisfy the race facts** on the real INIT. So
`clean`, `hazard`, `clean_iff`, `box_iff`, `env_latency_strict` hold for
each of them. -/
theorem c2_all (v fA rA : Bool) :
    let c := c2Cycle v fA rA
    Facts c2F c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 v (!v) := by
  have h := c2_facts_dec v fA rA
  simp only at h ⊢
  obtain ⟨h0, h1, h2, h3, h4f, h4t, h4x, h5, h6, h7, h8, h9, h10⟩ := h
  exact facts_of h0 h1 h2 h3 h4f h4t h4x h5 h6 h7 h8 h9 h10

/-- C-8g's transition on bd_c2n: I0 = a = 1 throughout, b falls 1 → 0
(C(1, ~0) = 1: the cell must rise, v = 0, n = 1), then b rises back
(release, C(1, ~1) holds). At equality the vector goes (1,0,0) → (1,1,1)
across C-8g's hazard (1,1,0) ↦ 0. -/
theorem c2n_c8g :
    Facts c2nF (K3.t, K3.t) (K3.t, K3.x) (K3.t, K3.f) (K3.t, K3.x) (K3.t, K3.t) false true :=
  facts_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## The boundary case on the real INIT: concrete traces -/

/-- bd_c2, rising, follow pin b, release pin a (a falls after q rose),
`tb = 0`, `wb = wa = 1`, `D = 420` (`dl = 120 + dw = 300`, CElemTiming's
instance). B's `≤` with equality: release select starts at `s = D = 420`,
its binary edge at 421 = `c + D` (c = 1). The root reads `n = 1` at 419 and
`x` at 420: a hazard on the output. -/
theorem boundary_x :
    let c := c2Cycle false false true
    let i := phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 420 1
    simG c2F i false 419 419 = K3.t ∧ simG c2F i false 419 420 = K3.x := by
  intro c i
  have L := sim_loop c2F i false 419 (I0 := c.1) (IX := c.2.1) (I1 := c.2.2.1)
    (RX := c.2.2.2.1) (R1 := c.2.2.2.2) (tb := 0) (wb := 1) (s := 420) (wa := 1) (fun _ => rfl)
  have H := c2_all false false true
  refine ⟨?_, ?_⟩
  · rw [prefix_ok L H (by omega) 419 (by omega)]; decide
  · -- the hazard tick: release select X, feedback select X
    rw [(sim_loop c2F i false 419 (fun _ => rfl)).H_TREE]
    unfold simQ
    simp only [show ¬ (420 < 419 + 1) by omega, ↓reduceIte]
    rw [prefix_ok L H (by omega) (420 - (419 + 1)) (by omega)]
    decide

/-- The same equality on the strict side: release one tick later
(`s = 421`) is clean, forever. -/
theorem strict_clean :
    let c := c2Cycle false false true
    Spec false true 0 1 (simG c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 421 1) false 419) :=
  clean (sim_loop _ _ _ _ (fun _ => rfl)) (c2_all false false true) (by omega) (by omega)

/-- bd_c2n, C-8g's transition, equality: the root is `x` at the release
tick (it should be 1). -/
theorem boundary_x_c2n :
    simG c2nF (phase (K3.t, K3.t) (K3.t, K3.x) (K3.t, K3.f) (K3.t, K3.x) (K3.t, K3.t) 0 1 420 1)
      false 419 420 = K3.x := by
  have L := sim_loop c2nF (phase (K3.t, K3.t) (K3.t, K3.x) (K3.t, K3.f) (K3.t, K3.x) (K3.t, K3.t)
    0 1 420 1) false 419 (I0 := (K3.t, K3.t)) (IX := (K3.t, K3.x)) (I1 := (K3.t, K3.f))
    (RX := (K3.t, K3.x)) (R1 := (K3.t, K3.t)) (tb := 0) (wb := 1) (s := 420) (wa := 1) (fun _ => rfl)
  rw [L.H_TREE]
  unfold simQ
  simp only [show ¬ (420 < 419 + 1) by omega, ↓reduceIte]
  rw [prefix_ok L c2n_c8g (by omega) (420 - (419 + 1)) (by omega)]
  decide

/-- Binary order (release select instantaneous, `wa = 0`, and the release
lands before the feedback moves): a full glitch back to 0 on bd_c2. -/
theorem binary_glitch :
    let c := c2Cycle false false true
    simG c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 300 0) false 419 300 = K3.f := by
  intro c
  have L := sim_loop c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 300 0) false 419
    (I0 := c.1) (IX := c.2.1) (I1 := c.2.2.1)
    (RX := c.2.2.2.1) (R1 := c.2.2.2.2) (tb := 0) (wb := 1) (s := 300) (wa := 0) (fun _ => rfl)
  rw [L.H_TREE]
  unfold simQ
  simp only [show (300 < 419 + 1) by omega, ↓reduceIte]
  decide

/-- With `wa = 0` equality is safe: release binary edge = feedback settle
tick (`s = tb + D + wb = 421`), clean. -/
theorem atomic_equality_clean :
    let c := c2Cycle false false true
    Spec false true 0 1 (simG c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 421 0) false 419) :=
  clean (sim_loop _ _ _ _ (fun _ => rfl)) (c2_all false false true) (by omega) (by omega)

/-! ## The same race in the latch: bd_latch odd bit (setup against the enable fall)

`bd_latch` odd bit: `LUT6 #(INIT 64'hB8B8_..._B8B8)`, pins I0 = d, I1 = en,
I2 = q (own feedback), I3..I5 = 0 (`Latch.ODD`). The follow phase is the
data edge `v -> n` while `en = 1`; the release is the enable fall. The race
facts hold for both values, so `clean_iff`/`env_latency_iff` apply: the
latch's own loop must settle before the enable's select starts moving. -/

def latF (de : K3 × K3) (q : K3) : K3 := lutK Formal.Cells.Latch.ODD [de.1, de.2, q, K3.f, K3.f, K3.f]

theorem latch_facts (v : Bool) :
    Facts latF (kb v, K3.t) (K3.x, K3.t) (kb (!v), K3.t) (kb (!v), K3.x) (kb (!v), K3.f) v (!v) := by
  cases v
  · exact facts_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact facts_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end CElemStrict
end Formal.Cells
