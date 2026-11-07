import Formal.Timing.ChainSettleExe
import Formal.Net.CellBindOps

/-!
# C-10o2 (3/3): composing the bridge with O4's `GenChain` (H_CHAIN_SETTLED)

* **`genChain_iff`**: O4's `CellBind.Ops.GenChain i o` (∃ a per-gate SI network of
  generated buffer/AND/OR stages from `i` to `o` whose input changes only when EVERY node
  shows it) is EQUIVALENT to three statements about the two end traces only:
  (lumped) `o` moves only to `i`'s previous value; (wait) `i` changes only when `o = i`;
  (init) `o 0 = i 0`. (`→`: O4's `chain_lumped` + the `Settled` clause at the last node;
  `←`: a one-stage buffer network.) So H_CHAIN_SETTLED as O4 USES it constrains the chain's
  ends, not its internal stages: the bridge has to deliver exactly those three facts, and it
  must deliver them on the chain's real input/tail traces.
* **Time base** (how SI ticks relate to the timed run): the Ops traces `i`, `o` of the
  chain ARE the timed node traces sampled every tick, 1 tick = 1 ps (the same convention as
  8d's `Bridge`, 8x's `run_settles` and 10o's `Semantics`): `i = sig 0` (the side-tap source,
  = the environment's pulse), `o = sig z` (the tail). No resampling.
* **`genChain_of_forced`** (AND chains: FASTFALL / gated) and **`genChain_of_forced_or`**
  (OR chains: FASTRISE `uack`, by negation): under H_INERTIAL (every arc an 8d `Inertial`
  channel, `lo ≥ 1`), H_AND / H_OR, H_PULSE (`F, T ≥ 1`), H_QUIET0, and the two FORCED
  conditions `SettledPt` (10o's `Settled` at the input's return) and `DAll` (D), the run's
  input/tail traces satisfy O4's `GenChain`.
* **`genChain_of_check`**: the same with the conditions replaced by the checker's verdict
  (`ChainSettleExe.verdict r = v`, `v.bridge = true`), so a decided row gives O4's
  hypothesis for that chain instance in every inertial run.

Core Lean only. No sorry/axiom/native_decide.
-/

namespace Formal.Timing.ChainSettleBridgeO4
open Formal.Net Formal.Timing Formal.Timing.ChainSettle Formal.Timing.ChainSettleBridge
open Formal.Timing.ChainSettleExe
open Formal.Net.CellBind Formal.Net.CellBind.Ops Formal.Net.CellBind.Chain
open Formal.Net.Bridge (Inertial)

/-- **O4's H_CHAIN_SETTLED is a statement about the chain's two ends.** -/
theorem genChain_iff (i o : Trace) :
    GenChain i o ↔
      (∀ t, o (t + 1) ≠ o t → o (t + 1) = i t) ∧
      (∀ t, i (t + 1) ≠ i t → o t = i t) ∧ o 0 = i 0 := by
  constructor
  · intro h
    refine ⟨chain_lumped h, ?_, ?_⟩
    · obtain ⟨n, st, x, hn, h0, hN, _, _, hS, _⟩ := h
      intro t ht
      rw [← h0] at ht ⊢; rw [← hN]
      exact hS t ht n (Nat.le_refl _)
    · obtain ⟨n, st, x, hn, h0, hN, _, _, _, hI⟩ := h
      rw [← hN, ← h0]; exact hI n (Nat.le_refl _)
  · rintro ⟨hl, hw, h0⟩
    refine ⟨1, fun _ => Stage.buf 0, fun j => if j = 0 then i else o, Nat.le_refl _, rfl, rfl,
      fun k _ _ => Nat.zero_le _, ?_, ?_, ?_⟩
    · intro k h1 hk t hm
      have hk1 : k = 1 := by omega
      subst hk1
      simp only [Stage.G, (sym_gate _).1, ite_true] at hm ⊢
      simp only [show (1 : Nat) ≠ 0 by decide, ite_false] at hm ⊢
      exact hl t hm
    · intro t ht j hj
      by_cases hj0 : j = 0
      · subst hj0; rfl
      · have : j = 1 := by omega
        subst this
        simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true] at ht ⊢
        exact hw t ht
    · intro j hj
      by_cases hj0 : j = 0
      · subst hj0; rfl
      · have : j = 1 := by omega
        subst this
        simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
        exact h0

/-- `GenChain` is invariant under negating both ends. -/
theorem genChain_not {i o : Trace} (h : GenChain i o) :
    GenChain (fun t => !i t) (fun t => !o t) := by
  rw [genChain_iff] at h ⊢
  obtain ⟨hl, hw, h0⟩ := h
  refine ⟨fun t ht => ?_, fun t ht => ?_, by simp [h0]⟩
  · have : o (t + 1) ≠ o t := fun e => ht (by simp [e])
    simp [hl t this]
  · have : i (t + 1) ≠ i t := fun e => ht (by simp [e])
    simp [hw t this]

variable {net : Netlist} {F T : Nat} {sig : Nat → Trace}

/-- **The bridge, AND chains (FASTFALL / gated).** -/
theorem genChain_of_forced (hwf : net.WF) (r : InRun net (pulse F T) sig) (hF : 1 ≤ F)
    (hT : 1 ≤ T) (hq : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → r.pin k 0 = true)
    {z : Nat} (hz : z ≠ 0) (hS : SettledPt net F T z) (hD : DAll net F T) :
    GenChain (sig 0) (sig z) := by
  have e : sig 0 = pulse F T := funext r.src
  rw [e, genChain_iff]
  exact lumped_of_forced hwf r hF hT hq hz hS hD

/-! ## OR chains (FASTRISE `uack`) by negation -/

theorem inertial_not {lo hi : Nat} {e o : Trace} (h : Inertial lo hi e o) :
    Inertial lo hi (fun t => !e t) (fun t => !o t) where
  lo_pos := h.lo_pos
  cause := by
    intro t hc
    have hc' : changes o t := by
      intro he; apply hc; show (!o t) = (!o (t + 1)); rw [he]
    obtain ⟨h1, h2⟩ := h.cause t hc'
    exact ⟨h1, fun u a b => by show (!e u) = (!o (t + 1)); rw [h2 u a b]⟩
  settle := by
    intro t ht hs
    have hs' : stableOn e (t - hi) t := by
      intro w a b
      have := hs w a b
      simp only at this
      cases h1 : e w <;> cases h2 : e (t - hi) <;> simp_all
    show (!o t) = (!e t); rw [h.settle t ht hs']

/-- A run of an OR network with inertial arcs. -/
structure OrInRun (net : Netlist) (inp : Trace) (sig : Nat → Trace) where
  pin : Nat → Trace
  src : ∀ t, sig 0 t = inp t
  inert : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → Inertial a.lo a.hi (sig a.src) (pin k)
  node : ∀ v, v ≠ 0 → ∀ t,
    (sig v t = false ↔ ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = v → pin k t = false)

/-- Negated, an inertial OR run is an inertial AND run of the negated input. -/
def OrInRun.neg {inp : Trace} (r : OrInRun net inp sig) :
    InRun net (fun t => !inp t) (fun v t => !sig v t) where
  pin := fun k t => !r.pin k t
  src := by intro t; simp only [r.src]
  inert := fun k a hk => inertial_not (r.inert k a hk)
  node := by
    intro v hv t
    have := r.node v hv t
    constructor
    · intro h k a hk hd
      have h' : sig v t = false := by simpa using h
      simpa using this.1 h' k a hk hd
    · intro h
      have h' : sig v t = false := this.2 (fun k a hk hd => by simpa using h k a hk hd)
      simp [h']

/-- **The bridge, OR chains (FASTRISE `uack`).** The OR chain's input is the negated pulse
(0 before `F`, 1 on `[F, F + T)`, 0 after); its forced-HIGH sets are 10o's `Lc` of the
pulse (`or_high_iff`), which is what `SettledPt` / `DAll` (and chainck's FR rows) compute. -/
theorem genChain_of_forced_or (hwf : net.WF) (r : OrInRun net (fun t => !pulse F T t) sig)
    (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hq : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → r.pin k 0 = false)
    {z : Nat} (hz : z ≠ 0) (hS : SettledPt net F T z) (hD : DAll net F T) :
    GenChain (sig 0) (sig z) := by
  let rn : InRun net (pulse F T) (fun v t => !sig v t) :=
    { pin := fun k t => !r.pin k t
      src := fun t => by simp only [r.src, Bool.not_not]
      inert := r.neg.inert
      node := r.neg.node }
  have := genChain_of_forced hwf rn hF hT (fun k a hk => by simp [rn, hq k a hk]) hz hS hD
  have := genChain_not this
  simpa using this

/-! ## From a decided row -/

/-- **A decided bridge row gives O4's H_CHAIN_SETTLED for that chain in every inertial
quiet run (AND chains).** -/
theorem genChain_of_check {r : Row} {v : Verdict} (hv : verdict r = v) (hb : v.bridge = true) :
    ∀ sig (run : InRun r.net (pulse r.F r.T) sig),
      (∀ (k : Nat) (a : Arc), r.net.arcs[k]? = some a → run.pin k 0 = true) →
      GenChain (pulse r.F r.T) (sig r.z) := by
  intro sig run hq
  obtain ⟨hwf, hT, hF, hz, hS, hD⟩ := bridge_sound hv hb
  have := genChain_of_forced hwf run hF hT hq hz hS hD
  rwa [show sig 0 = pulse r.F r.T from funext run.src] at this

/-- The same for OR chains (FASTRISE `uack` rows). -/
theorem genChain_of_check_or {r : Row} {v : Verdict} (hv : verdict r = v) (hb : v.bridge = true) :
    ∀ sig (run : OrInRun r.net (fun t => !pulse r.F r.T t) sig),
      (∀ (k : Nat) (a : Arc), r.net.arcs[k]? = some a → run.pin k 0 = false) →
      GenChain (fun t => !pulse r.F r.T t) (sig r.z) := by
  intro sig run hq
  obtain ⟨hwf, hT, hF, hz, hS, hD⟩ := bridge_sound hv hb
  have := genChain_of_forced_or hwf run hF hT hq hz hS hD
  rwa [show sig 0 = (fun t => !pulse r.F r.T t) from funext run.src] at this

end Formal.Timing.ChainSettleBridgeO4
