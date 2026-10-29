import Formal.Timing.ChainSettleChain
import Formal.Net.Bridge

/-!
# C-10o2 (1/3): the timed side of the bridge 10o `Settled` → O4 H_CHAIN_SETTLED

10o (`ChainSettle`) proves the exact forced-low set `Lc` of a delay chain's tail in the
per-arc `BoundedDelay` model (transport delay, glitches and stale replays allowed). O4
(`CellBind.Ops.GenChain`) needs a per-gate SI statement on the chain's input/tail traces.
`BoundedDelay` is too weak for any SI statement (8d, `BridgeTransport.transport_breaks_si`:
a change may copy a value older than a newer one already delivered, so a tail can bounce
inside its transition window without any input pulse behind it). So the bridge goes through
8d's refinement:

* **H_INERTIAL** (per arc): the pin trace of every arc is 8d's `Bridge.Inertial lo hi`
  copy of its source node (`lo ≥ 1`; a change delivers a value the source held for the
  last `lo` ticks; settles within `hi`). `Inertial ⇒ BoundedDelay` (`inertial_bounded`), so
  every 10o theorem (`cert_sound`, `settled_sound`) applies to these runs (`InRun.toAnd`).
  Consequence used everywhere: a pin moves only to its source's value of the PREVIOUS
  tick (`pin_si`), i.e. at 1 tick = 1 ps every pin is a per-gate SI node.
* **H_AND**, **H_INPUT** as in 10o (`AndRun`), H_PULSE (`pulse F T`, `F ≥ 1`).
* **H_QUIET0**: every pin is 1 at time 0 (the chain is full before the pulse).

Run-level results (no `Lc` yet):

* `phase_nolag`: while the input holds `v` on `[t0, t1)`, if at `t0` no chain pin lags
  AWAY from `v` (its source differs from `v` ⇒ it shows its source), then no pin and no node
  moves away from `v` in `(t0, t1]`. Gives monotone falls during the low phase.
* `phase_rise` (the masking argument, high phase): after the input returns at `t0`, no pin
  and no node rises and then falls again (`RF`) provided (M0) no chain pin is 0 while its
  source is 1 at `t0` (derived from the low phase) and (**D**, per chain pin `q` into a node
  `w` that has another in-arc) `q` is 0 at some `tq ≥ t0` while `w` is 0 on all of
  `[t0, tq)`: the lagging fall of `q` lands while another pin still holds `w` low.
* **`lumped_pulse`**: under H_INERTIAL, H_QUIET0, H_PULSE, D at `t0 = F + T` and
  `z (F+T-1) = 0`, the tail moves only to the input's previous value
  (`z (t+1) ≠ z t → z (t+1) = inp t`), equals the input whenever the input moves, and
  starts equal. That is exactly O4's `GenChain inp z` (`ChainSettleBridgeO4.genChain_iff`).
* **`lumped_of_forced`**: the same with D and `z (F+T-1) = 0` replaced by their FORCED
  forms over `Lc` (10o's calculus): `SettledPt` = `Lc z (F+T-1)` (a point of 10o's
  `Settled` window) and `DForced` (D with "forced low" in place of "is 0"). These are run-
  independent and decided by `ChainSettleExe`'s checker.

What it does NOT cover: multi-pulse inputs (one pulse, as chainck); FASTRISE (OR) chains are
the negation (`ChainSettleBridgeO4`); H_KLEENE_LUT (a LUT = its Boolean function on pins);
whether the fabric's pin delays are inertial (H_INERTIAL is a model choice: 8d's bridge
needs it too).

Core Lean only. No sorry/axiom/native_decide.
-/

namespace Formal.Timing.ChainSettleBridge
open Formal.Net Formal.Timing Formal.Timing.ChainSettle
open Formal.Net.Bridge (Inertial inertial_bounded)

/-- A run of an AND network whose arcs are INERTIAL channels (H_INERTIAL). -/
structure InRun (net : Netlist) (inp : Trace) (sig : Nat → Trace) where
  pin : Nat → Trace
  src : ∀ t, sig 0 t = inp t
  inert : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → Inertial a.lo a.hi (sig a.src) (pin k)
  node : ∀ v, v ≠ 0 → ∀ t,
    (sig v t = true ↔ ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = v → pin k t = true)

variable {net : Netlist} {inp : Trace} {sig : Nat → Trace} {F T : Nat}

/-- An inertial run is a 10o `AndRun` (so every 10o soundness theorem applies). -/
def InRun.toAnd (hwf : net.WF) (r : InRun net inp sig) : AndRun net inp sig where
  pin := r.pin
  src := r.src
  bd := fun k a hk => inertial_bounded (r.inert k a hk) (hwf a (List.mem_of_getElem? hk)).2
  node := r.node

/-- At 1 tick = 1 ps an inertial pin is a per-gate SI node: it moves only to its source's
value at the previous tick. -/
theorem pin_si (r : InRun net inp sig) {k : Nat} {a : Arc} (hk : net.arcs[k]? = some a) :
    ∀ t, r.pin k (t + 1) ≠ r.pin k t → r.pin k (t + 1) = sig a.src t := by
  intro t h
  have hi := r.inert k a hk
  obtain ⟨_, h2⟩ := hi.cause t (fun e => h e.symm)
  have := hi.lo_pos
  exact (h2 t (by omega) (Nat.le_refl _)).symm

/-! ## Discrete-time helpers -/

theorem bnot_ne (v : Bool) : v ≠ !v := by cases v <;> decide

/-- No move away from `v` on `[t0, τ)` and value `v` at `t0` ⇒ value `v` at `τ`. -/
theorem persist {x : Trace} {v : Bool} {t0 : Nat} :
    ∀ τ, t0 ≤ τ → (∀ σ, t0 ≤ σ → σ < τ → ¬ (x σ = v ∧ x (σ + 1) = !v)) → x t0 = v → x τ = v := by
  intro τ
  induction τ with
  | zero => intro h _ h0; rw [show t0 = 0 by omega] at h0; exact h0
  | succ τ ih =>
    intro hle h h0
    by_cases ht : t0 = τ + 1
    · subst ht; exact h0
    · have hτ := ih (by omega) (fun σ a b => h σ a (by omega)) h0
      cases hx : x (τ + 1) with
      | false =>
        cases v with
        | false => rfl
        | true => exact absurd ⟨hτ, hx⟩ (h τ (by omega) (by omega))
      | true =>
        cases v with
        | true => rfl
        | false => exact absurd ⟨hτ, hx⟩ (h τ (by omega) (by omega))

/-- Discrete intermediate value: from `!v` at `t0` to `v` at `τ` there is a step `!v → v`. -/
theorem ivt {x : Trace} {v : Bool} {t0 : Nat} :
    ∀ τ, t0 ≤ τ → x t0 = !v → x τ = v → ∃ σ, t0 ≤ σ ∧ σ < τ ∧ x σ = !v ∧ x (σ + 1) = v := by
  intro τ
  induction τ with
  | zero =>
    intro hle h0 h1
    rw [show t0 = 0 by omega, h1] at h0; exact absurd h0 (bnot_ne v)
  | succ τ ih =>
    intro hle h0 h1
    by_cases ht : t0 = τ + 1
    · subst ht; rw [h1] at h0; exact absurd h0 (bnot_ne v)
    · cases hx : x τ with
      | false =>
        cases v with
        | true => exact ⟨τ, by omega, by omega, hx, h1⟩
        | false =>
          obtain ⟨σ, a, b, c, d⟩ := ih (by omega) h0 hx
          exact ⟨σ, a, by omega, c, d⟩
      | true =>
        cases v with
        | false => exact ⟨τ, by omega, by omega, hx, h1⟩
        | true =>
          obtain ⟨σ, a, b, c, d⟩ := ih (by omega) h0 hx
          exact ⟨σ, a, by omega, c, d⟩

/-- A node that moves away from `v` has a pin that moves away from `v` at the same tick. -/
theorem node_away (r : InRun net inp sig) {w : Nat} (hw : w ≠ 0) {σ : Nat} {v : Bool}
    (h1 : sig w σ = v) (h2 : sig w (σ + 1) = !v) :
    ∃ (k : Nat) (a : Arc), net.arcs[k]? = some a ∧ a.dst = w ∧
      r.pin k σ = v ∧ r.pin k (σ + 1) = !v := by
  cases v with
  | true =>
    have hall := (r.node w hw σ).1 h1
    have hn : ¬ ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = w → r.pin k (σ + 1) = true := by
      intro h; have := (r.node w hw (σ + 1)).2 h; rw [h2] at this; exact Bool.noConfusion this
    apply Classical.byContradiction; intro hne
    apply hn; intro k a hk hd
    have hk1 := hall k a hk hd
    cases hp : r.pin k (σ + 1) with
    | true => rfl
    | false => exact absurd ⟨k, a, hk, hd, hk1, hp⟩ hne
  | false =>
    have hall := (r.node w hw (σ + 1)).1 h2
    have hn : ¬ ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = w → r.pin k σ = true := by
      intro h; have := (r.node w hw σ).2 h; rw [h1] at this; exact Bool.noConfusion this
    apply Classical.byContradiction; intro hne
    apply hn; intro k a hk hd
    have hk1 := hall k a hk hd
    cases hp : r.pin k σ with
    | true => rfl
    | false => exact absurd ⟨k, a, hk, hd, hp, hk1⟩ hne

/-! ## Phase lemma 1: no lag away from the input's value -/

/-- No pin moves away from `v` at `σ + 1`. -/
def PinsStay (r : InRun net inp sig) (v : Bool) (σ : Nat) : Prop :=
  ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → ¬ (r.pin k σ = v ∧ r.pin k (σ + 1) = !v)

theorem nodes_stay (r : InRun net inp sig) {v : Bool} {σ : Nat} (h : PinsStay r v σ) {w : Nat}
    (hw : w ≠ 0) : ¬ (sig w σ = v ∧ sig w (σ + 1) = !v) := by
  rintro ⟨h1, h2⟩
  obtain ⟨k, a, hk, _, hp1, hp2⟩ := node_away r hw h1 h2
  exact h k a hk ⟨hp1, hp2⟩

/-- **Phase lemma (no lag).** -/
theorem phase_nolag (r : InRun net inp sig) {v : Bool} {t0 t1 : Nat}
    (hin : ∀ u, t0 ≤ u → u < t1 → inp u = v)
    (hNL : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.src ≠ 0 →
      sig a.src t0 ≠ v → r.pin k t0 ≠ v) :
    ∀ τ, t0 ≤ τ → τ < t1 → PinsStay r v τ := by
  intro τ
  induction τ using Nat.strongRecOn with
  | ind τ ih =>
    intro h0 h1 k a hk ⟨hp1, hp2⟩
    have hs : sig a.src τ = !v := by
      rw [← pin_si r hk τ (by rw [hp1, hp2]; exact (bnot_ne v).symm), hp2]
    by_cases ha : a.src = 0
    · rw [ha, r.src, hin τ h0 h1] at hs; exact bnot_ne v hs
    · have stay : ∀ σ, t0 ≤ σ → σ < τ → ¬ (sig a.src σ = v ∧ sig a.src (σ + 1) = !v) :=
        fun σ a1 a2 => nodes_stay r (ih σ a2 a1 (by omega)) ha
      have hs0 : sig a.src t0 ≠ v := by
        intro he
        have := persist τ h0 stay he
        rw [hs] at this; exact bnot_ne v this.symm
      have hp0 : r.pin k t0 = !v := by
        have := hNL k a hk ha hs0; cases v <;> cases hq : r.pin k t0 <;> simp_all
      obtain ⟨σ, a1, a2, a3, a4⟩ := ivt τ h0 hp0 hp1
      have hsσ : sig a.src σ = v := by
        rw [← pin_si r hk σ (by rw [a3, a4]; exact bnot_ne v), a4]
      have := persist (t0 := σ) τ (by omega) (fun σ' b1 b2 => stay σ' (by omega) b2) hsσ
      rw [hs] at this; exact bnot_ne v this.symm

/-! ## Phase lemma 2: masking (high phase) -/

/-- Rise at `σ + 1` and fall at `τ + 1`, with `t0 ≤ σ < τ`. -/
def RF (x : Trace) (t0 τ : Nat) : Prop :=
  ∃ σ, t0 ≤ σ ∧ σ < τ ∧ x σ = false ∧ x (σ + 1) = true ∧ x τ = true ∧ x (τ + 1) = false

/-- **D** (run level) for chain pin `k` (arc `a`), from `t0`. -/
def DRun (r : InRun net inp sig) (t0 k : Nat) (a : Arc) : Prop :=
  ∃ tq, t0 ≤ tq ∧ r.pin k tq = false ∧ ∀ τ, t0 ≤ τ → τ < tq → sig a.dst τ = false

/-- `w` has an in-arc other than `k`. -/
def OtherIn (net : Netlist) (k w : Nat) : Prop :=
  ∃ (k' : Nat) (a' : Arc), net.arcs[k']? = some a' ∧ a'.dst = w ∧ k' ≠ k

/-- A trace with no rise in `[t0, τ)` that is 1 at `τ` was 1 on all of `[t0, τ]`. -/
theorem norise_one {x : Trace} {t0 τ : Nat} (_hle : t0 ≤ τ)
    (hn : ¬ ∃ ρ, t0 ≤ ρ ∧ ρ < τ ∧ x ρ = false ∧ x (ρ + 1) = true) (h1 : x τ = true) :
    ∀ u, t0 ≤ u → u ≤ τ → x u = true := by
  intro u a b
  cases hu : x u with
  | true => rfl
  | false =>
    obtain ⟨ρ, c, d, e, f⟩ := ivt (x := x) (v := true) (t0 := u) τ b hu h1
    exact absurd ⟨ρ, by omega, d, e, f⟩ hn

/-- **Phase lemma (masking).** -/
theorem phase_rise (r : InRun net inp sig) {t0 t1 : Nat}
    (hin : ∀ u, t0 ≤ u → u < t1 → inp u = true)
    (hM0 : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.src ≠ 0 →
      r.pin k t0 = false → sig a.src t0 = false)
    (hD : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.src ≠ 0 → OtherIn net k a.dst →
      DRun r t0 k a) :
    ∀ τ, t0 ≤ τ → τ < t1 →
      (∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → ¬ RF (r.pin k) t0 τ) ∧
      (∀ w, w ≠ 0 → ¬ RF (sig w) t0 τ) := by
  intro τ
  induction τ using Nat.strongRecOn with
  | ind τ ih =>
    intro h0 h1
    -- pins first
    have hpins : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → ¬ RF (r.pin k) t0 τ := by
      rintro k a hk ⟨σ, a1, a2, p1, p2, p3, p4⟩
      have sσ : sig a.src σ = true := by rw [← pin_si r hk σ (by rw [p1, p2]; decide), p2]
      have sτ : sig a.src τ = false := by rw [← pin_si r hk τ (by rw [p3, p4]; decide), p4]
      by_cases ha : a.src = 0
      · rw [ha, r.src, hin τ h0 h1] at sτ; exact Bool.noConfusion sτ
      · by_cases hr : ∃ ρ, t0 ≤ ρ ∧ ρ < σ ∧ sig a.src ρ = false ∧ sig a.src (ρ + 1) = true
        · obtain ⟨ρ, b1, b2, b3, b4⟩ := hr
          obtain ⟨ρ', c1, c2, c3, c4⟩ :=
            ivt (x := sig a.src) (v := false) (t0 := σ) τ (by omega) sσ sτ
          exact (ih ρ' c2 (by omega) (by omega)).2 a.src ha
            ⟨ρ, b1, by omega, b3, b4, c3, c4⟩
        · have hsrc := norise_one (by omega) hr sσ
          have hp0 : r.pin k t0 = false := by
            cases hq : r.pin k t0 with
            | false => rfl
            | true =>
              obtain ⟨u, c1, c2, c3, c4⟩ :=
                ivt (x := r.pin k) (v := false) (t0 := t0) σ a1 hq p1
              have := pin_si r hk u (by rw [c3, c4]; decide)
              rw [c4, hsrc u c1 (by omega)] at this; exact Bool.noConfusion this
          have := hM0 k a hk ha hp0
          rw [hsrc t0 (Nat.le_refl _) a1] at this; exact Bool.noConfusion this
    refine ⟨hpins, ?_⟩
    rintro w hw ⟨σ, a1, a2, w1, w2, w3, w4⟩
    obtain ⟨k, a, hk, hd, q1, q2⟩ := node_away r hw (v := true) w3 w4
    have qσ : r.pin k (σ + 1) = true := (r.node w hw (σ + 1)).1 w2 k a hk hd
    by_cases hr : ∃ ρ, t0 ≤ ρ ∧ ρ < τ ∧ r.pin k ρ = false ∧ r.pin k (ρ + 1) = true
    · obtain ⟨ρ, b1, b2, b3, b4⟩ := hr
      exact hpins k a hk ⟨ρ, b1, b2, b3, b4, q1, q2⟩
    · have hq1 := norise_one (by omega) hr q1
      by_cases ha : a.src = 0
      · have := pin_si r hk τ (by rw [q1, q2]; decide)
        rw [q2, ha, r.src, hin τ h0 h1] at this; exact Bool.noConfusion this
      · by_cases ho : OtherIn net k w
        · obtain ⟨tq, c1, c2, c3⟩ := hD k a hk ha (hd ▸ ho)
          have htq : τ < tq := by
            apply Classical.byContradiction; intro hc
            rw [hq1 tq c1 (by omega)] at c2; exact Bool.noConfusion c2
          have := c3 (σ + 1) (by omega) (by omega)
          rw [hd] at this; rw [this] at w2; exact Bool.noConfusion w2
        · -- single in-arc: the node IS the pin
          have hsame : ∀ u, sig w u = r.pin k u := by
            intro u
            cases hp : r.pin k u with
            | true =>
              exact (r.node w hw u).2 (fun k' a' hk' hd' => by
                by_cases e : k' = k
                · subst e; exact hp
                · exact absurd ⟨k', a', hk', hd', e⟩ ho)
            | false =>
              cases hs : sig w u with
              | false => rfl
              | true => have := (r.node w hw u).1 hs k a hk hd; rw [hp] at this; exact this.symm
          rw [hsame σ, hq1 σ a1 (by omega)] at w1; exact Bool.noConfusion w1

/-! ## The pulse -/

theorem pulse_val {F T t : Nat} : pulse F T t = !(decide (F ≤ t ∧ t < F + T)) := rfl

theorem pulse_chg {F T t : Nat} (h : pulse F T (t + 1) ≠ pulse F T t) :
    t + 1 = F ∨ t + 1 = F + T := by
  simp only [pulse_val] at h
  by_cases h1 : F ≤ t + 1 <;> by_cases h2 : t + 1 < F + T <;> by_cases h3 : F ≤ t <;>
    by_cases h4 : t < F + T <;> simp_all <;> omega

/-- **The bridge, run level.** Under H_INERTIAL, H_QUIET0, H_PULSE (`F ≥ 1`, `T ≥ 1`),
D at the input's return `F + T`, and the tail low just before the return, the tail is a
lumped SI copy of the input that the input waits for. -/
theorem lumped_pulse (r : InRun net (pulse F T) sig) (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hq : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → r.pin k 0 = true)
    {z : Nat} (hz : z ≠ 0) (hS1 : sig z (F + T - 1) = false)
    (hD : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.src ≠ 0 → OtherIn net k a.dst →
      DRun r (F + T) k a) :
    (∀ t, sig z (t + 1) ≠ sig z t → sig z (t + 1) = pulse F T t) ∧
    (∀ t, pulse F T (t + 1) ≠ pulse F T t → sig z t = pulse F T t) ∧
    sig z 0 = pulse F T 0 := by
  have inp_hi0 : ∀ u, 0 ≤ u → u < F → pulse F T u = true := by
    intro u _ h; simp only [pulse_val]; simp; omega
  have inp_lo : ∀ u, F ≤ u → u < F + T → pulse F T u = false := by
    intro u h1 h2; simp only [pulse_val]; simp; omega
  have inp_hi : ∀ u, F + T ≤ u → pulse F T u = true := by
    intro u h; simp only [pulse_val]; simp; omega
  have nodes0 : ∀ w, sig w 0 = true := by
    intro w
    by_cases hw : w = 0
    · subst hw; rw [r.src]; exact inp_hi0 0 (Nat.le_refl _) (by omega)
    · exact (r.node w hw 0).2 (fun k a hk _ => hq k a hk)
  -- phase [0, F): everything stays 1
  have P0 := phase_nolag r (v := true) (t0 := 0) (t1 := F) inp_hi0
    (fun k a hk _ h _ => h (nodes0 a.src))
  have pinsF : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → ∀ u, u ≤ F → r.pin k u = true :=
    fun k a hk u hu => persist u (Nat.zero_le _) (fun σ _ b => P0 σ (Nat.zero_le _) (by omega) k a hk)
      (hq k a hk)
  have nodesF : ∀ w, w ≠ 0 → ∀ u, u ≤ F → sig w u = true :=
    fun w hw u hu => persist u (Nat.zero_le _)
      (fun σ _ b => nodes_stay r (P0 σ (Nat.zero_le _) (by omega)) hw) (nodes0 w)
  -- phase [F, F + T): nothing rises
  have P1 := phase_nolag r (v := false) (t0 := F) (t1 := F + T) inp_lo
    (fun k a hk _ _ => by rw [pinsF k a hk F (Nat.le_refl _)]; decide)
  have nodes_norise : ∀ w, w ≠ 0 → ∀ σ, F ≤ σ → σ < F + T →
      ¬ (sig w σ = false ∧ sig w (σ + 1) = true) :=
    fun w hw σ a b => nodes_stay r (P1 σ a b) hw
  -- M0 at F + T
  have hM0 : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.src ≠ 0 →
      r.pin k (F + T) = false → sig a.src (F + T) = false := by
    intro k a hk ha hp
    obtain ⟨u, c1, c2, c3, c4⟩ := ivt (x := r.pin k) (v := false) (t0 := F) (F + T) (by omega)
      (pinsF k a hk F (Nat.le_refl _)) hp
    have hsu : sig a.src u = false := by rw [← pin_si r hk u (by rw [c3, c4]; decide), c4]
    exact persist (t0 := u) (F + T) (by omega)
      (fun σ b1 b2 => nodes_norise a.src ha σ (by omega) b2) hsu
  have zFT : sig z (F + T) = false := by
    cases h : sig z (F + T) with
    | false => rfl
    | true =>
      have := nodes_norise z hz (F + T - 1) (by omega) (by omega)
      rw [show F + T - 1 + 1 = F + T by omega] at this
      exact absurd ⟨hS1, h⟩ this
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    by_cases c1 : t + 1 ≤ F
    · exact absurd ((nodesF z hz (t + 1) c1).trans (nodesF z hz t (by omega)).symm) ht
    · by_cases c2 : t < F + T
      · rw [inp_lo t (by omega) c2]
        cases h : sig z (t + 1) with
        | false => rfl
        | true =>
          have h0 : sig z t = false := by
            cases h' : sig z t with
            | false => rfl
            | true => rw [h, h'] at ht; exact absurd rfl ht
          exact absurd ⟨h0, h⟩ (nodes_norise z hz t (by omega) c2)
      · rw [inp_hi t (by omega)]
        cases h : sig z (t + 1) with
        | true => rfl
        | false =>
          have h0 : sig z t = true := by
            cases h' : sig z t with
            | true => rfl
            | false => rw [h, h'] at ht; exact absurd rfl ht
          obtain ⟨ρ, b1, b2, b3, b4⟩ := ivt (x := sig z) (v := true) (t0 := F + T) t (by omega) zFT h0
          exact absurd ⟨ρ, b1, b2, b3, b4, h0, h⟩
            ((phase_rise r (t0 := F + T) (t1 := t + 1) (fun u a _ => inp_hi u a) hM0 hD t
              (by omega) (by omega)).2 z hz)
  · intro t ht
    rcases pulse_chg ht with e | e
    · rw [nodesF z hz t (by omega), inp_hi0 t (Nat.zero_le _) (by omega)]
    · rw [show t = F + T - 1 by omega, hS1, inp_lo _ (by omega) (by omega)]
  · rw [nodes0 z, inp_hi0 0 (Nat.le_refl _) (by omega)]

/-! ## Forced (run-independent) forms, decided by the checker -/

/-- 10o's `Settled` at the single point `F + T - 1` (the input's return). -/
def SettledPt (net : Netlist) (F T z : Nat) : Prop := Lc net (pulse F T) z (F + T - 1)

/-- **D, forced form**: chain pin `k` (arc `a`) is FORCED low at some `tq ≥ F + T` and its
node `a.dst` is FORCED low on `[F + T, tq)` (10o's `lowPin` / `Lc`). -/
def DForced (net : Netlist) (F T _k : Nat) (a : Arc) : Prop :=
  ∃ tq, F + T ≤ tq ∧ lowPin a.lo a.hi (Lc net (pulse F T) a.src) tq ∧
    ∀ τ, F + T ≤ τ → τ < tq → Lc net (pulse F T) a.dst τ

/-- All chain pins into multi-pin nodes satisfy `DForced`. -/
def DAll (net : Netlist) (F T : Nat) : Prop :=
  ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.src ≠ 0 → OtherIn net k a.dst →
    DForced net F T k a

theorem drun_of_forced (hwf : net.WF) (r : InRun net (pulse F T) sig) {k : Nat} {a : Arc}
    (hk : net.arcs[k]? = some a) (h : DForced net F T k a) : DRun r (F + T) k a := by
  obtain ⟨tq, h1, h2, h3⟩ := h
  refine ⟨tq, h1, ?_, fun τ b1 b2 => cert_sound hwf (r.toAnd hwf) (Lc_cert hwf _) a.dst τ (h3 τ b1 b2)⟩
  exact pin_low ((r.toAnd hwf).bd k a hk)
    (lowPin_mono (fun w hw => cert_sound hwf (r.toAnd hwf) (Lc_cert hwf _) a.src w hw) h2)

/-- **The bridge from the forced (checkable) conditions.** -/
theorem lumped_of_forced (hwf : net.WF) (r : InRun net (pulse F T) sig) (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hq : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → r.pin k 0 = true)
    {z : Nat} (hz : z ≠ 0) (hS : SettledPt net F T z) (hD : DAll net F T) :
    (∀ t, sig z (t + 1) ≠ sig z t → sig z (t + 1) = pulse F T t) ∧
    (∀ t, pulse F T (t + 1) ≠ pulse F T t → sig z t = pulse F T t) ∧
    sig z 0 = pulse F T 0 :=
  lumped_pulse r hF hT hq hz (cert_sound hwf (r.toAnd hwf) (Lc_cert hwf _) z _ hS)
    (fun k a hk ha ho => drun_of_forced hwf r hk (hD k a hk ha ho))

/-- 10o's `Settled` window (chainck's PASS: `[A, F + T + Lr)` with `A ≤ F + T - 1`) gives
`SettledPt`. -/
theorem settledPt_of_settled {F T z A Lr : Nat} (hA : A ≤ F + T - 1) (hT : 1 ≤ T)
    (h : Settled net (pulse F T) z A (F + T + Lr)) : SettledPt net F T z :=
  h _ hA (by omega)

/-! ## Monotone in the return time (chainck decides at the late side's lower bound) -/

theorem settledPt_mono (hwf : net.WF) {F T T' z : Nat} (hT : T ≤ T') (h1 : 1 ≤ T)
    (h : SettledPt net F T z) : SettledPt net F T' z :=
  Lc_dil hwf (pulse_dil hT) z _ ⟨F + T - 1, h, by omega, by omega⟩

theorem dAll_mono (hwf : net.WF) {F T T' : Nat} (hT : T ≤ T') (h : DAll net F T) :
    DAll net F T' := by
  intro k a hk ha ho
  obtain ⟨tq, h1, h2, h3⟩ := h k a hk ha ho
  have hlh := (hwf a (List.mem_of_getElem? hk)).2
  refine ⟨tq + (T' - T), by omega, ?_, fun τ b1 b2 => ?_⟩
  · exact lowPin_dil hlh (fun w hw => Lc_dil hwf (pulse_dil hT) a.src w hw) _
      ⟨tq, h2, by omega, by omega⟩
  · exact Lc_dil hwf (pulse_dil hT) a.dst τ ⟨τ - (T' - T), h3 _ (by omega) (by omega), by omega, by omega⟩

end Formal.Timing.ChainSettleBridge
