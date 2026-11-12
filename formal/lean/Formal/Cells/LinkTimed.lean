import Formal.Cells.CElemTiming
import Formal.Cells.Bundling
import Formal.Cells.LinkHandshake
open Formal.Core.LutList

/-!
# Track 6, probe 6d: one timed `bd_link` stage, controller composed in

One `bd_link` stage (Muller controller, `cells/rtl/bd_link.v`, `DELAY = DACK = 0`
unless folded into the environment latencies):

* controller `bd_link_ctl` = `bd_c2n`, INIT `0x00B200B200B200B2`, pins
  `I0 = req_in`, `I1 = c_next = ack_out`, `I2 = c` (own output through its routed
  feedback wire), `I3 = rst`. Modelled by probe 5b's `CElemTiming.Loop`
  (LUT window delay `[dlmin, dlmax]`, feedback wire window `[dwmin, dwmax]`).
* the node `O` (= `c`) drives `req_out`, `ack_in` and the enables of the latch
  LUTs. Each latch bit `i` reads the node through its OWN enable branch window
  `[elo i, ehi i]` (fanout wire + I1 arc), its data through `[dlo i, dhi i]`
  and its own output through `[flo i, fhi i]` (loop wire + I2 arc): probe 6c's
  `Bundling.LatchRel`, which `Bundling.odd_latch` / `pair_o5_latch` /
  `pair_o6_latch` derive from the real latch INITs under H_KLEENE_LUT.
* a timed four-phase sender and receiver, given by their event times at the
  controller pins (`ρ k`/`φ k`: `req_in` rise/fall of token `k`; `α k`/`β k`:
  `ack_out` rise/fall) and causality-with-latency hypotheses.

What is DERIVED here (not assumed):
1. `ctl_phases`, `enable_train`: the node is a pulse train, high on
   `[cph (2k) + dlmax, cph (2k+1) + dlmin)`, low on
   `[cph (2k+1) + dlmax, cph (2k+2) + dlmin)`, where `cph` are phase-start
   times computed from the environment's event times. The enable hypotheses
   of `Bundling.capture` (clean pulse) follow exactly when `dlmin = dlmax`
   (`stage_token_clean` calls `Bundling.capture` itself); for a genuine delay
   interval the node may glitch inside the transition windows of width
   `dlmax - dlmin`, and `capture_win` (a generalisation of `Bundling.capture`
   with an arbitrary closing window) covers that.
2. `stage_token`: for EVERY token `k` and every bit `i < W`, the latch output
   equals the sender's value `val k i` from `max (cph(2k)+dlmax+ehi i, dS k+dhi i)`
   until the next enable rise can reach the bit; `stage_forward`: it is valid
   at least until the receiver's acknowledge falls, and from the receiver's
   acknowledge rise on when the output-bundling inequality holds.
   The induction over tokens is the phase induction of
   `CElemTiming.c2_four_phase` plus `phase_gap` below.
3. The stage's timing contract is collected in the structures `CtlEnv` and
   `DataPath` (every field a named hypothesis); the notes file maps each one
   to the tighten.py / skew.py rule that checks it.
-/

namespace Formal.Cells.LinkTimed
open Formal.Cells

abbrev Trace := Nat → Bool

/-! ## 1. `bd_c2n` is `bd_c2` with its second input inverted -/

theorem c2n_as_c2 (a b q r : Bool) :
    CElemTiming.exc CElemTiming.INIT_c2n a b q r = CElemTiming.exc CElemTiming.INIT_c2 a (!b) q r := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- A `bd_c2n` loop is a `bd_c2` loop on the inputs `(a, ¬b)`: same LUT delay,
same feedback wire. -/
theorem loop_c2n {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}
    (L : CElemTiming.Loop CElemTiming.INIT_c2n a b rst O qp dlmin dlmax dwmin dwmax) :
    CElemTiming.Loop CElemTiming.INIT_c2 a (fun t => !b t) rst O qp dlmin dlmax dwmin dwmax where
  H_LUT := by
    have e : (fun t => CElemTiming.exc CElemTiming.INIT_c2 (a t) ((fun t => !b t) t) (qp t) (rst t))
        = (fun t => CElemTiming.exc CElemTiming.INIT_c2n (a t) (b t) (qp t) (rst t)) := by
      funext t; rw [c2n_as_c2]
    rw [e]; exact L.H_LUT
  H_FB := L.H_FB
  H_LOOP_POS := L.H_LOOP_POS

/-! ## 2. Phases from the environment's event times -/

/-- Previous `ack_out` fall (`0` before token 0). -/
def pb (β : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => β k

/-- Previous `req_in` fall (`0` before token 0). -/
def pf (φ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => φ k

/-- Phase-start times of the controller (both inputs at the phase target):
phase `2k` (rise of token `k`): `req_in = 1 ∧ ack_out = 0`, first at
`max (ρ k) (β (k-1))`; phase `2k+1` (fall): `req_in = 0 ∧ ack_out = 1`, first at
`max (φ k) (α k)`. -/
def cph (ρ φ α β : Nat → Nat) (j : Nat) : Nat :=
  if j % 2 = 0 then max (ρ (j / 2)) (pb β (j / 2)) else max (φ (j / 2)) (α (j / 2))

/-- Phase target of the node: 1 on even phases, 0 on odd ones. -/
def Vph (j : Nat) : Bool := decide (j % 2 = 0)

theorem cph_e (ρ φ α β : Nat → Nat) (k : Nat) : cph ρ φ α β (2 * k) = max (ρ k) (pb β k) := by
  simp only [cph, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega, ↓reduceIte]

theorem cph_o (ρ φ α β : Nat → Nat) (k : Nat) : cph ρ φ α β (2 * k + 1) = max (φ k) (α k) := by
  simp only [cph, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]; rfl

theorem cph_e1 (ρ φ α β : Nat → Nat) (k : Nat) :
    cph ρ φ α β (2 * k + 1 + 1) = max (ρ (k + 1)) (β k) := by
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, cph_e]; rfl

theorem cph_zero (ρ φ α β : Nat → Nat) : cph ρ φ α β 0 = ρ 0 := by
  have := cph_e ρ φ α β 0
  simp only [Nat.mul_zero] at this
  rw [this]; simp [pb]

theorem Vph_e (k : Nat) : Vph (2 * k) = true := by
  unfold Vph; rw [decide_eq_true_iff]; omega

theorem Vph_o (k : Nat) : Vph (2 * k + 1) = false := by
  unfold Vph; rw [decide_eq_false_iff_not]; omega

theorem Vph_alt (j : Nat) : Vph (j + 1) = !Vph j := by
  unfold Vph
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have h' : ¬ ((j + 1) % 2 = 0) := by omega
    simp [h, h']
  · have h' : (j + 1) % 2 = 0 := by omega
    simp [h, h']

theorem par_cases (P : Nat → Prop) (h0 : ∀ k, P (2 * k)) (h1 : ∀ k, P (2 * k + 1)) : ∀ j, P j := by
  intro j
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have := h0 (j / 2); rwa [show 2 * (j / 2) = j by omega] at this
  · have := h1 (j / 2); rwa [show 2 * (j / 2) + 1 = j by omega] at this

/-! ## 3. The controller plus its environment -/

/-- **Controller and environment hypotheses** (part of the stage contract).
All traces are at the controller LUT's pins (`req` at I0, `ack` at I1 =
`c_next`, `rst` at I3); `O` is the LUT output (the node), `qp` its feedback
pin. -/
structure CtlEnv (req ack rst O qp : Trace) (ρ φ α β : Nat → Nat)
    (dlmin dlmax dwmin dwmax E t0 : Nat) : Prop where
  /-- **H_CTL** (5b's `Loop` for the real `bd_c2n` INIT): LUT `I*->O` delay in
  `[dlmin, dlmax]`, feedback wire `O->I2` in `[dwmin, dwmax]`, positive loop.
  Test: prjxray-db min/max of the LUT arc and of the routed net `c`
  (`<link>.ctl.u.u`) in the SDF, >= 4 seeds. -/
  H_CTL : CElemTiming.Loop CElemTiming.INIT_c2n req ack rst O qp dlmin dlmax dwmin dwmax
  /-- **H_REQ_SHAPE**: `req_in` at the pin is low before `ρ 0`, high on
  `[ρ k, φ k)`, low on `[φ k, ρ (k+1))` (a clean four-phase request: no
  glitches at the pin). Test: GLS trace of `req_in` at the LUT pin. -/
  H_REQ_LOW0 : ∀ t, t < ρ 0 → req t = false
  H_REQ_HIGH : ∀ k t, ρ k ≤ t → t < φ k → req t = true
  H_REQ_LOW : ∀ k t, φ k ≤ t → t < ρ (k + 1) → req t = false
  /-- **H_ACK_SHAPE**: `ack_out` at the I1 pin low before `α 0`, high on
  `[α k, β k)`, low on `[β k, α (k+1))`. -/
  H_ACK_LOW0 : ∀ t, t < α 0 → ack t = false
  H_ACK_HIGH : ∀ k t, α k ≤ t → t < β k → ack t = true
  H_ACK_LOW : ∀ k t, β k ≤ t → t < α (k + 1) → ack t = false
  /-- **H_SND_FALL** (sender causality): the sender withdraws `req_in` of
  token `k` only after it has seen the node HIGH at some `u` from the current
  phase on, at least `E` earlier (E = minimum of node -> ack_in wire (+ DACK
  rise, FASTRISE: one hop) + sender reaction + sender -> req_in pin wire).
  `causal_of_wire` derives this form from an observation through a window
  wire. -/
  H_SND_FALL : ∀ k, ∃ u, cph ρ φ α β (2 * k) ≤ u ∧ u + E ≤ φ k ∧ O u = true
  /-- **H_RCV_RISE** (receiver causality): `ack_out` rises only after the
  receiver saw `req_out` (= node, DELAY line folded into `E`) high. -/
  H_RCV_RISE : ∀ k, ∃ u, cph ρ φ α β (2 * k) ≤ u ∧ u + E ≤ α k ∧ O u = true
  /-- **H_SND_RISE**: the next request only after the node was seen LOW. -/
  H_SND_RISE : ∀ k, ∃ u, cph ρ φ α β (2 * k + 1) ≤ u ∧ u + E ≤ ρ (k + 1) ∧ O u = false
  /-- **H_RCV_FALL**: `ack_out` falls only after `req_out` was seen low. -/
  H_RCV_FALL : ∀ k, ∃ u, cph ρ φ α β (2 * k + 1) ≤ u ∧ u + E ≤ β k ∧ O u = false
  /-- **H_ENV_POS**: the environment never responds in zero time. -/
  H_ENV_POS : 1 ≤ E
  /-- **H_ENV_LATENCY** (5b): `Dmax ≤ dlmin + E`, i.e. the environment's
  minimum node-to-input latency exceeds the feedback wire's max delay plus the
  LUT delay spread (isochronic fork `O -> neighbour` vs `O -> I2`). -/
  H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E
  /-- **H_RST_PULSE**: `rst = 1` for at least `Dmax` from `t0` ... -/
  H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true
  /-- ... **H_RST_OFF**: and `0` after it ... -/
  H_RST_OFF : ∀ s, t0 + (dlmax + dwmax) ≤ s → rst s = false
  /-- ... **H_RST_EARLY**: and released before the first request reaches I0. -/
  H_RST_EARLY : t0 + (dlmax + dwmax) ≤ ρ 0

section ctl
variable {req ack rst O qp : Trace} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}

theorem req_lo_pre (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ k t, pf φ k ≤ t → t < ρ k → req t = false := by
  intro k t h1 h2
  cases k with
  | zero => exact C.H_REQ_LOW0 t h2
  | succ k => exact C.H_REQ_LOW k t h1 h2

theorem ack_lo_pre (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ k t, pb β k ≤ t → t < α k → ack t = false := by
  intro k t h1 h2
  cases k with
  | zero => exact C.H_ACK_LOW0 t h2
  | succ k => exact C.H_ACK_LOW k t h1 h2

theorem f_gt (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    max (ρ k) (pb β k) + E ≤ φ k := by
  obtain ⟨u, hu1, hu2, _⟩ := C.H_SND_FALL k; rw [cph_e] at hu1; omega

theorem a_gt (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    max (ρ k) (pb β k) + E ≤ α k := by
  obtain ⟨u, hu1, hu2, _⟩ := C.H_RCV_RISE k; rw [cph_e] at hu1; omega

theorem r_gt (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    max (φ k) (α k) + E ≤ ρ (k + 1) := by
  obtain ⟨u, hu1, hu2, _⟩ := C.H_SND_RISE k; rw [cph_o] at hu1; omega

theorem b_gt (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    max (φ k) (α k) + E ≤ β k := by
  obtain ⟨u, hu1, hu2, _⟩ := C.H_RCV_FALL k; rw [cph_o] at hu1; omega

/-- Derived `H_ORDER` of `c2_four_phase`. -/
theorem ctl_order (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ j, cph ρ φ α β j < cph ρ φ α β (j + 1) := by
  have hE := C.H_ENV_POS
  apply par_cases
  · intro k; rw [cph_e, cph_o]; have := f_gt C k; omega
  · intro k; rw [cph_o, cph_e1]; have := r_gt C k; omega

/-- Derived `H_BOTH`. -/
theorem ctl_both (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ j, req (cph ρ φ α β j) = Vph j ∧ (fun t => !ack t) (cph ρ φ α β j) = Vph j := by
  have hE := C.H_ENV_POS
  apply par_cases
  · intro k
    rw [cph_e, Vph_e]
    have h1 := f_gt C k; have h2 := a_gt C k
    refine ⟨C.H_REQ_HIGH k _ (Nat.le_max_left _ _) (by omega), ?_⟩
    have h := ack_lo_pre C k (max (ρ k) (pb β k)) (Nat.le_max_right _ _) (by omega)
    simp [h]
  · intro k
    rw [cph_o, Vph_o]
    have h1 := r_gt C k; have h2 := b_gt C k
    refine ⟨C.H_REQ_LOW k _ (Nat.le_max_left _ _) (by omega), ?_⟩
    have h := C.H_ACK_HIGH k (max (φ k) (α k)) (Nat.le_max_right _ _) (by omega)
    simp [h]

/-- Derived `H_NEXT`. -/
theorem ctl_next (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ j s, cph ρ φ α β j ≤ s → s < cph ρ φ α β (j + 1) →
      req s = Vph j ∨ (fun t => !ack t) s = Vph j := by
  apply par_cases (fun j => ∀ s, cph ρ φ α β j ≤ s → s < cph ρ φ α β (j + 1) →
      req s = Vph j ∨ (fun t => !ack t) s = Vph j)
  · intro k s h1 h2
    rw [cph_e] at h1; rw [cph_o] at h2; rw [Vph_e]
    by_cases hf : s < φ k
    · exact Or.inl (C.H_REQ_HIGH k s (by omega) hf)
    · have h := ack_lo_pre C k s (by omega) (by omega)
      right; simp [h]
  · intro k s h1 h2
    rw [cph_o] at h1; rw [cph_e1] at h2; rw [Vph_o]
    by_cases hr : s < ρ (k + 1)
    · exact Or.inl (C.H_REQ_LOW k s (by omega) hr)
    · have h := C.H_ACK_HIGH k s (by omega) (by omega)
      right; simp [h]

/-- Derived `H_ACK` (the four-phase discipline at the node), from the
per-event causality of the sender and the receiver. -/
theorem ctl_ack (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ j s, cph ρ φ α β j ≤ s → (req s ≠ Vph j ∨ (fun t => !ack t) s ≠ Vph j) →
      ∃ u, cph ρ φ α β j ≤ u ∧ u + E ≤ s ∧ O u = Vph j := by
  apply par_cases (fun j => ∀ s, cph ρ φ α β j ≤ s →
      (req s ≠ Vph j ∨ (fun t => !ack t) s ≠ Vph j) →
      ∃ u, cph ρ φ α β j ≤ u ∧ u + E ≤ s ∧ O u = Vph j)
  · intro k s hs hd
    have hs' : max (ρ k) (pb β k) ≤ s := by rw [← cph_e]; exact hs
    rw [Vph_e] at hd ⊢
    by_cases h1 : s < φ k
    · by_cases h2 : s < α k
      · exfalso
        have r1 := C.H_REQ_HIGH k s (by omega) h1
        have r2 := ack_lo_pre C k s (by omega) h2
        simp [r1, r2] at hd
      · obtain ⟨u, hu1, hu2, hu3⟩ := C.H_RCV_RISE k
        exact ⟨u, hu1, by omega, hu3⟩
    · obtain ⟨u, hu1, hu2, hu3⟩ := C.H_SND_FALL k
      exact ⟨u, hu1, by omega, hu3⟩
  · intro k s hs hd
    have hs' : max (φ k) (α k) ≤ s := by rw [← cph_o]; exact hs
    rw [Vph_o] at hd ⊢
    by_cases h1 : s < ρ (k + 1)
    · by_cases h2 : s < β k
      · exfalso
        have r1 := C.H_REQ_LOW k s (by omega) h1
        have r2 := C.H_ACK_HIGH k s (by omega) h2
        simp [r1, r2] at hd
      · obtain ⟨u, hu1, hu2, hu3⟩ := C.H_RCV_FALL k
        exact ⟨u, hu1, by omega, hu3⟩
    · obtain ⟨u, hu1, hu2, hu3⟩ := C.H_SND_RISE k
      exact ⟨u, hu1, by omega, hu3⟩

theorem ctl_norst (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ s, cph ρ φ α β 0 ≤ s → rst s = false := by
  intro s hs; rw [cph_zero] at hs
  exact C.H_RST_OFF s (by have := C.H_RST_EARLY; omega)

/-- Derived `H_RESET_DONE`, from 5b's `c2_reset` applied to the reduced loop. -/
theorem ctl_reset_done (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ u, cph ρ φ α β 0 ≤ u → u < cph ρ φ α β 0 + dlmin → O u = !Vph 0 := by
  have L := loop_c2n C.H_CTL
  have hl := CElemTiming.winDelay_le C.H_CTL.H_LUT
  have hw := CElemTiming.winDelay_le C.H_CTL.H_FB
  have hp := C.H_CTL.H_LOOP_POS
  have he := C.H_RST_EARLY
  have res := CElemTiming.c2_reset L t0 (ρ 0 - 1) C.H_RST_PULSE
    (fun s _ h2 => Or.inl (C.H_REQ_LOW0 s (by omega)))
  intro u h1 h2
  rw [cph_zero] at h1 h2
  rw [res.1 u (by omega) (by omega)]; rfl

/-- **(1) The controller follows the four-phase environment** (from 5b's
`c2_four_phase`, every hypothesis of which is derived above): for every
phase `j`, the node is `Vph j` on `[cph j + dlmax, cph (j+1) + dlmin)` and the
feedback pin likewise on `[cph j + Dmax, cph (j+1) + Dmin)`. -/
theorem ctl_phases (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ j, (∀ t, cph ρ φ α β j + dlmax ≤ t → t + 1 ≤ cph ρ φ α β (j + 1) + dlmin → O t = Vph j) ∧
      (∀ t, cph ρ φ α β j + (dlmax + dwmax) ≤ t →
        t + 1 ≤ cph ρ φ α β (j + 1) + (dlmin + dwmin) → qp t = Vph j) :=
  CElemTiming.c2_four_phase (loop_c2n C.H_CTL) Vph (cph ρ φ α β) E Vph_alt (ctl_order C)
    (ctl_both C) (ctl_next C) (ctl_norst C) (ctl_ack C) C.H_ENV_LATENCY (ctl_reset_done C)

end ctl

/-! ## 4. Phase gap and "the environment never sees the new value early"

`c2_four_phase` proves, but does not export, that consecutive phase starts
are at least `Dmax` apart and that the node still shows the previous value
for `dlmin` after each phase start. Re-derived generically here. -/

theorem phase_gap {a b O : Trace} {V : Nat → Bool} {c : Nat → Nat} {E dlmin dlmax dwmax : Nat}
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, a (c k) = V k ∧ b (c k) = V k)
    (H_ACK : ∀ k s, c k ≤ s → (a s ≠ V k ∨ b s ≠ V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + dlmin → O u = !V 0)
    (PH : ∀ k t, c k + dlmax ≤ t → t + 1 ≤ c (k + 1) + dlmin → O t = V k) :
    ∀ j, (∀ u, c j ≤ u → u < c j + dlmin → O u = !V j) ∧ c j + (dlmax + dwmax) ≤ c (j + 1) := by
  have gap : ∀ j, (∀ u, c j ≤ u → u < c j + dlmin → O u = !V j) →
      c j + (dlmax + dwmax) ≤ c (j + 1) := by
    intro j R
    apply Classical.byContradiction; intro hlt
    have hb := (H_BOTH (j + 1)).1
    rw [H_ALT j] at hb
    have hne : a (c (j + 1)) ≠ V j := by
      rw [hb]; cases V j <;> decide
    obtain ⟨u, hu1, hu2, hu3⟩ := H_ACK j (c (j + 1)) (Nat.le_of_lt (H_ORDER j)) (Or.inl hne)
    have := R u hu1 (by omega)
    rw [hu3] at this; cases hv : V j <;> simp [hv] at this
  intro j
  induction j with
  | zero => exact ⟨H_RESET_DONE, gap 0 H_RESET_DONE⟩
  | succ j ih =>
    have R : ∀ u, c (j + 1) ≤ u → u < c (j + 1) + dlmin → O u = !V (j + 1) := by
      intro u h1 h2
      rw [H_ALT j, Bool.not_not]
      exact PH j u (by have := ih.2; omega) (by omega)
    exact ⟨R, gap (j + 1) R⟩

section token
variable {req ack rst O qp : Trace} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}

theorem ctl_gap (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) :
    ∀ j, (∀ u, cph ρ φ α β j ≤ u → u < cph ρ φ α β j + dlmin → O u = !Vph j) ∧
      cph ρ φ α β j + (dlmax + dwmax) ≤ cph ρ φ α β (j + 1) :=
  phase_gap Vph_alt (ctl_order C) (ctl_both C) (ctl_ack C) C.H_ENV_LATENCY
    (ctl_reset_done C) (fun k => (ctl_phases C k).1)

/-- An observation of the phase's new value is at least `dlmin` after the
phase start (the node cannot be seen to switch earlier). -/
theorem obs_late (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (j u : Nat) (h1 : cph ρ φ α β j ≤ u) (h2 : O u = Vph j) : cph ρ φ α β j + dlmin ≤ u := by
  apply Classical.byContradiction; intro hlt
  have := (ctl_gap C j).1 u h1 (by omega)
  rw [h2] at this; cases hv : Vph j <;> simp [hv] at this

/-- The sender drops the request no earlier than `dlmin + E` after the phase
start, hence the falling phase starts that late. -/
theorem fall_after (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    cph ρ φ α β (2 * k) + dlmin + E ≤ cph ρ φ α β (2 * k + 1) := by
  obtain ⟨u, hu1, hu2, hu3⟩ := C.H_SND_FALL k
  have := obs_late C (2 * k) u hu1 (by rw [Vph_e]; exact hu3)
  rw [cph_o]; omega

theorem ack_rise_after (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    cph ρ φ α β (2 * k) + dlmin + E ≤ α k := by
  obtain ⟨u, hu1, hu2, hu3⟩ := C.H_RCV_RISE k
  have := obs_late C (2 * k) u hu1 (by rw [Vph_e]; exact hu3)
  omega

/-- **(1') The latch enable is a pulse train.** Token `k`: the node is high on
`[cph (2k) + dlmax, cph (2k+1) + dlmin)` and low on
`[cph (2k+1) + dlmax, cph (2k+2) + dlmin)`; both intervals are non-empty
(`Dmax ≤ dlmin + E` and the phase gap). -/
theorem enable_train (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    (∀ t, cph ρ φ α β (2 * k) + dlmax ≤ t → t < cph ρ φ α β (2 * k + 1) + dlmin → O t = true) ∧
    (∀ t, cph ρ φ α β (2 * k + 1) + dlmax ≤ t → t < cph ρ φ α β (2 * k + 1 + 1) + dlmin →
      O t = false) ∧
    cph ρ φ α β (2 * k) + dlmax < cph ρ φ α β (2 * k + 1) + dlmin ∧
    cph ρ φ α β (2 * k + 1) + dlmax < cph ρ φ α β (2 * k + 1 + 1) + dlmin := by
  have hp := C.H_CTL.H_LOOP_POS
  have hw := CElemTiming.winDelay_le C.H_CTL.H_FB
  have g0 := (ctl_gap C (2 * k)).2
  have g1 := (ctl_gap C (2 * k + 1)).2
  refine ⟨fun t h1 h2 => ?_, fun t h1 h2 => ?_, by omega, by omega⟩
  · have := (ctl_phases C (2 * k)).1 t h1 (by omega); rwa [Vph_e] at this
  · have := (ctl_phases C (2 * k + 1)).1 t h1 (by omega); rwa [Vph_o] at this

end token

/-! ## 5. Latch capture with a dirty closing window -/

/-- **`Bundling.capture` generalised**: the enable is high on `[Ton, Toff1)`,
ARBITRARY (glitches allowed) on `[Toff1, Toff2)`, low on `[Toff2, Tnext)`.
`Toff1 = Toff2` is `Bundling.capture`. -/
theorem capture_win (d en q : Bundling.Sig) (dlo dhi elo ehi flo fhi : Nat)
    (hL : Bundling.LatchRel d en q dlo dhi elo ehi flo fhi)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff1 Toff2 Tnext Td Tnew : Nat) (v : Bool)
    (h12 : Toff1 ≤ Toff2)
    (h_on : ∀ t, Ton ≤ t → t < Toff1 → en t = true)
    (h_off : ∀ t, Toff2 ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_SETUP : max (Ton + ehi) (Td + dhi) + fhi ≤ Toff1 + elo)
    (H_HOLD : Toff2 + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v := by
  suffices H : ∀ n, ∀ t, t < n → max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v
    from fun t h1 h2 => H (t + 1) t (Nat.lt_succ_self t) h1 h2
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t htn h1 h2
    by_cases hA : t < Toff1 + elo
    · have he : Bundling.winK en elo ehi t = .t :=
        Bundling.win_eq (b := true) hew (fun u hu1 hu2 => h_on u (by omega) (by omega))
      have hd : Bundling.winK d dlo dhi t = K3.ofBool v :=
        Bundling.win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
      exact hL t v (by rw [he, hd]; rfl)
    · have hq : Bundling.winK q flo fhi t = K3.ofBool v :=
        Bundling.win_eq hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      by_cases hB : t < Toff2 + ehi
      · have hd : Bundling.winK d dlo dhi t = K3.ofBool v :=
          Bundling.win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
        exact hL t v (by rw [hq, hd, Bundling.mux_same])
      · have he : Bundling.winK en elo ehi t = .f :=
          Bundling.win_eq (b := false) hew (fun u hu1 hu2 => h_off u (by omega) (by omega))
        exact hL t v (by rw [he, hq]; rfl)

/-! ## 6. The data path and the per-token theorem -/

/-- **Data-path hypotheses** (rest of the stage contract). `d i` is the
sender's data net of bit `i`, `q i` the latch output of bit `i`, `O` the node
(the enable net, read by each bit through its own window). -/
structure DataPath (O : Trace) (d q : Nat → Bundling.Sig) (val : Nat → Nat → Bool)
    (dS dE : Nat → Nat) (dlo dhi elo ehi flo fhi : Nat → Nat) (W : Nat)
    (ρ φ α β : Nat → Nat) (dlmin dlmax E Erel Sdr Lag : Nat) : Prop where
  /-- **H_LATCH**: bit `i`'s latch LUT is the Kleene mux over its pin
  windows (from the real INIT by `Bundling.odd_latch` / `pair_o5_latch` /
  `pair_o6_latch`, under H_KLEENE_LUT). `[elo i, ehi i]` is THIS bit's branch
  of the enable fanout (routed wire + I1 arc). Test: SDF of the enable net to
  each `<link>.lat.*` pin, >= 4 seeds. -/
  H_LATCH : ∀ i, i < W → Bundling.LatchRel (d i) O (q i) (dlo i) (dhi i) (elo i) (ehi i) (flo i) (fhi i)
  H_WIN : ∀ i, i < W → dlo i ≤ dhi i ∧ elo i ≤ ehi i ∧ flo i ≤ fhi i
  /-- **H_LATCH_LOOP_POS**: each latch loop (wire + I2 arc) has positive delay. -/
  H_LATCH_LOOP_POS : ∀ i, i < W → 1 ≤ flo i
  /-- **H_DATA_VALID**: the sender holds token `k`'s value on its data nets
  from `dS k` until it releases them at `dE k`. -/
  H_DATA_VALID : ∀ k i t, i < W → dS k ≤ t → t < dE k → d i t = val k i
  /-- **H_DATA_LEAD**: the data nets settle no later than `Lag - Sdr` after
  the request reaches the controller pin (`Sdr`: lead of a "data then
  request" sender; `Lag`: lag of a sender whose request LEADS its data, e.g.
  an upstream `bd_link`, whose req_out leads data_out by one latch arc per
  stage -- bd_link.v header). Use `Lag = 0` or `Sdr = 0`. -/
  H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag
  /-- **H_DATA_REL** (sender release causality): the sender releases token
  `k`'s data only after it saw the node LOW, at least `Erel` earlier
  (`Erel` = min of node -> ack_in incl. the DACK chain's fall + sender's
  release path to its data net). -/
  H_DATA_REL : ∀ k, ∃ u, cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧ O u = false
  /-- **H_PULSE_WIDTH**: the enable's high phase at bit `i` outlasts its
  spread plus one latch loop. -/
  H_PULSE_WIDTH : ∀ i, i < W → dlmax + ehi i + fhi i ≤ 2 * dlmin + E + elo i
  /-- **H_DATA_SETUP**: data (launched `Sdr` before the request) is through
  the D arc and once round the latch loop before the earliest enable fall. -/
  H_DATA_SETUP : ∀ i, i < W → dhi i + fhi i + Lag ≤ Sdr + 2 * dlmin + E + elo i
  /-- **H_RULE_H**: the latest enable fall at bit `i` is no later than the
  earliest arrival of the released data at its D pin. -/
  H_RULE_H : ∀ i, i < W → dlmax + ehi i ≤ dlmin + Erel + dlo i

section data
variable {req ack rst O qp : Trace} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}
  {d q : Nat → Bundling.Sig} {val : Nat → Nat → Bool} {dS dE : Nat → Nat}
  {dlo dhi elo ehi flo fhi : Nat → Nat} {W Erel Sdr Lag : Nat}

theorem rel_after (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag) (k : Nat) :
    cph ρ φ α β (2 * k + 1) + dlmin + Erel ≤ dE k := by
  obtain ⟨u, hu1, hu2, hu3⟩ := D.H_DATA_REL k
  have := obs_late C (2 * k + 1) u hu1 (by rw [Vph_o]; exact hu3)
  omega

/-- **(2) Every token is latched.** For every token `k` and bit `i < W`, the
latch output is the sender's value from `max (cph(2k)+dlmax+ehi i, dS k + dhi i)`
until the next enable rise can reach the bit. -/
theorem stage_token (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    (k i : Nat) (hi : i < W) :
    ∀ t, max (cph ρ φ α β (2 * k) + dlmax + ehi i) (dS k + dhi i) ≤ t →
      t < cph ρ φ α β (2 * k + 1 + 1) + dlmin + elo i → q i t = val k i := by
  have hl := CElemTiming.winDelay_le C.H_CTL.H_LUT
  have ⟨hon, hoff, _, _⟩ := enable_train C k
  have hfa := fall_after C k
  have hrel := rel_after C D k
  have hlead := D.H_DATA_LEAD k
  have hrho : ρ k ≤ cph ρ φ α β (2 * k) := by rw [cph_e]; exact Nat.le_max_left _ _
  have ⟨hdw, hew, hfw⟩ := D.H_WIN i hi
  have hpw := D.H_PULSE_WIDTH i hi
  have hds := D.H_DATA_SETUP i hi
  have hh := D.H_RULE_H i hi
  exact capture_win (d i) O (q i) (dlo i) (dhi i) (elo i) (ehi i) (flo i) (fhi i)
    (D.H_LATCH i hi) hdw hew hfw (D.H_LATCH_LOOP_POS i hi)
    (cph ρ φ α β (2 * k) + dlmax) (cph ρ φ α β (2 * k + 1) + dlmin)
    (cph ρ φ α β (2 * k + 1) + dlmax) (cph ρ φ α β (2 * k + 1 + 1) + dlmin)
    (dS k) (dE k) (val k i) (by omega) hon hoff
    (fun t h1 h2 => D.H_DATA_VALID k i t hi h1 h2) (by omega) (by omega)

/-- **(2') Forwarding.** The output holds token `k`'s value at least until the
receiver's acknowledge falls (`β k`), the window the library promises a
sender's data. If moreover the OUTPUT-bundling inequality `H_OUT` holds for
the bit, it is valid from the receiver's acknowledge RISE (`α k`) on: whatever
the receiver latched before acknowledging, it is `val k i` from then on. -/
theorem stage_forward (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    (k i : Nat) (hi : i < W) :
    (∀ t, max (cph ρ φ α β (2 * k) + dlmax + ehi i) (dS k + dhi i) ≤ t → t < β k →
      q i t = val k i) ∧
    (dlmax + ehi i ≤ dlmin + E → dhi i + Lag ≤ Sdr + dlmin + E →
      ∀ t, α k ≤ t → t < β k → q i t = val k i) := by
  have hb : β k ≤ cph ρ φ α β (2 * k + 1 + 1) := by rw [cph_e1]; exact Nat.le_max_right _ _
  have ha := ack_rise_after C k
  have hlead := D.H_DATA_LEAD k
  have hrho : ρ k ≤ cph ρ φ α β (2 * k) := by rw [cph_e]; exact Nat.le_max_left _ _
  refine ⟨fun t h1 h2 => stage_token C D k i hi t h1 (by omega), fun H1 H2 t h1 h2 => ?_⟩
  exact stage_token C D k i hi t (by omega) (by omega)

/-- **Exact clean-pulse case.** With a fixed LUT delay (`dlmin = dlmax`) the
node is exactly the clean pulse train that `Bundling.capture` assumes
(`H_EN_CLEAN`), and `Bundling.capture` itself applies, unchanged. -/
theorem stage_token_clean (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    (hfix : dlmin = dlmax) (k i : Nat) (hi : i < W) :
    ∀ t, max (cph ρ φ α β (2 * k) + dlmax + ehi i) (dS k + dhi i) ≤ t →
      t < cph ρ φ α β (2 * k + 1 + 1) + dlmax + elo i → q i t = val k i := by
  have ⟨hon, hoff, _, _⟩ := enable_train C k
  have hfa := fall_after C k
  have hrel := rel_after C D k
  have hlead := D.H_DATA_LEAD k
  have hrho : ρ k ≤ cph ρ φ α β (2 * k) := by rw [cph_e]; exact Nat.le_max_left _ _
  have ⟨hdw, hew, hfw⟩ := D.H_WIN i hi
  have hpw := D.H_PULSE_WIDTH i hi
  have hds := D.H_DATA_SETUP i hi
  have hh := D.H_RULE_H i hi
  subst hfix
  exact Bundling.capture (d i) O (q i) (dlo i) (dhi i) (elo i) (ehi i) (flo i) (fhi i)
    (D.H_LATCH i hi) hdw hew hfw (D.H_LATCH_LOOP_POS i hi)
    (cph ρ φ α β (2 * k) + dlmin) (cph ρ φ α β (2 * k + 1) + dlmin)
    (cph ρ φ α β (2 * k + 1 + 1) + dlmin) (dS k) (dE k) (val k i)
    hon hoff (fun t h1 h2 => D.H_DATA_VALID k i t hi h1 h2) (by omega) (by omega)

end data

/-! ## 7. Where `E` comes from: observation through a routed wire -/

/-- A party that reads the node through a window wire `[lo, hi]` (e.g. the
`ack_in` net, or `req_out` to the receiver), reads only from `c + hi` on
(freshness), sees value `b` at `v` and acts `S` later, satisfies the
causality form used in `CtlEnv` with latency `E = lo + S`. -/
theorem causal_of_wire {O x : Trace} {lo hi c v S s : Nat} {b : Bool}
    (hw : CElemTiming.WinDelay lo hi O x) (hv : c + hi ≤ v) (hx : x v = b) (hs : v + S ≤ s) :
    ∃ u, c ≤ u ∧ u + (lo + S) ≤ s ∧ O u = b := by
  obtain ⟨u, h1, h2, e⟩ := hw v (by omega)
  exact ⟨u, by omega, by omega, by rw [← e]; exact hx⟩

/-! ## 8. Link to the untimed (interleaving) model of probe 6b

The timed stage orders the six events of every token as
`req↑ (ρ k) ≤ phase start < node↑ window < {req↓ (φ k), ack↑ (α k)}`, then
`max (φ k) (α k) = phase start < node↓ window < {req↑ (ρ (k+1)), ack↓ (β k)}`
(`timed_order`). Read as a word over `LinkHandshake.Lbl`
(`send gate (send recv | recv send) gate recv`), each token is a run of
6b's one-stage interleaving model that returns to the reset state
(`token_cycle`), so the timed trace refines the untimed model token by
token (`timed_refines`). -/

section link
open LinkHandshake

/-- A concrete state of the one-stage model: `req_in`, `C_0`, `ack_out`. -/
def st (a b c : Bool) : St := fun j => if j = 0 then a else if j = 1 then b else if j = 2 then c else false

theorem upd_st0 (a b c v : Bool) : upd (st a b c) 0 v = st v b c := by
  funext j; unfold upd st
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp_all

theorem upd_st1 (a b c v : Bool) : upd (st a b c) 1 v = st a v c := by
  funext j; unfold upd st
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp_all

theorem upd_st2 (a b c v : Bool) : upd (st a b c) 2 v = st a b v := by
  funext j; unfold upd st
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> by_cases h2 : j = 2 <;> simp_all

theorem reset_st : reset = st false false false := by
  funext j; unfold reset st
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> by_cases h2 : j = 2 <;> simp_all

theorem send1 (a b c : Bool) (h : a = b) : Step 1 .send (st a b c) (st (!a) b c) := by
  have := Step.send (N := 1) (st a b c) (by show a = b; exact h)
  rw [upd_st0] at this; exact this

theorem gate1 (a b c : Bool) (h : ctlB a c b false ≠ b) :
    Step 1 (.gate 1) (st a b c) (st a (ctlB a c b false) c) := by
  have := Step.gate (N := 1) (st a b c) 1 (Nat.le_refl 1) (Nat.le_refl 1) h
  rw [upd_st1] at this; exact this

theorem recv1 (a b c : Bool) (h : c ≠ b) : Step 1 .recv (st a b c) (st a b b) := by
  have : Step 1 .recv (st a b c) (upd (st a b c) 2 (st a b c 1)) := Step.recv _ h
  rw [upd_st2] at this; exact this

/-- One token of the one-stage link, in either order of `req↓`/`ack↑`, takes
the interleaving model from reset back to reset with two sends and two
receives. -/
theorem token_cycle (sendFirst : Bool) {s r : Nat} (h : Reach 1 reset s r) :
    Reach 1 reset (s + 2) (r + 2) := by
  rw [reset_st] at h ⊢
  have h1 := Reach.send h (send1 false false false rfl)
  have g1 : ctlB true false false false = true := by decide
  have h2 := Reach.gate h1 (gate1 true false false (by decide))
  rw [g1] at h2
  have g2 : ctlB false true true false = false := by decide
  cases sendFirst with
  | true =>
    have h3 := Reach.send h2 (send1 true true false rfl)
    have h4 := Reach.recv h3 (recv1 false true false (by decide))
    have h5 := Reach.gate h4 (gate1 false true true (by decide))
    rw [g2] at h5
    exact Reach.recv h5 (recv1 false false true (by decide))
  | false =>
    have h3 := Reach.recv h2 (recv1 true true false (by decide))
    have h4 := Reach.send h3 (send1 true true true rfl)
    have h5 := Reach.gate h4 (gate1 false true true (by decide))
    rw [g2] at h5
    exact Reach.recv h5 (recv1 false false true (by decide))

theorem timed_refines_run : ∀ k, Reach 1 reset (2 * k) (2 * k) := by
  intro k
  induction k with
  | zero => exact Reach.init
  | succ k ih =>
    have := token_cycle true ih
    rwa [show 2 * k + 2 = 2 * (k + 1) by omega] at this

end link

section order
variable {req ack rst O qp : Trace} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}

/-- **Time order of one token's events** in the timed stage. The node is
still low until `cph(2k) + dlmin` and high from `cph(2k) + dlmax`, both
after `req↑` and the previous `ack↓`, and the sender's `req↓` and the
receiver's `ack↑` come after the node's whole rise window; symmetrically for
the fall. The `send`/`gate`/`recv` word of 6b's model in this order is a run
(`token_cycle`, whichever of `req↓`, `ack↑` comes first). -/
theorem timed_order (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    -- node rise: after req↑ and the previous ack↓
    ρ k ≤ cph ρ φ α β (2 * k) ∧ pb β k ≤ cph ρ φ α β (2 * k) ∧
    (∀ u, cph ρ φ α β (2 * k) ≤ u → u < cph ρ φ α β (2 * k) + dlmin → O u = false) ∧
    -- req↓ and ack↑ only after the whole rise window
    cph ρ φ α β (2 * k) + dlmax ≤ φ k ∧ cph ρ φ α β (2 * k) + dlmax ≤ α k ∧
    -- node fall: after both, and still high until then
    cph ρ φ α β (2 * k + 1) = max (φ k) (α k) ∧
    (∀ u, cph ρ φ α β (2 * k + 1) ≤ u → u < cph ρ φ α β (2 * k + 1) + dlmin → O u = true) ∧
    -- next req↑ and ack↓ only after the whole fall window
    cph ρ φ α β (2 * k + 1) + dlmax ≤ ρ (k + 1) ∧ cph ρ φ α β (2 * k + 1) + dlmax ≤ β k := by
  have hl := CElemTiming.winDelay_le C.H_CTL.H_LUT
  have hEL := C.H_ENV_LATENCY
  have hfa := fall_after C k
  have har := ack_rise_after C k
  have R0 := (ctl_gap C (2 * k)).1
  have R1 := (ctl_gap C (2 * k + 1)).1
  have rr : cph ρ φ α β (2 * k + 1) + dlmin + E ≤ ρ (k + 1) := by
    obtain ⟨u, hu1, hu2, hu3⟩ := C.H_SND_RISE k
    have := obs_late C (2 * k + 1) u hu1 (by rw [Vph_o]; exact hu3); omega
  have bb : cph ρ φ α β (2 * k + 1) + dlmin + E ≤ β k := by
    obtain ⟨u, hu1, hu2, hu3⟩ := C.H_RCV_FALL k
    have := obs_late C (2 * k + 1) u hu1 (by rw [Vph_o]; exact hu3); omega
  have ff : cph ρ φ α β (2 * k) + dlmin + E ≤ φ k := by
    obtain ⟨u, hu1, hu2, hu3⟩ := C.H_SND_FALL k
    have := obs_late C (2 * k) u hu1 (by rw [Vph_e]; exact hu3); omega
  refine ⟨by rw [cph_e]; exact Nat.le_max_left _ _, by rw [cph_e]; exact Nat.le_max_right _ _,
    fun u h1 h2 => ?_, by omega, by omega, cph_o ρ φ α β k, fun u h1 h2 => ?_, by omega, by omega⟩
  · have := R0 u h1 h2; rwa [Vph_e] at this
  · have := R1 u h1 h2; rwa [Vph_o] at this

/-- **Timed refines untimed, token by token.** For every token, the timed
stage's events occur in the order of `timed_order`, and the corresponding
word of 6b's model (`send gate`, then `send recv` if `req↓` is no later than
`ack↑`, else `recv send`, then `gate recv`) is a run from reset to reset;
iterating gives a run of `2k` sends and `2k` receives for the first `k`
tokens. -/
theorem timed_refines (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) (k : Nat) :
    cph ρ φ α β (2 * k) + dlmax ≤ min (φ k) (α k) ∧
    cph ρ φ α β (2 * k + 1) + dlmax ≤ min (ρ (k + 1)) (β k) ∧
    (∀ s r, LinkHandshake.Reach 1 LinkHandshake.reset s r →
      LinkHandshake.Reach 1 LinkHandshake.reset (s + 2) (r + 2)) ∧
    LinkHandshake.Reach 1 LinkHandshake.reset (2 * (k + 1)) (2 * (k + 1)) := by
  have o := timed_order C k
  refine ⟨by omega, by omega, fun s r h => token_cycle (decide (φ k ≤ α k)) h,
    timed_refines_run (k + 1)⟩

end order

end Formal.Cells.LinkTimed
