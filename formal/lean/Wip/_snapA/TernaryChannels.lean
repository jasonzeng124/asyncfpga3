import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Formal.Core.Ternary
import Formal.Core.Delay.Pure
import Formal.Core.Delay.Inertial
import Formal.Core.Trace.Discrete
import Formal.Core.Discretize

/-!
# Formal.Core.TernaryChannels — ternary simulation is sound for the Core/Delay channels

Probe TernSound (shard A). Closes the gap the audit found in `Ternary.lean`:
there `soundA`/`noGlitchA`/`settleB` are proved for the discrete-time class
`Ternary.Causal` (time `ℕ`), and only GMW ⊆ `Causal` (`gmw_causal`) was
proved; "transport and inertial are instances" was prose.

**The literal claim is a type mismatch.** The transport channel
`DelayPure.Chan` and the inertial channels `DelayInertial.InertialRD` /
`BoundedInertial` are relations on continuous-time signals `ℝ → Bool`;
`Ternary.Causal` is a predicate on `ℕ`-indexed sequences. A continuous
behaviour is an instance of `Causal` only after a choice of discrete time.
This file gives the three honest readings, all proved:

1. **Continuous time, directly** (§2–§4). `RCausal N c σ δ` is the real-time
   analogue of `Causal`: from time 0 on, each node value is the Boolean gate
   function of input/node samples taken at least `δ` earlier. We reprove
   ternary soundness for it (`rsound_postfix`, `rsoundA`, `rnoGlitchA`; the
   induction is on `⌊s/δ⌋`, so `δ > 0` is used), and settling
   (`rsettleB`, `rsettleB_value`) under `SettlesWithin D`, a hypothesis
   **weaker than `Stale`** that both channel kinds satisfy. Then:
   * `chan_readsPast`, `chan_settles`: `Chan lo hi` reads the past by `≥ lo`
     and settles within `hi`;
   * `inertialRD_readsPast`, `inertialRD_settles`: `InertialRD ρ Δ` reads the
     past by `≥ Δ` and settles within `Δ` (for **every** `ρ`);
     `boundedInertial_*` likewise with `[lo, hi]`;
   * `rcausal_of_nodeChan`: a network each of whose nodes is a zero-delay
     gate followed by one of these channels, with every lower delay bound
     `≥ δ`, is `RCausal δ` (mixtures allowed, node by node). A routed wire is a
     node whose gate is a buffer, so "gate and wire delays" = one node each.
   * **Corollaries** `ternary_noGlitch_channels`, `ternary_settle_channels`.
2. **Discrete transport** (§5). `causal_of_transport`, `stale_of_transport`:
   if every node is a discrete `TraceDiscrete.Transport lo hi` channel of its
   excitation with `1 ≤ lo` (and `hi ≤ D`), the behaviour is literally
   `Ternary.Causal` (and `Ternary.Stale D`), so the original `soundA` /
   `settleB` apply verbatim.
3. **Sampling** (§6). `causal_of_sample`: grid samples of continuous `Chan`
   behaviours are literally `Ternary.Causal` when each node's excitation is
   `Discretize.Sep q` and `AtRest` and `L * q ≤ lo` with `1 ≤ L`
   (via `Discretize.chan_sample`). Without separation they need not be:
   `sample_not_causal` (a sub-quantum input pulse, delayed by a non-integral
   delay, appears at a grid point of the output and at no grid point of the
   input), and the samples then violate the conclusion of `noGlitchA`.

**Counterexamples (the extra hypothesis is necessary).** With lower delay bound
0 soundness fails for both channel kinds: `zero_delay_chan_unsound`,
`zero_delay_inertial_unsound` (a buffer fed back to itself with zero delay can
switch spontaneously although algorithm A says it holds). So the precise
statement is "sound for transport and inertial channels whose lower delay
bound is `≥ δ` for one `δ > 0` common to all nodes" — for finitely many nodes,
"every lower bound is positive" (`ternary_noGlitch_channels_pos`).

Not covered: zero-delay nodes inside an acyclic part (they would be sound
too, but `RCausal` asks every node for `δ > 0`; fold a zero-delay gate into
the channel of its reader instead); `Involution` channels (no instance in the
build); non-finitely-variable inputs are allowed (nothing here needs finite
variability).
-/

namespace Formal.Core.TernaryChannels

open Formal.Core
open Formal.Core.Ternary

/-! ## 1. Two channel properties -/

/-- Every output value is an input value from at least `δ` earlier. -/
def ReadsPast (δ : ℝ) (x y : ℝ → Bool) : Prop := ∀ s, ∃ τ, τ ≤ s - δ ∧ y s = x τ

/-- If the input is constantly `v` from `T` on, the output is `v` from `T + D` on. -/
def SettlesWithin (D : ℝ) (x y : ℝ → Bool) : Prop :=
  ∀ (T : ℝ) (v : Bool), (∀ t, T ≤ t → x t = v) → ∀ s, T + D ≤ s → y s = v

theorem readsPast_mono {δ δ' : ℝ} {x y : ℝ → Bool} (h : δ' ≤ δ) (hr : ReadsPast δ x y) :
    ReadsPast δ' x y := fun s => by
  obtain ⟨τ, hτ, e⟩ := hr s
  exact ⟨τ, by linarith, e⟩

theorem settlesWithin_mono {D D' : ℝ} {x y : ℝ → Bool} (h : D ≤ D') (hs : SettlesWithin D x y) :
    SettlesWithin D' x y := fun T v hx s hsT => hs T v hx s (by linarith)

/-- Transport `[lo, hi]` reads the past by at least `lo`. -/
theorem chan_readsPast {lo hi : ℝ} {x y : ℝ → Bool} (h : DelayPure.Chan lo hi x y) :
    ReadsPast lo x y := by
  obtain ⟨r, hr⟩ := h
  exact fun s => ⟨r.σ s, r.le s, hr s⟩

/-- Transport `[lo, hi]` settles within `hi`. -/
theorem chan_settles {lo hi : ℝ} {x y : ℝ → Bool} (h : DelayPure.Chan lo hi x y) :
    SettlesWithin hi x y := by
  obtain ⟨r, hr⟩ := h
  intro T v hx s hs
  rw [hr s]
  exact hx _ (by have := r.ge s; linarith)

/-- Inertial (window `ρ`, delay `Δ`) reads the past by at least `Δ`, for any `ρ`. -/
theorem inertialRD_readsPast {ρ Δ : ℝ} {x y : ℝ → Bool} (h : DelayInertial.InertialRD ρ Δ x y) :
    ReadsPast Δ x y := by
  intro s
  obtain ⟨τ, hτ, _, hb, _⟩ := h (s - Δ)
  have hb' : y (s - Δ + Δ) = x τ := hb
  rw [sub_add_cancel] at hb'
  exact ⟨τ, hτ, hb'⟩

/-- Inertial (window `ρ`, delay `Δ`) settles within `Δ`, for any `ρ`: once the
input is constant, the latest stable point is the current time. -/
theorem inertialRD_settles {ρ Δ : ℝ} {x y : ℝ → Bool} (h : DelayInertial.InertialRD ρ Δ x y) :
    SettlesWithin Δ x y := by
  intro T v hx s hs
  obtain ⟨τ, hτ, _, hb, hmax⟩ := h (s - Δ)
  have hb' : y (s - Δ + Δ) = x τ := hb
  rw [sub_add_cancel] at hb'
  rw [hb']
  have hu : T ≤ s - Δ := by linarith
  by_cases hτT : T ≤ τ
  · exact hx τ hτT
  · have hlt : τ < s - Δ := by linarith
    have hst : DelayInertial.Stable x (s - Δ) ρ := fun w h1 _ => by
      rw [hx w (by linarith), hx _ hu]
    rw [← hmax (s - Δ) hlt le_rfl hst]
    exact hx _ hu

theorem boundedInertial_readsPast {ρ lo hi : ℝ} {x y : ℝ → Bool}
    (h : DelayInertial.BoundedInertial ρ lo hi x y) : ReadsPast lo x y := by
  obtain ⟨Δ, hlo, _, hi'⟩ := h
  exact readsPast_mono hlo (inertialRD_readsPast hi')

theorem boundedInertial_settles {ρ lo hi : ℝ} {x y : ℝ → Bool}
    (h : DelayInertial.BoundedInertial ρ lo hi x y) : SettlesWithin hi x y := by
  obtain ⟨Δ, _, hhi, hi'⟩ := h
  exact settlesWithin_mono hhi (inertialRD_settles hi')

/-- The channel kinds of `Core/Delay` a node may use: transport `[lo, hi]` or
(bounded) inertial with window `ρ` and delay in `[lo, hi]`, with `δ ≤ lo` and
`hi ≤ D`. (Fixed inertial `InertialRD ρ Δ` is `BoundedInertial ρ Δ Δ`,
`inertialRD_nodeChan`.) -/
def NodeChan (δ D : ℝ) (x y : ℝ → Bool) : Prop :=
  (∃ lo hi, δ ≤ lo ∧ hi ≤ D ∧ DelayPure.Chan lo hi x y) ∨
  (∃ ρ lo hi, δ ≤ lo ∧ hi ≤ D ∧ DelayInertial.BoundedInertial ρ lo hi x y)

theorem chan_nodeChan {δ D lo hi : ℝ} {x y : ℝ → Bool} (h1 : δ ≤ lo) (h2 : hi ≤ D)
    (h : DelayPure.Chan lo hi x y) : NodeChan δ D x y := Or.inl ⟨lo, hi, h1, h2, h⟩

theorem inertialRD_nodeChan {δ D ρ Δ : ℝ} {x y : ℝ → Bool} (h1 : δ ≤ Δ) (h2 : Δ ≤ D)
    (h : DelayInertial.InertialRD ρ Δ x y) : NodeChan δ D x y :=
  Or.inr ⟨ρ, Δ, Δ, h1, h2, ⟨Δ, le_rfl, le_rfl, h⟩⟩

theorem nodeChan_readsPast {δ D : ℝ} {x y : ℝ → Bool} (h : NodeChan δ D x y) :
    ReadsPast δ x y := by
  rcases h with ⟨lo, hi, h1, _, h⟩ | ⟨ρ, lo, hi, h1, _, h⟩
  · exact readsPast_mono h1 (chan_readsPast h)
  · exact readsPast_mono h1 (boundedInertial_readsPast h)

theorem nodeChan_settles {δ D : ℝ} {x y : ℝ → Bool} (h : NodeChan δ D x y) :
    SettlesWithin D x y := by
  rcases h with ⟨lo, hi, _, h2, h⟩ | ⟨ρ, lo, hi, _, h2, h⟩
  · exact settlesWithin_mono h2 (chan_settles h)
  · exact settlesWithin_mono h2 (boundedInertial_settles h)

/-! ## 2. Real-time networks -/

section RealTime
variable {ι ν : Type}

/-- Real-time excitation of node `i`: its Boolean gate function of the current
input and node values. -/
def exc (N : Net ι ν) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool) (i : ν) : ℝ → Bool :=
  fun s => N.fb (c s) (σ s) i

/-- The waveform of node `i`. -/
def node (σ : ℝ → ν → Bool) (i : ν) : ℝ → Bool := fun s => σ s i

/-- **Real-time causal semantics with minimum delay `δ`** (continuous-time
analogue of `Ternary.Causal`): from time 0 on, each node value is its Boolean
gate function of samples of each input and each node taken at least `δ`
earlier, a different time per wire allowed. Before time 0 nothing is assumed
here (the initial state is a separate hypothesis). -/
def RCausal (N : Net ι ν) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool) (δ : ℝ) : Prop :=
  ∀ s i, 0 ≤ s → ∃ (τi : ι → ℝ) (τn : ν → ℝ), (∀ x, τi x ≤ s - δ) ∧ (∀ j, τn j ≤ s - δ) ∧
    σ s i = N.fb (fun x => c (τi x) x) (fun j => σ (τn j) j) i

theorem rcausal_of_readsPast {N : Net ι ν} {c : ℝ → ι → Bool} {σ : ℝ → ν → Bool} {δ : ℝ}
    (h : ∀ i, ReadsPast δ (exc N c σ i) (node σ i)) : RCausal N c σ δ := by
  intro s i _
  obtain ⟨τ, hτ, e⟩ := h i s
  exact ⟨fun _ => τ, fun _ => τ, fun _ => hτ, fun _ => hτ, e⟩

/-- **Every network whose nodes use `Core/Delay` transport or inertial
channels with lower bounds `≥ δ` is `RCausal δ`.** -/
theorem rcausal_of_nodeChan {N : Net ι ν} {c : ℝ → ι → Bool} {σ : ℝ → ν → Bool} {δ D : ℝ}
    (h : ∀ i, NodeChan δ D (exc N c σ i) (node σ i)) : RCausal N c σ δ :=
  rcausal_of_readsPast fun i => nodeChan_readsPast (h i)

/-- GMW-like sanity: `RCausal` is monotone in `δ`. -/
theorem rcausal_mono {N : Net ι ν} {c : ℝ → ι → Bool} {σ : ℝ → ν → Bool} {δ δ' : ℝ}
    (h : δ' ≤ δ) (hσ : RCausal N c σ δ) : RCausal N c σ δ' := by
  intro s i hs
  obtain ⟨τi, τn, h1, h2, e⟩ := hσ s i hs
  exact ⟨τi, τn, fun x => by have := h1 x; linarith, fun j => by have := h2 j; linarith, e⟩

/-! ## 3. Soundness in continuous time -/

theorem exists_mul_gt {D : ℝ} (hD : 0 < D) (x : ℝ) : ∃ n : ℕ, x < n * D := by
  obtain ⟨n, hn⟩ := Archimedean.arch x hD
  refine ⟨n + 1, ?_⟩
  rw [nsmul_eq_mul] at hn
  push_cast
  linarith

/-- **Soundness of post-fixed points, continuous time.** As
`Ternary.sound_postfix`, for every `RCausal δ` behaviour with `δ > 0`, the
initial state being covered at all negative times. -/
theorem rsound_postfix (N : Net ι ν) {u : ι → K3} {p : ν → K3} (hp : VLe p (N.F u p))
    {c : ℝ → ι → Bool} {σ : ℝ → ν → Bool} (hc : ∀ s, VLe u (vb (c s)))
    {δ : ℝ} (hδ : 0 < δ) (hσ : RCausal N c σ δ) (h0 : ∀ s, s < 0 → VLe p (vb (σ s))) :
    ∀ s, VLe p (vb (σ s)) := by
  have key : ∀ n : ℕ, ∀ s, s < n * δ → VLe p (vb (σ s)) := by
    intro n
    induction n with
    | zero => intro s hs; exact h0 s (by simpa using hs)
    | succ n IH =>
      intro s hs
      by_cases hneg : s < 0
      · exact h0 s hneg
      · intro i
        obtain ⟨τi, τn, _, hτn, e⟩ := hσ s i (not_lt.mp hneg)
        show K3.Le (p i) (K3.ofBool (σ s i))
        rw [e]
        refine K3.le_trans (hp i) (N.cover ?_ ?_ i)
        · intro x; exact hc (τi x) x
        · intro j
          have h1 : ((n + 1 : ℕ) : ℝ) * δ = n * δ + δ := by push_cast; ring
          exact IH (τn j) (by have := hτn j; linarith) j
  intro s
  obtain ⟨n, hn⟩ := exists_mul_gt hδ s
  exact key n s hn

variable (N : Net ι ν) (l : List ν) (hl : ∀ i, i ∈ l)

include hl in
/-- **Algorithm A is sound in continuous time.** Inputs move, input by input,
between `a` and `b` in any way; the behaviour is `RCausal δ` with `δ > 0` and
equals `s0` before time 0. Then `resultA` covers every state at every real
time. -/
theorem rsoundA (a b : ι → Bool) (s0 : ν → Bool) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool)
    (hc : ∀ s x, c s x = a x ∨ c s x = b x) {δ : ℝ} (hδ : 0 < δ) (hσ : RCausal N c σ δ)
    (h0 : ∀ s, s < 0 → σ s = s0) : ∀ s, VLe (resultA N l a b s0) (vb (σ s)) :=
  rsound_postfix N (resultA_postfix N l hl a b s0) (fun s => hull_le (hc s)) hδ hσ
    (fun s hs => by rw [h0 s hs]; exact resultA_le_start N l a b s0)

include hl in
/-- **No glitch, continuous time.** -/
theorem rnoGlitchA (a b : ι → Bool) (s0 : ν → Bool) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool)
    (hc : ∀ s x, c s x = a x ∨ c s x = b x) {δ : ℝ} (hδ : 0 < δ) (hσ : RCausal N c σ δ)
    (h0 : ∀ s, s < 0 → σ s = s0) (i : ν) (v : Bool) (hv : resultA N l a b s0 i = K3.ofBool v) :
    ∀ s, σ s i = v := by
  intro s
  have h := rsoundA N l hl a b s0 c σ hc hδ hσ h0 s i
  rw [hv] at h
  exact K3.ofBool_inj.mp (K3.ofBool_le_iff.mp h)

/-- A value below a Boolean, read off its binary refinements. -/
theorem le_ofBool_of {w : K3} {x : Bool} (h : ∀ v, w = K3.ofBool v → x = v) :
    K3.Le w (K3.ofBool x) := by
  cases w with
  | zero => rw [h false rfl]; exact K3.le_refl _
  | one => rw [h true rfl]; exact K3.le_refl _
  | X => exact K3.X_le _

include hl in
/-- **Settling (algorithm B), continuous time.** Inputs move between `a` and
`b` until `T0` and equal `b` from `T0` on; the behaviour is `RCausal δ`
(`δ > 0`), starts at `s0`, and every node settles within `D ≥ 0`
(`SettlesWithin D` of its excitation; this replaces `Ternary.Stale`, which
inertial channels do not satisfy). Then the `k`-th B-iterate covers every
state from `T0 + k·D` on. -/
theorem rsettleB (a b : ι → Bool) (s0 : ν → Bool) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool)
    (hc : ∀ s x, c s x = a x ∨ c s x = b x) (T0 : ℝ) (hb : ∀ s, T0 ≤ s → c s = b)
    {δ : ℝ} (hδ : 0 < δ) (hσ : RCausal N c σ δ) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ i, SettlesWithin D (exc N c σ i) (node σ i)) (h0 : ∀ s, s < 0 → σ s = s0) :
    ∀ (k : ℕ) (s : ℝ), T0 + k * D ≤ s → VLe (iterB N b (resultA N l a b s0) k) (vb (σ s)) := by
  intro k
  induction k with
  | zero => intro s _; exact rsoundA N l hl a b s0 c σ hc hδ hσ h0 s
  | succ k IH =>
    intro s hs i
    show K3.Le (N.F (vb b) (iterB N b (resultA N l a b s0) k) i) (K3.ofBool (σ s i))
    apply le_ofBool_of
    intro v hv
    have hkD : (0 : ℝ) ≤ k * D := mul_nonneg (Nat.cast_nonneg k) hD
    have hexc : ∀ t, T0 + k * D ≤ t → exc N c σ i t = v := by
      intro t ht
      have hcov := N.cover (u := vb b) (t := iterB N b (resultA N l a b s0) k) (a := c t)
        (s := σ t) (by rw [hb t (by linarith)]; exact vle_refl _) (IH t ht) i
      rw [hv] at hcov
      exact K3.ofBool_inj.mp (K3.ofBool_le_iff.mp hcov)
    have h1 : ((k + 1 : ℕ) : ℝ) * D = k * D + D := by push_cast; ring
    exact hS i (T0 + k * D) v hexc s (by linarith)

include hl in
/-- A node binary in the `k`-th B-iterate has settled to that value by `T0 + k·D`. -/
theorem rsettleB_value (a b : ι → Bool) (s0 : ν → Bool) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool)
    (hc : ∀ s x, c s x = a x ∨ c s x = b x) (T0 : ℝ) (hb : ∀ s, T0 ≤ s → c s = b)
    {δ : ℝ} (hδ : 0 < δ) (hσ : RCausal N c σ δ) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ i, SettlesWithin D (exc N c σ i) (node σ i)) (h0 : ∀ s, s < 0 → σ s = s0)
    (k : ℕ) (i : ν) (v : Bool) (hv : iterB N b (resultA N l a b s0) k i = K3.ofBool v) :
    ∀ s, T0 + k * D ≤ s → σ s i = v := by
  intro s hs
  have h := rsettleB N l hl a b s0 c σ hc T0 hb hδ hσ hD hS h0 k s hs i
  rw [hv] at h
  exact K3.ofBool_inj.mp (K3.ofBool_le_iff.mp h)

/-! ## 4. Corollaries: networks of transport / inertial channels -/

include hl in
/-- **Ternary simulation (algorithm A) is sound for networks of `Core/Delay`
transport and inertial channels.** Every node is a zero-delay gate (`N.fb`)
followed by a transport `Chan lo hi` or an inertial `BoundedInertial ρ lo hi`
channel (chosen per node) with `lo ≥ δ > 0`; the inputs move between `a` and
`b`; the state is `s0` before time 0. A node binary in `resultA` never
changes. -/
theorem ternary_noGlitch_channels (a b : ι → Bool) (s0 : ν → Bool)
    (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool) (hc : ∀ s x, c s x = a x ∨ c s x = b x)
    {δ D : ℝ} (hδ : 0 < δ) (hch : ∀ i, NodeChan δ D (exc N c σ i) (node σ i))
    (h0 : ∀ s, s < 0 → σ s = s0) (i : ν) (v : Bool) (hv : resultA N l a b s0 i = K3.ofBool v) :
    ∀ s, σ s i = v :=
  rnoGlitchA N l hl a b s0 c σ hc hδ (rcausal_of_nodeChan hch) h0 i v hv

include hl in
/-- **…and algorithm B is sound for settling**: inputs equal `b` from `T0`,
every upper delay bound is `≤ D`; a node binary in `resultB` equals that value
from `T0 + |ν|·D` on. -/
theorem ternary_settle_channels (a b : ι → Bool) (s0 : ν → Bool)
    (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool) (hc : ∀ s x, c s x = a x ∨ c s x = b x)
    (T0 : ℝ) (hb : ∀ s, T0 ≤ s → c s = b)
    {δ D : ℝ} (hδ : 0 < δ) (hch : ∀ i, NodeChan δ D (exc N c σ i) (node σ i))
    (h0 : ∀ s, s < 0 → σ s = s0) (i : ν) (v : Bool) (hv : resultB N l a b s0 i = K3.ofBool v) :
    ∀ s, T0 + l.length * D ≤ s → σ s i = v := by
  have hD : 0 ≤ D := by
    -- `NodeChan δ D` at any node forces `δ ≤ lo ≤ hi ≤ D` up to the band
    -- being nonempty; we do not need that: use the band of node `i`.
    rcases hch i with ⟨lo, hi, h1, h2, ⟨r, _⟩⟩ | ⟨ρ, lo, hi, h1, h2, ⟨Δ, h3, h4, _⟩⟩
    · have := r.ge 0; have := r.le 0; linarith
    · linarith
  exact rsettleB_value N l hl a b s0 c σ hc T0 hb hδ (rcausal_of_nodeChan hch) hD
    (fun j => nodeChan_settles (hch j)) h0 l.length i v hv

include hl in
/-- The same with only "every lower bound is positive" (per node), using that
there are finitely many nodes (`l` enumerates them) to get a common `δ`. -/
theorem ternary_noGlitch_channels_pos (a b : ι → Bool) (s0 : ν → Bool)
    (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool) (hc : ∀ s x, c s x = a x ∨ c s x = b x)
    (δn : ν → ℝ) (hδn : ∀ i, 0 < δn i) {D : ℝ}
    (hch : ∀ i, NodeChan (δn i) D (exc N c σ i) (node σ i))
    (h0 : ∀ s, s < 0 → σ s = s0) (i : ν) (v : Bool) (hv : resultA N l a b s0 i = K3.ofBool v) :
    ∀ s, σ s i = v := by
  -- the minimum of `δn` over `l` (and `1`)
  let m : ℝ := l.foldr (fun j acc => min (δn j) acc) 1
  have hm : 0 < m ∧ ∀ j ∈ l, m ≤ δn j := by
    simp only [m]
    induction l with
    | nil => exact ⟨one_pos, fun _ h => absurd h (List.not_mem_nil)⟩
    | cons j l IH =>
      obtain ⟨h1, h2⟩ := IH
      refine ⟨lt_min (hδn j) h1, fun k hk => ?_⟩
      rcases List.mem_cons.mp hk with e | e
      · subst e; exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (h2 k e)
  have hR : RCausal N c σ m :=
    rcausal_of_readsPast fun j => readsPast_mono (hm.2 j (hl j)) (nodeChan_readsPast (hch j))
  exact rnoGlitchA N l hl a b s0 c σ hc hm.1 hR h0 i v hv

end RealTime

/-! ## 5. Discrete transport is literally `Ternary.Causal` -/

section Discrete
variable {ι ν : Type}

/-- Every network whose nodes are discrete transport channels
(`TraceDiscrete.Transport lo hi`, lower bound `≥ 1`) of their excitations is
`Ternary.Causal`, so `soundA`/`noGlitchA` apply verbatim. -/
theorem causal_of_transport (N : Net ι ν) (c : ℕ → ι → Bool) (σ : ℕ → ν → Bool)
    (lo hi : ν → ℕ) (hlo : ∀ i, 1 ≤ lo i)
    (h : ∀ i, TraceDiscrete.Transport (lo i) (hi i) (fun t => N.fb (c t) (σ t) i)
      (fun t => σ t i)) : Causal N c σ := by
  intro t i
  obtain ⟨f, hf, e⟩ := h i
  right
  have h1 := hf.le_late (t + 1)
  have h2 := hlo i
  have hle : f (t + 1) ≤ t := by omega
  exact ⟨fun _ => f (t + 1), fun _ => f (t + 1), fun _ => hle, fun _ => hle, e (t + 1)⟩

/-- …and `Ternary.Stale D` when every upper bound is `≤ D` (`D ≥ 1`), so
`settleB`/`settleResultB` apply verbatim. -/
theorem stale_of_transport (N : Net ι ν) (c : ℕ → ι → Bool) (σ : ℕ → ν → Bool)
    (lo hi : ν → ℕ) (hlo : ∀ i, 1 ≤ lo i) (D : ℕ) (hD : 1 ≤ D) (hhi : ∀ i, hi i ≤ D)
    (h : ∀ i, TraceDiscrete.Transport (lo i) (hi i) (fun t => N.fb (c t) (σ t) i)
      (fun t => σ t i)) : Stale N c σ D := by
  intro t i ht
  obtain ⟨f, hf, e⟩ := h i
  have h1 := hf.le_late t
  have h2 := hf.early_le t
  have h3 := hlo i
  have h4 := hhi i
  have hb : t - D ≤ f t ∧ f t < t := ⟨by omega, by omega⟩
  exact ⟨fun _ => f t, fun _ => f t, fun _ => hb, fun _ => hb, e t⟩

end Discrete

/-! ## 6. Sampling continuous transport behaviours -/

section Sample
variable {ι ν : Type}

/-- **Grid samples of continuous transport behaviours are `Ternary.Causal`**,
when every node excitation is separated by one quantum and at rest before 0
(`Discretize.chan_sample`) and every lower bound is at least one quantum
(`1 ≤ L i`, `L i * q ≤ lo i`). -/
theorem causal_of_sample (N : Net ι ν) (c : ℝ → ι → Bool) (σ : ℝ → ν → Bool)
    {q : ℝ} (hq : 0 < q) (lo hi : ν → ℝ) (L H : ν → ℕ) (hL1 : ∀ i, 1 ≤ L i)
    (hL : ∀ i, (L i : ℝ) * q ≤ lo i) (hH : ∀ i, hi i ≤ (H i : ℝ) * q)
    (hch : ∀ i, DelayPure.Chan (lo i) (hi i) (exc N c σ i) (node σ i))
    (hsep : ∀ i, Discretize.Sep q (exc N c σ i)) (hrest : ∀ i, Discretize.AtRest (exc N c σ i)) :
    Causal N (Discretize.sample q c) (Discretize.sample q σ) :=
  causal_of_transport N _ _ L H hL1 fun i =>
    Discretize.chan_sample hq (hL i) (hH i) (hch i) (hsep i) (hrest i)

/-- One input, one node: a buffer of the input. -/
def bufNet : Net Unit Unit where
  fb a _ _ := a ()
  F u _ _ := u ()
  mono _ _ _ _ hu _ _ := hu ()
  ext _ _ _ := rfl

/-- A sub-quantum input pulse on `[1/4, 3/4)`. -/
noncomputable def runt (s : ℝ) : Bool := decide (1 / 4 ≤ s ∧ s < 3 / 4)

theorem runt_nat (k : ℕ) : runt ((k : ℝ) * 1) = false := by
  unfold runt
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; norm_num
  · have : (1 : ℝ) ≤ k := by exact_mod_cast h
    simp only [mul_one, decide_eq_false_iff_not, not_and, not_lt]
    intro _; linarith

/-- **Without separation, samples are not `Causal`.** The buffer's output is
the runt delayed by `3/2` (a `Chan 1 2` behaviour, lower bound one quantum),
but on the grid `q = 1` the input samples are all `false` while the output
sample at 2 is `true`. The samples even violate the conclusion of `noGlitchA`
(algorithm A with constant inputs `false` says the node is `0` for ever). -/
theorem sample_not_causal :
    let c : ℝ → Unit → Bool := fun s _ => runt s
    let σ : ℝ → Unit → Bool := fun s _ => runt (s - 3 / 2)
    (∀ i, DelayPure.Chan 1 2 (exc bufNet c σ i) (node σ i)) ∧
    ¬ Causal bufNet (Discretize.sample 1 c) (Discretize.sample 1 σ) ∧
    (∀ t x, Discretize.sample 1 c t x = false) ∧
    resultA bufNet [()] (fun _ => false) (fun _ => false) (fun _ => false) () = K3.zero ∧
    Discretize.sample 1 σ 0 = (fun _ => false) ∧ Discretize.sample 1 σ 2 () = true := by
  intro c σ
  have hin : ∀ t x, Discretize.sample 1 c t x = false := fun t _ => runt_nat t
  have h2 : Discretize.sample 1 σ 2 () = true := by
    show runt ((2 : ℕ) * 1 - 3 / 2) = true
    unfold runt; norm_num
  have h1 : Discretize.sample 1 σ 1 () = false := by
    show runt ((1 : ℕ) * 1 - 3 / 2) = false
    unfold runt; norm_num
  refine ⟨fun i => ?_, fun hC => ?_, hin, by decide, ?_, h2⟩
  · exact DelayPure.chan_shift (x := fun s => runt s) (by norm_num) (by norm_num)
  · rcases hC 1 () with h | ⟨τi, _, _, _, h⟩
    · rw [h2, h1] at h; exact Bool.noConfusion h
    · rw [h2] at h
      have : bufNet.fb (fun x => Discretize.sample 1 c (τi x) x) _ () =
          Discretize.sample 1 c (τi ()) () := rfl
      rw [this, hin] at h
      exact Bool.noConfusion h
  · funext _
    show runt ((0 : ℕ) * 1 - 3 / 2) = false
    unfold runt; norm_num

end Sample

/-! ## 7. Zero lower delay bound: soundness fails -/

/-- One node, a buffer of itself (no inputs used). -/
def loopNet : Net Unit Unit where
  fb _ s i := s i
  F _ t i := t i
  mono _ _ _ _ _ ht := ht
  ext _ _ _ := rfl

/-- A spontaneous rise at time 1. -/
noncomputable def stepSig (s : ℝ) : Bool := decide (1 ≤ s)

theorem loop_resultA :
    resultA loopNet [()] (fun _ => false) (fun _ => false) (fun _ => false) () = K3.zero := by
  decide

/-- **Transport with lower bound 0 is unsound.** For every `hi ≥ 0` the
self-looped buffer through `Chan 0 hi` may rise spontaneously at time 1,
although it starts at 0, the input never changes, and algorithm A gives `0`. -/
theorem zero_delay_chan_unsound {hi : ℝ} (hhi : 0 ≤ hi) :
    (∀ i, DelayPure.Chan 0 hi (exc loopNet (fun _ _ => false) (fun s _ => stepSig s) i)
      (node (fun s _ => stepSig s) i)) ∧
    (∀ s : ℝ, s < 0 → (fun _ => stepSig s) = fun (_ : Unit) => false) ∧
    resultA loopNet [()] (fun _ => false) (fun _ => false) (fun _ => false) () = K3.zero ∧
    stepSig 1 = true := by
  refine ⟨fun i => ?_, fun s hs => ?_, loop_resultA, by unfold stepSig; norm_num⟩
  · have := DelayPure.chan_shift (le_refl (0 : ℝ)) hhi (fun s => stepSig s)
    simpa [exc, node, loopNet] using this
  · funext _
    unfold stepSig
    simp only [decide_eq_false_iff_not, not_le]
    linarith

theorem noShort_stepSig (ρ : ℝ) : DelayInertial.NoShort ρ stepSig := by
  intro u
  by_cases hu : 1 ≤ u
  · refine ⟨1, hu, fun w h1 _ => ?_, fun v h1 _ => ?_⟩
    · unfold stepSig; simp [h1]
    · unfold stepSig; simp [h1]
  · push_neg at hu
    refine ⟨min u (1 - ρ), min_le_left _ _, fun w h1 h2 => ?_, fun v h1 h2 => ?_⟩
    · have : min u (1 - ρ) + ρ ≤ 1 := by have := min_le_right u (1 - ρ); linarith
      have hm : min u (1 - ρ) < 1 := lt_of_le_of_lt (min_le_left _ _) hu
      unfold stepSig
      simp only [decide_eq_decide]
      constructor <;> intro h <;> linarith
    · have hm : min u (1 - ρ) < 1 := lt_of_le_of_lt (min_le_left _ _) hu
      unfold stepSig
      simp only [decide_eq_decide]
      constructor <;> intro h <;> linarith

/-- **Inertial with delay 0 is unsound** (any rejection window `ρ`): the same
spontaneous rise is an `InertialRD ρ 0` behaviour of the self-loop. -/
theorem zero_delay_inertial_unsound (ρ : ℝ) :
    (∀ i, DelayInertial.InertialRD ρ 0 (exc loopNet (fun _ _ => false) (fun s _ => stepSig s) i)
      (node (fun s _ => stepSig s) i)) ∧
    resultA loopNet [()] (fun _ => false) (fun _ => false) (fun _ => false) () = K3.zero ∧
    stepSig 1 = true := by
  refine ⟨fun i => ?_, loop_resultA, by unfold stepSig; norm_num⟩
  show DelayInertial.Filt ρ (fun s => stepSig s) (fun u => stepSig (u + 0))
  simp only [add_zero]
  exact DelayInertial.filt_self_of_noShort (noShort_stepSig ρ)

end Formal.Core.TernaryChannels
