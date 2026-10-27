import Formal.Cells.WinFifoCausal
import Formal.Cells.PrelimCore
import Formal.Net.Prelim
import Formal.Core.LutTree

/-!
# Probe Bng: which delay channels give H_NO_REVERT, and what a LUT needs for it

Shard B. Note: `formal/notes/B-no-revert.md`. Core Lean only.

Bw/Bex (`WinFifo`, `WinFifoCausal`) reduced every B FIFO hypothesis to A's
window channel `Win` plus ONE extra hypothesis, H_NO_REVERT: inside one input
edge's uncertainty zone, once the output shows the new value it keeps it.
It has two forms:
* `WinFifo.NoRevert lo hi y c val` (zone form, needs the input's edges `c`);
* `WinFifoCausal.NoRevertI lo hi x y` (intrinsic form: if `x` holds `v` on
  `[a, b)` and `y` shows `v` at some `t1 ≥ a + lo`, `y` keeps `v` until
  `b + lo`). On a clean, spaced input it implies the zone form
  (`noRevert_of_I`).

## Part 1: channels

| channel | H_NO_REVERT? | theorem |
|---|---|---|
| B's inertial `CElemTiming.Inertial d` | **yes, for every input** (`NoRevertI d hi`) | `inertial_noRevertI` |
| Core's inertial `TraceDiscrete.inertial` (one tick late) | yes, every input | `coreInertial_noRevertI` |
| fixed transport `CElemTiming.Transport d` | yes, every input, band `[d, d]` | `transport_noRevertI` |
| fixed transport `d` read in a band `[lo, hi] ∋ d` | yes on clean spaced inputs; NOT for every input | `transport_noRevert`, `transport_band_needs_spread` |
| FIFO `PipeTimed.Ret` | yes on clean spaced inputs (Bw/Bex) | `no_revert_of_ret`, `noRevertI_of_ret` |
| Core bounded transport `TraceDiscrete.Transport lo hi` (monotone warp) | yes on clean spaced inputs (it is a `Ret`) | `coreTransport_ret`, `coreTransport_noRevert` |
| event channel (one ordered output event per input edge; the involution channel without cancellation) | yes under H_SPREAD_PULSE | `EventCh`, `eventCh_noRevert`, `invTimes_eventCh`, `eventCh_of_transport` |
| window `Win lo hi`, `hi ≥ lo + 2` | **no**, even on one isolated edge | `win_not_noRevert` |
| C's `Net.BoundedDelay lo hi`, `hi ≥ lo + 2` | **no**, same trace | `bdelay_glitch`, `bdelay_not_noRevert` |

Non-vacuity: `transport_witness` (Bw's witness is a transport, an event
channel and a constant-delay involution channel, all hypotheses met);
`PrelimCore.inertial_of_core` gives an `Inertial d` behaviour of every input.
The involution link is to a discrete event abstraction (`invTimes`); A's
real-valued `Core/Delay/Involution.lean` needs Mathlib, which is not built,
so the step "A's channel without cancellation = `invTimes`" is on paper.

## Part 2: the LUT mux tree (A's `Core.LutTree.PhysTree`)

* `kleene_revert`: H_SRAM + H_MUX_KLEENE with ONE moving pin making a
  monotone `old → X → new` transition do NOT give H_NO_REVERT at the root:
  a one-mux tree satisfying both shows `0, 1, 0, 1` at the root while its
  select is mid-rail. (The static case, equal old/new values, IS glitch free:
  A's `PhysTree.sic_glitch_free`.)
* `root_mono`: adding ONE per-mux hypothesis, **H_MUX_MONO** (if the Kleene
  value of a mux's delayed inputs progresses monotonically `A → X → B`, so does
  the node), gives the root a monotone `A → X → B` transition for a single
  moving pin whose select waveform is monotone (H_PIN_MONO), any per-mux and
  per-copy delays; or a constant if the LUT does not depend on the pin.
  `read_mono`: every fixed-threshold binary reading of such a waveform
  changes at most once (old to new), i.e. it is H_NO_REVERT in the binary
  sense. Non-vacuity: `exact_mux_mono` (A's exact Kleene timed tree meets
  H_MUX_MONO) and `root_mono_witness`.
-/

namespace Formal.Cells.NoRevert
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.WinFifo (Win Clean Spread NoRevert win_le no_revert_of_ret step glitch
  glitch_win dec_eq)
open Formal.Cells.WinFifoCausal (NoRevertI noRevertI_of_ret noRevert_of_I)

/-! ## 1. Channels that give H_NO_REVERT -/

/-- **B's inertial channel gives H_NO_REVERT for every input**, with `lo = d`
(any `hi`). Once the output shows `v` while the input has been `v` for `d`
ticks, a later output instant either copies `x (t - d) = v` (stable window)
or holds its previous value. -/
theorem inertial_noRevertI {d hi : Nat} {x y : Trace} (h : CElemTiming.Inertial d x y) :
    NoRevertI d hi x y := by
  intro a b v t1 t2 hab _ h1 h12 h2 hv
  have key : ∀ k, t1 + k < b + d → y (t1 + k) = v := by
    intro k
    induction k with
    | zero => intro _; simpa using hv
    | succ k ih =>
      intro hk
      have e := h (t1 + (k + 1) - d)
      rw [show t1 + (k + 1) - d + d = t1 + (k + 1) by omega] at e
      have hx : x (t1 + (k + 1) - d) = v := hab _ (by omega) (by omega)
      rw [e]
      split
      · exact hx
      · rw [show t1 + (k + 1) - 1 = t1 + k by omega]
        exact ih (by omega)
  have := key (t2 - t1) (by omega)
  rwa [show t1 + (t2 - t1) = t2 by omega] at this

/-- Core's inertial delay (`TraceDiscrete.inertial (d-1)`, one tick late,
`PrelimCore.coreInertial`) gives H_NO_REVERT for every input. -/
theorem coreInertial_noRevertI {d hi : Nat} (x : Trace) (hd : 1 ≤ d) :
    NoRevertI d hi x (PrelimCore.coreInertial d x) :=
  inertial_noRevertI (PrelimCore.inertial_of_core x hd)

/-- **Fixed transport gives H_NO_REVERT for every input**, band `[d, d]`. -/
theorem transport_noRevertI {d hi : Nat} {x y : Trace} (h : CElemTiming.Transport d x y) :
    NoRevertI d hi x y := by
  intro a b v t1 t2 hab _ h1 h12 h2 _
  have e := h (t2 - d)
  rw [show t2 - d + d = t2 by omega] at e
  rw [e]; exact hab _ (by omega) (by omega)

/-- Fixed transport `d` is a FIFO read for every band `[lo, hi] ∋ d`. -/
theorem transport_ret {lo d hi : Nat} {x y : Trace} (hl : lo ≤ d) (hh : d ≤ hi)
    (h : CElemTiming.Transport d x y) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  refine ⟨{ σ := fun t => t - d, lo := lo, hi := hi, mono := fun a b h => by omega,
            ge := fun t => by omega, le := fun t => by omega }, rfl, rfl, ?_⟩
  intro t ht
  have e := h (t - d)
  rw [show t - d + d = t by omega] at e
  exact e

/-- Fixed transport read in a band `[lo, hi] ∋ d`: H_NO_REVERT (both forms)
on every clean input with H_SPREAD_PULSE. -/
theorem transport_noRevert {lo d hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hl : lo ≤ d) (hh : d ≤ hi) (h : CElemTiming.Transport d x y)
    (hx : Clean x c val) (hsp : Spread lo hi c) :
    NoRevert lo hi y c val ∧ NoRevertI lo hi x y := by
  obtain ⟨r, rl, rh, hy⟩ := transport_ret hl hh h
  exact ⟨(no_revert_of_ret hx hsp r rl rh hy).2, noRevertI_of_ret hx hsp r rl rh hy⟩

/-- **The band form needs the spacing.** Transport `2` read in the band
`[0, 2]` violates `NoRevertI 0 2` on an input with a pulse just before the
held interval: the output replays that pulse inside the "zone". So for a band
wider than the channel's own delay, H_NO_REVERT is a property of channel AND
input (H_SPREAD_PULSE), not of the channel alone. -/
theorem transport_band_needs_spread :
    CElemTiming.Transport 2 (fun s => s != 1) (fun t => t != 3) ∧
      ¬ NoRevertI 0 2 (fun s => s != 1) (fun t => t != 3) := by
  refine ⟨fun t => ?_, fun h => ?_⟩
  · show (t + 2 != 3) = (t != 1)
    by_cases ht : t = 1
    · subst ht; rfl
    · simp
  · have := h 2 100 true 2 3 (fun s h1 _ => by
        show (s != 1) = true
        have : s ≠ 1 := by omega
        simp [this]) (by omega) (by omega) (by omega) (by omega) rfl
    exact absurd this (by decide)

/-- Core's bounded transport channel (a monotone warp, `Core.TraceDiscrete.Transport`)
is a FIFO read with the same band. -/
theorem coreTransport_ret {lo hi : Nat} {x y : Trace}
    (h : Formal.Core.TraceDiscrete.Transport lo hi x y) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  obtain ⟨f, hw, hf⟩ := h
  exact ⟨{ σ := f, lo := lo, hi := hi, mono := hw.mono, ge := hw.early_le, le := hw.le_late },
    rfl, rfl, fun t _ => hf t⟩

theorem coreTransport_noRevert {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (h : Formal.Core.TraceDiscrete.Transport lo hi x y)
    (hx : Clean x c val) (hsp : Spread lo hi c) :
    NoRevert lo hi y c val ∧ NoRevertI lo hi x y := by
  obtain ⟨r, rl, rh, hy⟩ := coreTransport_ret h
  exact ⟨(no_revert_of_ret hx hsp r rl rh hy).2, noRevertI_of_ret hx hsp r rl rh hy⟩

/-! ### Event channels (the involution channel without cancellation)

An event-based channel (involution, Függer et al.; A's
`Core/Delay/Involution.lean`) maps each input transition `j` to at most one
output transition at time `o j`; transitions that would not come after the
previous output transition annihilate in pairs. When none cancels, the
output shows `val j` from `o j` to `o (j + 1)`. -/

/-- **An event channel with one surviving, ordered output event per input
edge**, each inside its zone. -/
structure EventCh (lo hi : Nat) (c : Nat → Nat) (val : Nat → Bool) (y : Trace)
    (o : Nat → Nat) : Prop where
  zone : ∀ j, 1 ≤ j → c j + lo ≤ o j ∧ o j ≤ c j + hi
  ord : ∀ j, 1 ≤ j → o j < o (j + 1)
  out0 : ∀ t, hi ≤ t → t < o 1 → y t = val 0
  out : ∀ j t, 1 ≤ j → o j ≤ t → t < o (j + 1) → y t = val j

/-- **Event channels give H_NO_REVERT** under H_SPREAD_PULSE (the input's
values are not even used: the output is determined by the events). -/
theorem eventCh_noRevert {lo hi : Nat} {y : Trace} {c o : Nat → Nat} {val : Nat → Bool}
    (hsp : Spread lo hi c) (he : EventCh lo hi c val y o) :
    NoRevert lo hi y c val := by
  intro j t1 t2 hj h0 h1 h12 h2 hv
  have zj := he.zone j hj
  have zj1 := he.zone (j + 1) (by omega)
  have sj := hsp j hj
  -- `t2 < o (j+1)`
  have t2o : t2 < o (j + 1) := by omega
  -- before `o j`, the output shows `val (j-1)`
  have before : ∀ t, hi ≤ t → c j + lo ≤ t → t < o j → y t = val (j - 1) := by
    intro t ht1 ht2 ht3
    rcases Nat.lt_or_ge j 2 with h' | h'
    · have : j = 1 := by omega
      subst this; exact he.out0 t ht1 ht3
    · have zp := he.zone (j - 1) (by omega)
      have sp := hsp (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at sp
      exact he.out (j - 1) t (by omega) (by omega) (by rw [show j - 1 + 1 = j by omega]; exact ht3)
  by_cases ho : o j ≤ t2
  · exact he.out j t2 hj ho t2o
  · rw [before t2 (by omega) (by omega) (by omega)]
    rw [← before t1 h0 h1 (by omega)]; exact hv

/-- Output event times of a (discrete) involution channel without cancellation:
transition `j + 1` is scheduled `δ (j+1) T` after its input edge, where
`T = c (j+1) - o j` is the time since the previous output transition (A's
`Involution`: `δ↑`/`δ↓` chosen by the direction, here folded into `δ j`). -/
def invTimes (c : Nat → Nat) (δ : Nat → Int → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => c (j + 1) + δ (j + 1) ((c (j + 1) : Int) - (invTimes c δ j : Int))

/-- **Involution channel ⇒ event channel**: if every delay that occurs lies
in the band `[lo, hi]` (H_INV_BAND, what A's `up_bounds`/`down_bounds` give
under input separation) and the input satisfies H_SPREAD_PULSE, the scheduled
output transitions are strictly ordered (so none cancels, A's `cancel_iff`)
and each lies in its zone. With the involution output (`val j` from `o j`
to `o (j+1)`, H_INV_OUT) this is an `EventCh`, hence H_NO_REVERT. -/
theorem invTimes_eventCh {lo hi : Nat} {c : Nat → Nat} {val : Nat → Bool} {y : Trace}
    {δ : Nat → Int → Nat} (hsp : Spread lo hi c)
    (H_INV_BAND : ∀ j T, 1 ≤ j → lo ≤ δ j T ∧ δ j T ≤ hi)
    (H_INV_OUT0 : ∀ t, hi ≤ t → t < invTimes c δ 1 → y t = val 0)
    (H_INV_OUT : ∀ j t, 1 ≤ j → invTimes c δ j ≤ t → t < invTimes c δ (j + 1) → y t = val j) :
    EventCh lo hi c val y (invTimes c δ) := by
  have zone : ∀ j, 1 ≤ j → c j + lo ≤ invTimes c δ j ∧ invTimes c δ j ≤ c j + hi := by
    intro j hj
    cases j with
    | zero => omega
    | succ k =>
      have := H_INV_BAND (k + 1) ((c (k + 1) : Int) - (invTimes c δ k : Int)) hj
      simp only [invTimes]; omega
  refine ⟨zone, fun j hj => ?_, H_INV_OUT0, H_INV_OUT⟩
  have a := zone j hj; have b := zone (j + 1) (by omega); have s := hsp j hj
  omega

/-- Fixed transport on a clean input is an event channel (event `j` at
`c j + d`). -/
theorem eventCh_of_transport {lo d hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hl : lo ≤ d) (hh : d ≤ hi) (h : CElemTiming.Transport d x y) (hx : Clean x c val) :
    EventCh lo hi c val y (fun j => if j = 0 then 0 else c j + d) := by
  have ty : ∀ t, d ≤ t → y t = x (t - d) := fun t ht => by
    have e := h (t - d); rwa [show t - d + d = t by omega] at e
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun t ht h1 => ?_, fun j t hj h1 h2 => ?_⟩
  · simp only [show j ≠ 0 by omega, ↓reduceIte]; omega
  · simp only [show j ≠ 0 by omega, show j + 1 ≠ 0 by omega, ↓reduceIte]
    have := hx.mono j (j + 1) (by omega); omega
  · simp only [show (1 : Nat) ≠ 0 by omega, ↓reduceIte] at h1
    rw [ty t (by omega)]; exact hx.val 0 _ (by rw [hx.c0]; omega) (by rw [Nat.zero_add]; omega)
  · simp only [show j ≠ 0 by omega, show j + 1 ≠ 0 by omega, ↓reduceIte] at h1 h2
    rw [ty t (by omega)]; exact hx.val j _ (by omega) (by omega)

/-- Non-vacuity of `transport_noRevert`, `eventCh_noRevert` and
`invTimes_eventCh`: Bw's witness (`WinFifo.Wit`: edges 0, 200, 500, …, a
100-tick delay, band `[45, 124]`) is a fixed transport, an event channel, and
the involution channel with constant delay function `δ = 100`. -/
theorem transport_witness :
    CElemTiming.Transport 100 WinFifo.Wit.x WinFifo.Wit.y ∧ Clean WinFifo.Wit.x WinFifo.Wit.c WinFifo.Wit.val ∧
      Spread 45 124 WinFifo.Wit.c ∧
      EventCh 45 124 WinFifo.Wit.c WinFifo.Wit.val WinFifo.Wit.y (invTimes WinFifo.Wit.c (fun _ _ => 100)) := by
  have ht : CElemTiming.Transport 100 WinFifo.Wit.x WinFifo.Wit.y := fun t => by
    show WinFifo.Wit.x (t + 100 - 100) = _; rw [Nat.add_sub_cancel]
  have hx := WinFifo.Wit.x_clean
  have hs := WinFifo.Wit.wit.2.1
  have ev := eventCh_of_transport (lo := 45) (hi := 124) (by omega) (by omega) ht hx
  have eo : ∀ j, invTimes WinFifo.Wit.c (fun _ _ => 100) j = if j = 0 then 0 else WinFifo.Wit.c j + 100 := by
    intro j; cases j <;> simp [invTimes]
  refine ⟨ht, hx, hs, invTimes_eventCh hs (fun _ _ _ => ⟨by omega, by omega⟩) ?_ ?_⟩
  · intro t h1 h2; rw [eo] at h2; exact ev.out0 t h1 h2
  · intro j t hj h1 h2; rw [eo] at h1 h2; exact ev.out j t hj h1 h2

/-! ## 2. Channels that do NOT give H_NO_REVERT -/

/-- `c j = j * k`: edges every `k` ticks; value `false` then `true` forever. -/
def lin (k : Nat) (j : Nat) : Nat := j * k
def v01 (j : Nat) : Bool := j != 0

theorem step_clean {k : Nat} (hk : 1 ≤ k) : Clean (step k) (lin k) v01 where
  c0 := by simp [lin]
  mono := fun i j h => by simp only [lin]; exact Nat.mul_lt_mul_of_pos_right h (by omega)
  val := fun j s h1 h2 => by
    simp only [lin] at h1 h2
    simp only [step, v01]
    cases j with
    | zero => simp; omega
    | succ j =>
      have : k ≤ s := by have := Nat.le_mul_of_pos_left k (show 0 < j + 1 by omega); omega
      simp [this]

theorem step_spread {lo hi : Nat} : Spread lo hi (lin (hi + 1)) := by
  intro j _; simp only [lin, Nat.succ_mul]; omega

/-- **`Win` does not give H_NO_REVERT**, on a clean input with ONE edge
(every spacing holds). The glitch `1, 0, 1` of `win_glitch_not_fifo` lies in
the edge's zone. -/
theorem win_not_noRevert {lo hi : Nat} (h2 : lo + 2 ≤ hi) :
    Win lo hi (step (hi + 1)) (glitch (hi + 1) lo) ∧ Clean (step (hi + 1)) (lin (hi + 1)) v01 ∧
      Spread lo hi (lin (hi + 1)) ∧ ¬ NoRevert lo hi (glitch (hi + 1) lo) (lin (hi + 1)) v01 ∧
      ¬ NoRevertI lo hi (step (hi + 1)) (glitch (hi + 1) lo) := by
  have hc := step_clean (k := hi + 1) (by omega)
  have hs : Spread lo hi (lin (hi + 1)) := step_spread
  have hnr : ¬ NoRevert lo hi (glitch (hi + 1) lo) (lin (hi + 1)) v01 := by
    intro h
    have := h 1 (hi + 1 + lo) (hi + 1 + lo + 1) (Nat.le_refl _) (by omega)
      (by simp [lin]) (by omega) (by simp [lin]; omega)
      (by simp [glitch, v01])
    simp [glitch, v01] at this
  exact ⟨glitch_win h2, hc, hs, hnr, fun h => hnr (noRevert_of_I hc hs h)⟩

/-- The same glitch trace is a behaviour of C's bounded-delay channel
(`Net.BoundedDelay`: every output change copies an input value from
`d ∈ [lo, hi]` earlier; an input stable for `hi` ticks is copied). -/
theorem bdelay_glitch {lo hi c : Nat} (h2 : lo + 2 ≤ hi) (hc : 1 ≤ c) :
    Formal.Net.BoundedDelay lo hi (step c) (glitch c lo) := by
  constructor
  · intro t hch
    have pos : c + lo ≤ t + 1 := by
      apply Classical.byContradiction; intro hn
      apply hch; simp only [glitch]
      rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    by_cases hm : t + 1 = c + lo + 1
    · refine ⟨lo + 2, by omega, h2, by omega, ?_⟩
      simp only [glitch, step]; apply dec_eq; omega
    · refine ⟨lo, Nat.le_refl _, by omega, by omega, ?_⟩
      simp only [glitch, step]; apply dec_eq; omega
  · intro t ht hst
    simp only [glitch, step]
    by_cases htc : c ≤ t
    · have e := hst t (by omega) (Nat.le_refl _)
      simp only [step] at e
      have : c ≤ t - hi := by
        apply Classical.byContradiction; intro hn
        rw [decide_eq_true htc, decide_eq_false hn] at e; exact absurd e (by decide)
      apply dec_eq; omega
    · apply dec_eq; omega

/-- **C's `BoundedDelay` does not give H_NO_REVERT** either. -/
theorem bdelay_not_noRevert {lo hi : Nat} (h2 : lo + 2 ≤ hi) :
    Formal.Net.BoundedDelay lo hi (step (hi + 1)) (glitch (hi + 1) lo) ∧
      ¬ NoRevert lo hi (glitch (hi + 1) lo) (lin (hi + 1)) v01 :=
  ⟨bdelay_glitch h2 (by omega), (win_not_noRevert h2).2.2.2.1⟩

/-! ## 3. The LUT mux tree: what H_MUX_KLEENE gives, and what it needs

A's timed physical tree `Core.LutTree.PhysTree` (per-mux select and data
delays, per-copy input arrival, every node a K3 waveform, `X` = mid-rail).
A transition of a K3 waveform from `A` to `B` is **monotone** when it never
goes back: the waveform is `A …, X …, B …` (`Mono`). For `A ≠ B` this is the
K3 form of H_NO_REVERT, and every fixed-threshold binary reading of it
changes at most once (`read_mono`). -/

namespace Tree
open Formal.Core.LutTree
open Formal.Core.LutTree.K3 (ofBool Le)

abbrev K := Formal.Core.LutTree.K3

/-- Progress of a transition `A → B` between two instants: the earlier value
is still `A`, or the later one is already `B`, or both are mid-rail. -/
def Prog (A B a b : K) : Prop := a = A ∨ b = B ∨ (a = .X ∧ b = .X)

instance (A B a b : K) : Decidable (Prog A B a b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- **Monotone transition `A → B`** (K3 H_NO_REVERT). -/
def Mono (A B : K) (u : Time → K) : Prop := ∀ τ1 τ2, τ1 ≤ τ2 → Prog A B (u τ1) (u τ2)

theorem mono_shift {A B : K} {u : Time → K} (d : Time) (h : Mono A B u) :
    Mono A B (fun τ => u (τ - d)) := fun _ _ h12 => h _ _ (Int.sub_le_sub_right h12 d)

/-- Binary reading with a fixed threshold side: a mid-rail level reads `c`. -/
def rd (c : Bool) : K → Bool
  | .zero => false
  | .one => true
  | .X => c

theorem rd_step (A B c : Bool) (a b : K) (hAB : A ≠ B) (h : Prog (ofBool A) (ofBool B) a b) :
    (rd c a = B → rd c b = B) ∧ (rd c b = A → rd c a = A) := by
  revert hAB h
  cases A <;> cases B <;> cases c <;> cases a <;> cases b <;> decide

/-- **Binary H_NO_REVERT from a monotone K3 transition.** Every fixed-threshold
reading of a monotone `A → B` waveform (`A ≠ B`) is a single step: once it
reads `B` it keeps `B`, and once it has left `A` it never reads `A` again. -/
theorem read_mono {A B : Bool} (hAB : A ≠ B) {u : Time → K}
    (h : Mono (ofBool A) (ofBool B) u) (c : Bool) :
    ∀ τ1 τ2, τ1 ≤ τ2 → (rd c (u τ1) = B → rd c (u τ2) = B) ∧ (rd c (u τ2) = A → rd c (u τ1) = A) :=
  fun τ1 τ2 h12 => rd_step A B c _ _ hAB (h τ1 τ2 h12)

/-- One select step: a Kleene mux with constant legs maps a monotone select
transition `o → n` to a monotone output transition. -/
theorem sel_step (o n l0 l1 : Bool) (a b : K) (hon : o ≠ n)
    (h : Prog (ofBool o) (ofBool n) a b) :
    Prog (ofBool (if o then l1 else l0)) (ofBool (if n then l1 else l0))
      (kmux a (ofBool l0) (ofBool l1)) (kmux b (ofBool l0) (ofBool l1)) := by
  revert hon h
  cases o <;> cases n <;> cases l0 <;> cases l1 <;> cases a <;> cases b <;> decide

theorem kmux_same (s : K) (l : Bool) : kmux s (ofBool l) (ofBool l) = ofBool l := by
  cases s <;> cases l <;> decide

namespace PhysTree'
variable {n : Nat} (P : PhysTree n)

/-- The Kleene value of node `p`'s delayed inputs. -/
def kap (p : List Bool) (τ : Time) : K :=
  kmux (P.pin p.length (τ - P.dsel p)) (P.y (p ++ [false]) (τ - P.ddat p false))
    (P.y (p ++ [true]) (τ - P.ddat p true))

/-- **HYPOTHESIS H_MUX_MONO (one 2:1 mux).** If the Kleene value of a mux's
delayed select and data progresses monotonically from `A` to `B` (`A ≠ B`),
so does the node: no revert inside the mux (a mid-rail select between two
different legs moves the node monotonically, the restorer does not snap
back). A's exact Kleene tree meets it (`exact_mux_mono`); H_MUX_KLEENE alone
does not imply it (`kleene_revert`). -/
def H_mux_mono : Prop :=
  ∀ p : List Bool, p.length < n → ∀ A B : Bool, A ≠ B →
    Mono (ofBool A) (ofBool B) (kap P p) → Mono (ofBool A) (ofBool B) (P.y p)

/-- The INIT entry of the subtree at `p` under the steady pin levels `c`. -/
def val (c : Nat → Bool) (p : List Bool) : Bool := P.init (p ++ seg c p.length (n - p.length))

theorem val_cons (c : Nat → Bool) (p : List Bool) (h : p.length < n) :
    val P c p = val P c (p ++ [c p.length]) := by
  unfold val
  rw [show n - p.length = (n - (p.length + 1)) + 1 by omega]
  simp [seg, List.append_assoc]

theorem val_setb_gt (c : Nat → Bool) (i : Nat) (b : Bool) (p : List Bool) (h : i < p.length) :
    val P (setb c i b) p = val P c p := by
  unfold val; rw [seg_setb_gt c i b _ _ h]

theorem kleene_const (hm : P.H_mux_kleene) {p : List Bool} (hp : p.length < n) {v : Bool}
    {τ : Time} (h : kap P p τ = ofBool v) : P.y p τ = ofBool v := by
  have := hm p hp τ
  unfold kap at h; rw [h] at this; exact this.ofBool_eq

/-- The induction behind `root_mono`, one level at a time. -/
theorem claim (hs : P.H_sram) (hm : P.H_mux_kleene) (hmm : H_mux_mono P)
    (c : Nat → Bool) (i : Nat) (hi : i < n) (o nw : Bool) (hon : o ≠ nw)
    (hc : ∀ j, j ≠ i → j < n → ∀ τ, P.pin j τ = ofBool (c j))
    (hpin : Mono (ofBool o) (ofBool nw) (P.pin i)) :
    ∀ m (p : List Bool), p.length + m = n →
      (i < p.length → ∀ τ, P.y p τ = ofBool (val P c p)) ∧
      (p.length ≤ i →
        (val P (setb c i o) p = val P (setb c i nw) p → ∀ τ, P.y p τ = ofBool (val P (setb c i o) p)) ∧
        (val P (setb c i o) p ≠ val P (setb c i nw) p →
          Mono (ofBool (val P (setb c i o) p)) (ofBool (val P (setb c i nw) p)) (P.y p))) := by
  intro m
  induction m with
  | zero =>
    intro p hp
    refine ⟨fun _ τ => ?_, fun h => by omega⟩
    rw [hs p (by omega) τ]; unfold val; rw [show n - p.length = 0 by omega]; simp [seg]
  | succ m ih =>
    intro p hp
    have hL : p.length < n := by omega
    have ihb := fun b => ih (p ++ [b]) (by simp; omega)
    simp only [List.length_append, List.length_singleton] at ihb
    -- static select at level `p.length ≠ i`: the node reads child `c L`
    have static : p.length ≠ i → ∀ τ,
        kap P p τ = P.y (p ++ [c p.length]) (τ - P.ddat p (c p.length)) := by
      intro hne τ
      unfold kap; rw [hc p.length hne hL, kmux_ofBool]
      cases c p.length <;> rfl
    refine ⟨fun hgt τ => ?_, fun hle => ?_⟩
    · -- below the moving pin: constant
      have hk : kap P p τ = ofBool (val P c p) := by
        rw [static (by omega), (ihb (c p.length)).1 (by omega), ← val_cons P c p hL]
      exact kleene_const P hm hL hk
    · rcases Nat.lt_or_ge p.length i with hlt | hge
      · -- above the moving pin: the node follows one child through a static select
        have e : ∀ b : Bool, val P (setb c i b) p = val P (setb c i b) (p ++ [c p.length]) := by
          intro b
          rw [val_cons P _ p hL]
          simp [setb, Nat.ne_of_lt hlt]
        have ch := (ihb (c p.length)).2 (by omega)
        rw [e o, e nw]
        refine ⟨fun heq τ => ?_, fun hne => ?_⟩
        · apply kleene_const P hm hL
          rw [static (by omega), ch.1 heq]
        · apply hmm p hL _ _ hne
          have hmc := mono_shift (P.ddat p (c p.length)) (ch.2 hne)
          intro τ1 τ2 h12
          rw [static (by omega), static (by omega)]
          exact hmc τ1 τ2 h12
      · -- the moving pin's level: one mux with constant legs
        have hpi : p.length = i := by omega
        have leg : ∀ (b : Bool) τ, P.y (p ++ [b]) τ = ofBool (val P c (p ++ [b])) :=
          fun b => (ihb b).1 (by omega)
        have hk : ∀ τ, kap P p τ = kmux (P.pin i (τ - P.dsel p))
            (ofBool (val P c (p ++ [false]))) (ofBool (val P c (p ++ [true]))) := by
          intro τ; unfold kap; rw [leg, leg, hpi]
        have e : ∀ b : Bool, val P (setb c i b) p =
            (if b then val P c (p ++ [true]) else val P c (p ++ [false])) := by
          intro b
          rw [val_cons P _ p hL]
          have : setb c i b p.length = b := by simp [setb, hpi]
          rw [this, val_setb_gt P c i b _ (by simp; omega)]
          cases b <;> rfl
        rw [e o, e nw]
        refine ⟨fun heq τ => ?_, fun hne => ?_⟩
        · have hl : val P c (p ++ [false]) = val P c (p ++ [true]) := by
            revert heq hon; cases o <;> cases nw <;> simp <;> intro h <;> simp [h]
          apply kleene_const P hm hL
          rw [hk, ← hl, kmux_same]
          cases o <;> simp [hl]
        · apply hmm p hL _ _ hne
          intro τ1 τ2 h12
          rw [hk, hk]
          exact sel_step o nw _ _ _ _ hon (hpin _ _ (Int.sub_le_sub_right h12 _))

/-- **Single moving pin ⇒ monotone root transition.** Assumed: H_SRAM,
H_MUX_KLEENE, H_MUX_MONO; every pin but `i` steady at `c j` (H_ONE_PIN); pin
`i`'s select waveform a monotone `o → nw` transition (H_PIN_MONO, the input
buffer's no-revert). Per-mux and per-copy delays arbitrary. Proved: with
`A`, `B` the old and new INIT entries, the root is constantly `A` if
`A = B`, and a monotone `A → B` transition otherwise. -/
theorem root_mono (hs : P.H_sram) (hm : P.H_mux_kleene) (hmm : H_mux_mono P)
    (c : Nat → Bool) (i : Nat) (hi : i < n) (o nw : Bool) (hon : o ≠ nw)
    (hc : ∀ j, j ≠ i → j < n → ∀ τ, P.pin j τ = ofBool (c j))
    (hpin : Mono (ofBool o) (ofBool nw) (P.pin i)) :
    (P.init (seg (setb c i o) 0 n) = P.init (seg (setb c i nw) 0 n) →
        ∀ τ, P.y [] τ = ofBool (P.init (seg (setb c i o) 0 n))) ∧
      (P.init (seg (setb c i o) 0 n) ≠ P.init (seg (setb c i nw) 0 n) →
        Mono (ofBool (P.init (seg (setb c i o) 0 n))) (ofBool (P.init (seg (setb c i nw) 0 n)))
          (P.y [])) := by
  have := (claim P hs hm hmm c i hi o nw hon hc hpin n [] (by simp)).2 (by simp)
  simpa [val] using this

end PhysTree'

/-! ### H_MUX_KLEENE alone does not give H_NO_REVERT -/

/-- A buffer LUT (one mux, INIT `[0, 1]`) whose select makes a monotone
`0 → X → 1` transition on `[0, 3)`, and whose root shows `0, 1, 0, 1`. -/
def revTree : PhysTree 1 where
  init := fun p => p.headD false
  pin := fun _ τ => if τ < 0 then .zero else if τ < 3 then .X else .one
  dsel := fun _ => 0
  ddat := fun _ _ => 0
  y := fun p τ => if p = [] then (if τ < 0 then .zero else if τ = 1 then .zero else .one)
    else ofBool (p.headD false)

theorem revTree_pin : Mono .zero .one (revTree.pin 0) := by
  intro τ1 τ2 h12
  simp only [revTree, Prog]
  by_cases a : τ1 < 0
  · left; simp [a]
  · by_cases b : τ2 < 3
    · have h1 : τ1 < 3 := Int.lt_of_le_of_lt h12 b
      have h2 : ¬ τ2 < 0 := fun h => a (Int.lt_of_le_of_lt h12 h)
      right; right; simp [a, b, h1, h2]
    · have h2 : ¬ τ2 < 0 := fun h => a (Int.lt_of_le_of_lt h12 h)
      right; left; simp [b, h2]

/-- **H_SRAM + H_MUX_KLEENE + one monotone moving pin do NOT give
H_NO_REVERT.** `revTree` meets H_SRAM, H_MUX_KLEENE (when the select is
mid-rail and the legs differ, the Kleene mux is `X` and nothing is assumed)
and H_PIN_MONO, its root reverts `1 → 0 → 1` inside the select's mid-rail
interval, so the root is not a monotone transition, and `revTree` violates
H_MUX_MONO. -/
theorem kleene_revert :
    revTree.H_sram ∧ revTree.H_mux_kleene ∧ Mono .zero .one (revTree.pin 0) ∧
      revTree.y [] 0 = .one ∧ revTree.y [] 1 = .zero ∧ revTree.y [] 2 = .one ∧
      ¬ Mono .zero .one (revTree.y []) ∧ ¬ PhysTree'.H_mux_mono revTree := by
  have hs : revTree.H_sram := by
    intro p hp τ
    have : p ≠ [] := by intro h; subst h; simp at hp
    simp [revTree, this]
  have hm : revTree.H_mux_kleene := by
    intro p hp τ
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [revTree, List.nil_append, ite_true, Int.sub_zero, reduceCtorEq, ite_false,
      List.headD_cons, K3.ofBool_false, K3.ofBool_true]
    by_cases a : τ < 0
    · simp [a, kmux, Le]
    · by_cases b : τ < 3
      · simp [a, b, kmux, Le]
      · simp [a, b, show τ ≠ 1 from fun h => b (by subst h; decide), kmux, Le]
  have hnm : ¬ Mono .zero .one (revTree.y []) := by
    intro h
    have := h 0 1 (by decide)
    revert this; simp [revTree, Prog]
  refine ⟨hs, hm, revTree_pin, by simp [revTree], by simp [revTree], by simp [revTree], hnm, ?_⟩
  intro hmm
  apply hnm
  have := hmm [] (by simp) false true (by decide) (by
    intro τ1 τ2 h12
    have hp := revTree_pin τ1 τ2 h12
    simp only [PhysTree'.kap, List.nil_append, List.length_nil]
    have e : ∀ τ, kmux (revTree.pin 0 (τ - revTree.dsel [])) (revTree.y [false] (τ - revTree.ddat [] false))
        (revTree.y [true] (τ - revTree.ddat [] true)) = revTree.pin 0 τ := by
      intro τ
      simp only [revTree, Int.sub_zero, reduceCtorEq, ite_false, List.headD_cons, K3.ofBool_false,
        K3.ofBool_true]
      split
      · rfl
      · split <;> rfl
    rw [e, e]; exact hp)
  exact this

/-! ### Non-vacuity: A's exact Kleene tree meets H_MUX_MONO -/

theorem exact_mux_mono (n : Nat) init pin dsel ddat :
    PhysTree'.H_mux_mono (exactTree n init pin dsel ddat) := by
  intro p hp A B _ hk
  have e : ∀ τ, (exactTree n init pin dsel ddat).y p τ =
      PhysTree'.kap (exactTree n init pin dsel ddat) p τ := by
    intro τ
    have : n - p.length = (n - (p.length + 1)) + 1 := by omega
    simp only [exactTree, PhysTree'.kap, List.length_append, List.length_singleton]
    rw [this, exactNode]
  intro τ1 τ2 h12
  rw [e, e]; exact hk τ1 τ2 h12

/-- The exact buffer LUT with `revTree`'s select waveform meets every
hypothesis of `root_mono` (`i = 0`, `0 → 1`, INIT entries `0 ≠ 1`). -/
theorem root_mono_witness :
    let P := exactTree 1 (fun p => p.headD false) revTree.pin (fun _ => 0) (fun _ _ => 0)
    P.H_sram ∧ P.H_mux_kleene ∧ PhysTree'.H_mux_mono P ∧ Mono .zero .one (P.pin 0) ∧
      (∀ j, j ≠ 0 → j < 1 → ∀ τ, P.pin j τ = ofBool false) ∧
      P.init (seg (setb (fun _ => false) 0 false) 0 1) ≠ P.init (seg (setb (fun _ => false) 0 true) 0 1) :=
  ⟨exact_H_sram _ _ _ _ _, exact_H_mux _ _ _ _ _, exact_mux_mono _ _ _ _ _, revTree_pin,
    fun j h1 h2 => absurd h2 (by omega), by decide⟩

end Tree

end Formal.Cells.NoRevert
