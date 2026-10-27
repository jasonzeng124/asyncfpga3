import Formal.Core.Trace.Discrete
import Formal.Core.XSim
import Formal.Core.Delay.SAF

/-!
# Substrate, part 1: discrete time, signals, THE delay relation

Shard A, phase 1 ("one substrate"). Core Lean only (no Mathlib). Nothing is
copied: the trace type, the transport channel, the X-window and the SAF
channel are imported from `Formal.Core.Trace.Discrete`, `Formal.Core.XSim`
and `Formal.Core.Delay.SAF`; this file adds the canonical window relation and
proves how every existing delay relation sits relative to it.

## Time and signals

* Time is `ℕ`, one step = 1 ps (convention **H_GRID**, see the notes).
* `Sig := Nat → Bool` (= `TraceDiscrete.Sig`), `KSig := Nat → K3` (Kleene,
  `Formal.Core.K3`), `Covers a x` : the K3 signal `a` over-approximates `x`.

## The delay relations, one form

* `Win lo hi i o` (**the substrate's channel**): at every step `t ≥ hi`, the
  output shows the input as it was at SOME step `s` with
  `t - hi ≤ s ≤ t - lo` (written additively: `t ≤ s + hi`, `s + lo ≤ t`).
  The delay may vary from step to step (non-FIFO). Steps before `hi` are
  unconstrained: an arbitrary power-up value. Definitionally the same
  formula as shard B's `CElemTiming.WinDelay` (`Substrate/Legacy.lean`).
* `WinR lo hi i o` (the same at rest): `XSim.WinCh`, the window with
  truncated subtraction, so before `hi` the output shows an input value from
  `[0, t - lo]` (the signal is "constant before time 0").
  `winR_iff`: `WinR = Win ∧ Start ∧ lo ≤ hi`.
* `TraceDiscrete.Transport lo hi` (FIFO monotone warp) and the fixed delay
  `TraceDiscrete.delay d` are special cases.

Inclusions (all proved below; `⊊` means a proved counterexample to the
converse):

    delay d  ⊆  Transport lo hi  ⊊  WinR lo hi  ⊊  Win lo hi        (lo ≤ d ≤ hi)
    DelaySAF.saf d  ⊆  Transport 1 d  ⊆  WinR 1 d
    inertial δ  ⊄  Win lo hi           (pulse w with hi - lo < w ≤ δ)

and, in `Substrate/Legacy.lean`, `WinR ⊊ Net.BoundedDelay` (shard C) and
`Win = Cells.CElemTiming.WinDelay` (shard B).

## Why the window is THE relation (recommendation)

It is the weakest bounded-delay relation that still says "the output shows an
input value of the right age", so a theorem whose hypothesis is `Win` holds
for every transport, fixed-delay or SAF (GLS) channel at once (`*_win`
lemmas below). It is sound for runts and glitches: it can drop a short pulse
(like transport) and can also create one from a clean edge
(`winR_not_transport`), which a slow edge with noise on a real wire can do.
It is what the X-window simulator (`XSim.sound`) is sound for, and it is what
the discretisation theorem produces without any rest hypothesis
(`Substrate/Real.lean`). State cell and network theorems with `Win`
hypotheses; use `WinR` only where the proof needs the quiescent start.
-/

namespace Formal.Core.Substrate

open Formal.Core.TraceDiscrete (delay Transport Warp Mono pulse inertial)
open Formal.Core K3

/-! ## 0. Time, signals, K3 signals -/

/-- A binary signal on the 1-ps grid (the Core trace type). -/
abbrev Sig := TraceDiscrete.Sig

/-- A Kleene (three-valued) signal on the 1-ps grid. -/
abbrev KSig := Nat → K3

/-- The K3 signal `a` covers the binary signal `x`: wherever `a` is binary it
equals `x` (`a t ⊑ ofBool (x t)`). -/
def Covers (a : KSig) (x : Sig) : Prop := ∀ t, a t ⊑ ofBool (x t)

theorem covers_ofBool (x : Sig) : Covers (fun t => ofBool (x t)) x :=
  fun _ => K3.le_refl _

theorem covers_X (x : Sig) : Covers (fun _ => X) x := fun _ => K3.X_le _

/-! ### Edge vocabulary (same definitions as shard C's `Net.Prelim`) -/

def rises (s : Sig) (t : Nat) : Prop := s t = false ∧ s (t + 1) = true
def falls (s : Sig) (t : Nat) : Prop := s t = true ∧ s (t + 1) = false
/-- `s` changes between `t` and `t+1` (= `TraceDiscrete.Tr s t`, flipped). -/
def changes (s : Sig) (t : Nat) : Prop := s t ≠ s (t + 1)
/-- `s` is constant on `[a, b]`. -/
def stableOn (s : Sig) (a b : Nat) : Prop := ∀ t, a ≤ t → t ≤ b → s t = s a

theorem changes_iff_tr (s : Sig) (t : Nat) : changes s t ↔ TraceDiscrete.Tr s t :=
  ⟨fun h e => h e.symm, fun h e => h e.symm⟩

/-! ## 1. The window relations -/

/-- **The substrate's delay relation.** At every step `t ≥ hi` the output
equals the input at some step `s` that is between `lo` and `hi` steps
earlier. Before `hi`: unconstrained (power-up). -/
def Win (lo hi : Nat) (i o : Sig) : Prop :=
  ∀ t, hi ≤ t → ∃ s, t ≤ s + hi ∧ s + lo ≤ t ∧ o t = i s

/-- The window channel at rest (`XSim.WinCh`): truncated subtraction, so the
input is read as constant before time 0. -/
abbrev WinR (lo hi : Nat) (i o : Sig) : Prop := XSim.WinCh lo hi i o

/-- The start condition that `WinR` adds to `Win`: before `hi` the output
shows some input value at least `lo` old (truncated at 0). -/
def Start (lo hi : Nat) (i o : Sig) : Prop :=
  ∀ t, t < hi → ∃ s, s ≤ t - lo ∧ o t = i s

instance (lo hi : Nat) (i o : Sig) (t : Nat) : Decidable (∃ s, t ≤ s + hi ∧ s + lo ≤ t ∧ o t = i s) :=
  decidable_of_iff (∃ s, s < t + 1 ∧ (t ≤ s + hi ∧ s + lo ≤ t ∧ o t = i s))
    ⟨fun ⟨s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, by omega, h⟩⟩

/-- A nonempty `Win` forces `lo ≤ hi`. -/
theorem win_le {lo hi : Nat} {i o : Sig} (h : Win lo hi i o) : lo ≤ hi := by
  obtain ⟨s, h1, h2, _⟩ := h hi (Nat.le_refl _); omega

/-- A nonempty `WinR` forces `lo ≤ hi`. -/
theorem winR_le {lo hi : Nat} {i o : Sig} (h : WinR lo hi i o) : lo ≤ hi := by
  obtain ⟨s, h1, h2, _⟩ := h lo; omega

/-- `WinR ⊆ Win`. -/
theorem winR_win {lo hi : Nat} {i o : Sig} (h : WinR lo hi i o) : Win lo hi i o := by
  have hl := winR_le h
  intro t ht
  obtain ⟨s, h1, h2, e⟩ := h t
  exact ⟨s, by omega, by omega, e⟩

/-- **`WinR` is exactly `Win` plus the start condition.** -/
theorem winR_iff {lo hi : Nat} {i o : Sig} :
    WinR lo hi i o ↔ lo ≤ hi ∧ Win lo hi i o ∧ Start lo hi i o := by
  constructor
  · intro h
    refine ⟨winR_le h, winR_win h, fun t ht => ?_⟩
    obtain ⟨s, _, h2, e⟩ := h t
    exact ⟨s, h2, e⟩
  · rintro ⟨hl, hw, hs⟩ t
    by_cases ht : hi ≤ t
    · obtain ⟨s, h1, h2, e⟩ := hw t ht
      exact ⟨s, by omega, by omega, e⟩
    · obtain ⟨s, h2, e⟩ := hs t (by omega)
      exact ⟨s, by omega, h2, e⟩

/-! ## 2. Special cases: fixed delay, transport, SAF -/

/-- `Transport ⊆ WinR` (re-export of `XSim.transport_winCh`). -/
theorem transport_winR {lo hi : Nat} {i o : Sig} (h : Transport lo hi i o) : WinR lo hi i o :=
  XSim.transport_winCh h

/-- `Transport ⊆ Win`. -/
theorem transport_win {lo hi : Nat} {i o : Sig} (h : Transport lo hi i o) : Win lo hi i o :=
  winR_win (transport_winR h)

/-- A fixed delay `d ∈ [lo, hi]` is a transport behaviour. -/
theorem delay_transport' {lo hi d : Nat} (h1 : lo ≤ d) (h2 : d ≤ hi) (i : Sig) :
    Transport lo hi i (delay d i) :=
  TraceDiscrete.transport_mono h1 h2 (TraceDiscrete.delay_transport d i)

theorem delay_winR {lo hi d : Nat} (h1 : lo ≤ d) (h2 : d ≤ hi) (i : Sig) :
    WinR lo hi i (delay d i) := transport_winR (delay_transport' h1 h2 i)

theorem delay_win {lo hi d : Nat} (h1 : lo ≤ d) (h2 : d ≤ hi) (i : Sig) :
    Win lo hi i (delay d i) := transport_win (delay_transport' h1 h2 i)

/-- A fixed delay `d` with an arbitrary power-up prefix (shard B's and shard
C's `shift`/`Transport d` form: `o (t + d) = i t`, `o` free on `[0, d)`) is a
`Win` behaviour. -/
theorem shift_win {lo hi d : Nat} (h1 : lo ≤ d) (h2 : d ≤ hi) {i o : Sig}
    (h : ∀ t, o (t + d) = i t) : Win lo hi i o := by
  intro t ht
  refine ⟨t - d, by omega, by omega, ?_⟩
  have := h (t - d); rwa [Nat.sub_add_cancel (by omega)] at this

/-- **The research GLS's LUT channel (sample-at-fire) is a window channel**
with bounds `[1, d]` (from `DelaySAF.saf_transport`). Every theorem stated
with a `Win 1 d` hypothesis therefore covers the GLS's LUT model. -/
theorem saf_winR {d : Nat} (hd : 0 ≤ d) (x : Sig) : WinR 1 d x (DelaySAF.saf d x) :=
  transport_winR (DelaySAF.saf_transport x hd)

theorem saf_win {d : Nat} (hd : 1 ≤ d) (x : Sig) : Win 1 d x (DelaySAF.saf d x) :=
  winR_win (saf_winR hd x)

/-- **Non-vacuity (receptiveness).** Every input has a `WinR` (hence `Win`)
output iff the band is nonempty: a theorem with a `Win` hypothesis is not
vacuous. -/
theorem winR_total_iff {lo hi : Nat} : (∀ i : Sig, ∃ o, WinR lo hi i o) ↔ lo ≤ hi :=
  ⟨fun h => by obtain ⟨o, ho⟩ := h (fun _ => false); exact winR_le ho,
    fun h i => ⟨_, delay_winR (Nat.le_refl lo) h i⟩⟩

theorem win_total_iff {lo hi : Nat} : (∀ i : Sig, ∃ o, Win lo hi i o) ↔ lo ≤ hi :=
  ⟨fun h => by obtain ⟨o, ho⟩ := h (fun _ => false); exact win_le ho,
    fun h i => ⟨_, delay_win (Nat.le_refl lo) h i⟩⟩

/-! ## 3. Strictness -/

/-- The non-FIFO behaviour: a single clean rising edge at step 1 comes out as
`0 1 0 1 1 …` (a glitch), which the window `[0, 2]` admits. -/
def edge1 : Sig := fun t => decide (1 ≤ t)
def glitchy : Sig := fun t => decide (t = 1 ∨ 3 ≤ t)

theorem glitchy_winR : WinR 0 2 edge1 glitchy := by
  intro t
  by_cases h1 : t = 1
  · subst h1; exact ⟨1, by decide, by decide, by decide⟩
  · by_cases h2 : t = 2
    · subst h2; exact ⟨0, by decide, by decide, by decide⟩
    · refine ⟨t, by omega, by omega, ?_⟩
      simp only [glitchy, edge1]
      by_cases h0 : t = 0
      · subst h0; decide
      · have : 3 ≤ t := by omega
        simp [this, show 1 ≤ t by omega]

/-- **`Transport ⊊ WinR`**: the glitch is not a transport behaviour for any
bounds (a monotone warp cannot show the new value and then the old one). -/
theorem winR_not_transport (lo hi : Nat) : ¬ Transport lo hi edge1 glitchy := by
  rintro ⟨f, F, hf⟩
  have e1 := hf 1; have e2 := hf 2
  have m := F.mono 1 2 (by decide)
  simp only [glitchy, edge1] at e1 e2
  have a : 1 ≤ f 1 := by
    cases h : decide (1 ≤ f 1) with
    | false => rw [h] at e1; exact absurd e1 (by decide)
    | true => exact of_decide_eq_true h
  have b : ¬ 1 ≤ f 2 := by
    intro hb; rw [decide_eq_true hb] at e2; exact absurd e2 (by decide)
  omega

/-- **`WinR ⊊ Win`**: `Win` leaves the power-up prefix free. -/
theorem win_not_winR : Win 1 1 (fun _ => false) (fun t => decide (t = 0)) ∧
    ¬ WinR 1 1 (fun _ => false) (fun t => decide (t = 0)) := by
  refine ⟨fun t ht => ⟨t - 1, by omega, by omega, by simp; omega⟩, fun h => ?_⟩
  obtain ⟨s, _, _, e⟩ := h 0
  simp at e

/-- **The inertial channel is not a window channel**: a pulse of width
`w ≤ δ` is swallowed by `inertial δ`, but every window channel whose spread
`hi - lo` is below `w` must show it. So inertial filtering is never a
consequence of a `Win` hypothesis (cf. `DelayInertial`: proofs must not use
filtering). -/
theorem inertial_not_win {δ p w lo hi : Nat} (a : Bool) (hp : 1 ≤ p) (hw : w ≤ δ)
    (hspread : hi < w + lo) :
    ¬ Win lo hi (pulse a p w) (inertial δ (pulse a p w)) := by
  intro h
  obtain ⟨s, h1, h2, e⟩ := h (p + hi) (by omega)
  rw [TraceDiscrete.inertial_filters hp hw] at e
  have : pulse a p w s = !a := TraceDiscrete.pulse_eq_not.2 ⟨by omega, by omega⟩
  rw [this] at e; cases a <;> simp at e

/-! ## 4. Algebra of the window -/

theorem win_mono {lo hi lo' hi' : Nat} {i o : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : Win lo hi i o) : Win lo' hi' i o := by
  intro t ht
  obtain ⟨s, h1, h2, e⟩ := h t (by omega)
  exact ⟨s, by omega, by omega, e⟩

theorem winR_mono {lo hi lo' hi' : Nat} {i o : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : WinR lo hi i o) : WinR lo' hi' i o := by
  intro t
  obtain ⟨s, h1, h2, e⟩ := h t
  exact ⟨s, by omega, by omega, e⟩

/-- Series composition (`winDelay_comp` of shard B, same statement). -/
theorem win_comp {lo1 hi1 lo2 hi2 : Nat} {i m o : Sig}
    (h1 : Win lo1 hi1 i m) (h2 : Win lo2 hi2 m o) : Win (lo1 + lo2) (hi1 + hi2) i o := by
  intro t ht
  obtain ⟨s1, a1, b1, e1⟩ := h2 t (by omega)
  obtain ⟨s2, a2, b2, e2⟩ := h1 s1 (by omega)
  exact ⟨s2, by omega, by omega, e1.trans e2⟩

theorem winR_comp {lo1 hi1 lo2 hi2 : Nat} {i m o : Sig}
    (h1 : WinR lo1 hi1 i m) (h2 : WinR lo2 hi2 m o) : WinR (lo1 + lo2) (hi1 + hi2) i o := by
  intro t
  obtain ⟨s1, a1, b1, e1⟩ := h2 t
  obtain ⟨s2, a2, b2, e2⟩ := h1 s1
  exact ⟨s2, by omega, by omega, e1.trans e2⟩

/-- A pointwise Boolean map commutes with the window (an inverter or a
buffer on either side of a wire). -/
theorem win_map {lo hi : Nat} {i o : Sig} (g : Bool → Bool) (h : Win lo hi i o) :
    Win lo hi (fun t => g (i t)) (fun t => g (o t)) := by
  intro t ht
  obtain ⟨s, h1, h2, e⟩ := h t ht
  exact ⟨s, h1, h2, by simp only [e]⟩

theorem winR_map {lo hi : Nat} {i o : Sig} (g : Bool → Bool) (h : WinR lo hi i o) :
    WinR lo hi (fun t => g (i t)) (fun t => g (o t)) := by
  intro t
  obtain ⟨s, h1, h2, e⟩ := h t
  exact ⟨s, h1, h2, by simp only [e]⟩

/-! ## 5. Stability, causality, bundling -/

/-- A stable input window `[a, b]` gives a stable output window
`[a + hi, b + lo]` (it shrinks by the spread `hi - lo`). -/
theorem win_stable {lo hi a b : Nat} {v : Bool} {i o : Sig} (h : Win lo hi i o)
    (hs : ∀ s, a ≤ s → s ≤ b → i s = v) : ∀ t, a + hi ≤ t → t ≤ b + lo → o t = v := by
  intro t h1 h2
  obtain ⟨s, a1, a2, e⟩ := h t (by omega)
  rw [e]; exact hs s (by omega) (by omega)

/-- Stable from `a` on gives stable from `a + hi` on. -/
theorem win_stableFrom {lo hi a : Nat} {v : Bool} {i o : Sig} (h : Win lo hi i o)
    (hs : ∀ s, a ≤ s → i s = v) : ∀ t, a + hi ≤ t → o t = v := by
  intro t h1
  obtain ⟨s, a1, a2, e⟩ := h t (by omega)
  rw [e]; exact hs s (by omega)

/-- **Causality.** If the input holds `b` before `t0`, an output step
`t ≥ hi` that shows something else is at least `t0 + lo`. -/
theorem win_after {lo hi t0 t : Nat} {b : Bool} {i o : Sig} (h : Win lo hi i o)
    (hb : ∀ s, s < t0 → i s = b) (ht : hi ≤ t) (hne : o t ≠ b) : t0 + lo ≤ t := by
  obtain ⟨s, a1, a2, e⟩ := h t ht
  refine Nat.le_of_not_lt fun hc => hne ?_
  rw [e]; exact hb s (by omega)

/-- Causality at rest: no `t ≥ hi` side condition (the launch must be after
time 0, since the input is read as `i 0` before time 0). -/
theorem winR_after {lo hi t0 t : Nat} {b : Bool} {i o : Sig} (h : WinR lo hi i o)
    (ht0 : 0 < t0) (hb : ∀ s, s < t0 → i s = b) (hne : o t ≠ b) : t0 + lo ≤ t := by
  obtain ⟨s, a1, a2, e⟩ := h t
  refine Nat.le_of_not_lt fun hc => hne ?_
  rw [e]; exact hb s (by omega)

/-- **Bundled data in the substrate.** Data source stable at `v` on
`[t0 + ts, t1]`, data wire `Win loD hiD`, request launched at `t0` (it was
`b` before) through a `WinR loR hiR` wire. If `ts + hiD ≤ loR`, the data is
`v` at the receiver whenever it sees the request, up to `t1 + loD`.
(`DelayPure.bundle_two_wires` in discrete time, for the window channel.) -/
theorem win_bundle {loD hiD loR hiR t0 ts t1 s : Nat} {b v : Bool}
    {src data reqIn reqOut : Sig}
    (hsrc : ∀ u, t0 + ts ≤ u → u ≤ t1 → src u = v) (hD : Win loD hiD src data)
    (hR : WinR loR hiR reqIn reqOut) (ht0 : 0 < t0) (hb : ∀ u, u < t0 → reqIn u = b)
    (hbundle : ts + hiD ≤ loR) (hs : reqOut s ≠ b) (hs1 : s ≤ t1 + loD) :
    data s = v := by
  have := winR_after hR ht0 hb hs
  exact win_stable hD hsrc s (by omega) hs1

/-! ## 6. K3 view: the X-window over-approximates every window behaviour -/

/-- At every `t ≥ hi`, the X-window of the input (`XSim.win`, the `merge`
over `[t-hi, t-lo]`) is below the output of any `Win` behaviour. -/
theorem win_covered {lo hi : Nat} {i o : Sig} (h : Win lo hi i o) {t : Nat} (ht : hi ≤ t) :
    XSim.win lo hi (fun s => ofBool (i s)) t ⊑ ofBool (o t) := by
  obtain ⟨s, a1, a2, e⟩ := h t ht
  rw [e]; exact XSim.win_le (by omega) (by omega)

/-- `WinR`: at every `t`. -/
theorem winR_covered {lo hi : Nat} {i o : Sig} (h : WinR lo hi i o) (t : Nat) :
    XSim.win lo hi (fun s => ofBool (i s)) t ⊑ ofBool (o t) := by
  obtain ⟨s, a1, a2, e⟩ := h t
  rw [e]; exact XSim.win_le a1 a2

/-- The X-window is exact for one channel (re-export of `XSim.win_exact`):
an `X` means two `WinR` behaviours really disagree. -/
theorem winR_exact (lo hi : Nat) (hlh : lo ≤ hi) (e : Sig) (t : Nat)
    (h : XSim.win lo hi (fun s => ofBool (e s)) t = X) :
    ∃ o o' : Sig, WinR lo hi e o ∧ WinR lo hi e o' ∧ o t ≠ o' t :=
  XSim.win_exact lo hi hlh e t h

/-! ## 7. Gates and nets over the substrate -/

/-- A discrete-time net: each driven node `n` (`drv n`) is a zero-delay
Boolean function `f n` of the current node values, through a channel with
bounds `[lo n, hi n]` (ps). Undriven nodes are primary inputs. A LUT cell is
`f n = fun v => L.eval (fun j => v (pin j))` with a Core `Lut k`; a routed
wire is `f n = fun v => v src`. Same shape as `Discretize.DCircuit`. -/
structure DNet (N : Type) where
  drv : N → Prop
  f : N → (N → Bool) → Bool
  lo : N → Nat
  hi : N → Nat

namespace DNet
variable {N : Type} (C : DNet N)

/-- Excitation of node `n`: its gate function at the current values. -/
def exc (v : N → Sig) (n : N) : Sig := fun t => C.f n (fun m => v m t)

/-- **Behaviour** (window semantics, the default): every driven node is a
`Win` copy of its excitation. -/
def Beh (v : N → Sig) : Prop := ∀ n, C.drv n → Win (C.lo n) (C.hi n) (C.exc v n) (v n)

/-- Behaviour at rest (`WinR`). -/
def BehR (v : N → Sig) : Prop := ∀ n, C.drv n → WinR (C.lo n) (C.hi n) (C.exc v n) (v n)

/-- Behaviour with FIFO transport channels. -/
def BehT (v : N → Sig) : Prop :=
  ∀ n, C.drv n → Transport (C.lo n) (C.hi n) (C.exc v n) (v n)

/-- Behaviour with ONE fixed delay per node (`d n ∈ [lo n, hi n]`), the
"one die, one corner" reading; power-up prefix free. -/
def BehFixed (v : N → Sig) : Prop :=
  ∃ d : N → Nat, ∀ n, C.drv n → C.lo n ≤ d n ∧ d n ≤ C.hi n ∧
    ∀ t, v n (t + d n) = C.exc v n t

theorem BehT.toBehR {v : N → Sig} (h : C.BehT v) : C.BehR v :=
  fun n hn => transport_winR (h n hn)

theorem BehR.toBeh {v : N → Sig} (h : C.BehR v) : C.Beh v :=
  fun n hn => winR_win (h n hn)

theorem BehFixed.toBeh {v : N → Sig} (h : C.BehFixed v) : C.Beh v := by
  obtain ⟨d, hd⟩ := h
  intro n hn
  obtain ⟨h1, h2, h3⟩ := hd n hn
  exact shift_win h1 h2 h3

/-- **The theorem form.** A property proved for all window behaviours holds
for all at-rest, transport and fixed-delay behaviours. -/
theorem refines {P : (N → Sig) → Prop} (hP : ∀ v, C.Beh v → P v) :
    (∀ v, C.BehR v → P v) ∧ (∀ v, C.BehT v → P v) ∧ (∀ v, C.BehFixed v → P v) :=
  ⟨fun v h => hP v (BehR.toBeh C h), fun v h => hP v (BehR.toBeh C (BehT.toBehR C h)),
    fun v h => hP v (BehFixed.toBeh C h)⟩

/-- Widening every band keeps every behaviour. -/
theorem Beh.widen {v : N → Sig} {lo' hi' : N → Nat} (h : C.Beh v)
    (hlo : ∀ n, lo' n ≤ C.lo n) (hhi : ∀ n, C.hi n ≤ hi' n) :
    ({ C with lo := lo', hi := hi' } : DNet N).Beh v :=
  fun n hn => win_mono (hlo n) (hhi n) (h n hn)

end DNet

/-- The `XSim` LUT-gate list as a substrate net on wires `Fin n`: the at-rest
behaviours are exactly `XSim`'s window-channel behaviours (`relW`), so
`XSim.sound` applies to every `BehR` behaviour. -/
def ofLGates {n : Nat} (gs : List (XSim.LGate n)) : DNet (Fin n) where
  drv w := ∃ g ∈ gs, g.out = w
  f w := fun v => match XSim.driver gs w with
    | some g => g.lut.eval (fun j => v (g.ins j))
    | none => false
  lo w := match XSim.driver gs w with | some g => g.lo | none => 0
  hi w := match XSim.driver gs w with | some g => g.hi | none => 0

/-- If every driven wire has exactly the gate `driver` finds, a `BehR`
behaviour of `ofLGates gs` satisfies every `XSim` gate relation, so
`XSim.sound` gives `val ⊑ ofBool x`. (Uniqueness of drivers is the netlist
well-formedness condition; `XSim.driver` takes the first.) -/
theorem ofLGates_relW {n : Nat} {gs : List (XSim.LGate n)} {x : Fin n → Sig}
    (huniq : ∀ g ∈ gs, XSim.driver gs g.out = some g)
    (h : (ofLGates gs).BehR x) : ∀ g ∈ gs, g.relW x := by
  intro g hg
  have hd := huniq g hg
  have := h g.out ⟨g, hg, rfl⟩
  unfold DNet.exc at this
  simp only [ofLGates, hd] at this
  exact this

end Formal.Core.Substrate
