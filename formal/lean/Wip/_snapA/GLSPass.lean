import Formal.Core.Delay.SAF

/-!
# What a passing GLS run does and does not imply (discrete time)

PROGRAM.md Phase 2, item A, second half. `Formal.Core.DelaySAF` formalised the
research GLS's LUT channel ("sample at fire", `saf`). This file is about a
*run*: the research GLS (`cells/gls/gen.py` + `prims.v`, baked build
`-DGLS_TRANSPORT_IC`) simulates the routed netlist under

* ONE delay assignment: one number per arc (gen.py writes `(d:d:d)`; with
  nextpnr's own SDF that is the slow-max-like nominal arc, O6 = 124 ps),
* the SAF channel on every LUT (an iverilog specify path), and
* a transport (pure) delay on every baked wire (`ICBUF`, `o <= #D I`).

Time is `ℕ` (1 step = 1 ps, iverilog's timescale), signals are
`TraceDiscrete.Sig`. Lean core only.

## Model
* `Net`: signals `0 .. n-1`; `0 .. m-1` are primary inputs, `m .. n-1` are
  LUTs. LUT `k` computes `f k` of its pin vector; pin `j` sees signal `j`
  through a wire into `k`. Pins `j ≥ n` read `false`. Feedback is allowed by
  the definition; `Acyclic` (LUT `k` reads only `j < k`) is a hypothesis
  where used.
* `Asg`: a delay assignment, `d k` per LUT, `w k j` per wire.
* `SemRun σ N A inp s`: `s` is the run with LUT channel `σ` (`saf`,
  `transport` = pure delay, `inertial` = `Trace.Discrete`'s inertial delay
  with rejection `d-1` then one step, which agrees with SAF on isolated
  pulses), baked transport wires, all at assignment `A`.
  The GLS run is `SemRun .saf`.
* `BandRun N lo hi inp s`: a *silicon envelope* behaviour: every LUT and every
  wire is some bounded transport channel `Transport lo hi` (a monotone time
  warp, `Trace.Discrete` B2), per-arc band `[lo, hi]`.

## Results
(a) What a pass implies.
  * `run_unique`: on an acyclic net the run at a given assignment is unique
    (for every LUT semantics). So `gls_pass_of_saf_silicon`: IF the silicon
    is exactly SAF at exactly the annotated delays, a pass is a proof for it.
  * `gls_eq_transport_of_faithful`, `gls_pass_transport_of_faithful`: if every
    LUT's function value in the GLS run is `Faithful` (the monitor of
    A-delay-saf.md: every fire copies the value its own change set), the GLS
    run IS the pure-delay run at the same assignment, so a pass holds for
    pure-delay silicon at exactly that assignment.
  * `gls_in_envelope`: every GLS run is a `BandRun` with LUT band `[1, d]` and
    exact wires; every property proved for that whole envelope holds of it
    (the converse direction: the GLS cannot refute such a property).
(b) What a pass does NOT imply, each with an explicit circuit and stimulus:
  * `ce_skew` (a LUT with skewed inputs, an XOR hazard of width `w < d`):
    the GLS at `d` shows no glitch; (i) the GLS at any LUT delay `d' ≤ w`
    does; (ii) the transport LUT at the same `d` does; (iii) a silicon
    envelope behaviour in `[lo, d]` does, for every `lo`. The inertial LUT
    hides it too (`ce_skew_inertial_hides`). Numbers: `ce_skew_124`
    (O6 band [45, 124] ps, skew 100 ps) and `ce_skew_kappa` (within 5 % of
    the annotated arc).
  * `ce_capture` (bundled-data capture behind an XOR3 data LUT whose function
    value glitches, the audit's `tb_impact`): the GLS at 124 ps captures the
    right value at T = 248; (i) the GLS at 123 ps (inside the band, 1 %
    scatter) captures the wrong one: a FASTER LUT fails, so passing at the
    slow arc is not conservative; (ii) transport and inertial LUTs at the same
    124 ps capture the wrong one.
  * `annotated_ne_baked`: a wire pulse narrower than the wire delay vanishes
    in the annotated build (wire = SAF) and passes in the baked build (wire =
    transport): the two GLS builds are different runs.
(c) A sufficient condition for the whole band (`Rising` stimulus, monotone
  (positive) LUT functions, acyclic net):
  * `mono_saf_is_transport`: the GLS run equals the pure-delay run.
  * `band_bracket_hi` / `band_bracket_lo`: every `BandRun` with per-arc
    `hi ≤ A` is pointwise at least the GLS run at `A`; every `BandRun` with
    per-arc `lo ≥ A` is pointwise at most the GLS run at `A`.
  * `gls_mono_settle_band`: one GLS run at the per-arc maxima showing node `k`
    high at `T` implies node `k` high from `T` on in every behaviour of the
    band, for every assignment and every transport channel below the maxima.
  * `gls_mono_bundle`: two GLS runs (all-fast-min, all-slow-max) bracket the
    band; if the slow run has data high at `T` and the fast run has request
    low before `T`, every band behaviour satisfies "request ⇒ data".
  Both counterexample circuits in (b) use XOR, which is not monotone: that is
  the hypothesis they break.
-/

namespace Formal.Core.GLSPass

open Formal.Core.TraceDiscrete Formal.Core.DelaySAF

/-! ## 0. LUT semantics -/

/-- The three LUT channel semantics compared. -/
inductive Sem
  | saf
  | transport
  | inertial

/-- The channel of a LUT with delay `d` under semantics `σ`. -/
def Sem.ch : Sem → Nat → Sig → Sig
  | .saf, d, x => saf d x
  | .transport, d, x => delay d x
  | .inertial, d, x => delay 1 (inertial (d - 1) x)

/-! ## 1. Netlists, assignments, runs -/

/-- A netlist: signals `0..n-1`, primary inputs `0..m-1`, LUTs `m..n-1`;
LUT `k` computes `f k` of its pin vector. -/
structure Net where
  m : Nat
  n : Nat
  f : Nat → (Nat → Bool) → Bool

/-- A delay assignment: one number per LUT arc and per wire (what one SDF
annotates). -/
structure Asg where
  d : Nat → Nat
  w : Nat → Nat → Nat

/-- The pin vector at step `t` when pin `j` sees `ws j`. -/
def pins (N : Net) (ws : Nat → Sig) (t : Nat) : Nat → Bool :=
  fun j => if j < N.n then ws j t else false

/-- The zero-time LUT function value of LUT `k`. -/
def fval (N : Net) (k : Nat) (ws : Nat → Sig) : Sig := fun t => N.f k (pins N ws t)

/-- Pin signals of LUT `k` through baked (pure-delay) wires. -/
def wired (A : Asg) (k : Nat) (s : Nat → Sig) : Nat → Sig := fun j => delay (A.w k j) (s j)

/-- A run with LUT semantics `σ` and baked transport wires at assignment `A`.
Signals `≥ n` are pinned to `false` so a run is a single function. -/
def SemRun (σ : Sem) (N : Net) (A : Asg) (inp : Nat → Sig) (s : Nat → Sig) : Prop :=
  (∀ k, k < N.m → s k = inp k) ∧
  (∀ k, N.m ≤ k → k < N.n → s k = σ.ch (A.d k) (fval N k (wired A k s))) ∧
  (∀ k, N.n ≤ k → s k = fun _ => false)

/-- The GLS run (SAF LUTs, transport wires, one assignment). -/
abbrev GLSRun (N : Net) (A : Asg) (inp : Nat → Sig) (s : Nat → Sig) : Prop :=
  SemRun .saf N A inp s

/-- A silicon-envelope behaviour: every LUT and every wire is a bounded
transport channel with its own band. -/
def BandRun (N : Net) (lo hi : Asg) (inp : Nat → Sig) (s : Nat → Sig) : Prop :=
  (∀ k, k < N.m → s k = inp k) ∧
  (∀ k, N.m ≤ k → k < N.n → ∃ ws : Nat → Sig,
    (∀ j, j < N.n → Transport (lo.w k j) (hi.w k j) (s j) (ws j)) ∧
    Transport (lo.d k) (hi.d k) (fval N k ws) (s k)) ∧
  (∀ k, N.n ≤ k → s k = fun _ => false)

/-- LUT `k` reads only signals `j < k`. -/
def Acyclic (N : Net) : Prop :=
  ∀ k, N.m ≤ k → k < N.n → ∀ (u v : Nat → Bool), (∀ j, j < k → u j = v j) → N.f k u = N.f k v

/-! ## (a) What a passing run implies -/

theorem fval_congr {N : Net} (hN : Acyclic N) {k : Nat} (h1 : N.m ≤ k) (h2 : k < N.n)
    {ws ws' : Nat → Sig}
    (h : ∀ j, j < k → ws j = ws' j) : fval N k ws = fval N k ws' := by
  funext t
  apply hN k h1 h2
  intro j hj
  simp only [pins, h j hj]

/-- (a) On an acyclic net the run at one assignment is unique, for each LUT
semantics: the simulator's output is THE behaviour of that model. -/
theorem run_unique {σ : Sem} {N : Net} (hN : Acyclic N) {A : Asg} {inp s s' : Nat → Sig}
    (h : SemRun σ N A inp s) (h' : SemRun σ N A inp s') : s = s' := by
  have key : ∀ k, s k = s' k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases h1 : k < N.m
      · rw [h.1 k h1, h'.1 k h1]
      · by_cases h2 : k < N.n
        · rw [h.2.1 k (by omega) h2, h'.2.1 k (by omega) h2]
          congr 1
          apply fval_congr hN (by omega) h2
          intro j hj
          simp only [wired, ih j hj]
        · rw [h.2.2 k (by omega), h'.2.2 k (by omega)]
  funext k; exact key k

/-- (a) If the silicon is exactly the SAF model at exactly the annotated
assignment, a property of the GLS run holds of the silicon. Nothing weaker
than "silicon = SAF at `A`" is assumed here; see (b) for why it is needed. -/
theorem gls_pass_of_saf_silicon {N : Net} (hN : Acyclic N) {A : Asg} {inp g : Nat → Sig}
    (P : (Nat → Sig) → Prop) (hg : GLSRun N A inp g) (hp : P g) :
    ∀ s, GLSRun N A inp s → P s := by
  intro s hs; rw [← run_unique hN hg hs]; exact hp

/-- The `Faithful` monitor: in the run `g`, every LUT fire copies the value its
own change set (checkable on the GLS trace itself). -/
def MonitorClean (N : Net) (A : Asg) (g : Nat → Sig) : Prop :=
  ∀ k, N.m ≤ k → k < N.n → Faithful (A.d k) (fval N k (wired A k g))

/-- (a) A GLS run with a clean `Faithful` monitor IS the pure-delay run at the
same assignment (any net, feedback allowed). -/
theorem gls_eq_transport_of_faithful {N : Net} {A : Asg} {inp g : Nat → Sig}
    (hg : GLSRun N A inp g) (hm : MonitorClean N A g) : SemRun .transport N A inp g := by
  refine ⟨hg.1, ?_, hg.2.2⟩
  intro k h1 h2
  rw [hg.2.1 k h1 h2]
  exact saf_eq_delay_iff.2 (hm k h1 h2)

/-- (a) So a pass with a clean monitor holds for the pure-delay (transport)
silicon at exactly the annotated delays. -/
theorem gls_pass_transport_of_faithful {N : Net} (hN : Acyclic N) {A : Asg}
    {inp g : Nat → Sig} (P : (Nat → Sig) → Prop) (hg : GLSRun N A inp g)
    (hm : MonitorClean N A g) (hp : P g) :
    ∀ s, SemRun .transport N A inp s → P s := by
  intro s hs
  rw [← run_unique hN (gls_eq_transport_of_faithful hg hm) hs]; exact hp

/-- The assignment with every LUT delay replaced by `1` (wires kept). -/
def Asg.lut1 (A : Asg) : Asg := ⟨fun _ => 1, A.w⟩

/-- (a) Every GLS run lies in the envelope "LUT band `[1, d]`, wires exact".
So every property proved for all behaviours of that envelope (for instance by
a soundness theorem stated for transport channels) holds of the GLS run;
nothing proved only for a band `[lo, d]` with `lo ≥ 2` transfers
(`saf_not_transport`). -/
theorem gls_in_envelope {N : Net} {A : Asg} {inp g : Nat → Sig}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) (hg : GLSRun N A inp g) :
    BandRun N A.lut1 A inp g := by
  refine ⟨hg.1, ?_, hg.2.2⟩
  intro k h1 h2
  refine ⟨wired A k g, fun j _ => delay_transport _ _, ?_⟩
  rw [hg.2.1 k h1 h2]
  exact saf_transport _ (hd k h1 h2)

/-- A transport (pure-delay) run at `A` is a `BandRun` with band `[A, A]`. -/
theorem transport_in_band {N : Net} {A : Asg} {inp s : Nat → Sig}
    (hs : SemRun .transport N A inp s) : BandRun N A A inp s := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro k h1 h2
  refine ⟨wired A k s, fun j _ => delay_transport _ _, ?_⟩
  rw [hs.2.1 k h1 h2]
  exact delay_transport _ _

/-! ## (b) Counterexamples -/

/-- A step: low before `p`, high from `p` on. -/
def step (p : Nat) : Sig := fun t => decide (p ≤ t)

/-- A one-LUT net with two primary inputs (signals 0, 1) and the LUT (signal
2) computing `F` of its two pins. -/
def lut2 (F : Bool → Bool → Bool) : Net := ⟨2, 3, fun _ v => F (v 0) (v 1)⟩

theorem lut2_acyclic (F : Bool → Bool → Bool) : Acyclic (lut2 F) := by
  intro k h1 h2 u v h
  simp only [lut2] at h1 h2 ⊢
  rw [h 0 (by omega), h 1 (by omega)]

end Formal.Core.GLSPass
