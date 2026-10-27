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
  * `ce_c2` (`bd_c2` = majority LUT with its output fed back, reset `q = 0`,
    inputs `01 → 10` with skew `σ < d`): the GLS at `d` holds `q = 0`; (i) the
    GLS at any `d' ≤ σ` latches `q = 1`; (ii) the transport LUT at `d`
    latches; (iii) the envelope `[lo, d]` admits a latch for every `lo ≤ σ`.
    Numbers: `ce_c2_124` (skew 100 ps). Feedback runs are unique given the
    reset state: `gls_unique_time`.
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
  | .saf, d, x => DelaySAF.saf d x
  | .transport, d, x => delay d x
  | .inertial, d, x => delay 1 (TraceDiscrete.inertial (d - 1) x)

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
  rw [hg.2.1 k h1 h2]; simp only [Sem.ch]
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
  rw [hg.2.1 k h1 h2]; simp only [Sem.ch, Asg.lut1]
  exact saf_transport _ (hd k h1 h2)

/-- A transport (pure-delay) run at `A` is a `BandRun` with band `[A, A]`. -/
theorem transport_in_band {N : Net} {A : Asg} {inp s : Nat → Sig}
    (hs : SemRun .transport N A inp s) : BandRun N A A inp s := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro k h1 h2
  refine ⟨wired A k s, fun j _ => delay_transport _ _, ?_⟩
  rw [hs.2.1 k h1 h2]; simp only [Sem.ch]
  exact delay_transport _ _

/-! ## Rising signals (used in (b) and (c)) -/

/-- A signal that only ever rises (at most one transition, `0 → 1`). -/
def Rising (x : Sig) : Prop := ∀ a b, a ≤ b → x a = true → x b = true

/-- Pointwise order: `x` high implies `y` high (`y` rises no later). -/
def SLe (x y : Sig) : Prop := ∀ t, x t = true → y t = true

/-- A monotone (positive-unate) LUT function. -/
def MonoF (F : (Nat → Bool) → Bool) : Prop :=
  ∀ u v : Nat → Bool, (∀ j, u j = true → v j = true) → F u = true → F v = true

theorem rising_const_false : Rising (fun _ => false) := fun _ _ _ h => h

theorem rising_delay {x : Sig} (d : Nat) (h : Rising x) : Rising (delay d x) :=
  fun a b hab ha => h (a - d) (b - d) (by omega) ha

theorem sle_delay {x y : Sig} (d : Nat) (h : SLe x y) : SLe (delay d x) (delay d y) :=
  fun t ht => h (t - d) ht

theorem sle_trans {x y z : Sig} (h1 : SLe x y) (h2 : SLe y z) : SLe x z :=
  fun t ht => h2 t (h1 t ht)

theorem faithful_of_rising {d : Nat} {x : Sig} (hd : 1 ≤ d) (h : Rising x) : Faithful d x := by
  intro k hk
  cases h0 : x k <;> cases h1 : x (k + 1)
  · rw [h0, h1] at hk; exact absurd rfl hk
  · exact h (k + 1) (k + d) (by omega) h1
  · exact absurd (h k (k + 1) (by omega) h0) (by rw [h1]; decide)
  · rw [h0, h1] at hk; exact absurd rfl hk

/-- On a rising function value, SAF is the pure delay. -/
theorem saf_of_rising {d : Nat} {x : Sig} (hd : 1 ≤ d) (h : Rising x) : saf d x = delay d x :=
  saf_eq_delay_iff.2 (faithful_of_rising hd h)

theorem transport_rising {lo hi : Nat} {x y : Sig} (h : Transport lo hi x y) (hx : Rising x) :
    Rising y := by
  obtain ⟨f, F, hf⟩ := h
  intro a b hab ha
  rw [hf] at ha ⊢
  exact hx _ _ (F.mono a b hab) ha

/-- A rising input through any transport channel with `hi ≤ H` is high no later
than through the pure delay `H`. -/
theorem transport_ge {lo hi H : Nat} {x y : Sig} (h : Transport lo hi x y) (hx : Rising x)
    (hH : hi ≤ H) : SLe (delay H x) y := by
  obtain ⟨f, F, hf⟩ := h
  intro t ht
  rw [hf]
  have := F.early_le t
  exact hx (t - H) (f t) (by omega) ht

/-- ... and no earlier than through the pure delay `L ≤ lo`. -/
theorem transport_le {lo hi L : Nat} {x y : Sig} (h : Transport lo hi x y) (hx : Rising x)
    (hL : L ≤ lo) : SLe y (delay L x) := by
  obtain ⟨f, F, hf⟩ := h
  intro t ht
  rw [hf] at ht
  have := F.le_late t
  exact hx (f t) (t - L) (by omega) ht

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

/-- Any run of `lut2 F`, in closed form. -/
theorem lut2_run {σ : Sem} {F : Bool → Bool → Bool} {A : Asg} {inp s : Nat → Sig}
    (h : SemRun σ (lut2 F) A inp s) :
    s 2 = σ.ch (A.d 2) (fun t => F (delay (A.w 2 0) (inp 0) t) (delay (A.w 2 1) (inp 1) t)) := by
  rw [h.2.1 2 (by simp [lut2]) (by simp [lut2])]
  have e0 := h.1 0 (by simp [lut2])
  have e1 := h.1 1 (by simp [lut2])
  congr 1
  funext t
  simp only [fval, pins, wired, lut2, e0, e1]
  simp

/-- The skewed-input assignment: LUT delay `d`, pin 0 direct, pin 1 through a
wire of `w`. -/
def skewA (d w : Nat) : Asg := ⟨fun _ => d, fun _ j => if j = 1 then w else 0⟩

/-- The stimulus: one source edge at `p`, forked to both pins. -/
def skewIn (p : Nat) : Nat → Sig := fun _ => step p

/-- The skewed XOR LUT's function value is the hazard pulse `[p, p+w)`. -/
theorem skew_fval {p w : Nat} (hp : 1 ≤ p) :
    (fun t => xor (delay ((skewA d w).w 2 0) (skewIn p 0) t)
      (delay ((skewA d w).w 2 1) (skewIn p 1) t)) = pulse false p w := by
  funext t
  rw [pulse_false_eq]
  simp only [skewA, skewIn, step, delay]
  simp only [show ((0 : Nat) = 1) = False by decide, ↓reduceIte, Nat.sub_zero]
  by_cases c1 : p ≤ t <;> by_cases c2 : p ≤ t - w <;> simp [c1, c2] <;> omega

/-- (b) The skewed-input LUT (an XOR whose two pins see one source edge with
skew `w`, a static-0 hazard of width `w`), annotated LUT delay `d > w`.
* The GLS run shows no glitch on the LUT output.
* (i) The GLS run at any other LUT delay `d' ≤ w` shows one: passing at the
  annotated delay is not passing over the band.
* (ii) The pure-delay (transport) LUT at the same delays shows one.
* (iii) The silicon envelope `[lo, d]` (any `lo ≤ d`) admits a behaviour that
  shows it. The glitch is hidden by SAF, not absent from the circuit. -/
theorem ce_skew {p d w d' lo : Nat} (hp : 1 ≤ p) (hwd : w < d) (hd' : 1 ≤ d')
    (hd'w : d' ≤ w) (hlo : lo ≤ d) :
    (∀ s, GLSRun (lut2 xor) (skewA d w) (skewIn p) s → ∀ t, s 2 t = false) ∧
    (∀ s, GLSRun (lut2 xor) (skewA d' w) (skewIn p) s → s 2 (p + d') = true) ∧
    (∀ s, SemRun .transport (lut2 xor) (skewA d w) (skewIn p) s → s 2 (p + d) = true) ∧
    (∃ s, BandRun (lut2 xor) (skewA lo w) (skewA d w) (skewIn p) s ∧ s 2 (p + lo) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t
    rw [lut2_run hs, skew_fval hp]
    exact saf_pulse_short hp hwd t
  · intro s hs
    rw [lut2_run hs, skew_fval hp]
    simp only [Sem.ch, skewA]
    rw [saf_pulse_long hd' hp hd'w, pulse_false_eq]
    simp; omega
  · intro s hs
    rw [lut2_run hs, skew_fval hp]
    simp only [Sem.ch, skewA, delay, pulse_false_eq]
    simp; omega
  · refine ⟨fun k => if k = 2 then delay lo (pulse false p w) else if k < 2 then step p
        else fun _ => false, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro k hk
      simp only [lut2] at hk
      simp only [skewIn, show k ≠ 2 by omega, hk, ↓reduceIte]
    · intro k h1 h2
      simp only [lut2] at h1 h2
      have hk : k = 2 := by omega
      subst hk
      refine ⟨wired (skewA d w) 2 (fun k => if k = 2 then delay lo (pulse false p w)
        else if k < 2 then step p else fun _ => false), fun j _ => delay_transport _ _, ?_⟩
      have e : fval (lut2 xor) 2 (wired (skewA d w) 2 (fun k => if k = 2 then
          delay lo (pulse false p w) else if k < 2 then step p else fun _ => false)) =
          pulse false p w := by
        rw [← skew_fval (d := d) hp]
        funext t
        simp [fval, pins, wired, lut2, skewIn]
      rw [e]
      simp only [↓reduceIte]
      exact pulse_may_pass false hlo
    · intro k hk
      simp only [lut2] at hk
      simp only [show k ≠ 2 by omega, show ¬ k < 2 by omega, ↓reduceIte]
    · simp only [↓reduceIte, delay, pulse_false_eq]
      simp; omega

/-- (b) For the record: the inertial LUT (rejection `d-1`) hides the same
glitch, so "SAF vs inertial" does not separate on this circuit; `ce_capture`
does. -/
theorem ce_skew_inertial_hides {p d w : Nat} (hp : 1 ≤ p) (hwd : w < d) :
    ∀ s, SemRun .inertial (lut2 xor) (skewA d w) (skewIn p) s → ∀ t, s 2 t = false := by
  intro s hs t
  rw [lut2_run hs, skew_fval hp]
  simp only [Sem.ch, skewA, delay]
  exact inertial_filters hp (by omega) _

/-- (b) Numbers: the prjxray O6 arc is 45 / 56 / 100 / 124 ps (FAST_MIN /
FAST_MAX / SLOW_MIN / SLOW_MAX). With the GLS's 124 ps and a 100 ps routing
skew between the two pins: GLS clean; GLS with the LUT at 100 ps (inside
[45, 124]) glitches; transport at 124 glitches; the envelope [45, 124]
admits a glitch. -/
theorem ce_skew_124 :
    (∀ s, GLSRun (lut2 xor) (skewA 124 100) (skewIn 1000) s → ∀ t, s 2 t = false) ∧
    (∀ s, GLSRun (lut2 xor) (skewA 100 100) (skewIn 1000) s → s 2 1100 = true) ∧
    (∀ s, SemRun .transport (lut2 xor) (skewA 124 100) (skewIn 1000) s → s 2 1124 = true) ∧
    (∃ s, BandRun (lut2 xor) (skewA 45 100) (skewA 124 100) (skewIn 1000) s ∧
      s 2 1045 = true) :=
  ce_skew (by omega) (by omega) (by omega) (by omega) (by omega)

/-- `d'` lies within relative scatter `κ = num/den` of the annotated `d`. -/
def InScatter (num den d d' : Nat) : Prop := d * (den - num) ≤ d' * den ∧ d' * den ≤ d * (den + num)

/-- (b)(i) within ONE corner: a 118 ps skew; the LUT at 118 ps is within 5 %
scatter of the annotated 124 ps, and the GLS there glitches. -/
theorem ce_skew_kappa :
    InScatter 5 100 124 118 ∧
    (∀ s, GLSRun (lut2 xor) (skewA 124 118) (skewIn 1000) s → ∀ t, s 2 t = false) ∧
    (∀ s, GLSRun (lut2 xor) (skewA 118 118) (skewIn 1000) s → s 2 1118 = true) :=
  ⟨by unfold InScatter; decide, (ce_skew (d' := 118) (lo := 0) (by omega) (by omega) (by omega) (by omega)
      (by omega)).1,
    (ce_skew (d := 124) (lo := 0) (by omega) (by omega) (by omega) (by omega) (by omega)).2.1⟩

/-- A one-LUT net with three primary inputs (0, 1, 2) and an XOR3 LUT (3):
the data LUT of a bundled-data stage whose function value can glitch. -/
def lut3x : Net := ⟨3, 4, fun _ v => xor (xor (v 0) (v 1)) (v 2)⟩

theorem lut3x_acyclic : Acyclic lut3x := by
  intro k h1 h2 u v h
  simp only [lut3x] at h1 h2 ⊢
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega)]

theorem lut3x_run {σ : Sem} {A : Asg} {inp s : Nat → Sig} (h : SemRun σ lut3x A inp s) :
    s 3 = σ.ch (A.d 3) (fun t => xor (xor (delay (A.w 3 0) (inp 0) t)
      (delay (A.w 3 1) (inp 1) t)) (delay (A.w 3 2) (inp 2) t)) := by
  rw [h.2.1 3 (by simp [lut3x]) (by simp [lut3x])]
  have e0 := h.1 0 (by simp [lut3x])
  have e1 := h.1 1 (by simp [lut3x])
  have e2 := h.1 2 (by simp [lut3x])
  congr 1
  funext t
  simp only [fval, pins, wired, lut3x, e0, e1, e2]
  simp

/-- LUT delay `d`, wires 0 (the skew is in the stimulus). -/
def capA (d : Nat) : Asg := ⟨fun _ => d, fun _ _ => 0⟩

/-- The data inputs rise at `1`, `d0` and `2 d0 - 1`: the XOR3 function value
goes 0, 1, 0, 1 (the audit's `tb_impact` shape). -/
def capIn (d0 : Nat) : Nat → Sig :=
  fun j => if j = 0 then step 1 else if j = 1 then step d0 else step (2 * d0 - 1)

theorem cap_fval {d0 d : Nat} (h : 2 ≤ d0) :
    (fun t => xor (xor (delay ((capA d).w 3 0) (capIn d0 0) t)
      (delay ((capA d).w 3 1) (capIn d0 1) t)) (delay ((capA d).w 3 2) (capIn d0 2) t)) =
    early d0 1 := by
  funext t
  simp only [capA, capIn, delay, Nat.sub_zero]
  simp only [show ((1 : Nat) = 0) = False by decide, show ((2 : Nat) = 0) = False by decide,
    show ((2 : Nat) = 1) = False by decide, ↓reduceIte]
  simp only [step, early]
  by_cases c1 : 1 ≤ t <;> by_cases c2 : d0 ≤ t <;> by_cases c3 : 2 * d0 - 1 ≤ t <;>
    simp [c1, c2, c3] <;> omega

/-- (b) Bundled-data capture, general `d0 ≥ 2`. The data LUT (XOR3, delay
`d0`) sees its inputs rise at `1`, `d0`, `2 d0 - 1`; its final value is `1`.
A latch captures it when the request arrives at `T`.
* The GLS run shows the data `1` from `2 d0` on: a request at `T = 2 d0`,
  one step after the last data input moved, captures the right value.
* (ii) The pure-delay LUT at the same `d0` still shows `0` at `2 d0`; it
  shows the final value only from `3 d0 - 1`. -/
theorem ce_capture {d0 : Nat} (h : 2 ≤ d0) :
    (∀ s, GLSRun lut3x (capA d0) (capIn d0) s → ∀ t, 2 * d0 ≤ t → s 3 t = true) ∧
    (∀ s, SemRun .transport lut3x (capA d0) (capIn d0) s →
      s 3 (2 * d0) = false ∧ ∀ t, 3 * d0 - 1 ≤ t → s 3 t = true) := by
  constructor
  · intro s hs t ht
    rw [lut3x_run hs, cap_fval h]
    simp only [Sem.ch, capA]
    rw [saf_early_val (by omega) (by omega)]
    simp; omega
  · intro s hs
    rw [lut3x_run hs, cap_fval h]
    simp only [Sem.ch, capA, delay, early]
    constructor
    · simp; omega
    · intro t ht; simp; omega

/-- (b) Numbers (O6 annotated 124 ps; inputs at 1, 124, 247 ps; request at
248 ps). The GLS at 124 captures `1`. (i) The GLS at 123 ps, inside the O6
band [45, 124] and within 1 % scatter of 124, captures `0`: a FASTER LUT
fails where the slow arc passed, so the annotated maximum is not a
conservative corner. (ii) Transport and inertial LUTs at 124 capture `0`. -/
theorem ce_capture_124 :
    (∀ s, GLSRun lut3x (capA 124) (capIn 124) s → s 3 248 = true) ∧
    InScatter 1 100 124 123 ∧
    (∀ s, GLSRun lut3x (capA 123) (capIn 124) s → s 3 248 = false) ∧
    (∀ s, SemRun .transport lut3x (capA 124) (capIn 124) s → s 3 248 = false) ∧
    (∀ s, SemRun .inertial lut3x (capA 124) (capIn 124) s → s 3 248 = false) := by
  refine ⟨fun s hs => (ce_capture (d0 := 124) (by omega)).1 s hs 248 (by omega),
    by unfold InScatter; decide, ?_,
    fun s hs => ((ce_capture (d0 := 124) (by omega)).2 s hs).1, ?_⟩
  · intro s hs
    rw [lut3x_run hs, cap_fval (d0 := 124) (by omega)]
    decide
  · intro s hs
    rw [lut3x_run hs, cap_fval (d0 := 124) (by omega)]
    set_option maxRecDepth 20000 in decide

/-- (b) The annotated build (wire = specify path = SAF) and the baked build
(wire = transport) differ on any wire pulse narrower than the wire delay. -/
theorem annotated_ne_baked {p v w : Nat} (hp : 1 ≤ p) (hv : 1 ≤ v) (hvw : v < w) :
    saf w (pulse false p v) ≠ delay w (pulse false p v) := by
  intro h
  have := congrFun h (p + w)
  rw [saf_pulse_short hp hvw] at this
  simp [delay, pulse_false_eq] at this
  omega

/-! ### A C-element (`bd_c2`, feedback) -/

/-- (a) With feedback the run is fixed by its time-0 state: two GLS runs that
agree at step 0 on every LUT output are equal (LUT delays `≥ 1`). This is
what makes "the GLS run from reset state `q0`" a single behaviour. -/
theorem gls_unique_time {N : Net} {A : Asg} {inp s s' : Nat → Sig}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) (h : GLSRun N A inp s)
    (h' : GLSRun N A inp s') (h0 : ∀ k, N.m ≤ k → k < N.n → s k 0 = s' k 0) : s = s' := by
  have key : ∀ t k u, u ≤ t → s k u = s' k u := by
    intro t
    induction t with
    | zero =>
      intro k u hu
      rw [show u = 0 by omega]
      by_cases h1 : k < N.m
      · rw [h.1 k h1, h'.1 k h1]
      · by_cases h2 : k < N.n
        · exact h0 k (by omega) h2
        · rw [h.2.2 k (by omega), h'.2.2 k (by omega)]
    | succ t ih =>
      intro k u hu
      by_cases hut : u ≤ t
      · exact ih k u hut
      · have hu' : u = t + 1 := by omega
        subst hu'
        by_cases h1 : k < N.m
        · rw [h.1 k h1, h'.1 k h1]
        · by_cases h2 : k < N.n
          · have ex : ∀ v, v ≤ t →
                fval N k (wired A k s) v = fval N k (wired A k s') v := by
              intro v hv
              simp only [fval]
              congr 1; funext j; simp only [pins, wired, delay]; split
              · exact ih j _ (by omega)
              · rfl
            have es := congrFun (h.2.1 k (by omega) h2) (t + 1)
            have es' := congrFun (h'.2.1 k (by omega) h2) (t + 1)
            have et := congrFun (h.2.1 k (by omega) h2) t
            have et' := congrFun (h'.2.1 k (by omega) h2) t
            simp only [Sem.ch, saf_succ] at es es' et et'
            rw [es, es']
            have hf : fireB (A.d k) (fval N k (wired A k s)) t =
                fireB (A.d k) (fval N k (wired A k s')) t := by
              simp only [fireB]
              by_cases hdt : A.d k ≤ t
              · rw [ex (t - A.d k + 1) (by have := hd k (by omega) h2; omega),
                  ex (t - A.d k) (by omega)]
              · simp [hdt]
            rw [hf, ex t (Nat.le_refl t), ← et, ← et', ih k t (Nat.le_refl t)]
          · rw [h.2.2 k (by omega), h'.2.2 k (by omega)]
  funext k u; exact key u k u (Nat.le_refl u)

/-- Majority: `bd_c2`'s function with `rst` low (INIT `0xE8` on A1, A2, A3,
`q` fed back to A3). -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- `bd_c2` as a net: inputs `a` (0), `b` (1); the LUT (2) reads its own
output through a wire (here of delay 0, `capA`). -/
def c2 : Net := ⟨2, 3, fun _ v => maj (v 0) (v 1) (v 2)⟩

/-- `b` falls at `P + σ`. -/
def bIn (P σ : Nat) : Sig := fun t => !decide (P + σ ≤ t)

/-- The `a, b : 01 → 10` stimulus with skew `σ`: `a` rises at `P`, `b` falls
at `P + σ` (A-gls-compare §3). -/
def c2In (P σ : Nat) : Nat → Sig := fun j => if j = 0 then step P else bIn P σ

/-- A candidate `c2` run with LUT output `q`. -/
def c2Cand (P σ : Nat) (q : Sig) : Nat → Sig :=
  fun k => if k = 0 then step P else if k = 1 then bIn P σ else if k = 2 then q else fun _ => false

theorem c2_fval {d P σ : Nat} (q : Sig) :
    fval c2 2 (wired (capA d) 2 (c2Cand P σ q)) = fun t => maj (step P t) (bIn P σ t) (q t) := by
  funext t; simp [fval, pins, wired, c2, c2Cand, capA, delay]

theorem c2_cand_run {S : Sem} {d P σ : Nat} {q : Sig}
    (hq : q = S.ch d (fun t => maj (step P t) (bIn P σ t) (q t))) :
    SemRun S c2 (capA d) (c2In P σ) (c2Cand P σ q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [c2] at hk
    by_cases h0 : k = 0
    · subst h0; rfl
    · simp [c2Cand, c2In, show k = 1 by omega]
  · intro k h1 h2
    simp only [c2] at h1 h2
    have hk : k = 2 := by omega
    subst hk
    rw [c2_fval]
    simpa [c2Cand, capA] using hq
  · intro k hk
    simp only [c2] at hk
    simp [c2Cand, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

theorem c2_hold_fval {P σ : Nat} :
    (fun t => maj (step P t) (bIn P σ t) ((fun _ => false) t)) = pulse false P σ := by
  funext t
  rw [pulse_false_eq]
  simp only [maj, step, bIn]
  by_cases c1 : P ≤ t <;> by_cases c2 : P + σ ≤ t <;> simp [c1, c2] <;> omega

theorem c2_flip_fval {P σ d' : Nat} (hd' : d' ≤ σ) :
    (fun t => maj (step P t) (bIn P σ t) (step (P + d') t)) = step P := by
  funext t
  simp only [maj, step, bIn]
  by_cases c1 : P ≤ t <;> by_cases c2 : P + σ ≤ t <;> by_cases c3 : P + d' ≤ t <;>
    simp [c1, c2, c3] <;> omega

theorem rising_step (P : Nat) : Rising (step P) := by
  intro a b hab ha; simp only [step, decide_eq_true_eq] at ha ⊢; omega

theorem delay_step {P d : Nat} (hP : 1 ≤ P) : delay d (step P) = step (P + d) := by
  funext t; simp only [delay, step]; simp only [decide_eq_decide]; omega

/-- (b) `bd_c2` (C-element as a LUT with its output fed back), from reset state
`q = 0`, inputs `01 → 10` with skew `σ` (`a` rises at `P`, `b` falls at
`P + σ`), annotated LUT delay `d > σ`.
* The GLS run holds `q = 0` (the overlap `a = b = 1` of width `σ` is swallowed).
* (i) The GLS run at any LUT delay `d' ≤ σ` latches `q = 1` at `P + d'`.
* (ii) The pure-delay LUT at the same `d` latches `q = 1` at `P + d`.
* (iii) The envelope `[lo, d]` admits a behaviour that latches at `P + lo`,
  for every `1 ≤ lo ≤ σ`.
So a GLS pass ("the C-element holds") at one assignment says nothing about
the band: the GLS threshold is the arc of the annotated delay, not a property
of the cell (A-gls-compare §3; the board's unexplained arbiter fires). -/
theorem ce_c2 {P σ d d' lo : Nat} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (hσd : σ < d) (hd' : 1 ≤ d')
    (hd'σ : d' ≤ σ) (hlo : lo ≤ σ) :
    (∀ s, GLSRun c2 (capA d) (c2In P σ) s → s 2 0 = false → ∀ t, s 2 t = false) ∧
    (∀ s, GLSRun c2 (capA d') (c2In P σ) s → s 2 0 = false → s 2 (P + d') = true) ∧
    (∀ s, SemRun .transport c2 (capA d) (c2In P σ) s → s 2 (P + d) = true) ∧
    (∃ s, BandRun c2 (capA lo) (capA d) (c2In P σ) s ∧ s 2 0 = false ∧
      s 2 (P + lo) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs h0 t
    have hq : (fun _ => false) =
        Sem.saf.ch d (fun t => maj (step P t) (bIn P σ t) ((fun _ => false) t)) := by
      rw [c2_hold_fval]; funext t; exact (saf_pulse_short hP hσd t).symm
    have e := gls_unique_time (fun k _ _ => by simp [capA]; omega) hs (c2_cand_run hq)
      (fun k h1 h2 => by
        simp only [c2] at h1 h2
        rw [show k = 2 by omega, h0]; rfl)
    rw [e]; rfl
  · intro s hs h0
    have hq : step (P + d') =
        Sem.saf.ch d' (fun t => maj (step P t) (bIn P σ t) (step (P + d') t)) := by
      rw [c2_flip_fval hd'σ]
      simp only [Sem.ch]
      rw [saf_of_rising hd' (rising_step P), delay_step hP]
    have e := gls_unique_time (fun k _ _ => by simp [capA]; omega) hs (c2_cand_run hq)
      (fun k h1 h2 => by
        simp only [c2] at h1 h2
        rw [show k = 2 by omega, h0]; simp [c2Cand, step]; omega)
    rw [e]; simp [c2Cand, step]
  · intro s hs
    have e := congrFun (hs.2.1 2 (by simp [c2]) (by simp [c2])) (P + d)
    have e0 := hs.1 0 (by simp [c2])
    have e1 := hs.1 1 (by simp [c2])
    rw [e]
    simp only [Sem.ch, delay, fval, pins, wired, capA, c2, e0, e1]
    simp [c2In, step, bIn, maj]
    omega
  · refine ⟨c2Cand P σ (step (P + lo)), ⟨?_, ?_, ?_⟩, by simp [c2Cand, step]; omega,
      by simp [c2Cand, step]⟩
    · exact (c2_cand_run (S := .transport) (d := lo) (q := step (P + lo)) (by
        rw [c2_flip_fval hlo]; simp only [Sem.ch]; rw [delay_step hP])).1
    · intro k h1 h2
      simp only [c2] at h1 h2
      have hk : k = 2 := by omega
      subst hk
      refine ⟨wired (capA lo) 2 (c2Cand P σ (step (P + lo))),
        fun j _ => delay_transport _ _, ?_⟩
      rw [c2_fval, c2_flip_fval hlo]
      have := transport_mono (Nat.le_refl lo) (show lo ≤ d by omega)
        (delay_transport lo (step P))
      rw [delay_step hP] at this
      simpa [c2Cand, capA] using this
    · exact (c2_cand_run (S := .transport) (d := lo) (q := step (P + lo)) (by
        rw [c2_flip_fval hlo]; simp only [Sem.ch]; rw [delay_step hP])).2.2

/-- (b) Numbers: skew 100 ps, O6 annotated 124 ps: the GLS holds; at 100 ps
(inside [45, 124]) the GLS latches; transport at 124 latches; the envelope
[45, 124] admits a latch at 1045. -/
theorem ce_c2_124 :
    (∀ s, GLSRun c2 (capA 124) (c2In 1000 100) s → s 2 0 = false → ∀ t, s 2 t = false) ∧
    (∀ s, GLSRun c2 (capA 100) (c2In 1000 100) s → s 2 0 = false → s 2 1100 = true) ∧
    (∀ s, SemRun .transport c2 (capA 124) (c2In 1000 100) s → s 2 1124 = true) ∧
    (∃ s, BandRun c2 (capA 45) (capA 124) (c2In 1000 100) s ∧ s 2 0 = false ∧
      s 2 1045 = true) :=
  ce_c2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## (c) A sufficient condition: rising stimulus, monotone LUTs, no feedback -/

/-- Mask a pin family to the pins `j < k`. -/
def mask (k : Nat) (ws : Nat → Sig) : Nat → Sig := fun j => if j < k then ws j else fun _ => false

theorem fval_mask {N : Net} (hN : Acyclic N) {k : Nat} (h1 : N.m ≤ k) (h2 : k < N.n)
    (ws : Nat → Sig) : fval N k ws = fval N k (mask k ws) :=
  fval_congr hN h1 h2 (fun j hj => by simp [mask, hj])

theorem fval_rising {N : Net} {k : Nat} (hF : MonoF (N.f k)) {ws : Nat → Sig}
    (h : ∀ j, Rising (ws j)) : Rising (fval N k ws) := by
  intro a b hab ha
  apply hF _ _ _ ha
  intro j hj
  simp only [pins] at hj ⊢
  split
  · rename_i hjn; simp only [hjn, ↓reduceIte] at hj; exact h j a b hab hj
  · rename_i hjn; simp only [hjn, ↓reduceIte] at hj; exact hj

theorem fval_sle {N : Net} {k : Nat} (hF : MonoF (N.f k)) {ws ws' : Nat → Sig}
    (h : ∀ j, SLe (ws j) (ws' j)) : SLe (fval N k ws) (fval N k ws') := by
  intro t ht
  apply hF _ _ _ ht
  intro j hj
  simp only [pins] at hj ⊢
  split
  · rename_i hjn; simp only [hjn, ↓reduceIte] at hj; exact h j t hj
  · rename_i hjn; simp only [hjn, ↓reduceIte] at hj; exact hj

theorem mask_rising {k : Nat} {ws : Nat → Sig} (h : ∀ j, j < k → Rising (ws j)) :
    ∀ j, Rising (mask k ws j) := by
  intro j; simp only [mask]; split
  · rename_i hj; exact h j hj
  · exact rising_const_false

theorem mask_sle {k : Nat} {ws ws' : Nat → Sig} (h : ∀ j, j < k → SLe (ws j) (ws' j)) :
    ∀ j, SLe (mask k ws j) (mask k ws' j) := by
  intro j; simp only [mask]; split
  · rename_i hj; exact h j hj
  · exact fun _ h => h

/-- Hypotheses of (c) on the circuit and stimulus. -/
structure MonoCirc (N : Net) (inp : Nat → Sig) : Prop where
  acyclic : Acyclic N
  mono : ∀ k, N.m ≤ k → k < N.n → MonoF (N.f k)
  rising : ∀ k, k < N.m → Rising (inp k)

/-- (c) On a monotone circuit with a rising stimulus, every signal of the GLS
run rises at most once and the GLS run is the pure-delay run at the same
assignment (the `Faithful` monitor is automatically clean). -/
theorem mono_saf_is_transport {N : Net} {inp : Nat → Sig} (C : MonoCirc N inp) {A : Asg}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) {g : Nat → Sig} (hg : GLSRun N A inp g) :
    (∀ k, Rising (g k)) ∧ SemRun .transport N A inp g := by
  have hr : ∀ k, Rising (g k) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases h1 : k < N.m
      · rw [hg.1 k h1]; exact C.rising k h1
      · by_cases h2 : k < N.n
        · rw [hg.2.1 k (by omega) h2]
          simp only [Sem.ch]
          have hx : Rising (fval N k (wired A k g)) := by
            rw [fval_mask C.acyclic (by omega) h2]
            exact fval_rising (C.mono k (by omega) h2)
              (mask_rising (fun j hj => rising_delay _ (ih j hj)))
          rw [saf_of_rising (hd k (by omega) h2) hx]
          exact rising_delay _ hx
        · rw [hg.2.2 k (by omega)]; exact rising_const_false
  refine ⟨hr, hg.1, ?_, hg.2.2⟩
  intro k h1 h2
  rw [hg.2.1 k h1 h2]
  simp only [Sem.ch]
  exact saf_of_rising (hd k h1 h2)
    (fval_rising (C.mono k h1 h2) (fun j => rising_delay _ (hr j)))

/-- `A` bounds the band from above, arc by arc. -/
def Asg.Le (N : Net) (B A : Asg) : Prop :=
  (∀ k, N.m ≤ k → k < N.n → B.d k ≤ A.d k) ∧
  (∀ k j, N.m ≤ k → k < N.n → j < N.n → B.w k j ≤ A.w k j)

/-- (c) Upper bracket. Every envelope behaviour whose per-arc maxima are at most
the GLS assignment is pointwise at least the GLS run: whatever is high in the
GLS run at `t` is high in the behaviour at `t`. -/
theorem band_bracket_hi {N : Net} {inp : Nat → Sig} (C : MonoCirc N inp) {A lo hi : Asg}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) {g s : Nat → Sig} (hg : GLSRun N A inp g)
    (hs : BandRun N lo hi inp s) (hle : Asg.Le N hi A) :
    ∀ k, Rising (s k) ∧ SLe (g k) (s k) := by
  obtain ⟨hgr, hgt⟩ := mono_saf_is_transport C hd hg
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h1 : k < N.m
    · rw [hs.1 k h1, hgt.1 k h1]; exact ⟨C.rising k h1, fun _ h => h⟩
    · by_cases h2 : k < N.n
      · obtain ⟨ws, hws, hlut⟩ := hs.2.1 k (by omega) h2
        have hwr : ∀ j, j < k → Rising (ws j) :=
          fun j hj => transport_rising (hws j (by omega)) (ih j hj).1
        have hxs : Rising (fval N k ws) := by
          rw [fval_mask C.acyclic (by omega) h2]
          exact fval_rising (C.mono k (by omega) h2) (mask_rising hwr)
        have hle_x : SLe (fval N k (wired A k g)) (fval N k ws) := by
          rw [fval_mask C.acyclic (by omega) h2 (wired A k g),
            fval_mask C.acyclic (by omega) h2 ws]
          apply fval_sle (C.mono k (by omega) h2)
          apply mask_sle
          intro j hj
          exact sle_trans (sle_delay _ (ih j hj).2)
            (transport_ge (hws j (by omega)) (ih j hj).1 (hle.2 k j (by omega) h2 (by omega)))
        refine ⟨transport_rising hlut hxs, ?_⟩
        rw [hgt.2.1 k (by omega) h2]
        simp only [Sem.ch]
        exact sle_trans (sle_delay _ hle_x) (transport_ge hlut hxs (hle.1 k (by omega) h2))
      · rw [hs.2.2 k (by omega), hgt.2.2 k (by omega)]
        exact ⟨rising_const_false, fun _ h => h⟩

/-- (c) Lower bracket. Every envelope behaviour whose per-arc minima are at
least the GLS assignment is pointwise at most the GLS run: nothing rises in
the behaviour before it rises in the GLS run. -/
theorem band_bracket_lo {N : Net} {inp : Nat → Sig} (C : MonoCirc N inp) {A lo hi : Asg}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) {g s : Nat → Sig} (hg : GLSRun N A inp g)
    (hs : BandRun N lo hi inp s) (hle : Asg.Le N A lo) :
    ∀ k, Rising (s k) ∧ SLe (s k) (g k) := by
  obtain ⟨hgr, hgt⟩ := mono_saf_is_transport C hd hg
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h1 : k < N.m
    · rw [hs.1 k h1, hgt.1 k h1]; exact ⟨C.rising k h1, fun _ h => h⟩
    · by_cases h2 : k < N.n
      · obtain ⟨ws, hws, hlut⟩ := hs.2.1 k (by omega) h2
        have hwr : ∀ j, j < k → Rising (ws j) :=
          fun j hj => transport_rising (hws j (by omega)) (ih j hj).1
        have hxs : Rising (fval N k ws) := by
          rw [fval_mask C.acyclic (by omega) h2]
          exact fval_rising (C.mono k (by omega) h2) (mask_rising hwr)
        have hle_x : SLe (fval N k ws) (fval N k (wired A k g)) := by
          rw [fval_mask C.acyclic (by omega) h2 (wired A k g),
            fval_mask C.acyclic (by omega) h2 ws]
          apply fval_sle (C.mono k (by omega) h2)
          apply mask_sle
          intro j hj
          exact sle_trans
            (transport_le (hws j (by omega)) (ih j hj).1 (hle.2 k j (by omega) h2 (by omega)))
            (sle_delay _ (ih j hj).2)
        refine ⟨transport_rising hlut hxs, ?_⟩
        rw [hgt.2.1 k (by omega) h2]
        simp only [Sem.ch]
        exact sle_trans (transport_le hlut hxs (hle.1 k (by omega) h2)) (sle_delay _ hle_x)
      · rw [hs.2.2 k (by omega), hgt.2.2 k (by omega)]
        exact ⟨rising_const_false, fun _ h => h⟩

/-- (c) One GLS run at the per-arc maxima `A` showing signal `k` high at `T`
implies: in every envelope behaviour with per-arc maxima `≤ A` (any minima,
so any delay assignment below `A` and any transport behaviour within it),
signal `k` is high at every `t ≥ T`. -/
theorem gls_mono_settle_band {N : Net} {inp : Nat → Sig} (C : MonoCirc N inp) {A lo hi : Asg}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) {g s : Nat → Sig} (hg : GLSRun N A inp g)
    (hs : BandRun N lo hi inp s) (hle : Asg.Le N hi A) {k T : Nat} (hT : g k T = true) :
    ∀ t, T ≤ t → s k t = true :=
  fun t ht => (band_bracket_hi C hd hg hs hle k).2 t
    ((mono_saf_is_transport C hd hg).1 k T t ht hT)

/-- (c) The same for another GLS run (or pure-delay run) at any assignment
`A' ≤ A` arc by arc: one pass at the maxima covers every assignment below. -/
theorem gls_mono_settle_assign {N : Net} {inp : Nat → Sig} (C : MonoCirc N inp) {A A' : Asg}
    (hd : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A.d k) (hd' : ∀ k, N.m ≤ k → k < N.n → 1 ≤ A'.d k)
    {g g' : Nat → Sig} (hg : GLSRun N A inp g) (hg' : GLSRun N A' inp g') (hle : Asg.Le N A' A)
    {k T : Nat} (hT : g k T = true) : ∀ t, T ≤ t → g' k t = true :=
  gls_mono_settle_band C hd hg (transport_in_band (mono_saf_is_transport C hd' hg').2) hle hT

/-- (c) Bundled data from two GLS runs. Run `gF` at the all-fast-min
assignment `AF`, run `gS` at the all-slow-max assignment `AS`. If the data
signal `kd` is high at `T` in the slow run and the request `kr` is low before
`T` in the fast run, then in every envelope behaviour with per-arc band inside
`[AF, AS]` the request is never high while the data is not. -/
theorem gls_mono_bundle {N : Net} {inp : Nat → Sig} (C : MonoCirc N inp) {AF AS lo hi : Asg}
    (hdF : ∀ k, N.m ≤ k → k < N.n → 1 ≤ AF.d k) (hdS : ∀ k, N.m ≤ k → k < N.n → 1 ≤ AS.d k)
    {gF gS s : Nat → Sig} (hgF : GLSRun N AF inp gF) (hgS : GLSRun N AS inp gS)
    (hs : BandRun N lo hi inp s) (hlo : Asg.Le N AF lo) (hhi : Asg.Le N hi AS)
    {kd kr T : Nat} (hdata : gS kd T = true) (hreq : ∀ t, t < T → gF kr t = false) :
    ∀ t, s kr t = true → s kd t = true := by
  intro t ht
  have h1 := (band_bracket_lo C hdF hgF hs hlo kr).2 t ht
  have hT : T ≤ t := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    rw [hreq t hlt] at h1; exact absurd h1 (by decide)
  exact gls_mono_settle_band C hdS hgS hs hhi hdata t hT

end Formal.Core.GLSPass
