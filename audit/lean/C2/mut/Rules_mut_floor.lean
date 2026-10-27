import Formal.Net.Prelim

/-!
# Probe C-10b: what the post-route rules E, A and J establish, and when

The three rules (cells/verify/skew.py = E, cells/verify/tighten.py rule A,
cells/verify/arb_fork.py = J) all check one shape of property: a race between
two signals launched by ONE event, where one of them (the "late" side: rule
E's select, rule A's peer data outputs, rule J's A0 fall at `ua_k`) must have
settled before the other (the "early" side: the request, the request, the
grant at `ua_k`) first moves. `Bundled` below is that property, over the
bounded-delay traces of `Formal.Net.Prelim`.

Contents.
1. `Window`: a signal that is `v` up to `a` and `w` after `b`; `arc_window`:
   an H_BOUNDED_DELAY arc maps a window `[a,b]` to `[a+lo, b+hi]`;
   `Chain`/`chain_window`: the same along a path (sum of `lo`s / `hi`s);
   `gate_window`: a zero-delay function of delayed pin copies (the per-pin
   input-delay LUT model) takes the min / max over its inputs. This is exactly
   static timing analysis with interval bounds, proved sound for the trace
   semantics.
2. `race_sound`: interval STA (late side's sum of `hi` + launch window width
   < early side's sum of `lo`) implies `Bundled`. With a clean launch edge the
   launch window has width 0 (`race_sound_clean`).
3. The rules as implemented, as arithmetic on SDF numbers, and when they imply
   the interval premise: `ruleE_sound` (under the per-element scatter band
   H_BAND_772_1155 that skew.py's constants claim, plus H_CLEAN_EDGE at the
   divergence point), `ruleA_band_sound_small` / `ruleA_not_band_sound`
   (rule A's `max(0.2 t, 200 ps)` is weaker than that band for every
   `t_data >= 404 ps`).
4. Counterexample netlists, each with concrete traces that satisfy every arc
   relation (`shift_bd`) and on which the rule passes but `Bundled` fails:
   * `ruleA_counterexample`  (rule A vs the band skew.py adopts),
   * `ruleE_corner_counterexample` (one-corner model, fast corner, prjxray-db
     intervals, SDF = slow max + RC as nextpnr writes it; not routable),
   * `ruleE_sitepin_fails_all` (slow corner: the LUT site-pin delay prjxray-db
     has and nextpnr's SDF drops; fails for EVERY delay choice, and
     `ruleE_sitepin_nonvacuous` shows the arcs are satisfiable),
   * `ruleJ_counterexample` (rule J's shared-route credit, estimated from pip
     counts, over-credits; fails inside the rule's own band),
   * `prefix_credit_needs_clean_edge` (crediting a shared prefix is unsound
     when the divergence node can glitch, which H_BOUNDED_DELAY allows).

Time is `Nat` ticks of 1 ps. Core Lean only.

Hypotheses (named in the statements):
* H_BOUNDED_DELAY (`BoundedDelay`, Formal/Net/Prelim): each arc, wire or
  sensitized gate pin, delays every change by some amount in `[lo, hi]`.
* H_SENSITIZED: a path through a multi-input gate is a `Chain` arc only while
  the gate's side inputs are stable (the single-launch assumption every STA,
  and every one of these rules, makes). `gate_window` is the general form.
* H_CLEAN_EDGE (`Window v w τ τ X`): the divergence node makes ONE transition.
  True for a pure delay of a clean edge (`shift_window`); false in general for
  H_BOUNDED_DELAY (`prefix_credit_needs_clean_edge`).
* H_BAND_772_1155 (`BandLo 772`, `BandHi 1155`): every element's real delay is
  in `[0.772 D, 1.155 D]` of its SDF number `D`; skew.py's 95/95 tolerance
  band from five measured rings, applied per element.
* H_ONE_CORNER: all elements sit in the interval of the same PVT corner
  (prjxray-db fast or slow); the counterexamples choose all-fast or all-slow.
-/

namespace AuditRulesMut
open Formal.Net

/-! ## 1. Windows and their propagation -/

/-- `s` is `v` at every tick up to `a`, and `w` at every tick after `b`.
Between the two it may do anything (glitch). -/
def Window (v w : Bool) (a b : Nat) (s : Trace) : Prop :=
  (∀ t, t ≤ a → s t = v) ∧ (∀ t, b < t → s t = w)

theorem Window.mono {v w : Bool} {a b a' b' : Nat} {s : Trace}
    (h : Window v w a b s) (ha : a' ≤ a) (hb : b ≤ b') : Window v w a' b' s :=
  ⟨fun t ht => h.1 t (by omega), fun t ht => h.2 t (by omega)⟩

/-- One arc under H_BOUNDED_DELAY: the output starts moving no earlier than
`lo` after the input did, and has settled no later than `hi` after. -/
theorem arc_window {lo hi : Nat} {i o : Trace} {v w : Bool} {a b : Nat}
    (hd : BoundedDelay lo hi i o) (h0 : o 0 = v) (hw : Window v w a b i) :
    Window v w (a + lo) (b + hi) o := by
  constructor
  · intro t
    induction t with
    | zero => intro _; exact h0
    | succ n ih =>
      intro hn
      by_cases hc : o n = o (n + 1)
      · rw [← hc]; exact ih (by omega)
      · obtain ⟨d, hlo, _, hdt, hval⟩ := hd.cause n hc
        rw [hval]; exact hw.1 _ (by omega)
  · intro t ht
    have hst : stableOn i (t - hi) t := by
      intro t' h1 _
      rw [hw.2 t' (by omega), hw.2 (t - hi) (by omega)]
    rw [hd.settle t (by omega) hst]
    exact hw.2 t (by omega)

/-- A path: consecutive H_BOUNDED_DELAY arcs with intervals `(lo, hi)`, every
intermediate node at rest (same initial value) at time 0. -/
inductive Chain : List (Nat × Nat) → Trace → Trace → Prop
  | nil (s : Trace) : Chain [] s s
  | cons {lo hi : Nat} {es : List (Nat × Nat)} {s m o : Trace} :
      BoundedDelay lo hi s m → m 0 = s 0 → Chain es m o → Chain ((lo, hi) :: es) s o

def sumLo : List (Nat × Nat) → Nat
  | [] => 0
  | e :: es => e.1 + sumLo es

def sumHi : List (Nat × Nat) → Nat
  | [] => 0
  | e :: es => e.2 + sumHi es

def sumN : List Nat → Nat
  | [] => 0
  | d :: ds => d + sumN ds

/-- Pointwise relation between a list of numbers and a list of intervals
(core Lean has no `List.Forall₂`). -/
inductive Forall2 (P : Nat → Nat × Nat → Prop) : List Nat → List (Nat × Nat) → Prop
  | nil : Forall2 P [] []
  | cons {d : Nat} {e : Nat × Nat} {ds : List Nat} {es : List (Nat × Nat)} :
      P d e → Forall2 P ds es → Forall2 P (d :: ds) (e :: es)

/-- A Boolean evaluator for `Forall2`, so concrete instances close by `decide`. -/
def forall2b (r : Nat → Nat × Nat → Bool) : List Nat → List (Nat × Nat) → Bool
  | [], [] => true
  | d :: ds, e :: es => r d e && forall2b r ds es
  | _, _ => false

theorem forall2_of_check {P : Nat → Nat × Nat → Prop} [∀ d e, Decidable (P d e)] :
    ∀ {ds : List Nat} {es : List (Nat × Nat)},
      forall2b (fun d e => decide (P d e)) ds es = true → Forall2 P ds es
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
      simp only [forall2b, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .cons h.1 (forall2_of_check h.2)
  | [], _ :: _, h => by simp [forall2b] at h
  | _ :: _, [], h => by simp [forall2b] at h

theorem chain_window {es : List (Nat × Nat)} {s o : Trace} (hc : Chain es s o) :
    ∀ {v w : Bool} {a b : Nat}, Window v w a b s →
      Window v w (a + sumLo es) (b + sumHi es) o := by
  induction hc with
  | nil s => intro v w a b hw; simpa [sumLo, sumHi] using hw
  | cons hd h0 _ ih =>
    intro v w a b hw
    have hm := arc_window hd (by rw [h0]; exact hw.1 0 (Nat.zero_le _)) hw
    exact (ih hm).mono (by simp [sumLo]; omega) (by simp [sumHi]; omega)

/-- The per-pin input-delay gate model (each pin a delayed copy `ins j`, the
LUT a zero-delay function `f` of the copies): the output's window is the
intersection of the input windows. With `arc_window` this is the induction
step of interval STA over a DAG; `Chain` is its single-path case. -/
theorem gate_window {n : Nat} (f : (Fin n → Bool) → Bool) (ins : Fin n → Trace)
    (out : Trace) (hout : ∀ t, out t = f (fun j => ins j t))
    (vs ws : Fin n → Bool) (a b : Nat) (h : ∀ j, Window (vs j) (ws j) a b (ins j)) :
    Window (f vs) (f ws) a b out := by
  constructor
  · intro t ht
    rw [hout]; congr 1; funext j; exact (h j).1 t ht
  · intro t ht
    rw [hout]; congr 1; funext j; exact (h j).2 t ht

/-! ## 2. The property, and interval STA proves it -/

/-- The race property all three rules are about: once `early` has moved at
all, `late` already holds its final value `w`, and keeps it. -/
def Bundled (late : Trace) (w : Bool) (early : Trace) : Prop :=
  ∀ t, early t ≠ early 0 → ∀ t', t ≤ t' → late t' = w

/-- Interval STA is sound: both sides launched by one node `L` whose
transition lies in `[a, b]`; if the late side's latest settle beats the
early side's earliest move, the property holds. -/
theorem race_sound {er es : List (Nat × Nat)} {L early late : Trace}
    {v w : Bool} {a b : Nat}
    (hL : Window v w a b L) (he : Chain er L early) (hl : Chain es L late)
    (h : b + sumHi es < a + sumLo er) : Bundled late w early := by
  have hE := chain_window he hL
  have hS := chain_window hl hL
  intro t ht t' htt'
  have h0 : early 0 = v := hE.1 0 (Nat.zero_le _)
  have hlt : a + sumLo er < t := by
    apply Nat.lt_of_not_le; intro hle
    exact ht (by rw [hE.1 t hle, h0])
  exact hS.2 t' (by omega)

/-- With a clean launch edge (H_CLEAN_EDGE, width 0) only the two path sums
matter: `Σ hi(late) < Σ lo(early)`. -/
theorem race_sound_clean {er es : List (Nat × Nat)} {L early late : Trace}
    {v w : Bool} {τ : Nat}
    (hL : Window v w τ τ L) (he : Chain er L early) (hl : Chain es L late)
    (h : sumHi es < sumLo er) : Bundled late w early :=
  race_sound hL he hl (by omega)

/-! ## Pure delays: the arcs used by every counterexample -/

/-- A pure (transport) delay by exactly `d` ticks. -/
def shift (d : Nat) (s : Trace) : Trace := fun t => if t < d then s 0 else s (t - d)

/-- A pure delay `d ∈ [lo, hi]` satisfies H_BOUNDED_DELAY, so it is a legal
behaviour of any arc whose interval contains `d`. -/
theorem shift_bd {lo hi d : Nat} (s : Trace) (h1 : lo ≤ d) (h2 : d ≤ hi) :
    BoundedDelay lo hi s (shift d s) where
  cause := by
    intro t hc
    have hd : d ≤ t + 1 := by
      apply Nat.le_of_not_lt; intro hlt
      apply hc
      show shift d s t = shift d s (t + 1)
      simp only [shift, show t < d by omega, hlt, ↓reduceIte]
    refine ⟨d, h1, h2, hd, ?_⟩
    simp only [shift, show ¬ t + 1 < d by omega, ↓reduceIte]
  settle := by
    intro t ht hst
    simp only [shift, show ¬ t < d by omega, ↓reduceIte]
    exact (hst (t - d) (by omega) (by omega)).trans (hst t (by omega) (Nat.le_refl t)).symm

theorem shift_zero_at (d : Nat) (s : Trace) : shift d s 0 = s 0 := by
  simp [shift]

/-- H_CLEAN_EDGE is preserved by a pure delay (one physical wire, one sample). -/
theorem shift_window {v w : Bool} {τ d : Nat} {s : Trace} (h : Window v w τ τ s) :
    Window v w (τ + d) (τ + d) (shift d s) := by
  constructor
  · intro t ht
    simp only [shift]
    split
    · exact h.1 0 (Nat.zero_le _)
    · exact h.1 _ (by omega)
  · intro t ht
    simp only [shift, show ¬ t < d by omega, ↓reduceIte]
    exact h.2 _ (by omega)

/-- A path of pure delays, applied left to right. -/
def shiftChain : List Nat → Trace → Trace
  | [], s => s
  | d :: ds, s => shiftChain ds (shift d s)

theorem shiftChain_chain : ∀ (ds : List Nat) (es : List (Nat × Nat)) (s : Trace),
    Forall2 (fun d e => e.1 ≤ d ∧ d ≤ e.2) ds es → Chain es s (shiftChain ds s)
  | [], [], s, _ => Chain.nil s
  | d :: ds, (lo, hi) :: es, s, Forall2.cons h hs =>
    Chain.cons (shift_bd s h.1 h.2) (shift_zero_at d s) (shiftChain_chain ds es (shift d s) hs)

/-- The launch every counterexample uses: a clean rising edge after tick 0. -/
def step : Trace := fun t => decide (0 < t)

theorem step_window : Window false true 0 0 step :=
  ⟨fun t ht => by simp [step]; omega, fun t ht => by simp [step]; omega⟩

/-- A pure-delay path from `step` rises exactly once, at `sumN ds + 1`. -/
theorem shiftChain_step : ∀ (ds : List Nat) (t : Nat),
    shiftChain ds step t = decide (sumN ds < t) := by
  intro ds
  suffices H : ∀ (ds : List Nat) (k : Nat) (t : Nat),
      shiftChain ds (fun t => decide (k < t)) t = decide (k + sumN ds < t) by
    intro t; have := H ds 0 t; rw [Nat.zero_add] at this; exact this
  intro ds
  induction ds with
  | nil => intro k t; rfl
  | cons d ds ih =>
    intro k t
    have : shift d (fun t => decide (k < t)) = (fun t => decide (k + d < t)) := by
      funext u; simp only [shift]; split <;> simp <;> omega
    show shiftChain ds (shift d _) t = _
    rw [this, ih, sumN, Nat.add_assoc]

/-! ## 3. The rules as implemented, as arithmetic on SDF numbers

All three read the FIRST number of each SDF triple; nextpnr-xilinx writes
min = typ = max, one number `D` per arc (slow-corner max intrinsic delay; flat
25 ps for site pins). Constants are scaled by 1000 to stay in `Nat`. -/

/-- skew.py / arb_fork.py verdict: `int(0.772 (R - c) - 1.155 (S - c)) > 0`,
i.e. a guarded margin of at least 1 ps. `R`, `S` are the SDF arrivals of the
early and the late side from the launch, `c` the credited shared prefix. -/
def guardedPass (R S c : Nat) : Prop := 1155 * (S - c) + 1000 ≤ 772 * (R - c)

instance (R S c : Nat) : Decidable (guardedPass R S c) := by
  unfold guardedPass; infer_instance

/-- tighten.py rule A, not a violation: `t_e - t_l - max(0.2 t_l, 200) >= 0`
(`rule_a_links` pads only when the margin is negative). -/
def ruleAPass (te tl : Nat) : Prop := tl + max (tl / 5) 100 ≤ te

instance (te tl : Nat) : Decidable (ruleAPass te tl) := by
  unfold ruleAPass; infer_instance

/-- H_BAND (early side): real lower bound at least `lam/1000` of the SDF number. -/
abbrev BandLo (lam : Nat) : List Nat → List (Nat × Nat) → Prop :=
  Forall2 (fun D e => lam * D ≤ 1000 * e.1)

/-- H_BAND (late side): real upper bound at most `mu/1000` of the SDF number. -/
abbrev BandHi (mu : Nat) : List Nat → List (Nat × Nat) → Prop :=
  Forall2 (fun D e => 1000 * e.2 ≤ mu * D)

theorem bandLo_sum {lam : Nat} {Ds : List Nat} {es : List (Nat × Nat)}
    (h : BandLo lam Ds es) : lam * sumN Ds ≤ 1000 * sumLo es := by
  induction h with
  | nil => simp [sumN, sumLo]
  | cons h _ ih => simp only [sumN, sumLo, Nat.mul_add]; exact Nat.add_le_add h ih

theorem bandHi_sum {mu : Nat} {Ds : List Nat} {es : List (Nat × Nat)}
    (h : BandHi mu Ds es) : 1000 * sumHi es ≤ mu * sumN Ds := by
  induction h with
  | nil => simp [sumN, sumHi]
  | cons h _ ih => simp only [sumN, sumHi, Nat.mul_add]; exact Nat.add_le_add h ih

/-- Rule E (and rule J with an EXACT shared prefix) is sound under
H_BAND_772_1155 + H_CLEAN_EDGE at the divergence node `X`: the guarded check
on the divergent tails (`R - c = ΣDr`, `S - c = ΣDs`) implies the property.
This is what skew.py's comments argue, made precise: every element's own
scatter is inside the band, and the shared prefix is one sample. -/
theorem ruleE_sound {Dr Ds : List Nat} {er es : List (Nat × Nat)}
    {X early late : Trace} {τ c : Nat}
    (hX : Window false true τ τ X)                 -- H_CLEAN_EDGE
    (he : Chain er X early) (hl : Chain es X late) -- H_BOUNDED_DELAY, H_SENSITIZED
    (hbr : BandLo 772 Dr er) (hbs : BandHi 1155 Ds es)  -- H_BAND_772_1155
    (hpass : guardedPass (c + sumN Dr) (c + sumN Ds) c) :
    Bundled late true early := by
  apply race_sound_clean hX he hl
  have h1 := bandLo_sum hbr
  have h2 := bandHi_sum hbs
  unfold guardedPass at hpass
  simp only [Nat.add_sub_cancel_left] at hpass
  omega

/-- Rule A implies the band premise only for short data paths: with
`t_l ≤ 402 ps` the 200 ps floor is wider than the band needs. -/
theorem ruleA_band_sound_small {te tl : Nat} (h : ruleAPass te tl) (hs : tl ≤ 402) :
    1155 * tl < 772 * te := by
  unfold ruleAPass at h
  have : 200 ≤ max (tl / 5) 200 := Nat.le_max_right _ _
  omega

/-- ...and for every `t_l ≥ 404 ps` there is a passing rule A margin the band
does not cover: the request may run at 0.772x and the data at 1.155x. -/
theorem ruleA_not_band_sound (tl : Nat) (hs : 404 ≤ tl) :
    ruleAPass (tl + max (tl / 5) 200) tl ∧
      772 * (tl + max (tl / 5) 200) ≤ 1155 * tl := by
  refine ⟨Nat.le_refl _, ?_⟩
  by_cases hm : tl / 5 ≤ 200
  · rw [Nat.max_eq_right hm]; omega
  · rw [Nat.max_eq_left (by omega)]; omega

/-! ## 4. Counterexample netlists -/

/-- Rule A: request leg one element of SDF 2400 ps, peer leg one of 2000 ps.
Rule A passes (margin exactly 0); with the request at 0.772x and the peer
at 1.155x -- inside the band skew.py adopts -- the peer settles at 2311 ps,
after the request moved at 1854 ps. -/
theorem ruleA_counterexample :
    ∃ (Dr Ds : List Nat) (er es : List (Nat × Nat)) (early late : Trace),
      Chain er step early ∧ Chain es step late ∧
      BandLo 772 Dr er ∧ BandHi 1155 Ds es ∧
      ruleAPass (sumN Dr) (sumN Ds) ∧ ¬ Bundled late true early := by
  refine ⟨[2400], [2000], [(1853, 2772)], [(1544, 2310)],
    shiftChain [1853] step, shiftChain [2310] step,
    shiftChain_chain _ _ _ (forall2_of_check (by decide)),
    shiftChain_chain _ _ _ (forall2_of_check (by decide)),
    forall2_of_check (by decide), forall2_of_check (by decide), by decide, ?_⟩
  intro h
  have := h 1854 (by rw [shiftChain_step, shiftChain_step]; decide) 1854 (Nat.le_refl _)
  rw [shiftChain_step] at this
  exact absurd this (by decide)

/-! ### Rule E, one-corner model, fast corner

prjxray-db (zynq7, `tile_type_INT_L.json`, `timings/CLBLL_L.sdf`), 4-tuples
`(fast_min, fast_max, slow_min, slow_max)` in ps:
* `INT_L.LOGIC_OUTS_L0->>SW2BEG0`  (33, 41, 113, 137), RC term 10
* `INT_L.EE2END0->>NN2BEG0`        (50, 60, 109, 132), RC term 10
* LUT6 `A* -> O6`                 (45, 56, 100, 124)
nextpnr-xilinx's SDF number for a pip is `slow_max + RC` (147, 142), for a
LUT arc `slow_max` (124); formal/tools/timing/prjxray_intervals.py prints
them. The intervals below add the same RC term to the intrinsic bounds.
Early side (request tail): eight SW2BEG-class pips, SDF 8 x 147 = 1176.
Late side (select tail): five LUT arcs and one NN2BEG-class pip,
SDF 5 x 124 + 142 = 762. Guarded margin +26 ps: rule E passes.
At the fast corner the request may take 8 x 43 = 344 ps and the select
5 x 56 + 70 = 350 ps. Every element sits in its own fast interval.
This shape is NOT routable as written (LUT-to-LUT connections need pips,
and only a first hop leaves LOGIC_OUTS); it shows the band is not a corner
bound in principle. See the notes for realistic compositions. -/

def cornerReqSDF : List Nat := List.replicate 8 147
def cornerSelSDF : List Nat := [124, 124, 124, 124, 124, 142]
def cornerReqFast : List (Nat × Nat) := List.replicate 8 (43, 51)
def cornerSelFast : List (Nat × Nat) := [(45, 56), (45, 56), (45, 56), (45, 56), (45, 56), (60, 70)]

theorem ruleE_corner_pass : guardedPass (sumN cornerReqSDF) (sumN cornerSelSDF) 0 := by
  decide

theorem ruleE_corner_counterexample :
    ∃ (early late : Trace),
      Chain cornerReqFast step early ∧ Chain cornerSelFast step late ∧
      ¬ Bundled late true early := by
  refine ⟨shiftChain (List.replicate 8 43) step, shiftChain [56, 56, 56, 56, 56, 70] step,
    shiftChain_chain _ _ _ (forall2_of_check (by decide)),
    shiftChain_chain _ _ _ (forall2_of_check (by decide)), ?_⟩
  intro h
  have := h 345 (by rw [shiftChain_step, shiftChain_step]; decide) 345 (Nat.le_refl _)
  rw [shiftChain_step] at this
  exact absurd this (by decide)

/-! ### Rule E, slow corner: the LUT site-pin delay the SDF does not carry

prjxray-db `tile_type_CLBLL_L.json`, SLICEL site input pins, 4-tuples:
A1 (172, 214, 416, 516), A6 (2, 2, 4, 5). nextpnr-xilinx costs every site
entry pip at a flat 25 ps (`getPipDelay`, non-tile-routing branch), so the
SDF interconnect to A1 and to A6 differ by nothing.
Early side: five SW2BEG-class pips into A6 of the steer LUT, SDF
5 x 147 + 25 = 760. Late side (select): three IMUX-class pips
(`INT_L.BYP_BOUNCE0->>IMUX_L2`, (38, 47, 114, 138), RC 12, SDF 150) into
A1, SDF 3 x 150 + 25 = 475. Guarded margin +37 ps: rule E passes.
Slow corner (intrinsic + the same RC term): the request has arrived by
5 x 147 + 5 = 740 ps whatever the delays; the select cannot arrive before
3 x 126 + 416 = 794 ps. -/

def pinReqSDF : List Nat := [147, 147, 147, 147, 147, 25]
def pinSelSDF : List Nat := [150, 150, 150, 25]
def pinReqSlow : List (Nat × Nat) := [(123, 147), (123, 147), (123, 147), (123, 147), (123, 147), (4, 5)]
def pinSelSlow : List (Nat × Nat) := [(126, 150), (126, 150), (126, 150), (416, 516)]

theorem ruleE_sitepin_pass : guardedPass (sumN pinReqSDF) (sumN pinSelSDF) 0 := by
  decide

/-- For EVERY pair of traces the slow-corner intervals allow, the request
moves before the select has settled. -/
theorem ruleE_sitepin_fails_all (early late : Trace)
    (he : Chain pinReqSlow step early) (hl : Chain pinSelSlow step late) :
    ¬ Bundled late true early := by
  intro h
  have hE := chain_window he step_window
  have hS := chain_window hl step_window
  have e1 : early 741 = true := hE.2 741 (by decide)
  have e0 : early 0 = false := hE.1 0 (Nat.zero_le _)
  have l1 : late 741 = false := hS.1 741 (by decide)
  have := h 741 (by rw [e1, e0]; decide) 741 (Nat.le_refl _)
  rw [l1] at this
  exact Bool.false_ne_true this

/-- ...and such traces exist (the statement above is not vacuous). -/
theorem ruleE_sitepin_nonvacuous :
    ∃ (early late : Trace), Chain pinReqSlow step early ∧ Chain pinSelSlow step late :=
  ⟨shiftChain [123, 123, 123, 123, 123, 4] step, shiftChain [126, 126, 126, 416] step,
    shiftChain_chain _ _ _ (forall2_of_check (by decide)),
    shiftChain_chain _ _ _ (forall2_of_check (by decide))⟩

/-! ### Rule J: the shared-route credit is estimated from pip counts

arb_fork.py credits `c = min(d_a * shared / hops_a, d_b * shared / hops_b)`:
each sink's interconnect delay times the fraction of its pips on the shared
prefix. If the shared pip is cheap and the divergent ones dear, `c` exceeds
the real shared delay, and since the guarded margin grows by
`(1.155 - 0.772) c`, an over-credit is permissive.
Netlist: A0's route shares ONE pip (40 ps) between the two sinks, then five
192 ps pips to `ua_k` and five to `ustate` (each sink 1000 ps over 6 hops,
so `c = 1000 * 1 / 6 = 166`). late = 1000 + 124 (ua's A0 arc);
early = 1000 + 124 + 134 + 124 + 134 + 124 = 1640 (ustate arc, q net,
ugrant arc, g net, ua's g arc). Guarded margin with c = 166: +30 ps, pass.
With the true shared delay 40 the same band gives the early tail
(1600 ps of SDF) a real 1241 ps and the late tail (1084 ps) 1248 ps. -/

def cEst (da db shared hopsA hopsB : Nat) : Nat := min (da * shared / hopsA) (db * shared / hopsB)

theorem ruleJ_estimate : cEst 1000 1000 1 6 6 = 166 := by decide

theorem ruleJ_pass : guardedPass 1640 1124 (cEst 1000 1000 1 6 6) := by decide

/-- The exact-prefix check fails on the same numbers. -/
theorem ruleJ_exact_fails : ¬ guardedPass 1640 1124 40 := by decide

def jEarlySDF : List Nat := [192, 192, 192, 192, 192, 124, 134, 124, 134, 124]
def jLateSDF : List Nat := [192, 192, 192, 192, 192, 124]
def jEarlyIv : List (Nat × Nat) :=
  [(149, 221), (149, 221), (149, 221), (149, 221), (149, 221),
   (96, 143), (104, 154), (96, 143), (104, 154), (96, 143)]
def jLateIv : List (Nat × Nat) :=
  [(149, 221), (149, 221), (149, 221), (149, 221), (149, 221), (96, 143)]

/-- Inside the rule's own band, with the shared 40 ps pip one clean edge
(the divergence node is `step` here), the grant reaches `ua_k` before A0's
fall does: exactly the handover race rule J exists to exclude. -/
theorem ruleJ_counterexample :
    BandLo 772 jEarlySDF jEarlyIv ∧ BandHi 1155 jLateSDF jLateIv ∧
    40 + sumN jEarlySDF = 1640 ∧ 40 + sumN jLateSDF = 1124 ∧
    ∃ (early late : Trace), Chain jEarlyIv step early ∧ Chain jLateIv step late ∧
      ¬ Bundled late true early := by
  refine ⟨forall2_of_check (by decide), forall2_of_check (by decide), by decide, by decide,
    shiftChain [149, 149, 149, 149, 149, 96, 104, 96, 104, 96] step,
    shiftChain [221, 221, 221, 221, 221, 143] step,
    shiftChain_chain _ _ _ (forall2_of_check (by decide)),
    shiftChain_chain _ _ _ (forall2_of_check (by decide)), ?_⟩
  intro h
  have := h 1242 (by rw [shiftChain_step, shiftChain_step]; decide) 1242 (Nat.le_refl _)
  rw [shiftChain_step] at this
  exact absurd this (by decide)

/-! ### Crediting a shared prefix needs H_CLEAN_EDGE

Under H_BOUNDED_DELAY alone an arc may deliver one input edge as several
output edges inside its window (it is not FIFO). `glitchy` is a legal
output of a `[10, 100]` arc driven by `step`: it rises at 11, falls at 12,
rises for good at 101. Crediting the prefix (c = its delay) leaves tails of
100 ps (request) and 50 ps (select), a guarded margin of +19 ps; the request
moves at 111 while the select is still low at 111. -/

def glitchy : Trace := fun t => decide (t = 11) || decide (100 < t)

theorem glitchy_bd : BoundedDelay 10 100 step glitchy where
  cause := by
    intro t hc
    simp only [changes, glitchy, ne_eq] at hc
    by_cases h10 : t = 10
    · subst h10; exact ⟨10, by decide, by decide, by decide, by decide⟩
    by_cases h11 : t = 11
    · subst h11; exact ⟨12, by decide, by decide, by decide, by decide⟩
    by_cases h100 : t = 100
    · subst h100; exact ⟨10, by decide, by decide, by decide, by decide⟩
    exfalso; apply hc
    have a1 : decide (t = 11) = false := by simp [h11]
    have a2 : decide (t + 1 = 11) = false := by simp; omega
    rw [a1, a2]; simp; omega
  settle := by
    intro t ht hst
    by_cases h : t = 100
    · subst h
      have := hst 100 (by decide) (by decide)
      simp [step] at this
    · have h1 : 100 < t := by omega
      show (decide (t = 11) || decide (100 < t)) = decide (0 < t)
      rw [decide_eq_true h1, decide_eq_true (by omega : 0 < t), Bool.or_true]

theorem prefix_credit_needs_clean_edge :
    guardedPass 100 50 0 ∧
    ¬ Bundled (shift 50 glitchy) true (shift 100 glitchy) := by
  refine ⟨by decide, ?_⟩
  intro h
  have := h 111 (by decide) 111 (Nat.le_refl _)
  exact absurd this (by decide)

end AuditRulesMut
