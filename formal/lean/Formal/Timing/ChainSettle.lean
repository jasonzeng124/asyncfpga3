import Formal.Timing.Semantics

/-!
# C-10o: H_CHAIN_SETTLED, exactly, in the bounded-delay model (part 1: the network theorem)

Probe C-10o (shard C, track 10). O4 (`Formal/Net/CellBindChain.lean`, `fastfall_hazard`)
showed that a side-tapped delay chain can emit a runt when its input moves again before
every stage has followed (H_CHAIN_SETTLED). This file gives the EXACT condition in the
per-arc bounded-delay model of `Formal.Timing.Semantics` (C-10a), for any monotone
single-source network (every delay chain of the library is one).

## Model (named hypotheses)

A netlist `net : Netlist` (Semantics' arcs `src → dst` with `[lo, hi]` ps, `WF`: index
order is topological, `lo ≤ hi`). Node `0` is the chain's input (the side-tap source:
`a` of `bd_delay #(.FASTFALL(1))` / `#(.FASTRISE(1))`, `gate` of `bd_delay_gated`, the
link node `c` of bd_link's `uack`/RFAST `rdly`). A run `AndRun net inp sig` is
Semantics' `Run` with two changes:

* **H_INPUT** (replaces H_LAUNCH): node 0 carries an arbitrary given trace `inp` (the
  environment: the handshake that moves the chain input). The theorems below are for
  every `inp`; `ChainSettleChain` instantiates the pulse.
* **H_AND** (instance of H_ZERO_DELAY_FN + H_LOCAL): every other node is the AND of the
  pins of its in-arcs (a LUT1 buffer is the AND of one pin; `bd_delay`'s FASTFALL stage
  is `LUT2 INIT 8` = AND; a node with no in-arc is constant 1). OR networks (FASTRISE,
  `LUT2 INIT E`) are the dual: `OrRun`, by negating every trace.
* **H_BOUNDED_DELAY** per arc: Prelim's `BoundedDelay lo hi` (unchanged). The delay may
  differ from event to event, pulses shorter than `hi` may pass or vanish.
  H_QUIESCENT is NOT needed for soundness (the extremal run below satisfies it anyway).

## Results

* `lowPin lo hi L t`: the output of an arc `[lo, hi]` is FORCED low at `t` when its source
  is low on the window `[s - hi, max s (t - lo)]` for some `hi ≤ s ≤ t` (settled low at
  `s`, and no 1 young enough to arrive by `t`). `pin_low`: sound for every BoundedDelay
  output. `ext_bd`: the trace "1 unless forced" IS a BoundedDelay output (and quiescent):
  so `lowPin` is exact per arc.
* `Lc net inp v`: the forced-low set of node `v`, by recursion over the netlist
  (`Lc v t ↔ ∃ in-arc k, lowPin (Lc src) t`).
* **`cert_sound`**: any certificate `LowCert` (in particular `Lc`) is sound: in every run,
  `L v t → sig v t = false`.
* **`low_iff`** (exact): `(∀ runs, sig v t = false) ↔ Lc net inp v t`. The `→` direction
  is the extremal run `extRun` (every pin 1 unless forced; quiescent when `inp 0 = true`).
* `Settled net inp z A B` (**H_CHAIN_SETTLED**, exact form): `Lc z` covers `[A, B)`.
  `settled_sound`: then z is 0 on all of `[A, B)` in every run: no rise of z in between.
  **`runt_of_gap`** (converse): if `Lc z x`, `Lc z y`, `x < t < y` and NOT `Lc z t`, there
  is a run (the extremal one) with `z x = 0`, `z t = 1`, `z y = 0`: a runt on z.
* OR (FASTRISE) duals: `or_sound`, `or_runt_of_gap` (forced HIGH sets = `Lc` of the
  negated input).
* Interval calculus (what chainck computes): `lowPin_Ico` (an interval `[x, y)` with
  `y > x + hi` maps to `[x + hi, y + lo)`, a shorter one to nothing), `lowPin_union_gap`
  (sets separated by a point outside both map separately), `lowPin_mono`.

What this does NOT cover: the environment (H_INPUT: when the input moves again is
`ChainSettleChain`'s parameter `T`, bounded below by chainck's late side); a LUT's mux-tree
hazard (H_KLEENE_LUT: a LUT here is its Boolean function on pins, all delay on the pin
arcs); non-monotone stages (none in the library's chains).

Core Lean only (imports Semantics, which imports Prelim). No sorry/axiom/native_decide.
-/

namespace Formal.Timing.ChainSettle
open Formal.Net Formal.Timing

/-! ## 1. One arc -/

/-- The output of an arc `[lo, hi]` whose source is low on `L` is forced low at `t`. -/
def lowPin (lo hi : Nat) (L : Nat → Prop) (t : Nat) : Prop :=
  ∃ s, hi ≤ s ∧ s ≤ t ∧ ∀ w, s - hi ≤ w → (w ≤ s ∨ w + lo ≤ t) → L w

theorem lowPin_mono {lo hi : Nat} {L L' : Nat → Prop} (h : ∀ w, L w → L' w) {t : Nat}
    (hl : lowPin lo hi L t) : lowPin lo hi L' t := by
  obtain ⟨s, h1, h2, h3⟩ := hl
  exact ⟨s, h1, h2, fun w a b => h _ (h3 w a b)⟩

/-- **Per-arc soundness.** -/
theorem pin_low {lo hi : Nat} {i o : Trace} (hbd : BoundedDelay lo hi i o) {t : Nat}
    (hl : lowPin lo hi (fun w => i w = false) t) : o t = false := by
  obtain ⟨s, hs, hst, hw⟩ := hl
  have h0 : o s = false := by
    have hstab : stableOn i (s - hi) s := by
      intro w h1 h2
      rw [hw w h1 (Or.inl h2), hw (s - hi) (Nat.le_refl _) (Or.inl (Nat.sub_le _ _))]
    rw [hbd.settle s hs hstab]
    exact hw s (Nat.sub_le _ _) (Or.inl (Nat.le_refl _))
  have key : ∀ n, s + n ≤ t → o (s + n) = false := by
    intro n
    induction n with
    | zero => intro _; simpa using h0
    | succ n ih =>
      intro hn
      have ihn := ih (by omega)
      cases hx : o (s + (n + 1)) with
      | false => rfl
      | true =>
        exfalso
        have hc : changes o (s + n) := by
          unfold changes; rw [ihn, show s + n + 1 = s + (n + 1) by omega, hx]; decide
        obtain ⟨d, hd1, hd2, hd3, heq⟩ := hbd.cause (s + n) hc
        have hiw := hw (s + n + 1 - d) (by omega) (Or.inr (by omega))
        rw [show s + n + 1 = s + (n + 1) by omega, hx] at heq
        rw [show s + (n + 1) - d = s + n + 1 - d by omega] at heq
        rw [hiw] at heq; exact Bool.noConfusion heq
  have := key (t - s) (by omega)
  rwa [show s + (t - s) = t by omega] at this

open Classical in
/-- The extremal output of an arc: 1 unless forced low. -/
noncomputable def ext (lo hi : Nat) (L : Nat → Prop) : Trace :=
  fun t => if lowPin lo hi L t then false else true

theorem ext_false {lo hi : Nat} {L : Nat → Prop} {t : Nat} :
    ext lo hi L t = false ↔ lowPin lo hi L t := by
  unfold ext; split <;> simp_all

/-- **Per-arc exactness**: the extremal output is a BoundedDelay output. -/
theorem ext_bd {lo hi : Nat} (hlh : lo ≤ hi) (i : Trace) :
    BoundedDelay lo hi i (ext lo hi (fun w => i w = false)) where
  cause := by
    intro t hc
    unfold changes at hc
    by_cases h1 : lowPin lo hi (fun w => i w = false) (t + 1)
    · -- o (t+1) = false; then o t = true, so not forced at t
      have ht1 : ext lo hi (fun w => i w = false) (t + 1) = false := ext_false.2 h1
      have h0 : ¬ lowPin lo hi (fun w => i w = false) t := by
        intro h0; apply hc; rw [ht1, ext_false.2 h0]
      obtain ⟨s, hs1, hs2, hs3⟩ := h1
      have hseq : s = t + 1 := by
        apply Classical.byContradiction; intro hne
        exact h0 ⟨s, hs1, by omega, fun w a b => hs3 w a (by omega)⟩
      subst hseq
      refine ⟨hi, hlh, Nat.le_refl _, hs1, ?_⟩
      rw [ht1]; exact (hs3 _ (Nat.le_refl _) (Or.inl (Nat.sub_le _ _))).symm
    · have ht1 : ext lo hi (fun w => i w = false) (t + 1) = true := by
        cases h : ext lo hi (fun w => i w = false) (t + 1)
        · exact absurd (ext_false.1 h) h1
        · rfl
      have h0 : lowPin lo hi (fun w => i w = false) t := by
        apply Classical.byContradiction; intro h0
        apply hc; rw [ht1]
        cases h : ext lo hi (fun w => i w = false) t
        · exact absurd (ext_false.1 h) h0
        · rfl
      obtain ⟨s, hs1, hs2, hs3⟩ := h0
      -- some w in the (t+1)-window is high: it must be w = t + 1 - lo
      have hex : ∃ w, s - hi ≤ w ∧ (w ≤ s ∨ w + lo ≤ t + 1) ∧ ¬ (i w = false) := by
        apply Classical.byContradiction; intro hne
        apply h1
        refine ⟨s, hs1, by omega, fun w a b => ?_⟩
        apply Classical.byContradiction; intro hw
        exact hne ⟨w, a, b, hw⟩
      obtain ⟨w, hw1, hw2, hw3⟩ := hex
      have hwe : w + lo = t + 1 ∧ ¬ w ≤ s := by
        refine ⟨?_, ?_⟩
        · apply Classical.byContradiction; intro hne
          rcases hw2 with h | h
          · exact hw3 (hs3 w hw1 (Or.inl h))
          · exact hw3 (hs3 w hw1 (Or.inr (by omega)))
        · intro h; exact hw3 (hs3 w hw1 (Or.inl h))
      refine ⟨lo, Nat.le_refl _, hlh, by omega, ?_⟩
      rw [ht1, show t + 1 - lo = w by omega]
      cases h : i w
      · exact absurd h hw3
      · rfl
  settle := by
    intro t ht hst
    cases hit : i t with
    | false =>
      apply ext_false.2
      refine ⟨t, ht, Nat.le_refl _, fun w a b => ?_⟩
      have hwt : w ≤ t := by omega
      show i w = false
      rw [hst w a hwt, ← hst t (by omega) (Nat.le_refl _), hit]
    | true =>
      cases h : ext lo hi (fun w => i w = false) t with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨s, hs1, hs2, hs3⟩ := ext_false.1 h
        by_cases hc : t - lo ≤ s
        · have := hs3 s (Nat.sub_le _ _) (Or.inl (Nat.le_refl _))
          simp only at this
          rw [hst s (by omega) hs2, ← hst t (by omega) (Nat.le_refl _), hit] at this
          exact Bool.noConfusion this
        · have := hs3 (t - lo) (by omega) (Or.inr (by omega))
          simp only at this
          rw [hst (t - lo) (by omega) (Nat.sub_le _ _), ← hst t (by omega) (Nat.le_refl _),
            hit] at this
          exact Bool.noConfusion this

/-- The extremal output starts at 1 when the source starts at 1 (H_QUIESCENT). -/
theorem ext_zero {lo hi : Nat} {i : Trace} (h : i 0 = true) :
    ext lo hi (fun w => i w = false) 0 = true := by
  cases hx : ext lo hi (fun w => i w = false) 0 with
  | true => rfl
  | false =>
    obtain ⟨s, _, hs2, hs3⟩ := ext_false.1 hx
    have := hs3 0 (by omega) (Or.inl (by omega))
    simp only at this; rw [h] at this; exact Bool.noConfusion this

/-! ## 2. Monotone networks -/

/-- A run of an AND network driven by `inp` at node 0 (H_INPUT, H_AND, H_BOUNDED_DELAY). -/
structure AndRun (net : Netlist) (inp : Trace) (sig : Nat → Trace) where
  pin : Nat → Trace
  src : ∀ t, sig 0 t = inp t
  bd : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → BoundedDelay a.lo a.hi (sig a.src) (pin k)
  node : ∀ v, v ≠ 0 → ∀ t,
    (sig v t = true ↔ ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = v → pin k t = true)

/-- A forced-low certificate. -/
structure LowCert (net : Netlist) (inp : Trace) (L : Nat → Nat → Prop) : Prop where
  src : ∀ t, L 0 t → inp t = false
  step : ∀ v, v ≠ 0 → ∀ t, L v t →
    ∃ (k : Nat) (a : Arc), net.arcs[k]? = some a ∧ a.dst = v ∧ lowPin a.lo a.hi (L a.src) t

/-- **Soundness of any certificate.** -/
theorem cert_sound {net : Netlist} {inp : Trace} {sig : Nat → Trace} {L : Nat → Nat → Prop}
    (hwf : net.WF) (r : AndRun net inp sig) (hc : LowCert net inp L) :
    ∀ v t, L v t → sig v t = false := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro t hl
    by_cases hv : v = 0
    · subst hv; rw [r.src]; exact hc.src t hl
    · obtain ⟨k, a, hk, hd, hlow⟩ := hc.step v hv t hl
      have hlt : a.src < v := hd ▸ (hwf a (List.mem_of_getElem? hk)).1
      have hp : r.pin k t = false :=
        pin_low (r.bd k a hk) (lowPin_mono (fun w hw => ih a.src hlt w hw) hlow)
      cases hs : sig v t with
      | false => rfl
      | true =>
        have := ((r.node v hv t).1 hs) k a hk hd
        rw [hp] at this; exact Bool.noConfusion this

/-- The canonical forced-low set of each node. -/
def Lc (net : Netlist) (inp : Trace) : Nat → Nat → Prop
  | 0, t => inp t = false
  | v + 1, t => ∃ (k : Nat) (a : Arc), net.arcs[k]? = some a ∧ a.dst = v + 1 ∧
      ∃ _h : a.src < v + 1, lowPin a.lo a.hi (fun s => Lc net inp a.src s) t
termination_by v _ => v

theorem Lc_zero (net : Netlist) (inp : Trace) (t : Nat) : Lc net inp 0 t ↔ inp t = false := by
  rw [Lc]

theorem Lc_succ (net : Netlist) (inp : Trace) (v t : Nat) :
    Lc net inp (v + 1) t ↔ ∃ (k : Nat) (a : Arc), net.arcs[k]? = some a ∧ a.dst = v + 1 ∧
      ∃ _h : a.src < v + 1, lowPin a.lo a.hi (fun s => Lc net inp a.src s) t := by
  rw [Lc]

/-- On a WF netlist, `Lc` at a non-input node is exactly "some in-arc forces it". -/
theorem Lc_pos {net : Netlist} (hwf : net.WF) (inp : Trace) {v : Nat} (hv : v ≠ 0) (t : Nat) :
    Lc net inp v t ↔ ∃ (k : Nat) (a : Arc), net.arcs[k]? = some a ∧ a.dst = v ∧
      lowPin a.lo a.hi (Lc net inp a.src) t := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  rw [Lc_succ]
  constructor
  · rintro ⟨k, a, hk, hd, _, hl⟩; exact ⟨k, a, hk, hd, hl⟩
  · rintro ⟨k, a, hk, hd, hl⟩
    exact ⟨k, a, hk, hd, hd ▸ (hwf a (List.mem_of_getElem? hk)).1, hl⟩

theorem Lc_cert {net : Netlist} (hwf : net.WF) (inp : Trace) : LowCert net inp (Lc net inp) where
  src := fun t h => (Lc_zero net inp t).1 h
  step := fun _ hv t h => (Lc_pos hwf inp hv t).1 h

open Classical in
/-- The extremal run: every node 1 unless forced low. -/
noncomputable def extSig (net : Netlist) (inp : Trace) : Nat → Trace :=
  fun v t => if Lc net inp v t then false else true

/-- The extremal pins. -/
noncomputable def extPin (net : Netlist) (inp : Trace) : Nat → Trace :=
  fun k t => match net.arcs[k]? with
    | some a => ext a.lo a.hi (Lc net inp a.src) t
    | none => true

theorem extSig_false {net : Netlist} {inp : Trace} {v t : Nat} :
    extSig net inp v t = false ↔ Lc net inp v t := by
  unfold extSig; split <;> simp_all

theorem extSig_lowset (net : Netlist) (inp : Trace) (v : Nat) :
    (fun w => extSig net inp v w = false) = Lc net inp v := by
  funext w; exact propext extSig_false

/-- The extremal run is a run. -/
noncomputable def extRun {net : Netlist} (hwf : net.WF) (inp : Trace) :
    AndRun net inp (extSig net inp) where
  pin := extPin net inp
  src := by
    intro t
    cases h : inp t with
    | false => exact extSig_false.2 ((Lc_zero net inp t).2 h)
    | true =>
      cases h2 : extSig net inp 0 t with
      | true => rfl
      | false => have := (Lc_zero net inp t).1 (extSig_false.1 h2); rw [h] at this; exact absurd this (by simp)
  bd := by
    intro k a hk
    have hp : extPin net inp k = ext a.lo a.hi (fun w => extSig net inp a.src w = false) := by
      funext t; simp only [extPin, hk]; rw [extSig_lowset]
    rw [hp]; exact ext_bd (hwf a (List.mem_of_getElem? hk)).2 _
  node := by
    intro v hv t
    constructor
    · intro hs k a hk hd
      cases hp : extPin net inp k t with
      | true => rfl
      | false =>
        exfalso
        simp only [extPin, hk] at hp
        have : Lc net inp v t := (Lc_pos hwf inp hv t).2 ⟨k, a, hk, hd, ext_false.1 hp⟩
        rw [extSig_false.2 this] at hs; exact Bool.noConfusion hs
    · intro hall
      cases hs : extSig net inp v t with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨k, a, hk, hd, hl⟩ := (Lc_pos hwf inp hv t).1 (extSig_false.1 hs)
        have := hall k a hk hd
        simp only [extPin, hk] at this
        rw [ext_false.2 hl] at this; exact Bool.noConfusion this

/-- The extremal run is quiescent when the input starts at 1. -/
theorem extRun_quiet {net : Netlist} (hwf : net.WF) {inp : Trace} (h0 : inp 0 = true) :
    ∀ v, extSig net inp v 0 = true := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    cases hs : extSig net inp v 0 with
    | true => rfl
    | false =>
      exfalso
      have hl := extSig_false.1 hs
      by_cases hv : v = 0
      · subst hv; have := (Lc_zero net inp 0).1 hl; rw [h0] at this; exact Bool.noConfusion this
      · obtain ⟨k, a, hk, hd, ⟨s, _, hs2, hs3⟩⟩ := (Lc_pos hwf inp hv 0).1 hl
        have hlt : a.src < v := hd ▸ (hwf a (List.mem_of_getElem? hk)).1
        have := hs3 0 (by omega) (Or.inl (by omega))
        rw [← extSig_false, ih a.src hlt] at this; exact Bool.noConfusion this

/-- **Exactness**: a node is low at `t` in every run iff it is canonically forced low. -/
theorem low_iff {net : Netlist} (hwf : net.WF) (inp : Trace) (v t : Nat) :
    (∀ sig, AndRun net inp sig → sig v t = false) ↔ Lc net inp v t := by
  constructor
  · intro h; exact extSig_false.1 (h _ (extRun hwf inp))
  · intro hl sig r; exact cert_sound hwf r (Lc_cert hwf inp) v t hl

/-! ## 3. H_CHAIN_SETTLED -/

/-- **H_CHAIN_SETTLED** (exact form): the tail `z` is forced low on all of `[A, B)`. -/
def Settled (net : Netlist) (inp : Trace) (z A B : Nat) : Prop :=
  ∀ t, A ≤ t → t < B → Lc net inp z t

/-- Settled ⇒ in every run the tail is 0 on `[A, B)`: no rise (no runt) in between. -/
theorem settled_sound {net : Netlist} (hwf : net.WF) {inp : Trace} {z A B : Nat}
    (hs : Settled net inp z A B) {sig : Nat → Trace} (r : AndRun net inp sig) :
    ∀ t, A ≤ t → t < B → sig z t = false :=
  fun t h1 h2 => cert_sound hwf r (Lc_cert hwf inp) z t (hs t h1 h2)

/-- **Converse**: a hole in the forced-low set between two forced points is a runt in
some run (the extremal one, quiescent when `inp 0 = true`). -/
theorem runt_of_gap {net : Netlist} (hwf : net.WF) {inp : Trace} {z x t y : Nat}
    (hx : Lc net inp z x) (hy : Lc net inp z y) (ht : ¬ Lc net inp z t) :
    ∃ sig, ∃ _r : AndRun net inp sig, sig z x = false ∧ sig z t = true ∧ sig z y = false := by
  refine ⟨extSig net inp, extRun hwf inp, extSig_false.2 hx, ?_, extSig_false.2 hy⟩
  cases h : extSig net inp z t with
  | true => rfl
  | false => exact absurd (extSig_false.1 h) ht

/-- So the exact condition: `Settled` on `[A, B)` with `Lc z` at `A - 1`.. is equivalent to
"z is low on `[A, B)` in every run". -/
theorem settled_iff {net : Netlist} (hwf : net.WF) (inp : Trace) (z A B : Nat) :
    (∀ sig, AndRun net inp sig → ∀ t, A ≤ t → t < B → sig z t = false) ↔
      Settled net inp z A B := by
  constructor
  · intro h t h1 h2; exact (low_iff hwf inp z t).1 (fun sig r => h sig r t h1 h2)
  · intro hs sig r; exact settled_sound hwf hs r

/-! ## 4. OR networks (FASTRISE) by duality -/

/-- A run of an OR network: every non-input node is the OR of its pins. -/
structure OrRun (net : Netlist) (inp : Trace) (sig : Nat → Trace) where
  pin : Nat → Trace
  src : ∀ t, sig 0 t = inp t
  bd : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → BoundedDelay a.lo a.hi (sig a.src) (pin k)
  node : ∀ v, v ≠ 0 → ∀ t,
    (sig v t = false ↔ ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = v → pin k t = false)

/-- Negation commutes with a bounded-delay channel. -/
theorem bd_not {lo hi : Nat} {i o : Trace} (h : BoundedDelay lo hi i o) :
    BoundedDelay lo hi (fun t => !i t) (fun t => !o t) where
  cause := by
    intro t hc
    have hc' : changes o t := by
      intro he; apply hc; show (!o t) = (!o (t + 1)); rw [he]
    obtain ⟨d, h1, h2, h3, h4⟩ := h.cause t hc'
    exact ⟨d, h1, h2, h3, by show (!o (t + 1)) = (!i (t + 1 - d)); rw [h4]⟩
  settle := by
    intro t ht hs
    have hs' : stableOn i (t - hi) t := by
      intro w a b
      have := hs w a b
      simp only at this
      cases h1 : i w <;> cases h2 : i (t - hi) <;> simp_all
    show (!o t) = (!i t); rw [h.settle t ht hs']

/-- An OR run, negated, is an AND run of the negated input. -/
def OrRun.neg {net : Netlist} {inp : Trace} {sig : Nat → Trace} (r : OrRun net inp sig) :
    AndRun net (fun t => !inp t) (fun v t => !sig v t) where
  pin := fun k t => !r.pin k t
  src := by intro t; simp only [r.src]
  bd := fun k a hk => bd_not (r.bd k a hk)
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

/-- An AND run of the negated input, negated, is an OR run. -/
def AndRun.negOr {net : Netlist} {inp : Trace} {sig : Nat → Trace}
    (r : AndRun net (fun t => !inp t) sig) : OrRun net inp (fun v t => !sig v t) where
  pin := fun k t => !r.pin k t
  src := by intro t; simp only [r.src, Bool.not_not]
  bd := by
    intro k a hk
    have := bd_not (r.bd k a hk)
    exact this
  node := by
    intro v hv t
    have := r.node v hv t
    constructor
    · intro h k a hk hd
      have h' : sig v t = true := by simpa using h
      simpa using this.1 h' k a hk hd
    · intro h
      have h' : sig v t = true := this.2 (fun k a hk hd => by simpa using h k a hk hd)
      simp [h']

/-- **FASTRISE soundness**: the forced-HIGH set of an OR network is `Lc` of the negated
input. -/
theorem or_sound {net : Netlist} (hwf : net.WF) {inp : Trace} {sig : Nat → Trace}
    (r : OrRun net inp sig) (v t : Nat) (h : Lc net (fun t => !inp t) v t) : sig v t = true := by
  have := cert_sound hwf r.neg (Lc_cert hwf _) v t h
  simpa using this

/-- **FASTRISE converse**: a hole in the forced-high set is a low runt in some OR run. -/
theorem or_runt_of_gap {net : Netlist} (hwf : net.WF) {inp : Trace} {z x t y : Nat}
    (hx : Lc net (fun t => !inp t) z x) (hy : Lc net (fun t => !inp t) z y)
    (ht : ¬ Lc net (fun t => !inp t) z t) :
    ∃ sig, ∃ _r : OrRun net inp sig, sig z x = true ∧ sig z t = false ∧ sig z y = true := by
  obtain ⟨sig, r, h1, h2, h3⟩ := runt_of_gap hwf hx hy ht
  exact ⟨_, r.negOr, by simp [h1], by simp [h2], by simp [h3]⟩

/-- FASTRISE exactness. -/
theorem or_high_iff {net : Netlist} (hwf : net.WF) (inp : Trace) (v t : Nat) :
    (∀ sig, OrRun net inp sig → sig v t = true) ↔ Lc net (fun t => !inp t) v t := by
  constructor
  · intro h
    have := h _ (extRun hwf (fun t => !inp t)).negOr
    apply extSig_false.1
    simpa using this
  · intro hl sig r; exact or_sound hwf r v t hl

/-! ## 5. The interval calculus chainck implements -/

/-- An interval `[x, y)` longer than `hi` maps to `[x + hi, y + lo)`; a shorter one to ∅. -/
theorem lowPin_Ico {lo hi : Nat} (hlh : lo ≤ hi) (x y t : Nat) :
    lowPin lo hi (fun w => x ≤ w ∧ w < y) t ↔ (x + hi < y ∧ x + hi ≤ t ∧ t < y + lo) := by
  constructor
  · rintro ⟨s, hs1, hs2, hs3⟩
    have a := hs3 (s - hi) (Nat.le_refl _) (Or.inl (Nat.sub_le _ _))
    have b := hs3 s (Nat.sub_le _ _) (Or.inl (Nat.le_refl _))
    refine ⟨by omega, by omega, ?_⟩
    by_cases hc : lo ≤ t
    · have c := hs3 (t - lo) (by omega) (Or.inr (by omega))
      omega
    · omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x + hi, by omega, h2, fun w a b => by omega⟩

/-- Two sets separated by a point `g` outside both map separately (so a list of maximal
intervals maps interval by interval). -/
theorem lowPin_union_gap (lo hi g : Nat) (L1 L2 : Nat → Prop) (h1 : ∀ w, L1 w → w < g)
    (h2 : ∀ w, L2 w → g < w) (t : Nat) :
    lowPin lo hi (fun w => L1 w ∨ L2 w) t ↔ (lowPin lo hi L1 t ∨ lowPin lo hi L2 t) := by
  constructor
  · rintro ⟨s, hs1, hs2, hs3⟩
    -- the window [s - hi, max s (t - lo)] is contiguous and avoids g
    have hsW := hs3 s (Nat.sub_le _ _) (Or.inl (Nat.le_refl _))
    rcases hsW with hL1 | hL2
    · -- s < g: then every window point is < g
      have hsg := h1 s hL1
      left
      refine ⟨s, hs1, hs2, fun w a b => ?_⟩
      rcases hs3 w a b with h | h
      · exact h
      · exfalso
        have hgw := h2 w h
        -- g lies in the window: s < g < w
        rcases hs3 g (by omega) (by omega) with h' | h'
        · have := h1 g h'; omega
        · have := h2 g h'; omega
    · have hsg := h2 s hL2
      right
      refine ⟨s, hs1, hs2, fun w a b => ?_⟩
      rcases hs3 w a b with h | h
      · exfalso
        have hwg := h1 w h
        rcases hs3 g (by omega) (Or.inl (by omega)) with h' | h'
        · have := h1 g h'; omega
        · have := h2 g h'; omega
      · exact h
  · rintro (h | h)
    · exact lowPin_mono (fun w hw => Or.inl hw) h
    · exact lowPin_mono (fun w hw => Or.inr hw) h

/-- `Lc` is monotone in the input's low set (a longer input pulse forces more). -/
theorem Lc_mono_inp {net : Netlist} (hwf : net.WF) {inp inp' : Trace}
    (h : ∀ t, inp t = false → inp' t = false) : ∀ v t, Lc net inp v t → Lc net inp' v t := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro t hl
    by_cases hv : v = 0
    · subst hv; exact (Lc_zero _ _ _).2 (h t ((Lc_zero _ _ _).1 hl))
    · obtain ⟨k, a, hk, hd, hlow⟩ := (Lc_pos hwf inp hv t).1 hl
      have hlt : a.src < v := hd ▸ (hwf a (List.mem_of_getElem? hk)).1
      exact (Lc_pos hwf inp' hv t).2 ⟨k, a, hk, hd, lowPin_mono (fun w hw => ih a.src hlt w hw) hlow⟩

end Formal.Timing.ChainSettle
