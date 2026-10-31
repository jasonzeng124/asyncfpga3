import Formal.Timing.WinArray
import Formal.Timing.Unroll
import Formal.Net.Ops

/-!
# Probe C-8w: from tcheck's per-run verdicts to a channel's bundling (capstone O6)

Core Lean only. This file is the bridge between two trace models that the project had linked
only by hand:

* tcheck's **run semantics** (10a `Formal.Timing.Run`): ONE launch at time 0 (H_LAUNCH), every
  arc a bounded-delay channel (H_BOUNDED_DELAY), the netlist at rest before the launch
  (H_QUIESCENT), zero-delay node functions (H_ZERO_DELAY_FN, H_LOCAL). Every tcheck soundness
  theorem (`Tcheck.verdict_sound`, `cverdict_sound`, `xverdict_sound`; underneath them
  `checkArr_sound` and `potOK_sound`, both in this project) concludes, for ONE such run, a
  separation: every change of a data node precedes every change of a request (target) node by
  `setup`.
* the **Ops channel model** (8a/8f `Chan`, `Held`): one request, acknowledge and bus trace per
  channel, many transactions, four-phase protocol; `Held c` (H_BUNDLE) says the bus does not
  move across a step that starts and ends mid-transaction.

## The correspondence hypothesis (H_TXRUN), stated as data

A single-launch run says nothing about a circuit that handles many tokens. What links them is a
per-transaction windowing of the circuit's traces, `TxCover`:

* `τ k` is the launch of transaction `k` (the event tcheck's node 0 stands for: the common
  source, or the virtual launch of H_BUNDLED_T0);
* at `τ k` the channel is idle (`req = ack = 0`) and has offered exactly `k` tokens
  (H_LAUNCH_AFTER_CLOSE: the next token is launched only after the previous one closed);
* every request rise of the channel (the `k`-th offer) is a change of a request node of the
  `k`-th run, shifted by `τ k` (H_REQ_IN_RUN);
* every bus change of the channel is a change of a data node of SOME run `k`, shifted by `τ k`,
  with `τ k` not after it (H_DATA_IN_RUN). This is where the gate model meets the timing model:
  the physical bus at the capture pins, between two launches, is the response of the obligation's
  netlist to that launch.

`held_of_tx` (generic, any separation predicate): `TxCover` + the receiver half of the protocol
(`RecvStep`, the consumer's ack rises only while the request is high) + the per-run separation
⇒ `Held c`. The proof is the ordering argument only: a bus change attributed to run `k` happens
no later than the `k`-th request rise, and from `τ k` up to that rise the channel is idle.

Instantiations with the actual checkers:
* `held_of_checkArr`: tcheck's DAG verdict (rule A, E, F, J shapes; `Tcheck.verdict` is
  `decide net.WF && checkArr ..`, and `verdict_sound` is `checkArr_sound`);
* `held_of_cert`: tcheck's cert verdict (rules Hc, Rc, Fd, Z, X shapes: a data DAG plus a late
  side certified by a checked potential; `Tcheck.cverdict` unfolds to exactly the hypotheses
  `hwf`, `hpot`, `hnz`, `hwin` below with `late := lateNet ..` and the targets encoded).

## What is NOT shown here

* That a real circuit run meets `TxCover`. Its fields are the gate/timing-model correspondence
  and remain hypotheses. H_QUIESCENT at every launch is the hard part: the previous transaction's
  waves (request return-to-zero through a matched delay line, data glitches) must have died out
  before `τ k`. Rule F/Fd checks the request line's drain; nothing checks the data side's
  (it follows from the previous transaction's own A verdict plus H_LAUNCH_AFTER_CLOSE only if
  the data DAG's latest change bound is below the request bound, which is what A checks).
* That the channel here is the capstone's channel. `Held` is proved for the PHYSICAL
  observation of a channel (request at the capture cell's pin, bus at the capture pins). The
  capstone's traces satisfy zero-delay data equations (H_DATA_COMB, H_LATCH_COMB inside
  `H_CELLS`) and so cannot be the physical bus; see `Formal.Net.CapstoneBundle` and
  notes/C-8w-bundle.md.
-/

namespace Formal.Timing.Obl
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing

/-- H_TXRUN for one channel and one obligation, abstract form. `D k u`: some data node of the
`k`-th run changes at run time `u`; `R k v`: some request (target) node of the `k`-th run changes
at run time `v`. -/
structure TxCover (c : Chan) (D R : Nat → Nat → Prop) where
  τ : Nat → Nat
  idle : ∀ k, c.req (τ k) = false ∧ c.ack (τ k) = false
  count : ∀ k, cnt (riseB c.req) (τ k) = k
  reqIn : ∀ k r, OffAt c k r → R k (r - τ k)
  datIn : ∀ s, c.dat (s + 1) ≠ c.dat s → ∃ k, τ k ≤ s ∧ D k (s - τ k)

theorem riseB_of {s : Trace} {u : Nat} (h0 : s u = false) (h1 : s (u + 1) = true) :
    riseB s u = true := by simp [riseB, h0, h1]

/-- **The bridge, generic form.** -/
theorem held_of_tx {c : Chan} {D R : Nat → Nat → Prop} (X : TxCover c D R)
    (hrecv : ∀ t, RecvStep c t) (hsep : ∀ k u v, D k u → R k v → u ≤ v) : Held c := by
  intro t h0 _
  apply Classical.byContradiction
  intro hne
  obtain ⟨k, hkt, hD⟩ := X.datIn t hne
  -- from τ k to t: idle, and still k offers
  have key : ∀ n, X.τ k + n ≤ t →
      c.req (X.τ k + n) = false ∧ c.ack (X.τ k + n) = false ∧
        cnt (riseB c.req) (X.τ k + n) = k := by
    intro n
    induction n with
    | zero => intro _; exact ⟨(X.idle k).1, (X.idle k).2, X.count k⟩
    | succ n ih =>
      intro hn
      obtain ⟨hr, ha, hc⟩ := ih (by omega)
      have hreq : c.req (X.τ k + n + 1) = false := by
        cases hq : c.req (X.τ k + n + 1) with
        | false => rfl
        | true =>
          exfalso
          have hoff : OffAt c k (X.τ k + n) := ⟨riseB_of hr hq, hc⟩
          have hR := X.reqIn k _ hoff
          have := hsep k _ _ hD hR
          omega
      have hack : c.ack (X.τ k + n + 1) = false := by
        cases hq : c.ack (X.τ k + n + 1) with
        | false => rfl
        | true =>
          exfalso
          have := hrecv (X.τ k + n) (by rw [hq, ha]; decide)
          rw [ha, hr] at this
          exact this rfl
      refine ⟨hreq, hack, ?_⟩
      have hz : riseB c.req (X.τ k + n) = false := by simp [riseB, hr, hreq]
      show cnt (riseB c.req) (X.τ k + n + 1) = k
      rw [cnt, hz, hc]; rfl
  obtain ⟨hr, ha, _⟩ := key (t - X.τ k) (by omega)
  rw [show X.τ k + (t - X.τ k) = t by omega] at hr ha
  simp [inTx, hr, ha] at h0

/-! ## Instantiation with tcheck's DAG verdict (rules A, E, F, J; `Tcheck.verdict`) -/

/-- The data/request predicates of one DAG obligation, per transaction. -/
abbrev dagD (sig : Nat → Nat → Trace) (data : List Nat) (k u : Nat) : Prop :=
  ∃ d ∈ data, changes (sig k d) u
abbrev dagR (sig : Nat → Nat → Trace) (req : Nat) (k v : Nat) : Prop := changes (sig k req) v

/-- **tcheck PASS (DAG form) ⇒ H_BUNDLE of the observed channel**, under H_TXRUN.
`decide net.WF && checkArr net req data setup` is literally `Tcheck.verdict`. -/
theorem held_of_checkArr {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : checkArr net req data setup = true)
    {c : Chan} {sig : Nat → Nat → Trace} (runs : ∀ k, Run net (sig k))
    (X : TxCover c (dagD sig data) (dagR sig req)) (hrecv : ∀ t, RecvStep c t) : Held c :=
  held_of_tx X hrecv (fun k u v ⟨d, hd, hu⟩ hv => by
    have := checkArr_sound hwf hc (runs k) d hd u v hu hv
    omega)

/-! ## Instantiation with tcheck's cert verdict (rules Hc, Rc, Fd, Z, X; `Tcheck.cverdict`) -/

abbrev certR (sigL : Nat → Nat → Trace) (targets : List Nat) (k v : Nat) : Prop :=
  ∃ q ∈ targets, changes (sigL k q) v

/-- **tcheck cert PASS ⇒ H_BUNDLE of the observed channel**, under H_TXRUN. The hypotheses
`hwf`, `hpot`, `hnz`, `hwin` are the four conjuncts of `Tcheck.cverdict` with
`late = lateNet i.late stor G`, `pot = i.potf` and `targets = i.late.targets` encoded by
`enc i.late`. Two runs per transaction (data side, late side), launched together. -/
theorem held_of_cert {dag late : Netlist} (hwf : dag.WF) {pot : Nat → Nat}
    (hpot : potOK late.arcs pot = true) {data targets : List Nat} {setup : Nat}
    (hnz : ∀ q ∈ targets, q ≠ 0)
    (hwin : ∀ d ∈ data, ∀ e l, winArr dag d = some (e, l) → ∀ q ∈ targets, l + setup ≤ pot q)
    {c : Chan} {sigD sigL : Nat → Nat → Trace}
    (rD : ∀ k, Run dag (sigD k)) (rL : ∀ k, Run late (sigL k))
    (X : TxCover c (dagD sigD data) (certR sigL targets)) (hrecv : ∀ t, RecvStep c t) :
    Held c :=
  held_of_tx X hrecv (fun k u v ⟨d, hd, hu⟩ ⟨q, hq, hv⟩ => by
    have hb := potOK_sound hpot (rL k) v q (hnz q hq) hv
    obtain ⟨e, l, hw, _, hul⟩ := changes_in_winArr hwf (rD k) d u hu
    have := hwin d hd e l hw q hq
    omega)

/-! ## Several obligations on one channel

A channel can be covered by several instances (rule A emits one per start; rule E several
launches per pin). The cover only has to attribute each bus change to one of them. -/

/-- Union of per-instance predicates. -/
abbrev anyOf {ι : Type} (L : List ι) (P : ι → Nat → Nat → Prop) (k u : Nat) : Prop :=
  ∃ i ∈ L, P i k u

/-- A bus change attributed to instance `i` and a request change of instance `j` are
separated when every instance's data precedes every instance's request (what tcheck checks
when all instances of a channel share the request node and launch). -/
theorem held_of_many {ι : Type} {c : Chan} {L : List ι} {D R : ι → Nat → Nat → Prop}
    (X : TxCover c (anyOf L D) (anyOf L R)) (hrecv : ∀ t, RecvStep c t)
    (hsep : ∀ i ∈ L, ∀ j ∈ L, ∀ k u v, D i k u → R j k v → u ≤ v) : Held c :=
  held_of_tx X hrecv (fun k u v ⟨i, hi, hu⟩ ⟨j, hj, hv⟩ => hsep i hi j hj k u v hu hv)

/-! ## Necessity of the two ordering fields

Without H_LAUNCH_AFTER_CLOSE the bridge is false: a bus change can sit inside a transaction even
though every run's separation holds (the change is attributed to a launch that happened while
the channel was still busy). `held_needs_close` exhibits it: one transaction, the bus changes
mid-transaction, and the separation, `reqIn`, `datIn` and the receiver rule all hold; only the
launch-ordering fields `idle` and `count` fail. -/

/-- A channel that runs one four-phase transaction (req↑ at 0→1, ack↑ 1→2, req↓ 2→3, ack↓ 3→4)
and whose bus moves at step 1→2 (mid-transaction). -/
def badCh : Chan where
  req := fun t => t == 1 || t == 2
  ack := fun t => t == 2 || t == 3
  dat := fun t => if t ≤ 1 then 0 else 1

theorem badCh_not_held : ¬ Held badCh := by
  intro h
  have := h 1 (by decide) (by decide)
  simp [badCh] at this

/-- Dropping the launch-ordering fields (`idle`, `count`) breaks the bridge: with the launch of
run 0 placed at step 1 (mid-transaction), the separation, `reqIn` and `datIn` all hold and the
bus still moves mid-transaction. -/
theorem held_needs_close :
    ∃ (τ : Nat → Nat) (D R : Nat → Nat → Prop),
      (∀ k u v, D k u → R k v → u ≤ v) ∧ (∀ t, RecvStep badCh t) ∧
      (∀ k r, OffAt badCh k r → R k (r - τ k)) ∧
      (∀ s, badCh.dat (s + 1) ≠ badCh.dat s → ∃ k, τ k ≤ s ∧ D k (s - τ k)) ∧
      ¬ Held badCh ∧ ¬ (badCh.req (τ 0) = false ∧ badCh.ack (τ 0) = false) := by
  refine ⟨fun _ => 1, fun _ u => u = 0, fun _ v => v = 0, ?_, ?_, ?_, ?_, badCh_not_held, ?_⟩
  · intro k u v hu hv
    obtain rfl : u = 0 := hu
    obtain rfl : v = 0 := hv
    exact Nat.le_refl 0
  · intro t
    match t with
    | 0 => simp [RecvStep, badCh]
    | 1 => simp [RecvStep, badCh]
    | 2 => simp [RecvStep, badCh]
    | 3 => simp [RecvStep, badCh]
    | n + 4 =>
      intro h; exfalso; apply h
      show (n + 4 + 1 == 2 || n + 4 + 1 == 3) = (n + 4 == 2 || n + 4 == 3)
      have e1 : (n + 4 + 1 == 2) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      have e2 : (n + 4 + 1 == 3) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      have e3 : (n + 4 == 2) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      have e4 : (n + 4 == 3) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      rw [e1, e2, e3, e4]
  · intro k r hoff
    show r - 1 = 0
    have h1 : riseB badCh.req r = true := hoff.1
    have h2 : (!(r == 1 || r == 2) && (r + 1 == 1 || r + 1 == 2)) = true := h1
    cases hr : r with
    | zero => rfl
    | succ m =>
      rw [hr] at h2
      cases m with
      | zero => simp at h2
      | succ m' =>
        exfalso
        simp at h2 <;> omega
  · intro s hs
    refine ⟨0, ?_, ?_⟩
    · show 1 ≤ s
      apply Classical.byContradiction; intro h0
      have : s = 0 := by omega
      subst this; exact hs rfl
    · show s - 1 = 0
      apply Classical.byContradiction; intro h
      apply hs
      show (if s + 1 ≤ 1 then 0 else 1) = (if s ≤ 1 then 0 else 1)
      rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega)), ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]
  · simp [badCh]

end Formal.Timing.Obl
