# A-circuit: event-list bridge and the generic circuit layer

Probe of shard A, track 2 (bridge) + the circuit layer of PROGRAM.md's
"model the owner has in mind", item 1.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/Circuit.lean` | proved; checks clean (Lean core only, no Mathlib) |
| `formal/lean/Formal/Core/Trace/Bridge.lean` | proved; checks clean (imports `Mathlib.Algebra.Order.Archimedean.Real.Basic`, `Mathlib.Tactic.Linarith`) |
| `formal/lean/Wip/Circuit.lean` | two open statements, `sorry` |

Check commands (from `formal/lean`, `PATH=$HOME/.elan/bin:$PATH`):

    ../slot.sh lake env lean Formal/Core/Circuit.lean
    ../slot.sh lake env lean Formal/Core/Trace/Bridge.lean

## Circuit layer (`Formal.Core`, file `Circuit.lean`)

Definitions, all parametric in a wire type `W` and a signal type `σ`:

- `Beh W σ := W → σ` — a behaviour (signal on every wire).
- `Gate W σ := Beh W σ → Prop` — a gate is a relation. Builders
  `Gate.rel1 R a o`, `Gate.rel2 R a b o`, `Gate.relN R ins o`;
  `Gate.DependsOn g S` (gate reads only wires in `S`), with
  `rel1_dependsOn`, `rel2_dependsOn`; `Gate.rename f`.
- `Circuit W σ := List (Gate W σ)`; `Circuit.Sat c v := ∀ g ∈ c, g v`;
  `Circuit.compose := List.append`; `Circuit.rename f c` moves a circuit into a
  host wire type (two circuits are connected by mapping their wires to common
  host wires: this is the "disjoint union with shared wires").
- `Spec W σ := Beh W σ → Prop`; `Refines c S := ∀ v, Sat c v → S v`
  (the theorem form "for all traces satisfying every gate, P").
- `Circuit.Obs c ext e := ∃ v, Sat c v ∧ v ∘ ext = e` — hiding internal wires
  by existential projection onto an interface `ext : E → W`;
  `RefinesObs c ext S`.
- `Circuit.Receptive c inp` — every input assignment extends to a satisfying
  behaviour (non-vacuity).

Theorems (exact names):
`Circuit.sat_nil`, `Circuit.sat_cons`, `Circuit.sat_append` (Sat of a
composition = conjunction), `Circuit.sat_compose`, `Circuit.sat_rename`,
`Circuit.Sat.left`, `Circuit.Sat.right`, `Circuit.receptive_append`
(feed-forward composition preserves receptiveness),
`Refines.mono`, `Refines.of_mem`, `Refines.append_left`,
`Refines.append_right`, `Refines.and`, `Refines.append` (C1⊑S1, C2⊑S2 ⇒
C1++C2 ⊑ S1∧S2), `Refines.chain` (assume-guarantee), `Refines.rename`,
`Refines.compose` (circuits on their own wire types glued by renamings),
`Refines.toObs`, `Refines.ofObs`, `Refines.series` (two one-input relations in
series with the middle wire hidden refine any relation containing their
relational composition — bench B2's channel composition is an instance),
`RefinesObs.mono`, `RefinesObs.compose`, `RefinesObs.restrict` (hiding more
wires), plus a zero-delay AND sanity example.

Design decisions:
- Gates are predicates on the *whole* behaviour, not structured objects with
  input/output ports. This is the most general form (any relation, including
  ones with several outputs, metastability-producing ones, or environment
  assumptions) and costs nothing; port structure is recovered with
  `rel1/rel2/relN` and `DependsOn`. Input/output direction matters only for
  receptiveness, which is stated separately.
- Circuits are lists, not sets: decidable membership is not needed, and lists
  make `Sat` of concrete netlists reduce by `simp [Circuit.sat_cons]`.
- Composition is over one wire type; heterogeneous composition goes through
  `rename`. Shards B/C: write each cell over its own small wire type (e.g. an
  inductive of its port and internal names), prove `Refines`/`RefinesObs` for
  it, then place instances in the network with `Circuit.rename` and use
  `Refines.compose` / `RefinesObs.compose`.
- Universes are polymorphic except that the two components of
  `Refines.compose` share one universe (harmless).

Vacuity warning: a circuit whose relations have no common solution refines
everything. Theorems about cells should come with a receptiveness lemma
(`Circuit.receptive_append` handles feed-forward composition; feedback loops
need a time-induction construction, see Wip).

## Bridge (`Formal.Core.Bridge`, file `Trace/Bridge.lean`)

`EvTrace` = `init : Bool`, `ts : List ℝ`, `sorted : ts.Pairwise (· < ·)`.
`denote init ts t = init xor parity #{τ ∈ ts | τ ≤ t}` (right-continuous: at a
transition the new value holds). Predicates on `f : ℝ → Bool`: `RightCont`,
`LeftConst f t`, `ChangesAt f t := ¬ LeftConst f t`, `FinChanges f := ∃ list
covering all change points`.

Proved:
- `denote_rightCont`, `denote_eq_of_gap` (constant between transitions),
  `denote_below` (initial value before the first transition).
- `changesAt_denote`: for a strictly increasing list, `ChangesAt (denote i ts) t
  ↔ t ∈ ts`; `denote_finChanges`; `EvTrace.rightCont`, `EvTrace.finChanges`.
- `denote_injective`, `EvTrace.toFun_injective`.
- `eq_of_noChange` (connectedness, via `Real.exists_isLUB`),
  `left_of_change`, `eq_of_sameChanges` (uniqueness).
- `exists_evTrace`: every right-continuous `f` with finitely many changes is
  in the image; `range_toFun`: image = `{f | RightCont f ∧ FinChanges f}`.
  (Sorting helper `sortStrict` with `mem_sortStrict`, `sortStrict_sorted`.)

So both directions were tractable on ℝ; the bijection is complete. The ℝ≥0
variant is left as a Wip statement (`exists_evTrace_nonneg`), only because
the project has not fixed whether time starts at 0; it is a routine reduction.

Note on "change": `ChangesAt` is "not constant on any left neighbourhood". For
a right-continuous Bool function with finitely many changes this coincides
with "left limit ≠ value". A function that oscillates infinitely often near a
point (Zeno) has that point as a change point and, if there are infinitely
many such, is excluded by `FinChanges`.

## Status of the check

- `Circuit.lean`: checked with `slot.sh lake env lean`, no errors, no
  warnings, no sorry/axiom.
- `Bridge.lean`: checked with `slot.sh lake env lean` once
  `Mathlib.Algebra.Order.Archimedean.Real.Basic` was built (needed for
  `Real.exists_isLUB`; `Mathlib.Data.Real.Archimedean` is a deprecated alias of
  it): no errors, no warnings, no sorry/axiom/native_decide.
- `Wip/Circuit.lean`: statements elaborate (checked as a scratch concatenation,
  since Wip cannot import unbuilt Formal modules); two `sorry`s.

## Wip (`Wip/Circuit.lean`)

- `exists_evTrace_nonneg` — bridge on `[0, ∞)`.
- `inverter_ring_nonvacuous` — a self-loop inverter with pure delay `d > 0` has
  a behaviour (square wave); placeholder for receptiveness of cyclic circuits.

## Verdict

**Works.** The circuit layer is ~300 lines, all trivial proofs (minutes each),
no Mathlib; it imposes no choice of trace representation. The bridge is
~430 lines; the only non-trivial part was the connectedness argument
(`eq_of_noChange`, sup argument) and uniqueness. Wall time ≈ 1 h including
waiting; both files went through with almost no iteration (the only fix was
making `Gate/Spec/Circuit` `abbrev` so that membership and application see
through them).

Effort to finish: ℝ≥0 bridge ≈ 1 h; receptiveness of cyclic circuits with
positive-lower-bound delays ≈ 1–2 days (needs time induction over event
lists — the event-list side of the bridge is the natural place to build
witnesses).

What it buys: shards B and C get one fixed, representation-independent
statement form (`Refines` / `RefinesObs`) and the compositional lemmas, so
cell proofs compose into network proofs by `Refines.compose` without
re-proving plumbing. The bridge means the trace-representation decision of
track 2 is not a lock-in between event lists and `ℝ → Bool`: any theorem can be
transported, since `EvTrace.toFun` is a bijection onto well-formed signals.

## Fidelity notes

- The circuit layer itself makes no physical claim: fidelity lives entirely in
  the gate relations plugged in (LUT, routing, FF models from other probes).
  One structural assumption it does encode: **a circuit's behaviour is exactly
  the conjunction of its gates' relations** — wires are ideal equipotential
  nodes (one signal per wire, shared by every reader). On the 7-series fabric a
  net with several sinks has a *different* delay to each sink, so a net must
  be modelled as one driver wire plus one routing-channel gate per sink
  (`Gate.rel1 (channel lo hi) drv sinkᵢ`), never as a single wire read by all
  sinks. Testable by GLS with per-sink SDF interconnect delays (research
  branch) versus a single-wire model: they must disagree whenever sink delays
  differ.
- No interference/loading between gates (a gate's relation does not depend on
  who reads its output). Pass-transistor pips (prjxray marks them) violate this
  in principle (bidirectional, load-dependent delay); it is absorbed into the
  [lo, hi] bounds of the routing channel taken from prjxray-db's slow/fast
  min/max for the *routed* net. Hypothesis: those bounds hold for the final
  routing's loading. Test: board ring-oscillator measurements on the routed
  net vs. the bounds.
- Bridge: Boolean right-continuous traces with finitely many transitions.
  This excludes X/intermediate voltages and Zeno behaviour by construction;
  metastability is therefore not representable at this level (needs the
  Kleene or analog layer, items 3–4). Right-continuity is a convention (value
  at the switching instant), physically unobservable.
