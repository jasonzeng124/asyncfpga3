# A-trace-event: trace representation (b), event lists

Track 2, probe (b). Namespace `Formal.Core.TraceEvent`.

Files:
- `formal/lean/Formal/Core/Trace/Event.lean`: proved, 625 lines, no `sorry`/`axiom`/`native_decide`.
  `#print axioms` on the main theorems shows only `propext, Classical.choice, Quot.sound`.
- `formal/lean/Wip/TraceEvent.lean`: one open statement (`ChanX.comp`), marked `sorry`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && ../slot.sh lake env lean Formal/Core/Trace/Event.lean

This gives no errors and no warnings. Imports: `Mathlib.Basic.Real.Basic` and `Mathlib.Tactic.Linarith`.
`Mathlib.Data.Real.Basic` is now a deprecated alias of `Mathlib.Basic.Real.Basic` in this Mathlib.

## Representation

```lean
structure Sig where
  init   : Bool            -- value at -∞
  evs    : List ℝ          -- transition times
  sorted : evs.Pairwise (· < ·)   -- strictly increasing
def flips : List ℝ → ℝ → Bool        -- parity of #events ≤ t (works on ANY list)
def Sig.val (s : Sig) (t : ℝ) := xor s.init (flips s.evs t)
```

- **Val = Bool.** Every transition is a toggle, so an event is just a time stamp.
  The value is right-continuous: the new value holds from the event instant on.
- **ℝ, not ℚ.** Everything used is ordered-field arithmetic plus `linarith`, so ℚ would be no easier.
  ℝ matches the other probes and later ODE/analog work. The cost is that the definitions are
  `noncomputable` (`decide (e ≤ t)` on ℝ), so there is no `#eval`.
  Moving to ℚ (or to a generic linear ordered field) is a mechanical change if
  computation is ever wanted, for example to run a timing checker on concrete numbers.
- **Well-formedness** is the `sorted` field. Finite variability is automatic: the list is finite.
  The type is *stronger* than non-Zeno, though: a `Sig` has finitely many transitions **in total**.
  So it describes finite-horizon behaviours (one handshake, one pulse, a bounded run).
  It cannot describe a free-running ring oscillator or a never-ending handshake stream.
  Fixing this needs lazy/infinite lists, or `ℕ → ℝ` with `→ ∞`, which is much more painful.
  Alternatively, state liveness as "for every horizon T, the prefix up to T is a `Sig`".
- **Canonicity** (`Sig.ext_val`): two signals with equal `val` functions are equal as
  structures. Pointwise reasoning and list reasoning can therefore be mixed freely.
  This was the key enabling lemma for B5.
- `flips` is defined for *unsorted* lists too. Toggles commute (`flips_swap`) and coincident
  events cancel (`flips_dup`). This gives a clean semantics for crossing events (see B3).

## Benchmark results

All wall times are for writing plus fixing, measured from an empty file. The whole file took about 10
minutes; the Mathlib oleans were already there. Each check takes 5-15 s.

### B0 Definitions: proved (115 lines incl. canonicity)
`Sig`, `flips`, `Sig.val`, `const`, `flips_of_lt`, `flips_head`, `flips_swap`, `flips_dup`,
`flips_inj`, `exists_lt_all`, `Sig.ext_val`. The only nontrivial proof is
`flips_inj` (sorted toggle lists with equal parity functions are equal), about 30 lines.

### B1 Fixed pure delay: proved (29 lines)
`delay d s` shifts every event by `d`.
- `delay_val : (delay d s).val t = s.val (t - d)`
- `delay_delay : delay d₂ (delay d₁ s) = delay (d₁ + d₂) s`. This is a structural equality,
  proved by one `simp` (`List.map_map`, `add_assoc`).
- `delay_zero`.
The `d ≥ 0` hypothesis is not needed for the algebra; causality is the only reason to want it.
This is the easiest item in this representation: delay is just `List.map`.

### B2 Bounded transport channel as a relation: proved (96 lines incl. `val_stable`)
`Within lo hi l l'` pairs the i-th input event with the i-th output event, with delay in
`[lo, hi]`. `Chan lo hi x y := y.init = x.init ∧ Within lo hi x.evs y.evs`.
- Every input transition appears at the output: the pairing is one-to-one.
- No other output transitions: the lists have equal length.
- Order is preserved because `y` is a `Sig`, so its list is strictly sorted.

Proved:
- `Chan.comp`: `[lo₁,hi₁] ; [lo₂,hi₂] ⊆ [lo₁+lo₂, hi₁+hi₂]`.
- `Chan.mono`.
- `chan_point_iff`: `Chan d d x y ↔ y = delay d x`. The degenerate channel is exactly B1.
- `Chan.total`: if `lo ≤ hi`, every input has an output, so the relation is never vacuous.
- `Chan.val_stable`: if no input transition lies in `[t-hi, t-lo]`, then `y.val t = x.val (t-lo)`.
  This is the lemma that reads a settled gate output; circuit proofs will use it all the time.

All of these are list induction on `Within` plus `linarith`, with no pain.

### B3 Pulses: proved (64 lines). Order-crossing is handled by having TWO channels
- `chan_pulse`: through `Chan lo hi`, `pulse v a w` gives exactly one pulse `[b, b+w']`, where:
  - `lo ≤ b-a ≤ hi`;
  - `w-(hi-lo) ≤ w' ≤ w+(hi-lo)`;
  - **`0 < w'`**.

**Decision on order-crossing.** In `Chan` the output must be a sorted `Sig` matched index by index,
so behaviours in which the two edges cross or coincide are *excluded*. `Chan` is total, so it never
becomes vacuous, but it *under-approximates* the physical channel when `w ≤ hi-lo`. A safety proof
"for all traces satisfying `Chan`" would then miss the pulse-loss behaviour. That is unsound for
runt and glitch reasoning, and it is the arbiter's case.

The second channel `ChanX` fixes this:
- Definition: `ChanX lo hi x y := ∃ raw, Within lo hi x.evs raw ∧ ∀ t, y.val t = xor x.init (flips raw t)`.
  Each event gets its own delay, the raw list may be unsorted, and the output is its toggle
  parity.
- Crossed edges commute. A positive pulse whose falling edge overtakes its rising edge is seen as
  a positive pulse of width `|Δ|`.
- Coincident edges cancel, so the pulse is lost.

Proved:
- `Chan.toX` (`Chan ⊆ ChanX`) and `ChanX.mono`.
- `chanX_pulse_lost`: `w ≤ hi-lo` implies `ChanX lo hi (pulse v a w) (const v)`. The pulse can vanish.
- `chanX_pulse_kept`: `w > hi-lo` implies that every `ChanX` output differs from `v` at some time.
  The pulse can never vanish.

Not proved: `ChanX.comp` (in Wip). It needs a multiset-parity normal form for raw lists, about 150-250 lines.

Caveat: the toggle semantics models crossing as "both toggles happen". VHDL `transport` instead
deletes the overtaken transaction. Neither is silicon; see fidelity.

### B4 Inertial delay: proved (63 lines)
`inert δ` works on the sorted list, like VHDL `inertial` with reject limit δ. If the next event
comes less than δ later, both events are dropped. Otherwise the event is emitted at `e+δ`.
- `inert_sublist` / `inertial_sub`: the output is a subsequence of the input delayed by δ.
  Inertial delay never invents transitions. This also gives sortedness for free.
- `inertial_short`: `w < δ` gives the constant signal (no output transition).
- `inertial_long`: `δ ≤ w` gives `delay δ`.
- `inertial_spaced`: if all consecutive input events are ≥ δ apart, `inertial δ = delay δ`.

The only friction was Lean mechanics. `e :: tl@(e' :: rest)` patterns leak `namedPattern` into
goals, so I used `termination_by l.length` instead. `if_neg` is deprecated in this Mathlib.

Inertial delay is a *function* here. A bounded inertial *relation* (δ in `[lo,hi]`, composed with a
transport window) was not attempted. It would take about 50 lines on top.

### B5 Gate as relation, circuit as conjunction: proved (41 lines, plus 200 lines of gate merge)
- `AndGate lo hi a b y := ∃ z, (∀ t, z.val t = a.val t && b.val t) ∧ Chan lo hi z y`.
- `and_follows`: if `b ≡ 1`, then `AndGate lo hi a b y → Chan lo hi a y`, using `Sig.ext_val`.
- `and_chain`: a 2-gate circuit given as a conjunction `AndGate … a b y₁ ∧ AndGate … y₁ c y₂`, with
  `b, c ≡ 1`, gives `Chan (lo₁+lo₂) (hi₁+hi₂) a y₂`.
- To show the gate relation is **not vacuous**, I built the zero-delay gate as a function on event
  lists: `gateEv g`, a two-pointer merge that emits an event when `g` changes, with simultaneous
  input events handled together. It comes with:
  - `gateEv_sorted` and `gate_val : (gate g a b).val t = g (a.val t) (b.val t)` for **any**
    `g : Bool → Bool → Bool`;
  - `andGate_iff : AndGate lo hi a b y ↔ Chan lo hi (gate and a b) y`;
  - `AndGate.total`.

**Pain point:** the merge is the price of event lists. It is 200 lines of four-way case analysis
(left-only, right-only, `<`, `>`, `=`). This is where a `ℝ → Bool` representation would be
trivial (`fun t => a t && b t`). Still, it was written once, generically in `g`, and checked on
the first attempt. An n-input LUT would need an n-way merge, or a fold of the 2-way merge with
`Sig`-valued intermediate signals. That needs care because a LUT is not a composition of 2-input
gates when hazards matter.

## Verdict

**Works.** All of B0-B5 are proved, plus the extras above. The one open item (`ChanX.comp`) is in Wip.

Strengths:
- Delays and channels are list maps and pairwise relations. Every channel lemma is induction plus
  `linarith`, and B1-B4 had essentially no friction.
- "Which transitions exist and in what order" is first-class. That is exactly what pulse, runt,
  order-crossing and bundling-constraint arguments are about.
- Canonicity (`ext_val`) lets pointwise reasoning and list reasoning be mixed.
- Finite variability needs no proof obligation.

Weaknesses:
1. Pointwise logic (gates, LUTs) needs merge functions. That is about 200 lines per gate shape,
   or an n-way generalization.
2. Only finitely many transitions in total, so no infinite behaviours without extra machinery.
3. Order-crossing needs a second, non-canonical channel (`ChanX`), and its composition is the hard lemma.
4. `noncomputable` over ℝ.

**Effort to finish:**
- `ChanX.comp`: 0.5-1 day.
- A bounded inertial relation: 0.5 day.
- An n-input LUT gate built from `gateEv` or a generic n-way merge: 1 day.
- Infinite traces as horizon-indexed prefixes: 1-2 days.

**What it buys the project:** a channel calculus in which pulse survival, pulse loss, and window
composition are already theorems. It also provides a settled-output lemma (`Chan.val_stable`) for
circuit proofs, and an executable-shaped model: with ℚ it could evaluate concrete traces, so
it is close to a GLS cross-check. A natural hybrid: keep event lists as the *trace type* and use
`Sig.val` plus `ext_val` to state gate functions pointwise. That is already how `AndGate` works,
and `gate_val` discharges the existence side.

## Fidelity notes (7-series)

| primitive in this file | faithful to silicon? | explicit hypothesis | how to test |
|---|---|---|---|
| `delay d` (pure) | No: one number per arc. It is only the degenerate case of `Chan`. | `d` | none needed: it is subsumed by `Chan` |
| `Chan lo hi` (order-preserving transport) | Good for a routed net carrying edges that are well separated (`w > hi-lo`). Bounds should come from prjxray-db fast-min/slow-max (Elmore model in `prjxray/timing.py`), per arc. It does **not** separate rise and fall. | `[lo,hi]` per arc; inputs separated by more than `hi-lo` if `Chan` (rather than `ChanX`) is used | GLS with the prjxray-derived SDF min/max; ring-oscillator periods on the board must fall inside the composed window (`Chan.comp`) |
| `ChanX lo hi` (crossing allowed, toggles commute) | Over-approximates the *timing* of narrow pulses. Its *shape* for crossed edges (pulse of width `|Δ|`) is a modelling choice, not silicon. A buffered pip or a LUT input buffer is more likely to attenuate a runt to nothing, or to a degraded (non-binary) level. | that crossed or coincident edges behave as toggles | GLS pulse-width sweep through one pass-transistor pip chain and one buffered pip, with the transport-wire `prims.v` as on `claude/research`; board: a pulse-shrinking ring, measuring the width at which pulses die |
| `inertial δ` | It matches what the current iverilog GLS does for LUT/MUXF/FF pins (module-path inertial delays swallow narrow pulses), and research/PROGRAM.md flags exactly that as possibly *unfaithful*. A real LUT has no single δ: pulse rejection depends on the drive and load analog response. | the rejection threshold δ (and that it is sharp) | board: sweep input pulse width into one LUT, look for the threshold and how sharp it is; compare with the involution-channel probe |
| `gate g` / `AndGate` (zero-delay Boolean function, then a channel) | Idealized. A 7-series LUT is a pass-transistor mux tree. On multi-input changes it can glitch even when the Boolean output is constant; for example, AND with both inputs toggling at nearly the same time can produce a runt. Here simultaneous edges are merged exactly (no glitch), and near-simultaneous edges give a pulse of exactly the gap width. | that the LUT is glitch-free for single-input changes and has the Boolean function's value when settled (Kleene probe, track 4) | GLS with a mux-tree LUT model; board: two inputs with controlled skew into one LUT, count output pulses |
| `Sig` (finitely many transitions, binary) | No X/metastable level, and finite horizon only. | binary values everywhere | track 3 (Kleene) and the analog probe cover what this cannot |

## Comparison-ready table

| item | proved? | Lean lines | wall time | what was painful |
|---|---|---|---|---|
| B0 defs + canonicity (`Sig.ext_val`) | yes | 115 | ~3 min | `flips_inj` case analysis (30 lines); otherwise nothing |
| B1 pure delay, `delay_delay` | yes | 29 | ~1 min | nothing (`List.map`) |
| B2 `Chan` comp / mono / total / point=delay / `val_stable` | yes | 96 | ~2 min | nothing; induction on `Within` + `linarith` |
| B3 pulse width; loss iff `w ≤ hi-lo` | yes (`Chan`: width bounds; `ChanX`: lost/kept) | 64 | ~2 min | order-crossing needs a second channel `ChanX`; `ChanX.comp` **not proved** (Wip) |
| B4 inertial: short swallowed, long = delay, spaced = delay | yes | 63 | ~2 min | `namedPattern` from `@`-patterns, so use `termination_by` instead |
| B5 AND relation, `and_follows`, 2-gate circuit | yes | 41 | ~1 min | needs `ext_val` |
| B5 extra: zero-delay gate merge (any `g`), relation total | yes | 200 | ~5 min | the 4-way merge is the real cost of event lists for pointwise logic |
| **total** | **all B0-B5** | **625** | **~15 min of editing (plus 5-15 s per check)** | merge for gates; finite-total-transitions; crossing semantics is a choice |
