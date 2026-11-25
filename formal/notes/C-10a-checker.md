# C-10a: verified interval timing checker (track 10, core)

## Verdict

**Works.** Core Lean, about 1100 lines, checks in roughly 20 s. There is no sorry, axiom or
native_decide; the audit finds only propext, Classical.choice and Quot.sound.
- An executable interval STA checker over a DAG of delay arcs (`win`, `check`, `slack`).
- It is proved **sound** against Prelim's `BoundedDelay` (H_BOUNDED_DELAY) run semantics.
- Its per-node windows are proved **exact**: both ends are attained.
- The bundling check is proved **exact when the request and data cones share only the launch**.
- With a shared arc (correlated delay) the answer depends on the delay semantics, and both cases are proved on a minimal example:
  - Under per-event H_BOUNDED_DELAY, which passes glitches, the check is exact.
  - Under one fixed delay per arc it is only conservative: the CPPR (common path pessimism removal) case.
- It runs on a toy one-link netlist (`bd_link`-shaped). The 4-bit bus passes with 58 ps slack. A short delay element fails with -92 ps, and the model has a violating run for it.

## What checks

Run command (from `formal/`):

    ./check.sh Formal/Timing/Semantics.lean Formal/Timing/Checker.lean Formal/Timing/CheckerToy.lean

Single file: `cd formal/lean; LEAN_PATH=$PWD/.lake/build/lib/lean ../slot.sh lean FILE`
(compile Semantics, then Checker, to oleans first with `-o`).

| file | content |
|---|---|
| `Formal/Timing/Semantics.lean` | `Arc`, `Netlist`, `WF`, `Run` (the semantics), `FixedRun`, `shift`; lemmas `arc_window` (BoundedDelay maps an input switching window [a,b] to [a+lo, b+hi]), `shift_bd` (a fixed delay is a BoundedDelay), `shift_changes`, `FixedRun.toRun`, `Run.node_changes`, `FixedRun.node_changes` |
| `Formal/Timing/Checker.lean` | `win` (topological table), `check`, `slack`; `win_eq` (table = recurrence), `changes_in_window` (window soundness), `check_sound`, `check_stable`, `win_early_attained`, `win_late_attained`, `win_exact`, `mixRun`, `check_exact_disjoint` |
| `Formal/Timing/CheckerToy.lean` | toy link: `#eval` windows/slack (pinned with `#guard_msgs`), `toyLink_check` / `toyShort_check` (by `decide`, kernel), `toyLink_bundled` (end-to-end), `toyShort_broken`; correlation: `corr_check`, `corr_fixed_safe`, `corr_bd_violation` |

### Main theorems (all hypotheses explicit)
- `changes_in_window (hwf : net.WF) (r : Run net sig) : ∀ v t, changes (sig v) t → ∃ e l, win net v = some (e,l) ∧ e ≤ t ∧ t ≤ l`
- `check_sound … (hc : check net req data setup = true) (r : Run net sig) : ∀ d ∈ data, ∀ s t, changes (sig d) s → changes (sig req) t → s + setup ≤ t`
- `check_stable`: under the same assumptions, data is stable on `[t+1-setup, ∞)` whenever req switches at `t`.
- `win_exact`: if the node is unreachable, it never switches in any run. If it is reachable, every switch lies in `[e,l]`, and there are fixed-delay runs that switch exactly at `e` and exactly at `l`.
- `check_exact_disjoint`: assume `Separated net P`, `P req = false`, `P d = true` on the data, req is reachable and `check = false`. Then some FixedRun has a data change at `s` and a req change at `t < s + setup`.
- `corr_fixed_safe` / `corr_bd_violation`: on `0→[1,3]→1`, `1→[5,5]→2` (req), `1→[4,4]→3` (data), setup 1, the check fails (7+1 > 6).
  - Every FixedRun is safe.
  - There is a `Run` in which node 1 glitches (it switches at 1, 2 and 3). Data then switches at 7, after req switches at 6.

## Modelling decisions (and why)

- **Event semantics or Prelim.BoundedDelay?** I used Prelim's `BoundedDelay` unchanged, on one pin trace per arc. This is the trace-level relation, so the result is about the shared gate model, not an STA-only abstraction.
  - The event view ("a transition at u at t arrives at v in [t+lo, t+hi]") is then a *derived* lemma (`arc_window`), which needs one more hypothesis, H_QUIESCENT (`pin 0 = src 0`).
  - Without H_QUIESCENT the channel can switch arbitrarily late: an output that starts out of agreement with its constant input may "correct" itself at any time ≤ hi. So H_QUIESCENT is needed, not a convenience.
- **Cells:** each cell gets one input-pin arc per pin, with delay `[lo,hi]`, and a zero-delay local Boolean function `g v` on the pin values (H_LOCAL, H_ZERO_DELAY_FN).
  - The theorems quantify over every local `g`, so every LUT function (`Formal.Cells.lutB`) is covered without restating it.
  - Feedback cells (C-element, latch) are NOT in this DAG model: the DAG covers the combinational/wire paths of one handshake phase.
- **H_LAUNCH:** node 0 switches at most once, at t=0. This means one token and one phase; multi-token interaction is out of scope.
- **Fixed and per-event delay:** `Run` allows the delay to differ per event and lets pulses pass. `FixedRun` uses one delay per arc per run, which is the "one PVT corner, one physical wire" reading and closer to how a real wire behaves within one corner.
  - Every FixedRun is a Run, so soundness holds for both.
  - Exactness differs (see the next section).

## Is interval STA exact? (the question asked)

- **Per node:** it is exact in both semantics (`win_exact`).
- **For the bundling check with no shared arcs between the req and data cones:** it is exact in both semantics (`check_exact_disjoint`). The toy link is in this case, because the 4 data bits share the G net, which is not a req arc.
- **For the bundling check with a shared arc on both paths (reconvergence/correlation):**
  - FixedRun: conservative. `corr` is rejected but safe in every fixed-delay run, which is exactly the common-path pessimism that CPPR removes.
  - H_BOUNDED_DELAY: on `corr` the rejection is *justified*. The shared node can glitch, req takes the early edge and data takes the late one. A pure bounded-delay channel transmits glitches, and that is what makes the pessimism real.
  - Physically, an inertial channel or a fixed-per-corner wire delay would filter it.

  So whether interval STA is "exact" is a question about the channel model, not about STA. For this fabric the honest answer is: conservative by the CPPR amount, unless runt or glitch propagation through a shared wire is credible.
- **Open (not proved):** a general theorem "under `Run`, the check is exact for every netlist".
  - It fails in corner cases in discrete time: a pin whose window has width 1 cannot switch at both ends and still settle to the source value, because that needs 3 changes.
  - So the general statement needs a width ≥ 2 side condition or real time. The example plus the disjoint-cone theorem are what is proved.
- **Not done:** a CPPR-aware checker. It would compute windows relative to the last common node and prove it exact for FixedRun. This is the natural next step, about 1 day.

## Toy netlist (illustrative numbers, NOT prjxray data)

- **Request path:** wire 60..180, delay element 480..650 (3 LUTs), wire 60..180, C-element LUT 40..60, wire 50..150 to the latch G.
- **Data path:** G net 50..150, latch G→Q 100..152 ×4, D wires 80..220 / 90..260 / 70..200 / 100..300.
- **Result:** setup 30. The earliest req is 690 and the latest data is 602, so slack is 58 ps and `check` = true.
- **Short delay element:** with 330..450 it is -92 ps, and `toyShort_broken` exhibits a real violating fixed-delay run.

## Fidelity of each primitive model

- **Wire/pip arcs:** BoundedDelay `[lo,hi]` per arc.
  - This is faithful when lo/hi come from prjxray's fast-min/slow-max for the pip and wire, as in `prjxray/prjxray/timing.py`.
  - It does not model RC sharing: a fanout's load changes the delay of all branches, which is another correlation.
  - It does not model pass-transistor pip slew dependence.
  - Test: GLS with SDF min/max corners.
- **LUT cell:** per-input-pin delay plus an instantaneous function, which is prjxray's per-pin LUT delay model.
  - It ignores input-to-input skew effects inside the mux tree, and Kleene/X behaviour. Use B's `lutK` for that; it is not needed for timing windows.
- **Pure (non-inertial) channel:** it passes every glitch. That is pessimistic for real LUTs and wires, which swallow runts below some width, and it is what makes `corr` really fail. Test: inject short pulses into a routed LUT chain in GLS or on the board.
- **H_QUIESCENT:** the circuit is at rest before each launch. In a four-phase link this holds when the previous phase settled (hi) before the launch, which is the property being checked in the previous phase.

## Effort to finish / what it buys

- **Importing real arcs:** feeding routed delays from nextpnr (the SDF/FASM route plus the prjxray timing db) into `Netlist` is a small Python exporter plus `decide` on the result. Kernel `decide` handled 15 nodes and 14 arcs instantly. For hundreds of arcs, the table recomputation in `win` is O(n²·arcs) in the kernel and will need a single-pass array version proved equal (about 0.5 day).
- **CPPR-exact version for FixedRun:** about 1 day.
- **Glitch-width (inertial) channel:** about 2 to 3 days, using A's `DelayInertial`.
- **What it buys:** a bundling check (rule E/A-style, "req after data") whose PASS is a theorem about every delay assignment inside the extracted intervals, and whose FAIL produces a witness run. Track 10b decides whether the project's rules match this check.
