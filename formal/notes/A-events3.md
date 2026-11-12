# A-events3: shared parser, the `xevents2` executable, and choice (E5) in the event-count domain (shard A)

## Verdict

| task | verdict |
|---|---|
| (1) parser factored into `Parse.lean` | **Done.** Outputs are byte-identical before and after on 11 runs (8 xaudit, 3 xevents) |
| (2) `xevents2` executable | **Works.** On pipe3 and ring3 it reproduces A-events2's hand-written certificates and margins number for number, found automatically. It refuses what is outside the domain (`bd_arbiter`) and fails its negative controls |
| (3) E5, choice | **Works for reconverging choice** (steer → two arms → exclusive OR merge, i.e. an if-then-else inside a loop), proved for every select sequence. It is **not yet done for the mux's merge of two different sources or for loop entry/exit**; those are shapes in `Wip/Events3.lean`. My estimate for the rest of gcd's loop control is 3-4 days |

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Parse.lean` | new, TRUSTED code (no theorems, no `main`): the yosys-JSON parser, moved verbatim from `Main.lean` |
| `formal/lean/Formal/Core/XAudit/Main.lean` | edited: the parser copy removed, `import`/`open` of `Parse` added, one docstring line. Behaviour unchanged |
| `formal/lean/Formal/Core/XAudit/EventsMain.lean` | edited the same way |
| `formal/lean/Formal/Core/XAudit/Events2Main.lean` | new: proved verdict theorem `sound` (+ `env_rel`, `sat_close`) and the TRUSTED executable `xevents2` |
| `formal/lean/Formal/Core/XAudit/Events3.lean` | new, proved: `filt`, `filt_add`, `steer_val`, `or_val`, `fsum_le_max`, `min_le_fsum`, `steer_neg`, `or_neg`, `Choice`, `Bands3`, `ChoiceOK`, `Skew`, `Beh3`, `M`, `M_mono`, `P_le`, `walk_le`, `cycle_le`, `pin_le_q`, `arms_close`, `SelOK`, **`Beh3.safe`** |
| `formal/lean/Formal/Core/XAudit/Events3Ring.lean` | new, proved: **`ring_safe`** (ring3 with an if-then-else on the 1→2 request), `backOK`, `choiceOK`, `skewOK`, `crit_ok`, controls `skew_neg`, `slowfb_neg` |
| `formal/lean/Wip/Events3.lean` | new, open shapes (`sorry`): W-E5a merge (mux), W-E5b per-arm skew, W-E5c netlist link, W-E5d loop entry/exit, W-E5e arbiter |
| `formal/tools-A/xaudit/events3/run_xevents2.sh` | builds private oleans (via `../lean.sh`, no `lake build`) and runs `xevents2` on the designs and cells |
| `formal/tools-A/xaudit/events3/*.txt` | `xevents2` outputs (pipe3, ring3, negative controls, single cells) |
| `formal/tools-A/xaudit/events3/choice_sim.py`, `choice_sim.txt` | random gate-level transport simulation of the E5 instance (evidence only) |

### Check

Each command is run from `formal/lean`:

    ../check.sh Formal/Core/XAudit/Parse.lean Formal/Core/XAudit/Main.lean
    #   -> [audit] 1050 declarations checked, [check] OK
    ../check.sh Formal/Core/XAudit/Parse.lean Formal/Core/XAudit/EventsMain.lean
    #   -> [audit] 893 declarations checked, [check] OK
    ../check.sh Formal/Core/XAudit/Parse.lean Formal/Core/XAudit/Events2.lean \
      Formal/Core/XAudit/Events2Time.lean Formal/Core/XAudit/Events2Design.lean \
      Formal/Core/XAudit/Events2Main.lean
    #   -> [audit] 1281 declarations checked, [check] OK
    ../check.sh Formal/Core/XAudit/Events2.lean Formal/Core/XAudit/Events2Time.lean \
      Formal/Core/XAudit/Events3.lean Formal/Core/XAudit/Events3Ring.lean
    #   -> [audit] 430 declarations checked, [check] OK

- None of these files contains sorry, admit, axiom, native_decide or bv_decide.
- The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- Instance facts are checked with `decide +kernel`.
- Events2/Events2Time/Events2Design appear in the lists only because they are not in
  `.lake/build`; I did not edit them.

**Note for the lead.** The three executables cannot be audited in ONE `check.sh` call: each
defines a top-level `main`, so the audit file's imports clash ("environment already contains
'main'"). That is why they are checked separately above.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xevents2"
root = "Formal.Core.XAudit.Events2Main"
```

Usage: `xevents2 NETLIST.json [--top T] [--bands B.json] [--env LO:HI] [--cap N]`.
- `--env` is the environment's answer band in ps. The default is `0:500`; the lower end is
  raised to 1 step.
- `--cap` bounds the walk and cycle enumeration. The default is 4096; the report says CAPPED
  when the limit is hit.

Until the stanza exists, run `formal/tools-A/xaudit/events3/run_xevents2.sh`. It uses the
interpreter on private oleans in `/tmp/xevents2/olean`.

`Parse` needs no stanza. The `xaudit` and `xevents` builds pick it up as a dependency.

## (1) The parser refactor

- **What moved.** `Parse.lean` holds, verbatim, the helpers, `Bit`, `Bands`, `toSteps`,
  `GInfo`, `Built`, `St`, `M`, `buildDesign`, `getArg`, `readJson` and `pickTop`, under
  `namespace Formal.Core.XAudit.Parse`. The stimulus parser, `emitLean` and the report stay in
  `Main.lean`; they are xaudit-specific.
- **How it was tested (by the brief's method).**
  1. Before the edit, I ran `lake env lean --run` on `Main.lean` and `EventsMain.lean` over
     11 runs:
     - xaudit: pipe3 slow corner; pipe3 hold violation; pipe3 `--emit-lean`; ring3; ring3
       `--emit-lean`; `bd_c2` with stimulus; `bd_c3`; `bd_latch_W2`;
     - xevents: ring3 slow corner; ring3 slowfb; pipe3.
  2. After the edit, I re-ran the same 11, with `Parse` from a private olean.
  3. `diff -r` of the two output directories (stdout, stderr and exit code) is empty.
- The runs were scratch files in `/tmp/xevents2/{before,after}` and the script
  `/tmp/xevents2/runs.sh`.

## (2) `xevents2`

### What it does

**Recognises** (trusted code; everything it proposes is re-checked):
- **C-element stages.**
  - A stage is any LUT6 with a pin buffered from its own output.
  - Its arity `n` is the index of that pin.
  - Pins above `I(n+1)` must be tied to 0.
  - A `(reset value, bubble mask)` pair must pass `InitOK` (the E4 cell check, run over 64
    addresses).
  - So `bd_c2`, `bd_c2_set`, `bd_c2n`, `bd_c2n_set`, `bd_c3` and `bd_c4` are all found from
    their INITs, with no table of names. Latches and the arbiter's state LUT are reported as
    storage outside the control domain.
- **Pins.**
  - Each pin is traced back through 1-input buffers and inverters (routes, `bd_delay` LUT1s)
    to a stage output or an input port.
  - Anything else is refused, naming the gate: "not a 1-input buffer/inverter and not a
    C-element stage (choice, datapath …: E5/E6)".
- **The environment** (E2, now automatic).
  - An input port read by exactly one control pin gets an eager handshake partner of that
    stage: a 1-input gate from the stage's output to the port.
  - The gate inverts iff the pin, after chain parity and bubble, must read the opposite of
    the stage's output. This is A-events2's `envS`/`envR`, found automatically.
  - A port read by two control pins, or the reset port, is refused.
- **Back walks.** For each pin, it picks the simple upstream walk back to the stage, with at
  most `1 − off` tokens, that has the largest fastest traversal. The environment pins use the
  empty walk.
- **Certificates** (E3), by a Lean port of `cert.py`:
  - per-window bounds from the best closed walk through each stage;
  - the long-run UPPER rate (`σ`, `ρ`: tree into the max lo-ratio cycle);
  - the long-run LOWER rate (`π` by Bellman–Ford at the max hi-ratio).

**Checks** (compiled `Decidable` instances of the proved propositions): `Recog2` on the netlist
closed by the environment gates, `Back`, `EnvOK`, `walkOK`, `UpCert` and `LoCert`.

**Prints:**
- per-stage verdicts;
- per-pin Back margins;
- for environment pins, the **boundary margin** split as "port route vs own feedback" plus
  "the environment's minimum answer";
- the period bounds;
- a VERDICT line that names the environment hypothesis.

### What is proved about it

`Events2Main.sound`:
- **Hypotheses.** If
  - `Recog2 (close d env) net sm`,
  - `Back sm.bands back`, and
  - every environment gate satisfies `EnvOK`,

  then the theorem applies to every `Circuit.Sat` behaviour of the parsed netlist `d` in which
  each environment port is a transport channel from its stage in a sub-band of `[g.lo, g.hi]`
  (`henv`, the stated environment hypothesis).
- **Conclusion.** There is ONE count `M` such that:
  - (a) every C-element output is `ph v (M t j)` at every time;
  - (b) every closed walk gives the per-window bound;
  - (c) every `UpCert` and `LoCert` gives the long-run rates.
- **What this means for the printed bounds.** The printed bounds are instances of (b) and (c)
  for the printed certificates. Each certificate was re-checked by `decide` in the same run.

### Results (slow-corner ILLUSTRATIVE bands, `events3/*.txt`)

| run | verdict | matches |
|---|---|---|
| pipe3, env [10, 500] ps | CLEAN FOREVER; Back margins 930 ps (internal), **30 ps + env min** (both ports); 1 event per 1350 ps per window; upper ρ = [180, 90, 0] (T' = 135); lower π = [0, 114, 228] (T = 171) | exactly `Events2Pipe3.backOK50`, `up50`, `lo50`, `crit_ok` and the notes' 930 ps / 30 ps finding |
| pipe3, env [10 ps, 0.1 s] | CLEAN FOREVER (safety); lower rate degrades to the environment (1 per 10^10 ps) | `pipe3_safe` |
| ring3 | CLEAN FOREVER; margins 480/930 ps; 1 per 1350 ps window; lower π = [57, 0, 114], T = 171 | `Events2Ring3.lo_cert`, `crit_ok`; A-events' `[135, 171]` |
| **pipe3 slowfb (NEG)** | NOT PROVED, exit 1: margins −1130 ps (ports), −240 ps (internal) | `Events2Pipe3.slowfb_neg` |
| **ring3 slowfb (NEG)** | NOT PROVED, exit 1 | A-events |
| cells `bd_c2`, `bd_c2n_set`, `bd_c3`, `bd_c4` (each closed by its environment) | CLEAN FOREVER; 2-, 3- and 4-input stages found from the INIT; boundary margin 40 ps + env min | `cells_ok` |
| cell `bd_latch_W2` | no control: the latch LUT is reported as storage outside the domain | — |
| cell `bd_arbiter` (NEG, out of domain) | NOT RECOGNISED, exit 3: the grant LUTs are not chains (E5); `A0` is read by two control pins | — |

- **Run time.** About 4 s per design in the interpreter.
- **Trusted part.** The parser, the recogniser, the certificate search and the printing. A
  wrong recognition or search can only produce NOT PROVED, never a false CLEAN, because
  `sound`'s hypotheses are decided on exactly the objects printed. This relies on the
  compiler agreeing with the kernel, as for xaudit.

## (3) E5: choice in the event-count domain

### The abstraction

- **The select is an environment choice.**
  - `sel : Nat → Bool` gives the branch of each 4-phase transaction of the steered request.
  - Every theorem holds for every `sel`.
  - Choice is not resolved by the analysis. It is quantified over.
- **Per-branch counters.**
  - Arm `b` after the steer has fired `filt sel b m` times when the request has fired `m`
    times.
  - **Conservation** (`filt_add`): `filt sel false m + filt sel true m = m`. Every event goes
    down exactly one arm.
- **The steer is exact on counts** (`steer_val`).
  - Statement: `ph x ∧ [s = b] = ph (filt sel b x)`, PROVIDED the select seen by the AND gate
    is `sel (x/2)` while the request is high.
  - That proviso is the **bundling hypothesis** `SelOK`. It is a named hypothesis and is never
    derived here; discharging it is E6.
  - Return to zero needs no hypothesis, which is LIBRARY.md's argument for `bd_steer`, now as a
    lemma.
- **The exclusive merge is a sum** (`or_val`): `ph(filt₀ x₀) ∨ ph(filt₁ x₁) = ph(filt₀ x₀ +
  filt₁ x₁)` whenever `|x₀ − x₁| ≤ 1`.
- **A choice pin is a channel with two arms.**
  - Its count is `filt₀(M_src(G₀ s)) + filt₁(M_src(G₁ s))`.
  - That count lies between the source's counts at the two arm sample times (`fsum_le_max`,
    `min_le_fsum`).
  - So the min-plus recursion stays monotone. Walks, `Back` and `cycle_le` of Events2 go
    through unchanged with the merged band `[min lo, max hi]`.
- **Exclusivity is a timing condition** (`Skew`).
  - Each choice pin needs a closed walk through the steered source, with at most one token,
    whose fastest traversal covers the arm skew `max hi − min lo`.
  - Then the source fires at most once inside the skew window (`cycle_le`), so
    `|x₀ − x₁| ≤ 1` (`arms_close`).
  - This holds for the recursion, before any safety argument, so there is no circularity.
- **`Beh3.safe`.**
  - Hypotheses: `Back` (merged bands), `ChoiceOK` (a steered source is a 4-phase request with
    reset 0), `Skew` and `SelOK`.
  - Conclusion: every node of every behaviour equals its reset value flipped `M t j` times at
    every time.
  - So there is no X, no glitch, and no lost or duplicated token, whatever the select sequence.

### The instance (`Events3Ring.ring_safe`)

- **Circuit.** ring3, with stage 1's request to stage 2 steered into a then-arm and an
  else-arm and merged by an OR: an if-then-else body inside a loop.
- **Arm bands** (route → AND LUT → route → OR LUT → route):
  - then-arm: [126, 158] steps;
  - else-arm: [171, 215] steps (one `bd_delay` LUT1 + route more).
- **Checks.**
  - `Back` holds, with margins as in ring3.
  - `Skew` holds: skew 89 steps against the one-token cycle 1 → 2 → 1 of 180 steps.
- **Result.** For every `sel` and every behaviour with `SelOK`:
  - all three stages are `ph v (M t j)` for ever;
  - at most one event per 135 steps in every window;
  - the per-branch counts conserve stage 1's count.

### Negative controls

- **Lean, primitives.** These show that the two lemmas' hypotheses are needed.
  - `steer_neg`: the select changes while the request is high, so the AND raises the wrong arm.
  - `or_neg`: the arms are two events apart, so both are high and the OR loses a token.
- **Lean, instance.**
  - `slowfb_neg`: `Back` fails with slow feedback.
  - `skew_neg`: `Skew` rejects an else-arm with three delay stages (skew 203 > 180).
- **Simulation** (`choice_sim.py`, random gate-level transport delays, random select; 50 runs
  each). Five checks come from what is proved:
  - the ring firing order;
  - the arm event counts against `filt`;
  - the arms never both high;
  - the OR count equal to the source count;
  - a minimum same-stage gap of at least 135.

  | case | runs violating |
  |---|---|
  | bundled select, 1 delay stage | **0/50** (min gap 176 ≥ 135) |
  | select changes 60 steps after the rise, while the AND sees the request high | **50/50** (glitches, lost tokens, both arms high) |
  | select changes 20 steps after the rise (before the AND sees the rise: still bundled) | 0/50, as `SelOK` predicts |
  | slow feedback [130, 150] | **50/50** |
  | else-arm with 3 delay stages | **0/50** |

  The last row shows that **`Skew` is conservative** here:
  - in this ring the source cannot fire again until the slow arm's event has reached stage 2,
    so the arms never collide whatever their skew;
  - `Skew` cannot see that, because it uses the merged band and not per-arm causality;
  - `skew_neg` therefore shows that the check can fail, not that this circuit fails;
  - the precision fix is W-E5b.

### What it does not do

| item | what | estimate |
|---|---|---|
| W-E5a | **the mux's merge of two different sources** (`bd_mux`: `j_b = C(src_b, ctl·[s=b])`, `z_req = Δ(j0 + j1)`). The joins are already Events3 choice pins (steered `ctl`). The OR of two different C-elements needs a "merge" pin kind with count `M_j0 + M_j1`. Exclusivity would come from conservation against `ctl` (`M_j0 + M_j1 ≤ M_ctl` via `filt_add`) instead of `Skew`. The dual operator `unfilt` is drafted in Wip | 1.5 days |
| W-E5b | per-arm `Skew` (precision; would accept the 3-stage else-arm) | 1 day |
| W-E5c | netlist link: recognise `bd_steer` (LUT6_2 `0x8888888822222222`) and the OR (LUT2 `0xE`), compose arms with `chain_warp`-style lemmas, prove `design_beh3`, extend `xevents2` | 1 day |
| W-E5d | loop entry/exit (the token leaves to and enters from the environment), with E2's environment channels and W-E5a | 1 day |
| W-E5e | the arbiter: `sel` decided by arbitration; `SelOK` replaced by grant exclusivity (shard B's models) | research |
| E6 | discharging `SelOK` (select = channel data held from `req↑` to `ack↓`) | 2-3 days (unchanged) |

**What gcd's loop control still needs.**
- The exit branch is a steer, which is in the domain once W-E5c and W-E5d are done.
- The header mux is W-E5a plus W-E5d.
- The if-then-else of the body (`a > b ? a − b : b − a`) is exactly `ring_safe`'s shape.

## Fidelity

These items are in addition to A-events2's table, which still applies.

| item | model | status | test |
|---|---|---|---|
| steer | AND of the request pin and `[s = b]`, per arm, after transport channels (`hpin`). For `bd_steer`'s fractured LUT6_2 this is UG474-exact for O5/O6 | exact for the LUT function; the per-arm composite warp is the same FIFO hypothesis as every arc | GLS of `bd_steer` with a select that moves while `req` is low |
| select | an arbitrary sequence `sel`; **hypothesis** `SelOK`: while the request seen by an arm's AND is high, the select seen there is that transaction's branch | hypothesis (bundling). The simulation shows the conclusion fails without it (50/50) | GLS at both corners: the select's route must reach the steer's LUT before the request does, and change only after the request's fall has arrived there. This is a bdc/route gate of the same kind as `Race` |
| merge OR | LUT2 `0xE`, transport; exclusive by `Skew` | exact function; `Skew` is a checked inequality, sufficient and here conservative | GLS with arm delays near the skew bound; board: an if-else loop with a long else arm |
| environment (xevents2) | eager handshake partner per port, band `--env` | hypothesis (as in A-events2), now printed in every verdict | rig: synchronised FSM, `elo` ≥ one clock |
| bands | illustrative slow corner (±10 %) | not measured | per-arc prjxray bands of a real route |

## Effort and what it buys

**Effort.** About 3.5 h in total:
- 30 min for the refactor and its byte-identical test;
- 1 h for `xevents2`;
- 2 h for E5 (domain, instance, simulation).

**What it buys:**
- **One parser.** Every executable now shares one trusted parser.
- **`xevents2`.** A push-button, proof-backed, all-time verdict for open bundled-data control
  built from C-elements and delay lines, with the environment inferred. It prints the
  **open-boundary race** (`hiQ ≤ elo + loG(port route)`) per port. On the illustrative bands
  that is 30-40 ps plus the environment's minimum answer time; it should become a bdc/route
  gate.
- **The first data-dependent control in the counter domain.** Proved for every select
  sequence, it rests on three ideas:
  - per-branch counters with conservation;
  - the steer as an exact count filter under the bundling hypothesis;
  - the exclusive merge as a sum, with exclusivity reduced to a checkable cycle-versus-skew
    inequality.

  It turns E5 from "research" into three named engineering items (W-E5a/c/d, about 3.5 days),
  with E6 discharging the select hypothesis.
