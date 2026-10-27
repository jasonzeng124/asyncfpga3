# A-xaudit: a verified whole-design X/hazard audit executable (shard A, Phase 2 item A)

## Verdict

**Works for designs built from LUTs and routes, given an input stimulus. Blocked on gcd_hw.**

- `xaudit` reads a yosys `write_json` netlist, a band file and a stimulus. It reports every
  storage node (a LUT whose output is routed back to one of its own pins) that can see X or a
  hazard, with the time window. It uses two engines:
  - the timed X-window simulator `XSim`, sound for every delay inside the bands;
  - the untimed Eichelberger A/B (`Ternary`), sound for every delay at all.
- The functions it calls are the proved ones, or are proved equal to them. The parser and the
  report printer are trusted.
- It runs on real yosys JSON (all 11 cells of shard C's import) and on two hand-flattened
  multi-cell designs:
  - `pipe3`: bd_pipe W=2, N=3, the shipped defaults;
  - `ring3`: the tb_ring control ring.
- Results:
  - **pipe3 with one-corner bands: clean** (0 flagged).
  - **Hold-violation negative control: flagged** (stored X in all three latch stages).
  - **Slow own-feedback: flagged** (C-element glitches).
- **gcd_hw is not reachable here.** There is no toolchain in this container and no committed
  routed JSON. Even with them, four further pieces are missing (see "gcd_hw").

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Design.lean` | proved. `Design`/`GSpec`, `build`, the connection lemmas, the timed verdict theorems, `Stim` |
| `formal/lean/Formal/Core/XAudit/Untimed.lean` | proved. LutNet of a design, array A/B iteration = `Ternary.iterA/iterB`, verdict theorems |
| `formal/lean/Formal/Core/XAudit/Fast.lean` | proved. Array simulator `auditF` = `XSim.val` (`histF_spec`), fast verdict theorems |
| `formal/lean/Formal/Core/XAudit/Check.lean` | proved. `decide +kernel` cross-check of one verdict on the real `bd_c2.json` |
| `formal/lean/Formal/Core/XAudit/Main.lean` | compiles. The executable (parser, report): TRUSTED code, no theorems |
| `formal/lean/Wip/XAudit.lean` | 2 open statements (`sorry`): phase chaining (W1), FIFO precision (W2) |
| `formal/tools-A/xaudit/build.sh`, `lean.sh` | build the native exe without `lake build` (see below) |
| `formal/tools-A/xaudit/mkdesign.py` | hand flattening of `pipe3`/`ring3` (and `pipeN_W` for scaling) from cells/rtl |
| `formal/tools-A/xaudit/designs/*` | designs, stimuli, band files |
| `formal/tools-A/xaudit/run_all.sh`, `results/*.txt` | every run reported here |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Design.lean Formal/Core/XAudit/Untimed.lean \
      Formal/Core/XAudit/Fast.lean Formal/Core/XAudit/Check.lean Formal/Core/XAudit/Main.lean
    # -> [audit] 1053 declarations checked, [check] OK   (about 25 s)

- There is no sorry, admit, axiom, native_decide or bv_decide.
- The two kernel computations (`Check.design_wf`, `verdicts`, `q_X_at_36`, and the two window
  lemmas) use `decide +kernel`.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xaudit"
root = "Formal.Core.XAudit.Main"
```

`main` is the top-level `def main` at the end of `Main.lean`. After that, run
`lake exe xaudit NETLIST.json --stim S.json --bands B.json`.

Until then there are two ways to run it:
- `../slot.sh lake env lean --run Formal/Core/XAudit/Main.lean ARGS`. This is the interpreter,
  and needs the XAudit oleans, which `check.sh` writes. Its output equals the native one; I
  checked this on `bd_c2_kcheck` and `pipe3`.
- `formal/tools-A/xaudit/build.sh`, which builds a native binary at `$XAUDIT_OUT/xaudit`:
  - it re-elaborates the six proved dependencies and the XAudit modules with lake's module setup
    (package `formal`, via `--setup`) into a private olean dir;
  - it emits C with `lean -c` and links with `leanc`;
  - it never writes into `.lake/build`.

  Lake's own C for the dependencies could not be reused. `.lake/build/lib/lean/Formal/Core/XSim.olean`
  was evidently rebuilt by hand without the package setup, so its symbol names do not match
  lake's `XSim.c`. **Lead: a `lake build` will fix this. It is also why `[[lean_exe]]` is the
  real fix.**

### Usage

    xaudit NETLIST.json [--top T] [--bands B.json] [--stim S.json] [--xmax PS] [--all]
           [--emit-lean] [--kernel-sim | --crosscheck] [--timed-only]

**Bands** (all optional):
- `unit_ps` is the step; the default is 25.
- `lut` is the band of every LUT output, default [45,124] ps. This is 11b's prjxray LUT band.
- `route` is the band of every routed arc, default [100,700] ps. It is a placeholder that spans
  corners; it is not measured for any arc.
- `feedback` is the default for a LUT's own-feedback arcs.
- `cells{"cell" | "cell/O5"}` and `arcs{"cell/I3"}` override per gate and per arc.
- ps become steps as `lo = max(1, floor(lo/unit))` and `hi = ceil(hi/unit)`. A `lo` raised to 1
  step is listed in the report (a sub-unit delay is not modelled).

**Stimulus:**
- `init` and `events[{t_ps, set}]` set ports, `port[i]` bits or buses (an integer).
- A value may be `"x"`.
- `horizon_ps` is the length of the run.

## What the executable does and what is proved about it

**Parse (TRUSTED).** The yosys JSON becomes a `Design` with `m+1` wires and a list of `GSpec`s.
Each `GSpec` has an INIT number, pin wires, an output wire and `[lo, hi]` steps.
- Wire 0 is const0 and wire 1 is const1.
- Every non-constant LUT pin gets its own routed wire and a buffer gate (`k=1`, INIT `0b10`) from
  the driving net, with that arc's band. Wires are per-arc, so fanout branches are independent.
- LUT1..6 become one gate.
- LUT6_2 becomes two gates: O6 with `k=6` and the full INIT, and O5 with `k=5` and `INIT mod 2^32`
  on I0..I4. This is exact per UG474, including the O5 independence from I5.
- IBUF/OBUF/BUF are buffer gates with the `pad_steps` band, default [1,1].
- `$scopeinfo` is skipped.
- These are rejected loudly:
  - FDRE/FDCE/LDCE/SRL/BRAM/DSP: "clocked/hard storage; no clock, setup/hold model";
  - any other type: "unsupported";
  - two drivers on a net, an undriven net that is read, and x/z on a pin.
- `Design.wfB` (`decide d.WF`) is checked before any run. It checks pin count = `k`, indices in
  range, `1 ≤ lo ≤ hi` and `INIT < 2^2^k`.

**Connection lemma** (`Design.lean`):
- `toLGate_rel`: the `XSim` gate built from a `GSpec` relates its output wire to "INIT bit
  number `addr(values of the pin wires)`, through a Discrete transport channel `[lo, hi]`". This
  is literally the parsed cell.
- `sat_build_iff`: `Circuit.Sat (toCircuit (build d)) x ↔ ∀ g ∈ d.gates, (g.toLGate d).rel x`.

So the soundness theorems below are about the netlist as parsed. The only trusted step is the
parse itself.

### Timed engine (`XSim`)

- **Computed rows.** `audit d u T := XSim.hist (build d) u a0X T`, with power-up all X.
- **`audit_sound` / `audit_binary`.** Take every `x` with `Circuit.Sat (toCircuit (build d)) x`.
  That means every LUT, pad and route delay inside its band, as an arbitrary monotone warp, and
  any power-up state. If `x`'s primary inputs follow the stimulus (`InputsCovered`), every
  printed value covers `x`. A printed 0 or 1 is the value in every such behaviour.
- **Meaning of "no X reported at node `w` on `[t1,t2]`"** (`noX_sound`, `noX_deterministic`,
  and their fast versions `noXF_sound`): every behaviour has, at every step of `[t1,t2]`, the
  printed binary value. The waveform of `w` there is one fixed waveform, the same for every
  delay assignment in the bands. So `w` cannot glitch or see X there.
- **`settled_forever` / `settledF_forever`.** Suppose the inputs are constant from `T` and the
  last `maxHi+1` rows are equal. The report prints this as "FIXED POINT". Then every binary
  value of row `T` holds in every behaviour for all later time. The proof is via
  `XSim.val_stationary`.
- **Fast engine** (`Fast.lean`). `histF` keeps an `Array` driver table and `Array` rows.
  - `histF_spec`: entry `w` of row `s` is `XSim.val gs u a0 s w`, for every `s ≤ t`, given
    `1 ≤ lo ≤ hi`.
  - `auditF_eq` transfers every theorem above. The executable reads its timed verdicts from
    `auditF`.
  - `--kernel-sim` uses `audit` = `XSim.hist` itself. `--crosscheck` runs both: 0 mismatches
    over 112847 values on pipe3 (`results/pipe3_crosscheck.txt`).
  - Speed: pipe N=10 W=8 (361 wires, 2400 steps) takes 8.4 s against 26 s for `hist`. N=30 W=8
    (1061 wires) takes 19 s timed-only against 161 s for `hist` with the untimed part.
- **Classification (presentation only, TRUSTED).** Each maximal X run of a storage column is
  printed as one of:
  - power-up;
  - `transition p -> q`: `p ≠ q` and no longer than `--xmax`, default 2000 ps;
  - `POSSIBLE GLITCH`: `p = q`;
  - `STORED X POSSIBLE`: `p ≠ q` and longer than `--xmax`;
  - `UNRESOLVED` to the horizon.

  Only the X itself is a theorem. A "transition" window can still hide a glitch train inside
  it: X says "undetermined", nothing finer. Outside X windows the waveform is fixed.

### Untimed engine (`Ternary`, Eichelberger A/B)

- **The net.** `Untimed.toLutNet d (drvTable d)`:
  - node `w` is wire `w`;
  - a driven wire is the LUT of its parsed driver;
  - a pin on an undriven wire reads the input (`inl`), and a pin on a driven wire reads the
    node (`inr`).
- **`fb_driven`**: the node's Boolean function is INIT bit `addr(pins)` of its parsed driver.
- **`runA`/`runB`** are array iterations with an early stop at a fixed point. `runA_eq` and
  `runB_eq` prove them equal to `Ternary.iterA`/`iterB` after `n` steps (`iterF_eq`, `iterP_A`,
  `iterP_B`).
- **`soundA0` / `settleB0`** are Ternary's `soundA`/`settleB` generalised to a TERNARY start
  row. This is needed to start from the all-X power-up and to chain phases.
- **`untimed_noGlitch`.** Take every `Ternary.Causal` behaviour (any gate and wire delays,
  unbounded, a separate sample time per pin) whose inputs move, input by input, between `a`
  and `b`, and whose start state is covered by the start row. A storage node that A reports as
  binary `v` equals `v` at every time.
- **`untimed_settles`.** Add inputs equal to `b` from `T0` and bounded staleness `D`. Then a
  node that B reports as binary `v` equals `v` from `T0 + n·D`.
- **Phases.** The executable runs one phase per stimulus event group and starts each from the
  previous B row. **That chaining is NOT proved** (Wip W1): the per-phase theorems take "start
  state covered" as a hypothesis.

### Trust base

1. **The parser** (`Main.buildDesign`, `parseBands`, `parseStim`) and the report printer
   (`runs`, `classify`) are trusted.
2. **Compiled code trusts the Lean compiler, not the kernel.** The native binary and
   `lean --run` both execute compiled or interpreted definitions. Nothing in the run is
   kernel-checked.
   - Cross-check 1, kernel against binary: `Check.lean` re-runs `audit` on the design the
     binary emitted (`--emit-lean`) for the real yosys `bd_c2.json`, by `decide +kernel`, about
     7 s. The kernel agrees with every printed fact it checks:
     - q (wire 7) has no X on steps 10..33 and 40..43, i.e. 500..1650 ps and 2000..2150 ps;
     - it is 0 at step 20 and 1 at step 40;
     - it is X at step 36.

     `q_concrete` then states, for every behaviour of the parsed netlist: q = 0 on [10,33] and
     q = 1 on [40,43]. Expected values come from the cell (maj under rst = 0), not from the run.

     My first draft of this file said [39,43], from misreading the printed 1950 ps as the start
     of the 1-window. The kernel refused it (`decide` proved the conjunction false), and the
     binary was right.
   - Cross-check 2: the two compiled engines `audit` and `auditF` agree value for value on
     pipe3.
   - The interpreter output equals the native output.
3. **`--emit-lean` is trusted printing** of the parsed design. The Lean literal in `Check.lean`
   is that output.

## Results

All results are in `formal/tools-A/xaudit/results/`. Steps are 25 ps unless the band file sets
`unit_ps`.

### Parse smoke test: all 11 cells of shard C's import

- Every cell parses with no stimulus: LUT6, LUT6_2 pairs, IBUF/OBUF pads, the arbiter's three
  loops. Inputs are X.
- Storage nodes found:
  - c2, c2_set, c2n, c2n_set, c3, c4: 1 each;
  - latch W2: 2;
  - latch W3: 3;
  - latch_rst W1: 1;
  - arbcell: 1;
  - arbiter: 3 (q, A1, A2).
- The arbiter count matches `bd_arb.v`'s "three loops".

### bd_c2, real yosys JSON, four-phase (`bd_c2_default.txt`, default bands)

- Clean. q is X on [0,850] ps (power-up and reset), then on [4150,4825] for 0→1 and on
  [8150,8825] for 1→0. It reaches a FIXED POINT.
- I derived the windows by hand before the run, for b↑ at 4000:
  - the pad gives +25;
  - the route gives [100,700] → [4,28] steps;
  - the LUT gives [45,124] → [1,5] steps;
  - so X lies on [4000+150, 4000+825] ps, matching the run.
- Untimed: every phase is clean. Single-input changes are hazard-free (Ternary's
  `bdc2_single_input_ok`, now on the parsed netlist).

### pipe3: bd_pipe W=2 N=3 (11 LUT outputs, 29 routed arcs, 9 storage nodes)

The stimulus is two four-phase tokens, data 1 then 2. Data is held until ack_in falls, per
bd_link.v.

- **One-corner bands** (`slow_corner.bands.json`: LUT [99,121], route [360,440], own feedback
  [270,330] ps, 10 ps steps; ILLUSTRATIVE ±10% around a nominal, not measured per arc):
  **0 flagged.**
  - Every C-element and latch transition has a bounded X window, for example c0↑ X on
    [3450,3560]. This matches req↑ at 3000 + [360,440] route + [99,121] LUT.
  - The latch outputs carry token 1 = 01, then token 2 = 10, at all three stages. This matches
    data_in, not the run.
  - FIXED POINT at the end.
- **Negative control: hold violation** (`pipe3_holdviol.stim.json`: data changes at 5450 ps,
  while stage 0 closes):
  - **10 flagged.** Stage 0's latch shows `1 -> X -> 1` possible glitches, then
    `STORED X POSSIBLE` on [6620,13130]. The X is written into stages 1 and 2 as well.
  - A sweep of the data-change time agrees with a hand bound, `t + 360 > 5570 + 440`, i.e.
    t > 5650:
    - 5450, 5500, 5550 and 5600 ps are flagged;
    - 5700 ps is clean.
  - The defect (the injected race) is larger than the band. The control would fail if the audit
    missed it.
- **Slow own-feedback** (`slowfb.bands.json`: feedback [1300,1500] ps, longer than the next
  stage's fastest response, 3×360+2×99 = 1278 ps): **22 flagged.**
  - Example: c0 `1 -> X -> 1` POSSIBLE GLITCH on [4800,5190], then UNRESOLVED.
  - This is real in the model:
    1. c0 rises;
    2. c1 answers through r1 before c0's own feedback reaches I2;
    3. the LUT then sees a = b = 1 with q_pin still 0, holds 0, and c0 falls back.
- **Default bands** (corner-mixing [100,700] routes): the C-elements go X from the first
  request (9 flagged), for the same reason. The fastest neighbour response is 390 ps, against an
  own feedback of up to 700 ps.
- **Untimed** (any delays): each C-element is NO SETTLE at `req_in+`. Under the `Causal` model
  the own-feedback pin can be arbitrarily stale, which is the slow-feedback race again. So
  bd_link's Muller pipe is not delay-insensitive. Its LUT C-elements need the relative-timing
  assumption **own feedback < fastest neighbour response**. The timed engine checks that
  assumption against bands.
  - With one-corner ±10% bands it holds by 330 against 1278 ps. With corner-mixed bands it does
    not.
  - I did not find this obligation as an explicit rule in `cells/verify/tighten.py`. Rule L
    covers the latch feedback, not the C-element against its neighbour. Recommendation: B/C
    should state it as a cell constraint and check it on real per-corner arcs.

### ring3: tb_ring N=3 K=1, free running (`ring3_slow_corner.txt`)

- The audit flags all three nodes UNRESOLVED from about 5.2 ns, after about one lap.
- **This is imprecision, not a hazard.** A scratch Python transport simulation with 200 random
  fixed delay assignments in the same bands shows no runt pulse or stall. The scratch file is
  not committed.
- Cause:
  - XSim is proved sound for the non-FIFO window channel `WinCh`. Inside a window that channel
    may show any mix of old and new samples, and it is exact per gate for `WinCh` (`win_exact`).
  - In a free-running loop the windows grow every lap and the loop then latches the X.
  - Open-loop designs re-synchronise with the stimulus at every handshake, so the pipe is
    unaffected.
- Fix: a FIFO/transport-aware domain (Wip W2).

### gcd_hw: blocked

What blocks it, in order:

1. **No routed netlist here.**
   - The routed-GLS result (research JOURNAL "progress 21:20", routed.json md5 13643a10) is a
     build artifact and not committed. `git show origin/claude/research:cells/hw/` has
     `gcd_hw.v` and `gcd_hw_pads.json`, but no routed JSON.
   - This container has no toolchain: `~/dev2/lib/fpgatoolchain` is absent, and there is no
     yosys and no nextpnr. So it cannot be rebuilt.
   - The rebuild once a toolchain is present: `cd cells && BDC_SELECT_PADS=hw/gcd_hw_pads.json
     BD_RLOC=v4 ./hw/build_hw.sh gcd_hw`, then `cells/verify/toolchain.sh` and 4 seeds.
2. **Primitives.**
   - gcd_hw has a clocked instrumentation shell (15 `always @(posedge`, BSCANE2, 5 BUFG). The
     JOURNAL also lists 21 CARRY4 and 35 MUXF7 in the datapath.
   - Plan:
     - cut the shell at the rig's ports: FF outputs become stimulus inputs, FF D pins become
       observed;
     - model MUXF7/F8 as a LUT3 `S ? I1 : I0`;
     - model CARRY4 as 4 MUXCY (LUT3) + 4 XORCY (LUT2) gates with their internal bands.

     About 0.5 day.
3. **Per-arc bands from the route.**
   - nextpnr's routed JSON has per-net `ROUTING` pip lists.
   - The per-pip/pin delays exist in 11b's prjxray `pinDelay`/fasm2lean and in the research
     branch's `xray_delay.py`.
   - A converter to the `arcs{"cell/Ii": [lo,hi]}` band file, per corner, is about 1 day.
   - Also record the nextpnr patch set and fingerprint (CLAUDE.md).
4. **Scale and precision.**
   - gcd_hw has 1112 LUTs, so about 6000 wires once arcs are split. `auditF` costs about 8 µs
     per wire-step, so 1 µs at 10 ps steps takes about 80 min.
   - Possible improvements:
     - sliding-window or event-driven evaluation, a refinement proof like `histF_spec`: 1-2 days;
     - coarser steps;
     - one vector per run.
   - Worse, the gcd rig is a FREE-RUNNING self-timed loop (millions of laps). The window domain
     loses phase after about one lap (ring3), so it would report UNRESOLVED everywhere.
   - That needs W2 (FIFO-aware domain, 2-4 days) or a per-lap re-synchronisation argument.
     W2 is the real blocker for whole kernels, more than the toolchain.

## What is not proved, and why

- **W1, phase chaining for the untimed engine.** See `Wip/XAudit.lean` `chain_phases`. Needs a
  "covered window" variant of `sound_postfix` under `Stale`. About 0.5 day.
- **W2, a FIFO-aware abstract domain.** About 2-4 days; it is the precision fix for loops.
- **The parser.** It is trusted by design. A cheap mitigation: `--emit-lean` plus a `decide`
  that `build` of the emitted literal has the same gate count, INITs and pin wires as shard C's
  `Formal.Net.Import` netlist for the same JSON. About 0.5 day.
- **The classification of X windows** into transition, glitch or stored X is presentation, not
  a theorem.

## Fidelity (gate-fidelity rule)

| primitive / assumption | model | status | how to test |
|---|---|---|---|
| LUTk output, binary pins | INIT bit `addr(pins)`, I0 = LSB (`toLGate_rel`) | exact (UG474) | GLS with unisim LUT6 |
| LUT under X pins | `Lut.keval` mux tree (Kleene). For the untimed engine, `Ternary.kext` | hypothesis H_KLEENE_LUT (A-kleene-lut) | board: toggle a pin with equal cofactors, look for runts with a TDC |
| LUT6_2 | O6 = 6-input, O5 = INIT[31:0] on I0..I4; two independent gates on shared pins | exact functionally; delays independent per output | GLS |
| LUT delay | transport `[lo,hi]` monotone warp per output (soundness is for the weaker `WinCh`) | the band is an input; no inertial filtering is modelled, which is sound (it only removes behaviours) | GLS min/max SDF; board TDC |
| routed arc | own `Lut 1` buffer and band per (net, sink pin) | faithful to per-sink routing; bands from the user | prjxray per-pip delays (11b) |
| pads | buffer, `pad_steps` band, default 1 step | not faithful; pads exist only when a cell is synthesized as top | not needed for inner designs |
| time | 1 step = `unit_ps`. `lo` is rounded down (but at least 1) and `hi` up, so the bands widen and stay sound for the widened band. A sub-step `lo` raised to 1 is listed | discretisation as in A-discretize | — |
| power-up | all driven wires X | sound (covers any power-up state) | — |
| FFs, BRAM, DSP, CARRY4, MUXF7/8 | rejected loudly | not modelled | — |
| metastability | X means "either level, or in transit"; no M value | out of scope (arbiters) | — |
| untimed delays | `Ternary.Causal`: any staleness per pin, including the own feedback | the weakest causal model; this is why LUT C-elements in pipes come out NO SETTLE | — |

## What it buys the project

- **One command per design and stimulus**, with a stated theorem behind every clean verdict:
  - no X on node `w` in `[t1,t2]` ⇒ the same binary waveform in every behaviour with delays in
    the bands;
  - FIXED POINT ⇒ the values hold for all later time.
- **Precise flags.** The pipe's hold rule (H) and the C-element feedback-vs-neighbour race
  appear as concrete flagged windows on concrete nodes. The one-corner run is clean.
- **Scale.** The proved fast engine handles about 10^3 wires today. The design-size path to
  gcd_hw is engineering (items 2-3 above). The loop-precision path (W2) is research.

## Effort to finish

| item | estimate |
|---|---|
| `[[lean_exe]]` stanza | lead, 1 min |
| W1, phase chaining | 0.5 day |
| CARRY4/MUXF7/F8 and the FF cut | 0.5 day |
| route → per-arc band converter (prjxray, per corner) | 1 day |
| event-driven `auditF` with a refinement proof | 1-2 days |
| W2, FIFO-aware domain for free-running loops | 2-4 days |
| parser cross-check against `Formal.Net.Import` | 0.5 day |
