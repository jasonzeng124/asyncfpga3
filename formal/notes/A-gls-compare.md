# A-gls-compare: the formal model against the research branch's board-fidelity GLS

Probe: PROGRAM.md, "Compare the model with the board-fidelity GLS being built on
claude/research. Where the two disagree, find out which is wrong."

I ran the GLS's own primitive models from `origin/claude/research:cells/gls/prims.v`
(`SLICE_LUTX`, `SELMUX2_1`, `ICBUF`). I copied them read-only to `/tmp/gls-compare/prims.v`;
nothing in `cells/` was touched. The simulator was iverilog 12.0 with `-gspecify`, as `build.sh` uses.
The testbenches are tiny and use the exact build flags of the two GLS images:
- `gate.vvp`: annotated, with ICBUF as a specify path;
- `run_baked.vvp`: `-DGLS_TRANSPORT_IC`, with ICBUF as a transport assignment.

No Lean was written. The lemmas the findings suggest are listed in §5.

## Files (all in `formal/tools-A/gls-compare/`)

| file | what |
|---|---|
| `tb_runt.v` | runt sweep, w = 1..400 ps, through 1 LUT and a 2-LUT chain (direct, or with a 300 ps ICBUF), plus a two-pulse (w, gap) grid. Reference LUTs: `LUT_TR` (transport), `LUT_RF` (rise 56 / fall 124) |
| `tb_c2.v` | `bd_c2` (INIT `64'h00E8_00E8_00E8_00E8`, q→A3, rst→A4): every stable state × every single-input flip, then a,b 01→10 with skew s = −300..+300 ps at 1 ps steps, for q0 = 0 and q0 = 1. Variants: per-pin arcs, a feedback ICBUF, and a transport LUT (`LUT_TRC`) |
| `tb_c2_saf.v` | minimal demo: a 6 ps a/b overlap latches `bd_c2` if a 5 ps glitch happened 120 ps earlier |
| `channel_fit.py` | random edge traces → GLS LUT; scores each candidate channel model by exact match of the output event list |
| `tb_kleene.v`, `kleene_check.py` | all 3^6 {0,1,x} vectors into `SLICE_LUTX` (O6 and O5) for 30 INITs (the 15 library cells of `Core/Lut.lean`, plus zero, ones, xor6 and 12 random), and all 27 vectors into `SELMUX2_1`, compared with Lean's `Lut.kevalSpec` / `kmux` |
| `run_all.sh` | reproduces everything (about 3 min): `sh run_all.sh /tmp/gls-compare/prims.v /tmp/gls-compare` |

## 1. The headline: the GLS LUT is neither inertial nor transport. It is "sample at fire" (SAF)

The prims.v header, `research/PROGRAM.md` ("module-path (inertial) delays, which swallow narrow
pulses") and this repo's `A-delay-inertial.md` all describe iverilog's specify path as an
inertial delay. **It is not.** The behaviour is the following:

> **SAF channel.** Every change of the LUT's zero-time function `f` at time `t` schedules an
> update at `t + d`. Here `d` is the arc of the pin that changed, and the rise or fall value
> chosen by the new value of `f`. When the update fires, the output copies **the value `f` has
> at the fire time**. Nothing is ever cancelled.

`channel_fit.py` checked this against random traces. It counts exact matches of the whole
output event list, out of 140 traces:

| config | transport | inertial (Lean `InertialRD d d`, ties pass) | SAF |
|---|---|---|---|
| 1 pin, d = 124 (the GLS default) | 2/60 | 20/60 | **60/60** |
| XOR, A1 arc 100 / A2 arc 150 | 0/40 | 13/40 | **40/40** |
| rise 56 / fall 124 (the `cells/sim/bd_prims_sim.v` arcs) | 2/40 | 15/40 | **40/40** |

SAF and inertial agree on any isolated pulse, so both give the step at d seen in §2. They
disagree once two function changes fall within d of each other. Two consequences are
unphysical:

- **Early propagation (zero-latency edges).** Input pulse 1000–1010, then pulse 1120–1130
  (`/tmp/gls-compare/t3.v`): the GLS output is high **1124–1134**. That is a 10 ps pulse,
  4 ps after its cause, through a 124 ps LUT.
  - Any LUT whose function moved within the last d can pass a later change with latency
    anywhere in (0, d].
  - It is the same for a 2-input LUT where the changes come on different pins.
- **Runts of any width.** The same trace emits a 10 ps output pulse.
  `noShort_of_inertialRD` ("GLS can never show a LUT runt shorter than its path delay",
  A-delay-inertial.md §Fidelity 1) is **false of the GLS**.

**Which is right?** The Lean channel theorems are correct about the channels they define. The
error is the *claim that iverilog implements `InertialRD`*.

Against silicon, SAF is wrong. No physical LUT propagates an edge in 4 ps. Edges are delayed
by at least the minimum arc (prjxray O6 rise 56 ps). Runts in silicon are attenuated
continuously (involution / FNS), not copied at full swing with zero delay.

**Why it matters for the project:** a bundled-data margin check on the GLS is **optimistic**
on glitchy data cones. Example: `f` changes at 0, at 10 and finally at 120. The GLS settles
the cone's output at 124 ps. Any pure-delay channel with lo = 124 settles at 244 ps.
- So the GLS can report data valid up to one LUT delay early, per glitching LUT on the path.
  Adders and comparators glitch.
- That is exactly the direction CLAUDE.md says corrupts data silently. A request that arrives
  "after the data" in the GLS can arrive before it on silicon.

I have not measured how often this occurs in the routed gcd. The next step is for the
research GLS to re-run with the LUT specify path replaced by a transport `always @(f) o <= #d f`,
or with an inertial model that cancels, and to diff the bundle-arrival margins.

The **bridge survives**: if `f` never changes twice within d, then SAF = pure delay d. Each
fire at `t_i + d` samples `f`, which has been constant since `t_i`. So
`inertialRD_of_noShort` has an exact SAF analogue. The recommended proof shape in
A-delay-inertial.md §3 still transfers to the GLS: (a) prove there are no `f` pulses shorter
than d, then (b) the delay channel is irrelevant. Only the stated reason ("GLS is inertial")
must change.

## 2. Runt sweep, 1 LUT and 2-LUT chain (`tb_runt.v`)

| configuration | output vs input width w |
|---|---|
| GLS LUT, d = 124 | w ≤ 123: nothing. w ≥ 124: exactly w. The step is at d, and the tie passes. |
| GLS 2-LUT chain, direct or with a 300 ps **transport** ICBUF (baked build) | the same step at 124, width w (`inertial_comp_self`: ρ stays δ, Δ adds) |
| GLS 2-LUT chain with a 300 ps **annotated** ICBUF (`gate.vvp` build) | LUT1 passes w ≥ 124. The wire then removes everything below **300**. Step at 300 |
| transport LUT (Lean `Pure`, lo = hi) | every w ≥ 1 passes at width w |
| rise 56 / fall 124 (SAF) | positive pulses: none for w < 56, then **w + 68** per LUT (w + 136 after two). Negative pulses (derived from the validated SAF model): none for w < 124, then w − 68 |
| involution exp-channel, δ∞ = 124, T_p = δmin = 60 (Lean `ExpLog`, computed) | none for w ≤ 64 = τ ln 2 (`exp_pulse_cancel_iff`). Then continuous: 65 → 2 ps, 80 → 30, 100 → 62, 124 → 96. 2 stages: 124 → 56 (`pulseWidth_small`, `pulseWidth_strictMono`) |

Two-pulse grid, GLS LUT: two 40 ps pulses with a 60–120 ps gap come out as **one 2-edge
pulse**, the second pulse echoed with the first one's timing. Two 40 ps pulses with a 20–40 ps
gap give nothing. Lean `Filt` (inertial) predicts nothing in both cases, because there is no
124 ps window of 1s. This is where the SAF finding came from.

**Verdict on (2).** For isolated pulses the GLS implements Lean's `InertialRD d d`, with ties
passing exactly as the Lean note assumes. Lean's discontinuity theorem
`inertial_width_discontinuous` holds of it: the width jumps 0 → 124. The research PROGRAM's
sentence "inertial LUT paths swallow narrow pulses" is right for isolated pulses, and wrong
for bursts (§1).

The asymmetric case pins down A-delay-inertial Wip item 3: the threshold is the arc of the
*leading* edge, and the stretch is fall − rise. The +68 ps stretch is ARBITER.md's "+68 ps
each O6 LUT adds to a positive pulse". The research GLS emits one number for both edges
(gen.py writes `(d:d:d) (d:d:d)`), so it never shows that stretch.

**Second discrepancy, internal to the GLS.** `gate.vvp` and `run_baked.vvp` are *not* the
same simulation. A wire pulse narrower than the wire delay vanishes in the gate build and
passes in the baked build. The README's "every event timestamp identical" was observed on
gcd. It is not a property of the two builds.

Silicon: there is **no** board datum for a LUT's runt transfer curve. ARBITER.md's passband
(≤ 80 ps blocked, 160 ps passed at W = 1) was "measured … in simulation", i.e. on the SAF
`cells/sim` model. It must not be read as silicon evidence for any channel. The board test is
A-delay-inertial.md §4(ii) / A-delay-involution.md "how to test".

## 3. bd_c2 (`tb_c2.v`)

### Single-input flips

The test covers 6 stable states × {a, b, rst↑}, in the GLS, with per-pin arcs, with the
feedback wire, and with a transport LUT. **18/18 correct, with 0 extra transitions** in every
variant. This agrees with `bdc2_single_input_ok`, `bdc2_no_static_hazard`, `bdc2_settles`
(Core/Ternary) and `no_static_hazard_single` (Core/Lut).

That is expected. Soundness is proved for `Causal`, and SAF is a `Causal` behaviour at 1 ps
resolution: each update copies `f` of samples at or before the fire step.

### a,b 01→10, skew s (a moves at T, b at T + s)

| model | q0 = 0 | q0 = 1 |
|---|---|---|
| Lean Kleene (`Init.bd_c2_two_change_hazard`, `bdc2_two_input_hazard`: tA = tB = X) | X for every s ≠ 0: may glitch, final value undetermined | same |
| GLS, flat 124 | s ≤ 123: q stays 0, no event at all. **s ≥ 124: one clean full-swing flip to 1** | s ≥ −123: stays 1. s ≤ −124: flips to 0 |
| GLS, A1 = 100 / A2 = 150 | threshold s = 100 | threshold s = −150 |
| GLS, A1 = 150 / A2 = 100 | threshold s = 150 | threshold s = −100 |
| GLS + 300 ps transport ICBUF on the feedback (baked) | s ≤ 123: hold. **124 ≤ s ≤ 300: perpetual oscillation** (48 edges in 10 ns, still running) | mirror image |
| transport LUT, direct feedback (Lean `Pure`) | **1 ≤ s ≤ 123: perpetual oscillation** (about 160 edges in 10 ns, period 124). s ≥ 124: clean flip | mirror image |
| GLS, after a 5 ps glitch on a 120 ps earlier (`tb_c2_saf.v`) | **s = 6 ps flips q to 1** (without the glitch, s = 6 holds) | — |

So the GLS result **does** depend on skew at 1 ps granularity. It is a sharp, deterministic
step at s = the arc of the first-moving pin, with no X, no runt and no metastability. Under
SAF the step is also **history-dependent**: any `f` activity in the previous d moves it,
down to a few ps.

**Which is right:** Lean. Its X covers every one of these outcomes: hold, flip, oscillation.
That is the soundness theorem doing its job. Each binary model picks one arbitrary outcome:
- the GLS picks a sharp threshold;
- transport picks an eternal ring;
- inertial-plus-transport-wire also picks a ring.

None of them is silicon. A real runt entering the loop is attenuated or amplified each
round (involution: `cancel_iff`, `pulseWidth_small`). It resolves to 0 or 1 after an
unbounded time, which is metastability. It neither stops at a sharp threshold nor rings
forever. The perpetual oscillation is an artefact of width-preserving channels: their loop
gain is exactly 1.

Silicon evidence, graded:
- ARBITER.md: 15/192 `bd_arbcell` copies fire, 10 of them at zero skew. The full rise/fall
  timing model "predicts that no copy should ever fire", and "the mechanism is below what the
  flow's timing model can express". This is the board telling us that a deterministic-threshold
  binary model (the GLS's) misses real events in exactly this two-change C-element/SR
  situation. It is consistent with Lean's X and inconsistent with a GLS pass.
- It is not a measurement of *which* mechanism. The A5 pin lead is still open.

## 4. Mux-tree X-propagation (`kleene_check.py`)

There were 43,767 comparisons: 30 INITs × 729 vectors × {O6, O5}, plus 27 `SELMUX2_1`
vectors. **0 mismatches.**

The GLS's `?:` tree (A6 at the root) equals Lean's `Lut.keval`/`kevalSpec` (A1 at the root;
`keval_eq_kevalSpec` makes the order irrelevant), and `SELMUX2_1` equals `kmux`.

The reason is that IEEE 1364 `?:` with an X select merges the two operands bit by bit, which
is `merge`. This is the static half of the gate-fidelity claim (`evalTree_eq_tableEval`), now
confirmed against the GLS implementation rather than only argued. A caveat for anyone writing
reference models: a plain `INIT[{A6..A1}]` bit-select is **not** Kleene. An X index gives all
X; that was my first `LUT_TRC`, and I fixed it.

## 5. Summary table

| case | Lean prediction (theorem) | GLS result | agree? | which is right, and why |
|---|---|---|---|---|
| bd_c2 single-input flips | no glitch, settles (`bdc2_single_input_ok`, `bdc2_no_static_hazard`, `bdc2_settles`, `no_static_hazard_single`) | 18/18 clean, 0 extra edges | **yes** | both. SAF is a `Causal` behaviour, so soundness covers it |
| bd_c2 a,b 01→10, q = 0 | X: hazard, outcome undetermined (`bd_c2_two_change_hazard`, `bdc2_two_input_hazard`) | deterministic step at s = first pin's arc (124, or 100/150); with a feedback wire, a perpetual ring; history-dependent (6 ps flips after a glitch) | **no** (the GLS is one point of Lean's X) | **Lean.** The GLS threshold is an artefact of the delay rule. Board: unexplained arbiter fires at zero skew (ARBITER.md) |
| isolated runt, 1 LUT | inertial: step at ρ (`inertial_pulse_short/long`, `inertial_width_discontinuous`). Pure: always passes (`pulse_survives`). Involution: continuous shrink (`pulseWidth_small`) | step at 124, full width | GLS = **inertial** | for silicon, involution (FNS; Lean A-delay-involution.md). No board datum yet |
| isolated runt, 2-LUT chain | `inertial_comp_self` (ρ = δ, Δ = 2δ) | step at 124 (transport wire) / 300 (annotated wire) | yes / **gate ≠ baked** | the baked transport wire is the physical choice. The gate build's wire filter is an artefact |
| bursts (2 changes within d) | `InertialRD`: filtered; `noShort_of_inertialRD` | **SAF**: zero-latency edges, runts of any width | **no** | Lean is right about inertial channels, but the GLS is not one. Both SAF and inertial are wrong vs silicon. **SAF makes GLS bundling margins optimistic** |
| asymmetric arcs 56/124 | Wip item 3 (open) | threshold = leading-edge arc; stretch = fall − rise = 68 | — | pins down the open item; matches ARBITER.md's +68 ps |
| X on LUT / F7 inputs | `kevalSpec` / `kmux` (`keval_eq_kevalSpec`, `evalTree_eq_tableEval`) | 43,767/43,767 equal | **yes** | both. Verilog `?:` is the Kleene mux |

### Lean lemmas the discrepancies suggest (none written)

1. A SAF channel in `Core/Delay`:
   `Saf d x y :≡` y changes only at {tᵢ + d}, and `y(tᵢ+d) = x(tᵢ+d⁻)`. Then:
   - `saf_of_noShort` (`NoShort d x → Saf d x y ↔ y = shift d x`): the bridge;
   - `saf_eq_inertial_single_pulse`;
   - `saf_early`: for every ε > 0 there is an x whose output edge copies an input value set
     less than ε before;
   - `saf_runt`: output pulses of every width > 0 occur.
   About 1 day, reusing the `Filt` machinery.
2. A correction to `A-delay-inertial.md` §Fidelity, by its owner: replace "iverilog treats
   specify paths as inertial" with SAF, and restrict consequence 1 to isolated pulses.
3. `two_change_outcome_set`: under `Causal`, the bd_c2 01→10 run reaches q = 0, q = 1 and a
   non-settling run. That is completeness for this one case, an instance of Wip W1 in
   A-ternary.md, and it witnesses that the GLS's single outcome is not forced.

## Verdict

**Works.** All three comparisons ran. The LUT function and X-propagation agree exactly. The
delay semantics **disagree**: iverilog's module path is SAF, not inertial. That has a concrete
consequence: the GLS can be optimistic on bundled-data margins, and it shows a
history-dependent, sharp, metastability-free C-element threshold.

**Effort to finish:**
- SAF lemma set: about 1 day.
- A research-side experiment, gcd GLS with transport LUTs and diffed bundle margins: about
  half a day for that branch's owner.

**What it buys:**
- The research GLS gets a specific, reproducible defect report, with tiny benches.
- The formal side gets an exact description of what the GLS computes. That decides which
  formal statements a GLS pass can and cannot support:
  - it supports hazard-freedom claims via Ternary soundness;
  - it does not support runt-freedom or margin lower bounds.
