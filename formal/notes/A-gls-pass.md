# A-gls-pass: what a passing research-GLS run does and does not imply

Probe GLSimp. PROGRAM.md Phase 2, item A, second half: "prove what a passing GLS run does and
does not imply". The channel itself is in `Formal/Core/Delay/SAF.lean` (notes/A-delay-saf.md).
This file adds the *run*. Namespace `Formal.Core.GLSPass`. Discrete time (ℕ, 1 step = 1 ps,
iverilog's timescale). Lean core only: it imports `Formal.Core.Delay.SAF`, which imports
`Formal.Core.Trace.Discrete`. It does not import Mathlib, and it does not import the real-time
`Delay/Pure` or `Delay/Inertial`. "Transport" and "inertial" below are the discrete
`Trace.Discrete` versions: `delay`, `Transport lo hi`, and `inertial`.

## What checks

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Core/Trace/Discrete.lean Formal/Core/Delay/SAF.lean Formal/Core/Delay/GLSPass.lean
    -> [audit] 263 declarations checked
    -> [check] OK

The file compiles with no errors and no warnings. It contains no `sorry`, `admit`, `axiom`,
`native_decide` or `bv_decide`. Four concrete facts are proved by plain `decide`: two `InScatter`
inequalities and two 248-step evaluations. The inertial evaluation uses
`set_option maxRecDepth 20000`. The two dependencies are passed to check.sh only because
Mathlib/lake oleans were not built in this container. Nothing in them changed.

## The model (assumptions, all explicit in the Lean)

**Netlist (`Net`).**
- Signals are numbered `0..n-1`. Signals `0..m-1` are primary inputs and `m..n-1` are LUTs.
- LUT `k` outputs `f k` of its pin vector. Pin `j` sees signal `j` through a wire into `k`.
- Feedback is allowed (it is used for `bd_c2`). `Acyclic` is a hypothesis wherever it is needed.

**Assignment (`Asg`).** One number per LUT arc (`d k`) and one per wire (`w k j`). This is what
gen.py's single-number `(d:d:d)` SDF gives.
- It is the same delay for both edges and for all pins of a LUT. The per-pin and rise/fall
  cases are not modelled.

**GLS run (`GLSRun` = `SemRun .saf`).** Every LUT is SAF and every wire is a pure delay (the
baked build, `-DGLS_TRANSPORT_IC`). Signals `≥ n` are pinned to `false`.
- `SemRun .transport` uses pure-delay LUTs.
- `SemRun .inertial` uses `delay 1 ∘ inertial (d-1)`, which agrees with SAF on isolated pulses.

**Silicon envelope (`BandRun N lo hi`).** Each LUT and each wire is some `Transport lo hi`
behaviour, a monotone time warp, with its own band. Use this as the stand-in for "the chip under
some delays in the band". It is the sound digital envelope of Delay/Pure and Delay/Corner. It is
not an involution or analog model.

## Proved

### (a) What a pass implies

**`run_unique`.** On an acyclic net, the run at one assignment is unique for each LUT semantics.

**`gls_unique_time`.** With feedback, two GLS runs that agree on every LUT output at step 0 are
equal, provided every LUT delay is ≥ 1.

**`gls_pass_of_saf_silicon`.** **If the silicon is exactly SAF at exactly the annotated
delays**, then a property of the GLS run holds of the silicon.
- That is all a bare pass gives.

**`gls_eq_transport_of_faithful`, `gls_pass_transport_of_faithful`.** Suppose the `Faithful`
monitor is clean: in the GLS run, every LUT fire copies the value its own change set. Then:
- the GLS run *is* the pure-delay run at the same assignment (feedback allowed);
- so the pass holds for pure-delay silicon at exactly that assignment (acyclic net).

**`gls_in_envelope`.** Every GLS run is a `BandRun` with LUT band `[1, d]` and exact wires. A
property proved for that whole envelope holds of the GLS.
- The converse is the useful reading: such a property cannot be refuted by a GLS run.

### (b) What a pass does NOT imply

Each item is an explicit circuit and stimulus. Every theorem is proved for all parameters and
also instantiated at prjxray O6 numbers: 45 / 56 / 100 / 124 ps = FAST_MIN / FAST_MAX /
SLOW_MIN / SLOW_MAX, with the GLS using 124.

**LUT with skewed inputs: `ce_skew`, `ce_skew_124`, `ce_skew_kappa`, `ce_skew_inertial_hides`.**
- *Circuit and stimulus:* an XOR LUT whose two pins see one source edge, one of them through a
  100 ps wire. This gives a static-0 hazard of width 100 ps.
- *Pass:* the GLS at 124 ps shows no output glitch.
- (i) The GLS at any LUT delay `d' ≤ 100` glitches. 100 ps is inside [45, 124].
- (i, one corner) With a 118 ps skew, the LUT at 118 ps is within 5 % scatter of 124 ps, and the
  GLS there glitches.
- (ii) A transport LUT at 124 ps glitches.
- (iii) The envelope `[45, 124]` admits a glitching behaviour; in general this holds for every
  `lo ≤ d`. The glitch is in the circuit, and the SAF channel hides it.
- An inertial LUT hides it too, so this circuit does not separate SAF from inertial.

**Bundled-data capture: `ce_capture`, `ce_capture_124`.** This is the audit's `tb_impact`
shape.
- *Circuit and stimulus:* an XOR3 data LUT with inputs rising at 1, 124 and 247 ps. Its function
  value goes 0 → 1 → 0 → 1, with final value 1. A latch captures it when the request arrives at
  248 ps.
- *Pass:* the GLS at 124 ps captures 1.
- (i) The GLS at **123 ps** captures **0**. 123 ps is inside the band and within 1 % scatter of
  124. **A faster LUT fails where the slow arc passed, so annotating the slow maximum is not a
  conservative corner.**
- (ii) Transport and inertial LUTs at 124 ps capture 0. For general `d0`, the theorem proves
  that the pure-delay data is wrong at `2·d0` and right from `3·d0 − 1` on, which is 371 ps
  here. The GLS shows it right from 248 ps.

**C-element `bd_c2`: `ce_c2`, `ce_c2_124`.**
- *Circuit and stimulus:* the majority LUT with q fed back. It starts from reset `q = 0`. Inputs
  `a, b` go `01 → 10`, with `a` rising at 1000 ps and `b` falling at 1100 ps, so the skew is
  100 ps.
- *Pass:* the GLS at 124 ps holds `q = 0`.
- (i) The GLS at 100 ps latches `q = 1` at 1100.
- (ii) A transport LUT at 124 ps latches at 1124.
- (iii) The envelope `[45, 124]` admits a latch at 1045.
- The GLS's sharp threshold is "skew = annotated arc". It is a property of the number in the
  SDF, not of the cell. This matches the A-gls-compare §3 measurements, and the board's
  unexplained `bd_arbcell` fires are consistent with it.

**`annotated_ne_baked`.** A wire pulse narrower than the wire delay vanishes in the annotated
build, where the wire is a specify path and so SAF. It passes in the baked build. The two GLS
builds are different runs (audit finding 1c).

### (c) A sufficient condition under which one pass covers the band

The hypotheses (`MonoCirc`):
- the net is acyclic;
- every LUT function is monotone (positive-unate);
- every primary input only rises (`Rising`).

Under them:

**`mono_saf_is_transport`.** The GLS run is the pure-delay run, so the monitor is automatically
clean.

**`band_bracket_hi`.** Take any envelope behaviour whose per-arc maxima are ≤ the GLS
assignment. It is high wherever the GLS run is high. This covers any assignment below and any
transport behaviour inside it.

**`band_bracket_lo`.** Take any envelope behaviour whose per-arc minima are ≥ the GLS
assignment. It is high only where the GLS run is high.

**`gls_mono_settle_band`, `gls_mono_settle_assign`.** Suppose ONE GLS run at the per-arc
maxima has signal k high at T. Then every behaviour and every assignment below has k high from
T on.

**`gls_mono_bundle`.** Take two GLS runs, one with every arc at FAST_MIN and one with every arc
at SLOW_MAX. If the slow run has the data high at T and the fast run has the request low before
T, then in every envelope behaviour inside [FAST_MIN, SLOW_MAX] the request is never high while
the data is low.
- This uses two runs at two corners. Each run uses a single corner, so corners are never mixed
  within an analysis.

All three counterexample circuits in (b) break a hypothesis of (c):
- XOR and XOR3 are not monotone;
- `bd_c2` has feedback, and its stimulus has a falling input.

## NOT covered

**Per-pin and rise/fall arcs.** These are not covered, because gen.py emits one number per arc.
The fire order can then cross (A-delay-saf Wip W1). The `GLS_FID` opt-in model (per-pin
transport arcs plus a metastability resolver) is not modelled.

**(c) for real data paths.** Data words rise and fall, and adders and comparators are XOR-heavy.
So (c) applies to monotone control/completion cones driven by a single-direction phase of a
four-phase handshake. It does not apply to gcd's datapath.
- A unate generalization, with per-signal polarity, is plausible but not done.
- A version of (c) for nets with feedback is not done.

**Real time and the involution channel.** These are not covered. A glitch "admitted by the
envelope" is a transport behaviour. Whether silicon passes a 100 ps runt through a 124 ps LUT is
a channel question: see A-delay-involution, where it does for widths above τ·ln 2.

**X values, setup/hold checks, FF/CARRY/MUXF7 timing and DSP.** None of these are covered. The
LUT is a Boolean function here, not its mux tree.

**Measured gcd numbers.** No claim is made about how often these situations occur in the routed
gcd.

## Concrete changes this suggests for the research GLS (read-only suggestions)

1. **Add a fire monitor to `SLICE_LUTX` (the `Faithful` monitor).**
   - At each scheduled update, record f. At the fire, compare it with the current f.
   - Count mismatches per instance and print them.
   - A run with zero mismatches is the pure-delay run (`gls_eq_transport_of_faithful`), and
     its margins are the transport margins at that assignment.
   - A run with mismatches has optimistic margins (`ce_capture`) and hidden hazards
     (`ce_skew`, `ce_c2`).
2. **Or use transport LUTs by default.** Use `always @(f) o <= #d f`, or the existing
   `GLS_FID` per-pin transport model. Then a "no glitch" result at least means "no glitch at
   this assignment under transport".
3. **Do not take the nominal or slow column as the conservative corner.** `ce_capture` (a
   123 ps LUT fails where 124 passes) and `ce_c2` (a faster LUT latches) are counterexamples.
   - Run at least the FAST_MIN and SLOW_MAX corners. `GLS_SDF_FIELD`/`GLS_DELAY_SCALE`
     already allow this.
   - Read a pass over the band only under the conditions of (c), or with an STA bound.
4. **Treat a GLS "C-element holds" or "no glitch" as no evidence for the band.**
   - Sweep skews against the arc, or rely on the Ternary/Kleene X-result, which covers every
     outcome (A-gls-compare §3).
   - The `GLS_SCATTER` runs sample the band. They do not cover it.
5. **Annotated vs baked builds.** The acceptance gate (annotated, wires as specify paths) and
   the simulated build (baked, transport wires) are different semantics
   (`annotated_ne_baked`). The "every event timestamp identical" statement in `prims.v` and
   `build.sh` should be dropped or qualified.

## For the lead

- **Lakefile:** no change. The `Formal.+` glob picks the file up.
- **Root import:** optionally add `import Formal.Core.Delay.GLSPass` to `Formal.lean`, next
  to `Formal.Core.Delay.SAF`.
- **Wip:** none.
