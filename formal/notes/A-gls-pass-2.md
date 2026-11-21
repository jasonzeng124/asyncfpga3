# A-gls-pass-2: what a passing board-fidelity (GLS_MODEL=fid) GLS run implies

Probe GLSPass2, shard A, session 2026-10-29. STATUS: DONE (both files check).
Files: `formal/lean/Formal/Core/Delay/GLSFid.lean`, `formal/lean/Formal/Core/Delay/GLSPass2.lean`.
Research side read at `origin/claude/research` tip `6524fa3` (read-only `git show`), written
`R:<path>:<line>`. Lean core only (no Mathlib). Imports `Trace.Discrete` and `Delay.SAF`
(both already have oleans); does NOT import `GLSPass.lean` (being fixed by GLSFix).

## What checks

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Core/Delay/GLSFid.lean Formal/Core/Delay/GLSPass2.lean
    -> [audit] 249 declarations checked
    -> [check] OK

(check.sh per-file mode, so `-DautoImplicit=false`; no errors, no warnings in the last
`lake env lean` run; no sorry/axiom/native_decide; GLSFid is passed first only because it
has no olean in .lake/build yet.)

## 1. The fid LUT channel, as the Verilog implements it

The board-fidelity stack is the baked netlist compiled with `-DGLS_TRANSPORT_IC -DGLS_FID`
(`R:cells/gls/fid/build_fid.sh:71-73`). Its primitives:

| Verilog | what it does | Lean (`Formal.Core.GLSFid`) |
|---|---|---|
| `ICBUF`, `R:cells/gls/prims.v:51-54` | `always @(I) o <= #D I`: transport wire | `icbuf D = delay D` |
| `FID_LUT6` copies, `R:cells/gls/fid_core.vh:152-158,172-182` | each pin `ak <= #(dk) Ak`, `dk = max(T_k + level_k - 1, 0)` | `copy`, `copyDelay`, `off6`/`off5` (`FID_LEVEL_PS`) |
| mux tree, `fid_core.vh:191-202` | zero-time INIT lookup of the copies, A6 at the root | `muxTree6`/`muxTree5`, proved = `INIT.testBit idx` (`muxTree6_eq`, `muxTree5_eq`, all INIT) |
| `FID_SAMPLE`, `fid_core.vh:122-131,204-210` | output = f 1 ps after its first change in a step | `sample = delay 1` (end-of-step values) |
| `FID_RESOLVE`, `fid_core.vh:72-73` | identity unless state node (`en=1`, `TLOOP>0`) | non-state LUTs only; decision rule `resolve` (`:77-98`) |
| `FID_MUX2`, `fid_core.vh:216-227` | MUXF7/F8, same per-pin form | `fidMux2`, `fidMux2_eq` |

Proved:
- `fidO6_perPin`, `fidO5_perPin`: the fid LUT output is the **per-pin pure-delay gate**
  `perPin (lut6 INIT) D A t = lut6 INIT (k ↦ A k (t - D k))`, with `D k = pinDelay` (copy
  delay + the sampler's 1 ps).
- `fidO6_default`: with `FID_LEVEL_PS` unset (0) and arcs `T k ≥ 1`, `D k = T k` exactly.
- `one_le_pinDelay`, `pinDelay_clamp`: a fid pin never responds in under 1 ps; a large
  level offset clamps at 1 ps (it can reorder arrivals, only down to one quantum).
- `perPin_icbuf`: wire then pin = one per-pin delay `W + D`.
- `perPin_pulse_passes`: every pulse width passes (transport).
- `perPin_xor_hazard`: an XOR of one rising edge through arcs `d0 ≤ d1` outputs exactly the
  pulse `[p+d0, p+d1)`: the hazard the arrival order implies, nothing more.
- `perPin_equal`, `fid_eq_saf_iff`: with one arc `d` on every pin, fid = pure delay of the
  function value, and the default (SAF) model agrees with fid iff A-delay-saf's
  `Faithful` monitor is clean.
- `resolve_all_outcomes`: for every runt width, loop delay and `win ≥ 2`, some noise draw
  rejects, some commits, some reverts. Which one a run shows is decided by the seed.

Checked against iverilog 11 on the unmodified `fid_core.vh` (scratch testbench
`/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/GLSPass2/sim/tb.v`, XOR INIT
`64'h6666...`, T1=50, T2=80): every output edge equals `A1(t-50) xor A2(t-80)`, including a
1 ps input pulse (output 1550-1551) and two copies landing 1 ps apart (1780-1781). The X
window: O6 = x on [0, 80) = [0, max T_k). This is what fixed the sampler as `delay 1`
(the sampler resumes before the same step's NBA updates).

Resolver finding (iverilog, `sim/tb2.v`, TLOOP=200, default TAU=WIN=150): a 20 ps runt is
"rejected" (`RUNT ... rejected`), but the output `o` still shows the full-swing 20 ps pulse
(1000-1020). `fid_core.vh:30` says "the runt is rejected outright (the node never left)";
that is true of the node's later value, not of its output wire: `o_r = f` was executed at
the runt's first edge (`:113-115`), before the runt was recognised. Every fanout sees it.
A 150 ps runt resolved differently under `META_SEED=0` (commit after 251 ps) and
`META_SEED=5` (back, after 647 ps).

Not modelled: the time-0 X window (Lean signals are constant before 0, so `t < max T_k`
is not faithful), Kleene X, the resolver's event scheduling (only its decision), loops
through more than one cell (gen.py does not detect them either, `R:cells/gls/gen.py:667`),
CARRY4/flops/latches.

## 2. What a passing fid run implies (`Formal.Core.GLSPass2`)

Model: `PNet` (inputs `0..m-1`, cell `k` with `ar k` pins reading `src k j`, function
`F k`); `FidRun N D x s` = every cell is `perPin (F k) (D k)` (the fid run at per-pin
assignment `D` = wire + arc); `BandRun N lo hi x s` = every pin is SOME monotone warp with
delays in `[lo k j, hi k j]` (`Transport`, free per pin and per edge, so rise ≠ fall is
included). Hypotheses `Topo` (acyclic, topologically numbered) and `Local`.

(a) `fid_in_band`: a fid run at a point of the band is a band behaviour.
`fid_unique`: the fid run at an assignment is unique (acyclic).

(b) Sufficient conditions.
- Any logic: `band_settle_sta`, `band_agree_sta`, `fid_final_covers`. With a static-timing
  horizon `S` (inputs constant from `S i`; `S k ≥ S (src k j) + hi k j`), every band
  behaviour is settled from `S k` and all agree, so ONE fid run at any point of the band
  gives every band behaviour's final value from the horizon on. Nothing before it.
- Monotone logic, rising inputs: `bracket`. The two consistent-corner runs `sL` (all arcs
  at `lo`, `GLS_SDF_FIELD=min`) and `sH` (all at `hi`, `max`) bracket every band behaviour
  `sH ≤ s ≤ sL`, edge-varying ones included. Corollaries `cover_rise`, `cover_quiet`,
  `cover_bundle` (slow run has data high by T, fast run has request low before T ⇒ no band
  behaviour has request high with data low).

(c) Counterexamples (explicit nets; transport and inertial outputs).
- `xor_consistent_pass` / `xor_band_fail` / `xor_point_in_band`: XOR of one edge through two
  pins with identical corner data. Every consistent-corner run (each arc's delay a fixed
  function `g` of its own corner triple: min, typ, max, any `band` lerp, any
  `GLS_DELAY_SCALE`) keeps the XOR low; the mixed point (pin 0 at `lo`, pin 1 at `hi`)
  shows a `hi - lo` pulse. `xor_inertial_fail`: an inertial output with `δ < hi - lo` keeps
  it. `xor_inertial_hidden`: `δ ≥ hi - lo` hides it (fid is then pessimistic).
  `xor_o6`: at prjxray O6 45/124 ps, a 79 ps glitch at 1045-1123.
- `and_consistent_pass` / `and_band_fail`: the same with a monotone AND of a rising and a
  falling copy: `bracket`'s rising-inputs hypothesis cannot be dropped.
- `buf_every_point_passes` / `buf_band_loses`: a buffer on a `w` ps pulse. Every fid run at
  every assignment shows the pulse; a band behaviour whose rise is `w` slower than its fall
  (`w + lo ≤ hi`) never raises the output. `buf_inertial_loses`: inertial `δ ≥ w` loses it
  at every point while every fid run shows it.

Plain-language problem statements.
- `bracket`: ASSUMES an acyclic netlist of positive-unate cells, primary inputs that only
  rise, and that the two corner fid runs exist. PROVES every band behaviour lies between
  the slow-corner run and the fast-corner run at every signal and time. DOES NOT cover
  feedback (every C-element, latch, arbiter), falling inputs (`and_*` shows it fails), XOR
  data paths, X values, or inertial silicon.
- `band_agree_sta`: ASSUMES acyclic, local cells and a static horizon. PROVES all band
  behaviours agree and are constant from the horizon. DOES NOT say anything about glitches
  or values before the horizon, which is where bundled-data margins live.
- counterexamples: each is a concrete circuit, stimulus and pair of delay assignments;
  they show that the fid run set {min, typ, max, band(α), scaled} is not a cover of the
  band for non-monotone logic (`xor`), for monotone logic with mixed-direction inputs
  (`and`), and that even ALL fixed-delay runs are not a cover of the per-edge envelope
  (`buf`). They do not say how often such shapes occur in gcd_hw.

## 3. Comparison with B's notes/B-gls-vs-exact.md (read-only, written at research 7f6c724)

- B §1 "within one run, the fid GLS is one realisation of B's per-pin model with window
  width 0, rise = fall": now a theorem (`fidO6_perPin`, `fid_in_band`).
- B §3.2 "box/band terms (rise/fall spread) are not reachable by the GLS": formalised by
  `buf_every_point_passes` + `buf_band_loses`: no fixed-delay run, at any point, reaches a
  per-edge behaviour, and there are properties whose truth depends on it.
- B §3.2 "A-gls-pass (c)'s bracketing needs monotone acyclic logic, and every one of these
  cells has feedback": agrees. `bracket` is now per-pin (the fid shape) and covers
  edge-varying behaviours, but still needs acyclic monotone logic with rising inputs.
- B §1 "FID_RESOLVE counters invisible": agreed, and stronger: a "rejected" runt is still
  emitted on the output (iverilog, §1 above), so the counters alone would undercount what
  downstream saw.
- B §3.1 says CARRY4 and SLICE_LATX are SAF even under fid. That is stale at 6524fa3:
  `R:cells/gls/prims.v:209-215,459-465,557-562,1025-1028` now give FFs, latches, CARRY4 and
  BUFGCTRL per-pin transport fid variants. CARRY4 has the same per-(pin,output) shape as
  `perPin`, but this probe did not transcribe it.

## 4. For the research branch (suggestions only)

1. A fid pass at min/max/band corners is NOT a band pass for non-monotone logic
   (`xor_consistent_pass`/`xor_band_fail`): the consistent-corner runs keep every
   equal-band skew at 0. Add mixed-corner runs aimed at reconvergent pins (one pin min,
   the other max), or use the formal X/hazard audit, which covers the band.
2. `GLS_SCATTER` draws do give nonzero skews, so they can find the XOR case, but only with
   skew > δ under inertial silicon; they sample, they do not cover.
3. No fid run models rise ≠ fall; properties that need a pulse to arrive (two-phase
   enables, runt-sensitive loops) are not covered by any number of fid runs (`buf_*`).
4. `fid_core.vh:30` comment: a rejected runt is not invisible; print the resolver
   counters (B's C1) AND count runts emitted.
5. The time-0 X window [0, max T_k) is real in the fid LUT; harmless if reset outlasts it.

## 5. Not done
- Full trace model of FID_RESOLVE (event scheduling, kick, ignore windows); only the
  decision rule.
- CARRY4 / FF / latch fid variants; multi-cell loops.
- A unate (per-signal polarity) generalisation of `bracket`; nets with feedback.
- Existence of fid runs on general acyclic nets (hypothesis in `bracket`; existence shown
  for the counterexample nets: `twoPinRun_is`, `buf_run_exists`).
- Real time (the 1 ps quantum is iverilog's timescale, so discrete is faithful to the sim,
  not to silicon).

## For the lead
- Lakefile: no change (glob). Optionally add `import Formal.Core.Delay.GLSFid` and
  `import Formal.Core.Delay.GLSPass2` to `Formal.lean`.
- No Wip files.
