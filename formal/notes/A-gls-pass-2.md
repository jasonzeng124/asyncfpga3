# A-gls-pass-2: what a passing board-fidelity (GLS_MODEL=fid) GLS run implies

Probe GLSPass2, shard A, session 2026-10-29. STATUS: IN PROGRESS (Lean written; check
results below are updated as they come in).
Files: `formal/lean/Formal/Core/Delay/GLSFid.lean`, `formal/lean/Formal/Core/Delay/GLSPass2.lean`.
Scratch only: `formal/lean/Wip/GLSPass2/MuxTest.lean` (the mux-tree lemma's first try; superseded).
Research side read at `origin/claude/research` tip `6524fa3` (read-only `git show`), written
`R:<path>:<line>`. Lean core only (no Mathlib). Imports `Trace.Discrete` and `Delay.SAF`
(both already have oleans); does NOT import `GLSPass.lean` (being fixed by GLSFix).

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

## 3. Comparison with B's notes/B-gls-vs-exact.md

(see §5 once written)
