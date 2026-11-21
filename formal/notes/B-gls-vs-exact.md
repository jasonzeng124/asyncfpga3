# B-gls-vs-exact: shard B's exact cell conditions against the research board-fidelity GLS (probe Bgls)

Shard B, 2026-10-27. This is a read-only comparison. No Lean file was written, no simulation was
run, and no git command beyond `git show` / `ls-tree` / `log` was used. Every research-branch
citation is `origin/claude/research` at `7f6c724`, written as `R:<path>:<line>`. The B side is
`formal/out/cell_constraints.json` (rows with `exactness` exact or sufficient+necessary) plus the
B notes named in each row.

PROGRAM.md (formal) asks for this: "compare the model with the board-fidelity GLS; where the two
disagree, find out which is wrong."

## 1. What the GLS can represent

The "board-fidelity stack" is `GLS_MODEL=fid` on the netlist decoded from the bits, with the
prjxray SDF from `xray_delay.py` (`R:research/data/fid/fullstack.md:1-14`). The default model is
still the SAF specify-path model, and every older GLS result used it.

| B modelling feature | GLS default (SAF) | GLS fid (board-fidelity stack) | cite |
|---|---|---|---|
| per-pin read time (one wire per sink, one arc per pin) | yes: one ICBUF per sink and a specify arc per pin | yes: per-pin **transport** NBA, then a zero-time mux tree | `R:cells/gls/prims.v:51-72,103-108`; `R:cells/gls/fid_core.vh:9-21,172-182` |
| site-pin delay SP[pin] and the LUT→xMUX output hop | only with the xray SDF. nextpnr's SDF has no site-pin delays and charges a flat 25 ps per site pip | same | `R:cells/gls/fid/xray_delay.py:13-17,26-31,69,478-479,592` |
| per-pin feedback (own-loop wire + feedback-pin arc) | yes, as an ordinary sink | yes. gen.py also computes `TLOOP` = feedback wire + arc, for **single-cell loops only** | `R:cells/gls/gen.py:590-614` (limitation stated at 594-595), `:726-731` |
| one consistent corner | yes: `GLS_SDF_FIELD=min/typ/max/band` (band = one shared lerp) | yes | `R:cells/gls/gen.py:293-308` |
| rise ≠ fall on one arc | **no**: one number per arc, rise = fall (prjxray has no split) | **no**: one `T<k>` per pin | `R:cells/gls/fid/xray_delay.py:52-56`; `R:cells/gls/fid_core.vh:141-142` |
| a delay that varies from edge to edge (window, not a point) | **no**. Delays are fixed for a run. Scatter is drawn once per arc (or per pip) at generation time | **no** | `R:cells/gls/gen.py:313-345,412-426` |
| non-monotone (non-FIFO) pin reads | **no**. SAF ⊂ transport with a monotone read map (A's `saf_transport`) | **no**. A fixed transport delay is FIFO | `fid_core.vh:172-182` |
| X window at a binary edge (H_MUX_KLEENE's tick of X) | **no**. Kleene x exists only for x sources (power-up, FF violation) | **no**. `FID_SAMPLE` even strips zero-width glitches. `+META_X=1` gives X only while a runt is resolving | `fid_core.vh:121-131,204-212,104` |
| power-up X, Kleene mux tree | yes | yes | `prims.v:90-101`; `fid_core.vh:184-202` |
| runt on a state loop | SAF swallows pulses narrower than the arc. The gate build leaks one runt (B-gls-runs P4b/P5b) | `FID_RESOLVE` detects "output reverses < TLOOP after its last edge" and resolves it to a random value | `fid_core.vh:23-41,71-118` (condition 77-78) |

So within one run, the fid GLS is **one realisation of B's per-pin model in which every window
has width 0, rise = fall, and there are no X windows.** That realisation is B's `Transport`
(ArbPin), `H_RF_SYM` (LibGapLatch `sym_exact`) and `steer_pin_exact` (fixed delays). Scatter and
seeds sample several such points. None of them reaches a box corner where one pin's rise is slow
and its fall is fast, and none reaches a non-FIFO read.

### What the GLS detects (monitors)

Three checks decide a run, and all three are end to end:
- the vector compare (`RIG_ERR` / `RIG_OK`, width-filtered);
- lap counting;
- the deadlock and ring-stopped watchdogs.

(`R:cells/gls/tb_run.v:83-103,106-134`.)

Beyond those:
- **Cell-level checks.** The only ones are the bundled-data guards on gcd's abs and comparator
  (`R:cells/gls/gen_absguard.py`, `gen_cmpguard.py`) and the FF setup/hold check, which sets
  the flop to X (`prims.v:185-202`).
- **Grant-overlap monitor.** One exists only in the arb_mtbf cell bench
  (`R:cells/gls/fid/f3/tb_f3_arbm.v:16-41`), not in any design run.
- **FID_RESOLVE counters.** `n_meta`, `n_rej` and `n_commit` are printed only with
  `+META_VERBOSE` (`fid_core.vh:84-86,101-103`). `run_fid.sh` does not pass that flag
  (`R:cells/gls/fid/run_fid.sh:13`), so runts on state nodes are invisible in the board-fidelity
  runs.

## 2. Row by row

Legend for "can fail it": **pt** means the GLS can produce a violation at its point delays when
the route or corner violates the fixed-delay (H_RF_SYM) form. **box** means the box-only terms
can be produced. **non-FIFO** means the non-monotone counter-traces can be produced.

| condition (B row) | B result | GLS models it? | GLS can fail it? / detects it? | minimal change | more right, and why |
|---|---|---|---|---|---|
| **Own-feedback race, strict** (`bd_c2*/c3/c4.pulse_width`: enabling combination held ≥ dlmax + dwmax + 1; CElemStrict/2) | exact, strict (`+1` = H_MUX_KLEENE's one tick of X) | Loop wire + arc per pin: yes. The X tick: no, the GLS has binary edges (tie-inclusive: B-gls-runs P4b/P5b needed a 1 ps tie correction) | **pt** yes. Under fid a short enabling pulse gives an output reversal < TLOOP, which FID_RESOLVE catches; the node then resolves to a random value. Under SAF a pulse shorter than the arc vanishes and is hidden (A `ce_c2`). **Detection: end to end only.** META counters are not reported. At exact equality the GLS passes where B fails, by 1 ps | (C1) print the FID_RESOLVE counters in a `final` block. Make `n_meta + n_rej > 0` on any non-arbiter state node a FAIL in run_fid/soak. (C2) `+FID_XW=w`: drive the output x for w ps before each new value, in FID_LUT6 after `FID_SAMPLE`. w = 1 reproduces B's strict boundary, and larger w is the slew sensitivity | **Same condition at the point**; B-gls-runs shows the transport control flips exactly at B's threshold. On strictness neither is right in magnitude: B's 1 ps is the grid minimum, not a measured slew (CElemStrict2 "Not covered"). B has the right *shape*, a parameter wX. The GLS's equality pass is a scheduler tie, not physics. Immaterial against the guardbands. **SAF is wrong** (A-gls-pass), and fid fixes it |
| **Reset-width hold** (`bd_c2*.reset_width`, `design.rst_hold`: rst high ≥ arc(rst).hi + Qhi + 1 at hold vectors; CElemStrict2 `reset_width_iff`, NecessityReset) | exact, strict; needed only at hold vectors. gcd's 185 bd_c2n are released at req = ack = 0, which is a hold vector | yes: the real reset network (rst_sr FDSE, fanout-414 routed skews), the real power-up X and the Kleene resolution | **pt** only with a shortened reset. The rig's reset is µs-scale, so a run can never fail this. A violation would show as a node left x, or as extra tokens leading to wrong laps or deadlock (RigToken `short_rst_many_starts`) | none needed for gcd. For a test: a testbench knob that releases rst after W ps, swept across D, plus (C1) | **Agree.** The GLS is the better witness that the *shipped* reset meets it: real fanout skew and X start, which no rule checks (row says UNCHECKED). B supplies the exact threshold the sweep should find |
| **Latch setup_pulse** (`bd_latch[*].setup_pulse`: Won ≥ (Ehi−Elo) + fhi + 1; LibGapLatch `box_exact`). **No rule checks it** | exact over the box. Under H_RF_SYM it becomes A + Qhi ≤ B (`sym_exact`) | Feedback per pin: yes. **The enable spread term Ehi − Elo (rise read slow, fall read fast on the same pin): no**, because rise = fall | **pt** yes, for the sym form Won ≥ fhi only. The violation is a q reversal < TLOOP, so fid's resolver catches it, but unreported. **box: never** | (C1) makes the sym form a test. (C3) `GLS_RF_SPLIT`: separate rise/fall delays per pin (FID_LUT6 `d_k^r`, `d_k^f`, drawn inside the corner's [lo, hi] or within κ). That reaches the box term. (C7) below gives a direct margin | **B is more right as a gate.** The fabric's rise/fall asymmetry is real but uncharacterised (prjxray has none), and B's box covers it soundly. The GLS can only say the sym form holds at its sampled points. Under a κ corner model the spread shrinks to the κ part, and B's `sym_exact` per realisation is then what the GLS checks |
| **Latch setup_data / hold** (exact, strict; rule I misses fb arc + SP, rule H misses SP + `+1`) | exact over the box | yes, at points, with SP from the xray SDF. The O5 output hop is charged (`xray_delay.py:69`), matching the row's "feedback wire incl. LUT→xMUX hop" | **pt** yes. A setup violation **between** "d arrives after en closes" and "loop not committed" gives a runt, which the resolver sees. A gross setup violation (OLD kept) or a hold violation (NEW captured) is **silent** at the cell: only the vector compare or abs/cmp guards see it, and only if the value matters | (C7) emit per-instance pin-time monitors from `cell_constraints.json`: at each enable fall seen at the latch's own pin, check d stable over [en_fall − (dhi + fhi), en_fall + ehi − dlo] and print the margin | **Agree at a point** (B-gls-runs P5b: transport control at 419 = wfb + arc). B is more right over the band. The GLS is the only thing that knows the *actual* Toff/Tnew event times in context, so (C7) gives a margin per instance |
| **Steer bundled_s hold** (`bd_steer.bundled_s_hold`: F + pr.hi ≤ S1 + ps.lo; LibGapSteer). **No rule checks the hold half** | exact over the box. Also exact at fixed per-pin delays (`steer_pin_exact`) | yes: s and req are separate sinks with separate arcs. The fixed-delay form is exactly what one GLS run instantiates | **pt** yes. Effect: `late_hold_glitch` / a selected output falling early, or a pulse on the unselected exit (`spurious_token`). SAF swallows a glitch narrower than the arc (it hides it). fid passes it. **No monitor**: it is seen only if the stray token causes a wrong result or a deadlock | (C5) a 4-phase protocol monitor per channel, generated alongside `gen_chan.py`'s net list: req↑ only with ack = 0, req↓ only with ack = 1, no req pulse without an ack, and the unselected steer output never rises during a token | **Same condition at a point.** B is more right over the band, because pin independence covers per-pin scatter. S1 comes from bd_ctl's round-trip contract (OpsTimed2), so margins are normally large. The GLS gives the true S1 − F in context |
| **Mux bundled_s hold** (`bd_mux.bundled_s_hold`, uj0/uj1 with own feedback; LibGapMux). No rule checks it | exact (per pin); counter-trace `selected_early_fall` | yes at points | **pt** yes. An early fall of a join with feedback is a state-node reversal, so (C1) may catch it. Otherwise it is end to end only | (C5) + (C1) | as for steer |
| **Arbiter handover without pin FIFO** (`bd_arbcell.handover_overlap`; ArbPin/ArbPin2 `h12/h21_box_iff` vs `_transport_iff`) | Per pin (non-FIFO) ≠ transport whenever both q orderings are allowed (`h21_differs`). Point corners: per pin = transport (`pt_narrow`), all 144 rows safe, min margin 54 ps. Range rows: one arbiter (seed 2 `merge3.uarb1`) fails **even with FIFO** | Fixed delays imply FIFO **by construction**. At one point the GLS equals B's transport window, which equals B's per-pin window (`pt_narrow`) | **pt** only. GLS would show overlap only if the route/corner violates `C6 ≤ c5 ∨ B2 ≤ a2+c5` at that point. Point rows are all safe, so the GLS should never fail. The range-row failure needs independent per-arc values inside one corner: `GLS_SCATTER` per arc can sample it but is not aimed at it. **non-FIFO: never** (`h12_runt_cex`, `dd_runt_cex` need a non-monotone read). **No design-level grant monitor** | (C5') port `tb_f3_arbm.v`'s CHMON (g1&g2 count and width) to every bd_arbiter in the design runs. (C4) `+FID_JITTER=j`: add a fresh uniform [0, j] to each NBA delay, per edge. Out-of-order arrival then gives exactly B's non-FIFO read. This is a stress mode for H_PIN_FIFO, not a fidelity mode. For the range-row failure, run with `GLS_SCATTER_ONLY=` restricted to that arbiter and sweep seeds | **Neither can be the test.** The GLS assumes H_PIN_FIFO, and B makes it an explicit hypothesis. A buffered single-pin path is credibly FIFO (B-no-revert grades wire FIFO "B"). So at a consistent corner the GLS is probably right, and B's non-FIFO overlaps are a sound worst case. Only a board test decides (B-no-revert T-NR1). The board's 8% bd_arbcell overlap is explained by **neither**: fid shows ≤ 28 ps transient overlaps (`R:research/data/fid/f3_model.md:131`), and B's point rows are safe |
| **A0 fork** (`bd_arbiter.a0_fork_client*`: late ≤ early, both with SP; rule J misses SP) | exact | yes at points, with SP from the xray SDF (rule J has none: `R:research/PROGRAM.md:250-251`) | **pt** yes. An early ack is end-to-end visible (B-gls-runs P1b on the real prims: early ack from δ ≥ 296) | (C5') | **Agree at a point.** B is more right over the box: 15/72 clients fail in the independent box and are safe at every consistent corner (OnGcdArbA0). The GLS will pass at corners, which is consistent with B, but a GLS pass is no evidence for the box |
| **H_NO_REVERT / monotone wire read** (WinFifo, WinFifoCausal, NoRevert: FIFO ⟺ Win + H_NO_REVERT; `win_not_noRevert`, `kleene_revert`) | a hypothesis (grade B), not a timing row | **Assumed by construction.** A transport ICBUF and a transport pin replay edges in order. FID_SAMPLE removes same-step zero-width glitches (`fid_core.vh:204-212`), so the GLS cannot represent a revert inside a zone | **never** (non-FIFO) | (C4) shows what a revert *would* do downstream, for sensitivity only. B-no-revert T-NR2 (log pin events of every control LUT under fid and count function-hazard events per zone) is the GLS-side half and needs no model change: it tests H_SEL_ORDER, not the transistor | **Not decidable by GLS.** It is a fabric hypothesis, and the GLS bakes it in. B is more right in that it names it. Only T-NR1 / T-NR1b (board) decide |
| **Rig `uenv1` RT_FB** (H_FB_FIRST at `urig.uenv1.u`; RigToken `stale_fb_extra_start`) | Fails only under C-10h's 0.772/1.155 band: seed 2 −117/−221, seed 4 −86/−243 ps. It passes at the unguarded fast (+94) and slow (+161) corners (`C-10h-tcheck3.md:170-176`) | yes: the feedback and the response are separate sinks with real SP and the xMUX hop | **pt** at a consistent corner: no (margin +94/+161), so a GLS corner run must pass. Scatter: arc mode draws the shared xMUX prefix independently on both sinks (the same double charge tcheck makes, `C-10h-tcheck3.md:175`); wire mode shares it, which is correct. **No monitor**: an extra start offer is visible only if it corrupts a lap | (C6) count `start.req` rises between consecutive `RIG_LAP` rises in tb_run.v; it must be exactly 1 (RigToken §5). Per-pin fault knob `GLS_SCALE_PIN=inst/pin:f` (one sink arc). **Bug:** `GLS_SCALE_INST` is not applied to interconnect arcs in `GLS_SCATTER_MODE=wire` (`R:cells/gls/gen.py:494-512`: the wire branch returns without the SCALE_INST loop that `perturb` has at 420-424). So a "fault + wire scatter" run silently does not inject the wire part of the fault | **GLS (wire-mode scatter) is more right on the shared prefix.** The band's −86..−243 ps is partly the prefix charged twice. B/C's step-model counter-run shows what happens *if* it fails. Whether it fails is a per-route band question that a targeted GLS fault can answer, provided (C6) watches it |
| **bd_ctree.node_loop / bd_merge.uxa_loop** (loop terms with SP, strict) | exact | yes at points (single-cell loops: TLOOP is found) | **pt**, via resolver runts (C1) | (C1) | as for the own-feedback race |
| **bd_mux.uxa/uya_rtz**, **bdc_muxn.no_third_branch**, **gcd_rig.idx_setup** | exact | yes at points. idx_setup involves the FF and the hk clock, which the GLS models (FF TSU/THD → X in the default model) | **pt**. idx setup: an FF violation sets X in the default model and is caught. No-third-branch: a decode glitch, end to end only | (C5)/(C7) | agree at points; B is more right over the band |

## 3. Pattern: where the two disagree, and which is wrong

1. **At one consistent corner they agree, up to a 1 ps tie, once the LUT is transport.** Every B
   exact row has a fixed-delay form, and the fid GLS instantiates exactly that form.
   - B-gls-runs reproduced B's thresholds to the ps with transport controls (419 for the latch,
     δ > 0 for the A0 fork).
   - The one real model defect on the GLS side is SAF (default model; CARRY4 and SLICE_LATX are
     SAF even under fid, A-gls-compare-2). **There the GLS is wrong.**
2. **Box and band terms are not reachable by the GLS:** rise/fall spread on one pin, and
   independent per-edge values. The affected rows are setup_pulse's Ehi − Elo, the link's
   req-pin spread in the latch pulse budget, and the A0-fork box failures.
   - The GLS is not wrong here. It is incomplete: prjxray has no rise/fall data, so the GLS
     cannot know the spread, and B bounds it. As a ship gate, B (or the κ corner model) is
     the right side.
   - A GLS pass at FAST_MIN / SLOW_MAX / band does not cover these rows. A-gls-pass (c)'s
     bracketing needs monotone acyclic logic, and every one of these cells has feedback.
3. **Non-FIFO and X-window phenomena are excluded by construction:** the arbiter per-pin
   handover runts, H_NO_REVERT, and the strict `+1`.
   - B makes each an explicit hypothesis (H_PIN_FIFO, H_NO_REVERT, wX = 1). The GLS assumes
     them silently.
   - That silent assumption is a fidelity-table entry, not a bug. Only a board test decides
     these hypotheses. The GLS can at most show the consequence through (C4) / (C2) stress modes.
4. **Detection is the bigger gap than modelling.** Even where the fid GLS produces the violating
   behaviour, nothing at the cell flags it:
   - **runt on a state node:** resolved randomly, counters not printed;
   - **stray token:** caught only if it changes a gcd result;
   - **grant overlap:** no design monitor;
   - **extra start offer:** not counted.

   So a GLS pass on 16 vectors says less than "no B row is violated at the sampled delays".
   (C1), (C5), (C6) and (C7) close that gap cheaply.

## 4. Minimal GLS changes, ranked (cost in brackets)

- **C1 [small].** In a `final` block, print FID_RESOLVE `n_meta / n_rej / n_commit` per
  instance, with the cell's names.map name.
  - run_fid/soak: FAIL on any count > 0 at a state node that is not an arbiter `ustate`.
  - This turns every own-loop row into a test at the GLS's points: pulse_width, setup_pulse
    (sym form), the setup_data band, reset_width, node_loop, uxa_loop and mux-join hold.
- **C6 [small].** tb_run.v: count `start.req` rises per `RIG_LAP`; it must be 1.
  - Fix the `GLS_SCALE_INST` bypass in `perturb_ic` wire mode (`gen.py:494-512`).
  - Add `GLS_SCALE_PIN=inst/pin:f` for one sink, to aim a fault at uenv1's feedback pin.
- **C5 [medium].** A generated 4-phase protocol monitor per channel; the steer unselected-exit
  check; the arb_mtbf CHMON overlap monitor ported to every bd_arbiter.
- **C7 [medium].** Per-instance pin-time monitors generated from `cell_constraints.json`:
  - evaluate each exact row's inequality on the run's actual event times at the LUT pins;
  - print margins.
  - This is the direct row-by-row comparison PROGRAM.md asks for, and it gives every
    disagreement a number.
- **C2 [small].** `+FID_XW=w`: an x window on each LUT output edge. At w = 1 it reproduces B's
  strict boundary.
- **C3 [medium].** `GLS_RF_SPLIT`: per-pin rise/fall delays inside the corner interval or κ. It
  makes the box spread terms reachable. Keep transport semantics, so that a pulse shorter than
  |d^r − d^f| visibly inverts or vanishes, which is itself a finding.
- **C4 [small, stress only].** `+FID_JITTER=j`: a per-edge random NBA delay. Gives non-FIFO
  reads for H_PIN_FIFO / H_NO_REVERT sensitivity. It is not a fidelity mode.

## 5. Not covered

- **No GLS run.** Every "can fail" is argued from source. B-gls-runs ran the cell-level
  thresholds; this note adds no runs.
- **The "no single-input LUT glitch" claim.** fid's assumption (P. Alfke, comp.arch.fpga;
  `fid_core.vh:16-19`) is the same physical content as B's H_MUX_MONO and H_PIN_MONO. Neither
  side has evidence beyond that claim.
- **Multi-cell loops.** gen.py does not detect them (`gen.py:594-595`), so (C1) misses races on
  loops through two LUTs, such as the uenv0/uenv1 ring itself. That ring needs (C6).
- **Lean.** No GlsGap file was written. The needed facts already exist as B and A theorems:
  `sym_exact`, `steer_pin_exact`, `pt_narrow`, `transport_noRevertI` and A's `saf_transport`.
  "A fixed-delay run is a width-0 window behaviour" is immediate from them.
