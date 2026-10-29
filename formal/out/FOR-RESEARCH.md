# What the research branch should change (from claude/formal)

Rewritten 2026-10-28 (shard A, probe ForRes). It replaces every earlier draft.
The research tip checked is `origin/claude/research` 350f9be (last code change
da38b8d, 2026-10-27 11:19). Items the research branch has already fixed are listed in §15.

How to read this:
- Each item gives the finding, the evidence, the change, and a command that tests it.
- **"Proved"** means a Lean theorem that passes `formal/check.sh`. It is a statement about
  the named model. Whether that model matches silicon is a separate, named hypothesis.
- **"Measured"** means a script output on a route, not a proof.
- File:line references into the research branch are at 350f9be (read with `git show`).

Order: §1-§5 concern the timing rules and the delay model. §6-§10 concern the GLS. §11-§14
concern cells, the flow and the board.

## 1. Rule A: constant tie-off nets are timed as data (false path) — OPEN
- **Finding** (shard C, measured on 12 routes): `tighten.cell_boundary()` does not skip
  `$PACKER_GND_DRV` / `$PACKER_VCC_DRV`. Rule A's bundled pairing then launches a data path at
  the tie-off driver, and its 3-5 ns route becomes the "latest data".
  - A constant never switches, so this is a false path.
  - It sets the rule-A peak of 1-4 compute cells on every collatz/xorshift/ipow route, too
    high by 0.9-4.2 ns.
  - It is the whole cause of the only project-rule violation seen: ipow seed 3, rule A on
    `uut.umuli1`, −59 ps guarded. Without the tie-off the peak is 14226 ps instead of 17715.
  - The error is on the safe side, but delay lines ratcheted from rule A on those cells
    (T3/T9 sizes) are longer than they need to be.
- **Evidence:** `formal/notes/C-10n-kernels.md` ("Finding: rule A includes the constant
  tie-off drivers"); table `formal/tools/kcheck/results/constsrc.tsv`. In the code,
  `cells/verify/tighten.py:674-697` (`cell_boundary`) has no `is_const` test, while
  `starts_reaching` (:711-727) already has one.
- **Change:** in `cell_boundary`, skip the source when `is_const(s)`. The project's tcheck
  copy needs the same edit (`formal/tools/tcheck/rules2.py` rule A, shard C's file).
- **Test:**
  ```
  cd formal/tools/kcheck && ./run.sh ipow 3          # rebuilds the route, runs tighten + tcheck
  python3 constsrc.py build/ipow/s3/pnr build/ipow/src/cells   # peak with / without tie-offs
  ```
  After the fix, tighten's umuli1 peak should equal the "peak(no const)" column (14226) and
  the rule-A row should pass. Then re-ratchet the T3/T9 sizes on the affected cells.

## 2. Rule A as coded: its κ limit, and the post-lag guard — OPEN
- **Proved** (`formal/lean/Formal/Core/Delay/CornerCode.lean`): the gate
  `max(int(0.2·t), 200) + SLACK` with SLACK = 0 (`tighten.py:1132`) is sound iff the local
  scatter κ ≤ 25/276 ≈ 0.0906 (`ruleA_code_iff`, `ruleA_code_tight`). It is unsound at 1/11
  (`ruleA_code_unsound_1_11`). With SLACK ≥ 1 the limit is 1/11 again (`ruleA_slack_sound`,
  `ruleA_slack_tight`). The worst pair is t_data 1004, t_req 1204, where the 200 ps floor sets
  the guard. Not covered: the float-to-floor step of `int()` is argued, not proved.
- **Unverified, seen in the code:** `tighten.py:1705-1712` adds `upstream_lag` to the margin
  and to `t_l` *after* `check_bundled` has computed the guard from the pre-lag `t_l`. So the
  guard is a fifth of the shorter path.
- **Change:** use SLACK ≥ 1, or exact division, if the project's κ may exceed 9%. Recompute
  `req_guard(t_l + upstream_lag)` after adding the lag, or justify why the lag is exempt.
- **Test:** `cd formal && ./check.sh Formal/Core/Delay/CornerCode.lean` (21 declarations). For
  the lag, add one tighten unit test with a bundled channel with `upstream_lag > 0` and
  `t_l ≥ 1005`, and assert guard == (t_l + lag) // 5.

## 3. Delay model for every margin: shared corner + scatter κ, and the κ each check needs — OPEN
- **Model** (`Formal/Core/Substrate/CornerNat.lean`, `Delay/Corner.lean`):
  - the die has one corner c ∈ [0,1];
  - each arc's nominal delay is (1−c)·FAST + c·SLOW;
  - each actual delay is within 1 ± κ of its nominal.
  Checking a bundling inequality at the FAST and SLOW endpoints with κ applied is then exact
  for every corner (`bundle_realizes`, `endpoints_sound_real`).
- **Proved, shard B** (`Formal/Cells/ConstraintsKappa.lean`, checked under Mathlib, 861de85):
  - `allOK_of_gen`: the closed-form check GenOK is sound. It is exact under H_DISJ + H_DIV
    (`allOK_iff_gen`).
  - `box_unsound_with_kappa`: the "box" check (every hi at SLOW_MAX, every lo at FAST_MIN, no κ)
    is **unsound for κ > 0**.
  - `one_corner_unsound_with_kappa`: checking each corner alone is also unsound for κ > 0.
  - `slow_only_unsound`: a SLOW_MAX-only check is unsound **even at κ = 0**.
  - `endpointNat_not_sufficient`: rounding to integer ps at the endpoints is not sufficient.
    Use the unrounded form.
- **Thresholds proved so far.** A κ measurement must beat each of these:

  | check | sound for κ ≤ | evidence |
  |---|---|---|
  | gcd_hw's 36 arbiters, all 18 conditions, literal FAST_MIN..SLOW_MAX | 16587/374773 ≈ **0.0443** (tight) | `OnGcdArbKappa.design_lit_safe`, `design_lit_tight`, gate level `design_gate_lit` |
  | the same, RT1/RT1b crediting the server path (H_SERVER_GRAPH) | ≈ 0.0802 | `OnGcdArbKappa.lit_srv_min` |
  | the same, conservative reading (data at FAST_MAX/SLOW_MAX, request at FAST_MIN/SLOW_MIN) | none: 5 rows on 3 arbiters fail at κ = 0 | `OnGcdArbKappa.cons_neg` |
  | link_arb A0 fork | safe 8/8 at 1/11 | `OnNetlistArbKappa` |
  | rig pin `urig.uenv1.u` (gcd_hw seed 5) | between 0.07 and 0.08 at the slow corner | measured, xevents5; `formal/notes/A-kapres.md` §3 |
  | tighten rule A as coded | 25/276 ≈ 0.0906 | §2 |
  | skew.py rule E | ≈ 0.199 | `Corner.ruleE_sound` (tight) |

- **κ is unmeasured on the current toolchain.** The earlier "κ ≥ 0.311" came from ring
  ratios taken against pre-`lut-perm-sink` SDFs. It measures that SDF bug, not silicon
  scatter (`formal/notes/A-kappa.md`, correction 10c4065).
- **Changes:**
  1. Replace every box or SLOW-only bundling check with the endpoint check
     `(1+κ)·ΣD_s + a ≤ (1−κ)·ΣR_s + b`, for s ∈ {FAST, SLOW}, on prjxray per-pin numbers.
  2. Until κ is measured, state every guardband result as "sound for κ ≤ x".
- **Test (board):**
  - Cheapest: commit the per-ring raw logs of the `ro_many` 128-ring run, then
    `python3 formal/tools-A/kappa/kappa.py rawlogs <dir> <pred.tsv>`.
  - Real test: rings with a shared body that splits into two tails, rejoined at a
    scan-selected LUT mux. Use ≥ 64 pairs per length class, 4 seeds and 2 temperatures, then
    `kappa.py pairs` (schema in `formal/tools-A/kappa/data/pairs_template.csv`).
  - The number to beat for gcd_hw's arbiters is 0.0443.

## 4. prjxray-db has inverted FAST tuples; xray_delay.py propagates them — OPEN
- **Finding:** `prjxray-db/zynq7/tile_type_BRKH_INT.json` gives 14 pips through the
  horizontal clock-region break (`NL1BEG0-2`, `NR1BEG0-3`, `SL1END0-3`, `SR1END1-3`) the tuple
  `[FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX] = [0.202, 0.105, 0.231, 0.312]` ns, i.e.
  FAST_MIN > FAST_MAX. These are the only inverted tuples in the zynq7 db.
  - `cells/gls/fid/xray_delay.py` sums the columns along a route. So every crossing raises an
    arc's FAST_MIN by 97 ps more than its FAST_MAX.
  - On gcd_hw R5 this gives 2-20 arcs per seed with FAST_MIN > FAST_MAX (d 20, 3 7, 4 8, 5 2).
    collatz has them too.
  - The SDF xray_delay writes is `(FAST_MIN:SLOW_MIN:SLOW_MAX)`, so the GLS "fast-min" corner
    is up to 97 ps per crossing **too slow** on those arcs. That is the unsafe direction for a
    min.
  - Formal side: our band reader read such a band as [lo, lo]. This is being fixed in shard A.
- **Evidence:**
  - `formal/notes/A-kapres.md` §1 (the data quirk, counts);
  - `formal/notes/A-kapres2.md` §2 (traced to BRKH_INT; WIP note, nothing claimed in Lean);
  - re-verified for this file by scanning the db: 28 inverted entries, i.e. 14 pips × 2
    directions.
- **Change:** in xray_delay.py, read each pip tuple as fast = [min(t0,t1), max(t0,t1)] (or
  flag it and take the hull), and fail loudly on any element with lo > hi.
- **Test:**
  ```
  python3 -c "import json;d=json.load(open('$PRJXRAY_DB/zynq7/tile_type_BRKH_INT.json'));print(sum(float(v[k]['delay'][0])>float(v[k]['delay'][1]) for p,v in d['pips'].items() for k in ('src_to_dst','dst_to_src') if v.get(k,{}).get('delay')))"   # 28
  awk -F'\t' 'NR>1 && $5+0>$6+0' arcs.tsv | wc -l   # xray_delay --arcs: col 5 fast_min_ps, 6 fast_max_ps; after the fix: 0
  ```

## 5. What the verified checker (tcheck) replaces, and its known front-end gaps — STATUS
- **Proved** (`Formal/Timing/Checker.lean`: `verdict_sound`, `cverdict_sound`, `pot_sound`):
  a tcheck PASS means that, for every run of the *extracted* netlist with each arc delay in its
  interval, data precedes the target by the setup.
  - tcheck implements rules A, E, F/Fc, H/Hc, I and J (J0/Jp/Jx). Jx credits a shared prefix
    exactly, `SharedPrefix.pot2_sound` under H_CLEAN_EDGE.
  - The extraction (graph, intervals, obligations) is untrusted Python.
- **Agreement on collatz/xorshift/ipow** (12 routes, `formal/notes/C-10n-kernels.md`):
  - 1661 of 1900 comparable rows agree.
  - Every disagreement is "project PASS, tcheck FAIL".
  - 210 of the 239 are band-only: they fail only with the 0.772/1.155 band applied per arc to
    prjxray numbers.
  - 0 rows fail at a fixed corner.
- **Use it to replace** tighten/skew's per-rule arithmetic once the front-end gaps below are
  closed. Until then, use it as a second opinion.

  | gap | effect | owner / status |
  |---|---|---|
  | constant tie-off sources in rule A | §1 | shard C rules2.py + tighten.py |
  | `extract.Prjx.split`: a driver leaving its slice through two site pins (O6 on B and BMUX) counts sink a's OUTMUX hop as shared and drops sink b's | 16 pairs on gcd_hw routes; Jx optimistic (seed 3 merge11 c2 421 vs 336 ps; seed 4 merge12.uarb2 353/235 vs 270/152; still positive); seed 2 merge10.uarb1 client 1 −75/−211 ps in C-10i/10j rows; B's re-proof (`OnGcdArbFix`) flips no corner verdict | shard B finding (JOURNAL-B 11:50/12:00); fix in shard C's C-10m, **not committed** |
  | DSP48E1 arcs have no prjxray model (77,778 fallback arcs on ipow) | ipow rule-A verdicts through the multipliers are SDF-band verdicts, not prjxray | open |
  | CARRY4 CIN nets fall back to the SDF band, also in the fast variant | mixes slow max into the fast corner (collatz s3 `uaddi0` −4 ps) | open |
  | first stages fed by a compute cell are "not audited" by rule I in both tools (audit: collatz64 rule I audits 12 of 34 stages) | unchecked obligation, not a pass | open in both |
  | rule J (tighten) uses a flat 124 ps LUT arc and no per-pin site-pin delay (up to ~0.5 ns) | audit: −260 / −38 ps under fast-early/slow-late mixing | proposed rule J' in `formal/notes/B-arb-a0fork.md` |

- **Per-pin delays:** checks fed from nextpnr's SDF miss site-pin delays. The difference
  between a C-element's input pin and its feedback pin is −468..+308 ps at the slow corner, and
  goes the unsafe way on ~46% of own-feedback pins (`formal/notes/A-events2pin.md`).
  Research's `xray_delay.py` now writes a per-pin, OUTMUX-charged SDF for the GLS. **Change:**
  pass that same file to tighten.py/skew.py (both take the SDF as argv[1]) and to tcheck.
- **Test:**
  ```
  cd formal/tools/kcheck && ./run.sh <kernel> 1 2 3 4    # route + project rules + extract + tcheck + compare
  # results/<kernel>/summary.txt, disagree.tsv; guide: formal/notes/C-howto-new-kernel.md
  ```

## 6. GLS: early edges in sample-at-fire primitives — FIXED under GLS_MODEL=fid (78de9c2; default build still SAF)

**Status 2026-10-29 (6524fa3, notes/A-fid3.md):** CARRY4 and SLICE_LATX are per-pin transport under fid; acceptance values met (O0 1223/1233/1423, LQ 3100/3110/3160); multi-pin CARRY4 check 60/60 (default model 2/60, so the check can fail). DSP48E1 still SAF.

- **Finding (proved):** an iverilog `-gspecify` module path is "sample at fire".
  - A change at t schedules an update at t+d, which copies the function value at fire time.
    Nothing is cancelled.
  - So an edge that follows an earlier change within d comes out early: `SAF.saf_early`,
    `saf_not_transport`, `chain_early`.
  - Exact condition for SAF = transport: `saf_eq_delay_iff`. A run with no unfaithful fire
    equals the transport run: `net_eq_delay_of_faithful`.
  - The audit confirmed this (6/6 random traces SAF, 0/6 transport, 0/6 inertial).
- **Fixed for LUT and MUXF:** under `GLS_MODEL=fid` (5567170) these are per-pin transport. They
  match Lean's per-pin transport on 60/60 + 60/60 traces (`formal/notes/A-gls-compare-2.md`).
- **Still SAF:**
  - the default build (`prims.v` `SLICE_LUTX` specify paths), which is what the board-queue
    GLS runs used unless `GLS_MODEL=fid` was set;
  - **CARRY4 and SLICE_LATX even under fid.** Re-run for this file against the research tip
    (prims.v / fid_core.vh md5 equal to the 5d535d7 copies): O0 rises at 1223 ps, 23 ps after
    its cause, through a 223 ps arc. Carry chains are the bundled data cones (adders,
    comparators).
- **Change:**
  - `FID_CARRY4`: for each output Oi/COi, keep a transport copy of each support pin delayed by
    (that pin's arc to that output − 1). Evaluate the existing equations on the copies and send
    each output through `FID_SAMPLE`.
  - The same for `SLICE_LATX`: per-pin copies of D/CK/CE/SR at TCKQ − 1, then the zero-time
    latch function.
  - Make fid (or plain transport LUTs) the default for any run quoted as a margin.
- **Test:** `sh formal/tools-A/glsdiff/run_all.sh` (~3 min; copies research prims into `src/`).
  Acceptance: `tb_carry_saf` prints O0 at 1223, 1233 and 1423 (now: 1223 only); LQ at 3100,
  3110 and 3160 (now: 3100 only).

## 7. GLS: X handling of latch and flop — OPEN

**Status 2026-10-29 (6524fa3):** unchanged in both models (flop reads x on SR/CE as 0; latch X pessimistic). New: `tb_f3_kleene_ff` now codifies the X-hiding flop as correct. Tested fix: `formal/tools-A/glsdiff3/run-1029/patch/prims_x.diff` (L1-L3 = 0, F1/F2 = x in both models; run_f3.sh passes except its negative-control sed, whose target line is gone; retargeted mutation in notes/A-fid3.md §4).

- **Finding** (re-run for this file, default and fid identical; `tb_seq_x.v`):
  - `SLICE_LATX` is pessimistic. Cases L1-L3 give x where the Lean `LDCE_INIT` gives 0.
  - `SLICE_FFX` hides X on SR and CE. Cases F1 and F2 give 1 where the result is x.
  - The latch pessimism hides nothing; the flop optimism hides a reset/enable glitch.
- **Change** (`prims.v`):
  - latch:
    ```
    if (CK === ~GHIGH || CE === 1'b0) q = q;
    else if (CK === GHIGH && CE === 1'b1) q = D;
    else q = (q === D) ? q : 1'bx;
    ```
    and for SR = x, `q = (SRVAL === qn) ? SRVAL : 1'bx`.
  - flop, at posedge CK:
    ```
    nv = (SR===1) ? SRVAL
       : (SR===0) ? (CE===1 ? D : CE===0 ? Q : (D===Q ? Q : 1'bx))
       : (((CE===1 ? D : CE===0 ? Q : (D===Q ? Q : 1'bx)) === SRVAL) ? SRVAL : 1'bx)
    ```
- **Test:** `run_all.sh` as in §6. `CASE L1..L3` should print 0, and `F1`, `F2` should print x.

## 8. GLS: FID_RESOLVE decides at the wrong point; scatter is unbounded — OPEN

**Status 2026-10-29 (6524fa3):** unchanged; the 50% point is exactly TLOOP − WIN/2 (349 ps at TLOOP 424). Proposed change: `formal/tools-A/glsdiff3/run-1029/patch/fid_core_centre.diff` (`+META_CENTRE_PM`, default 500 = TLOOP/2), tb_f3_meta at DT = TLOOP/2, use `+META_X=1` for evidence runs (the involution loop emits a 13-81-edge pulse train while resolving; the GLS holds a clean value). TAU = 150 ps is not pessimistic under involution (TAU_eff 0.5-7 ns in a Float transcription, not a theorem). Only the board settles the centre (hw/arb_mtbf skew sweep + q toggle count). Scatter still unclipped Gaussian.

**Also (2026-10-29, `formal/lean/Formal/Core/Delay/GLSResolve.lean`, proved on bd_c2's loop, binary, xmode=0, every seed/TAU; iverilog cross-check 480/480 pulses):** (1) `fid_core.vh:29` ("the node never left") holds only for the final value: a rejected runt is emitted full-swing to fanout (`rejected_runt_emitted`), and a commit with trp > 0 gives fanout two rising edges for one set (`commit_gap`). (2) `fid_core.vh:36-37` ("applied late, not lost") is false: after a non-committing runt, a following pulse of width ≥ TLOOP that ends inside the ignore window is lost forever (`follow_lost`), where the transport/C-element model forces O = 1. (3) Every resolver run settles within 3 edges; the transport loop at the same point can oscillate forever (`hides_oscillation`). (4) A run that printed no RUNT/META line equals the plain transport loop at that delay point, so the C-element theorems cover exactly those runs. Change: report every emitted runt in evidence runs, treat any RUNT/META line as a failed run, and fix the two comments.

- **Finding:**
  - `fid_core.vh:28,82` splits at `delta = p − (TLOOP − WIN/2)`, which is 349 ps of a 424 ps
    loop (measured).
  - A Float run of Lean's involution OR-loop recurrence decides at about TLOOP/2 (212-246 ps
    for τ = 40-200). This is a computation, not a theorem. Lean proves only that the critical
    gap lies in about (9, 424) ps.
  - The audit agrees that the window is pessimistic: a request 360 ps later still wins 75/200.
  - The comment "rejected: the node never left" (`fid_core.vh:29`) is wrong: the runt reaches
    fanout at full width.
  - `GLS_SCATTER(_REGION)` factors are unbounded Gaussians, so a scatter run tests delays
    outside every κ regime of §3.
- **Change:**
  - `delta = p − TLOOP/2 + noise` (asymmetric arcs: `p − TLOOP·tf/(tr+tf)`), exposed as
    `+META_CENTRE=`;
  - fix the comment;
  - clip the scatter at a stated κ, or say "unclipped" wherever scatter results are quoted.
- **Test:** `run_all.sh` (the `S <ps>` sweep). With r2 360 ps late, r1 should win about 200/200.

## 9. What a passing GLS run implies — OPEN (wording + run plan)
- **Proved** (`Formal/Core/Delay/GLSPass.lean`, 263 declarations with deps):
  - A SAF GLS pass implies the property only if silicon is SAF at exactly the annotated delays
    (`gls_pass_of_saf_silicon`).
  - XOR skew (`ce_skew_124`), XOR3 capture (`ce_capture_124`) and `bd_c2` with feedback
    (`ce_c2_124`) each pass at 124 ps and fail at another delay in [45,124] ps, under transport
    or under inertial.
  - A faster LUT can fail where the slow arc passed, so the slow column is not a conservative
    corner.
  - Sufficient condition: for acyclic monotone LUT cones with rising inputs, two runs (all
    FAST_MIN, all SLOW_MAX) bound every behaviour in the band (`gls_mono_bundle`). Not
    covered: per-pin arcs, X, feedback (so not gcd's control).
- **Annotated vs baked:** `annotated_ne_baked` proves that the two builds differ on short wire
  pulses. The audit rates "identical timestamps" OVERSTATED. Both claims are still in
  `cells/gls/prims.v:47` ("identical delays -- proved by diffing a run") and
  `cells/gls/build.sh:104-106`.
- **Change:**
  - Report a GLS margin only from paired FAST_MIN and SLOW_MAX runs. The research branch does
    this now for BQ#3; make it the rule.
  - Never read a pass on a feedback cone as a band result.
  - Qualify the two comments: "identical on the gcd run, which has no wire pulse shorter than
    its wire delay".
- **Test:**
  `cd formal && ./check.sh Formal/Core/Trace/Discrete.lean Formal/Core/Delay/SAF.lean Formal/Core/Delay/GLSPass.lean`.

## 10. GLS cannot show runts on loops; the faithful channel is involution — PARTLY FIXED
- **Proved:** inertial paths remove pulses narrower than the arc (`Inertial.inertialRD_pulse_short`,
  `noShort_of_inertialRD`). The involution channel shrinks them continuously
  (`Involution.pulseWidth_small`).
- **Status:** fid's transport LUTs pass runts; FID_RESOLVE then decides them (§8). The default
  build still drops them.
- **So:** a default-build pass is no evidence of runt-freedom for any C-element, latch or
  arbiter loop.
- **Test (board):** a pulse-width sweep through a LUT chain with a TDC, to fit δ↑/δ↓
  (`formal/notes/A-delay-involution.md`).

## 11. Add a rule: C-element own feedback faster than every neighbour loop; items to test on gcd_hw — OPEN
- **Proved:** `FbBound` (shard C, `Formal/Net/MullerTimed*`). For every C-element, the
  feedback-wire hi must be < the lo-sum of every loop through a neighbour back to its inputs
  (strict). No rule checks it today. `xaudit` flags it independently
  (`formal/tools-A/xaudit/run_all.sh`, `pipe3_slowfb`).
- **On gcd_hw R5** (checker results, not counter-traces):
  - At each single corner the obligation holds on every seed (xevents7/8: slow and fast CLEAN
    on d/3/4/5).
  - With skew.py's own band (one die anywhere in [0.668, 1.0] × slow max), Events8 fails ENTRY
    on three arbiter guard pins on seed d: `ucontrol_merge3.uarb1.ua2` pin0 −51 ps,
    `ucontrol_merge3.uarb1.ua1` pin0 −94, `ucontrol_merge2.uarb1.ua2` pin0 −68 (JOURNAL.md
    12:38).
  - The rig's `urig.uenv1.u` own-feedback fails at κ ≥ ~0.08 (seed 5; §3) and at the
    guardband on collatz seed 5 too (−9 ps, K2).
  - One concrete runt reproduces with per-element [fast_min, slow_max] bands: 9 ps in
    `ucontrol_merge4.uarb1.ua2`, seed d, answer still correct
    (`formal/tools-A/xaudit/gcd/results/`).
- **Change:** add the FbBound gate to tighten.py. Use prjxray per-pin numbers, with slow-max
  feedback and fast-min loops, scaled by (1±κ) as in §3. Re-time the rig's `uenv1`.
- **Test:** `sh formal/tools-A/xaudit/events5/run5.sh` (event checker on the 4 R5 nets), and
  the gate's own unit test with `pipe3_slowfb` from xaudit as the failing case.

## 12. bd_arb: two header claims to correct — OPEN
- **Proved** (`Formal/Core/LutAudit.lean`):
  - `arb_tie_from_idle_hazard`: a same-sense tie is a static hazard on q. `cells/rtl/bd_arb.v:52-53`
    still says "resolved deterministically".
  - `arb_grant_near_tie_runt`: the losing grant can pulse without metastability.
    `bdc/emit.py:423` drives `won[k] = g2[k] | ack` straight into `index`.
- **Change:**
  - fix the header;
  - add same-sense near-ties to the MTBF experiment (`cells/verify/MTBF.md`);
  - check that nothing samples `index` inside the grant-runt window.
- **Test:** `cd formal && ./check.sh Formal/Core/LutAudit.lean`.

## 13. toolchain.sh cannot see missing runtime libraries — OPEN
- **Finding:** a restored toolchain cache lacked libtcl8.6 and boost 1.83. `toolchain.sh`
  greps the binaries and passed 9/9 anyway. Shard C hit the same failure (JOURNAL-C 11:46).
  `cells/verify/toolchain.sh` has no `ldd` check.
- **Change:** add `ldd "$NEXTPNR" "$YOSYS" | grep 'not found' && fail`, plus one smoke run
  (`yosys -V`).
- **Test:** run toolchain.sh with `LD_LIBRARY_PATH` pointed away from libtcl; it must fail.

## 14. Hypotheses only the board can test
Graded list: `formal/notes/A-substrate.md`; fidelity table: FEASIBILITY.md.
- κ on path differences (§3). The number to beat is 0.0443.
- `H_mux_kleene`: a LUT mux with a mid-rail select and equal data passes the data. Test: a
  masked-pin toggle into a fabric edge counter.
- Involution δ↑/δ↓ per LUT pin and edge (§10).

## 15. Already fixed on the research branch (re-check only)
- **SDF triples are (FAST)(SLOW), not rise/fall.**
  - Fixed: e239db7 (journal), 801db02 (gen.py column selection), 5d535d7 (`bd_prims_sim.v` at
    one corner; tb_arb_overlap/tb_ctl/tb_arb re-asserted). The audit had rated "rise and fall
    differ 2.2×" REFUTED. Its re-check of 5d535d7 is still PENDING (audit row 60).
  - Left on the formal side: the ArbHeldTimed numeric instances (shard B), not research.
- **Rule F in-flight term.** 7a8199b adds "latest ripple-input arrival − fastest side tap". It
  includes the head stage through `late[ip]` (`tighten.py:616-640`). It should cover the
  `bd_delay_gated` head hop that Events5 measured at −365 ps (seed d `ushli0`) and −726 ps
  (seed 3 `uselect1`) on mixed dies.
  - Not yet re-run on routes, by either branch.
  - Test: rebuild gcd_hw R5 seeds d and 3, run tighten rule F, and compare with
    `formal/tools-A/xaudit/events5/` rows.
- **Slice OUTMUX/FFMUX hops in the fid delay calculator:** 7dc5dde (audit r5 row).
- **Dropped: LUT mux-tree order in prims.v** (A6 at the leaves). It has no logic, X or timing
  effect in the GLS (internal wires are zero-delay; audit CONFIRMED; `LutTree.evalTree_swap`).


## 16. iverilog RAMB18E1 stand-in has no hold check and does not poison — OPEN (2026-10-29)

`cells/sim/bd_prims_sim.v`'s RAMB18E1 uses one 2454 ps CLK->DO point (prjxray band: fast 585..1098, slow 1353..2454 ps), has no hold check, and on a setup violation only prints, though its header says it poisons the output. `formal/lean/Formal/Core/Prims/Ram.lean` (A, checked) gives the windows (slow corner only in prjxray: ADDR [-566,+360], WE [-532,+197], DI WRITE_FIRST [-737,+667] ps) and shows a DI/WE change inside its window gives X. Change (research GLS, since cells/ is frozen): band the CLK->DO arc, add hold checks, set DO to X on any violation. Only testbenches and board rigs use bd_mem today.
