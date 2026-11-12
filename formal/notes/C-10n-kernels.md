# C-10n: the verified timing checker on collatz, xorshift and ipow (generic per-kernel runner)

Shard C, probe 10n, 2026-10-27. Python and shell only; no new Lean. The compiled checker is
tcheck (C-10e/10g/10h), used unchanged.

**STATUS: DONE.**
- `formal/tools/kcheck/run.sh` builds the routes of any compiled kernel with the project's own
  flow, runs the project rules and tcheck, and writes a row-by-row comparison.
- It has been run on collatz, xorshift and ipow: 4 seeds each, 12 routes, every one placed and
  routed.
- Every disagreement is explained. None is a predicted silicon failure.
- One finding is about the project's own rule A (a false path through the constant tie-off
  drivers). It explains the only project-rule violation seen on these 12 routes.

## Verdict

**Coverage.** tcheck ran on 12 routes: 2,664 / 2,970 / 3,186 instances per route (collatz,
xorshift, ipow). That gives 2,276 project rows: 1,900 comparable, of which 1,661 agree and 239
disagree; 376 have no counterpart on one side.
- **Project rules on the same routes:**
  - rules E and J: clean on all 12;
  - rules A/H/I/F: clean on 11 of 12;
  - the exception is ipow seed 3, rule A on `uut.umuli1`: -59 ps guarded, +3484 raw.
- **Agreement:** every disagreement is "project PASS, tcheck FAIL". There is no "project FAIL,
  tcheck PASS" row. The one project FAIL (ipow s3 umuli1) is also a tcheck FAIL, so that row
  agrees.
- **Disagreement classes, in order of size:**
  1. **band-only** (210 of the 239 disagreeing rows). The unguarded prjxray fast and slow corners both pass. The
     failure exists only once the project's 0.772/1.155 band is applied per arc to prjxray
     numbers. This is the class C-10h found on gcd_hw. It is larger here, mostly in rule I.
  2. **spread-only** (10 rows: xorshift I 8, ipow I 1, ipow A 1). No fallback arc is involved,
     and the row fails at an unguarded corner. It passes when every arc sits at the same end of
     its prjxray interval (all at fast_min, all at fast_max, all at slow_min, or all at
     slow_max; `pointcheck.py`). The failure needs request arcs at slow_min while data arcs sit
     at slow_max in one corner: independent within-corner spread with no on-die correlation.
     That is the corner model's κ question, not a routing defect. Example: xorshift s2 I
     `ulink_n_falseResult_1` stage 1:
     - SDF: +893;
     - tcheck slow interval: -279;
     - every fixed point: +253..+725.
  3. **frontend-gap(const)** (18 rows: ipow A 15, xorshift A 3). These rows come from a false
     path the project rule and tcheck both contain; see the next item.
  4. **frontend-gap(fallback)** (1 row: collatz s3 A `uaddi0`, fast -4 ps). The data critical
     path crosses three CARRY4 CIN nets that have no prjxray number. They fall back to the SDF
     band (84..128 ps each) even in the fast variant, so they mix nextpnr's slow-max number into
     the fast corner.
  - **corner-fail** (fails even at a fixed point, no fallback, no constant source): **0 rows.**
  - **project-only:** 0 rows.
- **Finding: rule A includes the constant tie-off drivers.** `tighten.cell_boundary()` does not
  skip `$PACKER_GND_DRV` / `$PACKER_VCC_DRV`. Rule A's bundled pairing (`check_bundled`) then
  launches a data path at the tie-off driver, and its 3-5 ns route becomes the "latest data".
  - A constant never switches, so that path is false.
  - It sets the rule-A peak of 1 to 4 compute cells on **every** route, overstating it by
    0.9-4.2 ns (`results/constsrc.tsv`):
    - collatz `uselect0` (VCC);
    - xorshift `ucmpi0`;
    - ipow `ucmpi2`, `umuli1`, `uselect0`, `ushrsi0`.
  - It is the whole cause of ipow s3's rule-A violation. With the tie-off removed, the same
    tighten code gives umuli1 a peak of 14226 instead of 17715 ps and a margin about 4.2 ns
    larger.
  - The error is on the conservative side: it over-sizes delay lines and costs speed, never
    safety. But any sizes ratcheted from rule A asks on those cells (T3/T9) may be longer than
    they need to be.
  - tcheck's rule A mirrors `cell_boundary`, so it carries the same false path. In its prjxray
    variants the tie-off arc falls back to the SDF band, which mixes corners and makes the fast
    variant fail.
  - Fix for the project: skip `is_const` sources in `cell_boundary`, as `starts_reaching`
    already does. Fix for tcheck: the same in rules2.py's rule A. Neither file is mine; both
    are reported here, not edited.
- **The OUTMUX question.** The main verdicts above use tcheck's Python front end at git
  `7ad3b5e`, which predates C-10m. That front end already charges the driver-side site hop
  (a5lut→amux and the like, C-10h) on every interconnect arc.
  - A second pass used the front end at `24e47ca`, which includes C-10m's work in progress: the
    Jx shared-prefix split when the two sinks leave the LUT through different output pins.
  - That pass changed **only Jx rows**: 4 / 4 / 5 of 16 (collatz / xorshift / ipow), margins
    moved by -278..+172 ps; `results/<k>_outmux/prepost.tsv`.
  - One verdict flipped: collatz s2 `ucontrol_merge0.uarb1#2` Jx went from PASS to FAIL
    (`results/collatz_outmux/disagree.tsv`).
    - Before: fastG +45, slowG +123.
    - After: unguarded fast +175 and slow +421, but fastG -62 and slowG -121, which are now
      equal to J0.
    - The two sinks leave the LUT through different output pins, so there is no shared prefix
      to credit. The flip is band-only.
  - If C-10m's final fix differs from `24e47ca`, rerun with
    `KCHECK_FRONT_REV=<rev> KCHECK_TAG=<tag> SKIP_ROUTE=1 run.sh <k>`.

## Agreement per rule (4 seeds; agree / comparable rows; tcheck verdict = PASS at fastG and slowG)

| rule | flavour | collatz | xorshift | ipow | gcd_hw (C-10h, for scale) |
|---|---|---|---|---|---|
| A | | 22/40 | 22/44 | 25/44 | 199/200 |
| E | credited E | 69/72 | 92/96 | 89/96 | 465/472 |
| F | F / Fc | 28/28 | 24/28 | 28/28 | 113/116 |
| H | H (chain) | 104/104 | 106/112 | 123/132 | 630/632 |
| H | Hc (cert) | 116/116 | 123/132 | 134/148 | 630/632 |
| I | | 36/52 | 12/64 | 36/72 | 300/300 |
| J | J0 / Jp | 15/16 | 16/16 | 16/16 | 57/72 |
| J | Jx (exact shared) | 16/16 | 16/16 | 16/16 | 71/72 |

"Not comparable" rows (`-`) are links that tighten reports as "not audited" (first stages of a
`many` link: no upstream controller for rule I) and have no tcheck instance either. The same
was true on gcd_hw.

**Why the agreement is lower than on gcd_hw.** The routes and data are different, but the main
reason is that these three kernels were *ratcheted* by the research branch: the delay sizes
were tightened until the project's own guard was just met (T3/T9). A design sized to one guard
model fails a stricter one:
- tcheck's band charges 0.772 on every request arc and 1.155 on every data arc, both on prjxray
  numbers;
- on rule I's long handshake round trip that costs about 1 ns;
- tighten's own rule-I guard is 312-621 ps on the disagreeing xorshift rows.

gcd_hw R5 had more headroom.

## Disagreement mechanisms, with one traced example each (`diag.py` on the instance)

- **band-only, rule I:** xorshift s1 `ulink_n6` stage 1.
  - Project: raw +1319, guarded +850.
  - tcheck: sdf +1319 (equal to tighten's raw), fast +194, slow +263, fastG -511, slowG -1277.
- **band-only, rule A** (a long delay-line request against a carry-chain datapath): collatz s2
  `uaddi0`.
  - The request is a 29-link bd_delay chain. Each LUT is 124 ps in the SDF but 45..56 ps at prjxray
    fast, so the request side shrinks about 2.5x at the fast corner.
  - Margins: fast +896, slow +3945, fastG -1776, slowG -2081.
- **spread-only:** see the Verdict.
- **frontend-gap(const):** xorshift s3 `ucmpi0`.
  - The data critical path runs `$PACKER_GND_DRV/Y` → `ucmpi0.$abc$3913/A1`, an SDF arc of
    5205 ps.
  - tighten's peak is 9467 = tcheck's sdf data latest, exactly.
  - Without constant sources the peak is 4437 + lag, and the project margin rises from 1439 to
    about 6400.
- **frontend-gap(fallback):** collatz s3 `uaddi0` (see the Verdict).

**Fallback census per route** (identical on all 4 seeds of a kernel; `obl.json` `fallback_kinds`):

| | collatz | xorshift | ipow |
|---|---|---|---|
| arcs with prjxray numbers | 17,127 | 11,542 | 14,444 |
| arcs falling back to the SDF band | 2,153 | 1,752 | 80,698 |
| of which constant-driver nets (never switch) | 1,859 | 1,655 | 2,622 |
| of which F7/F8 select nets | 196 | 4 | 106 |
| of which LUT-pin nets with no prjxray route | 82 | 80 | 187 |
| of which CARRY4 CIN | 14 | 11 | 3 |
| of which DSP48E1 cell/pin arcs | none | none | 77,778 |

The front end has no DSP48E1 model, so on ipow any obligation through a multiply is graded
almost entirely by the SDF band: 99% of the arcs of the umuli1/uselect0 rule-A instances fall
back. **ipow's rule-A verdicts through the DSPs are not prjxray verdicts.**

## Routes (nextpnr fingerprint and inputs)

- **Toolchain:**
  - `cells/verify/toolchain.sh` reported 9/9 ok before every route;
  - nextpnr-xilinx `0.9.2-100-gbfdeaf7c`, sha256 `9c732bc6303458df`;
  - yosys 0.62 (`7326bb7d6`).
- **Seeds:** NEXTPNR_SEED 1, 2, 3, 4 for each kernel. All 12 placed and routed. flow.sh exited
  0 with every gate PASS: fracture, fasm_audit, BUFG, SETUPHOLD, zero_arcs.
- **Design:** `cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir` → `bdc/emit.py`
  (soak top, fork fusion on, cap 4, the defaults) → `cells/flow.sh`. BD_DSP=1 and BD_RLOC is
  flow.sh's default.
- **Sizes**, read from `origin/claude/research`; every macro is referenced by the emitted top:
  - collatz `collatz_sizes_T3.vh` (blob 3e55aefc, 42 macros);
  - xorshift `xorshift_sizes_T3.vh` (9a9008d4, 47);
  - ipow `ipow_dsp1_sizes_T9.vh` (3c6a8aa1, 52).

  These are the size sets the research journal reports as "every audit + routed GLS clean on 8
  seeds" (collatz/xorshift 21:30/01:30, ipow 23:25), without BDC_LINK_FASTFALL.
- **Source tree:** `cells/` and `bdc/` from this branch's HEAD at the time (`7ad3b5e`; `bdc/` is
  identical to the research tip).
- **--freq:** `cells/flow.sh` passes no --freq, so kcheck patches its **private exported copy**
  (one line: `--freq 100 --timing-allow-fail`; pnr.log confirms "target frequency 100.00 MHz").
  - Control: collatz seed 1 re-routed with the unpatched flow.sh produced a byte-identical SDF
    and FASM.
  - These designs have no clock, so --freq changes nothing. These routes are what flow.sh
    produces for those seeds either way.
- **Size and run time:** LUT sites 1713 / 1019 / 1484 (ipow also has 6 DSP48E1). Each route
  took about 3-6 min with 2 nextpnr jobs at once on a shared 4-core machine. Each check
  (extract + tcheck + rules) took about 2-8 min.
- **No research route was available.** Its SDFs were not on disk in this container, so every
  route was rebuilt. ipow T9 was validated by the research on seeds 29-36, so seed 3's rule-A
  violation is on a route the research never audited.

## What checks (exact commands)

    cd formal/tools/kcheck
    ./run.sh collatz 1 2 3 4        # toolchain.sh; tcheck snapshot + toy/cert self-tests;
    ./run.sh xorshift 1 2 3 4       # routes (2 at a time); project rules; extract + tcheck;
    KCHECK_FRONT_REV=7ad3b5e ./run.sh ipow 1 2 3 4    # compare; pointcheck; summary
    SKIP_ROUTE=1 KCHECK_TAG=outmux KCHECK_FRONT_REV=24e47ca ./run.sh <k> 1 2 3 4   # C-10m WIP pass
    python3 prepost.py <k> outmux   # before/after table (results/<k>_outmux/prepost.tsv)
    python3 constsrc.py build/<k>/s<seed>/pnr build/<k>/src/cells   # rule-A constant-source diagnostic
    cd build/tcheck_snap && FORMAL_SLOT_CWD=$PWD ../../../../slot.sh lake env lean test/Axioms.lean
        # -> results/axioms.txt: all 12 theorems [propext, Classical.choice, Quot.sound]

The tcheck binary was built from a snapshot of `formal/tools/tcheck`'s Lean package:
- `sync.sh --check` passed on the original before the snapshot was taken;
- source hash `418060dcc58ef84d` (Main.lean + Tcheck/ + Formal/);
- the toy and cert self-tests pass.

Since then `24e47ca` changed only the documentation of `Formal/Timing/Checker.lean` (the
exactness qualifier), so the binary is the current checker.

## Files (all mine)

| file | what |
|---|---|
| `formal/tools/kcheck/run.sh` | the pipeline (see the howto) |
| `formal/tools/kcheck/route.sh` | one route: exported copy, emit, flow.sh with --freq patched in the copy |
| `formal/tools/kcheck/check.sh` | project rules + extract + tcheck + comparisons for one route |
| `formal/tools/kcheck/kernels.tsv` | kernel → MLIR, sizes, BD_DSP |
| `formal/tools/kcheck/compare2k.py` | **copy** of `tcheck/compare2.py`: reads one route dir; adds the deciding instance's fallback count. Logic unchanged |
| `formal/tools/kcheck/summarize.py` | per-kernel tables and the disagreement classes |
| `formal/tools/kcheck/pointcheck.py` | fixed-point margins of the disagreeing plain-DAG rows (spread-only vs corner-fail) |
| `formal/tools/kcheck/constsrc.py` | rule-A peak with and without constant tie-off sources (tighten's own code) |
| `formal/tools/kcheck/prepost.py` | before/after table for two front ends |
| `formal/tools/kcheck/results/{collatz,xorshift,ipow}{,_outmux}/` | summary.txt, agree/disagree/rows/routes/pointcheck.tsv, toolchain.txt |
| `formal/tools/kcheck/results/constsrc.tsv`, `results/axioms.txt` | the rule-A finding table; axiom audit |
| `formal/notes/C-howto-new-kernel.md` | the command-by-command guide (PROGRAM goal 3) |

Nothing outside these paths was edited. `formal/tools/tcheck/` is called read-only: the Python
front end is frozen into `build/tools/front_*` by `git show <rev>`, and helper directories are
symlinked. Large artefacts stay in `kcheck/build/`, which is git-ignored: routes, obl.tc.gz,
logs.

## Fidelity and what this does NOT show

- **What a tcheck PASS means** (proved, `verdict_sound` / `cverdict_sound` / `pot_sound`): for
  every run of the *extracted* netlist with each arc's delay in its interval, data precedes the
  target by the setup.
  - The extraction is untrusted: graph, intervals, obligations and phase rules.
  - The intervals are prjxray-db + Elmore under H_ONE_CORNER, with the band in the G variants
    and fallback arcs at the SDF band (H_FALLBACK_BAND).
  - A tcheck FAIL is not a counterexample run. The window is exact only over a free choice of
    cell functions (Checker.lean's corrected docstring), and the prjxray within-corner
    [min, max] is applied per arc independently.
- **Rows mirror the project rules (A/E/F/H/I/J + W/R/Rc) only.**
  - The gcd_hw capstone rows (rules10k/10l: X/Xi/Z/Fd/K) are gcd_hw-specific and were not run.
  - No end-to-end correctness claim is made for these kernels. The token-level ipow theorem
    (C-8v) is separate and not linked to these routes.
- **No silicon or GLS evidence was produced here.** "spread-only" rows are unresolved until the
  corner model's local scatter κ is measured. Rows through DSP48E1 (ipow) are SDF-band rows.
- **These are 4 placer seeds per kernel**, all from one source revision. The routes are samples.

## Surprises

- **The project's rule A times a constant net** on every route of all three kernels (above).
  This is the only cause of the single project-rule violation seen here.
- **--freq does not change a route** of these clockless designs (byte-identical SDF/FASM). The
  CLAUDE.md rule is harmless here, but it is not what makes these numbers meaningful.
- **Rule I is where tcheck's band bites hardest** on ratcheted kernels (xorshift: 12 of 64
  comparable rows agree). The project rule-I guard is a fraction of the data path only. tcheck's
  band is applied to the request round trip as well. Which one is right is a guard-band
  question that only the corner model with measured κ, or the board, can settle.
- **ipow's rule-A rows through the multiplier are 99% fallback.** A DSP48E1 timing model from
  prjxray-db is the next front-end gap to close for that kernel.
- **A sandbox incident, now fixed.** A first ipow pass silently used a newer, WIP front end,
  because the lead committed C-10m's WIP between kernel runs and `run.sh` snapshotted "HEAD".
  It was discarded and rerun pinned to `7ad3b5e`, and every pass now records its front-end rev
  and hash in `results/<k>/toolchain.txt`.

## 10m correction (2026-10-29, probe C-10m)

The numbers above stay as they were; the rows they describe are **superseded** by the
corrected front end below. Full tables: `formal/tools/kcheck/results/<k>_m10/` and
`formal/notes/C-10m-outmux.md`.

**What changed in tcheck's front end** (C-10m, `formal/tools/tcheck/`):
1. `rules2.py` rule A drops the constant tie-off starts (`$PACKER_GND_DRV`/`$PACKER_VCC_DRV`)
   before the common/bundled decision. Reason: a constant never switches, so no run launches a
   transition there; under 10a's `Run` semantics a node with no changing input never changes,
   so this is the circuit's behaviour, not a weakening (the false path this note found).
   `TCHECK_KEEP_CONST=1` restores the old start set for before/after tables only.
2. `extract.Prjx.split` (Jx): two sinks that leave one LUT through different site pins (A..D
   direct and AMUX..DMUX) share nothing; each side carries its own OUTMUX hop. This is the
   `24e47ca` work-in-progress pass above, now final.
3. The driver-side OUTMUX hop itself was already present at `7ad3b5e` (C-10h). C-10m checked
   it arc by arc against the auditor's independent model (C-10m-outmux.md section 1). That
   includes collatz s2: all 17,800 common arcs agree within 11 ps once the xMUX/xMUXL hull is
   set aside (`TCHECK_HOP_NOL=1`). With the hull, 867 arcs are higher, by at most 34 ps at slow
   max.

**Routes:** all 12 rebuilt with `route.sh` (nextpnr sha256 `9c732bc6303458df`, toolchain.sh
9/9 ok) are byte-identical (SDF sha) to the routes above, so every row compares one to one.
Run: `SKIP_ROUTE=1 KCHECK_FRONT_REV=worktree KCHECK_TAG=m10 KCHECK_JOBS=1 ./run.sh <k> 1 2 3 4`
(front-end hash `73a44366152685fe`, tcheck snapshot `33c9d370d363b469`, toy/cert self-tests ok).

**Row changes, final front end against the `24e47ca` pass:** only rule-A rows of the cells whose
boundary held a tie-off start (collatz `uselect0`; xorshift `ucmpi0`; ipow `ucmpi2`, `umuli1`,
`uselect0`, `ushrsi0`); every other row (E/E0, F/Fc, H/Hc, I, J0/Jx/Jp) is identical. Against
`7ad3b5e` (the main tables above) the Jx moves of the `24e47ca` pass are added (4/4/5 of 16).

| kernel | A agree (before -> after) | A verdict flips (tcheck) | disagreement lines (before -> after) |
|---|---|---|---|
| collatz | 22/40 -> 25/40 | uselect0 FAIL->PASS on s1, s3, s4 | 42 -> 40 (Jx flip +1, uselect0 -3) |
| xorshift | 22/44 -> 26/44 | ucmpi0 FAIL->PASS on all 4 seeds | 105 -> 101 |
| ipow | 25/44 -> 33/44 | ucmpi2, ushrsi0 FAIL->PASS on all 4 seeds | 92 -> 84 |

(Disagreement lines count one line per rule flavour, as disagree.tsv; E and E0 both appear.)

- **"frontend-gap(const)" is gone** (18 lines: ipow 15, xorshift 3). Those rows now either
  agree (PASS/PASS) or, on ipow `umuli1`/`uselect0`, still fail in tcheck for a different,
  stated reason: their instances are 99.7% DSP48E1 fallback arcs (no prjxray DSP model), now
  classed `frontend-gap(fallback)` (7 lines).
- **ipow s3 `umuli1`** (the one project-rule violation, -59 ps guarded): tcheck's `sdf` margin
  without the tie-off start is +6973 ps (it was +3484, equal to tighten's raw, while the
  tie-off was kept). The project FAIL and tcheck FAIL still "agree" in the table, but for
  different reasons: the project's FAIL is the false path; tcheck's is the DSP fallback in its
  prjxray variants (fast -5279). **No prjxray verdict exists for this row.**
- **summarize.py** now classes a project rule-A FAIL whose peak is a tie-off route and that
  tcheck passes as `project-false-path(const)` (none occur on these routes: the only such
  project FAIL, ipow s3 umuli1, still fails in tcheck for the DSP reason), and applies
  `frontend-gap(const)` only to front ends that still keep the tie-off.
- Unchanged conclusions: every disagreement is still "project PASS, tcheck FAIL"; corner-fail
  (fails at a fixed point with no fallback): 0 lines; band-only remains the dominant class
  (collatz 39, xorshift 93, ipow 75 lines); spread-only: xorshift 8, ipow 2.
- **The project's rule A still contains the false path** (tighten.cell_boundary is not ours to
  edit); this note's fix recommendation for `cells/verify/tighten.py` stands.
