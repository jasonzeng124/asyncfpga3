# C-10m: the slice OUTMUX hop and the tie-off false path in tcheck's front end, every row re-run

Shard C, probe 10m, 2026-10-29. Python/shell only; no Lean module changed (the proved
checker is unchanged, `sync.sh --check` passes, axiom audit below).

## Verdict

**Done. The audit's Finding M (the OUTMUX hop is missing) is true of C-10g (1e7947a), the
commit the audit read, but the hop was already added in C-10h. One OUTMUX bug was left, in the
Jx shared-prefix split, and it is now fixed. The constant tie-off false path is removed from rule A.
Every row was re-run.**

1. **Arc by arc**, tcheck's prjxray numbers equal the auditor's independent model
   (`audit/tc/xrc.py`, no shared code) on **all 86,037 common arcs of gcd_hw seed 4 within
   11 ps**, and on all 17,800 of collatz seed 2. This holds with the cross-check switch
   `TCHECK_HOP_NOL=1`. Without it, tcheck is higher by at most 34 ps on the MAX side of
   5,395 LUT-via-xMUX arcs: prjxray-db has `xMUX` and `xMUXL` entries, and tcheck takes their
   hull.
2. **The bug that was left (Jx, rule J).** Two sinks of one LUT output can leave the slice
   through different site pins: A..D directly, and AMUX..DMUX through the OUTMUX. C-10h treated
   the OUTMUX hop as shared, which credited it to the side that does not have it. With the
   previous 10m's fix in `Prjx.split` (kept): **all 72 J clients match xrc within 15 ps** on
   fast/slow/fastG/slowG (max 5/12/7/10 ps). Before the fix, 7 clients were off by about the hop
   (±75 fast, ±170..212 slow).
3. **The tie-off false path.** `rules2.py` rule A no longer starts at `$PACKER_GND_DRV` or
   `$PACKER_VCC_DRV`. A constant never switches, and under 10a's Run semantics a node with no
   changing input never changes. Removing these starts therefore models the circuit; it is not
   a weakening.
4. **gcd_hw, 4 seeds (byte-identical routes):**
   - Every verdict is unchanged from C-10h: agree3, unchecked3, cert3 and fallback3 are
     identical.
   - 25 of 1,592 compare rows moved:
     - 7 Jx rows from fix 2;
     - 18 rule-A rows from fix 3, all with higher margins.
   - The J tally stays 71/72. The one Jx FAIL is seed 4 `merge12.uarb2#2`, now
     fast/slow/fastG/slowG 142/383/**-116/-204**. That matches the audit's -111/-201 and is
     worse than 10g's -9/+39. It fails only under the band: the consistent corners pass.
5. **Kernels (12 byte-identical routes):** the only changes are the rule-A rows of cells with a
   tie-off start.
   - tcheck verdict flips: collatz `uselect0` (3 seeds), xorshift `ucmpi0` (4) and ipow
     `ucmpi2`/`ushrsi0` (4 each) go FAIL->PASS. Agreement on A rises: collatz 22->25/40,
     xorshift 22->26/44, ipow 25->33/44.
   - "frontend-gap(const)" is gone.
   - ipow `umuli1`/`uselect0` still fail tcheck, because 99.7% of their arcs are DSP48E1
     fallback (no DSP timing model).
6. **No corner-fail anywhere.** Every remaining disagreement is "project PASS, tcheck FAIL",
   band-only or spread-only, as before. The certificates were regenerated (0 CERTBAD on 12 runs)
   and the axiom audit is clean.

## 1. Arc by arc against the auditor's model (`xrcarcs.py`)

**Routes.**
- The gcd_hw seeds d, 2, 3 and 4 were rebuilt with `tcheck/route.sh`. All four are
  **byte-identical** to the C-10e/10h routes (fasm, routed json, sdf; `results/sha_*.txt`), which
  the audit also rebuilt identically.
- All 12 kernel routes rebuilt with `kcheck/route.sh` are byte-identical to C-10n's (SDF sha).
- Toolchain: nextpnr-xilinx `0.9.2-100-gbfdeaf7c`, sha256 `9c732bc6303458df`.
  `cells/verify/toolchain.sh` reports every patch ok. `--freq 100` was passed (route.sh copies
  build_hw.sh's / kcheck's patched flow).

**Method.** Every SDF arc of the route that both models resolve is compared:
- tcheck: `extract.Prjx.interconnect`/`iopath`;
- auditor: `xrc.route_arc`.

xrc.py is read with `git show origin/claude/audit:audit/tc/xrc.py` into `build/xrc/`.

**gcd_hw seed 4.** 86,037 arcs are common (tcheck resolves 90,158, xrc 86,778).

| class | arcs | within 15 ps (4 corners), default | within 15 ps, `TCHECK_HOP_NOL=1` | max abs diff fmin/fmax/smin/smax, default |
|---|---|---|---|---|
| LUT cell arc (physical pin) | 39642 | 39642 | 39642 | 3/4/9/11 |
| net, LUT O6 out on A..D (no hop) | 22322 | 22322 | 22322 | 0 |
| net, LUT O5 via xMUX (a5lut->amux ...) | 10600 | 6963 | 10600 | 0/5/0/29 |
| net, LUT O6 via xMUX (a6lut->amux ...) | 5981 | 4223 | 5981 | 0/6/0/34 |
| MUXF7/F8 cell arc | 3603 | 3603 | 3603 | 0 |
| net, F8 via BMUX / F7 via AMUX, CMUX | 2457 | 2457 | 2457 | 0 |
| net, FF / 5FF / CARRY4 O,CO via xMUX | 1432 | 1432 | 1432 | 0 |

- **The OUTMUX hop is in the front end** for O6 and O5 LUT outputs, MUXF7/F8 outputs and CARRY4
  outputs. Since C-10h it has been the `dh` term of `Prjx._ic`.
- **The minimum side matches exactly.** The only differences are on the maximum side of
  LUT-via-xMUX arcs. Their cause: prjxray-db's `slicel.sdf`/`slicem.sdf` carry two ROUTING_BEL
  instances per output mux, for example
  - `a6lut->amux` (0.071::0.088)(0.168::0.209), and
  - `a6lut->amuxl` (0.072::0.089)(0.194::0.241).

  Which one a configured site uses is not decoded. tcheck takes the hull, which is sound if
  either applies (C-10h's decision, kept). xrc reads `AMUX` only. The cost of the hull is at
  most 34 ps at slow max, on the pessimistic side.
- **Other configurations reproduce the audit.** With `XRC_NOMUX=1 TCHECK_NO_DRVHOP=1`, both
  models drop the LUT hop. They then agree on every LUT net: this is the C-10g model, the one the
  audit reproduced to the ps.
- **collatz seed 2** (`results/xrcarcs_collatz_s2*.tsv`): 17,800 common arcs, the same picture.
  867 arcs differ in the default mode, 0 with `TCHECK_HOP_NOL=1`.
- **Site pins, re-measured** (`results/sitepin10m_d.tsv`, 4000 sampled LUT-pin nets on seed d,
  hop and hull included): A1 slow_max-SDF mean **+609**, p10 404, p90 772, max 2204. Nets
  through an xMUX alone: +696. At FAST_MIN the SDF is *high* by 200..557 ps mean per pin.
  - The audit got +596 / p90 763 / max 2280 / +683 (all arcs, no hull).
  - So the C-10g "+490" (the mean, OUTMUX omitted) is superseded, and the audit's wording
    correction ("a mean, slow corner only") stands.

## 2. Rule J (the audit's "J 67/70 PARTLY REFUTED"), client by client against xrc

`results/cmpxrc_j.txt`: tcheck Jx (exact branch-point credit) against xrc's `rulej_x.tsv`, on
the same routes.

| | clients within 15 ps (all 4 cols) | mean diff f/s/fG/sG | max abs |
|---|---|---|---|
| C-10h front end (committed tables, `results/before10m/`) | 65/72 | -2/-3/-3/-1 | 93/212/105/243 |
| **C-10m** | **72/72** | -2.0/-2.5/-4.6/-4.1 | 5/12/7/10 |
| C-10m against xrc with `XRC_NOMUX` (the C-10g model) | - | +31/+81/+19/+57 | 144/347/115/266 |

**The 7 Jx rows that moved** (fast/slow/fastG/slowG):

| seed | client | C-10g | C-10h | C-10m | xrc (audit) |
|---|---|---|---|---|---|
| d (BQ#1) | merge6.uarb1#1 | 224/536/-10/-8 | 297/717/46/132 | **370/885/102/262** | 372/887/107/266 |
| 2 | merge6.uarb1#1 | | 728/1643/473/1054 | 797/1809/527/1182 | 802/1821/533/1192 |
| 2 | merge9.uarb1#1 | | 466/1175/293/752 | 541/1345/351/884 | 545/1348/357/888 |
| 3 | merge11.uarb1#2 | | 421/977/196/452 | 326/763/86/205 | 328/765/91/209 |
| 3 | merge6.uarb1#2 | | 428/1010/177/416 | 497/1176/231/544 | 500/1179/235/548 |
| 4 | merge12.uarb2#1 | | 353/860/116/295 | 260/649/9/52 | 265/654/16/58 |
| 4 | merge12.uarb2#2 | 235/594/-9/39 | 235/594/-9/39 | **142/383/-116/-204** | 144/385/-111/-201 |

Also:
- 2 merge12.uarb1#1: C-10g -35/-86; now 222/523/**16/44** (xrc 224/526/22/49). This is a thin
  pass; it did not move in 10m, because C-10h had already fixed it.

**The audit's three J rows, settled:**
- **d merge6#1** (the boarded route) **passes**. It was an artefact of the missing hop.
- **2 merge12.uarb1#1** passes thinly.
- **4 merge12.uarb2#2** fails the band by -116/-204 ps. A0 reaches ua2 through DMUX, so the hop
  belongs to the late side. Unbanded, both corners pass (+142/+383).
- J tally: 10g 67/70 -> 10h 71/72 -> 10m **71/72** (the same verdicts as 10h; only the
  seed-4 margin moved).

**Why the C-10h numbers were wrong on these rows.** Two sinks of one LUT output can leave the
slice through different site pins. The router used both A and AMUX for one net: these are two
routed site nets, so they have no common RC element. C-10h nevertheless returned the hop of sink
a as "shared". That credits the OUTMUX hop to a side that never passes through it and drops it
from the side that does. `Prjx.split` now returns shared = 0 when the element lists have no
common prefix, and each side carries its own driver hop. The `assert dh == _dh` guards the
shared case.

**J over-credit** (project pip-count c minus the exact branch-point share, SDF units):
- mean 42 / 28 / 66 / 55 ps (d/2/3/4);
- max 138 / 88 / 162 / 137;
- under-credits on 4 / 3 / 1 / 2 clients, down to -353 (seed d merge9).

The audit's "33-68 mean, max 96-162, under-credits 1-4 per route down to -353" is reproduced.
The C-10g "95 ps avg, permissive on 69/70" is superseded.

## 3. The other rules against the audit's tables (`results/cmpxrc_rows.txt`, `cmpxrc_r.txt`)

### RT_FB (R/Rc)
1656 node rows are compared; 1472 of them are within 15 ps on all four columns. Every outlier
has tcheck LOWER, which is the conservative side. There are two groups:
- **About -40 ps at slow (30-50 nodes per seed).** This is the xMUX hull on the feedback wire.
- **-150..-450 ps on about 10 arbiter/fork nodes per seed** (merge9/11 ua1/ua2, fork26/27/31,
  link_n112). All of them have margins above 1 ns. tcheck's late side is the checked potential
  over the whole routed graph (C-10h `pot_sound`), while the audit's `rtfb_x.py` request is a
  Dijkstra on LUT-only weights. tcheck finds a shorter response, which keeps it sound; the path
  itself was not traced.

Thin and failing nodes:
- **seed 2 uenv1:** tcheck 44/162/-117/-221, xrc 46/164/-114/-219.
- **seed 4 uenv1:** tcheck 94/161/-86/-243, xrc 99/197/-81/-201 (the hull, -36/-42 at slow).
- **DUT minimum (seed d merge10.uarb1.ua2.u):** tcheck 252/530/23/19, xrc 254/532/26/21.
- No banded verdict differs.

### E (gates)
The algorithms differ by design:
- tcheck **E** credits at the deepest node that DOMINATES both pins (H_CLEAN_EDGE there). tcheck
  **E0** takes the minimum over skew's launches, with no credit.
- The audit takes skew's worst-guarded launch and skew's measured-path credit.

Where the audit used its full model (seed d: MUXF modelled), tcheck E0 is at most the audit's
E0 + 15 ps on **all 118 gates**. Examples:
- **umux13.uj0:** tcheck 216/528/**-203/-426**, audit 225/538/-190/-412;
- **umux13.uj1:** -31/-39 against -18/-26.

On seeds 2 and 3 the audit tables are LUT-only. Unmodelled MUXF/CARRY arcs keep their SDF number
there, which makes those tables up to about 600 ps more pessimistic at fast. Seed 4 is
fallback-scaled. The E0 differences on those seeds come from that fallback, not from the hop.

Banded verdicts that differ:
- **E0 umux4.uj1 (seed 2), umux19/umux4.uj1 (seed 3), umux3.uj1 (seed 4).** tcheck fails by
  -6..-34 ps, while the audit passes these rows thinly. tcheck takes the minimum over launches;
  the audit takes the launch whose slowG is worst.
- **E umux19.uj1, umux2.uj1.** tcheck passes by more than 1.8 ns because a dominator credit
  exists. The audit fails them, because skew's measured path got t_c = 0.
- **E umux4.uj0/uj1 (seeds 2, 3), umux3.uj1 (seed 4).** tcheck fails, because no dominator
  exists, so credit = 0, equal to E0. The audit passes, because skew's measured-path credit
  applies at a divergence that does not dominate. tcheck refuses that credit: it is not sound
  without a dominating node.

All of these are the C-10g/10h E differences. None of them moved in 10m.

### A, F
Verdicts agree on every row the audit has (d and 4; 50 A + 29 F per seed). The margins differ:
- the audit ran tighten.py's own walk and guard on corner SDFs;
- tcheck runs the all-paths race under the band.

## 4. The tie-off false path (rules2.py rule A)

**Construction.** `T.cell_boundary` keeps the packer's constant drivers as boundary starts. On gcd_hw (seed 3), all 91 rule-A obligations (50 cells) had a tie-off start removed: both GND
and VCC in 90 of them, one in the other. rules2.py now removes them before deciding between common and bundled, so a constant can
never be a "common source". The obligation json records `const_dropped`. With
`TCHECK_KEEP_CONST=1` the old start set comes back; that switch is for before/after comparison
only, never for a verdict.

**Effect on gcd_hw.** 18 A rows changed: ucmpi2, ucmpi3, uori2, uori4 on every seed, plus
uori3 on seeds 3 and 4. Every change is upward, by +34..+6,207 ps at fast. No verdict changes,
because those rows already passed.

**Effect on the kernels.** The changed rows are listed in C-10n-kernels.md, "10m correction".

**What the project still has.** tighten.py's rule A still times the tie-off route, which is
outside this probe's files. C-10n's recommendation to tighten.py stands: skip `is_const` in
`cell_boundary`.

**The other rules do not time tie-offs.**
- In H/I/F/J/W/R/E every data side starts at a launch that is a storage node, a link controller
  or a net fall, and a constant driver cannot be reached from any of those.
- In the cert late sides (Hc/Fc/Rc) the constant drivers stay in the graph, but they are inert:
  they get the cap potential and can never be the cause of an earliest change (C-10h). They
  appear in the census as "constant driver: never switches" (about 7,816 arcs per route).
- rules10k already skips them.

## 5. Every row re-run: gcd_hw (C-10e/10g/10h/10k/10l rows)

`./run10m.sh d 2 3 4` runs one seed at a time, because each extract takes about 1 GB. Seeds d,2
and 3,4 were run as two streams. Then the summaries were made. Outputs are in
`formal/tools/tcheck/results/`, and `results/before10m/` holds the committed C-10h/10k/10l
tables at dfc8edc.

| table | rows | changed | verdict changes | cause |
|---|---|---|---|---|
| compare5 (A, E/E0, F/Fc, J0/Jx/Jp vs the project rules; H, I in agree3) | 1592 | 25 | 0 | 7 Jx (split fix), 18 A (tie-off) |
| agree3 / disagree3 (verdict tallies) | | identical | 0 | disagree3: only seed 4 merge12.uarb2#2 Jx numbers |
| unchecked3 (W, R, Rc), cert3, fallback3 | | identical | 0 | |
| r10k_rows (Fd, Z, X, Xi) | 604 | 0 | 0 | |
| r10l_rows (Xc/Xic/Xm, K) | 944 | 184 | 103 | **not from 10m**, see below |

**The r10l changes do not come from this probe.**
- The 168 K rows and 16 Xm rows differ because `rules10l.py`'s rule K, as it stands at dfc8edc
  and HEAD, is newer than the committed `r10l_rows.tsv`/`summary10l.txt`. Those were made at
  08:57 on 10-27 with the older K. The `Kold` ablation in rules10l.py records that older rule.
- rules10l.py calls neither `Prjx.split` nor rule A, and this probe changed no interval code (the
  `TCHECK_*` switches are off). So the 10m front end cannot move an r10l row.
- The new r10l tables are simply the current rule's output on the current front end. **Their
  interpretation belongs to C-10l2 (rule K).**

**Agreement (verdicts identical to C-10h's table).**

| rule | A | E | E0 | F/Fc | H/Hc | I | J0/Jp | Jx |
|---|---|---|---|---|---|---|---|---|
| agree / comparable (4 seeds) | 199/200 | 465/472 | 460/472 | 113/116 | 630/632 | 300/300 | 57/72 | 71/72 |

Every disagreement is "project PASS, tcheck FAIL only under the 0.772/1.155 band on a prjxray
corner". Unbanded fast and slow pass on every row.

## 6. Every row re-run: collatz, xorshift, ipow (C-10n rows)

Run as `SKIP_ROUTE=1 KCHECK_FRONT_REV=worktree KCHECK_TAG=m10 KCHECK_JOBS=1 kcheck/run.sh <k> 1 2 3 4`:
- front-end hash `73a44366152685fe`;
- tcheck snapshot `33c9d370d363b469`, rebuilt from the current Lean sources (sync.sh --check
  passes; toy and cert self-tests ok);
- outputs in `kcheck/results/<k>_m10/`.

**Changes against C-10n's 24e47ca pass:** only the rule-A rows of the tie-off cells. Against
C-10n's main tables, the 24e47ca Jx moves are added as well. The full table is in
C-10n-kernels.md, "10m correction".

| kernel | A agree before -> after | tcheck A flips FAIL->PASS | disagreement lines | classes after |
|---|---|---|---|---|
| collatz | 22/40 -> 25/40 | uselect0 s1, s3, s4 | 42 -> 40 | band-only 39, fallback 1 |
| xorshift | 22/44 -> 26/44 | ucmpi0 s1-s4 | 105 -> 101 | band-only 93, spread-only 8 |
| ipow | 25/44 -> 33/44 | ucmpi2, ushrsi0 s1-s4 | 92 -> 84 | band-only 75, fallback(DSP) 7, spread-only 2 |

On ipow s3 `umuli1` (the only project violation), tcheck's sdf margin without the tie-off is
+6973 ps (+3484 with it). It still fails tcheck, but in its prjxray variants, because of DSP
fallback.

## 7. Lean side

- **No Lean module was edited and no new theorem is claimed.** tcheck's PASS verdicts rest on
  the C-10e/10h theorems, unchanged:
  - `Tcheck.verdict_sound`, `cverdict_sound`, `pverdict_sound`, `xverdict_sound`;
  - `Formal.Timing.pot_sound`, `SharedPrefix.pot2_sound`, `MaxNode.potMax_sound`.
- **Certificates regenerated.** Every run re-emitted the potentials (Hc/Fc/Rc, the 10k pair
  certificates, the 10l credited certificates), and the compiled checker re-checked them:
  **0 CERTBAD** in the 12 gcd_hw outputs (t5/t10k/t10l × 4 seeds) and in every kernel run.
- **Axiom audit** (`results/axioms10m.txt`, `slot.sh lake env lean test/Axioms.lean`): all 12
  theorems depend only on [propext, Classical.choice, Quot.sound].
- `formal/lean/Wip/C10m/` is not used. Nothing needed WIP Lean.

## 8. Hypotheses (unchanged from C-10h, plus the following)

1. **H_FALSE_CONST.** `$PACKER_GND_DRV`/`$PACKER_VCC_DRV` outputs never change after
   configuration.
   - True of a configured 7-series fabric: the tie-offs are static.
   - In 10a's terms this is H_QUIESCENT for those nodes, which `Run` already assumes for every
     node that is not the launch. It is therefore not a new assumption of the theorem; it is a
     statement about which nodes the extractor may launch.
   - Witness of non-vacuity: every route has the two drivers, and they appear in all 91
     rule-A start sets on gcd_hw seed 3.
2. **xMUX/xMUXL hull** (C-10h, restated with its measured cost): sound if the site uses either
   instance. It costs at most 34 ps per arc at slow max.
3. **Two-pin split.** When two sinks of one LUT output leave through different site pins, the
   front end assumes nothing shared beyond the LUT output, so the credit is 0. This is
   conservative in the Jx sense: less credit.

## 9. What this does NOT show

- Elmore RC on prjxray-db numbers is the model, not silicon. Both tcheck and xrc share
  prjxray-db, so the arc-level agreement checks the implementation, not the data.
- The rows mirror the project rules. A tcheck FAIL is not a counterexample run (Checker.lean's
  exactness qualifier).
- ipow rows through the DSPs are SDF-band rows.
- The BOARD-QUEUE routes BQ#2 and BQ#3 (R5 sizes) were not routed here. The lead's brief said
  "gcd_hw R5 routes (4 seeds)"; the rows tcheck reports are on the BQ#1 recipe (no sizes), seeds
  d/2/3/4, and those were re-run. The audit's BQ#2/#3 findings (BQ#3 rule A ushrsi1 at -36 ps
  fast) are not re-derived by tcheck. That needs `route.sh` with the R5 sizes file, about 1 hour
  more.

## Files (all under formal/tools/tcheck/ unless stated)

| file | what |
|---|---|
| `extract.py` | `Prjx.split` two-pin fix (previous 10m, kept); `TCHECK_NO_DRVHOP` and `TCHECK_HOP_NOL` cross-check switches (never a verdict) |
| `rules2.py` | rule A drops tie-off starts (`TCHECK_KEEP_CONST=1` restores them) |
| `run10m.sh` | the full gcd_hw re-run, one seed at a time, plus summaries and cross-checks |
| `xrcarcs.py` | arc-by-arc tcheck against xrc.py |
| `cmpxrc.py` (previous 10m), `cmpxrc_r.py`, `cmpxrc_rows.py` | J, RT_FB and E/A/F rows against the audit tables |
| `beforeafter10m.py` (previous 10m) | before/after of compare5, r10k, r10l |
| `sitepin.py` | header fixed for the OUTMUX columns |
| `run4.sh` | makes skew_v if missing (previous 10m) |
| `results/xrcarcs_{4,4_nol,4_nomux,collatz_s2,collatz_s2_nol}.tsv` (+ `_out.tsv`), `cmpxrc_{j,r,rows}.txt`, `beforeafter10m.tsv`, `sitepin10m_d.tsv`, `axioms10m.txt`, `before10m/` | the tables |
| `results/{agree3,disagree3,unchecked3,cert3,fallback3}.tsv`, `compare5_*.tsv`, `r10k_rows.tsv`, `r10l_rows.tsv`, `summary10k/10l.txt` | re-run outputs |
| `formal/tools/kcheck/summarize.py` | classes `project-false-path(const)`; `frontend-gap(const)` only for a front end that keeps tie-offs |
| `formal/tools/kcheck/results/{collatz,xorshift,ipow}_m10/` | kernel re-run |

## Reproduce

    cd formal/tools/tcheck
    for s in d 2 3 4; do ./route.sh $s; done        # ~15 min each; sha == results/sha_*.txt
    ./run10m.sh d 2 3 4                             # ~1 h per seed on a shared machine
    O=build/tree_4/cells/build/hw/gcd_hw
    python3 xrcarcs.py $O gcd_hw build/tree_4/cells build/xrc 4
    TCHECK_HOP_NOL=1 python3 xrcarcs.py $O gcd_hw build/tree_4/cells build/xrc 4_nol
    SITEPIN_TAG=10m_ python3 sitepin.py d 4000
    FORMAL_SLOT_CWD=$PWD ../../slot.sh lake env lean test/Axioms.lean
    cd ../kcheck
    for k in collatz xorshift ipow; do ./route.sh $k prep; for s in 1 2 3 4; do ./route.sh $k $s; done
      SKIP_ROUTE=1 KCHECK_FRONT_REV=worktree KCHECK_TAG=m10 KCHECK_JOBS=1 ./run.sh $k 1 2 3 4
      python3 prepost.py $k m10; done
