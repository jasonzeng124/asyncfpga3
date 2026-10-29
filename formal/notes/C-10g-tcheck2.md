# C-10g: tcheck phase 2. Rules A, E, F and J, plus two races no rule checks, on 4 gcd_hw routes

Shard C, probe 10g, 2026-10-27.

## Verdict

**It works. tcheck now covers rules A, E, F, H, I and J, and two obligations the project
does not check:**
- **W**, 8e's latch open width;
- **R**, RT_FB, the C-element feedback race.

The four seeds of gcd_hw are the C-10e routes, unchanged. Each route gives 1325
obligations from rules A, E, F, J, H and I, which is 7950 instances. With W and R there are
another 676 obligations and 3384 instances.

**The algorithm reproduces the rules exactly.** On the `sdf` variant, tcheck's margin equals
the rule's own raw margin to the picosecond on:
- E: 471 of 472 rows;
- J: 72 of 72;
- F: 115 of 116;
- A: 185 of 200.

The rows that differ are all lower in tcheck, so tcheck is more conservative there (see
below).

**Every verdict disagreement has the same direction: the rule passes and tcheck fails.**
None of them come from the algorithm. Each one appears only after the project's own
0.772/1.155 band is applied to prjxray corner data. Unguarded, the prjxray corner passes,
with two exceptions, both explained under "Disagreements". The causes, quantified below,
are:
1. **Site-pin delays the SDF does not carry.**
2. **The SDF holds one number, the slow max.** A long LUT-chain request shrinks to the fast
   corner while the band still applies.
3. **The fallback band** on arcs that have no prjxray number (H_FALLBACK_BAND). This is a
   front-end gap, and it is pessimistic.

**Obligations no project rule checks:**
- **W (open width)** passes everywhere. The minimum is +336 ps at fastG.
- **R (RT_FB)** fails on 2 of 4 seeds, at one C-element, `urig.uenv1.u`:
  - seed 2: fastG -7 ps;
  - seed 4: fastG -37 ps, slowG -95 ps.
  - The thinnest margin in the DUT is +19 ps (seed d, `ucontrol_merge10.uarb1.ua2.u`).
  - These fail only under the band: unguarded, seed 4 has +114 ps fast and +234 ps slow.
    So they are thin margins, not predicted failures. No rule in the project would see
    them.

**Nothing new is proved in Lean.** Every PASS is `Tcheck.verdict_sound` (C-10e) applied to an
emitted instance. What is new is untrusted Python: the obligation shapes, and hypotheses
named per rule below.

## Files (all under formal/tools/tcheck/, which this probe owns)

| file | what |
|---|---|
| `extract.py` | 10e's front end. Adds `--rules2 LETTERS` and `--no-hi`, and an optional `inside` (confinement) on `segment`. In `Prjx`: `split` (the exact shared part of one routed net from the RC tree, for J), the **MUXF7/F8 cell arcs** and the **LUT→F7 site hop** from prjxray-db slicel/slicem.sdf, and the **min>max hull** (0-19 arcs per route have fast_min > fast_max in the db after Elmore; 10e emitted them as an ILLFORMED interval, now the hull). Fallback arcs fell from 7554 to about 3800 per route. |
| `rules2.py` | Rules A, E, F, J as race instances (docstring = the exact construction) |
| `rules3.py` | W (8e open width) and R (RT_FB) |
| `compare2.py` | One row per project row, against tighten.py (A; F through `audit_fastfall`), `skew.py -v` (E) and arb_fork.py (J) |
| `summarize2.py` | Writes `results/agree2.tsv`, `disagree2.tsv` and `unchecked2.tsv` |
| `diag.py` | Untrusted explanation aid: the critical paths of one instance, with each arc's interval in every variant |
| `sitepin.py` | SDF against prjxray per physical LUT pin → `results/sitepin_d.tsv` |
| `run2.sh`, `run3.sh` | The pipelines (see below) |
| `results/compare2_{d,2,3,4}.tsv` | The row-by-row tables |

## Run

    cd formal/tools/tcheck
    ./run2.sh d 2 3 4     # sync --check, lake build (FORMAL_SLOT_CWD set), toy test, then per seed:
                          # skew.py -v (once), extract H,I + A,E,F,J, tcheck, compare.py, compare2.py
    SKIP_BUILD=1 ./run2.sh ...   # skips lake build when the slot semaphore is busy; the exe is current
    ./run3.sh d 2 3 4     # W and R
    python3 summarize2.py # writes results/*.tsv

- **Time and memory per seed:** extract takes about 3-4 min and 0.9 GB; tcheck takes about 7 s
  for 7950 instances (the A file is 47 MB).
- **The run has three parts.** `sync.sh --check` passes, with the four copies unchanged.
  `lake build` is a no-op: no Lean file changed. The toy self-test passes.

## The obligations (exact constructions are in rules2.py and rules3.py)

### A (tighten `check`/`check_bundled`)
- Each instance uses tighten's own `request_sites`, peers, `cell_boundary`, `upstream_bd_links`
  and confinement. All paths are kept; confinement works as in `walk` (the destination must be
  inside).
- **Common source:** one instance per start.
- **Bundled:** a virtual launch drives every start at [0,0]. This is **H_BUNDLED_T0**, the
  assume-guarantee from check_bundled's docstring.
  - The data side is entered through a "lag" node: the hull of the upstream links'
    controller→latch segments. That is `upstream_data_lag` per variant.
- 30 of the 50 cells use the common source; 20 are bundled.

### E (skew.py)
- **Launches** are skew's own choice: `back()` and cand[:4] plus the (3) C nodes are ported
  verbatim.
- **Graph:** each side is a level-unrolled DAG. A node (k, pin) means pin reached after
  exactly k storage crossings; a crossing goes through any non-feedback input, as skew.walk
  seeds.
  - Request side: the fast-fall-pruned arcs. Select side: all arcs.
  - Each side is unrolled to the first level at which its pin is reached. This is skew's lap
    rule, kept as **H_LEVEL**, a protocol fact (10b).
- **E0:** launch at the launch node, with no credit.
- **E:** launch at X, the deepest node that **dominates both pins**. This is the exact shared
  prefix. It needs H_CLEAN_EDGE at X.
  - Across the 4 seeds, X is a LUT output in 252 instances (H_CLEAN_EDGE then needs a
    glitch-free gate), a storage node in 38, and a single-driver pin in 32.
  - skew credits t_c at the divergence of the two *measured* paths, which need not dominate.
    On these routes it credited t_c = 0 on every disagreeing row.

### F (audit_fastfall)
- **Launch:** the fall of the line's input net.
- **Data:** every stage's fall, bounded by its side tap alone. This is **H_CONTROLLING**: a 0 on
  either AND input forces the stage low. The 10a hull would take the later input, which is
  pessimistic. The head is fed from src through all paths.
- **Request:** the tail's earliest fall, plus the shortest tail→src path through anything,
  which is tighten's `shortest_to`. That path is chosen by Dijkstra on the sdf, fast and slow
  lower bounds, and the chains are merged by taking the minimum. It was one chain on every
  line.
- **Comment/code mismatch in tighten.py.** The rule F comment says "the tail's earliest fall
  plus two LUT arcs, no wire credited". The code uses `shortest_to` over the whole graph. Only
  the code was mirrored.

### J (arb_fork)
- **J0:** launch at A0's driver, with no shared credit. It needs no H_CLEAN_EDGE.
- **Jx:** launch at the **branch point of A0's RC tree**. `Prjx.split` takes the elements the
  two sinks share by identity; their intrinsic delays and Elmore terms are identical numbers.
  - The sdf/sdfband columns use the SDF number minus the same fraction, at the slow max.
  - It needs H_CLEAN_EDGE on a wire, which holds physically, plus H_ONE_SAMPLE_PER_WIRE.
- **Jp:** the project's pip-count c, in the sdf/sdfband columns only. It exists to reproduce
  arb_fork.
- 2 of 72 clients have no Jx (seed d, merge9): fasm2lean's walk dies on a floating LV/LVB long
  line.

### W (8e open width)
- Applied per upstream/downstream controller pair; 150 per route.
- **Launch:** the rise of `up`.
- **Data:** up→every enable pin of its own bank.
- **Request:** the round trip up→ctl→up, plus up's LUT arc. A C node falls on its last input,
  so the ack alone is a lower bound.
- Pairs are taken in both directions, and each one is a valid lower bound.

### R (RT_FB)
- Applied to every non-latch storage node; 414 per route.
- **Data:** the node's routed feedback wire or wires.
- **Request:** the earliest response at any other pin of the node: a Dijkstra chain through
  anything, using lower bounds on 3 variants, merged.

## Agreement tables (tighten/skew/arb_fork verdict against tcheck = PASS at fastG and slowG)

`results/agree2.tsv`. Each cell is agree / disagree / not comparable.

| rule | flavour | d | 2 | 3 | 4 | total agree |
|---|---|---|---|---|---|---|
| A | | 44/6/0 | 42/8/0 | 43/7/0 | 43/7/0 | 172/200 |
| E | credited (E) | 117/1/0 | 117/1/0 | 116/2/0 | 115/3/0 | 465/472 |
| E | no credit (E0) | 115/3/0 | 114/4/0 | 115/3/0 | 114/4/0 | 458/472 |
| F | | 28/1/0 | 29/0/0 | 28/1/0 | 28/1/0 | 113/116 |
| H (10e, re-run) | | 157/1/21 | 157/1/21 | 158/0/21 | 158/0/21 | 630/632 |
| I (10e, re-run) | | 75/0/104 | 75/0/104 | 75/0/104 | 75/0/104 | 300/300 |
| J | J0 | 14/4/0 | 14/4/0 | 13/5/0 | 16/2/0 | 57/72 |
| J | Jx (exact shared) | 15/1/2 | 17/1/0 | 18/0/0 | 17/1/0 | 67/70 |
| J | Jp | 14/4/0 | 14/4/0 | 13/5/0 | 16/2/0 | 57/72 |

- **The project rules report everything as PASS on all four routes:** E 0/118 violated, J
  pass, A 0 violations, and F 29 lines all ok. So every disagreement is "project PASS,
  tcheck FAIL".
- **H and I with the MUXF data:** the verdicts are 10e's exactly.

## Algorithm agreement (variant `sdf` against the rule's raw margin)

- **E:** 471 of 472 equal. On seed 4, one gate is 676 ps lower in tcheck. Most likely cause
  (not traced): tcheck reports the minimum over launches, while the skew row prints the
  launch with the worst *guarded* margin. That is a reporting difference, not a verdict
  difference.
- **J:** 72 of 72 equal (Jp and J0).
  - **sdfband** matches arb_fork's guarded margin within 3-8 ps. That is floor/ceil per arc,
    because arb_fork rounds once.
- **F:** 115 of 116 equal. One row on seed 2 is 141 ps lower. Most likely cause (not traced):
  H_CONTROLLING's side-tap bound is above tighten's min(ripple, side) for a stage whose ripple
  is earlier.
- **A:** 185 of 200 equal. In 15 rows tcheck is lower by 2..367 ps. The cause is not traced
  (candidates: confinement at a start outside the region, or per-start copies against
  tighten's shared tables). No verdict depends on it: all 15 still pass at `sdf`.

## Every disagreement, explained (`results/disagree2.tsv`)

Every disagreeing row has `tc_sdf` equal to the project's raw margin, so the cause is in the
intervals, not in the rule. Classified by `diag.py` on the critical paths:

### 1. Site pins (10b's finding, measured on this route: `results/sitepin_d.tsv`)

Sample: 2975 LUT-pin nets on seed d.

| physical pin | n | SDF mean | prjxray slow_max mean | site-pin intrinsic (slow_max) | slow_max - SDF: mean [p10, p90] |
|---|---|---|---|---|---|
| A1 | 582 | 736 | 1226 | 522 | **+490** [386, 670] |
| A2 | 572 | 780 | 1231 | 508 | **+452** [359, 581] |
| A3 | 564 | 765 | 1079 | 356 | +314 [217, 450] |
| A4 | 586 | 693 | 911 | 291 | +218 [147, 361] |
| A5 | 603 | 631 | 676 | 121 | +45 [-29, 156] |
| A6 | 68 | 1111 | 1149 | 7 | +37 [-125, 256] |

- **The site-pin term explains the whole difference.** In the mean, delta ≈ site-pin
  intrinsic - about 30 ps.
- **Which pin a net lands on moves the slow corner by about 0.45 ns** between A1/A2 and A5/A6.
  The SDF sees none of it.

The disagreements in this class:
- **E (credited), 7 rows:**
  - seed d umux13.uj0;
  - seed 2 umux4.uj0;
  - seed 3 umux4.uj0, umux4.uj1;
  - seed 4 umux1.uj1, umux8.uj0, umux8.uj1.
  - Example, umux13.uj0 on seed d (launch is the link's C node, X = launch, 12 arcs, 0
    fallback): the select's last net is 295 ps in the SDF and 479..739 ps at prjxray slow.
  - Summed along the critical paths, the select goes from 927 ps in the SDF to 1743 at slow
    max (+88%). The request goes from 2251 to 2352 (+4%): its first net rises (435 → 721..872),
    but its other 295-ps nets drop to 235..286.
  - The guarded margin falls from +667 in skew to -201 at slowG. Unguarded: fast +250,
    slow +609.
  - **These are thin, guard-only failures.** Under H_ONE_CORNER with no band, every one of the
    7 passes; the margins are listed in disagree2.tsv. The worst is seed 3 umux4.uj1 at
    -511 ps slowG (unguarded +784 fast, +1821 slow).
- **J, Jx (the exact credit), 3 rows:**
  - seed d merge6.uarb1#1: c = 0, so A0 branches at its source; -10 / -8 ps.
  - seed 4 merge12.uarb2#2: -9 ps fastG.
  - seed 2 merge12.uarb1#1: -35 / -86 ps.
  - The A0 net to ua_k is 559 ps in the SDF and 803..971 at prjxray slow, against a grant
    path whose site pins are cheap.
- **R uenv1.u** (below) is the same mechanism.

### 2. The SDF holds only the slow max; the request side is long LUT chains

- **Mechanism:** at the fast corner a LUT arc is 0.36/0.45 of slow, while a pip is 0.24-0.45
  and the band still multiplies. This is 10b's "corner safety is a property of composition".
  It combines with class 1 in most E rows.
- **E0 rows that fail while E passes** (umux19.uj1, umux2.uj0/uj1 and others: 14 E0 against 7
  E) are the no-credit version. The storage dominator X (for example
  `ulink_n166__0.stage[1].ctl.u.u` for umux19) is on both sides. Without the credit, the band
  is charged on the prefix twice.
  - skew passes these with t_c = 0 because its band is applied to SDF sums that are about
    30% shorter than prjxray slow.

### 3. Fallback (H_FALLBACK_BAND, pessimistic at the fast corner)

These are front-end gaps, not findings.
- **A, all 28 rows:** bundled arithmetic cells (shli0, shrsi0..4 on every seed, uaddi0 and
  ucmpi2 on two each).
  - Every one fails at fastG only, except seed 3 shrsi1, which fails at `fast` (-845) too.
  - **Critical path of seed 3 shrsi1 at fast:** 2 of its 19 arcs fall back. These are the
    MUXF7/F8 select (S0/AX/BX) nets of 1085 and 3446 ps SDF, which keep [0.772, 1.155] × SDF:
    5235 of the 7821 ps data latest.
  - At a prjxray-like 0.4x those arcs would be about 1.8 ns, and the row would pass by more
    than 1.5 ns.
  - **Fix:** extend `Prjx._ic` from LUT A-pins to every CLB site input pin (AX..DX, CIN,
    S#), and add the CARRY4 cell arcs.
- **F seed d ucmpi8:** the head-input net (2251 ps SDF) falls back. It is -738 at fastG and
  passes at fast (+359).
- **J0/Jp seed d merge9 (both clients):** the A0 nets fall back (floating LV long line in
  fasm2lean), so neither the prjxray numbers nor Jx exist. J0 fails even at `fast` (-645).
  - The fallback band charged on a 2.2 ns shared trunk without credit is the cause. On seeds
    3 and 4 the same arbiter resolves, and J0 seed 3 is -60/-34, Jx passes. **No verdict.**

### 4. The project guard is weaker than the band (10b's rule A finding, here on rule F)

- **F seed 4 ucontrol_merge12.udly:** tighten has raw 833, guard 200, margin +463. tcheck
  gives sdfband -73, fastG -176 and slowG -399. The unguarded corners pass (+317 / +697).
- Seed 3 has the same line at -11 slowG.
- **Mechanism:** a short flush race (833 ps) whose `max(0.2 t, 200)` guard is much smaller
  than 0.772/1.155 of the two sides.

### 5. J's pip-count estimate over-credits

The project's c, against the exact branch-point fraction in SDF units (Jx), over 70 clients:

| seed | rows | mean (c_proj - c_x) | max | rows where c_proj < c_x |
|---|---|---|---|---|
| d | 16 | 106 | 148 | 0 |
| 2 | 18 | 95 | 211 | 0 |
| 3 | 18 | 95 | 162 | 0 |
| 4 | 18 | 89 | 137 | 1 |

- **What it costs:** the guarded margin is about 0.383 c, so the over-credit is worth about
  35-80 ps per client. In the prjxray columns Jx is still the higher of J0/Jx (credit is
  real), but lower than Jp.
- **This is 10b's `ruleJ_counterexample` mechanism on a real route** (a cheap shared pip
  prefix, dear divergent pips).
- On these routes no Jx verdict flips because of it: the 3 Jx failures are class 1. But the
  estimate is biased in the permissive direction on 69 of 70 clients.

## Obligations no project rule checks (`results/unchecked2.tsv`)

| seed | rule | rows | min sdf | min fast | min slow | min fastG | min slowG | FAIL | slowG < 100 ps |
|---|---|---|---|---|---|---|---|---|---|
| d | W | 150 | 1940 | 761 | 1784 | 467 | 1111 | 0 | 0 |
| 2 | W | 150 | 1800 | 679 | 1531 | 378 | 846 | 0 | 0 |
| 3 | W | 150 | 1800 | 699 | 1684 | 420 | 1035 | 0 | 0 |
| 4 | W | 150 | 1800 | 598 | 1454 | 336 | 847 | 0 | 0 |
| d | R | 414 | 835 | 252 | 530 | 23 | 19 | 0 | 1 (ucontrol_merge10.uarb1.ua2.u +19) |
| 2 | R | 414 | 419 | 139 | 375 | -7 | 25 | **1** (urig.uenv1.u) | 1 |
| 3 | R | 414 | 838 | 484 | 895 | 225 | 347 | 0 | 0 |
| 4 | R | 414 | 419 | 114 | 234 | **-37** | **-95** | **1** (urig.uenv1.u) | 1 |

- **R on seed 4, urig.uenv1.u** (gcd_hw's environment C-element, outside udut but in the
  shipped bitstream):
  - The feedback wire is 295 ps in the SDF and 592..717 ps at slow. The site-pin class
    applies on the feedback pin.
  - The response is a 3-arc path, 714 ps in the SDF, and its first net is also
    site-pin-heavy.
  - Results: slowG 829 against 734 → -95; unguarded slow +234.
- **RT_FB in the DUT:** the C-elements in udut keep at least +19 ps at slowG on every seed
  (merge10.uarb1.ua2.u, an arbiter ack C-element, feedback route 575 ps in the SDF). That is
  the same thin-margin picture 10f found on the Muller pipeline, here on a shipped design.
- **W:** the open width is never close: at least +336 ps at fastG and +846 ps at slowG. A
  whole handshake round trip races one enable net.

## Hypotheses (new in this probe; 10e's still apply: Run semantics, H_ONE_CORNER plus band, H_FALLBACK_BAND, H_EXTRACT_MIN, H_SEGMENT)

- **H_BUNDLED_T0 (A, bundled):** all of a cell's boundary nets launch together at t = 0, with
  latches lagging by their controller segments. This is the assume-guarantee in tighten's
  docstring and is not composed with the upstream rule A.
  - Test: GLS on a generated unit, measuring a_req against a_data skew at the cell boundary.
- **H_LEVEL (E):** the first level at which each pin is reached is the transaction's path;
  deeper levels are laps. A protocol fact (10b), not timing.
  - Test: handshake-model (track 8) concurrency sets.
- **H_CLEAN_EDGE at X (E credited):** one transition at the dominator. Physical for storage
  and wire X; for a LUT-output X (252 of 322 credited instances) it needs a hazard-free gate
  on this transition.
  - Test: GLS with per-transition random delays on the prefix gates. E0 is the
    hypothesis-free row.
- **H_CONTROLLING (F):** an AND stage's fall is bounded by its side tap's fall plus the arc.
  This is true of the LUT2 INIT 8 (bd_delay FASTFALL); it is argued by hand, not in 10a's
  model.
- **H_ONE_SAMPLE_PER_WIRE (Jx):** the shared RC prefix has one delay in both sinks' sums.
  That is exact in Elmore; on silicon it is the 10b correlation hypothesis.
- **H_EXTRACT_MIN for F, R and W.** The late side is lower-bounded by Dijkstra chains in
  Python: 3 per obligation, on different variants, merged. Every node fires on first arrival,
  which is a sound lower bound only if the chosen chain really is the minimum. It is not
  verified.
  - Fix: emit the full crossing graph unrolled, the same construction as E's level DAG.
- **Prjx additions:** MUXF7/F8 IOPATHs and the LUT→F7 ROUTING_BEL hop come from prjxray-db
  verbatim. Site-internal F7→F8 has no db entry and stays at its SDF 0 (optimistic by less
  than about 25 ps, the size of the F7 entry). The min>max hull is wider, so it is sound if
  either number is.

## Effort to finish and what it buys

- **Remaining fallback, about 1 day.** Add CLB non-LUT site input pins (AX..DX, S#/CIN nets)
  to `Prjx._ic`, the CARRY4 arcs, and fasm2lean's LV/LVB long-line walk. That removes every
  class-3 row: all 28 A rows, F ucmpi8 and J merge9.
- **Full crossing-graph late sides for F, W, R and H, about 1 day.** This removes
  H_EXTRACT_MIN.
- **What it buys now:**
  - The six rules and two new obligations run through one proved checker, on real routes, in
    about 4 min per route.
  - The algorithms are confirmed equal to the rules' own numbers.
  - Two shipped-route facts the rules cannot see:
    - the SDF misses +0.45 ns of site pin on A1/A2 sinks, which makes the project's guarded
      E/J/F/R margins thin or negative under its own band at prjxray corners: 7 E gates, 3 J
      clients, 2 F lines and 1 RT_FB node over 4 routes;
    - J's estimate over-credits by about 95 ps on average.
  - The RT_FB race, which no project rule has, is the thinnest real margin in the design:
    +19 ps in the DUT, and -95 ps at the environment C-element on seed 4.

## Decisions taken (no one to ask)

- **H/I kept as 10e wrote them.** The MUXF arcs and the min>max hull changed their inputs; the
  verdicts are unchanged.
- **E is compared per gate, as the minimum over launches.** skew prints one launch per gate (the
  worst guarded). That is why one seed-4 row differs at `sdf`.
- **J's sdf-column "exact" c is the prjxray slow_max fraction applied to the SDF number.**
  nextpnr's per-pip delays are not in the SDF; reproducing them needs the chipdb.
- **The W pairs include the reverse direction** (an upstream ctl reached through the ack).
  Each one is a valid lower bound on up's next fall, so keeping them is sound.
- **No Lean was edited.** The lake build is a no-op. `run2.sh` passes `FORMAL_SLOT_CWD`
  (`SKIP_BUILD=1` was used once, while the slot semaphore was held by other shards).

## 10m correction (2026-10-29, probe C-10m)

The numbers above are kept as they were. Where they conflict with this section they are
**superseded**. Full tables are in `formal/notes/C-10m-outmux.md` and
`formal/tools/tcheck/results/`.

- **Finding M (audit, `audit/findings/tcheck.md`) applies to this probe's model.** The prjxray
  front end of 10e/10g omitted the slice OUTMUX hop: A..D LUT -> AMUX..DMUX, for example
  a6lut->amux 0.071/0.088/0.168/0.209 ns, and the O5 path a5lut->amux. It was added in C-10h.
  - C-10m checked it arc by arc against the auditor's independent `xrc.py`. On gcd_hw seed 4
    the two models agree on all 86,037 common arcs within 11 ps when the xMUX/xMUXL hull is set
    aside; the hull costs at most +34 ps at slow max.
  - The remaining OUTMUX bug, in the Jx shared split, is fixed. All 72 J clients now match xrc
    within 15 ps.
- **"J 67/70" is superseded by 71/72** (C-10h's tally; C-10m keeps it with corrected margins).
  | row | before (10g) | now |
  |---|---|---|
  | seed d merge6.uarb1#1 (BQ#1) | -10/-8 FAIL | **PASS**, 370/885/102/262; xrc 372/887/107/266. The 10g FAIL was an artefact of the missing hop. |
  | seed 2 merge12.uarb1#1 | -35/-86 FAIL | PASS, thin: 222/523/16/44 |
  | seed 4 merge12.uarb2#2 | -9 fastG | **FAIL**, worse: 142/383/-116/-204; xrc -111/-201. A0 reaches ua2 through DMUX. Band-only. |
- **"SDF low by +490 ps on A1"** was a mean, without the OUTMUX hop, at the slow corner only.
  With the hop, on a 4000-net sample of seed d, the mean is **+609**: p10 404, p90 772, max 2204;
  nets through an xMUX alone +696. At FAST_MIN the SDF is *high* by 200-557 ps mean per pin.
- **"J's estimate over-credits about 95 ps on average, permissive on 69/70"** is superseded.
  With the hop:
  - mean 28-66 ps per seed, max 88-162;
  - the pip estimate **under**-credits on 1-4 clients per seed, down to -353 ps (seed d merge9).
  - This matches the audit.
- **RT_FB uenv1 on seeds 2 and 4.** The 10g values (-7/+25 and -37/-95) are superseded by
  C-10h's, which C-10m confirms: seed 2 44/162/-117/-221 (xrc -114/-219), seed 4
  94/161/-86/-243 (xrc -81/-201; the difference is the hull). Band-only.
- **The F seed d ucmpi8 "fallback, front-end gap" explanation is superseded** (audit row 6). It
  is a guard-versus-band row: -498/-497 banded, +941/+2300 unbanded (C-10h).
- **Rule A false path (C-10n finding).** Rule A in rules2.py mirrored
  `tighten.cell_boundary`, which keeps the GND/VCC tie-off drivers as starts.
  - It now drops them. On these routes this raises 18 A rows (ucmpi2/3, uori2/3/4), with no
    verdict change.
- **Unchanged:** every remaining disagreement is band-only on a prjxray corner. The
  algorithm-agreement statements (sdf columns equal the rules' raw margins) still hold.
