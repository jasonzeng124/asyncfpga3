# C-10h: tcheck phase 3. Closing the trust gaps (H_EXTRACT_MIN, fallback arcs)

Shard C, probe 10h, 2026-10-27.

## Verdict

**It works. Both gaps named in C-10g are closed, apart from the residual fallback listed below.**

- **(b) H_EXTRACT_MIN is gone for rules H, F and R.** The late sides are no longer a path a
  Python Dijkstra picked. tcheck now gets the whole routed graph, which is cyclic, and
  checks a potential on every arc. The new theorem `Formal.Timing.pot_sound` makes any
  potential that passes the check a sound lower bound, so the extractor's choice is no
  longer trusted.
  - The old chain was **not** the minimum on 277-352 of the 948 prjxray H variant-rows per
    seed. It was too high by up to 1147 ps. In 10g's terms that makes the old H late side
    unsound.
  - No verdict depended on it: the lowest corrected guarded margin among those rows is
    +753 ps.
- **(a) Fallback arcs:**
  - **Added from prjxray-db:** CARRY4 cell arcs, the LUT→CARRY4 S/DI site hops, AX→DI
    through the CY0 mux, the wide-mux select nets (AX/CX/BX), and LV/LVB long lines used
    in their reverse direction.
  - **A fix on the optimistic side:** the driver-side site hop (a5lut→amux,
    carry4_o→xmux, f7amux→amux, and so on). 10e/10g left it out, which was optimistic.
  - **Result:** every class-3 ("front-end gap") disagreement of 10g is gone:
    - rule A: 28 rows down to 1, and that one is now a band finding;
    - F ucmpi8: now a band finding;
    - J merge9: Jx now exists.
  - fasm2lean's "floating node" errors fell from 83-133 per route to 55. All 55 are the
  BSCAN (JTAG) site outputs, which feed debug logic outside udut; none is a long line.
- **(c) Re-run on the 4 gcd_hw routes:**
  - **No disagreement is a front-end gap any more.** All 33 disagreeing project rows (61
    lines in disagree3.tsv, one per row and flavour) are "project PASS, tcheck FAIL only
    under the 0.772/1.155 band on a prjxray corner".
  - The unguarded fast and slow corners pass on every one of them.
- **Traced:**
  - **A (the 15/200 rows):** a reporting difference. tighten prints the raw margin of its
    worst *guarded* pair; tcheck's `sdf` margin equals tighten's own *minimum* raw margin
    on all 15 (traceA.py).
  - **F (the 1/116 row):** tcheck's data side for that line is looser (more conservative)
    than tighten's, by design (see below).

## What is proved (no sorry, axiom or native_decide; audit = propext, Classical.choice, Quot.sound)

`formal/lean/Formal/Timing/Unroll.lean` (core Lean, compiled with `slot.sh lean`, olean in
formal/lean/.lake/build) is copied verbatim into tcheck by `sync.sh`, which checks it as a
5th module:

- **`pin_cause`.** Under H_BOUNDED_DELAY and H_QUIESCENT, a pin that changes at t copies a
  source change at some s with s + lo ≤ t.
- **`pot_sound` / `potOK_sound`.** For ANY netlist, cyclic included, and 10a's unchanged
  `Run`:
  - **The check:** every arc a with dst ≠ 0 satisfies `pot dst ≤ rho pot src + lo`, where
    `rho` is 0 at the launch. Also, `lo = 0 → src < dst`, which makes the induction over
    zero-delay arcs well-founded.
  - **The conclusion:** every change of a node v ≠ 0 happens at a time ≥ pot v.
  - **The proof:** strong induction on time, then on node index.
  - The capped Dijkstra distance `min(dist, C)` always passes the check. **Tightness**
    (that the bound equals the earliest change) **is not proved.** It is shown
    empirically: on the `sdf` variant, H, F and R are identical to 10g's chain on every
    row of every seed.

`formal/tools/tcheck/Tcheck/Cert.lean`:
- **`Late`, `expand`, `switches`, `lateNet`.** The per-obligation phase rule over the
  global graph. It is the modelling content, stated in Lean (see the Hypotheses section).
- **`lateOK_eq`.** The streaming check equals `potOK` on `lateNet`.
- **`cverdict_sound`.** Suppose:
  - tcheck prints PASS for a cert obligation;
  - the data side is a `Run` of the emitted DAG;
  - the response is a `Run` of `lateNet` (same launch, at time 0).

  Then every data change precedes every target change by at least `setup`.

tcheck prints **CERTBAD** when the potential fails the check. This is a negative control:
`test/toycert.tc` contains a lie, a claimed 500 where the true minimum is 180, and it is
rejected.

## Files (all under formal/tools/tcheck/ unless stated)

| file | what |
|---|---|
| `formal/lean/Formal/Timing/Unroll.lean` | the theorem above (new) |
| `Tcheck/Cert.lean` | phase rule, cert verdict and its soundness (new) |
| `Main.lean` | parser: adds `graph`/`g`/`stor` (global graph, 6 intervals per arc, FASTRISE flag), `late`/`sw`/`blocked`/`target`/`cap`/`pot` (per instance); `CERTBAD` tag |
| `sync.sh` | Unroll.lean added to the copied modules |
| `certs.py` | numbering (topological order of zero-lo arcs), graph emission, product Dijkstra mirroring `Tcheck.expand`, the potential |
| `extract.py` | `--cert` (Hc), `--only`; Prjx: `site_tables` (every ROUTING_BEL hop and CARRY4* IOPATH, hulled), CARRY4 cell arcs, S/DI/select sinks, driver-side hop, `_bidir` (reverse long-line pips), split() includes the hops; census separates constant drivers |
| `rules2.py`, `rules3.py` | Fc, Rc emission (the 10g F, R kept alongside for comparison) |
| `compare2.py` | run tag argument; F rows also for Fc |
| `cmpcert.py` | 10g chain vs cert per obligation and variant |
| `summarize3.py` | `results/agree3.tsv`, `disagree3.tsv`, `unchecked3.tsv`, `cert3.tsv`, `fallback3.tsv` |
| `traceA.py` | rule A with guard 0 (the min raw margin) vs the guarded pair's raw |
| `run4.sh` | the pipeline |
| `test/toycert.tc`, `.expected`; `test/Axioms.lean` | cert self-test; axiom audit (now includes `pot_sound`, `cverdict_sound`) |
| `results/compare5_*.tsv`, `cmpcert5_*.tsv` | row-by-row tables of this run |

## Run

    cd formal/tools/tcheck
    ./run4.sh d 2 3 4     # sync --check (5 modules), lake build with FORMAL_SLOT_CWD, toy + cert
                          # self-tests, then per seed in parallel: one extract (all rules + Hc/Fc/Rc),
                          # tcheck, compare.py (H, I, Hc), compare2.py (A, E, F/Fc, J), cmpcert.py;
                          # summarize3.py
    FORMAL_SLOT_CWD=$PWD ../../slot.sh lake env lean test/Axioms.lean
    python3 traceA.py SEED

- **Time and memory per seed:** extract takes about 6 min with 4 in parallel, at 1.05 GB
  each; tcheck takes about 2 min for 15738 instances (the cert check streams about 90k
  arcs × 2 phases per instance). The .tc file is about 230 MB.
- **Self-tests and drift check:** `sync.sh --check` and both self-tests pass.

## Agreement (results/agree3.tsv; project verdict vs tcheck PASS at fastG and slowG; agree/NO/not comparable)

| rule | flavour | d | 2 | 3 | 4 | total | 10g |
|---|---|---|---|---|---|---|---|
| A | | 50/0/0 | 50/0/0 | 49/1/0 | 50/0/0 | **199/200** | 172/200 |
| E | credited (E) | 116/2/0 | 116/2/0 | 117/1/0 | 116/2/0 | 465/472 | 465/472 |
| E | no credit (E0) | 115/3/0 | 114/4/0 | 116/2/0 | 115/3/0 | 460/472 | 458/472 |
| F | F (10g chain) | 28/1/0 | 29/0/0 | 28/1/0 | 28/1/0 | 113/116 | 113/116 |
| F | **Fc (cert)** | 28/1/0 | 29/0/0 | 28/1/0 | 28/1/0 | 113/116 | |
| H | H (10e chain) | 157/1/21 | 157/1/21 | 158/0/21 | 158/0/21 | 630/632 | 630/632 |
| H | **Hc (cert)** | 157/1/21 | 157/1/21 | 158/0/21 | 158/0/21 | 630/632 | |
| I | | 75/0/104 | 75/0/104 | 75/0/104 | 75/0/104 | 300/300 | 300/300 |
| J | J0 | 14/4/0 | 14/4/0 | 13/5/0 | 16/2/0 | 57/72 | 57/72 |
| J | Jx (exact shared) | 18/0/0 | 18/0/0 | 18/0/0 | 17/1/0 | **71/72** | 67/70 |
| J | Jp | 14/4/0 | 14/4/0 | 13/5/0 | 16/2/0 | 57/72 | 57/72 |

The project rules still report every row PASS, so every disagreement is "project PASS,
tcheck FAIL".

### Findings vs front-end gaps

**Front-end gaps among the disagreements: none.**
- No disagreeing row has a fallback arc on its critical path. Checked with diag.py on A
  shrsi1 and F ucmpi8; the census follows.
- The 10g class-3 rows resolved as follows:
  - **A, 27 of 28 now agree.** The one left, seed 3 shrsi1, has no fallback on either
    critical path. Its data side holds a 3446-ps SDF wire, 2225..2453 at prjxray fast.
    The result is fastG -339, fast +2512, slowG +1641: a band finding.
  - **F seed d ucmpi8.** Its head-input net was the floating LVB line; it now has prjxray
    numbers. The result is fastG -498 / slowG -497, unguarded +941 / +2300. It stays a
    disagreement, but it is now a finding, not a gap.
  - **J seed d merge9.** The A0 nets now resolve, so Jx exists for both clients and both
    agree. J0 (no credit) fails at -770 / -1237, and unguarded passes.

**Findings: every one is class "band on a prjxray corner only".** Unguarded fast and slow
pass on all 33 disagreeing project rows. The mechanisms are the ones 10g quantified:
- the site-pin delay the SDF misses (E, J, R);
- a long LUT-chain request shrinking to the fast corner while the band still applies to
  the data (A shrsi1, the E0 rows);
- `max(0.2 t, 200)` being weaker than the band on short races (F merge12 on seeds 3 and 4;
  H falseResult_55 on seed d and n143 on seed 2, now -28/-9 and -1/-74).

### Unchecked obligations (results/unchecked3.tsv)

**W (open width).** Minimum +346 ps at fastG and +832 ps at slowG. W never used a Dijkstra:
its late side is 10e's all-paths segment DAG. The 10g note listing W under H_EXTRACT_MIN
was wrong. W rests on H_SEGMENT instead.

**R and Rc (RT_FB).** The cert values are identical to the chain values except 1 variant-row
on seed d, 3 ps lower. 112 of the 526 storage nodes per seed have no path back to another
pin of the node; those PASS vacuously and are listed as "vacuous". The other 414 are 10g's
R rows.

| seed | min fastG | min slowG | FAIL | worst |
|---|---|---|---|---|
| d | +23 | +19 | 0 | ucontrol_merge10.uarb1.ua2.u |
| 2 | **-117** | **-221** | 1 | urig.uenv1.u (fast +44, slow +162) |
| 3 | +225 | +347 | 0 | urig.uenv1.u |
| 4 | **-86** | **-243** | 1 | urig.uenv1.u (fast +94, slow +161) |

- These are worse than 10g's numbers (-7/+25 and -37/-95). The cause is the driver-side hop
  10e/10g omitted: uenv1's O6 leaves through a xMUX site pin, which adds +166..239 ps at
  slow to both the feedback wire and the response's first net.
- R gives no credit for that shared prefix, so the band is charged on it twice.
- Still band-only, but the environment C-element's RT_FB is the thinnest real race on the
  shipped bitstream.

### Late side: 10g chain vs cert (results/cert3.tsv, cmpcert5_*.tsv)

| seed | Hc: rows equal / cert lower | max drop | Fc | Rc lower |
|---|---|---|---|---|
| d | 638 / 310 | 1027 ps | 174 equal | 1 (3 ps) |
| 2 | 616 / 332 | 977 ps | 174 equal | 0 |
| 3 | 671 / 277 | 1147 ps | 174 equal | 0 |
| 4 | 596 / 352 | 1029 ps | 174 equal | 0 |

- **Every lower row is on a prjxray variant, never `sdf`.** 10e's H chain was chosen on the
  SDF numbers only, so at the prjxray corners a different disturbance path is shorter.
- **No verdict flips:** the lowest new fastG/slowG margin among the changed rows is +753 ps.
- **21 H obligations per seed have no disturbance path at all.** These are the "-" rows
  that both tools leave unaudited (tighten's t_ext case, the D pins being driven from
  outside). They are now PASS by proof but vacuous; the report lists them, they are not
  counted as covered.

## The two traces asked for

### A, the 15 rows where tcheck's `sdf` margin is lower than the rule's raw margin

- `T.check` returns the pair (start, peer) that minimises the guarded margin
  `t_e - t_l - max(0.2 t_l, 200)`, and compare2 reports that pair's raw `t_e - t_l`.
- tcheck reports the minimum raw margin over all pairs.
- With the guard set to 0, tighten's own `check` gives the tcheck number on all 15 rows,
  to the picosecond (`traceA.py d|2|3|4`). The rows are ucontrol_merge2/3/4/6/11/12 and
  the differences are -2..-367 ps.
- So this is not an algorithm difference. The guarded verdict is unaffected (tighten's
  guarded minimum is correct). Only the printed "raw" belongs to a different pair.

### F, the 1 row (seed 2 uselect1.udly, -141 ps)

- **The request side is the same in both:** t_reuse is 5923 ps in tighten and in tcheck.
- **The difference is on the data side:** tighten's t_flush is 1617 ps, tcheck's latest
  data is 1758 ps.
- tighten bounds each AND stage by min(ripple, side tap), because a controlling 0 on
  either input forces the stage low. tcheck uses the side tap alone (H_CONTROLLING). The
  10a node model is a hull, so a "fires on the earlier input" node cannot be expressed in
  it.
- On this line one stage's ripple (1617) is earlier than its side tap (1634 + 124). Both
  are sound upper bounds under H_CONTROLLING; tcheck's is looser.
- Closing it needs a min-node (AND with a controlling value) in the 10a semantics. That is
  a new theorem, not a front-end change.

## Fallback census (results/fallback3.tsv; whole graph, 89974 arcs per route)

The graph now has prjxray numbers on 80102 arcs and the SDF band on 9870-9872. Of those:
- **7815-7817 are driven by the packer's constant drivers.** These never switch, so no
  interval on them matters.
- **686 are F7→F8 site-internal arcs.** The SDF number is 0, so the band is [0,0], and
  prjxray-db has no entry for them. That is optimistic by less than about 25 ps (C-10g).
- **1253 are FF arcs** (D, CE, CK, SR, Q): the environment's clocked logic. Not added.
- **47 are CARRY4 CIN.** This is the dedicated COUT→CIN cascade, which has no db number.
- **48 are LUT pins with a non-SLICE driver** (IOB, BUFG, BSCAN) or a walk failure.
- **About 30 are BUFG/IOB arcs.**

Per instance (data DAGs only), the instances with a fallback arc are:
- A: 108 of 546;
- E0: 2076 of 3576;
- R (10g chain): 18-48 of 2484;
- all others: 0.

These were not classified per instance. The graph census suggests the F7→F8 [0,0] hops,
but that is not checked.

## Hypotheses: every remaining trusted component

**Trusted code:**
1. **The Lean compiler and runtime** (`lake exe`).
2. **The tcheck parser (`Main.lean`, about 200 lines).** Only the parse is trusted: it must
   build the instance from the text faithfully. The potential it builds is not trusted;
   any array is checked.

**What the front end emits (untrusted Python; the theorems are about what it emits):**

3. **H_NETLIST.** The graph is the routed circuit: nextpnr SDF IOPATH and INTERCONNECT arcs,
   false arcs cut by LUT INIT (tighten), the `--osc` instruments cut, and storage = tighten's
   census.
4. **H_ONE_CORNER plus band.** The die sits at one prjxray corner, and each element lies
   within 0.772/1.155 of that corner's interval. H_RC_EXACT: Elmore RC per sink.
5. **prjxray-db numbers.** New choices in this probe:
   - **Hull** over the CARRY4* celltypes (DI source and output-load variants) and over the
     xMUX/xMUXL and xFF/xFFL hop instances. The hull is sound if the site's real
     configuration is one of them.
   - **The wide-mux select** (AX/CX/BX → S0) has no db sink hop, so it is taken as direct.
   - **H_BIDIR.** A long line driven from its far end uses the bidirectional pip's
     `dst_to_src` delay.
6. **H_FALLBACK_BAND** on the arcs counted above.
7. **10a `Run` semantics, now on cyclic late-side netlists too.**
   - Its hypotheses are H_LAUNCH, H_BOUNDED_DELAY, H_QUIESCENT, H_LOCAL and
     H_ZERO_DELAY_FN.
   - **On a cyclic graph:** the only spontaneous event is the launch. Every other change
     has an input-change cause ("OR-causal"). That is a lower bound for any gate,
     C-elements included, *under quiescence*.
   - **H_COMMON_LAUNCH.** The data-side DAG run and the late-side run are the same
     physical response, launched at time 0. This is a hypothesis of `cverdict_sound`.
8. **Phase rules (Tcheck.Late), stated in Lean:**
   - **H_POLARITY.** FASTRISE-side arcs are inert on a falling wave until a state node fires
     (Hc phase 0, Fc phase 0).
   - **H_OWN_LATCH_CLOSED.** ctl's own latch bits do not propagate (Hc `blocked`).
   - **H_F_THROUGH_TAIL.** src's next rise is caused through the line's tail, and the
     falling wave does not leave storage before the tail (Fc).
9. **Data-side shapes, as in 10e/10g:**
   - **H_SEGMENT:** the I and W request sides, and every segment's storage stop.
   - **H_CONTROLLING (F), H_BUNDLED_T0 (A bundled), H_LEVEL and H_CLEAN_EDGE at X (E),
     H_ONE_SAMPLE_PER_WIRE (Jx).**
10. **Obligation identification** comes from tighten's helpers (request_sites, peers,
    latch_enables, ...). It is unverified, and it is linked to 8e's races by hand.
11. **The comparison scripts** (compare*.py, cmpcert.py, summarize3.py, diag.py,
    traceA.py). They are reporting only; no verdict depends on them.

**Removed by this probe:**
- **H_EXTRACT_MIN** for H, F and R.
- **The silent omission of the driver-side site hop.** This was an optimistic,
  unstated gap in 10e/10g.

## Effort to finish and what it buys

- **Remaining fallback, about half a day.** The FF arcs (FF_INIT/REG_INIT cell types,
  CE/CLK/D sinks), CARRY4 CIN (cascade wire), and non-SLICE drivers. None of these is on
  a disagreeing row.
- **A min-node in 10a, about 1 day of Lean.** It would remove F's conservatism and turn
  H_CONTROLLING into a proved node property. The node is an AND with a controlling value:
  the output falls at the earliest controlling input.
- **I and W request sides, about half a day.** Give them the same cert treatment, with an
  AND rule for the C-element (which input must be awaited). That would trade H_SEGMENT
  for a stated C-element rule.
- **What it buys now.** Every late side that was a Python choice is now a checked
  certificate. The front end is down to structural claims, and every disagreement on 4
  routes is a stated finding about the band on prjxray corners, none a gap. It also
  surfaced one optimistic gap in the old prjxray numbers: the driver-side site hop, worth
  up to about 0.24 ns at slow per net driven through a xMUX pin.

## Decisions taken (no one to ask)

- **A potential certificate on the cyclic graph instead of an unrolled DAG.** An unrolled
  DAG of a cyclic graph is either infinite or cut at a depth Python chooses, and that
  choice would be a new trusted component. The certificate needs no unrolling, its
  soundness does not depend on Python at all, and the proof is about 60 lines.
  - So "Unroll.lean" holds the theorem that the checked bound is at most the earliest
    window of the (infinitely) unrolled graph.
- **The 10g chain instances are kept alongside** (H, F, R next to Hc, Fc, Rc) so that every
  change is measured. The verdict to use is the cert one.
- **The H phase rule allows FASTRISE arcs out of a state node in phase 0.** This mirrors
  the old Dijkstra, which used the next phase. With that rule, `sdf` agrees on every row.
- **Constant drivers stay in the graph.** Their arcs are harmless, because a node with no
  changing input never changes.
- **No git; nothing outside the owned files was edited.** fasm2lean's long-line issue is
  fixed by adding reverse pips in extract.py before Extract is built. fasm2lean.py itself
  is unchanged.
