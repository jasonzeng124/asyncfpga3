# Probe Bp: which physical LUT pin carries the feedback and handshake nets

Shard B, 2026-10-27. File: `formal/lean/Formal/Cells/PinAssign.lean` (285 lines). It
imports `Formal.Cells.Prelim` and C's generated, drift-checked fixture modules
`Formal.Net.Fasm.CePairS1..4` and `Formal.Net.FasmLink.S1..4` (read-only, through
their existing oleans).

Check command (it checks clean in about 11 s wall, with no errors and no warnings):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/PinAssign.lean

`#print axioms` was run on a scratch copy for all 88 theorems:
- 86 use only `[propext]`;
- 2 use `[propext, Quot.sound]`.

There is no sorry, admit, axiom or native_decide. Every proof is a plain `decide`.

**No routing was done, and no routed numbers are new.** Every route here comes from C's
committed fixtures. Their toolchain stamps (`*.toolchain`) say: `toolchain.sh` ok, and
**nextpnr sha256 9c732bc6303458df**, with the lut-pinmap and lut-perm-sink patches.

## Method (from the bits, not from guesses)

1. **prjxray-db.** The container has no `$TC`, so I fetched f4pga/prjxray-db master
   `0a0addedd73e7e4139d52a6d8db4258763e0f1f3` (2021-12-14) into the scratchpad. I fetched
   only the zynq7 tile_type/ppips/tilegrid/tileconn/package_pins/timings files.
2. **Re-running C's importer.** I ran C's importers (`fasm2lean2.py` and `fasm2lean.py`,
   unchanged, with `--db` pointing at that checkout) on the **read-back** FASM
   (`*.fromBit.fasm`) of:
   - link_arb s1..4;
   - ce_pair s1..4;
   - muller64 s1 (routed2lean fixture).

   All outputs went to the scratchpad.
3. **Proof that the database matches.** For all 8 two-cell and link_arb seeds, the
   regenerated LUT, pin-source and `pinDelay` blocks are **byte-identical** to C's
   committed `S<n>.lean` and `CePairS<n>.lean`. So this database gives the same sources
   and delays that C's database gave.
4. **Matching each LUT to its cell.** For each LUT, I enumerated every bijection from the
   cell's logical non-constant inputs (the real INIT from `cells/rtl`) to the physical
   non-tied pins. I kept the bijections under which the **physical INIT**, with the tied
   pins as wired, equals the logical INIT. For LUT6_2 cells this is checked on O6 and O5.
5. **Separating symmetric inputs.** The INIT alone leaves ambiguity:
   - 2 maps for bd_c2n (a and q are symmetric);
   - 6 maps for bd_c2 (a, b and q are symmetric).

   Requiring each pin's **source net**, found by walking the active pips, to be the net
   the logical input names (its own output for the feedback) leaves **exactly one map in
   every case** (36 of 36 LUTs, plus 64 of 64 in muller64).
6. **Cross-check against the SDF.** nextpnr's SDF INTERCONNECT sink pins are physical
   after the lut-pinmap patch. They agree with the FASM-derived pin for all 11 checked
   nets × 4 seeds (fb ctl/ua1/ua2, A0→ua1/ua2/ustate, req/ack→ctl, q→ugrant, g1/g2→ua).
7. **Cross-check against C-10d.** The muller64 feedback pins agree 64/64 with C-10d's
   independent `muller64_rt.txt`.

Lean (`PinAssign.lean`) proves both halves of the map for every one of the 36 LUTs:
- `<inst>_o6` / `_o5` : `Realizes L o F vec pm nv = true`. The physical INIT on the
  permuted pins, with the other pins at their ties, equals the real logical INIT, for
  all Boolean inputs. `Realizes.sound` turns this into the ∀ statement.
- `<inst>_src` : the pins in `pm` are wired, in C's bit-derived `PLut.pins`, to the
  expected nets. Examples are `(.lut 0 .o6)` for the own feedback and `(.port 7)` for
  req_in.
- `c2n_init_symmetric` (ce_pair s4): the map with feedback and req swapped also
  realizes the INIT. So the `_src` half is necessary.
- `wrong_map_fails`: this is the negative control. Swapping ack and feedback gives
  `Realizes … = false`, so the check can fail.

Scripts (scratch, not in the repo):
`/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/pins/pinassign.py`
(analysis), `genlean.py` (emits the Lean file), `m64join.py` and `latch.py`. The full
output is in `report_corner.txt` and `report_risefall.txt` in the same directory.

## 1. Pin maps (physical pin per logical input; the pin index k is "A_k" of that LUT letter)

link_arb (bd_link W=3 + bd_arbiter), seeds 1..4:

| inst | s1 | s2 | s3 | s4 |
|---|---|---|---|---|
| ctl bd_c2n (req, ack=c_next, **fb**, rst) | C2, C3, **C4**, C1 | C3, C2, **C1**, C5 | D5, D2, **D4**, D1 | B5, B3, **B4**, B1 |
| ua1 bd_c2 (g1, A0, **fb**, rst) | D2, D3, **D5**, D1 | C4, C3, **C5**, C1 | D4, D1, **D5**, D3 | C4, C3, **C1**, C2 |
| ua2 bd_c2 (g2, A0, **fb**, rst) | C4, C2, **C3**, C1 | A2, A1, **A5**, A3 | C4, C2, **C1**, C5 | D2, D1, **D5**, D4 |
| ustate (r1, r2, **fb q**, rst, A0) | A3, A4, **A5**, A1, A2 | A3, A2, **A5**, A1, A4 | A5, A2, **A1**, A3, A4 | A1, A4, **A5**, A3, A2 |
| ugrant (r1, r2, q) | A1, A4, A5 | A1, A5, A3 | A3, A2, A5 | A3, A2, A5 |
| latch pair (d0, en, **fb0**, d1, **fb1**) | A5, A3, **A2**, A4, **A1** | A3, A4, **A2**, A1, **A5** | A2, A4, **A5**, A3, **A1** | A4, A2, **A5**, A3, **A1** |
| latch odd (d, en, **fb**) | D1, D3, **D5** | D5, D1, **D2** | A4, A2, **A5** | C2, C3, **C1** |

ce_pair (u1 = bd_c2 C(a,b); u2 = bd_c2n C(q1,~c)):

| inst | s1 | s2 | s3 | s4 |
|---|---|---|---|---|
| u1 (a, b, **fb**, rst) | B4, B3, **B1**, B2 | A3, A4, **A5**, A2 | B3, B4, **B1**, B5 | C3, C2, **C4**, C1 |
| u2 (req=q1, ack=c, **fb**, rst) | A1, A4, **A5**, A3 | B5, B3, **B1**, B4 | A1, A5, **A2**, A3 | B5, B3, **B1**, B4 |

**A feedback lands on pin 1 (the slowest site pin) in:**
- ctl 1/4;
- ce u2 2/4;
- ce u1 2/4;
- ua1 1/4;
- ua2 1/4;
- ustate 1/4;
- **latch pair O6 bit 3/4**;
- latch odd 1/4;
- muller64: **24/64** (one route; pin histogram {1: 24, 2: 1, 3: 1, 4: 13, 5: 25}).

A6 is never used by a cell input here. It is VCC on the fractured LUTs, and GND or VCC on
the others.

**Bq's unverified reading is settled:**
- ce_pair s1: the feedback is on A5. Correct.
- ce_pair s4: the feedback is on **B1** with req on B5. Correct, the unfavourable case.
- ce_pair s2: the feedback is also on B1. Bq's table left this one open.
- ce_pair s3: the feedback is on A2, with req on A1.

Bq's "LOGIC_OUTS17 = own output" is confirmed: the `_src` theorem shows `(.lut 0 .o6)`.

## 2. Bq's per-pin term `pq − min(pr, pa)` per controller (ps)

Site-pin delays are the exact tile type's (prjxray `tile_type_CLBLM_R.json`). SLICEM pins
are slower than SLICEL/CLBLL pins:
- SLICEM: A1 [180, 225, 428, 531], D1 slow max 540;
- SLICEL: A1 [172, 214, 416, 516].

So I used each pin's own value, not the CLBLL_L table.

Corner readings:
- **slow** = q at slow_max, inputs at slow_min;
- **fast** = q at fast_max, inputs at fast_min;
- **box** = q at slow_max, inputs at fast_min.

| controller | s1 | s2 | s3 | s4 | mean [range], slow | fast | box |
|---|---|---|---|---|---|---|---|
| link ctl (bd_c2n) slow | −2 | +234 | +245 | +189 | **+166 [−2, +245]** | +66 [−2, +105] | +278 [+171, +407] |
| ce_pair u2 (bd_c2n) slow | −118 | +425 | +410 | +425 | **+286 [−118, +425]** | +123 [−43, +179] | +369 [+35, +484] |
| ce_pair u1 (bd_c2) slow | +279 | −117 | +279 | −2 | +110 [−117, +279] | +52 [−44, +128] | +265 [+26, +431] |
| arb ua1 (bd_c2, inputs g1, A0) slow | −166 | −113 | −39 | +279 | −10 [−166, +279] | −1 [−67, +130] | +132 [+4, +432] |
| arb ua2 (bd_c2, inputs g2, A0) slow | +126 | −287 | +290 | −297 | −42 [−297, +290] | −19 [−129, +128] | +151 [−58, +430] |

**The resulting minimum environment answer time.** Combining the term with the feedback
route gives `E_need = (fb route slow_max + Elmore) + pq.slow_max − min(pr, pa).fast_min`.
This is the latency, at the pins, that H_SEL_ORDER requires of the environment in the box
reading:
- link ctl: **+544 [+335, +805] ps**;
- ce u2: +584 [+197, +825];
- ua1: +332 [+167, +600];
- ua2: +351 [+103, +598].

**muller64** is one route with 64 bd_c2n. Over its stages the Bq slow term has:
- mean +105, median +2, range [−297, +425];
- a positive value on 35/64 stages.

I joined it per stage with C-10d's exact routed RT_FB check, the same ordering condition
evaluated with real neighbours (`muller64_rt.txt`, slowE). **Every one of the 12 RT_FB
failures has a positive term:**
- 11 of them have terms of +410 to +425 (feedback on pin 1);
- one has +128 (feedback on A3 via a 7-pip detour);
- **no stage with term ≤ +100 fails** (33 stages).

So, on the one fixture where the environment is routed, the per-pin term is what
separates failing stages from passing ones.

## 3. 7g's site-pin correction per arbiter client (ps)

`corr = (pSt + pQG + pGC − pAC) − 2·25`, where:
- pSt: A0 on ustate;
- pQG: q on ugrant;
- pGC: g_k on ua_k;
- pAC: A0 on ua_k.

Corner readings:
- slow = early at slow_min, late at slow_max;
- fast = fast_min against fast_max;
- box = fast_min against slow_max;
- 7g-lit = everything at slow_max, which is 7g's "same slow corner".

| client | s1 | s2 | s3 | s4 | slow mean [range] | fast | box | 7g-lit |
|---|---|---|---|---|---|---|---|---|
| 1 (pins A0@ust / q@ug / g@ua / A0@ua) | A2/A5/D2/D3 | A4/A3/C4/C3 | A4/A5/D4/D1 | A2/A5/C4/C3 | +292 [−68, +529] | +85 [−74, +197] | **−157 [−388, −13]** | +496 [+156, +751] |
| 2 | A2/A5/C4/C2 | A4/A3/A2/A1 | A4/A5/C4/C2 | A2/A5/D2/D1 | +236 [+16, +376] | +53 [−47, +117] | **−247 [−341, −189]** | +429 [+153, +606] |

In 3 of the 8 client-seeds, A0 lands on pin 1 of ua_k (s2 client2, s3 client1, s4
client2). That is 7g's worst assignment for the late branch.

The **box** correction is negative on 8/8, at −13 to −388 ps. That is inside 7g's bound
of −498 ps for the worst assignment, and up to ~0.4 ns in practice.

Rule J itself, recomputed raw from each fixture's nextpnr SDF:
- unguarded, where c cancels: client 1 +1350 [+910, +1959], client 2 +1441 [+1123, +1696];
- guarded at 0.772/1.155 with **no** shared-prefix credit (a lower bound on rule J):
  client 1 +628 [+299, +1122], client 2 +699 [+464, +838];
- the same plus the box site-pin correction: client 1 **+472 [+225, +734]**, client 2
  **+452 [+209, +565]**.

**So on these 4 routes the site-pin term does not flip rule J.** Caveat: A0 here comes
from a pad, and both branches are long (SDF 984–1053 ps). An in-design A0 from a nearby
LUT has much shorter branches, where 7g's survey minimum (+618 raw) is the relevant scale.

**The fork margin computed entirely from prjxray** (C's per-pip intervals, unshared pips
only; the late side carries its full Elmore, which is conservative):

| reading | client 1, 4 seeds | client 2, 4 seeds |
|---|---|---|
| same-die slow corner | +973 [+757, +1149] | +983 [+711, +1148] |
| same-die fast corner | +317 [+234, +377] | +308 [+197, +376] |
| independent box (H_INDEP, early fast_min vs late slow_max) | −113 [−280, −5] | −181 [−305, −98] |

The table uses C's corner reading of the LUT arcs.
- Under the **independent box** the condition fails on 8/8, which is expected: that box is
  ~3× wider than any guardband.
- Under either same-die corner it passes on 8/8.

**Arc-reading discrepancy (flag for 7g).** prjxray's `timings/CLBLM_R.sdf` writes
`(IOPATH A1 O6 (0.045::0.056)(0.100::0.124))`:
- 7g read the two triples as **rise/fall**;
- C-10b/C-10d (routed2lean) read them as **fast/slow corners**.

These give different early-side arc credits. Under 7g's reading client 2 has +55 ps more
in the box and ~−55 ps less at the slow corner. Totals under 7g's reading are in
`report_risefall.txt`. They do not change any sign above. I did not resolve which reading
is right. [Resolved after the audit (REPORT row 10, REFUTED): the corner reading is right;
`prjxray/utils/makesdf.py:63` writes `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`, so 56/124
is FAST_MAX/SLOW_MAX of one arc. 7g's rise/fall totals (`report_risefall.txt`) are
withdrawn; corrected arc credits are `ArbCorners.ruleJ_arcs` (B-arb-corners.md §3).]

## 4. Side finding: latch hold term (site pins only)

A latch closes when its en select switches. The data pin must hold until then, so the
hold term is `en_pin − d_pin`. Over 4 seeds:

| latch | slow | box |
|---|---|---|
| pair | +81 [−125, +270] | +258 [+123, +421] |
| odd | +158 [−75, +468] | +324 [+172, +509] |

The SDF does not see this term either.

## 5. What the fixtures can and cannot tell

**Can:**
- the exact physical pin per logical input, from the bits (proved in Lean against C's
  bit-derived `PLut`s, and cross-checked against the SDF and C-10d);
- site-pin delays of the exact tile and slice type (prjxray tile json, four corners);
- prjxray intrinsic per-pip intervals plus an Elmore term per sink (C's `pinDelay`,
  labelled by C as "not yet cross-checked against prjxray/timing.py or the board").

**Cannot:**
- **Environments.** The environments are pads (ce_pair, link_arb), so `E_τ` for the
  controllers is not a routed quantity. Only E_need is given.
- **In-design arbiters.** A0 is a pad, so the arbiter fork is not representative of
  in-design arbiters.
- **Seeds.** Only 4 seeds per design (muller64: 1 route, used only as a per-instance
  census, never as a margin across seeds).
- **Silicon.** No board or silicon delays: prjxray's corners are a model.
- **Corner correlation.** "Same-die corner" vs "independent box" is a choice of model
  (H_ONE_CORNER vs H_INDEP), not something the fixtures decide.
- **Wire delays in the SDF.** These fixtures' SDF carries nextpnr's wire delays but no
  per-pin site delay (a flat 25 ps).
- **Other cells.** No placement-rule fixtures exist for bd_c2n inside the shipped flow
  (RLOC groups), so the pin-1 rate for real designs is not measured. Here it is 24/64
  (muller64), 12/36 feedback pins (4-seed fixtures), and 3/4 for the latch-pair O6 feedback.

## Verdict

**Works.** The pin maps are now proved from the bits (88 theorems, plain `decide`, ~11 s).
The per-pin terms are tabulated on 4 seeds:
- **Bq's H_SEL_ORDER term is real and frequent.** On the controllers, the slow-corner
  mean is +166 ps (link ctl) and +286 ps (ce u2), with a maximum of +425. On the
  routed-environment fixture (muller64) it predicts exactly C-10d's RT_FB failures (12/12
  failures have a term > 0, and 0 of 33 stages with term ≤ +100 fail).
- **7g's correction is negative in the box reading on all 8 client-seeds**, at −13 to
  −388 ps. It does not flip rule J on these pad-driven routes, whose guarded margin stays
  ≥ +209 ps.

**Effort to finish: about 0.5 day.** This makes it a gate (rule J' and an H_SEL_ORDER
check):
- read pins from the routed JSON (`X_ORIG_PORT`) or from FASM, as done here;
- add the site-pin table to arb_fork.py and skew.py;
- run it over the shipped designs' 4-seed rebuilds.

**What it buys:** the evidence that the per-pin site delays matter (pin 1 is used for
feedback in a third of instances, and those are exactly the instances that fail RT_FB),
plus the inputs that such a rule needs.

## Fidelity per primitive

- **LUT**: the binary `o6B`/`o5B` from Prelim, on the physical INIT and pins (C's
  `PLut.fn`), compared with the real cell INIT. Values only, no timing in Lean.
- **Site pin**: prjxray's four-corner delay per pin, an input buffer before the mux tree.
  It is used only in the arithmetic in the notes.
- **Routes**: C's source walk over active pips. Pass-transistor and buffered flags and
  intervals are prjxray's intrinsic values plus Elmore; these are candidates and have not
  been checked against silicon.
- **Ties**: GND/VCC as wired in the bits.
