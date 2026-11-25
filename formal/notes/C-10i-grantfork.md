# C-10i: is the arbiter grant-fork race live on shipped routes? (H_GRANT_FORK)

> **Corner check (2026-10-29, probe C-12d; `C-12d-corner.md`).** This probe did NOT use the
> "rise 56 / fall 124" corner mix: `extract.py` prices every element as one per-pin delay
> per prjxray column (no rise/fall split), and the verdicts are per consistent corner
> (FMIN, FMAX, SMIN, SMAX points; `fast`/`slow` = every element inside ONE corner's band).
> `GrantFork.lean` / `GrantForkInst.lean` need no restating. Two things are corrected or added:
> - The comparison with C-12c's "wq_g < 56 ps" (inertial) used a corner-mixed number. At one
>   corner the inertial bound on the shared-copy cell is wq_g < min{lo(O5) if hi(O5) > lo(O6);
>   lo(O6) if hi(O6) > lo(O5)}: 42 ps at FAST, 100 at SLOW, 56 at FAST_MAX points, 150 at
>   SLOW_MAX (C-12d, TChecker, fitted to every row). The structural point of the comparison
>   (on real routes the inertial window is about the transport window) is unchanged.
> - **Corner model (A's shared corner c + scatter kappa), from the committed data**
>   (`formal/tools/grantfork/kappa.py`, exact rationals, arithmetic not Lean): transport
>   H_GRANT_FORK passes on 23 / 7 / 4 of 80 instance-clients at kappa = 0 / 1/11 / 0.1988 in
>   the `lit` reading (F = FMIN, S = SMAX), and 7 / 4 / 1 in the `cons` reading. The race is
>   open on at least 57 of 80 at kappa = 0, so the verdict "live on shipped routes" stands and
>   gets stronger with scatter. Per-instance kappa* are in C-12d-corner.md.
> - The ackcheck "mixed" row below (SMAX arbiter legs vs 0.772 x SDF server, -198 ps) was
>   already flagged here as a corner-mix artefact; the consistent pricing (+342 ps minimum) is
>   the one to use.

Shard C, probe 10i, 2026-10-27. Files (mine): `formal/tools/grantfork/{extract,ackcheck,summarize}.py`,
`check.sh` (outputs in `formal/tools/grantfork/build/`), `formal/lean/Formal/Timing/GrantFork.lean`
(theory and checkers), `formal/lean/Formal/Timing/GrantForkInst.lean` (generated: 560 boxes,
1680 kernel `decide`s). `Wip/C10i/` is empty because nothing is unfinished.

## Verdict

**Works.** The race is live on the shipped routes: the timing condition fails on most
instances. Its consequences in `bd_arbiter` look benign, but that is evidence, not proof.
- **Condition.** H_GRANT_FORK fails for at least one client at a consistent prjxray corner on
  **32 of the 40** routed `bd_arbiter` instances: 36 in the 4 gcd_hw routes, plus link_arb s1..s4.
  - At SLOW_MAX, 23 of 80 arbiter-clients pass (transport reading) and 24 pass (inertial).
  - 26 instances fail for both clients.
  - Only 8 instances pass for both clients at all four consistent corners. They are
    the ones whose q and r forks happen to be near-isochronic.
- **Size.** The runt on the grant is up to ~1.2 ns at SLOW_MAX, and up to ~600 ps at FAST_MIN.
- **Cause.** The window is mostly a **pin-assignment effect**, which nextpnr's SDF cannot see.
  - The site-pin part of W (SP[ugrant q] − SP[ustate q] − SP[ugrant r] + SP[ustate r]) correlates
    0.85 with W at SLOW_MAX over the 72 non-fallback rows.
  - All 37 rows where that site-pin term is positive fail.
  - SDF alone passes 30 of 80 rows; prjxray SMAX passes 23.
- **Consequence (evidence only).** For `bd_arbiter` the runt does not reach an acknowledge.
  - A0 is low throughout the window. With prjxray pricing, the runt on g_k ends at ua_k at
    least 342 ps before A0 can rise there (ackcheck).
  - Its other reader, the bdc_amerge data-mux select (`won = g2 | in_ack`), is bundled from
    the same q edge.
  - So what breaks is the header's claim that **the grant wires are exclusive**, not the
    handshake. This claim is NOT proved: H_RUNT_ACK and the rule-A coverage are unproved.
- **The bd_arbcell 8 % overlap.** This race does not explain it on its own. Details are in (3).

## What checks (exact command)

    formal/tools/grantfork/check.sh      # ~40 s: extract 8 routes (one process each), drift check,
                                         # summary, ackcheck, Lean (GrantFork + 1680 decides), scan.py,
                                         # negative control (one flipped verdict is refused by the kernel)

Last run: `C-10i check PASS`. Both files compile with core Lean only (imports
`Formal.Cells.ArbBinary`, read-only). `#print axioms`:
- the theory theorems use only propext, Classical.choice and Quot.sound;
- the decided verdicts use no axioms;
- `scan.py` is clean.

## The race (gate fidelity, real INITs)

The scenario is client 2's. Client 1 is the mirror: q falls, r1 rises, and the runt
`g1 = r1·q` appears on O5.
1. The server is idle, so A0 is low.
2. r1 asks alone, and q rises at T.
3. r2 rises after q's feedback copy has reached ustate's own q pin. So q does not reverse:
   there is no q runt, and tier 3 is excluded.
4. r2 rises before q's other copy reaches ugrant's q pin. So ugrant reads `r2 ∧ ¬q(old)`,
   and g2 runs high until the new q arrives.

The model uses per-pin pure delays, as in B's `ArbOverlapRace.Dl`. Each delay is
route + site pin + LUT arc of that pin:
- `ustate`: `stA` (INIT FFF0_FFB2_ACAC_ACAC);
- `ugrant`: `gr1`/`gr2` (0C0C_0C0C_A0A0_A0A0).

### Theorems (namespace `Formal.Timing.GrantFork`)

- `consistent2_iff` / `consistent1_iff`: the step waveform of q solves the ustate relation
  iff `T + L ≤ t2 + s2`, i.e. r_k reaches ustate after q's own feedback.
- `runt2_iff` / `runt1_iff`: g_k is ever high iff `t_k + a_k < T + b`.
- `runt2_width`: every high instant lies in `[t2 + a2, T + b6)`, and the runt is at most W wide.
- **`fork_runt2_iff` / `fork_runt1_iff`**: a consistent scenario with a grant runt exists
  iff `W > 0`. W is defined as follows:
  - `W2 = (b6 − L) − (a2 − s2)`;
  - `W1 = (b5 − L) − (a1 − s1)`.
- `lumped_W` (H_SHARED_PREFIX):
  - Write each lumped delay as prefix + suffix + arc, with ONE prefix per net.
  - Then `W = (dqg + agq) − (dqs + asq) − ((drg + agr) − (drs + asr))`. The prefixes cancel.
  - The extractor computes the suffixes exactly from the RC tree (`tcheck/extract.Prjx.split`,
    the same machinery as rule J').
- `okT` (transport checker):
  - `okT_iff`: exact on non-empty boxes.
  - `transport_sound1/2`: a passing box has no runt at any delays in it, for any prefixes,
    and for any L ≥ 1.
  - `transport_exact1/2`: a failing box has delays in it and a concrete runt scenario.
- `okI` (inertial reading, C-12c):
  - The model is a Boolean core per LUT followed by an inertial output delay.
  - **H_INERTIAL_COMMIT** (`Adm`): r_k reaches ustate's core no earlier than T, and ustate's
    reversal excitation is shorter than ustate's inertial delay `dst = max asq asr`.
  - The grant core's stale-q excitation is then at most
    `maxW = dqg − (drg − drs) − max 0 (dqs − dst + 1)` (`inWidth_le`, `inWidth_attained`).
  - The runt is swallowed iff `maxW < min agq agr` (H_INERTIAL_ARC).
  - `okI_iff`: exact on non-empty boxes.
  - With C-12c's rows (zero r-fork skew, wq_s < 56) this reduces to its `wq_g < 56`.
  - A first version dropped the `max 0 (dqs − dst + 1)` term. That counted tier-3 q
    reversals as grant-fork runts: 3 of 80 passed, against 24 now. It was corrected before
    any verdict was reported.
- `GrantForkInst.<design>_<inst>_c<k>_<variant>_{wf,T,I}`: 560 boxes, decided by the kernel.
  - The variants are `fast` and `slow` (independent box per element, as tcheck), the
    consistent corners `FMIN FMAX SMIN SMAX` (point values), and `sdf`.
  - The verdicts carry meaning only through the theorems above. The numbers are evidence.

## Per-instance verdicts

W is in ps; > 0 means the race is open. "T ok at" lists the variants where transport
H_GRANT_FORK holds (kernel-decided). The inertial verdicts are in `build/summary.md`; they
differ from the transport ones on 15 of 560 boxes, all with |W| ≤ 46 ps.
- "r fb" marks link_arb: r comes from a pad, so prjxray cannot split it. It uses the SDF
  guard band on the whole net, which is pessimistic.
- The full per-variant table, with pins and inertial widths, is `build/summary.md`.
- The raw intervals are in `build/grantfork.json`.

| design | instance | client 1: pins ug/st q | W FMIN / SMAX / sdf | T ok at | client 2: pins | W FMIN / SMAX / sdf | T ok at |
|---|---|---|---|---|---|---|---|
| gcd_hw_2 | merge10.uarb1 | A1/A5 | 134 / 475 / 277 | none | A1/A5 | 296 / 900 / 295 | none |
| gcd_hw_2 | merge11.uarb1 | A5/A3 | 589 / 1026 / 876 | none | A5/A3 | 348 / 530 / 1000 | none |
| gcd_hw_2 | merge12.uarb1 | A5/A1 | -149 / -506 / 107 | FMIN,FMAX,SMIN,SMAX | A5/A1 | -144 / -400 / -6 | all |
| gcd_hw_2 | merge12.uarb2 | A1/A5 | 274 / 830 / 36 | none | A1/A5 | 79 / 261 / -1 | sdf |
| gcd_hw_2 | merge2.uarb1 | A5/A5 | -23 / -74 / 179 | FMIN,FMAX,SMIN,SMAX | A5/A5 | 108 / 281 / 279 | none |
| gcd_hw_2 | merge3.uarb1 | A5/A1 | -56 / -261 / -98 | all | A5/A1 | -285 / -848 / -64 | all |
| gcd_hw_2 | merge4.uarb1 | A2/A5 | 246 / 723 / 108 | none | A2/A5 | 263 / 721 / 149 | none |
| gcd_hw_2 | merge6.uarb1 | A2/A5 | 246 / 691 / 147 | none | A2/A5 | 123 / 352 / 140 | none |
| gcd_hw_2 | merge9.uarb1 | A4/A3 | -81 / -256 / -215 | all | A4/A3 | -83 / -252 / -213 | all |
| gcd_hw_3 | merge10.uarb1 | A1/A5 | 277 / 786 / 281 | none | A1/A5 | 80 / 266 / -145 | sdf |
| gcd_hw_3 | merge11.uarb1 | A5/A5 | 6 / -28 / -34 | SMIN,SMAX,sdf | A5/A5 | 0 / -4 / 0 | all |
| gcd_hw_3 | merge12.uarb1 | A5/A1 | -67 / -274 / -32 | all | A5/A1 | -223 / -624 / 14 | FMIN,FMAX,SMIN,SMAX |
| gcd_hw_3 | merge12.uarb2 | A5/A5 | 184 / 399 / 236 | none | A5/A5 | 1 / 1 / 0 | sdf |
| gcd_hw_3 | merge2.uarb1 | A4/A4 | 2 / 5 / 0 | sdf | A4/A4 | 12 / 17 / 0 | sdf |
| gcd_hw_3 | merge3.uarb1 | A5/A5 | 41 / 84 / 106 | none | A5/A5 | 111 / 303 / 140 | none |
| gcd_hw_3 | merge4.uarb1 | A2/A5 | 287 / 912 / 127 | none | A2/A5 | 152 / 465 / 149 | none |
| gcd_hw_3 | merge6.uarb1 | A2/A2 | -2 / 25 / 17 | FMIN,FMAX | A2/A2 | 68 / 175 / 0 | sdf |
| gcd_hw_3 | merge9.uarb1 | A3/A3 | -114 / -328 / -353 | all | A3/A3 | -192 / -586 / -213 | all |
| gcd_hw_4 | merge10.uarb1 | A1/A5 | 247 / 674 / 267 | none | A1/A5 | 307 / 762 / 140 | none |
| gcd_hw_4 | merge11.uarb1 | A4/A4 | -2 / -10 / 0 | all | A4/A4 | 1 / 1 / 0 | SMIN,sdf |
| gcd_hw_4 | merge12.uarb1 | A2/A1 | -95 / -300 / -75 | all | A2/A1 | -51 / -164 / -136 | all |
| gcd_hw_4 | merge12.uarb2 | A4/A1 | 46 / 177 / 119 | none | A4/A1 | -102 / -286 / 95 | FMIN,FMAX,SMIN,SMAX |
| gcd_hw_4 | merge2.uarb1 | A4/A5 | 381 / 823 / 330 | none | A4/A5 | 43 / 170 / 0 | sdf |
| gcd_hw_4 | merge3.uarb1 | A2/A5 | 113 / 348 / 113 | none | A2/A5 | 528 / 1211 / 406 | none |
| gcd_hw_4 | merge4.uarb1 | A4/A5 | 100 / 334 / 202 | none | A4/A5 | 92 / 327 / 426 | none |
| gcd_hw_4 | merge6.uarb1 | A3/A3 | 109 / 244 / 217 | none | A3/A3 | -8 / -38 / -65 | all |
| gcd_hw_4 | merge9.uarb1 | A3/A5 | 18 / 131 / -75 | sdf | A3/A5 | 17 / 124 / -73 | sdf |
| gcd_hw_d | merge10.uarb1 | A1/A5 | 262 / 824 / 213 | none | A1/A5 | 195 / 639 / -1 | sdf |
| gcd_hw_d | merge11.uarb1 | A2/A5 | 147 / 399 / 24 | none | A2/A5 | 258 / 688 / 302 | none |
| gcd_hw_d | merge12.uarb1 | A1/A5 | 196 / 559 / 142 | none | A1/A5 | 108 / 326 / 140 | none |
| gcd_hw_d | merge12.uarb2 | A5/A5 | 242 / 515 / 382 | none | A5/A5 | 87 / 168 / 198 | none |
| gcd_hw_d | merge2.uarb1 | A4/A4 | -2 / -10 / 0 | all | A4/A4 | -1 / -5 / 0 | all |
| gcd_hw_d | merge3.uarb1 | A2/A5 | 123 / 384 / 31 | none | A2/A5 | 264 / 751 / 213 | none |
| gcd_hw_d | merge4.uarb1 | A1/A4 | 94 / 262 / 213 | none | A1/A4 | 101 / 405 / 74 | none |
| gcd_hw_d | merge6.uarb1 | A1/A4 | 229 / 640 / 215 | none | A1/A4 | 280 / 810 / 213 | none |
| gcd_hw_d | merge9.uarb1 | A5/A3 | -143 / -511 / -32 | all | A5/A3 | -72 / -245 / 0 | all |
| link_arb_s1 | arb | A5/A5 (r fb) | 444 / 489 / 100 | none | A5/A5 (r fb) | 595 / 681 / 282 | none |
| link_arb_s2 | arb | A3/A5 (r fb) | 487 / 739 / 108 | none | A3/A5 (r fb) | 651 / 905 / 203 | none |
| link_arb_s3 | arb | A5/A1 (r fb) | 500 / 260 / 252 | none | A5/A1 (r fb) | 134 / -67 / -26 | SMIN,SMAX,sdf |
| link_arb_s4 | arb | A5/A5 (r fb) | 855 / 984 / 608 | none | A5/A5 (r fb) | 535 / 703 / 319 | none |

The worst rows are listed below. Their SDF windows are smaller, because the SDF has no site pins.

| design | instance | client | W at SMAX | why |
|---|---|---|---|---|
| gcd_hw_4 | merge3.uarb1 | 2 | 1211 ps | q on A2 at ugrant, A5 at ustate |
| gcd_hw_2 | merge11.uarb1 | 1 | 1026 ps | r1 reaches ugrant 680 ps before ustate (SDF 635 vs 1315) |

## Does shard B already have this condition?

**No, not as a condition.** Its consequence is bounded, and the two results agree.

- **ArbBinary (7a).** `exclusion_transport` with H_REQ_SEP / H_GRANT_SKEW assumes this race
  away. The model says so: "the grant LUT reads the same q value the state LUT reads; routing
  skew between those two branches is NOT modelled". In our terms that model has
  `b6 = L + d6` and `a2 = s2 + d6`, so W = 0 identically. H_REQ_SEP (request edges more than
  one loop apart) is satisfied by the race scenario, so it does not exclude the race.
- **ArbHandover (7e).** The skew theorems (σ = request-fork skew) treat the handover
  direction (a request FALLS). The grant-fork race is a request RISING after a lone-request
  commit, so it is not covered.
- **ArbOverlapRace (Bov).** Its per-pin `Dec` model contains this race.
  - Its `grant_cap` bounds every g1∧g2 run by `|b5 − b6|`, for any request waveforms and fork
    skew, which includes our runts. That is ≤ 33 ps at a consistent corner and ≤ 112 ps in
    the box.
  - So the two results agree. B bounds the overlap the race causes. This probe states when
    the race exists (`fork_runt_iff`) and how long the runt on the grant wire itself is (≤ W).
- **B-obligations.** H_GRANT_FORK belongs in §5/§6 as a new row: "A8 grant fork".
  - Inequality: `W ≤ 0` (transport) or `maxW < min arc` (inertial).
  - Status: E (exact both ways).
  - Rule: none yet. Margins: this note.

## (3) Does this race explain the bd_arbcell 8 % overlap?

**No, not by itself.** `bd_arbcell` has the same race, since its q also forks to ustate and
ugrant. But the overlap it produces is capped by the same q edge:
1. The runt on g2 ends when the new q reaches ugrant. That same edge raises g1.
2. So g1∧g2 lasts at most `|b5 − b6|`, the O5-vs-O6 arc difference of q's pin. This is B's
   `grant_cap`: ≤ 33 ps at a consistent corner, ≤ 112 ps in the box.
3. At the detector the run is at most `min(−(s + b), W2)` (mirror: `min(s + b, W1)`), with
   B's detector skew `s`.
   - The runt starts no earlier than `T + L − s2 + a2`, which gives the W bound.
   - B's `raw_cap |s + b|` gives the other bound.
4. So a filtered (≥ 203 ps) event through this channel needs BOTH of these:
   - B's detector skew `|s + b| ≥ 203`;
   - `W ≥ 203` on the same side.

What it adds:
- It is a third trigger for B's detector-skew mechanism, next to the two handovers. B's
  pre-registered per-copy predicate should become
  `max(s + min(κ1, b), −s + min(κ2, −b), min(−(s+b), W2), min(s+b, W1)) > Dw`.
- A possible handle on the A5 lead, at one LUT only:
  - q on A5 at **ugrant** cuts `dqg`, by up to ~400 ps at the slow corner (site pin 112 vs
    516). That shrinks W and so removes copies from this channel, which is the lead's
    direction.
  - q on A5 at **ustate** cuts `dqs` and so GROWS W, which is the opposite direction.
  - The lead pools both, so as with B, the signs are mixed.
- It cannot be decided here: the routed arb_mtbf artefacts are not on disk, and a rebuild
  re-draws the pins (43 of 50 bad copies turned clean on rebuild).

## (4) What GLS or board experiment would show it

### GLS (cells/gls)

GLS reads nextpnr's SDF, which has no site pins, so it can only exercise the `sdf` rows.
Choose rows with a large SDF window:
- gcd_hw_2 merge11.uarb1: c2 W_sdf = 1000 ps, c1 876 ps;
- gcd_hw_4 merge3.uarb1 c2: 406 ps.

Negative control: gcd_hw_2 merge3.uarb1, W_sdf = −98 / −64. Its r forks are isochronic in
the SDF (2419/2419 and 1604/1604).

Procedure:
1. Build tree_2's gcd_hw GLS with `-DGLS_TRANSPORT_IC`. Wires are then transport; LUT
   specify paths stay inertial, which is the mixed reading.
2. In a small tb, `force` the instance's z_ack (A0) low.
3. Force the DRIVER nets of r1 (`ucond_br35`) and r2 (`ucond_br39`), not the ICBUF outputs,
   so that each fork keeps its routed skew.
4. Raise r1 at t1 and r2 at t1 + Δ. Sweep Δ in 10 ps steps over [0, 2.5 ns].
5. Record:
   - every 1 on ugrant's O6 net (g2);
   - q's waveform (no reversal expected);
   - ua2's output (must stay 0, since A0 is forced low).

Pre-registered prediction, from the SDF numbers for merge11.uarb1 c2 (qg 946, qs 718,
rg 428, rs 1200, arcs 124; r1→ustate 1315 + 124, so T = t1 + 1439):
- transport LUTs: a g2 pulse iff Δ ∈ [957, 1957) ps;
- iverilog-inertial LUTs: a g2 pulse iff Δ ∈ (833, 1833] ps;
- the negative control: no g2 pulse for any Δ;
- no ua2 edge in either case.

A second run that lets A0 follow R0 through a short forced delay `d` measures H_RUNT_ACK
directly: ua2 fires iff `d` is below the ackcheck margin.

### Board

Pin choice is the lever.
1. Build `bd_arbiter` copies whose q lands on A1 at ugrant and A5 at ustate (large W), and
   copies with A5/A5 (W ≈ 0). This uses the same pin-forcing route as ARBITER.md's untried
   "q on A5" build.
2. Drive each copy as in arb_mtbf, but with a fast server: A0 = R0 through a short
   `bd_delay`, so that smin falls below the runt length.
3. Count client completions against server transactions (the tb_arb counter).

Predictions:
- large-W copies over-acknowledge;
- W ≈ 0 copies never do;
- with the shipped server latency, neither does.

This tests H_GRANT_FORK and H_RUNT_ACK together without a g1&g2 detector, which carries its
own site-pin skew (B's lesson).

## Consequence evidence (not proved): H_RUNT_ACK and the data mux

`ackcheck.py` compares two times, both measured from q's output edge T:
- **runt end** at ua_k's g pin: `q → ugrant → g_k → ua_k`, prjxray at a corner;
- **earliest A0 rise** at ua_k's A0 pin: `q → ustate O5 (R0)`, then the SDF-shortest server
  path R0 → … → A0, crossing every node as a pass-through, which is a lower bound.

The server path was evaluated two ways:
- **Priced arc by arc with prjxray at the same column:** min margin **+342 ps** (gcd_hw_4
  merge12.uarb1 c2, FMIN). Every row is positive.
- **Mixed:** SMAX arbiter legs against `0.772 ×` SDF for the server. Worst row −198 ps
  (gcd_hw_d merge12.uarb1 c1). This is a corner-mix artefact; the same row priced
  consistently gives +1355.

Caveats:
- The path is SDF-shortest, not prjxray-shortest.
- link_arb is not resolved: r and A0 come from pads.

Data side: the runt's falling edge is q's arrival at ugrant, so the select settles on the
q-launched path, the same path rule A must already cover for a legitimate handover. This was
argued, not checked against tighten.py's rule A walk.

## Fidelity of every primitive

- **LUTs.** Real INITs through B's `stA`, `gr1` and `gr2` (lutB/o6B/o5B). Pin identity comes
  from nextpnr's `X_ORIG_PORT_A*`: connections are physical, INIT is logical. The extractor
  asserts the logical INIT is r1·q / r2·¬q and that q / r_k nets sit on the identified pins.
- **Transport reading.** One pure delay per (pin, output), no rise/fall split; prjxray has
  none. This is pessimistic for narrow pulses: it passes every runt.
- **Inertial reading.** A Boolean core plus an inertial output delay. Per-pin arc
  differences are neglected (H_INERTIAL_ARC). This matters for O5, whose arcs differ per pin
  by up to ~40 ps; O6 is flat. It is optimistic for runts just under the arc.
- **The real LUT** lies between the two readings. They disagree on only 15 of 560 boxes, all
  with |W| ≤ 46 ps, so the verdicts barely depend on the choice.
- **Wires.** prjxray RC trees from the FASM's ON pips, with site pins, site hops and Elmore
  terms (tcheck's Prjx). The shared prefix is exact by element identity.
  - Fallback (link_arb r nets from pads): SDF × [0.772, 1.155] on the whole net, with no
    prefix cancellation (H_FALLBACK_BAND). These rows are flagged.
  - No other fallback occurred.
- **Corners.** The independent box (`fast`, `slow`) is very pessimistic: 7 of 80 pass. Read
  the consistent-corner rows.
- **Environment.**
  - Free clients: H_A0_LOW, plus a request rising in the window.
  - Whether gcd_hw's merges can ever see a second request within ~1 ns of a lone-request
    commit is a protocol question this probe does not answer. A single-token loop never
    contends; pipelined merges can.
  - The cell's contract is free clients: "possibly-coincident requests".

## What did not work / surprises

- **Prjx is not reusable across designs in one process.** The first all-designs run printed
  "floating LV node" for gcd_hw_3 nets that extract cleanly when that design runs alone, so
  module-level caches in fasm2lean/ringdelay leak between designs. The extractor now runs one
  design per process, and every gcd row has no fallback. Anyone looping Prjx over several
  routes in one process should do the same. tcheck itself runs one route per process.
- 12c's sign is confirmed and refined. Transport needs `wq_g − wq_s` minus the r-fork skew
  `≤ 0`, plus arc terms. The r-fork skew can be large: in gcd_hw_2 merge11.uarb1, r2 reaches
  ugrant 772 ps before it reaches ustate in the SDF. It appears in both readings.
- C-12c's inertial "wq_g < 56 ps, independent of wq_s" holds only while the q feedback is
  shorter than ustate's arc. On real routes (dqs 76-500 ps) the inertial window is about the
  transport window.

## Effort to finish / what it buys

- **Buys:**
  - a new, exact, per-instance obligation (H_GRANT_FORK);
  - its routed status: open on 32 of 40 instances;
  - the finding that it is a site-pin effect invisible to every SDF-based rule;
  - a decomposition showing what it actually threatens (grant-wire exclusivity) and what it
    does not (acks and data, subject to H_RUNT_ACK and rule A).
- **To finish (~1 day):**
  1. Prove H_RUNT_ACK in Lean. Add a C-element with A0 low, extending B's `A2_low_before`
     with this runt. Decide it on the routed numbers, with the server path priced by a
     proved min-path (tcheck's checker).
  2. Check that rule A's walk starts at q for bdc_amerge's select.
  3. Run the GLS sweep above.
  4. If the cell's exclusivity claim is to stand as written, add a pin constraint that puts
     q on the same or a faster pin at ugrant than at ustate. That costs no LUTs. As a rule,
     it would be the `okT` check on prjxray numbers, as rule J' is for the A0 fork.
