# B probe Br: the top unchecked cell obligations on four real gcd_hw routes

Shard B, 2026-10-27. This probe evaluates B-obligations' ranked items 1, 2 and 4 on
fresh routes of the shipped kernel's board rig (`cells/hw/gcd_hw.v`):
- item 1: C3 `H_SELORD`, the per-pin C-element feedback order;
- item 2: L1, latch setup (rule I) with the feedback-pin arc and site pins;
- item 4: L3, rule H with the enable/data site-pin difference.

There is no Lean in this probe. No committed file was edited, and no git command that
changes anything was run. Builds, scripts and outputs are in
`/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/gcdr/`.

## Answer in one paragraph

On 4 placer seeds, no obligation has a negative margin at a consistent corner. That holds
with the guardband, and it covers every C-element and every latch bit.

- **H_SELORD** (363 C-elements per route):
  - Box reading (H_INDEP: feedback at SLOW_MAX, response at FAST_MIN, element by element):
    **7.8 [5, 10]** instances negative per seed; worst **-386 [-585, -282] ps**.
  - One-corner readings: **0** negative at SLOW_MAX and at FAST_MIN.
  - Guarded one-corner margin (0.772·E − 1.155·F): worst **+24 ps (FAST_MIN)** and
    **+58 ps (SLOW_MAX)**, both on seed 4. Both are on the **rig's** bare 2-cell Muller ring
    `urig.uenv1` (bd_c2n_set, feedback on pin 1). The kernel's own worst guarded margin is
    +193 (FAST_MIN) and +668 (SLOW_MAX).
- **Rule I, corrected** (1688 bits per route): the corrected per-bit margin stays ≥ +1288 ps
  guarded in the box. The added terms are 0.68 ns median and up to 1.13 ns. They are covered
  because rule I's close path holds a whole handshake round trip (5.5-5.8 ns).
- **Rule H, corrected** (3508 bits): the site-pin term is up to +509 ps in the box. It
  exceeds the 200 ps guard floor on **~60% of bits**. The worst corrected margin is
  **+40 ps guarded / +240 raw (seed 3)**, against +514 coded.
- **Shipped gates on the same routes:**
  - rules A/H/I/F/B/C, E (0/118) and J (18/18 clients) pass on all 4 seeds;
  - rule D reports its documented 38 screen hits.

The thinnest numbers are the rig's `uenv1` loop and rule H once site pins are added. Neither
is negative.

## Toolchain and build (CLAUDE.md)

- **Toolchain check.** `cells/verify/toolchain.sh` passed before each build:
  - all 9 patch fingerprints "ok";
  - **nextpnr sha256 `9c732bc6303458df`** (`openXC7 0.9.2-100-gbfdeaf7c` + the repo's
    patches);
  - yosys 0.62 (`7326bb7d6`).

  The binary is the one restored at `$TC = ~/dev2/lib/fpgatoolchain` by the earlier probe.
  `toolchain.txt` beside each SDF and tighten.py's banner both name `9c732bc6303458df`.
- **Command** (`scratch build.sh SEED`). It is BOARD-QUEUE #1's command, run in a private
  copy of `cells/` and `bdc/` (C-10e's `route.sh` recipe), plus `--freq`:

      NEXTPNR_SEED=$S NEXTPNR_FREQ=100 BDC_SELECT_PADS=$T/cells/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw

  The frontend comes from `cloud/fixtures/frontend/gcd`.
- **`--freq` was passed.** There is no documented frequency for gcd_hw. BOARD-QUEUE's
  commands set no `NEXTPNR_FREQ`, so nextpnr's 12 MHz default applies. I passed 100 MHz, as
  C-11b did. All 8 clock checks per seed PASS at 100 MHz:
  - BSCAN `tck`, ring-clocked `hk_ck`, `lap_ck`, `cmp_ck`;
  - lowest Fmax 165 MHz.

  As a consequence, these routes are **not** the BOARD-QUEUE bitstreams. None of the
  quantities analysed here is a clock path.
- **Seeds 1, 2, 3, 4, pinned.** The four routes really differ: FASM, routed JSON and SDF
  md5 all differ (`md5_<s>.txt`). For example, the SDFs start `49161b6c`, `d8aeae28`,
  `e1c2eb3b`, `21b4368b`.
- **Each seed:** 0 RLOC groups dropped, `fasm_audit PASS`, `build_hw.sh PASS` (bitstream
  written).

### The shipped audit gates on these routes

The gates were run as `tighten_loop.sh` / `converge.sh` / C-10e run them:
- `skew.py`;
- `tighten.py --osc dhk --osc invhk`;
- `arb_fork.py`.

| seed | A min | H min | I min | F min | D (screen) | E | J (18 clients) guarded min |
|---|---|---|---|---|---|---|---|
| 1 | +4538 | +373 | +2829 | +731 | 38 hits | 0/118 | +381 |
| 2 | +4520 | +514 | +2472 | +1333 | 38 hits | 0/118 | +445 |
| 3 | +4892 | +514 | +2663 | +673 | 38 hits | 0/118 | +437 |
| 4 | +4622 | +514 | +2068 | +463 | 38 hits | 0/118 | +500 |

- **Pass/fail.** Every rule passes except D. D's 38 hits are the documented one-sided screen
  ("rule D 38 = the documented screen", BOARD-QUEUE #1), and tighten.py exits 1 on them, as
  in every earlier gcd_hw audit.
- **Rule H on seeds 2-4.** The worst margin is the identical +514 on all three: the same
  link-latch geometry recurs. RLOC v4 places each bd_link C node next to its latch bank, so
  these intra-group routes repeat across seeds. **The seed scatter on rule H is therefore
  smaller than the 150-200 ps tighten.py's header quotes for un-RLOC'd routes.**

## Step 2: H_SELORD per C-element (B-pipe-per-pin, B-fifo-fidelity C3)

### Tool

C-10f's `formal/tools/rtfb/rtfb_design.py`, imported unchanged through a scratch wrapper
`tools/rtfb_bidi.py`. For each `bd_c2`/`bd_c2n`/`bd_c2n_set`/`bd_c3`/`bd_c4` LUT it
computes, over the FASM's active pips and prjxray-db:

- **slack = E − F**, where:
  - E is the earliest arrival, at the select of any non-feedback pin, of any simple LUT path
    that starts from the C-element's own O6 edge;
  - F is the latest arrival of the feedback at its select.

Each route element is a pip, Elmore RC, the **site pin** or a LUT arc (O6 or O5, per pin).
Including the site pin at both ends makes this exactly `wh + pq.hi ≤ E_τ + p_dep.lo`, taken
over every departure. E is "the shortest round trip through the neighbouring cells", over
the whole design.

**Physical feedback pin.** It comes from the bits (own-output walk), cross-checked against
`X_ORIG_PORT`; the tool aborts on a mismatch. My summary also checks it against the SDF's
O6→own-pin INTERCONNECT: **363/363 agree on every seed**.

**Wrapper changes:**
- Walker fix: register the reverse orientation of bidirectional long-line pips. This is
  probe Bmt's `percopy.py` fix.
- It is run on nextpnr's own FASM, whose pip orientation is the routed direction. The
  read-back FASM's orientation is fixed by the segbits.
- `--capture`: E and F per variant, read off `main()`'s locals with `sys.setprofile`.

With the fix there are **0 walk errors**, against 132-374 per seed with the unchanged tool
on the read-back FASM. **C's unchanged tool on the read-back FASM gives identical counts and
worst slacks on all 4 seeds** (`rt/s*/rtd.out`), so the walk errors (rig vector-ROM nets
and a few C-node fanouts) never decided a C-element.

### Readings

| reading | meaning |
|---|---|
| indep | box: every element of F at slow_max, every element of E at fast_min |
| slow / fast | one prjxray column: F at its max, E at its min |
| pSmax / pFmin | one point corner: every element at SLOW_MAX / FAST_MIN |
| guarded | skew.py's GUARD_LO/HI on a point corner: `0.772·E − 1.155·F` |

### Counts (363 C-elements per route: 185 bd_c2n, 153 bd_c2, 14 bd_c4, 10 bd_c3, 1 bd_c2n_set)

| seed | negative: indep | slow | fast | pSmax | pFmin | guarded pSmax | guarded pFmin | worst indep | worst fast | worst guarded pFmin | worst guarded pSmax |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | -585 | +187 | +193 | +531 |
| 2 | 8 | 0 | 0 | 0 | 0 | 0 | 0 | -290 | +109 | +55 | +213 |
| 3 | 5 | 0 | 0 | 0 | 0 | 0 | 0 | -282 | +248 | +298 | +621 |
| 4 | 8 | 0 | 0 | 0 | 0 | 0 | 0 | -389 | **+4** | **+24** | **+58** |
| **mean [range]** | **7.8 [5, 10]** | 0 | 0 | 0 | 0 | 0 | 0 | **-386 [-585, -282]** | +137 [+4, +248] | +142 [+24, +298] | +356 [+58, +621] |

- **Point corners, unguarded.** Worst pSmax is +830 mean [+431, +1249]; worst pFmin is
  +318 [+167, +547].
- **Most C-elements are never close.** Per seed, 353/355/358/355 C-elements have **no**
  response path that can arrive before the feedback even in the box.
- **The negatives are all box-only.** Each has 1-2 LUT hops on the earliest response.

**Kernel versus rig.** The rig has three C-elements: `uenv0`, `uenv1` and the fork's `g3`.

| | kernel (360) | rig (3) |
|---|---|---|
| box negatives per seed | 9 / 7 / 4 / 7 | 1 per seed (`uenv1`) |
| worst guarded pFmin per seed | +193 / +259 / +344 / +334 | `uenv1`: +195 / +55 / +298 / **+24** |
| worst guarded pSmax per seed | +668 / +737 / +934 / +930 | `uenv1`: +531 / +213 / +621 / **+58** |

`uenv1` is the binding instance on every seed. It is gcd_rig.v's bare `bd_c2n_set` 2-cell
ring, the same one C-10f found worst on its own routes.
- Its feedback is on **pin 1** on every seed (C1 or B1, SP 173..521 ps), with an in-slice
  295 ps SDF wire.
- Its response comes back through `uenv0` in one hop.
- Seed 4, at FAST_MIN: E = 440, F = 273 ps.

**Feedback pins (physical, all 363).**

| seed | pin 1 | pin 2 | pin 3 | pin 4 | pin 5 |
|---|---|---|---|---|---|
| 1 | 49 | 19 | 18 | 55 | 222 |
| 2 | 57 | 9 | 9 | 60 | 228 |
| 3 | 47 | 13 | 14 | 68 | 221 |
| 4 | 57 | 24 | 7 | 44 | 231 |

- Pin 6 is never used.
- Pin 1 is used by 13-16%. Bp's muller64 had 24/64; RLOC v4 puts most link controllers'
  feedback on A5.
- The feedback site pin at SLOW_MAX: median 126 ps, max 540 ps.
- The SDF feedback wire: median 295 ps (in-slice), max 721-1203 ps.

### Worst box instance, element by element

Seed 1, `ulink_n_trueResult_14.many.stage[1].u.ctl` (bd_c2n, SLICE_X28Y67.A, `--dump`,
`dump/s1_X28Y67A_indep.txt`).

**Feedback, F = 1462 ps at slow_max.** The feedback is **not in-slice**. It leaves the tile
on NW6, returns via NE2, SE6 and WL1, and lands on **A1**:
- pips: 748 ps;
- RC: 183 ps;
- site pin A1: 531 ps.

**Earliest response, E = 877 ps at fast_min.** It goes through the mux's join and C-element
and returns to the ack pin A5:
- `umux1.uj0` (C3);
- `umux1.uxa` (D1);
- ack pin A5 (38 ps site pin).

**Box margin: -585 ps.** About 210 ps of it is the box's own artefact. The first two pips
(LOGIC_OUTS→NW6BEG0→NE2BEG0) are shared by both paths but enter F at max and E at min. The
tree shares only the launch.

**One-corner margins:** +187 at fast and +768 at slow.

### The `sdf` variant

rtfb's `sdf` variant reprices the same paths with nextpnr's own SDF, with no site pins. It
gives **-133 ps on seed 1** (`ucontrol_merge12.uarb2.ua1`). **This is a tool artefact.**
- `rtfb_design.py`'s `sdf_lut` returns None for O5 arcs, so they count 0.
- This path crosses two O5 arcs: `uarb1.ustate$LUT5` → `uarb2.ugrant$LUT5`.
- The SDF's own O5 IOPATHs are 150-152 ps each, which gives about +170.

The path is also only physically connected: rtfb does not check that the INIT is sensitive
to the pin. It is not evidence of a real violation. **0 on the other seeds.**

## Step 3: latch bits, rule I and rule H, as coded and corrected

### Tool

`tools/tighten_dump.py`, generated by `tools/mkdump.py`. It is a scratch copy of
`cells/verify/tighten.py` with **its rule code unchanged**, plus JSON dumps of rule H/I
internals:
- enable pins, arrivals and arcs;
- per-data-pin earliest disturbance, computed by `earliest_disturbance`'s walk recording
  every target;
- rule I's close and arrivals per upstream node.

Its report equals the shipped run's line for line. The one exception is rule A's printed
"latest peer"/common-source name on one mux, where set iteration order breaks a tie. All
margins are equal.

`tools/latchsp.py` then works per bit. A bit is one `$LUT5`/`$LUT6` half or an `odd` LUT.
- **Pins.** The bit's physical en, d and fb pins come from the SDF, checked against
  `X_ORIG_PORT` for the role (pair half O5: I0/I1/I2; O6: I3/I1/I4; odd: I0/I1/I2) and
  against the SDF's own O→own-pin loop. Any mismatch aborts; none occurred.
- **Site pins.** From the prjxray tile json of the cell's tile, at four corners. They
  replace the SDF's flat 25 ps.
- **Rule I, corrected:**
  - data side: `+ IOPATH(fb pin → O) + (SP_hi[d] − 25) + (SP_hi[fb] − 25)`;
  - close side: `+ (SP_lo[en] − 25)`;
  - guard `max(0.2·t_data, 200)` recomputed on the corrected data;
  - "raw" = no guard.
- **Rule H, corrected:** `− (SP_hi[en] − 25) + (SP_lo[d] − 25)`, with tighten's guard.
- **Corners for SP:**
  - slow = both at SLOW_MAX;
  - box = hi at SLOW_MAX, lo at FAST_MIN;
  - fast = both at FAST_MIN.

  The rest of each margin is nextpnr's single-valued SDF, as tighten.py reads it. This is
  B-obligations' "cheapest check", not a prjxray re-timing.

### Population per seed

- **3508 latch-bit halves.** All of them are in rule H. **1688** are in rule I (75
  controllers); the rest take their data from outside a link stage and are "not audited",
  as coded.
- **Physical pins (seed 1)**, bit-half counts:

  | pin | 1 | 2 | 3 | 4 | 5 |
  |---|---|---|---|---|---|
  | fb | 734 | 548 | 473 | 839 | 914 |
  | en | 793 | 731 | 1090 | 369 | 525 |

  Seeds 2-4 are within ±40.
- **Feedback** SP slow_max median 344 ps, max 540 ps. Loop wire (SDF) median 295 ps, max
  1.5-2.2 ns.

### Rule I (setup, data part, L1). Worst bit per seed; no negative bit or controller on any seed, in any reading

| reading | s1 | s2 | s3 | s4 | mean [range] |
|---|---|---|---|---|---|
| tighten.py per controller (as shipped) | +2829 | +2472 | +2663 | +2068 | +2508 [+2068, +2829] |
| tighten formula, per bit | +2829 | +2619 | +2663 | +2421 | +2633 [+2421, +2829] |
| + feedback-pin arc (rule I', B-rules-kl) | +2647 | +2470 | +2514 | +2241 | +2468 [+2241, +2647] |
| + arc + site pins, SLOW_MAX, guarded | +1770 | +1973 | +2105 | +1367 | +1804 [+1367, +2105] |
| + arc + site pins, **box, guarded** | +1675 | +1715 | +1846 | +1288 | **+1631 [+1288, +1846]** |
| + arc + site pins, box, raw | +2326 | +2373 | +2360 | +2037 | +2274 [+2037, +2373] |

- **Size of the correction.** Arc plus site pins, box: median 0.68 ns, max 1.13 ns per bit.
  It is larger than the 200 ps guard on **every** bit (1688/1688).
- **Why rule I still holds.** Rule I's close path on gcd is `t_rise + t_ack + t_fall` +
  enable, 5.5-5.8 ns, against data arrivals of 2.0-2.8 ns. The missing terms are real,
  but this design does not bind on them.
- **Worst bit (seed 4):** `ulink_n_falseResult_51.many.stage[1].lat.pair[8]$LUT5`, with en
  on A5, d on A2, fb on A3.

**Side finding (tighten.py rule I, a quirk, not unsound here).** A split LUT6_2's two halves
each list all five shared physical pins. `latch_data_pins` therefore returns the OTHER
half's data pin on each half; false-arc pruning leaves that copy with no arc. Rule I then
times it with arc 0 plus THIS half's `loop_wire`, a pairing no bit has.

On seeds 2 and 4 this pairing **is** the shipped per-controller worst: +2472 against +2619,
and +2068 against +2421 with own pins. It is pessimistic here. It is not the bit's real
requirement in either direction.

### Rule H (hold, L3). Worst bit per seed; no negative bit on any seed, in any reading

| reading | s1 | s2 | s3 | s4 | mean [range] |
|---|---|---|---|---|---|
| tighten.py (as shipped; = per bit) | +373 | +514 | +514 | +514 | +479 [+373, +514] |
| + SP[en] − SP[d], SLOW_MAX, guarded | +596 | +171 | +119 | +523 | +352 [+119, +596] |
| + SP[en] − SP[d], **box, guarded** | +259 | +90 | **+40** | +179 | **+142 [+40, +259]** |
| + SP[en] − SP[d], box, raw | +459 | +290 | +240 | +379 | +342 [+240, +459] |
| + SP[en] − SP[d], FAST_MIN, guarded | +457 | +426 | +377 | +516 | +444 [+377, +516] |

- **Size of the site-pin term, box:** median about 300 ps (281-315), max **509 ps**. It is
  **> 200 ps (the guard floor) on 2071-2103 of 3508 bits** per seed. At SLOW_MAX alone the
  median is about 13 ps, with a max of 409 ps.
- **Worst bit, box (seed 3):** `ulink_n_falseResult_55.many.stage[1].lat.odd` (rig-side
  loop link):
  - en on **A2**, d on **A5**, term 474 ps;
  - +514 coded becomes +40 guarded.
- On seed 2, the same shape on `ulink_n143.many.stage[1].lat.odd` gives +90.

## What this does not show

- **Not the board's bitstream.** `--freq 100` changes the route. These are 4 samples of
  the flow's route population, not the BOARD-QUEUE #1/#2 routes.
- **prjxray corners only.**
  - No within-die mismatch: the 8.5% ring scatter is not a guardband, and the GUARD_LO/HI
    reading is the project's convention, not a measured bound.
  - No rise/fall asymmetry (`H_RF_ASYM`).
  - No temperature or speed-grade statement.

  The box is sound but double-counts shared route prefixes; the point corners are
  H_ONE_CORNER.
- **Response paths are physical, not logical.** rtfb counts any physically connected
  pin→O arc, including pins the INIT ignores and O5 halves. So E can be earlier than any
  real response: conservative for H_SELORD. Paths through FFs, carry or IOBs are cut as
  opaque environment. On C-elements the only such pin is one on seed 3:
  `ulink_n82.stage[0].ctl` A6, on `$PACKER_GND_NET`, a routed constant.
- **Latch margins are a hybrid.** nextpnr's SDF for routes and arcs, with prjxray site pins
  at the stated corners in place of its flat 25 ps. They are not prjxray re-timed paths.
  - Rule I's other omissions are unchanged and not evaluated: the min-over-bits close,
    `H_PW`/L2, and data from outside.
  - Rule H's zero-time state-node firing is unchanged.
- **C-element obligations other than H_SELORD** are not evaluated here: C1 pulse width, C5
  reset, H_RST_SEL, H_ACK_FLUSH. Nor is the kernel's logical function for E. H_TREE_FIFO
  and H_PIN_FIFO remain assumptions.

## Files (scratchpad `.../scratchpad/gcdr/`)

- **Build:** `build.sh SEED`, giving `tree_<s>/` (private cells/bdc copies; outputs in
  `tree_<s>/cells/build/hw/gcd_hw/`). Logs: `build_<s>.log`, `toolchain_<s>.log`,
  `md5_<s>.txt`.
- **Shipped gates:** `skew_<s>.log`, `tighten_<s>.log`, `arbfork_<s>.log`.
- **H_SELORD:**
  - `rtb.sh SEED` + `tools/rtfb_bidi.py` (the result runs);
  - `rt.sh SEED` (C's unchanged tool on the read-back FASM, the cross-check);
  - outputs: `rtb/s<s>/{rtd.txt,rtd.json,cap.json}`, `rt/s<s>/`;
  - summary: `tools/selord_sum.py` → `selord_summary.txt`;
  - worst-instance dump: `dump/s1_X28Y67A_indep.txt`.
- **Latches:**
  - `lat.sh SEED` = `tools/tighten_dump.py` (from `tools/mkdump.py`) + `tools/latchsp.py`;
  - outputs: `lat/dump_<s>.json`, `lat/lat_<s>.json`, `lat/lat_<s>.txt`;
  - summary: `tools/lat_sum.py`.

## Correction (audit pass 4, rows 43/71)
The H_SELORD/RT_FB evaluation above reused C's rtfb_design.py, which omits the driver-side LUT->xMUX hop (prjxray a6lut->amux 0.071..0.209 ns). With it the rig's urig.uenv1 ring fails on 2 of 4 seeds (C's tcheck: seed 2 -114/-219 ps, seed 4 -81/-201 ps banded). The "+4 ps" above is optimistic. Kernel C-elements keep positive margins.
