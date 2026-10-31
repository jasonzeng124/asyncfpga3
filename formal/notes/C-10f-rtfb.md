# C-10f: is the C-element feedback race (RT_FB) real on shipped designs?

Shard C, probe 10f (track 10), 2026-10-27.

## Correction (2026-10-29, probe C-10f2; see notes/C-10f2-rtfb.md)

The audit (P4, row on 1149aa1) was right: `rtfb_design.py` had no driver-side LUT -> xMUX hop.
Every route leaving a slice through AMUX..DMUX was short by the prjxray ROUTING_BEL hop, for
example `a6lut -> amux (0.071::0.088)(0.168::0.209)` ns. This applied to the feedback and to the
responses alike.

C-10f2 added the hop, re-routed all 12 routes (FASM-byte-identical to the ones below), and
regenerated every RtFb Lean file. Theorem names are kept; their numbers changed.

- **WITHDRAWN: "gcd_hw: 0 failures in fast, slow, fastE and slowE".** On seed 4 the rig's
  `urig.uenv1.u` fails the `fast` variant at **−16 ps**; this section originally reported +4.
  - Kernel-checked: `gcd4_pass` (fast 9 of 10) and `gcd4_fast_exact`, which gives a violating
    fixed-delay run.
  - slow, fastE and slowE still have 0 failures on all 4 seeds. uenv1 on seed 4: +51 / +94 / +161
    (was +124 / +114 / +234). On seed 2: fast +14, slowE +162 (was +109 / +375).
  - **The kernel alone (without uenv0/uenv1) still has 0 failures in every one-corner variant on
    every seed.** Worst: fast +70, slowE +530.
  - The −16 comes from charging uenv1's one shared CMUX hop at its max on the feedback and its min
    on the response. The per-element window model always does this. With either single prjxray
    instance (xMUX or xMUXL) the slack is −13.
  - With every element at one common corner end, the rig still passes by at least +167 ps (seeds 2
    and 4; Python evidence).
- **Muller pipeline.** The race is still real on all 8 seeds, but smaller.
  - slowE: 1 to 8 of 64 fail (mean 3.9; was 4 to 12, mean 7.2). Worst slack −4 to −218.
  - fastE: 0 to 5 fail.
  - Common corner: 2 of 8 seeds fail (was 5 of 8). Seed 3's −112 is gone; seed 8 has −68.
- **The tables below are the no-hop model.** RTFB_NO_HOP=1 reproduces them exactly. Do not cite
  them as current.

## Verdict

**Works. The race is real on the bare Muller pipeline, on every seed. It is not reached on
the shipped gcd_hw kernel in any one-corner model, on any of 4 seeds.**

- **Muller pipeline (10d's 64-stage `bd_c2n` ring), 8 seeds.** Under slowE, 4 to 12 of the
  64 C-elements fail RT_FB (mean 7.2). The worst slack is between −116 and −231 ps.
  - It survives perfect correlation. With every element at the same corner end, 5 of the
    8 seeds still have 1 to 3 failing stages. The worst is seed 3: −112 ps with
    everything at slow_max.
  - 10d's seed 1 happens to be a seed where full correlation saves every stage.
- **gcd_hw (the board-measured kernel plus its rig), 4 seeds, 363 C-elements each.**
  - 0 failures in fast, slow, fastE and slowE. The worst slowE slack is +234..+895 ps
    (mean +508).
  - Under H_INDEP (no correlation at all), 5 to 9 fail (mean 7.5). The worst is −282 to
    −503 ps.
  - The kernel is safe because almost every response path runs through more logic
    (`bd_delay` chains, DACK, joins). The earliest response is 2 to 5 LUT hops away, so it
    arrives about 1-4 ns (median) after the latest feedback.
  - The tightest C-element on 2 of the 4 seeds is the RIG's `uenv1`, not the kernel's.
    `uenv0`/`uenv1` in `cells/hw/gcd_rig.v` are a bare 2-cell Muller ring. On seed 4 it
    has +4 ps at the fast corner when RC is allowed down to 0, and +234 ps at slowE.
- **Pins.** The feedback lands on physical pins 1-5 and **never on A6**. Every failing
  Muller stage has its feedback on pin 1, 2 or 3, the slow site pins (409-531 ps at
  slow_max, against 112-137 ps for pin 5).
  - gcd_hw has the same distribution: of 1452 C-element instances (4 × 363), 212 have the
    feedback on pin 1, 63 on pin 2, 41 on pin 3, 235 on pin 4 and 901 on pin 5.
- **No constraint in the flow.** Nothing in `cells/`, `bdc/` or `patches/` pins the
  feedback (no LOCK_PINS, no BEL-pin attribute, no cost term), and the nextpnr binary
  contains no LOCK_PINS string. The feedback pin is whatever the router's LUT-permutation
  pseudo-pips happen to pick.

## What checks (run it)

    formal/tools/rtfb/run.sh          # routes + Python + Lean data + formal/check.sh (~1.5 h; gcd bitstreams dominate)
    formal/tools/rtfb/run.sh --no-route
    cd formal && ./check.sh Formal/Timing/RtFbCore.lean Formal/Timing/RtFbM64S{2,3,4,5,6,7,8}.lean \
        Formal/Timing/RtFbMuller.lean Formal/Timing/RtFbGcdS{d,2,3,4}.lean Formal/Timing/RtFbGcd.lean

- Compile times on this machine: each Muller data file about 80 s, `RtFbMuller.lean` about
  10 min (one slot, under 1 GB RSS), each gcd file plus `RtFbGcd` under 2 min.
- `check.sh` result: **[check] OK, 449 declarations audited**.

**Toolchain.** `cells/verify/toolchain.sh` passed before every route, with nextpnr
**sha256 9c732bc6303458df**. `fasm_audit.py` PASS on every route.

**Muller routes.** 10d's `pipe/route.sh` invocation (cells/flow.sh options, `--freq 100
--seed s`), written to `formal/tools/rtfb/build/muller/`. The seed-1 read-back FASM is
byte-identical to 10d's fixture.

FASM sha256 prefixes, Muller:

| seed | sha256 prefix |
|---|---|
| s1 | 2beed0e8eb948279 |
| s2 | beaaa1bf973073a5 |
| s3 | 83fb734c9b762226 |
| s4 | 23707c4e7442f68a |
| s5 | 9673f229c25f7df9 |
| s6 | 2a99521d3c1f3c17 |
| s7 | e0d0be95a87beb4f |
| s8 | df990ce74e43e96b |

**gcd_hw routes.** These are C-10e's (`formal/tools/tcheck/route.sh`): the project flow
`cells/hw/build_hw.sh gcd_hw` on a private copy of cells/ and bdc/, with
`cloud/fixtures/frontend/gcd`, `BDC_SELECT_PADS=gcd_hw_pads.json`, `BD_RLOC=v4` and
`NEXTPNR_SEED` pinned (d = no `--seed`).
- They are copied to `build/gcd/s*/` before use.
- Seeds 2 and 4: 10e's `build_hw.sh` PASS, and their `.bit` was used.
- Seeds d and 3: 10e's bitstream step died. `gcd_rt.sh` wrote the bits itself, with the
  same `fasm2frames`/`xc7frames2bit` calls.

FASM sha256 prefixes, gcd_hw:

| seed | sha256 prefix |
|---|---|
| d | b73e1ba0e4cba92f |
| 2 | 1ee50d56638ef0b3 |
| 3 | 855635c4ebed15e5 |
| 4 | b56d32b1eecdaed9 |

I did not build xorshift: gcd_hw is the design with the board measurements and the GLS rig.

### Files (all mine)

| file | content |
|---|---|
| `formal/tools/rtfb/route_muller.sh` | Routes the Muller pipeline for one seed and reads it back from the bits |
| `formal/tools/rtfb/muller_rt.sh` | 11b's fasm2lean plus 10d's rt_all.py, both unchanged, giving the report and the Lean data `RtFbM64S<s>.lean` |
| `formal/tools/rtfb/rtfb_design.py` | **Whole-design RT_FB** (below) |
| `formal/tools/rtfb/gcd_rt.sh` | Copies a 10e route, reads back its bits, runs rtfb_design |
| `formal/tools/rtfb/lean_gcd.py` | Generates `RtFbGcd.lean` |
| `formal/tools/rtfb/summarize.py` | Mean and range over seeds |
| `formal/tools/rtfb/run.sh` | All of the above |
| `formal/lean/Formal/Timing/RtFbCore.lean` | `nPass`, `worstSlack`, `rt_sound_of`, `rt_violated_of` |
| `RtFbM64S2..8.lean` | Generated Muller data |
| `RtFbMuller.lean` | Muller theorems |
| `RtFbGcdS{d,2,3,4}.lean` | Generated gcd data |
| `RtFbGcd.lean` | gcd theorems |

Outputs (gitignored) are under `formal/tools/rtfb/build/`:
- `muller/summary.txt` and `muller/point_summary.txt`;
- `muller/worst_s3_slowE.txt`, the concrete violating run;
- `muller/muller64_s*.{rt,rtd,point}.txt`;
- `gcd/summary.txt` and `gcd/s*/rtd.txt` (the per-C-element table and the worst paths),
  plus `rtd.json`.

## The checker for whole designs: `rtfb_design.py`

10d's `rt_all.py` cannot run on a shipped design for two reasons:
- fasm2lean stops on any LUT pin fed by an FF, a carry chain or an F7 mux;
- it only looks one LUT hop from the C-element.

`rtfb_design.py` replaces both limits. It reuses the following unchanged by import:
fasm2lean's `Fabric`, `Extract.walk`, `read_fasm` and `corners`, and routed2lean's
`lut_arcs` and `parse_sdf`.

- **C-elements are identified from the netlist.** They are the cells of nextpnr's routed
  JSON whose `src` is a LUT6 line of `cells/rtl/bd_ce.v` (bd_c2, bd_c2_set, bd_c2n,
  bd_c2n_set, bd_c3, bd_c4, and the norst variants).
  - The physical feedback pin is the logical I2/I3/I4, mapped through X_ORIG_PORT.
  - **It is cross-checked against the bits:** the pin the bitstream wires from the LUT's
    own output must be that pin. The tool exits if not. All 363 × 4 and 64 × 8 instances
    agree.
- **RT_FB(i):** the feedback route reaches its pin before ANY response to i's O6 edge
  reaches another pin of i.
  - A response is any simple LUT path i → j1 → … → i, through O6 or O5, with prjxray LUT6
    or LUT5 arcs.
  - The paths are unrolled as a TREE: every path gets its own node copies. So no simple
    path is lost to the unrolling, and the cones share only the launch (`sepOne`).
- **Pruning.** A prefix is dropped when its H_INDEP lower bound plus a backward-Dijkstra
  distance is at least the feedback's H_INDEP upper bound. Such a path arrives late in
  every bound variant.
- **Independent cross-checks.** An unpruned Dijkstra computes the earliest response and
  the exact slack per variant. It agrees with the tree on every C-element of every route,
  with 0 disagreements. On all 8 Muller seeds the failing counts equal 10d's `rt_all.py`
  exactly.
- **Long-line walk failures.** On gcd_hw, 132 to 374 LUT pins per route cannot be walked
  by fasm2lean. They sit on long-line LV/LH nodes reached through bidirectional pips,
  whose FASM feature names one fixed orientation. Mostly these are `rig_rst`, the BSCAN
  `bs_capture`, and a few high-fanout handshake nets.
  - For these pins the SOURCE comes from nextpnr's routed JSON and the ROUTE is
    **H_UNKNOWN_ROUTE = [0, 10^5] ps**. That credits the earliest possible response, which
    is conservative for RT_FB.
  - A feedback pin is never one of them (checked).
  - Trying to walk bidirectional pips in reverse produced false shorts, so it is disabled
    (`Ex.BIDIR = False`).

## Results

### (1) Muller pipeline, 8 seeds

C-elements failing, of 64 per seed (each count is kernel-checked as `m64sN_pass`):

| seed | indep | fast | slow | fastE | slowE | sdf |
|---|---|---|---|---|---|---|
| 1 | 42 | 16 | 14 | 12 | 12 | 1 |
| 2 | 43 | 11 | 8 | 4 | 5 | 0 |
| 3 | 41 | 14 | 14 | 11 | 11 | 0 |
| 4 | 39 | 9 | 7 | 5 | 5 | 0 |
| 5 | 37 | 7 | 6 | 4 | 4 | 0 |
| 6 | 43 | 12 | 8 | 4 | 4 | 0 |
| 7 | 40 | 11 | 10 | 7 | 7 | 0 |
| 8 | 42 | 15 | 15 | 11 | 10 | 0 |
| **mean [range]** | 40.9 [37..43] | 11.9 [7..16] | 10.2 [6..15] | 7.2 [4..12] | 7.2 [4..12] | 0.1 [0..1] |

Worst slack in ps, mean [range] over the 8 seeds (per seed in `m64sN_worst`): indep −641
[−726..−594], fast −133 [−188..−117], slow −218 [−325..−184], fastE −67 [−94..−47],
slowE −154 [−231..−116], sdf +96 [−7..+206].

**Common-corner evidence (Python, H_CORRELATED).** Every element is at the same end of its
range (fast_min, fast_max, slow_min or slow_max), with RC = E. The slack is linear in a
common quantile, so the two ends are enough.
- Failing stages per seed: 0, 2, 3, 0, 2, 1, 0, 2 (at slow_max: 0, 2, 3, 0, 2, 1, 0, 1).
- The worst is seed 3: −31 / −45 / −84 / −112 ps.
- So, unlike 10d's seed 1, correlation does not rescue the pipeline in general.

**Pins (slowE, 8 seeds).**

| feedback pin | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| C-elements with this pin | 135 | 20 | 15 | 134 | 208 | 0 |
| of which fail RT_FB | 42 | 13 | 3 | 0 | 0 | 0 |

- prjxray site-pin delays at [slow_min, slow_max]: pin 1 ≈ 416-531 ps, pin 2 ≈ 406-512,
  pin 3 ≈ 278-372, pin 4 ≈ 227-303, pin 5 ≈ 91-137, pin 6 ≈ 4-22.
- Pin 6 is never used for the feedback. On every C-element seen, nextpnr puts the tied-off
  logical I5 on A6 (`X_ORIG_PORT_A6 = I5` on 362 of 363 gcd cells, the last having no
  attribute, and on 64 of 64 Muller cells). So the fastest pin carries a constant, and
  the feedback competes for A1..A5.
- The responding neighbour usually arrives on pin 5 (54 of 128 neighbour pins of failing
  stages).

### (2) gcd_hw, 4 seeds, 363 C-elements each

The C-elements per seed are 153 bd_c2, 185 bd_c2n, 1 bd_c2n_set (the rig), 10 bd_c3 and 14
bd_c4. Only 5 to 9 per route have any response path that could arrive before the
feedback. The rest are excluded by the bound (H_CONE, Dijkstra-checked).

| seed | in Lean | indep fail / worst | fast | slow | fastE | slowE | slowE worst at | kernel-only slowE worst |
|---|---|---|---|---|---|---|---|---|
| d | 9 | 9 / −503 | 0 / +70 | 0 / +348 | 0 / +252 | 0 / **+530** | ucontrol_merge10.uarb1.ua2 | +530 |
| 2 | 8 | 8 / −290 | 0 / +109 | 0 / +345 | 0 / +139 | 0 / **+375** | rig uenv1 (bd_c2n_set) | +946 |
| 3 | 5 | 5 / −282 | 0 / +248 | 0 / +659 | 0 / +484 | 0 / **+895** | rig uenv1 | +1094 |
| 4 | 8 | 8 / −389 | 0 / **+4** | 0 / +124 | 0 / +114 | 0 / **+234** | rig uenv1 | +1220 |

- Mean of the worst slowE slack: +508 ps, range [+234..+895].
- Median slowE slack per route: about +3.7..+4.0 ns.
- Common-corner models (seeds 2 and 4): 0 failures, worst +167 ps.

So in this placement flow the feedback race is a property of bare C-element rings: 10d's
pipeline, and the rig's `uenv0`/`uenv1`. Compiled bd_link chains are not affected. The
fast corner with RC down to 0 leaves the rig only +4 ps on seed 4. That margin rests on
H_RC_EXACT's lower bound, and also on H_UNKNOWN_ROUTE never being involved there (it is
not: the `uenv1` path is fully walked).

### (3) Which pins, and does the flow constrain them

- The feedback pin is chosen by the router through the LUT-permutation pseudo-pips (see
  `patches/README.md`, lut-perm-sink).
- No file in `cells/`, `bdc/` or `patches/` constrains it: grep for LOCK_PINS, lock_pin
  and BEL_PIN finds nothing relevant, and `rloc_stamp.py` sets only placement.
- The installed nextpnr has no LOCK_PINS support string.
- The project's only defence today is structural: response paths pass through delay
  chains.
- Possible fixes, none applied:
  1. a LOCK_PINS-style patch keeping the feedback on pin 5 (or freeing A6 by declaring the
     cell LUT6 with I5 used);
  2. a router cost on slow site pins for self-loops;
  3. this checker as a post-route gate. It costs about 2 min per gcd route.

### (4) The worst case: concrete run, and what GLS would need

Muller seed 3, stage `st[50]` = SLICE_X40Y98.CLUT (bd_c2n), slowE slack −231. Run
`rtfb_design.py --dump`; the output is in `build/muller/worst_s3_slowE.txt`. Launch is c[50]'s O6
edge at t = 0:

- **Feedback**, every element at slow_max: CMUX → LOGIC_OUTS22 → NL1BEG_N3 (131) →
  IMUX_L29 (138) → RC 62 → **site pin C2 507**. It arrives at **838 ps**.
- **Response** from the same-slice neighbour BLUT (c[51]), every element at slow_min:
  IMUX_L24 (114) → RC 59 → B5 93 → LUT A5→O6 100 → BMUX → IMUX_L31 (114) → RC 35 →
  **C5 92**. It arrives at **607 ps**.
- Between 607 and 838 ps the C-element's inputs disagree while C2 still holds the old
  value. The majority LUT pulls c[50] back after about 100-124 ps, a runt of up to about
  231 ps. The runt then circulates on the feedback.
- With every element at slow_max (fully correlated) the same pair is still −112 ps. A
  single-corner simulation can therefore show it, without any per-element mixing.
- Kernel-checked: `m64s3_slowE.2` gives a FixedRun violating RT_FB for this entry, and
  `m64s3_worst` gives the −231.

**What a GLS run (cells/gls/) needs to show it:**
1. **Per-sink delays from prjxray, not nextpnr's SDF.** For each `ICBUF`: pips + Elmore +
   the PHYSICAL site pin. nextpnr's SDF puts a flat 25 ps site pin, and sdf = 0/64
   failing on this seed.
2. **The LUT IOPATH per physical pin** (prjxray 100-124 ps slow, the same for all pins).
3. **A LUT model that passes runts.** The annotated build's specify paths are inertial and
   would swallow a pulse shorter than the LUT delay, so a transport LUT output is needed,
   as `GLS_TRANSPORT_IC` already does for ICBUF.
4. **The design.** gen.py would have to be pointed at the Muller pipeline's routed JSON
   (`build/muller/muller64_s3_routed.json`) with the toggle environment as testbench. One
   req edge suffices.
5. **The observable.** c[50] shows a non-monotonic edge after the wave passes stage 50, or
   the token count diverges from the reference.

For gcd_hw a GLS with the same delays should show nothing (+234 ps minimum). Showing that
negative needs the same items 1 to 3.

## What is proved (kernel `decide +kernel`, no sorry/axiom/native_decide)

**`RtFbCore`:**
- `rt_sound_of`: every passing entry satisfies RT_FB in every `Run`.
- `rt_violated_of`: every failing entry has a violating `FixedRun`.
- Both lift 10d's `rtOne_sound` and `rtOne_exact`.

**`RtFbMuller`, for each seed N = 1..8** (seed 1 on 10d's data):
- `m64sN_pass`: the count of passing C-elements for all 6 variants;
- `m64sN_worst`: the worst slack for all 6 variants;
- `m64sN_wf`, `m64sN_sep`;
- `m64sN_slowE`: passing stages are safe in every run, and failing stages have a real
  violating run.

`m64_seeds_slowE_range`: on every seed, 52 to 60 of the 64 pass at slowE.

**`RtFbGcd`, for each seed S ∈ {d, 2, 3, 4}:**
- `gcdS_len`, `gcdS_pass`, `gcdS_worst`, `gcdS_wf`, `gcdS_sep`;
- `gcdS_slowE_safe` and `gcdS_fastE_safe`: every C-element with a response path in the
  bound satisfies RT_FB in every run (H_ONE_CORNER + H_RC_EXACT);
- `gcdS_indep_violated`.

**Evidence only (Python, labelled):**
- H_CONE (the C-elements pruned out on gcd_hw, 354-358 per route);
- the common-corner (H_CORRELATED) results;
- the pin statistics;
- the gcd kernel-vs-rig split and the medians.

## Hypotheses (each named, and how to test it)

- **H_INDEP, H_ONE_CORNER, H_RC_EXACT** (10d): per-element intervals from prjxray.
  - The verdict on the Muller pipeline hangs on how correlated on-die delays are.
  - Test: rings at many sites (10d's band hypothesis).
- **H_CONE**: paths pruned by the H_INDEP bound cannot violate.
  - True by monotonicity of sums. It is checked by the Python Dijkstra, which agrees with
    the tree on every C-element; it is not in Lean.
  - Lean form: emit the backward distances as a certificate. Not done.
- **H_UNKNOWN_ROUTE**: an unwalkable long-line route is [0, 10^5] ps.
  - It is conservative for responses and never used on a feedback.
  - Test: fix the fasm2lean bidirectional-pip walk.
- **H_OPAQUE_CUT**: FF, carry, IOB and BSCAN outputs do not respond to a C-element edge
  inside the window.
  - FFs are clocked, and these sources feed no C-element pin on these designs (0-1 pins,
    a GND).
  - Test: GLS.
- **H_ZERO_DELAY_FN, per-event channel** (10a): a violation is a hazard, not necessarily a
  board failure, because a real LUT filters short runts. That is why GLS item 3 matters.
- **prjxray corner data**: there is no rise/fall split, no OUTMUX site delay, and the site
  pins are per pin.

## What does not work / not done

- **The fasm2lean bidirectional long-line walk.** fasm2lean cannot walk LV/LH long-line
  nodes driven through bidirectional pips (132-374 pins per gcd route). This is worked
  around (H_UNKNOWN_ROUTE), not fixed.
- **H_CONE is not in Lean.**
- **Self-feedback latch LUTs not checked.** The 2282 other self-feedback LUTs
  (bd_latch/dctl) are listed but not checked; their race is a different property
  (enable against data).
- **No xorshift build.**
- **No GLS run.** It needs the gen.py changes in (4).

## Decisions (no one to ask)

- **Reused C-10e's gcd_hw routes** instead of routing gcd_hw a fifth time on a 4-CPU
  machine they were already loading. They are the project flow with a pinned seed and
  toolchain.sh. They are copied, never edited.
- **The bitstream is always the source.** For seeds d and 3, whose bitstream step died in
  10e's run, the bits were written here.
- **All gcd C-elements are in the result, rig included.** The rig's `uenv1` is on the
  board too.
- **Read-only throughout:** no git, and no edits outside the files listed.

## check.sh

`./check.sh` on the 14 RtFb files: **[check] OK, 449 declarations audited** (only propext /
Quot.sound / Classical.choice; no sorry, axiom or native_decide). Log: `formal/tools/rtfb/build/check.log`.
