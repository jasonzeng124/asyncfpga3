# B-on-netlist-arb (probe Bt3): the arbiter's timed theorems on the routed bits

Shard B x shard C. 2026-10-27. File: `formal/lean/Formal/Cells/OnNetlistArb.lean` (core Lean,
1525 lines, 108 theorems). This continues probes Bt and Bt2 (`B-on-netlist-timed*.md`). It does
for the routed `bd_arbiter` what they did for the C-element and the latch.

Data: C-11c's `Formal.Net.FasmLink.S1..S4`, read back from the four routed `link_arb`
bitstreams. They were routed by **nextpnr sha256 9c732bc6303458df** (all 9 patches `ok`,
`toolchain.sh` ok, as stamped in `fixture/link_arb_s*.toolchain` by `fasm2lean2/check.sh`).
Nothing was re-routed, so no new routed numbers come from a new build.

Per-corner windows are recomputed from the per-pip prjxray data in probe Bp's regenerated
importer JSON (`scratchpad/pins/out/la_s*.json`). Bp showed those files are byte-identical to
C's committed `S<n>.lean`. A script assertion checks that their box windows equal C's
`pinDelay` for every arbiter pin. In Lean, `pinDelay_fork_s*` ties the fork pins to C's
`pinDelay` by `decide`.

## Verdict

**Works.** The bridge is built and instantiated on all 4 seeds × 2 clients. RT1/RT2 are
instantiated on all 4 seeds in three readings, and each `smin` requirement is proved exact
(sufficient and tight). The answer depends on the corner model:

- **Consistent die corner** (H_ONE_CORNER: every LUT and route at one prjxray corner). The
  fork is safe on all 8 seed×client pairs at both corners. This is proved on C's `Behaves`.
- **Independent box** (H_INDEP: each delay anywhere in [fast_min, slow_max + Elmore]). The fork
  margin is **negative on all 8 pairs**, even with 7g's shared-prefix credit. 7g's
  `client{1,2}_box` then proves that some fixed-delay run in the box acknowledges early.
- **With the CLAUDE.md guardband on top of the corner windows** (arithmetic only): the fork
  margin is negative on 2/8 pairs at the slow corner and 7/8 at the fast corner.

So "safe as routed" holds only under the one-corner model. The fixtures cannot decide which
corner model is right (Bp, "Cannot").

## Check command

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OnNetlistArb.lean

- **Clean**: no output, about 22 s.
- All imported oleans already existed: `Prelim`, `CElemTiming`, `ArbA0Fork`, `ArbHeldTimed`,
  `ArbHeldTimed2`, `Fasm.Basic`, `FasmLink.S1..S4`. Nothing was compiled into `.lake`.
- `python3 formal/scan.py` on the file is clean.
- `#print axioms` on all 108 theorems, run on a scratch copy:
  - 59 give `[propext, Classical.choice, Quot.sound]`;
  - 16 give `[propext, Quot.sound]`;
  - 29 give `[propext]`;
  - 4 (`wiring_s*`) depend on no axioms.

  There is no `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`.

The generator scripts (not in the repo) are in
`/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/bt3/`:
- `data.py` holds the windows;
- `rt.py` holds the RT arithmetic;
- `gen.py`, `gen2.py`, `gen3.py` and `gen4.py` emit sections 3–5 and the tightness lemmas.

## Theorems (namespace `Formal.Cells.OnNetlistArb`)

### Generic

| name | statement |
|---|---|
| `win_before`, `win_step_late` | Window-channel facts. A window copy of a trace that holds `v` before `T` holds `v` before `T+lo`. A window copy of a falling step at `T0` is high only before `T0+hi`. |
| **`fork_safe_win`** | The positive direction of 7g's `no_early_ack_iff`, **lifted to C/B's `WinDelay`** (the delay may vary per tick inside its window). Nine window channels: A0→ustate pin, ustate LUT, q feedback, q→ugrant pin, ugrant LUT, grant→ua_k pin, A0→ua_k pin, ua_k LUT, ua_k feedback. Hypotheses: H_A0_FALL (one falling step at `T0`), H_SETTLED (held values before `Ts`, every window's `hi ≤ Ts ≤ T0`), H_LOOP (both loops `lo ≥ 1`), and **H_FORK `hi(A0→ua_k) ≤ lo(A0→ust) + lo(ust) + lo(q→ug) + lo(ug) + lo(g→ua_k)`**. Conclusion: `A_k` never rises. ua_k's own LUT window drops out, because the LUT reads both inputs at the same instant. |
| **`fork_safe_net`** | **The bridge.** From C's `Behaves` on any `PNet`, for LUTs `iS/iG/iA` that satisfy two conditions: (a) their physical functions on their physical pins equal 7g's `F`, `G` and `cel` (`hfn*`); (b) their pins are routed as the arbiter wires them (q feedback, A0 from port `p0` into both, q into ugrant, grant on output `og` into ua_k, ua_k feedback). Then `fork_safe_win` holds, with every window being C's `dl`/`dw`. |

### Per seed

| name | statement |
|---|---|
| `wiring_s*` | The physical pin sources of ustate, ugrant, ua1 and ua2 (`rfl`). |
| `pinDelay_fork_s*` | The box windows of the 9 fork pins are C's `pinDelay` (decided). |
| `fn_ust_c{1,2}_s*`, `fn_ug_c{1,2}_s*`, `fn_ua{1,2}_s*` | The physical INIT on the physical pins equals 7g's `F1/F2`, `G1` (O5) / `G2` (O6) and `cel`. The ties come from the bits; the steady requests and rst are substituted. Decided. |
| `fn_ust_req_swap_fails_s1` | **Negative control.** With the r1 and r2 pins swapped, the function is not `F2`. Swapping A0 and q is *not* a control, because `F2 q a = q && a` is symmetric. |
| **`fork_c{1,2}_s{1..4}_{slow,fast}`** (16 theorems) | On `Behaves Sn.net`, with H_DIE_SLOW / H_DIE_FAST (the window values), H_A0_FALL at port 0, H_REQ_STEADY (the r1, r2 and rst pins of ustate, ugrant and ua_k are constant), `H_TS : 2000 ≤ Ts ≤ T0` and H_SETTLED, ua_k's output is false at every `t`. |
| `run7g_c{1,2}_s*_box_full`, `_box_unsh` | `¬ ∀ p ∈ box, ArbA0Fork.Safe …`. This is 7g's `client_box`, only-if direction, on the routed windows. |
| `run7g_c{1,2}_s*_{slow,fast}` | `∀ p ∈ box, Safe …` at one corner (7g's run model, with the shared-prefix `c`). |
| **`rt_s*_{box,slow,fast}`** | For every `ArbHeldTimed.Dl` whose wires and arcs lie in the routed windows (`RtBox.has`) and with `smin ≥ S`, RT1, RT2, RT1b and RT2b hold. In the slow/fast readings, A0Fork and A0Fork2 hold too. |
| **`rt_s*_*_tight`** (11 theorems) | A record in the same box with `smin = S − 1` breaks the binding condition. So each `S` is exact. |

### Hypotheses (all named)

- From C's `Behaves`:
  - **H_LUT**: one window per LUT site;
  - **H_ROUTE**: one window per routed pin;
  - **H_TIE**.
- **H_DIE_SLOW / H_DIE_FAST**: the windows of the 3 LUTs and 6 routed pins used, at one
  corner. A route window is [Σ pip corner-min + site-pin corner-min, Σ pip corner-max +
  site-pin corner-max + Elmore]. The LUT window is the CLB SDF column envelope:
  - LUT6_2 (ustate, ugrant), O5∪O6: slow [93, 157], fast [42, 63];
  - LUT6 (ua_k): slow [100, 124], fast [45, 56].

  Test: GLS with prjxray SDF at one corner, or the board at temperature extremes.
- **H_A0_FALL**: the A0 port makes exactly one falling edge at `T0`.
- **H_REQ_STEADY**: the request and rst pins are steady. This is 7g's prose hypothesis made
  formal at the pins. Physically: client k holds its request until acked, and the other client
  cannot re-request before its own ack falls.
- **H_SETTLED, H_TS**: the held state has been settled for `Ts ≥ 2000 ps` (above every window
  max, which is ≤ 1617) before A0 falls. `WinDelay` constrains nothing before its `hi`, so the
  power-up values have to be assumed.
- **H_SERVER_MIN (`smin`)**: the minimum response of the server, kept as a hypothesis. The
  server is a pad here.
- **H_A0_SHARED** (only in the `unsh`/corner `run7g` and in the RT readings): the A0 prefix
  that both branches share is one wire with one delay per run. The r1 and r2 nets use the same
  assumption at their divergence node.

## Numbers (ps; 4 seeds; mean [range]; never a single route)

### (1) The 7g fork per seed and client: `margin = lo(early) − hi(late)`

`early` = A0→ustate pin + ustate + q→ugrant pin + ugrant + g_k→ua_k pin. `late` = A0→ua_k pin.

| reading | client | s1 | s2 | s3 | s4 | mean [range] |
|---|---|---|---|---|---|---|
| **box, full routes** (C's `pinDelay` verbatim; theorem `run7g_*_box_full`) | 1 | 837−1283 = **−446** | 924−1282 = **−358** | 970−1461 = **−491** | 867−1500 = **−633** | **−482 [−633, −358]** |
| | 2 | 804−1443 = **−639** | 1008−1462 = **−454** | 964−1617 = **−653** | 998−1464 = **−466** | **−553 [−653, −454]** |
| **box, unshared** (7g's `c` credit; `run7g_*_box_unsh`) | 1 | 677−795 = **−118** | 752−760 = **−8** | 754−809 = **−55** | 695−978 = **−283** | **−116 [−283, −8]** |
| | 2 | 644−955 = **−311** | 836−940 = **−104** | 748−965 = **−217** | 826−942 = **−116** | **−187 [−311, −104]** |
| **slow die, full routes** (`Behaves` theorem `fork_*_slow`) | 1 | 2084−1283 = +801 | 2338−1282 = +1056 | 2442−1461 = +981 | 2164−1500 = +664 | +875.5 [+664, +1056] |
| | 2 | 2063−1443 = +620 | 2513−1462 = +1051 | 2457−1617 = +840 | 2479−1464 = +1015 | +881.5 [+620, +1051] |
| **fast die, full routes** (`fork_*_fast`) | 1 | 837−577 = +260 | 924−595 = +329 | 970−674 = +296 | 867−681 = +186 | +267.75 [+186, +329] |
| | 2 | 804−655 = +149 | 1008−683 = +325 | 964−731 = +233 | 998−685 = +313 | +255 [+149, +325] |
| slow die, unshared (`run7g_*_slow`) | 1 | +878 | +1139 | +1087 | +747 | +962.75 [+747, +1139] |
| | 2 | +697 | +1134 | +946 | +1098 | +968.75 [+697, +1134] |
| fast die, unshared (`run7g_*_fast`) | 1 | +302 | +374 | +350 | +231 | +314.25 [+231, +374] |
| | 2 | +191 | +370 | +287 | +358 | +301.5 [+191, +370] |

**With the guardband** (`⌊0.772·early − 1.155·late⌋` on the full-route corner windows;
arithmetic, not in Lean):

| reading | client | s1 | s2 | s3 | s4 | mean [range] |
|---|---|---|---|---|---|---|
| slow | 1 | +126 | +324 | +197 | **−62** | +146.25 [−62, +324] |
| slow | 2 | **−75** | +251 | +29 | +222 | +106.75 [−75, +251] |
| fast | 1 | **−21** | +26 | **−30** | **−118** | −35.75 [−118, +26] |
| fast | 2 | **−136** | **−11** | **−101** | **−21** | −67.25 [−136, −11] |

The guardband is arguably double counting here, because the windows are already corner
envelopes with full Elmore on the late side. CLAUDE.md asks for guarded margins, though, and
CLAUDE.md says take the longer number when ambiguous.

**FLAGS (negative margin):**
1. Every seed and client is negative in both box readings: 8/8 full, 8/8 unshared.
2. The guarded readings are negative at:
   - slow: s4 client 1, s1 client 2;
   - fast: 7 of 8 pairs (all but s2 client 1).
3. The tightest raw one-corner margin is **s1 client 2 at the fast corner: +149 ps**.

### (2) RT1/RT2 (7h, client 1 releases) and RT1b/RT2b (7j, client 2 releases)

`S` is the `smin` each seed needs. Each value is proved sufficient (`rt_s*_*`) and tight
(`rt_s*_*_tight`). `smin` is measured from R0 at ustate's output to A0 at A0's three-way
divergence node: R0's output route, the OBUF, off chip, the IBUF and the shared input
prefix.

| reading | s1 | s2 | s3 | s4 | mean [range] | binding condition |
|---|---|---|---|---|---|---|
| box (H_INDEP) | 718 | 865 | 898 | 710 | 797.75 [710, 898] | RT2.g1 (s1, s2), RT2b.g2 (s3, s4) |
| slow die | 6 | 189 | 24 | 0 | 54.75 [0, 189] | g1 (s1, s2), g2 (s3); none on s4 |
| fast die | 66 | 153 | 101 | 37 | 89.25 [37, 153] | g1 (s1, s2), g2 (s3, s4) |

How to read the table:
- The binding condition is always the "g" leg: g_k's fall reaches ua_k and the ua_k loop
  closes before A0 re-rises. Its coefficient on `smin` is 2.
- In the box, **A0Fork and A0Fork2 fail on every seed** (worst-case values −305, −98, −211,
  −110 and −115, −5, −52, −280). These are part (1)'s box numbers, read through 7h's per-output
  arcs. So `rt2_exclusion_arcs` and 7j's mirror theorem **cannot be applied in the box
  reading**, whatever `smin` is.
- In both one-corner readings every A0Fork holds, so all of 7h/7j's exclusion theorems apply
  once `smin ≥ S`.
- **Does the pad server meet `S`?** The on-chip shared A0 prefix alone is [160..216, 488..652]
  (fast_min … slow_max over the seeds); its slow_min is 411 / 439 / 546 / 439 and its
  fast_min 160 / 172 / 216 / 172. At one corner that alone covers `S` on every seed even with
  zero off-chip time (tightest: s2 fast, 153 needed against 172). In the box, `S` = 710–898 needs the off-chip round trip. That
  is physically certain (ns), but **unproved: H_SERVER_MIN stays a hypothesis**. The
  OBUF/IBUF/board path is not in `pinDelay`, as Bt2 found for rule H.

### (3) Cross-check against Bp (site-pin-corrected rule J and the prjxray fork)

- **Bp's prjxray fork margin** (unshared pips, box): client 1 −113 [−280, −5], client 2 −181
  [−305, −98]. Mine is −116 / −187. The difference is exact:
  - I take one LUT window per site (`Behaves`), so the LUT6_2 envelope 42 replaces Bp's 45 for
    the ustate arc and the ugrant O6 arc;
  - that is 3 ps for client 1 and 6 ps for client 2, matching to the ps per seed (e.g. s1:
    −115 → −118, −305 → −311).
- **Corner columns:**
  - Bp at the slow corner: +973 / +983. Mine: +962.75 / +968.75. Bp used 100 and 96 for the
    early arcs, against my SDF column minima of 93 and 93.
  - Bp at the fast corner: +317 / +308. Mine: +314.25 / +301.5.

  Same signs on all 8 pairs in every reading.
- **Rule J from nextpnr's SDF** (Bp, per seed):

  | | client | s1 | s2 | s3 | s4 |
  |---|---|---|---|---|---|
  | raw | 1 | +910 | +1477 | +1959 | +1055 |
  | raw | 2 | +1123 | +1464 | +1696 | +1482 |
  | guarded, no c credit, + box site-pin correction | 1 | +286 | +641 | +734 | +225 |
  | guarded, no c credit, + box site-pin correction | 2 | +208 | +538 | +496 | +564 |

  All 8 are positive.

  **Rule J (shipped gate) passes every pair that the prjxray box reading fails.** Rule J
  reads a single nextpnr number per wire and applies 0.772/1.155. The prjxray box spans
  fast_min to slow_max + Elmore, a ratio of about 3 per wire. That is wider than any guardband
  (Bp: "~3× wider").

  The orderings differ too:
  - rule J's tightest pairs are s4 client 1 and s1 client 2;
  - the slow-die tightest are s4 client 1 (+664) and s1 client 2 (+620);
  - the fast-die tightest are s4 client 1 (+186) and s1 client 2 (+149).

  So the weakest pairs agree.
- **The 7g box theorem and rule J are the same inequality** (7g `box_safe_iff`). Only the box
  differs. On these 4 routes, whether the arbiter is provably safe depends **only** on the
  corner model, not on the bits.

## What did not work / limits

1. **No Behaves-level counter-run.** The negative direction is proved in 7g's fixed-delay run
   model (`run7g_*_box_*`), not as a `Behaves` witness. That would need traces for all 7 LUTs
   and every pin. A fixed delay is a `WinDelay` behaviour (`transport_winDelay`), so it is
   only bookkeeping, about 0.5 day.
2. **`Behaves` has no shared-prefix notion.** Each pin's route is an independent window from
   the port, so the Behaves-level theorem gets no `c` credit. With the one-corner windows it
   does not need it. A refined `Behaves` with a divergence-node trace (H_A0_SHARED) would carry
   it; it is not needed for any positive result here.
3. **The one-corner windows are not in C's generated file.** They come from the same per-pip
   prjxray data (Bp's regenerated, byte-identical JSON) through my script. In Lean they enter
   as named hypotheses with numbers (H_DIE_*), and only the box windows are `rfl`/`decide`-tied
   to C's `pinDelay`. C should emit per-corner `pinDelay` columns so these can be tied too.
4. **Elmore** is added to every max (slow and fast), as C does. This is conservative for
   `late`. Shared-prefix Elmore is charged to the unshared windows (also conservative).
5. **Arc reading.** prjxray's `(a::b)(c::d)` is read as fast/slow corners, following
   ArbCorners and C. Bp flagged that 7g read it as rise/fall. No sign changes in Bp's
   comparison; not re-done here.
6. **7h/7j RT numbers are in 7h's fixed-delay model.** No WinDelay lift was done for RT1/RT2.
   Their positive proofs use exact edge instants (`q_eq`, `g1_eq`), so a window lift is more
   work than the fork's: about 1–2 days.
7. **H_SERVER_MIN cannot be discharged** from the fixture (pad server). See (2).
8. **Kleene X, metastability and inertial filtering** are absent, as in 7g/7h. `Behaves` is
   binary.
9. **Only the A0-fall handover.** The fork theorem covers the A0 fall with client k waiting.
   The A0 rise and the mutual-exclusion (arbitration) case are 7e/7f's and are not bridged.

## Fidelity per primitive

- **ustate, ugrant (LUT6_2).** C's H_LUT is one window per site over the PHYSICAL INIT on the
  PHYSICAL pins. The window is the O5∪O6 column envelope. The function is decided equal to
  7g's `F`/`G` with the bits' ties and steady requests. Glitches are admitted (delay varies per
  tick). Mux-tree internals, X and inertial filtering are not modelled.
- **ua1, ua2 (LUT6, bd_c2).** The same, with the O6 window. The feedback is a routed wire with
  its own window (H_ROUTE), so this is "a LUT whose output feeds back to its own input pin".
- **Routes, including site pins.** Each sink is a window: prjxray intrinsic pips + site pin +
  Elmore. The box form is C's `pinDelay`; the corner forms are my script's.
- **Ties.** Constant (H_TIE).
- **Server.** In the RT readings it is the relation H_SERVER_MIN. In the fork theorem it is
  only the A0 port's single falling edge.

## Effort to finish and what it buys

**Remaining:**
- the Behaves-level counter-run: about 0.5 day;
- per-corner `pinDelay` columns from C's importer: about 0.5 day for C;
- a WinDelay lift of RT1/RT2: 1–2 days;
- **deciding the corner model** (H_ONE_CORNER vs H_INDEP vs "shared corner + local scatter"):
  board or GLS work (research). It is the only thing that decides whether these routes are
  safe.

**What it buys:**
- 7g's fork obligation is now a theorem about the four real bitstreams (pins, INITs, routes).
- The RT obligations come with exact `smin` requirements per seed.
- A sharp statement for the research track:
  - under one-corner timing every route is safe, with fork margins 149–1056 ps;
  - under independent per-wire scatter every route has an early-ack run;
  - guarded corner margins already go negative on 7 of 8 pairs at the fast corner, even
    though the shipped rule J passes all 8 with ≥ +208 ps.
