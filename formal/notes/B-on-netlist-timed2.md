# B-on-netlist-timed2 (probe Bt2): finishing the timed bridge on the routed bits

Shard B x shard C. 2026-10-27. File: `formal/lean/Formal/Cells/OnNetlistTimed2.lean` (core Lean, no Mathlib).
This continues probe Bt (`B-on-netlist-timed.md`, `OnNetlistTimed.lean`).

## Verdict

**Works.** All four items are done and checked clean on all four routed seeds:
1. Latch bits q1 and q2, `holds_value`.
2. `c2_reset`.
3. Rule H, per seed and per bit.
4. `LinkTimed.stage_token`, per seed and per bit.

Rule H cannot be *discharged* from the routed data alone. It needs a lower bound `A` on
"C node falls → the sender changes its data port". That path is the `ack_in` output route,
the OBUF, the off-chip sender, and the input IOB. C's `pinDelay` covers only LUT input
pins, so `A` stays a named hypothesis. Its required value is proved per seed and per bit.

**FLAG: with `A = 0`, rule H fails on all 12 seed×bit pairs** (`rule_h_needs_ack_latency`). On
the bits, the enable fanout reaches the latch enable pin later than the data port reaches the
data pin. The harness is safe only because of the ack_in → off-chip → data_in round trip.

Data source: the same as probe Bt. It is C-11c's `Formal.Net.FasmLink.S1..S4`, routed by
**nextpnr sha256 9c732bc6303458df** (all 9 patches `ok` in `fixture/link_arb_s*.toolchain`,
as stamped by `fasm2lean2/check.sh`). Nothing was re-routed. LUT windows are the
prjxray-db CLB SDF envelope: O6 [45, 124] ps, O5 [42, 157] ps. Every route window is C's
`pinDelay`, linked by `rfl`.

## Check command

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OnNetlistTimed2.lean

- **Result: clean**, no output, about 6 s.
- It needs `OnNetlistTimed.olean`, which was missing. I compiled it with
  `... ../slot.sh lean Formal/Cells/OnNetlistTimed.lean -o .lake/build/lib/lean/Formal/Cells/OnNetlistTimed.olean`.
  This wrote only a build artifact; no source changed.
- `formal/scan.py` is clean on the file. There is no `sorry`, `axiom` or `native_decide`.
  A plain grep for "admit" matches only Prelim's `K3.admits` identifier.
- `#print axioms`, run on a scratch copy:
  - the `holds_value`, rule H and `stage_token` theorems give `[propext, Classical.choice, Quot.sound]`;
  - `c2n_reset`, `c_reset_s*`, `cnode_loop_n`, `ctl_loop_s*`, `latchRel_from` and
    `capture_win_from` give `[propext, Quot.sound]`;
  - the function lemmas give `[propext]`;
  - `bmux_of_mux` and `rule_h_needs_ack_latency` give none.
- 69 theorems.

## Theorems (namespace `Formal.Cells.OnNetlistTimed2`)

### Generic

| name | statement |
|---|---|
| `latch_bit_net` | **Bridge, any latch bit.** Suppose LUT `i`, output `o` (O5 or O6), has a physical function on its physical pins equal to `bmux(pin ie, pin id, pin iq)`, and pin `iq` is routed from its own output. Then `Behaves` gives B's `Latch.holds_value`, with loop bound `dlhi + whi` (through probe Bt's `latch_holds_bits`). |
| `latch_rule_h_net` | **Rule H, windowed form of `Latch.link_latch_holds`.** The enable pin is routed from `se` with window [elo, ehi]. The data pin is routed from `sd` with window [rlo, rhi]. The hypotheses are: `H_NODE_LOW` (the node is low on [tc, T]); `H_SENDER_HOLD` (the sender keeps `v` until `tc + A`); `H_SETUP_PORT` (`s0 + rhi ≤ s`); `H_EN_OPEN`; and **`H_RULE_H : ehi ≤ A + rlo`**. The conclusion: the bit holds `v` on [s + dlhi, T + dllo]. |
| `c2n_reset` | B's `c2_reset` for `C(a, ~b)`. The release condition is `a = 0 ∨ b = 1`. |
| `bmux_of_mux` | A Kleene mux that is definite, read over windows that admit the pin values, fixes `bmux` (decided). |
| `latchRel_from` | **Behaves → `Bundling.LatchRel`, from `tstar = dlhi + M` on.** The LUT window and each route window add up to [dllo + lo, dlhi + hi]. |
| `capture_win_from` | `LinkTimed.capture_win`, with the latch relation needed only from `tstar` (`H_PU`). |
| `stage_token_bit` | `LinkTimed.stage_token` for one bit, using `capture_win_from`. The `DataPath` fields become named hypotheses with the same names. |
| `cnode_loop_n` | The physical C node is `LinkTimed.CtlEnv.H_CTL` (`Loop INIT_c2n`, no negation). |
| `stage_token_net` | `stage_token` on a physical latch bit: `Behaves` + `CtlEnv` + data hypotheses. |

### Per seed (s1..s4)

| name | statement |
|---|---|
| `l6_fn_s*`, `lo_fn_s*` | The physical INIT on the physical pins, with ties substituted, equals `bmux` on the right pins. This is checked for q1 (pair O6) and q2 (odd LUT6), by `decide`. |
| `l6_fn_wrong_fails_s1`, `lo_fn_swap_fails_s1` | Negative controls: q1 with q0's pins, and q2 with d and q swapped, are not the physical function. |
| `q1fb_s*`, `q2fb_s*`, `q12_pins` | Feedback `pinDelay` values (`rfl`) and the pin sources. |
| `latch_q1_s*`, `latch_q2_s*` | `holds_value` for q1 and q2. |
| `c_reset_s*` | `c2_reset` on the routed C node. |
| `rule_h_q{0,1,2}_s*` | Rule H for each bit, with the required `A` as hypothesis `H_A`. |
| `rule_h_needs_ack_latency` | With `A = 0`, rule H's inequality is false for all 12 seed×bit pairs (decided). |
| `ctl_loop_s*` | `CtlEnv.H_CTL` discharged on the bits. |
| `stage_token_q{0,1,2}_s*` | `LinkTimed.stage_token` on the bits, with concrete obligations. |

## Numbers (ps). Mean and range over the 4 seeds. Never a single route.

### (1) Latch loop bound `L = dlhi + feedback dw_hi`

These are the `H_EN_OPEN` bounds of `holds_value`.

| bit | s1 | s2 | s3 | s4 | mean | range | ×1.155 (mean) |
|---|---|---|---|---|---|---|---|
| q0 (O5, from Bt) | 1029 | 1029 | 601 | 604 | 815.75 | 601–1029 | 942.75 |
| q1 (pair O6, [42,157]) | 1132 | 447 | 1132 | 1132 | 960.75 | 447–1132 | 1110.25 |
| q2 (odd LUT6 O6, [45,124]) | 400 | 997 | 396 | 813 | 651.5 | 396–997 | 753 |

Feedback windows:
- q1: s1 [286,975], s2 [76,290], s3 [286,975], s4 [286,975].
- q2: s1 [71,276], s2 [228,873], s3 [71,272], s4 [214,689].

The output holds `v` on `[s + 157, T + 42]` for q1, and on `[s + 124, T + 45]` for q2.

### (2) `c2_reset`

The rst pin must stay at 1 for Dmax = 569 / 838 / 960 / 590 (mean 739.25, range 569–960). This
is the same loop bound as probe Bt's follow-and-hold. After that, the node reads 0 from
`t0 + 124` to `t2 + 45`, while req and ack never both reach the set value.

### (3) Rule H at the pins: required `A ≥ E − R`

- `E` is the enable-pin route maximum.
- `R` is the data-pin route minimum.
- The guarded column uses `ceil(GUARD_HI·E − GUARD_LO·R)`, with `GUARD_LO` = 0.772 and
  `GUARD_HI` = 1.155 from `cells/verify/skew.py`.

| bit | s1 | s2 | s3 | s4 | mean | range | guarded s1/s2/s3/s4 | guarded mean (range) |
|---|---|---|---|---|---|---|---|---|
| q0 | 233 (525−292) | 328 (690−362) | 223 (640−417) | 391 (696−305) | 293.75 | 223–391 | 381/518/418/569 | 471.5 (381–569) |
| q1 | 137 (525−388) | 213 (690−477) | 272 (640−368) | 384 (696−312) | 251.5 | 137–384 | 307/429/456/564 | 439 (307–564) |
| q2 | 678 (1066−388) | **929** (1172−243) | 510 (844−334) | 135 (521−386) | 563 | 135–929 | 932/**1167**/717/304 | 780 (304–1167) |

The worst bit per seed is 678 / 929 / 510 / 391 (guarded: 932 / 1167 / 717 / 569). The odd bit q2
is the worst on 3 of the 4 seeds, because its enable branch is the longest (up to 1172 on s2).

**Does it hold "as routed"?** There is no validated lower bound for `A`, so the honest answer
is "conditional on `A`".
- For information only, not used in Lean: nextpnr's single-corner SDF gives the
  `lnk.ctl.u.u/O6 → ack_in OBUF` route as 2038 / 1804 / 1979 / 1807. With `GUARD_LO` applied,
  that is 1573 / 1392 / 1527 / 1395. That clears every requirement, guarded ones included,
  even before the IOB and off-chip time.
- But nextpnr's numbers are not fast-min bounds. On the C feedback pins, `pinDelay` lo is
  about 0.42× nextpnr's figure (125 vs 295).
- Scaled the same way, a fast-min ack route would be about 760 ps. That is **below the s2 q2
  requirement (929) and the guarded s1 q2 (932) and s2 q2 (1167) requirements.** Those bits
  would then rely on the IOB and the off-chip sender for their margin.
- So **s2/q2 and s1/q2 are flagged**: they need a validated min of the ack_in output path
  (C/research), or a GLS/board measurement.

### (4) `stage_token` obligations on the bits (LinkTimed form)

The windows are the LUT window plus the route, e.g. enable `[dllo+elo, dlhi+ehi]`. The C node
has dlmin = 45 and dlmax = 124. The obligations are:
- pulse width: `E ≥ Xpw = 34 + ehi + fhi − elo`;
- setup: `Sdr + E ≥ Xsu + Lag`;
- rule H (`Erel ≥ Xh = 79 + ehi − dlo`). This is stricter than (3), because LinkTimed puts the
  LUT's full spread into each window independently;
- power-up: `cph(2k) ≥ Xpu`.

| bit | Xpw s1/s2/s3/s4 (mean, range) | Xsu (mean, range) | Xh (mean, range) | Xh guarded (mean, range) | Xpu (mean, range) |
|---|---|---|---|---|---|
| q0 | 1551/1690/1217/1237 (1423.75, 1217–1690) | 1931/2113/1885/1588 (1879.25, 1588–2113) | 427/522/417/585 (487.75, 417–585) | 639/775/675/826 (728.75) | 380/423/668/351 (455.5) |
| q1 | 1654/1108/1748/1765 (1568.75, 1108–1765) | 2363/1880/2259/2038 (2135, 1880–2363) | 331/407/466/578 (445.5, 331–578) | 565/687/713/821 (696.5) | 709/772/511/273 (566.25) |
| q2 | 1270/1953/1101/1296 (1405, 1101–1953) | 1470/1668/1280/2011 (1607.25, 1280–2011) | 836/1087/668/293 (721, 293–1087) | 1149/1384/934/521 (997) | 200/0/179/715 (273.5) |

For comparison, B's `H_ENV_LATENCY` from probe Bt needs only `E ≥ 524 / 793 / 915 / 545`. On
these bits, the latch pulse-width obligation (`E ≥` 1101–1953) is the binding constraint on
the environment's latency, not the C element's. The worst case is s2/q2 at 1953.

## What did not work / limits

1. **`A` is not in `pinDelay`.** C's tool reports LUT input pins only. The output route to the
   OBUF, the IOB delays and the off-chip sender are not modelled, so rule H is proved
   conditional on `H_A`. A real pipeline would need a two-stage routed design, where `A` and
   `R` are LUT-to-LUT and fully in `pinDelay`. That is the next fixture to ask C for.
2. **`Latch.link_latch_holds` is not instantiated verbatim.** Its `H_EN_FANOUT` needs the
   enable low for all `t ≥ tc + E`, which is false in any multi-token run because the node
   rises again. `latch_rule_h_net` is the windowed form: the same inequality (`E ≤ A + R`),
   with the enable low only up to `T`. It goes through `holds_value`, as
   `link_latch_holds` does. Suggest that B's statement take a window.
3. **`LinkTimed.DataPath` could not be built from `Behaves`.** `H_LATCH` (`Bundling.LatchRel`)
   is required at every `t`, including the power-up interval. There, `winK` clamps `t − s` at
   0, and `Behaves` says nothing. So `capture_win` and `stage_token` were re-proved with the
   relation required only from `tstar` (hypothesis `H_PU`). The proofs are copies of B's with
   one extra premise. Suggest that `LinkTimed` adopt a `tstar`.
4. **The per-seed `stage_token` takes `C : CtlEnv` as an argument.** Its `H_CTL` is the
   physical C node: `ctl_loop_s*` proves it from `Behaves`, with the routed numbers in the
   type. The environment fields of `CtlEnv` (request and ack shapes, causality) stay as
   hypotheses on the physical pin traces, as in Bt.
5. **The OUTMUX arc on O5 is still missing** (probe Bt limit 2). This affects q0 only. The
   q1 and q2 outputs use the direct O6 pin.
6. **Binary `Behaves`.** `latchRel_from` builds the Kleene window reading from Boolean traces,
   so B's X semantics are used only as a conservative reading, never fed X.
7. **One `dl` per LUT site** (Bt limit 6). q1 shares the pair site's O5 envelope [42, 157].
8. **The H_DW upper ends are unvalidated** (Bt limit 1). Every number above is conditional on
   C's `pinDelay` and the SDF envelope.

## Fidelity per primitive

- **Pair LUT6_2, O6 (q1):** C's `H_LUT` window [42, 157] (site envelope), using the PHYSICAL
  INIT on the PHYSICAL pins. The function is decided equal to `bmux`, with A6 tied to VCC.
  Glitches are admitted (the delay varies per tick). Mux-tree internals and inertial
  filtering are not modelled.
- **Odd LUT6 (q2):** the same, with window [45, 124]. The router re-ties unused pins (e.g. A4
  to VCC on s1 and s2); the physical INIT accounts for that, and the decided lemma covers it.
- **Feedback, enable and data routes:** window channels (`H_ROUTE`), with C's per-pin
  `pinDelay`. The enable fanout is a separate wire per latch pin, with its own window. That is
  what rule H is about.
- **C node:** as in Bt (`Loop`), now also in `INIT_c2n` form for `LinkTimed`.

## Effort to finish and what it buys

- **Closing rule H on real silicon numbers:** this needs a min-corner bound on the ack_in
  output path, or a two-stage routed fixture. C needs about 0.5 day for the fixture; the Lean
  side is mechanical, the same generator.
- **Kleene `Behaves` and the OUTMUX arc:** as in Bt, about 1 day.

**What it buys.** All three latch bits, the reset, and the stage's per-token theorem now hold
for the cells as the four real bitstreams wire them, with numbers for each seed. The spread
across seeds is large: q2's loop bound ranges 396–997 ps, its rule-H requirement 135–929 ps,
and the stage pulse-width obligation 1101–1953 ps. Any single route would misstate these
contracts by up to 2.5×.
