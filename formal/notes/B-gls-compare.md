# Probe Bg: the shard-B cell models against the research branch's board-fidelity GLS

Probe: PROGRAM.md says "Compare the model with the board-fidelity GLS being built on
claude/research. Where the two disagree, find out which is wrong." This note does that for
shard B's models (C-element, latch and link, arbiter). Shard A's `A-gls-compare.md` already
did the bare-LUT channel; this note builds on it and does not repeat it.

No Lean was written. Nothing in the repo was changed except this file.

## Sources and what was run

- **Formal side.** Every `formal/notes/B-*.md` (20 notes), plus `A-gls-compare.md`.
- **Research side.** Read-only with `git show origin/claude/research:…` at `7e90c4f`, without
  checking it out:
  - `research/PROGRAM.md` (the board-fidelity section);
  - `research/JOURNAL.md` (the rule J entries, 00:00 to 00:50, and F1/F2, 03:06 to 03:28);
  - `cells/gls/prims.v`, `gen.py`, `README.md`, `build.sh`;
  - `cells/gls/fid/README.md` and `xray_delay.py`;
  - `research/data/fid/f1_compare.txt`.
- **prjxray source**, to settle a disagreement (§1). This was a sparse, read-only clone of
  `f4pga/prjxray` at `c9f02d8` in
  `/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/gls/prjxray`.
  The files read were `utils/makesdf.py` and `fuzzers/007-timing/bel/runme.tcl`.
- **iverilog is NOT installed in this container** (`which iverilog` fails; none anywhere on
  disk). So no GLS and no `cells/sim` bench was run, and the 7e `tb_arb` prediction is
  untested. The oscillation-band prediction was instead checked against the iverilog results
  that A-gls-compare recorded (§3).
- **Python proxies** were run instead of iverilog. They are event models of the GLS LUT
  channel ("sample at fire", SAF). A-gls-compare fitted SAF to iverilog's specify path and
  matched 140 of 140 random traces. They are proxies, not GLS runs. Scripts and logs are in
  `/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/gls/`:
  - `saf_ua.py` (log `saf_ua_124_295.log`): the 7g ack C-element under A0-fork skew;
  - `saf_latch.py` (logs `saf_latch_124_295.log`, `saf_latch_124_60.log`): the 6c latch
    setup boundary;
  - `saf_latch_gate.py` (log `saf_latch_gate.log`): the same, comparing the gate and baked
    GLS builds.

  Each runs in under a second: `python3 -I <script> [arc] [wfb]`.

## 1. Headline: prjxray has no rise/fall split, so the rise/fall numbers in shard B are corner-mixing artefacts

Several shard-B instances, and the `cells/sim` models, read prjxray's cell arcs as
rise/fall:
- `cells/sim/bd_prims_sim.v` lines 12 and 60–69: `BD_T_RISE 56`, `BD_T_FALL 124`, and
  O5 55/152, 52/150.
- `B-arb-handover.md` (7e): the "rise-fast OR channel", `H_rise_le_fall`, `header_16ps`,
  `sim_overlap`.
- `B-arb-held-timed.md` (7h): `prj`, `prj_arc_only`.
- `B-arb-held-timed2.md` (7j): `prj_pulse2_tight` (the "wfa2 + 16" margin) and the runt band
  `68 < p`.
- `B-arb-a0fork.md` (7g): correction item 1, "client 2 is ustate fall + ugrant O6 rise =
  145–180 ps".
- `B-muxtree-fidelity.md`: "45/56 ps rise, 100/124 ps fall".
- Outside shard B: `A-gls-compare.md` §2 ("+68 ps stretch") and `cells/docs/ARBITER.md`
  ("the +68 ps stretch each O6 LUT adds to a positive pulse").

**This reading is wrong.** The research F1 entry (JOURNAL 03:08) says so, and I checked it
against prjxray's own source:
- `utils/makesdf.py` writes every cell arc as
  `(IOPATH in out ({FAST_MIN}::{FAST_MAX})({SLOW_MIN}::{SLOW_MAX}))`.
- `fuzzers/007-timing/bel/runme.tcl` dumps only the Vivado speed-model properties
  `DELAY FAST_MAX FAST_MIN SLOW_MAX SLOW_MIN`. No rise or fall property exists.

SDF syntax reads two groups as (rise)(fall). nextpnr's `parse_sdf.py` did, and the
`cells/sim` arcs inherited that.

So `(0.045::0.056)(0.100::0.124)` means "45–56 ps at the fast corner, 100–124 ps at the slow
corner, either edge". `f1_compare.txt` agrees: the xray A→O IOPATH is exactly nextpnr's 124 ps
at SLOW_MAX, and 0.363× that (45 ps) at FAST_MIN. The research GLS writes rise = fall
(`gen.py` emits `(d:d:d) (d:d:d)`; `xray_delay.py` says "rise and fall are written equal").

**Consequences for shard B.** The theorems are parametric in the arcs and stay true. Only the
prjxray *instances* change. A "rise 56 / fall 124" instance puts the fast corner and the slow
corner in one run on one die. A consistent corner cannot produce it, and within-die scatter
(8.5% median) does not come close to 2.2×.

| instance | as stated | consistent corner (all arcs equal d, w ≥ 0) | full box ([fast-min, slow-max] per arc, independent) |
|---|---|---|---|
| 7e `header_16ps` / `sim_overlap`: bare-cell r2→r1 handover overlap | 16 ps at w = 0; `max(0, 16 − R)` in `cells/sim` | `max(0, d − (d + w + d)) = 0`: **never**, for every w ≥ 0 | `124 − 45 − 42 = 37` ps at w = 0 |
| 7e skew caps (72 / 94 ps for any σ) | 72 / 94 | `max(0, g2f − g1r_q) = 0` (and 0 the other way) | 124 − 42 = 82 ps and 150 − 45 = 105 ps |
| 7j tightest margin `wfa2 + 16 ≤ smin + wa0s + wfb` | 96 ps at zero routing | the 16 is `c2f − qr − O5_I2 = 124 − 56 − 52`; with equal arcs it is `d − d − d = −d`, so the margin **grows** by d + 16 | 124 − 45 − 42 = 37, i.e. `wfa2 + 37 ≤ …`, still positive for smin ≥ 37 |
| 7j runt band `c1f − c1r < p`, i.e. 68 < p | A1_stuck for p ≤ 68 | `c1f = c1r`: the stuck region is empty and the band is `0 < p < c1f + wfa1` | — |
| 7g item 1 ("rule J's flat 124 is biased unsafe by 68–161 ps") | — | wrong as stated: at SLOW_MAX, 124 is the right per-arc number. The real issue is corner **ratio** (below) | the box form `box_safe_iff` is still the right theorem |
| ARBITER.md "+68 ps stretch", W = 1 passband (≤ 80 ps blocked, 160 ps passed) | measured on `cells/sim` | no stretch. The SAF threshold is the arc at the chosen corner (124 or 45) | — |

**Which side is right.**
- On the data, the research GLS is right: there is no rise/fall split in prjxray or in the
  Vivado model it was fuzzed from.
- Silicon certainly has *some* rise/fall asymmetry. Nothing in the repo measures it, so any
  value is a hypothesis.

The formal side should change as follows:
- replace `H_rise_le_fall` with prjxray-sourced data by two instances, a consistent corner
  (rise = fall = d) and the full box;
- name rise/fall asymmetry as an unmeasured hypothesis `H_RF_ASYM` (it could be measured with
  a ring that has an odd number of inversions, compared against one built of buffers).

ARBITER.md's conclusion ("predicts that no copy should ever fire") gets **stronger**: the
consistent-corner cap is 0. The 8% stays unexplained.

**A real issue that the misreading hid: corners scale cells and wires differently.**
`f1_compare.txt` (gcd) gives these FAST_MIN/SLOW_MAX ratios:
- LUT IOPATH: 0.363;
- interconnect: median 0.55 (p10 0.37, p90 0.82).

Margins of the form "two arcs plus wires on the early side, one wire on the late side" can
therefore change sign between corners, even with both sides at one corner. Rule J (7g) and
RT1/RT2 (7h, 7j) are such margins.

Worked example for 7g: early = 2 arcs (248 ps) + 885 ps of wire, late = 1000 ps of wire.
- At SLOW_MAX the margin is +133 ps.
- At FAST_MIN it is 0.363·248 + 0.55·885 − 0.55·1000 ≈ +27 ps.

Rule J's flat 0.772 / 1.155 guard does not track this. `client2_iff` evaluated per corner
(a consistent corner plus local scatter) is the right check. That makes it **prediction P2b**
below.

## 2. Second finding: the GLS and the post-route rules share a blind spot of one LUT arc

The GLS LUT is SAF (A-gls-compare §1). SAF, like inertial delay, swallows an *isolated* pulse
of `f` narrower than the arc. Shard B's positive theorems use transport or window channels,
which pass every pulse. On a feedback cell this decides when a late input "counts". The two
cases below were computed with the SAF proxy, with arc 124 ps and a same-slice feedback hop
of 295 ps (the patched-nextpnr figure quoted in 7g).

**(a) bd_latch setup (6c `counter_rule_I`).** Here d leads the enable fall at the pins by w
(`saf_latch.py`).

| w (ps) | transport (6c's model) | GLS, baked build (SAF LUT, transport wire) | GLS, gate build (SAF LUT, SAF wire) |
|---|---|---|---|
| ≤ 124 | rings | **OLD value, clean** | OLD value |
| 125–294 | rings | rings for ever (period 419) | OLD value |
| 295–418 | rings | **new value** | new value |
| ≥ 419 | new value | new value | new value |

Three different thresholds:
- 6c's H_SETUP needs `w ≥ wfb + arc = 419`.
- The baked GLS latches correctly from `w ≥ wfb = 295`. With `wfb = 60 < arc` it needs
  `w ≥ 125`, i.e. roughly `max(wfb, arc + 1)`.
- Rule I without its guard is `w ≥ wfb`, which is **exactly the GLS threshold** when
  wfb ≥ arc.

So a GLS pass cannot confirm or refute 6c's missing I2-arc term: the GLS has the same hole.
The guard (≥ 200 ps) hides it in both.

Note also that the gate build and the baked build disagree for 125 ≤ w ≤ 294 (OLD value
vs. ringing). That is the same gate-versus-baked wire issue that A-gls-compare found for
isolated pulses, now in a closed loop.

**(b) The ack C-element under A0-fork skew (7g, 7i).** δ = late − early at ua_k's pins
(`saf_ua.py`).

| δ (ps) | transport (7g's model) | GLS (SAF), baked | inertial (5d) |
|---|---|---|---|
| ≤ 0 | no ack | no ack | no ack |
| 1–124 | **rings for ever** (period D = 419) | **no ack** | no ack (rings at exactly 124: tie convention) |
| 125–294 | rings | rings | rings |
| 295–418 | rings | latched | latched from 296 |
| ≥ 419 | latched | latched | latched |

7g's `no_early_ack_iff` (safe iff δ ≤ 0) is rule J's raw sign. The GLS is safe up to
δ ≤ arc of ua_k's g pin: it is **optimistic by one arc**.

There is a small correction to 7g's prose as well. Below one loop, transport gives a
perpetual ring, not "a runt": g stays high and A0 low, so ua_k is the OR loop of 5b/5d,
whose `runt_oscillatesR` applies.

**Which is right?** Neither exactly.
- In silicon, a hole of width h < arc in a LUT's mux-tree output is attenuated, not deleted at
  a sharp threshold. A-gls-compare's involution (ExpLog) numbers cancel only below about
  τ ln 2 ≈ 64 ps for δ∞ = 124, and pass a shrunken runt above that.
- So the true safe threshold lies strictly between 0 (transport) and one arc (SAF).
- No board datum pins it down.

CLAUDE.md says: when ambiguous, take the longer number. So **the formal (transport) conditions
stand as the gates**: 7g's δ ≤ 0 and 6c's H_SETUP. **GLS passes inside the one-arc window
must not be used as evidence** that rule I's missing term or a near-zero rule J margin is
safe.

The research journal's rule J validation has no point inside the window. Its points are
+344, −607 and −1090 raw, and they agree with both models. The window is therefore untested
on both sides.

## 3. Confirmations (the formal predictions already tested)

- **7g / 7i, A0-fork early ack: confirmed by the research GLS** (JOURNAL 00:00–00:50).
  - In gcd_hw `ucontrol_merge2`, with ua2's arcs ×2.5, "ua2 = C(g2, A0) rises at 662.7
    because A0's fall has not reached it yet". The control token is lost and the design
    deadlocks.
  - Rule J's raw sign, which is 7g's exact condition `late ≤ early`, predicted the GLS
    outcome in 4 of 4 cases.
  - 7i's witness, a lag of 3 gate delays on ua2's A0 branch alone giving a latched early ack,
    is the discrete shadow of this run. The GLS failure needed δ well beyond one ua2 arc,
    which is consistent with §2(b).
- **7g, site-pin delays missing from nextpnr's SDF: confirmed** (F1, JOURNAL 03:08).
  - `xray_delay.py` charges the prjxray Inpin delay that nextpnr omits: on average +338 ps,
    with LUT A1/A2 about 0.51 ns and A6 about 0.005 ns at SLOW_MAX. These are the same
    figures as B-muxtree's table.
  - The xray SDF puts them in each sink's INTERCONNECT. The baked GLS therefore applies them
    as transport delay on the physical pin, after gen.py's `X_ORIG_PORT` permutation, which is
    exactly 7g's per-pin model.
  - Consequence: rule J run on the xray SDF *is* 7g's proposed rule J′, without hand
    arithmetic. The "−25 ps site pip" term also disappears, since F1 drops nextpnr's 25 ps
    site pips.
- **5d, inertial loop band `[ρ, D − ρ]`, empty when 2ρ > D: confirmed on the GLS primitives.**
  - A-gls-compare ran `bd_c2` with a, b moving 01→10 at skew s (a set runt of width s)
    through the research `SLICE_LUTX` (iverilog, results recorded in its §3):
    - with flat 124 ps and direct feedback (D = 124, so 2ρ > D): no ring at any s, and a
      sharp flip at s = 124;
    - with a 300 ps transport ICBUF on the feedback (D = 424): **a perpetual ring for exactly
      124 ≤ s ≤ 300 = [ρ, D − ρ]**, holding below and latching above.
  - 5d's `inertial_lost`, `inertial_circulates` and `inertial_latches` predict both
    configurations exactly, including the tie at s = ρ and s = D − ρ.
  - The reason: SAF equals `InertialRD` on isolated pulses, and the circulating train has
    every pulse and gap ≥ ρ (`train_noShort`).
  - The SAF proxy reproduces the band for ua_k with wfb = 295 (125–294, ±1 ps from the
    pulse-end convention).
  - Which is right: neither, for silicon. 5d §3 (involution) proves that silicon-like channels
    have isolated critical widths with unbounded resolution time, not a whole interval of
    eternal rings, and not a sharp threshold.
- **LUT function and X: agree exactly.** This is A-gls-compare §4 (43,767 of 43,767 vectors),
  together with MuxTree's `lut6_gls_order`: the GLS's `?:` tree, with A1 at the output mux,
  computes `lutK`.
- **SAF lies inside 7f's gate model (argued, not proved in Lean).**
  - 7f's GMW gate either holds or takes `lutB` of what its pins see. An SAF update copies
    `f(now)`, so it is such a gate.
  - SAF satisfies H_GATE_BOUND with D = the arc: the last change of `f` fires one arc later
    and samples the settled value.
  - ICBUF (transport) satisfies H_WIRE_CAUSAL and H_WIRE_BOUND.
  - Hence 5a, 7b, 7f and 7i's ternary soundness theorems cover every run of both GLS builds.
    Every definite ternary value is a hard oracle for the GLS.
  - The converse fails. SAF is **not** inside 6c's `Gate` window relation with exact delays.
    `f` changing at 0, 10 and 120 gives output 1 at t = 140, while the window reads `f(16) = 0`.
    So 6c's and 6d's timing theorems do not cover GLS runs whose data cones glitch.

## 4. Per-primitive table

| primitive | formal model (shard B) | GLS model (claude/research, 7e90c4f) | board evidence | more faithful, and why |
|---|---|---|---|---|
| **LUT function** | the real INIT via `lutB`/`o5B`/`o6B` with RTL pin maps (every B probe). Assumes the RTL INIT reaches the bits | zero-time `?:` mux tree. INIT physically addressed with nextpnr's permutation pre-applied (gen.py). In `fid/`, every LUT function is decoded **from the bitstream** (fasm2net; 10136 of 10136 equal on BQ#3) | the August lut-pinmap bug (a deterministic bitstream defect). An injected re-run gives FASM-GLS 0/16 while the JSON-GLS stays 16/16 | **fid GLS.** It sees the bits. The formal model should take INITs from the FASM (C-11b) and not from RTL |
| **LUT X semantics** | `lutK` = per-2:1-mux Kleene (H_KLEENE_LUT, reduced to one mux by MuxTree) | Verilog `?:` with an X select merges bitwise, which is exactly `K3.mux` (43,767 of 43,767) | none. B-muxtree grades the hypothesis B overall and **low** for "mid-rail select while equal data legs rise" | **equal, and neither is evidence for the other**: both are Kleene by construction. Weak spot: R0 = r1·q + r2·¬q stays 1 under a metastable q (7b, 7i `arb_tie_acked`) exactly while r1 and r2 rise, which is B-muxtree's low-fidelity case. Only the board (B-muxtree experiment 2) or SPICE can test it |
| **LUT per-pin timing, incl. site pins A1..A6** | 7g: site-pin pure delay per physical pin (prjxray table) plus one output arc. 7e/7h/7j: flat O6 arcs, per-pin O5 arcs, with rise/fall (§1: a misreading). 5b/5d/6c/6d: lumped LUT delay, no per-pin spread | nextpnr SDF: flat 124 ps, **no site-pin delay**. xray SDF: prjxray IOPATH (O6 uniform, O5 per pin), site-pin delay added to each sink's INTERCONNECT, one column (FAST_MIN, SLOW_MIN or SLOW_MAX) for the whole design, rise = fall | ARBITER.md's A5 lead (q on A5: 2/107 fire, else 13/85). Board ring periods: all within [fast min, slow max] at about 0.35–0.41 of the band (F1). No direct per-pin datum | **xray GLS = 7g's model** (agree). Both beat nextpnr's SDF by up to about 0.5 ns per pin. The formal rise/fall instances must be redone (§1). Neither models where the edge enters the mux tree (A1 at the SRAM end on silicon, A1 at the output in prims.v), which matters only for multi-input hazards |
| **LUT delay channel** | transport/window in all positive B theorems (5b, 6c, 6d, 7e, 7g, 7h, 7j). Inertial as a counter-model (5d, 7a). Involution (5d §3) | **SAF** (A-gls-compare): identical to inertial on isolated pulses, and early-propagating on bursts | none for LUTs | **neither for silicon** (involution is the faithful binary model). For margins: formal transport is conservative by one arc and the GLS optimistic by one arc (§2). Take the formal number as the gate |
| **Feedback wires** (C-element, latch, ustate q) | positive delay, H_LOOP_POS (all), intervals `[dwmin, dwmax]` (5b, 5d, 6c, 6d), fixed (7g, 7h). 5b/6d: `H_ENV_LATENCY: E ≥ dwmax + (dlmax − dlmin)`, which **no rule checks** | ICBUF: **transport** in the baked build, **SAF** in the gate build. nextpnr: 295 ps same-slice hop. xray: an Elmore value | none per wire. Ring periods constrain wires in aggregate only | the **baked** GLS matches the formal wire. The gate build changes loop behaviour (§2a: OLD value instead of ringing for 125–294 ps), so loop results are build-dependent. Use the baked build for any loop question |
| **Routing pips and forks** | a pure-delay interval per sink. 7g: shared prefix `c` plus independent branches; **`c` cancels exactly** (proved) | per-sink lumped delay. nextpnr: one number per pip. xray: Elmore RC tree with fanout loading, buffered vs pass-transistor pips from prjxray. Scatter `arc` mode draws an independent factor per sink; `wire` mode uses the mean factor of the pips on each sink's path | ring set (F1: slope 0.938, the +988 ps offset partly reproduced) | **xray GLS for numbers.** For forks, 7g's theorem says arc-mode scatter overstates branch divergence (the sigma-25% deadlock came from it, JOURNAL 00:50). `wire` mode is the physically consistent one. Prediction P8 checks O5/O6 bels on one site pin |
| **Corners** | 7g: independent box `[lo, hi]` (`box_safe_iff`). 6c/6d: intervals. The prjxray instances mixed corners via the rise/fall reading | one SDF column for the whole design (correlated), then ×0.9/×1.1 or Gaussian scatter | the board sits at about 0.35–0.41 of [fast min, slow max] on long rings (F1) | **GLS** (corner-correlated plus local scatter). This is PROGRAM's "shared corner plus local scatter". The formal side should add a correlated-corner instance (§1, P2b) |
| **Metastability / near-coincidence** | Kleene X, sound for GMW, so it covers the GLS (5a, 7b, 7f, 7i). Binary witnesses that never settle (7a, 7i `arb_tie_exact`, `cel_x_exact`). Inertial band (5d). Involution critical width (5d §3). ODE (7c/7d, outside the digital north star) | PROGRAM says "resolve in zero time". **Not quite:** an SAF loop with a transport feedback wire ≥ arc rings for ever for set-runt widths in [ρ, D − ρ] (§3), and decides sharply otherwise. F3 (random resolution / X) has not landed | ARBITER.md: 15/192 copies fire with no structural explanation; MTBF rigs: zero failures (bounds only) | **formal Kleene X for proofs** (sound for every GLS run). **Involution for mechanism.** The GLS band is an artefact. Recommendation for F3: inject X on q for a bounded random time. GLS `?:` is Kleene, so 7b/7i's ternary theorems then give exact expected values (P6) |

## 5. Predictions the GLS or the board can test

Status key:
- **C**: confirmed by existing data;
- **O**: open, with a ready test;
- **U**: untestable here (no iverilog).

| # | prediction (formal source) | how to test | status |
|---|---|---|---|
| P1 | **7g / 7i:** with H_A0_FORK violated, ua_k latches an early ack, and rule J's raw sign is the exact condition | GLS_SCALE_INST on ua2 (journal) | **C** (4/4) |
| P1b | **this probe:** the GLS hides 0 < δ ≤ arc(ua_k). In the baked build, A2 rings with period `arc + wfb` for arc < δ < wfb and latches beyond | a delay on the single ICBUF from A0 into ua2 (needs a per-ICBUF scale; GLS_SCALE_INST scales every arc into the instance). Step δ through 0, 60, 124, 125, 200, 295, 420 | **O** |
| P2 | **7g:** nextpnr's SDF lacks per-pin site delays (up to about 0.5 ns) | F1 | **C** |
| P2b | **7g with §1:** rule J's sign can flip between SLOW_MAX and FAST_MIN on routes whose margin is carried by arcs. Cells scale 0.36 and wires 0.55 | run `arb_fork.py` on the xray SDF at `GLS_SDF_FIELD=min` and `max` over the 168 survey routes. Report the rows whose raw sign differs | **O** |
| P3 | **7e:** in `cells/sim`, `tb_arb`'s bare-cell overlap is `max(0, 16 − R)` ps: 8 ps at R = 8, 0 at R ≥ 16 | `BD_ROUTE_PS=8 cells/run_sim.sh` (tb_arb). Caveats: (i) tb_arb counts **events**, not ps, so record `$realtime` on entry and exit; (ii) at R = 16 the overlap has zero length, but same-timestep scheduling may still count 1 instant; (iii) the 16 ps is an artefact of `cells/sim` (§1). In the research GLS with equal arcs, the prediction is **0 at every R ≥ 0** | **U** |
| P4 | **5d:** an inertial/SAF C-element loop rings for ever exactly for runt widths in `[ρ, D − ρ]`, empty when the feedback wire < arc | A-gls-compare's `tb_c2` | **C** (124–300 for D = 424; none for D = 124) |
| P4b | **5d + this probe:** a routed bd_c2 with nextpnr's 295 ps same-slice feedback rings in the baked GLS for set runts of 125–294 ps, and does **not** ring in the gate build | `tb_c2`-style bench on `prims.v` with ICBUF feedback, `-DGLS_TRANSPORT_IC` on and off | **O** |
| P5 | **6c:** rule I omits the I2 (feedback-pin) arc. H_SETUP needs `w ≥ wfb + arc` | **The GLS cannot arbitrate this:** its own threshold is `w ≥ wfb` (§2a), the same as unguarded rule I. Board, or an involution-channel GLS, only | **O** (board) |
| P5b | **this probe:** a latch bit whose data leads the enable fall by w ≤ arc keeps its OLD value silently in both GLS builds. For arc < w < wfb, the baked build rings for ever (period `arc + wfb`) and the gate build keeps the old value | a GLS_SCALE_INST negative control on one latch's D ICBUF | **O** |
| P6 | **7i `arb_runt_held`:** with A0 = 1 on both branches, q, g2, A1 and A2 never move, whatever r1 and r2 do, including near-ties at 1 ps | a GLS bench on prims.v. SAF is a GMW gate, so this must hold in **every** GLS run, and a violation is a GLS or proof bug | **O** (cheap regression) |
| P6b | **7i `arb_tie_acked`:** with q forced to X during a tie (F3's metastability injection), R0 stays 1, and A1 = A2 = 0 until A0 rises | force `q` = 1'bx in GLS | **O** |
| P7 | **5b / 6d `H_ENV_LATENCY`:** a C-element whose own feedback wire exceeds its environment's ack-to-input latency fails, and no rule checks it | GLS_SCALE_INST on one C-element's feedback ICBUF until dwmax > E | **O** |
| P8 | **7a `exclusion_zero_skew`:** grant overlap needs O5/O6 skew. O5 and O6 of one LUT6_2 read the **same** site pin, so xray must give both bels' sinks the same INTERCONNECT | grep the xray SDF for the A5LUT/A6LUT sink pairs of one site pin. Arc-mode scatter breaks this, so prefer `GLS_SCATTER_MODE=wire` | **O** |
| P9 | **ARBITER.md with §1:** with no rise/fall stretch, the structural handover overlap cap at a consistent corner is 0 | follows from 7e's theorems. Board: the q-on-A5 build ARBITER.md proposes | the 8% stays unexplained |
| P10 | **5d §3 (involution):** a C-element runt at the critical width circulates for an unbounded time. Silicon has no sharp threshold | board: sweep a/b skew on a `bd_c2` with a delay-line vernier and count late resolutions vs skew. A peak at one skew (not a plateau) refutes the inertial/SAF band | **O** (board) |

## 6. What did not work or was not done

- No iverilog, so there is no GLS or `cells/sim` run (P3 and P4b are untested). I did **not**
  install it: the brief's rule was "if not, say so". `apt-get` is available, if a later probe
  may install it.
- The Python SAF proxies are not iverilog. They rely on A-gls-compare's 140/140 fit, which
  used flat or (rise, fall) arcs on one LUT, not closed loops. P1b, P4b and P5b should be
  rerun on the real `prims.v` before anyone relies on them.
- No routed JSON, SDF or toolchain is on disk, so none of the route-dependent numbers (pins,
  per-hop delays, P2b) could be computed.
- No Lean. The suggested lemmas follow.
  - (a) A parametric consistent-corner instance for 7e/7h/7j replacing `H_rise_le_fall`:
    about 2 h, a re-instantiation.
  - (b) A `Saf` channel on Core and the statement "SAF is a GMW, Bounded gate", which would
    make §3's argument a theorem: about half a day.
  - (c) The latch and C-element thresholds of §2 as theorems on SAF loops, i.e. 5d's
    `inLoop` with SAF in place of `InertialRD`: about 1 day.

## Verdict

**Works.**

What the probe found:
1. **A real error on the formal side.** prjxray's two arc groups are fast/slow corners, not
   rise/fall. The shard-B rise/fall instances (7e's 16 ps, 7h/7j's margins and runt band,
   7g's arc correction), `cells/sim`, and ARBITER.md's "+68 ps" are corner-mixing artefacts.
   The theorems survive; the numbers change.
2. **A systematic one-arc disagreement on feedback cells.** The GLS's SAF LUT accepts a late
   input one arc earlier than the formal transport model. It matches rule I and rule J
   exactly where those rules are weakest. Neither side is silicon. The formal, longer number
   should gate, and GLS passes inside that window are not evidence.
3. **Confirmed predictions:** the A0-fork early ack (7g/7i), the missing site-pin delays (7g),
   and the 5d inertial oscillation band (via A's recorded GLS-primitive runs).
4. **Exact agreement** on LUT function and X.
5. **A GLS regression check:** every ternary result from 5a/7b/7f/7i is a hard check on every
   GLS run.

Effort to finish:
- about ½ day with iverilog to run P1b, P4b, P5b, P6 and P8 on the real `prims.v`;
- about ½ day for the research owner to run P2b;
- about 1–1.5 days of Lean, items (a)–(c).

What it buys: it corrects which prjxray numbers the formal instances may use. It also tells
the research branch which GLS passes it may treat as ground truth: not any bundling or loop
margin within one LUT arc of zero.
