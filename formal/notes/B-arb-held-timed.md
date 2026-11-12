# B probe 7h: timed exclusion of the held bd_arbiter (RT1, RT2)

File: `formal/lean/Formal/Cells/ArbHeldTimed.lean`. It is core Lean and imports
only `Formal.Cells.Prelim`. It checks clean in about 9 s. There is no
`sorry`/`admit`/`axiom`/`native_decide`. `#print axioms` on `rt1_exclusion`,
`rt1_counter_minserver`, `rt2_exclusion_arcs`, `rt2_counter` and
`prj_arc_only` gives `propext, Classical.choice, Quot.sound`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbHeldTimed.lean

No shared definitions were added. Everything is local: `FS`/`FR`/`FG1`/`FG2`/`CE`,
`Dl`, `Sigs`, `Server`, `Run`, `Scn`, `int_ind` and `and_dec_false`. The small
INIT lemmas of 7e are re-proved here so this file does not depend on 7e's olean.

This probe builds on 7e (`B-arb-handover.md`, which found the untimed traces
`held_grant_overlap_untimed` and `held_ack_overlap_untimed`). It cites 7g
(`B-arb-a0fork.md`, `ArbA0Fork.lean`) for the A0 fork into ua2. Here that fork
is only a named hypothesis (`A0Fork`, 7g's `late ≤ early`), and it is not
re-derived.

## Audit correction (claude/audit REPORT rows 10, 24; findings AB2 #2; 2026-10-27)

The `prj` instance below reads the pairs 56/124 (O6), 55/152 (O5 I0/I1) and
52/150 (O5 I2) as rise/fall arcs. They are prjxray's FAST_MAX and SLOW_MAX of
ONE arc (`prjxray/utils/makesdf.py:63` writes
`(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`, each for both edges; prjxray has no
edge split). So `prj` mixes corners (FAST_MAX rises with SLOW_MAX falls;
`ArbCorners.prj_is_mix`), and its margins (292/164/276/220/332 ps, "112 ps
server = two LUT1 rise arcs" = 2 × FAST_MAX) are artefacts. The generic
theorems (every `Dl`, rise = fall included) are unaffected. Corrected values
(B-arb-corners.md §2):
- arc parts at a consistent corner: `ArbCorners.arcs_slowMax` /
  `arcs_fastMin` (RT1 248 / 90, pulse 150 / 42, g1 150 / 42, forkA 274 / 87,
  forkG 274 / 87, 7g fork 248 / 90; old mix 180, 52, 52, 108, 108, 180);
- arc-only margins with the server = two arcs at the same corner (248 / 90 ps):
  `ArbCorners.slow_arc_only` (RT1 496, pulse 398, g1 646, forkA 522, forkG 770,
  fork 248) and `ArbCorners.fast_arc_only` (180, 132, 222, 177, 267, 90);
- box (each arc independently in [FAST_MIN, SLOW_MAX]): `ArbCorners.box_7h`,
  `box_7h_worst`;
- with plausible routing every margin grows by about +0.1 to +0.2 ns at
  SLOW_MAX (arithmetic); corner sign changes: `ArbCorners.fast_neg_iff`.
Corrected values are inlined below; withdrawn ones are in brackets.

## Verdict

**Works.** Both relative-timing conditions are named in arc terms and proved
sufficient, for every server whose response time is at least `smin`. Each has
a counter-trace that shows it is needed.
- At zero routing, RT1, RT2 and 7g's fork condition hold at a consistent
  corner: the smallest margin is 90 ps at FAST_MIN (the 7g fork; 132 ps among
  RT1/RT2; server 90 ps) and 248 ps at SLOW_MAX (the fork; 398 among RT1/RT2) (`ArbCorners.fast_arc_only`, `slow_arc_only`). [Withdrawn:
  "with the prjxray arcs ... smallest margin 164 ps, with a 112 ps server",
  a corner mix.]
- With plausible routing, every margin is about 0.6 ns or more.

So the header's tier "during handover: structural WITH THE HOLD" is wrong as
worded. Exclusion during handover holds because of relative timing, with
margins of about a server round trip. It is not structural.

hw/arb_prot reads viol 0/96 and ovl 0/96. The model predicts exactly that
reading, but the reading cannot tell these margins apart from structural
exclusion.

Effort to finish: about 1 day. That covers:
- the mirror direction (client 2 releases);
- a run-existence witness;
- characterising the runt band.

What it buys the project:
- A proof-backed correction to the tier table in bd_arb.v and ARBITER.md.
- Five arc inequalities that a post-route checker (rule-style) could evaluate
  exactly on the routed SDF.

## Model

| element | model |
| --- | --- |
| time | `Int` ps |
| signal | `Int → Bool` |
| LUT outputs | 7e's rise-fast pure-delay OR channel: `o t = f(pins at rise arcs) ‖ f(pins at fall arcs)`. Each pin is also delayed by its route, which includes the site-pin delay. |
| `ustate` | real INIT 0xFFF0FFB2ACACACAC (O6 = q, O5 = R0) |
| `ugrant` | 0x0C0C0C0CA0A0A0A0 (O5 = g1, O6 = g2) |
| `ua1`/`ua2` | `bd_c2` 0x00E800E800E800E8 |
| server | the relation `Server smin R0 A0` |

All LUT functions are evaluated with `lutB`/`o5B`/`o6B`. The lemmas `FS_eq`,
`FR_eq`, `FG1_eq`, `FG2_eq`, `CE_eq` and `FR_indep` (R0's O5 ignores I4 = A0)
are proved by `decide` on the INITs.

**Server.** A0 may change at time t only if two things hold:
- R0 carried the new value at some instant `u ≤ t − smin`;
- A0 has stayed in its old phase since `u`.

This is the four-phase environment with minimum response time
**H_SERVER_MIN**. It allows any slower server. A delay-chain server driven by
a hazard-free R0 satisfies it.

**Scenario (`Scn`).**
- Client 1 holds: q = 1, A0 = 1 (since `ta`), A1 = 1, A2 = 0.
- Client 2 waits: r2 = 1.
- r1 falls at `t0`.
- The server's actual edges are `TA` (A0 falls) and `TA2` (A0 rises again).
  Both are free and constrained only through `Server`.
- Everything is stated up to a horizon `Hz`, before which no client moves again.
- **H_SETTLED**: A0's rise reached ustate's and ua1's views before r1 fell.

### Named hypotheses

| name | physical fact | test |
| --- | --- | --- |
| `Dl` routes `w..` | Route from the driving output to the pin, plus the site-pin delay of the physical pin (A1 slowest, A6 fastest; B-muxtree-fidelity) | routed SDF interconnect + prjxray `tile_type_CLBLL_*.json` |
| `Dl` arcs | Cell arcs: O6 flat; O5 per pin (I0, I1, I2) | prjxray / `bd_prims_sim.v`; GLS |
| `H_NONNEG` | causality | – |
| `H_RISE_LE_FALL` | rise ≤ fall per arc. [The pairs 56/124, 55/152, 52/150 once cited here are FAST_MAX/SLOW_MAX of one arc, makesdf.py:63, not rise/fall; prjxray gives rise = fall per corner, which satisfies this. The real asymmetry is the unmeasured `ArbCorners.RF`.] | board: odd-inversion LUT ring vs buffer ring |
| `H_LOOP_POS` | ustate, ua1 and ua2 feedback loops have positive delay | routed SDF |
| `smin` / H_SERVER_MIN | minimum R0-edge → A0-edge response of the server | routed SDF of the server chain; GLS |
| `Scn.H_SETTLED` | A0↑ reached ustate (+qf) and ua1 (+c1f) before r1↓ | holds whenever client 1's own A1↑ → r1↓ path is slower, which it is (3-LUT client chain) |
| `A0Fork` (7g's H_A0_FORK) | A0's fall reaches ua2 no later than g2's rise | 7g |

## Theorems

### Exact traces of one handover (client 1 → client 2)

These hold for every run, below the horizon `Hz`:

- **`TA_ge`**: the server relation forces
  `TA ≥ TR + smin`, where `TR = t0 + wr1s + Rf1`.
- **`TA2_ge`**: it also forces `TA2 ≥ RR + smin`, where
  `RR = QB + wfb + Rrq` and `QB = TA + wa0s + qf`.
- **`q_eq`**: `q t = [t < QB]`.
  - Below QB, q is held high by A0.
  - From QB on, q is reset, and it stays held at 0 after A0 rises again.
- **`R0_hi`/`R0_lo`**: R0 is high below TR and low on [TR, RR).
- **`g2_eq`**: `g2 t = [G2 ≤ t]`, where `G2 = QB + wq + g2r`.
- **`g1_eq`**: `g1 t = [t < G1]`, where
  `G1 = min(t0 + wr1g + g1f1, QB + wq + g1fq)`.

### RT1: grant exclusion

- **`overlap_exact`**: `g1.g2` is high at t iff `G2 ≤ t < G1`.
- **RT1**, in arc terms (the `RT1` definition): either

      wr1g + g1f1  ≤  wr1s + Rf1 + smin + wa0s + qf + wq + g2r

  or, structurally, `g1fq ≤ g2r` (g1 also falls through q no slower than g2
  rises). The first form says that r1↓ → g1↓ (through ugrant I0) must beat
  this chain:

  | step | arc term |
  | --- | --- |
  | r1↓ → R0↓ | `wr1s + Rf1` |
  | server | `smin` |
  | A0↓ reaches ustate I4 | `wa0s` |
  | q↓ | `qf` |
  | q reaches ugrant | `wq` |
  | g2↑ | `g2r` |

- **`rt1_exclusion`**: RT1 implies that g1 and g2 are never both high before
  the horizon, for every server allowed by H_SERVER_MIN.
- **`rt1_counter`**: the counter-trace. Suppose both of these hold:
  - `G2 < t0 + wr1g + g1f1`: the r1 path to g1 loses, for this run's `TA`;
  - `g2r < g1fq`.

  Then g1 and g2 are both high at the instant `G2`.
- **`rt1_counter_minserver`**: for a server that answers in exactly `smin`,
  `¬RT1` implies the overlap. So RT1 is necessary as well as sufficient.

### RT2: ack exclusion

Two instants:
- `T1 = max(G1 + wg1, TA + wa01) + c1f` is A1's fall.
- `T2 = TA2 + wa02 + c2r` is A2's earliest rise.

Run-form theorems:
- **`A1_low_after`**: under RT2a (`T1 + wfa1 ≤ TA2 + wa01`), A1 is low from T1
  to the horizon. RT2a says A1's fall has gone round its own feedback loop
  before A0's next rise reaches ua1. Otherwise the C-element re-latches,
  because maj(0, 1, 1) = 1.
- **`A2_low_before`**: under H_A0_FORK, A2 is low before T2.
- **`rt2_exclusion`**: RT2a, plus RT2b (`T1 ≤ T2`), plus H_A0_FORK, imply that
  A1 and A2 are never both high.

**`rt2_exclusion_arcs`** is the arc form, valid for every server. `RT2` is
these four inequalities, together with `A0Fork`:

| field | inequality | meaning |
| --- | --- | --- |
| `pulse` | `c1f + wfa1 ≤ wa0s + qf + wfb + Rrq + smin` | A0's low pulse at ua1 outlasts ua1's fall loop |
| `g1` | `wr1g + g1f1 + wg1 + c1f + wfa1 ≤ wr1s + Rf1 + 2·smin + wa0s + qf + wfb + Rrq + wa01` | g1's fall reaches ua1, and the loop closes, before A0 rises again |
| `forkA` | `wa01 + c1f ≤ wa0s + qf + wfb + Rrq + smin + wa02 + c2r` | A1 falls before A2 can rise (A0 fork skew between ua1 and ua2) |
| `forkG` | `wr1g + g1f1 + wg1 + c1f ≤ wr1s + Rf1 + 2·smin + wa0s + qf + wfb + Rrq + wa02 + c2r` | the same, along g1's path |

The counter-trace:
- **`A1_stuck`**: suppose `TA2 + wa01 ≤ max(G1 + wg1, TA + wa01 + c1f − c1r)`.
  That is, A0 rises again at ua1 before g1's fall arrives, or A0's low pulse
  at ua1 is no longer than ua1's fall−rise arc difference. Then A1 never falls.
- **`rt2_counter`**: if, in addition, g2 is at ua2 when A0 arrives there
  again, then A1 and A2 are both high at T2.

This is the timed form of 7e's `held_ack_overlap_untimed` and `held_a1_runt`.

**Gap.** Between RT2a and the `A1_stuck` condition is a band of about one ua1
loop delay (`c1r + wfa1`). Inside it, A1 dips and re-latches, or produces a
runt. The band is **not characterised** here, and it is the C-element runt
regime (`CElemTiming`).

### Corner-mixed instance (`prj`, `prj_RT1`, `prj_RT2`, `prj_arc_only`)

The arcs are (as "rise/fall"; really FAST_MAX/SLOW_MAX of one arc,
makesdf.py:63, see the audit correction):
- O6: 56/124;
- O5 I0/I1: 55/152;
- O5 I2: 52/150.

Everything in this subsection is the corner mix. Corrected:
`ArbCorners.arcs_slowMax`, `arcs_fastMin`, `slow_arc_only`, `fast_arc_only`,
`box_7h` (identity pin map, SLICEL); per routed seed, with each O5 arc from its
physical pin's `CLBLM_R.sdf` SLICEM line: `ArbCornersPin.parts_slowMax` /
`parts_fastMin`.

The R0 (ustate O5) and g1 (ugrant O5) arcs from I0 are both 152 here (that is
the SLOW_MAX of `CLBLL_L.sdf` SLICEL A1/A2 -> O5, not a fall arc), so they
cancel. That cancellation also assumes the identity pin map: on the four routed
seeds ustate's and ugrant's r1 pins differ and the two O5 arcs differ by -32 to
+2 ps (`ArbCornersPin.parts_slowMax`, B-arb-corners-pin.md). The conditions
reduce to:

| condition | reduced form |
| --- | --- |
| RT1 | `wr1g − wr1s ≤ 180 + smin + wa0s + wq` (180 = qf + g2r) |
| RT2 pulse | `wfa1 ≤ smin + 52 + wa0s + wfb` |
| RT2 g1 | `(wr1g − wr1s) + wg1 + wfa1 ≤ 2·smin + 52 + wa0s + wfb + wa01` |
| RT2 forkA | `wa01 − wa02 ≤ smin + 108 + wa0s + wfb` |
| RT2 forkG | `(wr1g − wr1s) + wg1 ≤ 2·smin + 108 + wa0s + wfb + wa02` |
| 7g fork | `wa02 ≤ wa0s + 180 + wq + wg2` |

**`prj_arc_only`** (proved): with every route 0 and a 112 ps server (2 ×
FAST_MAX), all of these hold. The margins below are corner-mixed (SLOW_MAX /
FAST_MIN in brackets, `ArbCorners.slow_arc_only` / `fast_arc_only`):

| condition | margin |
| --- | --- |
| RT1 | 292 ps [496 / 180] |
| pulse | 164 ps [398 / 132] |
| g1 | 276 ps [646 / 222] |
| forkA | 220 ps [522 / 177] |
| forkG | 332 ps [770 / 267] |

## Margin estimate with plausible routing (not a proof; arithmetic on the formulas)

**hw/arb_prot's server** is `bd_delay #(SLEN=2)`: two LUT1 hops from R0 to A0.
- Arcs alone give 2×124 = 248 ps at SLOW_MAX and 2×45 = 90 ps at FAST_MIN,
  for both edges. [Withdrawn: "2×56 = 112 ps (rise) and 2×124 = 248 ps
  (fall)", which read FAST_MAX/SLOW_MAX as rise/fall.]
- With the build's 434–945 ps per hop (cells/docs/LIBRARY.md), each server
  edge is about 1.0–2.1 ns. Take smin ≈ 980 ps, the minimum.

Other routing assumptions:
- Inter-LUT routes are 434–945 ps.
- Feedback routes (`wfb`, `wfa1`) may be intra-site and short: assume
  100–945 ps.
- Site-pin delays are A1 0.17–0.52 ns down to A6 ≈ 0. Pins map I_k → A_(k+1)
  with no pin permutation, so r1 and g1 land on A1 and A0 lands on A5. They
  are in the route terms; the skews below include them.

The worst-case sign of each skew gives (arc terms here are the corner-mixed
ones; at SLOW_MAX each margin grows by the arc change, about +0.1 to +0.2 ns,
e.g. RT2 pulse ≈ 0.72 ns; see B-arb-corners.md §2):

| condition | worst-case margin |
| --- | --- |
| RT1 | 180 + 980 + 434 + 434 − 511 (r1 skew) ≈ **1.5 ns** |
| RT2 pulse | 980 + 52 + 434 + 100 − 945 ≈ **0.62 ns** (the tightest, set by ua1's feedback route against ustate's) |
| RT2 g1 | −511 + 1960 + 52 + 434 + 100 + 434 − 945 − 945 ≈ **0.58 ns** |
| RT2 forkA | 980 + 108 + 434 + 100 − 511 ≈ **1.1 ns** |
| RT2 forkG | −511 + 1960 + 108 + 434 + 100 + 434 − 945 ≈ **1.6 ns** |

All of these are far above the 8.5% scatter, and above a `max(0.2·t, 200 ps)`
guard. To break any of them, a single feedback or A0 route would have to
exceed a whole server delay plus a hop.

**Consistency with hw/arb_prot (viol 0/96, ovl 0/96).** The timed model
predicts 0 for both.

That means the zeros are consistent, but they do not discriminate:
- They cannot tell "RT1 and RT2 hold by about 0.6–1.5 ns" from "exclusion is
  structural".
- They therefore do not support the header's "structural" wording.
- They do not specifically test the metastability tier either. A metastable q
  would still have to beat these margins to show up as A1.A2.

Two more points on the detectors:
- ovl is width-filtered (W = 2). An RT1 violation shorter than the filter
  would be invisible anyway.
- viol is unfiltered. A `rt2_counter`-type failure latches A1 high for a
  whole transaction, so viol would catch it.

As 7e noted, viol is not an exclusive signature of the unheld defect. With the
hold, it is also the signature of an RT2 failure.

## Fidelity per primitive

- **LUT function**: exact. The real INITs and pin maps are evaluated with
  `lutB`/`o5B`/`o6B`. ustate's O5 is proved independent of I4, so A0's delay
  to O5 is omitted.
- **LUT timing**: rise-fast pure-delay OR channel with per-pin O5 arcs and
  flat O6 arcs, as in 7e.
  - It is exact for isolated edges.
  - It is transport, with no inertial rejection.
  - No Kleene/X or mux-tree glitches are modelled. In this scenario every
    function-irrelevant pin edge is masked at the Boolean level, and the
    Kleene lemma (MuxTree) says the silicon tree does not glitch on those
    edges.
  - O6 per-pin arcs are assumed flat. The per-pin differences sit in the site
    pins, which are folded into the routes.
- **Routing**: a fixed pure delay per pin (route plus site pin). The edge
  direction is not distinguished on routes. Each route is a single number
  because every net makes at most one relevant edge in the window.
- **C-element (ua1/ua2) and state node (ustate)**: a LUT whose output feeds
  back to its own pin through a routed wire with positive delay
  (`H_LOOP_POS`).
- **Server**: a relation with minimum response time, not a gate model. The
  hw server (two LUT1s) is one instance of it.
- **Clients**: fixed input traces up to the horizon.
- **Metastability**: absent. q's evaluation is never racing in this scenario,
  because r2 is steadily high when the hold releases. Probe 7c/7e's runt is a
  different scenario.

## Not done

- **Mirror direction** (client 2 releases, q rises). This is not proved. The
  same method applies with different arcs:
  - RT1 becomes `wr2g + 124 ≤ wr2s + 152 + smin + wa0s + 56 + wq + 52`, a
    margin of 136 + smin + … .
  - RT2 pulse becomes `c2f + wfa2 ≤ wa0s + qr + wfb + 52 + smin`, a margin of
    smin − 16 + … . That is the tighter direction: 96 ps arc-only with a
    112 ps server. [Corner mix: at one corner the arc part is +150 (SLOW_MAX)
    / +42 (FAST_MIN), `ArbCorners.pulse2_zero_routing`.] (Since done: 7j,
    B-arb-held-timed2.md.)

  Done by hand from the formulas; about 2–3 h to prove, mostly duplication
  (or abstracting the polarity).
- **Run existence.** No proof that the relations plus `Scn` have a solution.
  They are consistent by inspection: the stylised infinite past with A0 low
  before `ta`, R0 high, q = A1 = 1 and A2 = 0 satisfies every gate equation.
  A closed-form witness would take about 2 h.
- **The runt band** between RT2a and `A1_stuck`, which is about one ua1 loop
  delay wide.
- **Free-running, multi-handover behaviour.** Only one handover up to a
  horizon is covered; repeated handovers are not chained.
- **Port to shard A's `Formal/Core` channels.**
