# B probe 7j: held bd_arbiter, mirror direction, non-vacuity, runt band

File: `formal/lean/Formal/Cells/ArbHeldTimed2.lean` (684 lines). It is core
Lean and imports only `Formal.Cells.ArbHeldTimed` (7h, read-only), which in
turn imports `Formal.Cells.Prelim`. It checks clean in about 10 s. It contains
no `sorry`, `admit`, `axiom` or `native_decide`.

`#print axioms` was run on these theorems:
- `rt1_exclusion2`
- `rt1_counter2_minserver`
- `rt2_exclusion2_arcs`
- `rt2_counter2`
- `prj_arc_only2`
- `nonvacuous`
- `A1_band`
- `A1_band_overlap_matched`

Each one gives `propext, Classical.choice, Quot.sound`. The `#print` lines were
removed afterwards.

Check commands. The first is needed only if 7h's olean is missing; it was
missing, so it was built once for this probe:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbHeldTimed.lean -o .lake/build/lib/lean/Formal/Cells/ArbHeldTimed.olean
    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbHeldTimed2.lean

No shared definitions were added. Everything new is local to the file:
- the scenario `Scn2`;
- the instants `TRb`/`QBb`/`RRb`/`G1b`/`G2b`/`T1b`/`T2b`;
- the conditions `RT1b`/`RT2b`/`A0Fork2`;
- the witness `D0`/`W1`/`W2`;
- the INIT lemmas `FS_bool`, `FS_set`, `FR_r1`, `FG1_r1`, proved by `decide` on
  the real INIT.

`Run`, `Dl`, `Server`, `Scn` and `prj` are 7h's, unchanged.

## Audit correction (claude/audit REPORT row 24, OVERSTATED; findings AB2 #1; 2026-10-27)

7h's `prj`, and so `D0` and every number of this note quoted "with the prjxray
arcs", reads the pairs 56/124 (O6), 55/152 (O5 I0/I1) and 52/150 (O5 I2) as
rise/fall. They are prjxray's FAST_MAX and SLOW_MAX of ONE arc
(`prjxray/utils/makesdf.py:63` writes `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`,
each for both edges). `D0` therefore mixes corners (`ArbCorners.prj_is_mix`):
the 16 ps pulse2 threshold (= 124 − 56 − 52), the 96 ps "tightest margin", the
"112 ps server = two LUT1 rise arcs" (= 2 × FAST_MAX) and the band edge 68 ps
(= 124 − 56) are artefacts. The generic theorems and the non-vacuity itself
remain valid mathematics. Corrected (B-arb-corners.md §2, §4):
- `ArbCorners.pulse2_zero_routing`: at zero routing pulse2 holds iff
  `smin ≥ d6 − o5q`, i.e. for every `smin ≥ 0` at any consistent corner. The
  pulse condition is `wfa2 ≤ smin + 150 + wa0s + wfb` at SLOW_MAX and `+42` at
  FAST_MIN (box: `wfa2 + 37 ≤ smin + wa0s + wfb`, `ArbCorners.box_7j`).
- Arc-only margins, server = two arcs at the same corner (248 / 90 ps):
  `ArbCorners.slow_arc_only` (RT1b 550, pulse2 398, g2 674, forkA2 522,
  forkG2 798, fork2 274) and `ArbCorners.fast_arc_only` (176, 132, 221, 177,
  266, 87).
- Non-vacuity at consistent corners: `ArbCorners.nonvacuous_corners` (`Dslow`,
  `Dfast`, runs `W1s/W2s/W1f/W2f`), replacing `nonvacuous`'s `D0`.
- Runt band: `ArbCorners.stuck_pulse_vacuous`, `A1_band_corner` (band
  `0 < p < c1f + wfa1`; `δ < p` under the unmeasured asymmetry
  `ArbCorners.RF`, `A1_band_asym`).
Corrected values are inlined below; withdrawn ones are in brackets.

## Verdict

**Works.** All three items are done. Item 3 is done for the first excursion
and the resulting overlap; the echo train afterwards is not proved.

### 1. Mirror direction (client 2 releases, q rises)

The exclusion theorems and counter-traces are proved. Their structure matches
7h's.

[Withdrawn, corner mix:] "The tightest margin anywhere in the held arbiter is
this direction's RT2 pulse condition. With the prjxray arcs it reads
`wfa2 + 16 ≤ smin + wa0s + wfb`: 96 ps at zero routing with a 112 ps server;
`prj_pulse2_tight`: holds iff `smin ≥ 16`. q rises on the fast O6 arc (56)
instead of falling on the slow one (124), making A0's low pulse 68 ps
shorter." The theorems are correct for `prj`, but 56 and 124 are FAST_MAX and
SLOW_MAX of the same O6 arc, not a rise and a fall. At one consistent corner
the condition reads `wfa2 ≤ smin + 150 + wa0s + wfb` (SLOW_MAX) or `+ 42`
(FAST_MIN), holds for every `smin ≥ 0` at zero routing
(`ArbCorners.pulse2_zero_routing`), and the two directions' pulse conditions have
the same arc part; there is no 16 ps threshold.

### 2. Non-vacuity

`nonvacuous` exhibits one delay set and two runs:
- The delay set is `D0`: 7h's `prj` arcs (corner-mixed; consistent-corner
  replacement `ArbCorners.nonvacuous_corners`), all routes 0, `smin` = 112. It
  satisfies RT1, RT2 and A0Fork of 7h and RT1b, RT2b and A0Fork2 of 7j.
- Each run is an explicit step-function trace. It satisfies `Run D0` for
  **all t in ℤ**, server relation included, and it satisfies `Scn` or `Scn2`
  for every horizon past the second server edge.

In both runs the server answers in exactly `smin`. So the hypotheses of every
exclusion theorem in 7h and 7j are simultaneously satisfiable, and the
worst-case server is realised.

### 3. Runt band

The band is characterised exactly. A0's low pulse is `p = TA2 − TA`. Assume
g1 is at ua1 before A0's fall arrives there. Then the band is

    c1f − c1r < p < c1f + wfa1

which is 68 < p < 124 + wfa1 with the `prj` arcs. [At a consistent corner
c1r = c1f, so the band is `0 < p < c1f + wfa1` and `A1_stuck`'s pulse disjunct
is vacuous: `ArbCorners.stuck_pulse_vacuous`, `A1_band_corner`.] In this band:
- A1 makes a low runt of width `p − (c1f − c1r)`.
- A1 is then high again for `c1f + wfa1 − p`.

With a matched A0 fork (`wa02 + c2r = wa01 + c1r`), A2 rises at exactly the
start of that window. So **every** A0 pulse shorter than `c1f + wfa1` gives an
A1.A2 overlap, whether A1 is stuck or makes a runt. RT2a is therefore not only
sufficient but necessary for ack exclusion in the matched case.

### Effort and what it buys

- Effort to finish the remaining items: about ½ day for the mirror runt band
  and a counter-trace witness; 1–2 days for the echo train.
- What it buys: the held arbiter's timed exclusion now covers both handover
  directions. It is proved non-vacuous. The RT2 failure mode is pinned down
  completely at the first excursion. The post-route checker list from 7h grows
  by six arc inequalities (RT1b, RT2b ×4, A0Fork2). Its tightest entry is
  `wfa2 + 16 ≤ smin + wa0s + wfb`.

## Model

Everything here is 7h's model, unchanged. See `B-arb-held-timed.md`:
- real INITs through `lutB`/`o5B`/`o6B`;
- a rise-fast pure-delay OR channel per LUT output, with flat O6 arcs and
  per-pin O5 arcs;
- one routed pure delay per pin, which includes the site pin;
- the server is the relation `Server` (H_SERVER_MIN).

### Scenario `Scn2`

- Before the release, client 2 holds: q = 0, A0 = 1, A2 = 1, A1 = 0.
- Client 1 waits: r1 = 1 up to the horizon.
- r2 falls at `t0`.
- The server edges `TA` and `TA2` are free.

**H_SETTLED (mirror)**: `ta + wa0s + qf ≤ t0` and `ta + wa02 + c2f ≤ t0`.
- Physical fact: A0's rise had reached ustate and ua2 before client 2 dropped
  r2.
- It holds because client 2's own chain A2↑ → r2↓ is longer than either path.
- Test: in GLS, measure the A0↑ → ustate/ua2 settling time against the
  A2↑ → r2↓ client delay.

The other named hypotheses are 7h's `Dl` fields (H_NONNEG, H_RISE_LE_FALL,
H_LOOP_POS), H_SERVER_MIN, and the fork conditions, now in both directions.

## Theorems

### Mirror direction (all in `section` over `Run D s`, `Scn2 D s t0 ta TA TA2 Hz`)

**Instants**

| instant | definition |
| --- | --- |
| `TRb` (R0's fall via r2, pin I1) | `t0 + wr2s + Rf2` |
| `QBb` (q's rise) | `TA + wa0s + qr` |
| `RRb` (R0's re-rise via q) | `QBb + wfb + Rrq` |
| `G1b` (g1's rise) | `QBb + wq + g1rq` |
| `G2b` (g2's fall, O6 flat arc) | `min(t0 + wr2g, QBb + wq) + g2f` |
| `T1b` (A2's fall) | `max(G2b + wg2, TA + wa02) + c2f` |
| `T2b` (A1's earliest rise) | `TA2 + wa01 + c1r` |

**Server bounds**
- **`TA_ge2`**: `TRb + smin ≤ TA`.
- **`TA2_ge2`**: `RRb + smin ≤ TA2`.

**Exact traces below the horizon**
- **`q_eq2`**: `q t = [QBb ≤ t]`.
  - `q_lo2`: q is held at 0 by A0.
  - `q_hi2`: q is set by the released hold, then held at 1. Only the fast
    view is needed, which is the rise-fast channel.
- **`R0_hi2` / `R0_lo2`**: R0 is high below `TRb` and low on `[TRb, RRb)`.
- **`g1_eq2`**: `g1 t = [G1b ≤ t]`.
- **`g2_eq2`**: `g2 t = [t < G2b]`.

**RT1b: grant exclusion**
- **`overlap_exact2`**: g1.g2 at t holds iff `G1b ≤ t < G2b`.
- **`RT1b`** is

      wr2g + g2f ≤ wr2s + Rf2 + smin + wa0s + qr + wq + g1rq   ∨   g2f ≤ g1rq

  It says that r2↓ → g2↓ beats the chain r2↓ → R0↓ → server → A0↓ → q↑ → g1↑.
  The structural disjunct `g2f ≤ g1rq` is 124 ≤ 52, which is false for
  prjxray, so only the race form applies.
- **`rt1_exclusion2`**: RT1b implies no grant overlap, for every server.
- **`rt1_counter2`**: if g1 rises before g2 falls for the actual `TA`, and
  `g1rq < g2f`, both grants are high at `G1b`.
- **`rt1_counter2_minserver`**: for a server that answers in exactly `smin`,
  ¬RT1b implies the overlap. So RT1b is necessary.

**RT2b: ack exclusion**

Run-form theorems:
- **`A2_low_after2`**: RT2a', which is `T1b + wfa2 ≤ TA2 + wa02`, implies A2
  is low from `T1b` to the horizon.
- **`A1_low_before2`**: A0Fork2 implies A1 is low before `T2b`.
- **`rt2_exclusion2`**: the run form, combining the two.

**`rt2_exclusion2_arcs`** is the arc form, for every server. `RT2b` is these
four inequalities, together with `A0Fork2`:

| field | inequality |
| --- | --- |
| `pulse` | `c2f + wfa2 ≤ wa0s + qr + wfb + Rrq + smin` |
| `g2` | `wr2g + g2f + wg2 + c2f + wfa2 ≤ wr2s + Rf2 + 2·smin + wa0s + qr + wfb + Rrq + wa02` |
| `forkA` | `wa02 + c2f ≤ wa0s + qr + wfb + Rrq + smin + wa01 + c1r` |
| `forkG` | `wr2g + g2f + wg2 + c2f ≤ wr2s + Rf2 + 2·smin + wa0s + qr + wfb + Rrq + wa01 + c1r` |
| `A0Fork2` | `wa01 ≤ wa0s + qr + wq + g1rq + wg1` (7g's fork on client 1's side) |

Counter-traces:
- **`A2_stuck2`**: suppose `TA2 + wa02 ≤ max(G2b + wg2, TA + wa02 + c2f − c2r)`.
  Then A2 never falls.
- **`rt2_counter2`**: if, in addition, g1 is at ua1 when A0 re-rises there,
  A1 and A2 are both high at `T2b`.

### `prj` (corner-mixed) form

The constants in this table come from reading FAST_MAX/SLOW_MAX as rise/fall
(makesdf.py:63). Consistent-corner arc parts (`ArbCorners.arcs_slowMax` /
`arcs_fastMin`): RT1b 302 / 86, pulse 150 / 42, g2 178 / 41, forkA 274 / 87,
forkG 302 / 86, A0Fork2 274 / 87 (old 136, −16, 12, 40, 68, 108).

The theorems are `prj_RT1b`, `prj_RT2b`, `prj_fork2`, `prj_arc_only2` and
`prj_pulse2_tight`.

| condition | reduced form | zero-routing margin, smin = 112 |
| --- | --- | --- |
| RT1b | `wr2g ≤ wr2s + 136 + smin + wa0s + wq` | 248 |
| pulse | `wfa2 + 16 ≤ smin + wa0s + wfb` | **96** |
| g2 | `wr2g + wg2 + wfa2 ≤ wr2s + 2·smin + 12 + wa0s + wfb + wa02` | 236 |
| forkA | `wa02 ≤ wa01 + smin + 40 + wa0s + wfb` | 152 |
| forkG | `wr2g + wg2 ≤ wr2s + 2·smin + 68 + wa0s + wfb + wa01` | 292 |
| A0Fork2 | `wa01 ≤ wa0s + 108 + wq + wg1` | 108 |

**`prj_pulse2_tight`**: at zero routing, the pulse condition holds iff
`16 ≤ smin`, for the corner-mixed `prj`. [At a consistent corner it holds for
every `smin ≥ 0` (`ArbCorners.pulse2_zero_routing`); the "smin − 16" estimate
and this tightness are artefacts of the mix.]

**Margins with plausible routing.** This is arithmetic, not a proof, with the
corner-mixed constants. [At SLOW_MAX, replacing the arc parts by the corrected
ones: RT1b ≈ 1.64, pulse ≈ 0.72, g2 ≈ 0.71, forkA ≈ 1.28, forkG ≈ 1.77,
A0Fork2 ≈ 0.63 ns; so the pulse is no longer the tightest. Arithmetic.] It
uses the same conventions as 7h's notes:
- smin ≈ 980 ps;
- inter-LUT routes 434–945 ps;
- feedback routes 100–945 ps;
- worst-case sign for each skew.

| condition | arithmetic | margin |
| --- | --- | --- |
| RT1b | 136 + 980 + 434 + 434 − 511 | ≈ 1.47 ns |
| pulse | 980 − 16 + 434 + 100 − 945 | ≈ **0.55 ns** (the tightest in the arbiter; 7h's direction gives 0.62) |
| g2 | −511 + 1960 + 12 + 434 + 100 + 434 − 945 − 945 | ≈ 0.54 ns |
| forkA | 980 + 40 + 434 + 100 − 511 | ≈ 1.04 ns |
| forkG | −511 + 1960 + 68 + 434 + 100 + 434 − 945 | ≈ 1.54 ns |
| A0Fork2 | 108 + 3·434 − 945 | ≈ 0.47 ns (wa01 at the top of the range, the others at the bottom) |

All of these are still far above the 8.5 % scatter and above the
`max(0.2·t, 200 ps)` guard. To break the pulse condition, ua2's feedback
route would have to exceed about a whole server delay.

### Non-vacuity witness

The witness, `D0 = prj 0 … 0 112`, and the theorems:
- `D0_all`: all six conditions hold.
- `W1_run`, `W1_scn Hz` (for `Hz > 552`).
- `W2_run`, `W2_scn Hz` (for `Hz > 484`).
- `W_minserver`: both servers answer in exactly `smin`.
- `nonvacuous`: the existential that packs these together.

**`W1`**: `t0 = 0`, `ta = −1000`, `TA = 264`, `TA2 = 552`.

| signal | trace |
| --- | --- |
| r1 | `[t < 0]` |
| r2 | 1 |
| A0 | `[−1000 ≤ t < 264] ∨ [552 ≤ t]` |
| q | `[t < 388]` |
| R0 | `[t < 152] ∨ [440 ≤ t]` |
| g1 | `[t < 152]` |
| g2 | `[444 ≤ t]` |
| A1 | `[t < 388]` |
| A2 | `[608 ≤ t]` |

**`W2`**: `TA = 264`, `TA2 = 484`.

| signal | trace |
| --- | --- |
| r1 | 1 |
| r2 | `[t < 0]` |
| A0 | `[−1000 ≤ t < 264] ∨ [484 ≤ t]` |
| q | `[320 ≤ t]` |
| R0 | `[t < 152] ∨ [372 ≤ t]` |
| g1 | `[372 ≤ t]` |
| g2 | `[t < 124]` |
| A1 | `[540 ≤ t]` |
| A2 | `[t < 388]` |

Before `ta`, both witnesses are in the stylised settled past. After the last
edge, they are at a fixed point with constant inputs. So the gate relations
hold for every t: each relation is checked by `simp` + `omega` over all of ℤ,
and the server relation is checked at its three edges.

All values were derived by hand from the instant formulas. None was pasted
from a run. A wrong value would fail to check.

### Runt band (7h's direction, `Run D s`, `Scn D s …`)

Each statement below is proved without extra timing hypotheses. Each interval
is empty when the band condition fails.

- **`A1_hi_before`**: A1 is high before `T1`.
- **`A1_runt_low`**: A1 is low on `[T1, TA2 + wa01 + c1r)`.
- **`A1_runt_high`**: A1 is high on `[TA2 + wa01 + c1r, T1 + c1r + wfa1)`.
- **`A1_runt_overlap`**: if `T2` lies in that high window and g2 is at ua2 in
  time, then A1 and A2 are both high at `T2`.
- **`A1_band`**: assume g1 arrives early, so `G1 + wg1 ≤ TA + wa01`, and
  `c1f − c1r < TA2 − TA < c1f + wfa1`. Then A1 is high at `T1 − 1`, low at
  `T1`, and high at `TA2 + wa01 + c1r`.
- **`A1_band_overlap_matched`**: assume `wa02 + c2r = wa01 + c1r`, g1 arrives
  early, `TA2 − TA < c1f + wfa1`, and g2 is there in time. Then A1.A2 at
  `T2`.

Taken with 7h's `A1_low_after` (RT2a) and `A1_stuck`, the first excursion of
A1 is now known for every pulse length:

| pulse length (with g1 early) | A1's first excursion | theorem |
| --- | --- | --- |
| `p ≤ c1f − c1r` (68 ps with `prj`; 0, i.e. vacuous, at a consistent corner) | A1 never falls | `A1_stuck` |
| `68 < p < c1f + wfa1` | a low runt of width `p − 68`, then a re-latch of width `c1f + wfa1 − p` | runt theorems above |
| `p ≥ c1f + wfa1` | clean fall, stays low | `A1_low_after` |

With `prj` the pulse is at least `176 + smin + wa0s + wfb` (corner-mixed;
the band's upper edge, and so this conclusion, is unchanged at a consistent
corner, B-arb-corners.md §2). So the band is
reachable only when `wfa1 > 52 + smin + wa0s + wfb`, which is exactly the
failure of RT2 `pulse`. The band is not a separate risk; it is how a pulse
failure shows up.

**Not proved: the echo train.** After the re-latch window, the hole comes
round ua1's loop again. By hand, in this rise-fast OR model:
- each round shrinks the hole by `c1f − c1r`, so A1 ends latched high after
  `⌈p/68⌉ − 1` runts in total (68 is the corner-mixed `c1f − c1r`; with
  rise = fall the hole does not shrink in this channel, and the asymmetry is
  the unmeasured `ArbCorners.RF`);
- the holes do not interact (checked by hand for `p < c1f + wfa1`).

This is not formalised. What silicon does with sub-arc runts is outside this
model, which has no inertial rejection; that question belongs to
`CElemTiming` / ArbAnalog. The mirror runt band (A2 in `Scn2`) is the same
proof with the 2↔1 roles swapped; it is not written out.

## Fidelity per primitive

This is unchanged from 7h.
- **LUT function**: exact. The real INITs are used.
- **LUT timing**: a rise-fast pure-delay OR channel. It is exact for isolated
  edges. It is transport, with no inertial rejection. The runt-band
  statements are therefore statements about this channel. A real LUT may
  swallow or stretch runts shorter than its arcs.
- **Routing**: one pure delay per pin.
- **C-elements and the state node**: LUT plus routed feedback with positive
  delay.
- **Server**: the relation H_SERVER_MIN. The witnesses use the fastest server
  it allows.
- **Clients**: fixed input traces.
- **Metastability**: absent. It is not reachable in these scenarios.

## Not done

- **Counter-trace witnesses.** These would be concrete runs in which RT1/RT2
  fail and an overlap occurs. The counter-trace theorems are implications;
  their hypotheses are not shown satisfiable here. The `Scn` constraints make
  this plausible, but it is unproved. A witness for the runt band needs the
  echo train in closed form. Effort: about ½ day.
- **Echo-train formalisation and eventual latch** (see above): 1–2 days.
- **Mirror runt band**: about 1 h of duplication.
- **Multi-handover chaining** and a **port to shard A's `Formal/Core`**.
