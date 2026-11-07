# B probe Bov: does a digital race trace explain the unexplained bd_arbcell overlap?

Shard B, Phase 2, 2026-10-27. The owner asked: "whether a race trace explains the
unexplained bd_arbcell overlap" (ARBITER.md: on `hw/arb_mtbf.v`, 15 of 192 copies fire
the FILTERED sticky bit, W = 2, minimum threshold about 203 ps; the flow predicts at most
96 ps).

File: `formal/lean/Formal/Cells/ArbOverlapRace.lean`. It is core Lean, imports only
`Formal.Cells.ArbBinary` (7a, read-only, for `stF`, `gr1`, `gr2` and their INIT
lemmas), and adds no shared definitions. Local definitions: `adist`, `HighOn`, `DET`,
`det`, `Dl`, `Dec`, `Rig`, `Decomp`, `slowD`, `slowP`, `ctrlD` and the trace signals
`sR1 sR2 sQ sG1 sG2 sRaw`.

Check command (checks clean in about 2 s, no errors, no warnings):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbOverlapRace.lean

The file has no `sorry`, `admit`, `axiom` or `native_decide`. I ran `#print axioms` on
all 21 main theorems from a scratch copy. Every one depends only on a subset of
`propext, Classical.choice, Quot.sound`, and two depend on no axioms at all.

No routing was done. No toolchain was run. All numbers come from prjxray-db
(`timings/CLBL{L,M}_{L,R}.sdf` and `tile_type_CLBL{L,M}_{L,R}.json`, the master checkout
`0a0added` that B-pin-assign fetched into the scratchpad). Route lengths are the
B-arb-a0fork figures: a same-slice O6 → A hop is 295 ps, and the next tile is 426-576 ps.

## Answer in one paragraph

**The cell alone: no.** For every digital trace of `bd_arbcell`, no interval with both
grants high is longer than |O5 arc − O6 arc| of q's pin. That bound is ≤ 33 ps at any
consistent corner and ≤ 112 ps in the independent box. It holds for any request
waveforms, request-fork skew, near-tie, runt or endless q oscillation, so candidates (a),
(b) and (c) all fail at the cell. **The rig: yes, at the slow corner.** The detector
`raw = g1c & g2c` reads the two grants through its own site pins. Their input-buffer
delays (slow max: A1 516 ps, A5 112 ps, A6 5 ps) are absent from nextpnr's SDF, and with
them the cap becomes |s + b|. An explicit SLOW_MAX trace with zero SDF interconnect
skew, q settled before and after, and real INITs overlaps for 305 ps and passes every
filter threshold below 305 ps. At FAST_MIN with zero interconnect skew it is impossible:
every run is ≤ 184 ps. So the digital model explains the observation only through the
measurement apparatus, namely the detector's pin assignment together with the
request-fork term. It does not explain it through the arbitration cell. This mechanism
depends on routing and is invisible to the flow, which fits "copies turn clean on
rebuild" and "146 zero-SDF-skew copies still fire".

## Model (gate fidelity)

- **Gates.** These are the real INITs. `ustate` = `bd_c2n_set` `FFB2…`, through 7a's
  `stF` (= `lutB`). `ugrant` O5/O6 = `0C0C0C0C_A0A0A0A0`, through `gr1`/`gr2`
  (= `o5B`/`o6B`). The detector is a LUT2 with INIT `4'h8`, through `lutB` (`det_eq`
  proves it is AND).
- **Timing.** There is one pure (transport) delay per (pin, output): route + site-pin
  input buffer + the LUT arc from that pin. `Dl` has 11 delays: `s1 s2 L` (ustate),
  `a1 x2 b5` (O5), `x1 a2 b6` (O6), `e1 e2` (detector). There is no rise/fall split,
  because prjxray has none (`ArbCorners.RF.sym`).
- **Structures.**
  - `Dec` = grant LUT + detector, with **nothing assumed about q** (`H_G5`, `H_G6`,
    `H_DET`).
  - `Rig` = `Dec` + `H_ST` (state LUT with its loop).
  - `Decomp` names the physical pieces. Each piece is a named hypothesis:
    - `H_SHARED_Q_PIN`: O5 and O6 read q through one physical pin, so they share its
      route and site buffer.
    - `H_DET_PATHS`: each detector input is route + its own site pin + arc, plus `xo5`
      for any extra O5 output delay. prjxray lists none, so it is set to 0.

## Theorems (namespace `Formal.Cells.ArbOverlapRace`)

### §1 The shared-signal cap
- `run_cap`: if `x(t−a)` is high and `x(t−b)` is low throughout `[T, T+ℓ)`, then
  `ℓ ≤ |a−b|`. Nothing is assumed about `x`.
- `run_cap_tight`: one falling edge attains the bound.

### §2 Caps
- **`grant_cap`**: under `Dec`, every interval of `g1 ∧ g2` has length ≤ `|b5 − b6|`.
  This holds for any r1, r2 and q waveforms. The reason is that `g1 = r1·q` is killed
  by q falling and `g2 = r2·~q` by q rising. A request reaching ugrant late (fork skew)
  therefore cannot keep a grant up past q's own edge.
- **`raw_cap`**: every run of `raw` has length ≤ `|(e1+b5) − (e2+b6)|`.
- `b_cancel`: `b5 − b6 = o5q − o6q`. q's route and site pin cancel.
- `sb_eq`: `(e1+b5) − (e2+b6) = (w1−w2) + xo5 + (p1−p2) + (o5q−o6q)`. Only `w1 − w2`
  is in nextpnr's SDF.

### §3 Exact handovers (Rig, q settled before the edge)
- **`handover12`**: r2 is high, r1 falls at f, and q = 1 before. q falls exactly at
  `f + s1`, and `raw` is high exactly on
  `[f+s1+e2+b6, min(f+e1+a1, f+s1+e1+b5))`. So
  **D12 = s + min(κ1, b)**, where:
  - `s = e1 − e2`
  - `b = b5 − b6`
  - `κ1 = a1 − s1 − b6` (the request-fork term: r1 → ugrant − r1 → ustate − q → ugrant).
- **`handover21`**: the mirror case. **D21 = −s + min(κ2, −b)**, where
  `κ2 = a2 − s2 − b5`.

### §4 Filter
- `filter_iff`: `raw(t−c0) ∧ raw(t−c0−Dw)` fires on an isolated run `[lo, hi)` iff
  `Dw < hi − lo`.
- `train_passes` (candidate (b) caveat): with transport delays the filter is not a width
  filter for trains. Pulses 6 ps wide every 140 ps pass a 280 ps filter by aliasing. Each
  run is still capped by `raw_cap`.

### §5 prjxray numbers
- **O6** is flat over the pins: 45 / 56 / 100 / 124 ps (FAST_MIN / FAST_MAX / SLOW_MIN /
  SLOW_MAX).
- **O5** ranges over all LUTs, pins and CLB types:
  - [42, 51] / [52, 63] / [93, 127] / [116, 157];
  - A5 → O5 is the fast pin: 116-120 slow max, against 149-157 for A1-A4.
- **Site pins**, SLICEL slow max: A1 516, A2 507, A3 344, A4 284, A5 112, A6 5. Fast
  min: 172 / 170 / 107 / 86 / 33 / 2. SLICEM is up to 531 / 180.
- `cell_cap_consistent`: |b| ≤ 6 / 7 / 27 / 33 at the four corners.
- `cell_cap_box`: |b| ≤ 112 in the box.
- **`cell_never_203`**: for every digital trace of the cell with arcs in the box, every
  `g1 ∧ g2` run is ≤ 112 ps < 203 ps.
- **`rig_cap_fastMin`**: at FAST_MIN with zero interconnect skew (`w1 = w2`, `xo5 = 0`),
  every `raw` run is ≤ 184 ps. Nothing passes 203.
- `rig_cap_slowMax_value`: the same bound at SLOW_MAX is 559 ps, which is not a
  rejection.
- **Explicit SLOW_MAX trace** (`slowD`, `slowP`; zero SDF skew):
  - ustate: r1 on A5 over a 400 ps route.
  - ugrant: r1 on A1 over the same 400 ps route; q on A5 over the 295 ps same-slice hop.
  - detector: g1c on A1 and g2c on A5, over equal 300 ps routes.
  - This gives s = 404, b = −6 and κ1 = −99.
  - `slow_trace_rig`: every gate relation holds.
  - `slow_trace_raw`: `raw` is high exactly on [1703, 2008), i.e. **305 ps**.
  - `slow_trace_passes`: the filter fires iff Dw < 305.
  - `slow_trace_passes_203`.
- **Negative control** `ctrl_trace_clean`: the same trace with g1c also on A5
  (`e1 = e2`, s = 0) has no overlap at all. `slow_pins_at_fastMin`: the same pins at
  FAST_MIN give s + b = 142 < 203.

## Comparison with the board facts

| board fact | this model |
|---|---|
| 96 ps flow cap, "no copy should fire" | The cap was computed from nextpnr's SDF. That SDF has a flat 124 ps per LUT arc and no site-pin delays (B-arb-a0fork, C-10b), so it cannot see `p1 − p2` (up to ±511 ps slow) or the site-pin parts of κ. The cell part is right (`cell_never_203`). The detector part is missing. |
| 146 zero-skew copies still fire at 6.8% | "Zero skew" is `w1 − w2`. `sb_eq` shows that the decisive part `p1 − p2` is not in it. |
| 43 of 50 bad copies turn clean on rebuild | nextpnr's chipdb gives every LUT pin the same delay, so the pin choice is arbitrary per build (B-arb-a0fork). `s` and `κ` are re-drawn on each build. |
| no spatial clustering, die position p = 0.23 | Pin assignment is not spatial. |
| filter race margin p = 0.60 | That margin was SDF-only as well. The filter threshold has its own site-pin term, `Dw = chain + p(I1) − p(I0)` at `uwand`, so it varies per copy by up to ±0.5 ns slow. This was not modelled beyond `filter_iff`'s parameter. |
| A5 lead (q on A5: 2/107 against 13/85) | **Not explained, and the model predicts mixed signs.** q on A5 at **ugrant** makes `pq` small. That raises κ1 and κ2 by 172-404 ps, which means MORE overlap whenever κ binds. It also makes b = −6 instead of +26..+33, which shifts 32 ps from D12 to D21. q on A5 at **ustate** forces r1 and r2 onto slower ustate pins, which raises s1 and s2, which means LESS overlap. The pooled lead mixes the two. |

**Firing condition the model predicts per copy** (transport, slow-ish die):

    max( s + min(κ1, b),  −s + min(κ2, −b) )  >  Dw_copy

Here:
- `s = (w1−w2) + (p1−p2)`, with `p` the detector site pins of g1c and g2c;
- `κ1 = (w_r1→ug − w_r1→st) + (p_r1@ug − p_r1@st) + (O5(r1 pin) − O6) − (wq + pq + O6)`;
- `κ2 = (w_r2→ug − w_r2→st) + (p_r2@ug − p_r2@st) − (wq + pq + o5q)`.

A necessary condition is |s| ≥ 203 − 33 = 170 ps, i.e. g1c and g2c on detector pins
whose site delays differ by ≥ 170 ps, with the sign matching the direction.
**Pre-registered test.** From the arb_mtbf bitstream's FASM pin maps (C's importer plus
PinAssign's method), evaluate the formula at the slow corner for all 192 copies, and
check that the 15 firing copies are the ones above threshold. Those per-copy data are not
in this container. The routed arb_mtbf artefacts are not on disk.

## What did not work / not done

- **Rise/fall asymmetry** (H_RF_ASYM, unmeasured) is not modelled. For the cell alone to
  reach 203 ps, an output's fall would have to be ≥ ~170 ps slower than its rise, beyond
  the O5/O6 arc difference. That would be a large unmeasured asymmetry.
- **Inertial channels.** The 305 ps trace consists of wide pulses only (every edge is
  isolated by more than one arc), so inertial and transport readings agree on it. The caps
  in §2 are proved for transport only. The train caveat (`train_passes`) needs runts of a
  few ps to traverse at least 4 LUT stages, which is unlikely on silicon. It is not a
  candidate I would pursue.
- **Per-copy evaluation.** As above, the data are missing here.
- **The silicon corner.** The die's actual corner is not known. The mechanism exists at
  SLOW_MAX and is excluded at FAST_MIN (with zero interconnect skew). FAST_MAX allows up
  to 230 ps, which is marginal.
- **Scope of §3.** The handover traces use global steps (r2 ≡ 1). On the board r2 is a
  ~1.9 ns half-period square wave. The run depends only on a ~2 ns window (transport,
  causal), but that locality is argued, not proved.

## Verdict

**Works.** It checks in about 2 s and took about 1.5 h of the 3 h box.
- **The cell:** a race trace of `bd_arbcell` cannot explain the overlap. The proved cap
  is ≤ 33 ps at a consistent corner and ≤ 112 ps in the box, for every digital trace.
  This settles candidates (a), (b) and (c) at the cell.
- **The rig:** the digital model does explain filter-passing overlaps in the rig, via
  detector site-pin skew plus the request fork. An explicit 305 ps SLOW_MAX trace with
  zero SDF skew is proved. The effect is routing-dependent and invisible to the SDF, as
  the board shows.
- **Remaining work:** about 0.5 day, if the arb_mtbf FASM is available. Run the per-copy
  formula over the 192 copies with C's importer. If it holds, the 8% is a detector
  artefact and is closed.
- **What it buys:** it closes the open item in ARBITER.md's summary table one way or the
  other. It also flags that every width-filter conclusion in the rig carries a hidden
  per-copy site-pin term (in the detector and in `uwand`).

## Fidelity per primitive

- **LUTs** (ustate, ugrant O5/O6, detector): real INITs evaluated with `lutB`/`o5B`/`o6B`.
  Each pin is a transport delay that lumps the route, the site-pin input buffer and the
  per-pin arc (the mux tree behind its input buffers). There is no rise/fall split and no
  Kleene X. A metastable q appears only as an arbitrary Boolean waveform, which
  `grant_cap` and `raw_cap` cover.
- **Feedback:** ustate's loop is a transport delay `L` (a routed wire plus the arc). It
  is irrelevant to every cap.
- **Shared q pin:** O5 and O6 read one physical pin (`H_SHARED_Q_PIN`), which is a fact
  of the CLB.
- **Filter:** `raw ∧ delay(raw)` with transport delays. Its threshold `Dw` is a parameter
  (H_FILTER, about 203 ps or more on the board).
