# B probe Cm2: timed arc forms of the control_merge obligations

Shard B, follow-up of probe Cm (`B-amerge.md`). 2026-10-27. Gives the ARC
forms of the three wrapper obligations Cm found as SI scheduling filters
(H_BUNDLED_IDX, H_IDX_ACK_FORK, H_RT2_CASCADE), in the style of 7h
(`ArbHeldTimed`): `Int` ps, every LUT output the rise-fast OR channel of 7h
with the REAL INIT, every route and arc a named field, the arbiter part of each
run being 7h's / 7j's `Run` + `Scn` / `Scn2` unchanged.

No route, no board, no GLS, no nextpnr run: **nothing below is a routed
number**. All numbers are prjxray consistent-corner arc values (FAST_MIN /
SLOW_MAX columns, `ArbCorners`, `ArbCornersPin`) with routes set to 0
("arc-only"); gcd_hw's DELAY values (12 for the 7 amerge2, 24 for the amerge3)
are from `B-gcd-cells.md` (synthesis listing).

## Files (all CLAIMED, core Lean, no Mathlib)

| file | lines | content | check |
|---|---|---|---|
| `formal/lean/Formal/Cells/AMergeTimed.lean` | 371 | wrapper delays `Wd`, index LUT channel `Idx`/`Cons`, H_REQ_PATH (`ReqZ`), race 1 and race 2 of H_BUNDLED_IDX (amerge2), H_IDX_ACK_FORK | ~6 s |
| `formal/lean/Formal/Cells/AMergeTimedW.lean` | 331 | witnesses: parametric arbiter runs `W1g`/`W2g` at any consistent corner and server, wrapper `wW`, non-vacuity at both corners, DELAY = 0 counter instance, per-pin A5 instance, fork witnesses | ~5 s |
| `formal/lean/Formal/Cells/AMergeTimedC.lean` | 513 | H_RT2_CASCADE: the cascade server lemma (arbiter 2 + its server as arbiter 1's server), RT2 of arbiter 1 both directions, counter-trace, explicit two-arbiter witness; amerge3 `index[0]` race 1 + counter + witness | ~9 s |

Imports (read-only): `Formal.Cells.AMergeGates` (the inferred INITs `idx2`,
`idx3l` and their equations), `Formal.Cells.ArbCorners` (which imports
`ArbHeldTimed`, `ArbHeldTimed2`, `ArbA0Fork`, `ArbHandover`). `ArbCornersPin`
was read, not imported (its per-pin arc table is quoted below; `pinA5_delay0`
uses its values). No shared definitions added; Prelim untouched.

Check (in dependency order; the first two write the oleans the later files import):

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/AMergeTimed.lean -o .lake/build/lib/lean/Formal/Cells/AMergeTimed.olean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/AMergeTimedW.lean -o .lake/build/lib/lean/Formal/Cells/AMergeTimedW.olean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/AMergeTimedC.lean
    cd .. && ./check.sh Formal/Cells/AMergeTimed.lean   # [check] OK (likewise W, C)

All three check clean (no output) and `check.sh` prints `[check] OK` for each.
No sorry/admit/axiom/native_decide. `#print axioms` (scratch file importing the
oleans) on every theorem named below: `propext, Classical.choice, Quot.sound`
or a subset (`idx_ack_fork_*`: `propext, Quot.sound`).

**Negative control** (scratch copy): weakening each of `BidxA`, `BidxB.ack`
and `IdxAckFork` by 1 ps (`+ 1` on the request side) breaks the corresponding
sufficiency proof (`bidx_new_owner`, `bidx_old_owner` at two places,
`idx_ack_fork_hold`) with an omega failure: every term of each inequality is
load-bearing up to 1 ps. The counter-traces show the same from the other side.

## Model

* **Arbiter**: 7h's `Dl`, `Sigs`, `Run` (ustate O6/O5, ugrant O5/O6, ua1/ua2,
  real INITs, per-pin O5 arcs, flat O6 arcs, every route incl. site pin,
  server relation H_SERVER_MIN) and 7h's `Scn` (client 1 -> client 2) / 7j's
  `Scn2` (client 2 -> client 1). Their exact traces are reused: `g2_eq`,
  `g2_eq2`, `R0_lo`, `R0_lo2`, `TA_ge*`, `TA2_ge*`, `A2_low_before`,
  `A2_low_after2`. New arbiter lemma: `A2_hi_before2` (in the mirror run A2
  stays high until its fall instant `T1b`).
* **Index LUT** (inferred, H_YOSYS_MAP): `Idx t = idx2 (g2, A2 at view xr) ||
  idx2 (g2, A2 at view xf)`, `idx2` = INIT 4'hE through `lutB`
  (`AMergeGates.idx2`); pins delayed by routes `wgi` (g2) and `wai`
  (in1_ack). amerge3: `idx3l` = INIT 16'h000E, pins [in1_ack, g2(arb1),
  g2(arb2), in2_ack] (`Cons3`).
* **Consumer**: index reaches the capture point through `wid` (pure
  transport, max side, H_WIRE_TRANSPORT); needs setup `su`.
* **Request path** (H_REQ_PATH, `ReqZ`): the capture instant `Zr` of the new
  token is caused by R0 high at some `u` after R0 fell for the previous token,
  `u + dz ≤ Zr`; `dz` = R0 -> uor -> bd_delay_gated rise -> z_req -> consumer
  (min side). For amerge3 R0 is arbiter 2's.
* **Client** (fork only, H_CLIENT_MIN): `r2` falls no sooner than `cmin` after
  in1_ack rose at ua2's output.
* **Cascade**: arbiter 2 is a second 7h `Run` whose `r1` IS arbiter 1's R0 and
  whose `A1` IS arbiter 1's A0 (same nets, `hr`, `hA`); arbiter 2's z_ack is
  its server (H_SERVER_MIN with arbiter 2's `smin` = uor + DELAY + consumer).

## Theorems

### H_BUNDLED_IDX race 1 (new owner = client 2 / in1; `AMergeTimed`)

* `BidxA D W`: `wq + g2r + wgi + xr + wid + su ≤ wfb + Rrq + dz`. Launch q's
  fall at ustate O6; data q -> ugrant.I2 -> g2 rise -> index -> consumer;
  request q -> ustate.I2 (feedback) -> R0 rise (O5 from the q pin) -> uor ->
  DELAY -> z_req -> consumer. The common part (A0 fall -> q) cancels.
* `bidx_new_owner` (sufficient): for every run of the real arbiter, every
  server, every capture instant allowed by `ReqZ`: the consumer sees
  `index = 1` from `Zr − su` to the horizon.
* `bidx_new_owner_counter`: if `¬ BidxA`, with the minimal capture
  `Zr = RR + dz`, the consumer sees `index = 0` (the PREVIOUS owner) at
  `Zr − su`. Extra hypotheses: 7g's `A0Fork` (A2 still low) and
  H_Z_IN_SRV `dz ≤ smin` (the server's minimum response includes the
  request path: the consumer acknowledges only what it captured).
  So `BidxA` is necessary and sufficient at the minimal request path.

### H_BUNDLED_IDX race 2 (previous owner = client 2 leaves; `AMergeTimed`)

* `BidxB D W`, three fields (all needed: index = g2 | A2 must have fallen):
  - `ack`: `wa02 + c2f + wai + xf + wid + su ≤ wa0s + qr + wfb + Rrq + dz`
    (the race named in Cm: A0 fall -> ua2 -> A2 fall -> index, vs A0 fall
    -> ustate.I4 -> q rise -> feedback -> R0 rise -> z_req);
  - `gack` (any of two forms): g2's fall reaching ua2 when it is A2's later
    input, via r2 (contains `wr2s + Rf2 + smin`) or via q;
  - `grant` (any of two forms): g2's fall reaching the index LUT directly.
* `bidx_old_owner` (sufficient, under the arbiter's own `RT2b`): the consumer
  sees `index = 0` from `Zr − su` on.
* `bidx_old_owner_counter`: if the `ack` leg (with `xr`) fails, then at the
  minimal capture the consumer still sees `index = 1`. TA cancels: holds for
  every server. `bidx_old_owner_counter_g`: same via the grant leg.
  At a consistent corner (`xr = xf`) `ack` is exact.

### H_IDX_ACK_FORK (`AMergeTimed`)

* `IdxAckFork D W cmin`: `wai + xr ≤ cmin + wr2g + g2f + wgi + xf`. Launch:
  in1_ack rise at ua2.O6; data: -> index.I1; request: the other fork branch,
  -> client -> in1_req fall -> ugrant.I1 -> g2 fall -> index.I0. At a
  consistent corner the index arcs cancel: `wai ≤ cmin + wr2g + g2f + wgi`.
* `idx_ack_fork_hold` (sufficient): index stays 1 from in1_ack's rise to the
  horizon (needs only ugrant's relation, 7h's `Run.H_g2` verbatim, and
  `FkScn`: q held low by A0 (H_Q_HELD, = 7h's `FS_hold`), r2/A2 step traces,
  H_CLIENT_MIN, H_SETTLED).
* `idx_ack_fork_counter`: if the actual race is lost, index = 0 at the instant
  g2's fall arrives while in1_ack is high at its source;
  `idx_ack_fork_counter_minclient`: with `t1 = Ar + cmin`, `¬ IdxAckFork`
  suffices (necessary and sufficient). `idx_ack_fork_in_window`: that
  instant precedes z_ack's fall whenever `wr2g + g2f + wgi + xf < wr2s + Rf2
  + smin` (7j's `TA_ge2`), i.e. the consumer is still holding.

### H_RT2_CASCADE (amerge3, `AMergeTimedC`)

* `cascade_server`: from arbiter 2's real gates and its server, in the window
  of one arbiter-1 handover with arbiter 2 staying with acc1 (`CScn`):
  acc1_ack falls no sooner than `sF = wr1s + Rf1 + smin + wa01 + c1f` after
  acc1_req fell and re-rises no sooner than `sR = wr1s + Rr1 + smin + wa01 +
  c1r` after acc1_req re-rose (arbiter 2's fields). Proved through
  `TZ_ge`, `TA_ge_c`, `TZ2_ge`, `TA2_ge_c` (z_ack's two edges by the server
  relation, acc1_ack's two edges by ua1's C-element relation).
* `RT2C D1 sF sR` / `RT2Cb`: 7h's `RT2` / 7j's `RT2b` with `smin` -> `sR` in
  `pulse`, `forkA` and `2·smin` -> `sF + sR` in `g1`/`g2`, `forkG`.
* `rt2_cascade`, `rt2_cascade2` (sufficient): arbiter 1's acks never both
  high, for every run of both arbiters and every server of arbiter 2.
  (`cscn_of`, `cscn_of2` build arbiter 2's view from arbiter 1's run.)
* `rt2_cascade_counter`: with the cascade at its minimum (`TA = TR + sF`,
  `TA2 = RR + sR`), acc1_ack re-rising at ua1 before g1's fall arrives gives
  A1 and A2 of arbiter 1 both high (7h's `rt2_counter`).
* `cascade_nonvacuous` (generic in the corner arcs and in arbiter 2's server
  `S2`): explicit runs of BOTH arbiters for all t, wired as the cascade by
  `rfl`, every hypothesis of `rt2_cascade` true, and the derived bounds
  attained with equality (`sF`, `sR` are tight). `cascade_corners`: with
  DELAY = 24 (`S2` = 25 arcs) `sR` = 3376 / 1214 ps (SLOW_MAX / FAST_MIN).

### amerge3 `index[0]`, race 1 (`AMergeTimedC`)

* `BidxA3 D1 D2 W`: `wq1 + g2r1 + wgi + xr + wid + su ≤ wfb1 + Rrq1 + wr1s2 +
  Rr1_2 + dz`: the request path runs through arbiter 2's ustate O5 (one more
  O5 arc + route of slack than amerge2).
* `bidx3_new_owner` (sufficient, H_IN2_IDLE: g2(arb2) = in2_ack = 0 in the
  window), `bidx3_new_owner_counter` (minimal request path; won1 = 0 forces
  index[0] = 0 whatever the in2 pins do), `bidx3_nonvacuous_slow`.

### Non-vacuity and instances (`AMergeTimedW`, `AMergeTimedC`)

* `dW a b cq S` (= `ArbCorners.cDl slowMax/fastMin RF.sym (x0 S)` by `rfl`,
  `dW_slow`, `dW_fast`), `W1g`, `W2g`: parametric runs, `Run` for all t,
  `Scn`/`Scn2` for every horizon past the second server edge, server answering
  in exactly `S` (needs `a ≤ S`: A0's low pulse covers the ua loops).
* `nonvacuous_slow` / `nonvacuous_fast` (DELAY = 12, `S = dz` = 13 arcs):
  `BidxA`, `BidxB`, `A0Fork`, `RT2b`, H_Z_IN_SRV, both runs, legal `ReqZ`;
  the consumer's index is 0 at 2135 and 1 from 2136 (slow), 1 at client 2's
  capture and 0 at client 1's.
* `counter_fast_delay0`: DELAY = 0 (bypass) at FAST_MIN fails race 1 by 3 ps
  and the counter-trace fires on an explicit run; `slow_delay0_passes`
  (+26 ps at SLOW_MAX); `pinA5_delay0`: with ustate's q on A5 (routed seeds
  S1, S2, S4; SLICEM O5 from A5 48/116) it flips: fails at SLOW_MAX by 8 ps,
  passes at FAST_MIN by 3 ps.
* `fork_nonvacuous_slow`, `fork_counter_witness` (an in1_ack route of 700 ps
  against a two-arc client: index 0 at t = 496 while in1_ack is high).
* `bidx3_nonvacuous_slow`: index[0] at the consumer 0 at 3899, 1 from 3900 to
  the capture at 7054.

## Arc-only margins (routes 0; not routed numbers)

| obligation | form | SLOW_MAX | FAST_MIN |
|---|---|---|---|
| race 1 amerge2, DELAY = 12 | `cq + dz − a − x` | 1514 | 537 |
| race 1 amerge2, DELAY = 0 (identity pins, q on A3) | | +26 | **−3** |
| race 1 amerge2, DELAY = 0, q on A5 (seeds S1, S2, S4) | | **−8** | +3 |
| race 2 `ack`, DELAY = 12 | `cq + dz − x` | 1638 | 582 |
| race 1 amerge3 index[0], DELAY = 24 | `cq + b + dz − a − x` | 3154 | — |
| fork, client = two arcs | `cmin + g2f − wai` (index arcs cancel) | 372 | 135 |
| cascade `pulse`, DELAY = 24 | `qf + Rrq + sR − c1f` | 3526 | 1256 |

Reading: with gcd_hw's DELAY = 12 / 24 the index races are carried entirely by
the DELAY line (the index cone and R0's cone are both two LUTs; without the
line the race is a 3-8 ps O5-vs-O6 arc difference whose sign depends on the
corner AND on which physical pin ustate reads q on). The fork obligation is a
pure route-skew condition: in1_ack's route into the index LUT must not exceed
the client's loop + in1_req's route + one O6 arc + g2's route. The cascade
`pulse` has a whole extra server of slack over a single arbiter's RT2.
These are arc-only; routes enter every term (site pins A1 0.17-0.52 ns), so
the real check is the per-instance EndpointOK below on routed SDF + site pins.

## EndpointOK forms for `formal/out/cell_constraints.json` (NOT written; listed here)

Conventions as the JSON's (`conventions.form`, `arc_kinds`, `corner_rule`;
mode `1C`; every `w*` includes the physical pin's site delay). `index_lut` =
the inferred LUT driving `index` (amerge2: LUT2 4'hE; amerge3: index[0] LUT4
16'h000E, index[1] LUT2 4'hE), found by the checker as the driver of the
`index` net (H_YOSYS_MAP). `margin_ps` 0 (guardband applied by the checker).

1. **`bdc_amerge.bundled_idx_grant`** (7 amerge2 instances; catalogue: new).
   launch: `uarb1.ustate.O6` (q) edge.
   data: wire `ustate.O6 -> ugrant.I2` (`wq`) + site_pin `ugrant.I2` +
   lut_arc `ugrant.I2 -> O6` (`g2r`) + wire `ugrant.O6 -> index_lut.I0`
   (`wgi`) + site_pin + lut_arc `index_lut.I0 -> O6` (`xr`) + env
   `index -> consumer capture` (`wid`) + cell_param/env setup (`su`).
   request: feedback_wire `ustate.O6 -> ustate.I2` (`wfb`) + site_pin
   `ustate.I2` + lut_arc `ustate.I2 -> O5` (`Rrq`, per physical pin:
   `ArbCornersPin.pinCol`) + wire `R0 -> uor.I0` + site_pin + lut_arc `uor`
   + line `udly` rise chain (DELAY hops) + wire `z_req -> consumer` (`dz`).
   lean: `AMergeTimed.bidx_new_owner` (sufficient), `bidx_new_owner_counter`
   (counter_trace), `AMergeTimedW.nonvacuous_slow/_fast` (witness),
   `counter_fast_delay0`, `pinA5_delay0` (instances). exactness: necessary
   and sufficient at the minimal request path (with `A0Fork`, H_Z_IN_SRV).
   rule: rule A on `<cell>.uor` covers it only if its data cone includes the
   index LUT's g2 pin (today it audits the whole input cone).
2. **`bdc_amerge.bundled_idx_ack`** (7). launch: `z_ack` (= A0) fall.
   data: wire `A0 -> ua2.I1` (`wa02`) + site_pin + lut_arc `ua2 -> O6`
   (`c2f`) + wire `ua2.O6 -> index_lut.I1` (`wai`) + site_pin + lut_arc
   `index_lut.I1 -> O6` (`xf`) + `wid` + `su`. request: wire `A0 ->
   ustate.I4` (`wa0s`) + site_pin + lut_arc `ustate.I4 -> O6` (`qr`) +
   feedback_wire (`wfb`) + site_pin + lut_arc `ustate.I2 -> O5` (`Rrq`) + uor
   + udly rise + `dz`. lean: `bidx_old_owner` (field `ack`),
   `bidx_old_owner_counter`. exactness: exact at a consistent corner.
3. **`bdc_amerge.bundled_idx_ack_g`** (7), combine `any` of two forms
   (`BidxB.gack`): launch in1_req fall: data `wr2g + g2f + wg2 + c2f + wai +
   xf + wid + su`, request `wr2s + Rf2 + env smin + wa0s + qr + wfb + Rrq +
   dz`; or launch q rise: data `wq + g2f + wg2 + c2f + wai + xf + wid + su`,
   request `wfb + Rrq + dz`. lean: `bidx_old_owner` (sufficient).
4. **`bdc_amerge.bundled_idx_grant_fall`** (7), combine `any`
   (`BidxB.grant`): as 3 with `wg2 + c2f + wai` replaced by `wgi` (g2 ->
   index_lut.I0 directly). lean: `bidx_old_owner`, `bidx_old_owner_counter_g`.
5. **`bdc_amerge.idx_ack_fork`** (7 amerge2: pin in1_ack; amerge3: the same
   form per ack pin of each index LUT, stated, not proved). launch: `ua2.O6`
   (in1_ack) rise. data: wire `ua2.O6 -> index_lut.I1` (`wai`) + site_pin +
   lut_arc `index_lut.I1 -> O6` (`xr`). request: env `client_response`
   (in1_ack at ua2.O6 -> client -> in1_req fall, min; `cmin`) + wire
   `in1_req -> ugrant.I1` (`wr2g`) + site_pin + lut_arc `ugrant.I1 -> O6`
   (`g2f`) + wire `ugrant.O6 -> index_lut.I0` (`wgi`) + site_pin + lut_arc
   `index_lut.I0 -> O6` (`xf`). lean: `idx_ack_fork_hold` (sufficient),
   `idx_ack_fork_counter_minclient` (counter_trace; necessary and sufficient
   at the minimal client), `fork_nonvacuous_slow`, `fork_counter_witness`.
6. **`bdc_amerge3.rt2_cascade_{pulse,g1,forkA,forkG}`** and
   **`..._{pulse2,g2,forkA2,forkG2}`** (1 instance, `uarb1`): the eight
   `bd_arbiter.rt2_*` / `rt2b_*` forms of uarb1 with its `env smin` replaced
   by the explicit path `sR` (rise: wire `acc1_req -> uarb2.ustate.I0`
   (`wr1s`) + site_pin + lut_arc `uarb2.ustate.I0 -> O5` (`Rr1`) + env
   `smin` of uarb2 (uor + udly + consumer -> z_ack) + wire `z_ack ->
   uarb2.ua1.I1` (`wa01`) + site_pin + lut_arc `uarb2.ua1 -> O6` (`c1r`)),
   and `2·smin` by `sF + sR` (`sF` the same with the fall arcs). lean:
   `AMergeTimedC.rt2_cascade`, `rt2_cascade2` (sufficient), `cascade_server`
   (reduction), `rt2_cascade_counter` (counter_trace),
   `cascade_nonvacuous` (witness). Side hypotheses (not inequalities):
   H_ACK1_PULSE = `bd_c2.pulse_width` of instance `uarb2.ua1`; H_SETTLED;
   scope H_IN2_IDLE (see below).
7. **`bdc_amerge3.bundled_idx0_grant`** (1): as 1 with `index_lut` = the
   index[0] LUT4 (g2(arb1) on I1) and the request path extended by wire
   `acc1_req -> uarb2.ustate.I0` + site_pin + lut_arc `uarb2.ustate.I0 ->
   O5` (`Rr1`) before uor. lean: `bidx3_new_owner`,
   `bidx3_new_owner_counter`, `bidx3_nonvacuous_slow`.

Everything else (`bd_arbiter.rt1*`, `rt2*`, `a0_fork*` per instance of the 9
arbiters) is unchanged from the existing JSON ids.

## Named hypotheses

| name | where | physical fact | test |
|---|---|---|---|
| `Wd` routes/arcs (`wgi`, `wai`, `xr`, `xf`, `wid`, `dz`, `su`) | index LUT, consumer | routed interconnect incl. site pin; prjxray IOPATH; consumer setup | routed SDF + prjxray tile json |
| H_NONNEG, H_ARC_POS, H_RISE_LE_FALL | `Wd` | causality; LUT arc > 0; rise ≤ fall (prjxray: equal per corner) | – |
| H_WIRE_TRANSPORT | `Cons` | index -> capture point is a pure transport delay | GLS |
| H_REQ_PATH (`ReqZ`) | capture | capture caused by R0 high ≥ `dz` earlier, after R0 fell for the previous token | GLS: z_req rise vs R0 rise per token |
| H_Z_IN_SRV (`dz ≤ smin`) | counter-traces only | the server's minimum response includes the request path | structural (consumer acks what it captured) |
| H_CLIENT_MIN (`cmin`) | fork | min in1_ack -> in1_req fall of the client | routed netlist walk / GLS |
| H_Q_HELD (`FkScn.H_q`) | fork | q low while client 2 owns (7h `FS_hold`) | follows from the arbiter run |
| `FkScn.H_SETTLED` | fork | r2, q settled in g2's/index views before in1_ack rose | GLS |
| H_IN2_IDLE / `CScn.H_r2` | cascade, index[0] | arbiter 2's own input idle during arbiter 1's handover (scope restriction) | – (see below) |
| H_ACK1_PULSE | cascade | acc1_ack's low phase ≥ uarb2.ua1's loop (`bd_c2.pulse_width`) | GLS |
| `CScn.H_SETTLED` | cascade | z_ack's and acc1_ack's rises reached ua1's views before acc1_req fell | GLS |
| H_YOSYS_MAP | index LUTs | inferred INITs as Cm found | gcd_hw synth JSON |
| 7h/7j: `Dl`, H_SERVER_MIN, `Scn.H_SETTLED`, `A0Fork`, `RT2b` | arbiter | cited | 7h, 7j, 7g |

## What did not work / not done

* All three files checked on first or second try; no unproved goals.
* Not proved: (a) amerge3 `index[1]` (= won2, a LUT2 like amerge2's: the
  amerge2 theorems apply verbatim to arbiter 2's own handovers, but the
  composition "arbiter 2 hands over while arbiter 1 also moves" is not
  modelled); (b) H_IDX_ACK_FORK for amerge3's LUT4 (stated per pin, not
  proved; the LUT4's won2 pins can only pin index[0] to 0, `idx3l_hold`);
  (c) the cascade when arbiter 2 hands over to in2 during arbiter 1's
  handover (`H_IN2_IDLE` is a scope restriction: then acc1_ack stays low
  longer, which only lengthens TA2, but this is not proved); (d) race 2 for
  amerge3; (e) a run witness of `rt2_cascade_counter` (the cascade's g1 leg
  cannot fail at zero routing; it is 7h's `rt2_counter` instantiated, valid
  but not exhibited); (f) the consumer's real structure (bd_fork + links of
  gcd_hw) is abstracted into `wid`, `dz`, `su`; (g) no GLS, no routed
  numbers.
* The arc-only fork margin (372 / 135) assumes a two-arc client; the real
  client of each gcd_hw control_merge input was not walked.

## Verdict

**Works.** All three obligations Cm left as SI filters now have arc forms
proved sufficient against the real arbiter run (7h/7j) and the real inferred
index INITs, each with a counter-trace that makes it necessary at the minimal
request path / client / cascade, each non-vacuous by explicit runs at both
consistent corners (both arbiters explicit for the cascade). Findings:
(1) H_BUNDLED_IDX is carried by the DELAY line: with the bypass (DELAY = 0)
amerge2's race 1 fails by 3-8 ps at one corner whichever pin ustate reads q
on; with gcd_hw's DELAY = 12 the arc-only margin is 1514 / 537 ps.
(2) H_IDX_ACK_FORK reduces at a consistent corner to the route-skew condition
`wai ≤ cmin + wr2g + g2f + wgi`, not covered by any existing rule.
(3) H_RT2_CASCADE is 7h's RT2 for uarb1 with its server DERIVED from uarb2's
gates (`cascade_server`, tight), so uarb1's RT2 margins grow by a whole
uarb2 server; the side obligation is uarb2.ua1's pulse width.
Effort to finish the gaps above: about 1 day (index[1]/LUT4 fork per pin
½ day, the in2-handover cascade case ½ day). What it buys: 7 new per-instance
EndpointOK entries (listed above) for the checker, replacing three SI
filters; together with Cm, the control_merge is now proved at gate level with
timed obligations in the same form as the arbiter's.

## Fidelity per primitive

* index LUTs (LUT2 4'hE, LUT4 16'h000E, inferred): 7h's rise-fast OR channel of
  the real INIT through `lutB`, one pure transport per pin route (site pin
  included), flat O6 arcs; no runts or intra-LUT skew below the channel (grade
  B, as 7h). Kleene behaviour not used (Cm's `idx2_both_moving` is the reason
  the races must be ordered at all).
* ustate / ugrant / ua1 / ua2: exactly 7h's model (per-pin O5 arcs, flat O6,
  feedback as a routed wire with its own delay, C-element = LUT reading its
  own output).
* uor + bd_delay_gated: lumped into the min-side request delay `dz` (rise
  only); its gated fall and flush are not used here (`GcdCells`,
  `ConstraintsFastFall`).
* consumer: transport `wid` + setup `su` (no latch model).
* server: 7h's relation H_SERVER_MIN; for the cascade, arbiter 2 + its server
  is DERIVED to be a server for arbiter 1 with responses `sF`/`sR`.
* client: a minimum response `cmin` (fork only), otherwise 7h's scenario step
  traces.
