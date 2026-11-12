# B probe Lt2: finishing the timed operator cells (data path, steer packaging, pulses, FASTFALL)

Follows probe Lt (`B-ops-timed.md`). Items (b), (d), (a), (c) of its "not done"
list, in that order. All four are now kernel-checked; open points are at the end.

## File and check

| file | lines | contents | check time |
|---|---|---|---|
| `formal/lean/Formal/Cells/OpsTimed2.lean` | ~1230 | §1-3 mux data path + witness; §4-5 merge data path (usel + datamux) + witness; §6 steer causal/static packaging + witness; §7 non-empty pulses (mux, merge) + witness; §8 FASTFALL=1 line (`and_tok`, `ff_tok`, `mux_ok_fastfall`) | ~15-25 s |

CLAIMED, core Lean (no Mathlib), no `sorry`/`admit`/`axiom`/`native_decide`.
Imports, read-only: `Formal.Cells.OpsTimedWit` (and through it OpsTimedMux,
OpsTimed, PipeTimed, LibCtlMergeMux) and `Formal.Cells.ConstraintsMux` (and
through it Bundling, MuxRtzTimed). ConstraintsFastFall is NOT imported: the
FASTFALL part is done in the FIFO (`Ret`) world, see §8. No shared defs added;
Prelim untouched. New top-level names are in namespace `Formal.Cells.OpsTimed`
(no clash with probe Lt's).

The oleans of `ConstraintsMux`, `ConstraintsFastFall` and `OpsTimed2` were
compiled into `.lake/build/lib/lean/Formal/Cells/` with `-o` (as probe Lt did).

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ConstraintsMux.lean -o .lake/build/lib/lean/Formal/Cells/ConstraintsMux.olean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsTimed2.lean -o .lake/build/lib/lean/Formal/Cells/OpsTimed2.olean
    cd .. && ./check.sh Formal/Cells/OpsTimed2.lean      # [check] OK (1708 declarations audited)

`#print axioms` (scratch file importing the olean) on every main theorem and
witness below: `[propext, Classical.choice, Quot.sound]` only.

Negative controls (scratch copies, proof-level): replacing `Wx.lo` by `Wx.hi`
in `S_Z_X` breaks `mux_data_ok` (omega); replacing `Wzx.hi` by `Wzx.lo` in
`S_SEL_XA_Z` breaks `merge_data_ok` (omega). Both obligations are load-bearing
in the proofs. These are not counter-traces (no trace showing the cell fails
when the inequality fails); exactness is not claimed.

## (b) The data path

### bd_mux (`mux_data_ok`, `mux_value_ok_static`)

Model: `bd_datamux` bit = Bundling window relation over the REAL INIT
(`8'hE4`, or `64'hFFAA_5500_E4E4_E4E4` O5/O6), turned into `DmRel` (Kleene
`s ? b : a` over pin windows) by ConstraintsMux's `dm_odd_rel` /
`dm_pair_o5_rel` / `dm_pair_o6_rel`. The theorem is stated on `DmRel`, so it
holds for every bit of every LUT shape (bits are independent by the `*_kleene`
lemmas). Each pin's window `[lo, hi]` = routed wire + site pin + LUT arc from
the DRIVER (control sender's `s`, client's data net).

Sender contracts (`MuxDataEnv`, named): `H_S_DATA/H_X_DATA/H_Y_DATA` (the
token's value held on `[S, E]` at the driver), `H_*_LEAD` (settled `L*` before
the sender's request rises: the upstream's own bundling), `H_*_HOLD` (held
until the sender has SEEN its acknowledge RISE: control sender through `Wzc`,
clients at their pins). The library's contract (bd_ctl.v: held "from
req-rise until ack-fall") implies these, so the theorem needs less than the
library promises.

**`mux_data_ok`**: for every control token `k` and every `t` with
`Z(2k) ≤ t + Mz` and `t ≤ ζ(2k) + holdM k`, `z t = zv k`, where
`zv k = if sv k then yv (idx κ1 k) else xv (idx κ0 k)` (the bit of the token
the control selected), `Z` = z_req at the server, `ζ` = the server's z_ack,
`holdM k = min (Wzc.lo + slo) (Wz?.lo + L?a.lo + W?a.lo + data lo)` (a sum of
MIN delays). Hypotheses: `DmRel`, the two enumerations, `MuxDataEnv`,
`MuxDataStatic`.

**`mux_value_ok_static`**: `mux_ok_static`'s conclusions (one server
transaction per control token; x/y acknowledged exactly in their tokens) AND
`mux_data_ok`, from `MuxCausal` + `MuxStatic` + reset + data contracts +
`MuxDataStatic`, with the same `Wzc`.

Witness (`MuxWit.value_witness`, `value_witness_values`): probe Lt's unit-delay
mux run, `zW` = one odd bit with the real INIT `8'hE4` and unit transport delay
on each pin (window relation by `Bundling.transport_gate`); all hypotheses
proved for every token; delivered bits `zW 14, 32, 50, 68 = 1, 0, 0, 1`
(tokens x, y, x, y), and in tokens 0, 1, 3 the unselected input carries the
opposite bit at that instant (`yd 13 = 0`, `xd 31 = 1`, `xd 67 = 0`).

Finding: the HOLD side of `bundled_z` needs no inequality under the bundled
protocol: each sender holds until it sees its ack, which is after z_ack's rise
at the server (`mux_ζ_le_XA`), so `z` stays valid until `ζ(2k) + holdM`.
Only the SETUP side is an obligation, and it has TWO launches, not the JSON's
one (see the table).

### bd_merge (`merge_data_ok`)

Model: `usel` (`LUT2 4'hE`, pins x_req `[lr, hr]`, x_ack = uxa's output net
`[lq, hq]`) and the datamux (`.a(y_data), .b(x_data), .s(sel)`), both window
relations of the REAL INITs; the uxa node is the token trace from probe Lt's
`cel_run`/`cel_node` (re-derived inside the proof exactly as `merge_ok` does).

**`merge_data_ok`**: under `merge_ok`'s environment in causal/static form
(`MergeGates`, `MergeEnv`, `MergeCausal`, `MergeStatic`, reset), the usel and
datamux relations, `MergeDataEnv` (per merged token, owner's data contract)
and `MergeDataStatic`: for every merged token `k` and `t` with
`Z(2k) ≤ t + Mz`, `t ≤ ζ(2k) + Hm`, `z t = if sv k then yv k else xv k`.

* x token: `sel` is high from `x_req` alone (`usel_high`); x_ack is not
  needed under the early window.
* y token: `sel` must be LOW; `usel_low2` (new: separate start times per pin)
  needs x_req low since the previous token's request fall and the uxa node
  low since the previous token's x_ack fall at uxa's output. The latter is
  launched by z_ack's fall (or the request's) and must beat the NEXT owner's
  request through uor and the line to the server: S_SEL_XA_Z / S_SEL_XA_R.
  This is the timed form of the JSON's `bd_merge.isochronic_forks` x_ack
  branch ("broad window").
* Token 0 needs a start-up condition (`H_SEL_START`: uxa's output and usel's
  windows are inside the clean region before the first z_req).

Witness (`MergeWit.value_witness`, `value_witness_values`): probe Lt's
unit-delay merge run with `selW` (real `4'hE`) and `zmW` (real `8'hE4`), unit
transport delays; delivered `1, 1, 0, 0` for tokens x, y, x, y, the other
input carrying the opposite bit each time.

## (d) bd_steer causal/static packaging (`steer_ok_static`)

`SteerCausal` (receiver answers `Er` after its request edge, sender `Es` after
its ack edge, select sender lead `Ls`/hold `Hs` around its request,
positivity) and `SteerStatic` (per-arc). `steer_env_of_static` derives every
field of probe Lt's `SteerEnv` (H_S_PIN via `steer_s_pin_of_wire`, H_ACK_SKEW
via the new `steer_gap_causal` + `fst_order`); `steer_ok_static` is `steer_ok`
under them. `steer_hold_of_ackfall`: the library contract (s held until ack
fall seen) gives H_S_HOLD with `Hs = Wq.lo + Lm + Er + Wm + La.lo + Wk.lo` (a
whole round trip), so S_S_HOLD is then `Wq.hi ≤ Hs + Ws.lo`. Witness
`SteerWit.static_witness`: the unit-delay steer with a select driver one wire
before `u.I1`, `SteerStatic … ` by `decide`.

## (a) Non-empty pulses

`Tok.at_edge` / `Tok.at_gap`: a slot is non-empty iff its edges are strictly
ordered, and then the trace shows the slot's value at the slot's first edge.
So "one NON-EMPTY pulse per token" = strict monotonicity of the derived edges.

* `mux_Z_step`: z_req's edges at the server are a whole round trip apart:
  `Z j + (Es + Kc + wo + Lor.lo + Dz.lo) ≤ Z (j+1)`; causality alone.
  `merge_Z_step` likewise (`Es + Ka + wo + Lor.lo + Dz.lo`).
* `mux_XA_step`, `mux_YA_step`, `merge_XA_step`: x_ack at the client is
  strictly monotone under **S_XA_PW** (new obligation; two forms, launched by
  z_ack and by the join/request): the spread (hi − lo) of `z_ack → uxa →
  client` is below one round trip. This is the per-wire pulse-width > spread
  condition probe Lt asked for, at the ack C-element.
* `mux_pulses`: under `1 ≤ Es`, start-up `H_START`, S_XA_PW, S_YA_PW: every
  phase of z_req, x_ack, y_ack is non-empty; z_req is high at `Z(2k)` and low
  at `Z(2k+1)` for every token; x_ack (y_ack) is high at the start of every
  token selecting x (y) and low after it. Witness `MuxWit.pulses_witness`.
* Not done: the join nodes `j0/j1` individually (their strictness follows the
  same way from `E_le_ζ`/`ζ_le_E`; not written), merge `merge_pulses` wrapper
  (the two step lemmas are there; the wrapper is mechanical).

## (c) FASTFALL = 1 on the request path

Model: in the FIFO world, stage `i ≥ 1` is `s(i+1) t = s i ((H i).σ t) && a
((Tp i).σ t)` (hop path and tap path FIFO; a LUT arc is a read map, so it
distributes over the AND; stage 0 LUT1 a FIFO). The line is not FIFO.

* `and_tok`: AND of two clean four-phase traces is one, rise = later rise,
  fall = earlier fall (`andEdges`), iff-direction not claimed, provided each
  input's fall precedes the other's next rise.
* `ff_tok`: every stage `1..N` of an `FFLine` is a clean four-phase trace on
  `ffE` (recursive: rise = slowest path, fall = fastest), under
  **H_FLUSH_STAGE** (per stage, per token, event form): stage `i`'s fall
  through hop `i` arrives no later than the input's next rise through tap `i`,
  and the tap's fall no later than stage `i`'s next rise through the hop.
  This is ConstraintsFastFall's per-stage flush (`bd_delay[FASTFALL].flush_per_stage`)
  restated for FIFO arcs; `flush_stage_static` is the one-line static
  sufficient form (`fst_order`): `f + H.hi ≤ e(2k+2) + Tp.lo` with `f` an upper
  bound of the stage's fall (ConstraintsFastFall's `fallBound`).
* `mux_ok_fastfall`: `mux_ok` with the line replaced (instantiate the run's
  `Dz := Ret.shift 0`, gates with `zr := ei`, which is sound because no field
  of `MuxTiming` mentions `Dz`): z_req at the server is one clean transaction
  per control token on `ffE H Tp P.Z N`; x/y acks as before.
* Not done: a non-vacuity witness for `ff_tok` / `mux_ok_fastfall`; the
  static unrolling of `ffE`'s fall bound (only the one-step lemma); the merge
  with FASTFALL (the merge's RTL has no FASTFALL parameter, so nothing to do);
  the data side under FASTFALL (the rise of z_req is the slowest path, so the
  setup obligations S_Z_* hold with `Dz.lo` replaced by the min over the
  rise of `ffE`, not written).

## Obligations and `formal/out/cell_constraints.json` (JSON not edited)

EndpointOK form = `launch`; data path (hi); request path (lo); margin. `Kz =
wo + Lor.lo + Dz.lo + Es`, mux `Kc = Wzc.lo + Ec + wc + lj`, merge
`Ka = wz + la + wa + Eo` as in probe Lt.

| Lean name | proposed JSON id | EndpointOK form | status vs JSON |
|---|---|---|---|
| `MuxDataStatic.S_Z_S0/S1` | `bd_mux.bundled_z_s` (new) | launch: `s` settled at the control sender's driver. data: `s` wire → `udat.I0` site pin → udat arc (hi) + `Mz`. request: env lead `Ls` (s settled → ctl_req rise at sender, lo) + ctl_req wire → `uj0.I1` (`uj1.I1`) + uj arc + j → uor wire + uor arc + udly rise + wire to server (lo) | **refines** `bd_mux.bundled_z`, whose launch "join edge" presumes `s` already settled there; proved sufficient (lumped LUT arcs) |
| `MuxDataStatic.S_Z_X/Y` | `bd_mux.bundled_z_data` (new) | launch: x_data (y_data) settled at the client's driver. data: data wire → `udat.I1|I3` (`I2|I4`) site pin → udat arc (hi) + `Mz`. request: env lead `Lx` + x_req wire → `uj0.I0` + uj0 arc + j0 → uor + uor + udly rise (lo) | **missing** in JSON (bundled_z covers only the select cone) |
| (none: hold) | `bd_mux.bundled_z` hold half | no inequality: senders hold until their ack rise is seen; margin `holdM` = sum of MIN delays | JSON has no hold half; this says none is needed beyond the sender protocol |
| `MergeDataStatic.S_ZM_SEL_X` | `bd_merge.bundled_z` | launch x_req rise; data: x_req → usel.I0 + usel arc + sel → udat select + udat arc (hi) + `Mz`; request: x_req → uor.I0 + uor + udly rise (lo) | **match** (same arcs); now inside a whole-cell timed theorem |
| `MergeDataStatic.S_ZM_X/Y` | `bd_merge.bundled_z_data` (new) | launch: data settled at client; data: data wire + udat (hi) + `Mz`; request: lead + req → uor + uor + udly (lo) | **missing** |
| `MergeDataStatic.S_SEL_XR` | `bd_merge.sel_low_xreq` (new) | launch: previous token's request fall; data: x_req → usel.I0 + usel + udat select (hi) + `Mz`; request: `Kz + Ka` + y_req → uor + uor + udly (lo) | **missing** (easy) |
| `MergeDataStatic.S_SEL_XA_Z` | `bd_merge.isochronic_forks` x_ack branch, z_ack form | launch: previous token's z_ack fall at the server; data: z_ack → uxa.I1 + uxa arc + x_ack → usel.I1 + usel + udat select (hi) + `Mz`; request: `Ka` (z_ack → owner's ack C-element → client → next request) + y_req → uor + uor + udly (lo) | JSON entry is `unproved`, `forms: []`; this is a **timed sufficient form** (candidate to fill `forms`) |
| `MergeDataStatic.S_SEL_XA_R` | same entry, request form | launch: previous request fall; data: x_req → uxa.I0 + uxa + x_ack → usel + usel + udat select (hi) + `Mz`; request: `Kz + Ka` + y_req → uor + uor + udly (lo) | as above |
| `MergeDataStatic.S_HM_*` | `bd_merge.bundled_z` hold | pure lower bounds (`Hm + 1 ≤ …lo`) | not an obligation in practice (sum of MIN delays vs consumer hold) |
| `MergeDataStatic.H_SEL_START` | reset: `bd_merge.reset_first` (new) | first token: uxa output and usel clean before the first z_req | missing (start-up) |
| `SteerStatic.S_S_SETUP` | `bd_steer.bundled_s_setup` | launch: `s` settled at its driver; data: s wire → u.I1 (hi); request: lead `Ls` + req wire → u.I0 (lo) | **proved, lumped LUT arc** (the JSON form also has the I1-vs-I0 arc difference; add it as margin) |
| `SteerStatic.S_S_HOLD` | `bd_steer.bundled_s_hold` | launch: req fall at the sender; data: req wire → u.I0 (hi); request: hold `Hs` + s wire (lo); with the library contract `Hs` = a whole round trip (`steer_hold_of_ackfall`) | **proved, lumped** |
| `SteerStatic.S_ACK` | `bd_steer.ack_or_skew` (probe Lt: missing) | `Wa_b.hi ≤ Loop + Wa_b'.lo`, `Loop = Wm + La.lo + Wk.lo + Es + Wq.lo + Lm + Er` | missing in JSON; proved sufficient |
| `S_XA_PW` (`mux_XA_step`, `merge_XA_step`), `S_YA_PW` | `bd_mux.ack_pulse_width`, `bd_merge.ack_pulse_width` (new) | launch z_ack edge: data: z_ack → uxa + uxa arc + x_ack → client (hi); request: same path (lo) + one round trip (`Kc + Kz`, merge `Ka + Kz`) + 1 ps; second form launched by the join/request edge with `Kc + 2Kz` | **missing**; the per-wire pulse-width > spread condition |
| `mux_Z_step` / `merge_Z_step` | none needed | causality alone (+ `1 ≤ Es`) | z_req pulses are never swallowed (FASTFALL=0) |
| `H_FLUSH_STAGE` (`ff_tok`, `mux_ok_fastfall`) | `bd_delay[FASTFALL].flush_per_stage` | per stage: stage fall through hop (hi) ≤ next input rise through tap (lo) | **match** (FIFO-arc version of ConstraintsFastFall's; now composed with the mux) |

## What did not work / not done

* No counter-traces: the new obligations are proved sufficient; their
  necessity is not shown (the negative controls only show they are used).
* Data-side under FASTFALL (S_Z_* with the line's rise path) and a witness
  for the FASTFALL theorems.
* `merge_pulses` wrapper and join-node strictness (mechanical).
* Per-pin LUT arcs: the steer's `u.I1` vs `u.I0` arc and the datamux's
  select-vs-data arc are lumped into the pin windows (the window model does
  carry per-pin windows for udat/usel; the FIFO model for u does not).
* Broad data protocol for the merge (consumer needing data until after its
  own ack falls): `sel` would then need the x_ack term; not done.
* Still not composed into gcd_hw (Phase 3).

## Verdict

**Works.** The value half of bd_mux and bd_merge is now a kernel-checked
timed theorem on top of probe Lt's handshake theorems, with the real datamux
and usel INITs: in every transaction the server sees the selected (mux) or
requesting (merge) client's value from z_req's arrival until after z_ack. The
mux's whole contract (control + value) is one theorem from causal partners
and per-arc static inequalities, with a unit-delay witness whose two inputs
always disagree. The steer has the same causal/static packaging as mux and
merge. Non-empty pulses are proved (z_req from causality alone; acks under a
new pulse-width obligation). FASTFALL=1 lines are handled exactly in the FIFO
model and composed with the mux.

Effort to finish the leftovers: ~0.5 day (FASTFALL witness + data-side under
FASTFALL, merge_pulses wrapper, counter-traces for S_Z_X and S_SEL_XA_Z).
What it buys: gcd's correctness needs "the mux delivers the selected value"
(now proved, per bit, for every token); eight new or refined
`cell_constraints.json` entries (table) including a timed form for the
`unproved` `bd_merge.isochronic_forks` x_ack branch.

## Fidelity per primitive

* **bd_datamux (LUT3 8'hE4, LUT6_2 FFAA_5500_E4E4_E4E4)** and **usel (LUT2
  4'hE)**: Bundling window relation: Kleene closure (H_KLEENE_LUT) of the
  REAL INIT over per-pin windows (wire + site pin + arc), output unconstrained
  when the closure is `x` (glitches allowed). Sound for any transport delay in
  the windows (`transport_gate`); not for inertial rejection wider than the
  window. Grade A- (per-pin windows, Kleene, no metastability).
* **uj0/uj1/uxa/uya/uor/u/uack** (control side): as probe Lt: binary FIFO
  LUT arcs (H_LUT_FIFO), feedback window channels. Grade B.
* **bd_delay FASTFALL=0**: one FIFO channel. **FASTFALL=1**: AND of FIFO
  paths per stage (exact in the FIFO model); no glitches inside a stage's
  window (binary).
* **Wires**: FIFO per fork branch (control); window per pin (data path).
  Mixing: the data theorem reads control-side event times (FIFO model) and
  data-side values (window model) on the same nets; consistent because both
  are bounded-delay models of the same wire, but the two delay parameters
  (Ret lo/hi vs window lo/hi) are separate symbols and must be filled from
  the same route.
* **Partners**: abstract four-phase parties with reaction latencies and data
  holds (`MuxDataEnv`, `MergeDataEnv`, `SteerCausal`).
* **Time**: ℕ ticks.
