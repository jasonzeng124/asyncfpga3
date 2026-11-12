# B probe Lt: timed handshake proofs for bd_steer, bd_mux and bd_merge

Shard B, Phase 2 item B ("prove every cell against a handshake spec"), timed
form, for the three dataflow operators gcd_hw's loop goes through (branch =
`bd_steer`, `bd_mux`, plus `bd_merge`). Style of 6e/6f (`PipeTimed`,
`PipeTimedN`): FIFO LUTs and wires, real INITs, derived event times, every
timing assumption a named field.

## Files and check

All CLAIMED, core Lean (no Mathlib), no `sorry`/`admit`/`axiom`/`native_decide`.

| file | lines | contents | check time |
|---|---|---|---|
| `formal/lean/Formal/Cells/OpsTimed.lean` | ~635 | `Tok`, FIFO transfer, gated functions, `or_tok`; **bd_steer** (`steer_ok`) and its unit-delay witness | ~3 s |
| `formal/lean/Formal/Cells/OpsTimedMux.lean` | ~1270 | sub-sequences (`Enum`, `rx`, `Tok.reindex`, `Tok.lift`), timed gated C-element (`CEl`, `exc_hold`, `cel_run`), **bd_mux** (`mux_ok`), **bd_merge** (`merge_ok`), and both derived from port-level causality + static per-arc inequalities (`mux_timing_of_static`, `mux_ok_static`, `merge_timing_of_static`) | ~12-21 s |
| `formal/lean/Formal/Cells/OpsTimedWit.lean` | ~490 | unit-delay non-vacuity witnesses for mux and merge (causal partners, static obligations, kernel-evaluated sample values) | ~8 s |

Imports (read-only): `Formal.Cells.PipeTimed` (for `Ret`, `fifo_*`, `lfind`;
through it LinkTimed/CElemTiming/Bundling/LinkHandshake) and
`Formal.Cells.LibCtlMergeMux` (the INITs and their equations). No new shared
definitions outside these files; Prelim untouched.

Check commands (oleans of my own files were compiled into
`.lake/build/lib/lean/Formal/Cells/` with `-o` so that the later parts import
the earlier ones):

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsTimed.lean -o .lake/build/lib/lean/Formal/Cells/OpsTimed.olean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsTimedMux.lean -o .lake/build/lib/lean/Formal/Cells/OpsTimedMux.olean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsTimedWit.lean
    cd .. && ./check.sh Formal/Cells/OpsTimed.lean   # [check] OK (likewise OpsTimedMux, OpsTimedWit)

`#print axioms` (scratch file importing the oleans): every main theorem uses a
subset of {propext, Classical.choice, Quot.sound}; `witness_routes` /
`witness_values` (kernel `decide` on the simulated traces) use only propext.

Negative control (scratch copy): weakening `cel_run`'s departure condition
from `c + L.hi + wh` to `c + L.hi` (dropping the feedback wire) breaks the
proof in 9 places (omega), so the C-element's feedback-wire term is
load-bearing (the same finding as MuxRtzTimed's negative control, here at the
level of the whole four-phase run).

## Model (one paragraph per primitive)

* **Token traces.** `Tok T x e g`: from `T` on, `x` is low before `e 0`,
  shows gate `g k` on `[e(2k), e(2k+1))`, low on `[e(2k+1), e(2k+2))`. A clean
  four-phase request is gate `true`; a branch of a steer has gate "token `k`
  routed here" (low for the whole slot otherwise).
* **LUTs.** Output = Boolean function of the pins, from the REAL INIT through
  `Prelim.lutB` (`req0B/req1B` = `o5B/o6B` of `0x8888888822222222`, `or2B` =
  `4'hE`, `c2B` = bd_c2 `0x00E800E800E800E8`, `j0B/j1B` = `0x0000AE080000AE08`
  / `0x0000EA800000EA80`), read through a FIFO bounded delay (`Ret`,
  **H_LUT_FIFO**, 6e). The equations used (`steer_req0/1`, `or2_spec`,
  `c2_spec`, `j0_spec`, `j1_spec`) are LibCtlMergeMux theorems over the INITs.
* **Feedback LUTs** (uj0, uj1, uxa, uya): `CEl`: the function is proved to be
  `~rst · C(a, b)` (`a, b` = `x_req, ctl_req·~s` for uj0); the own-output
  feedback net is a window channel `[wl, wh]` (non-FIFO allowed).
* **Wires.** Every fork branch is its own FIFO channel (`H_WIRE_FIFO`); no
  fork is assumed isochronic: fork skews appear as explicit inequalities.
* **bd_delay** (FASTFALL = 0): one FIFO channel (a symmetric LUT1 chain is
  FIFO by `PipeTimed.fifo_comp`), `H_LINE_FIFO`.
* **Partners.** Event times (`ρ`, `ξ`, `η`, `γ`, `ζ`, `A`) with clean `Tok`
  traces at their ports; their causality is either stated against the derived
  edges (`*Env`/`*Timing`, event form) or as port-level reaction latencies
  (`MuxCausal`, `MergeCausal`), from which the event form is derived.

## Theorems

### Shared machinery
* `Tok.fifo`: through a FIFO channel a token trace stays one, every edge moved
  to `Ret.fst` of itself, gates unchanged.
* `Tok.gate`: `f (x t) (s t)` with `f false _ = false` and `s` holding the
  token's value while `x` is high is a token trace with gate `f true (sv k)`
  (the steer's two outputs, the mux's control decode).
* `or_tok`: OR of two exclusively gated token traces is a clean four-phase
  trace on the selected input's edges, provided each pin's edge precedes the
  other pin's next edge (**H_OR_SKEW**).
* `Enum`, `idx`, `rx`, `Tok.reindex`, `Tok.lift`: the mux's sub-sequences.
  `κ0` enumerates the control tokens selecting x; a control-indexed trace low
  in every slot not selecting x is, on `rx e κ0`, a clean x-indexed trace, and
  back (`lift` needs the control-indexed edges monotone).
* `exc_hold`, `cel_run`, `cel_node`: **timed four-phase run of a gated
  C-element.** Inputs token traces on `ea`, `eb` with gates `ga`, `gb`; reset
  high on `[0,R)`, released before the first edge; every input leaves its
  phase value at least `L.hi + wh` after the phase start
  `max (ea j) (eb j)` (**H_DEP**, 5b's env latency). Then the excitation is the
  token trace on `max (ea j) (eb j)` with gate `ga k && gb k`, and the node the
  same through the FIFO arc. A slot where only one input pulses (a server
  transaction for the other mux input) leaves the C-element low: that slot's
  safety is exactly the H_DEP instance at its start, which for uxa against the
  next z_ack edge is **H_MUX_RTZ**.

### bd_steer (`OpsTimed.lean`)
* `steer_fwd`: receiver 0's request pin is `Tok` on `R0` with gate `!sv k`,
  receiver 1's on `R1` with gate `sv k`: **each token reaches exactly the
  branch its condition names; the other branch is low for the whole slot.**
  Needs only the gates, a clean request and **H_BUNDLED_S_PIN**.
* `steer_back`: the sender's acknowledge pin is a clean four-phase trace on
  `K` (one acknowledge per token), given the receivers acknowledge only their
  own tokens (H_RCV_QUIET, `Tok` with gates on common edges `A`) and
  **H_ACK_SKEW** at `uack`.
* `steer_ok`: both, plus the order of a four-phase cell (`ρ j ≤ Rsel j`,
  `Rsel j + Er ≤ A j`, `A j ≤ K j`, `K j + Es ≤ ρ (j+1)`).
* `steer_s_pin_of_wire`: static form of H_BUNDLED_S_PIN:
  setup `sS k + Ws.hi ≤ ρ(2k) + Wq.lo`, hold `ρ(2k+1) + Wq.hi ≤ sE k + Ws.lo`.
* `steer_gap`: consecutive acknowledge edges are a whole sender round trip
  apart, so H_ACK_SKEW follows from the static
  `Wa_b.hi ≤ Wa_b'.lo + Loop` (via `fst_order`),
  `Loop = min(Wa.lo) + La.lo + Wk.lo + Es + Wq.lo + min(L5.lo+W0.lo, L6.lo+W1.lo) + Er`.
* `SteerWit.witness`, `witness_routes`: unit delays, `sv` alternating, `s`
  changing mid-idle; all hypotheses proved for every token; `r0 4 = 1, r1 4 = 0,
  r0 20 = 0, r1 20 = 1, ack 8 = ack 24 = 1`.
  **Scope (self-audit correction).** This run witnesses `steer_ok` (every field of
  `SteerGates` and `SteerEnv`: `SteerWit.gates`, `SteerWit.env`) and, via
  `OpsTimed2.SteerWit.static_witness`, `steer_ok_static`. It is NOT a witness of
  `ContractsB.steer_contract`, whose extra hypotheses `H_T1` (`T1 Tr ≤ R0 (2·κ false 0)`)
  and `H_T2` (`T2 Ta ≤ K 0`) it violates: `SteerWit.not_H_T1` (`¬ T1 Tr ≤ R0 0` for every
  `Tr`: `T1 Tr ≥ 5 > R0 0 = 4`) and `SteerWit.not_H_T2` (`T2 6 = 10 > K 0 = 8`). `H_T1` is
  not a hypothesis of `steer_ok`/`steer_ok_static`, so nothing in this file is unwitnessed;
  `steer_contract`'s witness is `SelfAuditB4.steer_contract_witness` (ContractsTruncWit's run,
  first request at 9). Caveat: the unit-delay windows `T1 0 = 5`, `T2 6 = 10` start after the
  first branch request (4) and first acknowledge (8), so `witness`'s `Tok` conclusions cover
  token 0 only from those times on; `witness_routes` checks token 0 directly.

### bd_mux (`OpsTimedMux.lean`)
* `mux_E_mono`: the selected join's node edges `E` (control-indexed, defined
  from the x-/y-indexed join edges through `idx`) form one nondecreasing
  sequence (from H_DEP_J* and H_CTL_SEQ).
* **`mux_ok`**: under `MuxGates` (real INITs), `MuxEnv` (clean partners,
  enumerations, H_BUNDLED_S_PIN at both joins) and `MuxTiming`:
  (1) `j0` is `Tok` on `E` with gate `!sv`, `j1` with gate `sv`: each join
  fires exactly for the control tokens selecting its input, once per token;
  (2) `z_req` at the server is a clean four-phase trace on `Z`: **one server
  transaction per control token**; (3) `x_ack` at the x client is `Tok` on `XA`
  with gate `!sv` and, reindexed, a clean trace on x's own tokens: **each x
  token acknowledged exactly once, in the control token that selected it, and
  never during a y transaction** (y symmetric); (4) order: the join for x's
  `m`-th token fires only after both x's request and control token `κ0 m`
  reached it; each acknowledge rises after the server's.
* `mux_timing_of_static`: every field of `MuxTiming` except reset sequencing
  is DERIVED from port-level causality (`MuxCausal`: x/y drop/raise `Ex`/`Ey`
  after seeing their acknowledge, the control sender moves `Ec` after seeing
  ctl_ack = z_ack through its wire `Wzc`, the server `Es` after z_req) and the
  static per-arc inequalities of `MuxStatic` (table below). `H_CTL_SEQ` needs no
  static condition at all (causality alone).
* `mux_ok_static`: `mux_ok`'s conclusions (2)-(3) from the static form.
* `MuxWit.*`: unit delays, period 18 ticks per control token, alternating
  selection, each input raising its request during the other input's
  transaction (it waits at its join: `y 24 = 1`, `j1 24 = 0`); the partners
  are causal (`MuxCausal run uW 1 1 1 1`), `MuxStatic` holds by `decide`, and
  `MuxTiming` is obtained through `mux_timing_of_static`; `mux_ok` applied.
  Sample values: `xak 17 = 1, yak 17 = 0, xak 35 = 0, yak 35 = 1, zr 13 = zr 31 = 1`.

### bd_merge (`OpsTimedMux.lean`)
* **`merge_ok`**: under `MergeGates`, `MergeEnv` (H_MERGE_SEQ's shape: x's and
  y's requests are the two halves of ONE sequence of four-phase transactions
  on common edges `ρ`, owner `sv k`) and `MergeTiming`: `z_req` is one clean
  transaction per merged token; `x_ack` pulses exactly in x's tokens and
  `y_ack` exactly in y's (**each server transaction acknowledges exactly the
  client that requested it**), each after its z_ack rise; `z_req`'s edge
  follows the requesting client's edge.
* `merge_timing_of_static`: `MergeTiming` from `MergeCausal` (owner drops
  `Eo` after its ack rises, NEXT requester raises `Eo` after the previous
  owner's ack fell = H_MERGE_SEQ causal form, server `Es`) and `MergeStatic`.
* `MergeWit.*`: unit delays, alternating owners, causal partners, static
  obligations by `decide`, `merge_ok` applied; `xak 11 = 1, yak 11 = 0,
  xak 27 = 0, yak 27 = 1`.

## Timing obligations and `formal/out/cell_constraints.json`

Notation: `Kz = wo + Lor.lo + Dz.lo + Es` (join/request edge → z_ack edge, min);
mux `Kc = Wzc.lo + Ec + wc + lj` (z_ack edge → next join edge through the
control sender, min); merge `Ka = wz + la + wa + Eo` (z_ack edge → next
request through an ack C-element and a client). `wo, wc, lj, wz, la, wa` are
lower bounds of the corresponding pair of arcs.

| cell | name (Lean) | static form | JSON id | status |
|---|---|---|---|---|
| all | H_LUT_FIFO, H_WIRE_FIFO, H_LINE_FIFO | (not inequalities) | `hypotheses_not_inequalities` H_LUT_FIFO / H_PIN_FIFO | match |
| steer | `SteerEnv.H_S_PIN` | `steer_s_pin_of_wire`: `sS+Ws.hi ≤ ρ(2k)+Wq.lo`, `ρ(2k+1)+Wq.hi ≤ sE+Ws.lo` | `bd_steer.bundled_s_setup`, `bd_steer.bundled_s_hold` (added to the JSON during this probe, status `unproved`, "no timed theorem") | match with LUMPED LUT arcs: `steer_fwd` + `steer_s_pin_of_wire` is a timed sufficiency proof of both; the JSON's form also carries the `u.I1→O` vs `u.I0→O` per-pin arc difference, which this model does not have (add it as a margin) |
| steer | `SteerEnv.H_ACK_SKEW` | `Wa_b.hi ≤ Wa_b'.lo + Loop` (`steer_gap`, `fst_order`) | none | **missing**: `bd_steer.ack_or_skew` |
| steer | `H_RCV`, `H_SND`, `H_RCV_QUIET` | partner protocol | none | protocol (not a cell constraint) |
| mux | `MuxEnv.H_S_PIN0/1` | pin form (static form as steer) | `bd_mux.bundled_s_setup`, `bd_mux.bundled_s_hold` | match (pin form; now a premise of a timed theorem) |
| mux | `H_DEP_J0/J1` ← `S_J0_X`, `S_J1_Y` | `Lj.hi + wjh ≤ Lj.lo + Wjx.lo + Lxa.lo + Wxa.lo + Ex + Wx.lo` | `bd_c2.env_latency` is per bd_c2; uj0/uj1 are a different INIT | **missing**: `bd_mux.uj_env_latency_req` |
| mux | `H_DEP_J0/J1` ← `S_J0_C`, `S_J1_C` | `Lj.hi + wjh ≤ Lj.lo + Kz + Wzc.lo + Ec + Wc.lo` | none | **missing**: `bd_mux.uj_env_latency_ctl` |
| mux | `H_CTL_SEQ` | none needed (from causality) | `bd_mux.isochronic_forks` (ctl_req branch) | refinement: under H_WIRE_FIFO the `ctl_req -> {uj0,uj1}` fork needs no condition (MergeMuxSI's `mux_needs_iso_cr` is a two-transitions-on-one-wire hazard, which a FIFO wire excludes by assumption) |
| mux | `H_OR_SKEW` ← `S_OR` | `W0o.hi ≤ Kz + Kc + W1o.lo` (and symm.) | none | **missing**: `bd_mux.or_skew` |
| mux | `H_DEP_XA/YA` ← `S_XA_RTZ`, `S_YA_RTZ` | `Wzx.hi + Lxa.hi + wxah ≤ Wzx.lo + Kc + Kz` | `bd_mux.uxa_rtz_env`, `bd_mux.uya_rtz_env` | match (same arc set as MuxRtzTimed's H_RTZ_ENV / ConstraintsMux's uya instance), here as part of a whole-cell theorem |
| mux | `H_DEP_XA/YA` ← `S_XA_FORK`, `S_YA_FORK` | `Wzx.hi + Lxa.hi + wxah ≤ Kc + W0x.lo` | `bd_mux.isochronic_forks` (z_ack branch) | the JSON entry is `unproved` with empty `forms` ("needs a timed mux trace model"; "missing is 'same transition seen consistently' between branches"). `mux_timing_of_static` + `mux_ok` give a timed sufficient form: with FIFO branches, consistency is automatic, and the numeric condition is S_*_FORK (z_ack branch) plus nothing for the ctl_req branch. Candidate to mark `proved` (sufficient, lumped arcs) |
| mux | `H_DEP_XA/YA` ← `S_XA_J`, `S_YA_J` | `W0x.hi + Lxa.hi + wxah ≤ Kz + Kc + W0x.lo`, `≤ 2Kz + Kc + Wzx.lo` | generic `bd_c2.env_latency` at uxa (j input) | partial: JSON's env_latency is the generic form; this instance (join→uxa wire) is **missing** as an arc-level entry |
| mux, merge | `H_RST_LONG`, `H_RST_EARLY` | reset ≥ every wire/loop hi; released before first edge at each C-element | `bd_c2.reset_width` (width only) | **missing**: "released before first edge" for uj0/uj1/uxa/uya |
| mux | (data) | not covered | `bd_mux.bundled_z` | not covered here |
| merge | `MergeEnv.H_X/H_Y` + `MergeCausal.H_OWN` | partner protocol | `bd_merge.seq` | match (timed shape + causal form) |
| merge | `S_OR` | as mux, with `Ka` | none | **missing**: `bd_merge.or_skew` |
| merge | `S_XA_FORK`, `S_YA_FORK` | `Wzx.hi + Lxa.hi + wxah ≤ Ka + Wxc.lo` | `bd_merge.isochronic_forks` (z_ack branch; JSON `unproved`), `bd_merge.seq` (timing part) | timed sufficient form for the z_ack branch; the x_ack branch (broad data window via `usel`) is not covered |
| merge | `S_XA_ZA`, `S_YA_ZA` | `Wzx.hi + Lxa.hi + wxah ≤ Wzx.lo + Ka + Kz` | `bd_merge.uxa_feedback` | match |
| merge | `S_XA_R`, `S_YA_R` | request edge at uxa outlasts loop | generic `bd_c2.env_latency` | partial (arc-level instance missing) |
| merge | (data select `usel`) | not covered | `bd_merge.bundled_z`, `bd_merge.isochronic_forks` (x_ack branch, broad window) | not covered here |

The JSON on disk was regenerated during this probe (commit ab76c0f, 87
entries): it gained `bd_steer.bundled_s_setup/hold` (unproved) and
`bd_mux.uya_rtz_env` became proved (ConstraintsMux). The table above is
against that version.

Obligations the JSON lacks (report): `bd_steer.ack_or_skew`, `bd_mux.or_skew`,
`bd_merge.or_skew`, `bd_mux.uj_env_latency_req`, `bd_mux.uj_env_latency_ctl`,
arc-level `env_latency` instances of uxa/uya against their request/join
input, reset "released before first edge" for the ops' C-elements, and
(not proved here, see below) a per-wire pulse-width-vs-spread condition.

## What did not work / not done

* **Pulse non-emptiness is not a theorem.** `Tok` allows a slot of zero length
  (a FIFO channel may swallow a pulse shorter than its spread). The
  conclusions say each token's pulse is the right one and in the right place,
  and the witnesses show the pulses are non-empty, but "exactly one NON-EMPTY
  pulse per token" in general needs a pulse-width > spread condition per
  channel (cf. `bd_delay[sym].pulse_width`, PipeTimedN's `live`). For the join
  and ack nodes it follows from H_DEP (not written out). ~0.5 day.
* **Data path not covered**: `bd_datamux` / z_data (mux) and `usel` / z_data
  (merge), i.e. `bundled_z` and the merge's broad select window. The select
  pin's bundling is LinkTimed/Bundling-style and would reuse `Tok.gate`. ~0.5-1 day.
* **FASTFALL = 1** delay line (bdc emits it with `BDC_LINK_FASTFALL=1`): not
  covered; the line is assumed symmetric FIFO. PipeTimedN's `fastrise_or` is the
  dual model to reuse. ~0.5 day.
* **The steer's obligations are only partly in static form**
  (`steer_gap`, `steer_s_pin_of_wire`); no `SteerCausal`/`SteerStatic`
  packaging like the mux's. ~1 h.
* **Not composed into gcd_hw** (Phase 3). The interfaces compose (every
  output is a `Tok` that is the next cell's input), but a cyclic graph needs
  the event times defined by recursion on (phase, node) as in PipeTimedN.
* Binary model only: no X / runts beyond FIFO swallowing; single-X glitch
  freedom of every INIT is LibCtlMergeMux's. Lumped LUT arcs, no per-pin arcs.
* Behaviour before `T` (power-up, during reset) is unconstrained.

## Verdict

**Works.** bd_steer, bd_mux and bd_merge each have a kernel-checked timed
theorem in the LinkTimed/PipeTimed style: real INITs, FIFO LUTs and wires,
window feedback nets, derived event times, and a handshake spec for every
token (steer: routes each token to its branch only; mux: transfers exactly the
selected input once per control token, never acknowledging the other; merge:
each server transaction acknowledges exactly its requester). For mux and merge
every timing obligation except reset sequencing is reduced to per-arc static
inequalities under port-level causal partners; H_MUX_RTZ falls out as one of
them with exactly MuxRtzTimed's arc set, and the JSON's two `unproved`
isochronic-fork entries and the two `unproved` steer select entries get
timed sufficient forms (lumped LUT arcs). Each cell has a unit-delay non-vacuity witness with
causal partners and alternating selection.

Effort to finish: non-empty pulses ~0.5 day; data/select path ~0.5-1 day;
FASTFALL=1 ~0.5 day; gcd_hw composition (event-time recursion over the graph)
2-3 days. What it buys: the operator half of Phase 3's composition (fork/join
from CTree, buffer from PipeTimedN, these three here), seven obligations to
add to `cell_constraints.json`, and proofs for four of its `unproved` entries.

## Fidelity per primitive

* **LUT6 / LUT2 / LUT6_2 (u, uack, uor, uj0, uj1)**: binary function of the
  real INIT through `lutB` (via LibCtlMergeMux), lumped FIFO arc
  (H_LUT_FIFO: one transition in, one out; a pin change that leaves the
  function unchanged gives no glitch). LUT6_2: O5 and O6 are two FIFO arcs of
  the same pin values. Grade B (no per-pin arcs, no X).
* **bd_c2 (uxa, uya) and the joins' feedback**: LUT as above plus the routed
  own-output net as a window channel `[wl, wh]` (non-FIFO allowed); `rst` a
  trace with a release time.
* **Wires**: one FIFO channel per fork branch, never isochronic by assumption.
* **bd_delay**: one FIFO channel (FASTFALL = 0 only).
* **Partners**: abstract four-phase parties (event times, clean traces at
  their ports, reaction latencies).
* **Time**: ℕ ticks.
