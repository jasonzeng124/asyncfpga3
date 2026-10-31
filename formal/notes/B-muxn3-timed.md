# B probe Mn: timed `bdc_muxn3_32` (gcd_hw's 3-way loop header)

Shard B, follows Cm (`B-amerge.md`: `MuxN3`/`MuxN3Proof`, speed-independent)
and Lt/Lt2/Lt3 (`B-ops-timed.md`, `B-ops-timed2.md`, `B-ops-counter.md`:
timed `bd_mux`). 2026-10-27. No route, no board, no GLS: nothing below is a
routed number, and no nextpnr was run (no fingerprint applies).

## File and check

| file | contents | check time |
|---|---|---|
| `formal/lean/Formal/Cells/MuxN3Timed.lean` | §1 gate facts (`selF_idx`, `selF_off`, `or3_spec`, `dm5_sel`, `tok_gate2`, `or3_same`, `ffE_ge`, copy of Lt3's `Tok.retime`); §2 `MN3Run`/`MN3Gates`/`MN3Env`/`MN3Timing`/`MN3Causal`; §3 event lemmas; §4 **`muxn3_ok`**; §5 `MN3Static`, **`muxn3_timing_of_static`**, **`muxn3_ok_static`**; §6 **`muxn3_s_pin_of_static`**; §7 **`muxn3_data_ok`**; §8 unit-delay witness `Mn3Wit` | see below |

CLAIMED, core Lean (no Mathlib), no `sorry`/`admit`/`axiom`/`native_decide`.
Imports (read-only): `Formal.Cells.OpsTimedMux`, `Formal.Cells.OpsTimed2`
(brings OpsTimedWit, ConstraintsMux, Bundling), `Formal.Cells.MuxN3` (brings
AMergeGates: the inferred INITs and their equations). No shared definitions
added; Prelim untouched. Namespace `Formal.Cells.MuxN3Timed` (no clashes).
`tok_slot_of`/`tok_retime` are a verbatim copy of `OpsCounter`'s
`Tok.slot_of`/`Tok.retime` (OpsCounter is not imported, to keep the import
set to the three files the brief names).

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/MuxN3Timed.lean

Checks clean (no output), about 15-20 s, under 1 GB. `cd .. && ./check.sh
Formal/Cells/MuxN3Timed.lean` prints `[check] OK` (2893 declarations
audited). `#print axioms` (scratch copy): every theorem below uses a subset
of {propext, Classical.choice, Quot.sound}; `witness_values`, `data_values`
use only propext. Kernel `decide` on simulated traces runs to t = 135 with
`maxRecDepth 100000` (set locally on those theorems only). No olean was
written (OpsTimed2's olean was being rebuilt by the lead's `lake build`
during the probe; the check above ran after it had finished).

## Model (what each primitive is)

As Lt/Lt2, generalised to an input index `i ∈ {0,1,2}` (every per-input
delay is a function of `i`):

* **decode `sel_i`** (inferred LUT3 `8'h10` / `8'h40` / `8'h40`, pin maps of
  H_YOSYS_MAP): `selF i` = `AMergeGates.sel0/1/2` = `lutB` of the INIT. Lumped
  FIFO arc `Ls i` (H_LUT_FIFO), its three pins read at one instant: the
  per-pin arc difference (s pin vs ctl pin) is folded into the pin wires.
  `selF_idx` (proved from the INITs): with the bits of `v < 3` on the s pins,
  `sel_i = ctl_req · (v = i)`; `selF_off`: `sel_i = 0` while ctl_req is low.
* **wire `sel_i -> uj_i.I1`** (`Wsj i`): the gate+wire bd_mux does not have.
* **joins `uj_i`, acks `ua_i`** (`bd_c2`, REAL INIT `0x00E8_00E8_00E8_00E8`
  through `LibCtlMergeMux.c2B`): Lt's `CEl` (FIFO arc + own-output window
  `[wl, wh]`), run by Lt's `cel_run`/`cel_node`.
* **`|j`** (inferred LUT3 `8'hFE`, `or3_spec`): FIFO arc `Lo`. The three join
  pins are first RE-TIMED (Lt3's `Tok.retime`, copied as `tok_retime`) onto
  the selected join's edges `Sor`, then OR-ed on common edges (`or3_same`): no
  skew condition between the three `j -> |j` wires is needed (Lt3's finding
  for bd_mux's `uor`, here for three pins).
* **`uor` + `bd_delay_gated`** (FASTFALL = 1, what gcd_hw emits): Lt2's
  `FFLine` with input AND gate net `|j`; stage 0 reads `|j` through the
  composite FIFO path `H 0` = `|j -> uor (LUT1) -> wire -> LUT1`
  (`PipeTimed.fifo_comp`); AND stage `i` reads its hop `H i` and the tap
  `Tp i` from `|j`. z_req at the server = stage `N` = DELAY. H_FLUSH_STAGE
  per stage (Lt2's `ff_tok`) is an event-form field; `ffE_ge` (new): every
  line edge is at least `Dl` after its input edge if `Dl ≤ (H 0).lo` and
  `Dl ≤ (Tp i).lo` (conservative for rise edges, which take the slowest path).
* **data LUT5** (`32'hF0AA_CCF0`, pins `I0 in2, I1 in1, I2 in0, I3 s0, I4 s1`):
  Bundling `Gate` (Kleene closure over per-pin windows from the drivers).
  `dm5_sel` (kernel-checked on the INIT): with definite index bits of `v < 3`,
  the output is the selected pin's reading WHATEVER the other two data pins
  read, `x` included.
* **wires**: every fork branch its own FIFO channel; no fork isochronic.
* **partners**: four-phase traces with event times; port-level causal
  latencies `Ex` (clients), `Ec` (control sender, sees z_ack through `Wzc`),
  `Es ≥ 1` (server).
* **time**: ℕ ticks.

## Theorems

* **`muxn3_ok`** (event form): under `MN3Gates` (real INITs), `MN3Env`
  (clean partners, **H_S_RANGE** `sv k < 3`, enumerations, **H_S_PIN** at each
  decode), `MN3Timing` (reset, H_DEP_J per join, H_DEP_A per ack, line flush,
  `1 ≤ N`) and `MN3Causal` (used only to order the selected edges):
  (1) join `i` is `Tok` on the selected-join edges `E` with gate `sv k = i`:
  it fires exactly in the control tokens selecting `i`, once per token;
  (2) `|j` and z_req at the server are one clean four-phase transaction per
  control token; (3) `in_i_ack` pulses exactly in the tokens selecting `i`
  (control-indexed) and is a clean trace on input `i`'s own tokens: **only
  the selected input is acknowledged, once per control token; the other two
  keep their tokens**; (4) order: join `i` fires for its `m`-th token only
  after both its request and its decode arrived; every ack rises after the
  server's z_ack.
  `E_step`: `E j ≤ Sor j < E (j+1)` from causality alone (no H_CTL_SEQ, no
  OR skew).
* **`muxn3_timing_of_static`**: every field of `MN3Timing` except reset
  sequencing and the line flush is DERIVED from `MN3Causal` and the per-arc
  `MN3Static` (table below). **`muxn3_ok_static`**: `muxn3_ok`'s (1)-(3) from
  that form.
* **`muxn3_s_pin_of_static`**: H_S_PIN at every decode from the s wires
  `Ws0 i`, `Ws1 i`, the control sender's data contract (bits valid on
  `[sS k, sE k]`, lead `Lsd` before ctl_req rises, held until the sender has
  SEEN ctl_ack FALL, the `bdc_muxn` header's contract) and two static
  inequalities per pin (S_S_SETUP, S_S_HOLD).
* **`muxn3_data_ok`**: for every control token `k`, from `Mz` before z_req
  reaches the server until `Hm` after z_ack rises, the LUT5 output bit equals
  input `sv k`'s bit for the token `k` consumes (`idx (κ (sv k)) k`), under
  `MN3DataEnv` (senders' hold/lead contracts) and `MN3DataStatic`.
* **`rtz_of_fork_j`**: S_A_RTZ follows from S_A_FORK and S_A_J's second half
  whenever the z_ack branch's spread is at most the j branch's (e.g. any
  fixed-delay run). Consequence below.
* **Non-vacuity `Mn3Wit`**: unit delays, DELAY = 1, control token `k`
  selects `k % 3` (each input selected infinitely often), each client raises
  its request during the previous (other input's) token and waits.
  `causal`, `static` (all `MN3Static` fields), `timing` (DERIVED via
  `muxn3_timing_of_static`), `witness` (= `muxn3_ok` applied), `s_pin_static`
  (H_S_PIN obtained from `muxn3_s_pin_of_static`, S_S_SETUP tight with
  equality), `witness_values` (kernel: in0_ack high at 40 and in1/in2_ack low;
  in1_ack only at 60; in2_ack only at 80; z_req high at 35, 55, 75, low at 50;
  input 1's request high at 30 while its join is low). Data: `zW_gate` (real
  LUT5 INIT, one-tick transport per pin), `data_env`, `data_static`,
  `data_witness` (= `muxn3_data_ok` applied), `data_values`: delivered bits
  `1,0,1,0,1,0` in tokens 0..5 (inputs 0,1,2,0,1,2) and in each token an
  unselected input carries the opposite bit at that instant (expected values
  come from the run's `xvW`, not from simulation output).
* **Counter-run `Mn3Cex` (s_setup, one tick)**: same cell and control timing,
  clients re-request as early as causality allows (`Ex = 1`, so the client the
  previous token selected is waiting when the next token starts).
  `bnd_ok`: s wires 1 tick (S_S_SETUP with equality): H_S_PIN via
  `muxn3_s_pin_of_static`, then `muxn3_ok_static` applies (all hypotheses
  proved). `cex_setup_violated`: s wires 2 ticks: S_S_SETUP fails by one
  tick, S_S_HOLD holds; every other hypothesis is the same proof term
  (`gates d` is parametric in the wire delay, `H_X`, `causal`, `static`,
  `s_data`, `s_lead`, `s_hold`). `cex_values`/`cex_fails`: in the violating
  run every decode reads the previous token's index for one tick, decode 0
  emits a one-tick runt at the start of token 1 (which selects input 1), the
  waiting client 0's join takes it: join 0 is high at 52 ∈ `[E 2, E 3)`, so
  `Tok (j 0) E (g 0)` (conclusion (1) of `muxn3_ok`) is FALSE, and in0_ack is
  high at 59, in token 1: input 0's token is consumed by the wrong control
  token. In the boundary run both are low. (The traces show more: the runt is
  shorter than the join's two-tick loop, and join 0 and in0_ack oscillate with
  period 2 for the rest of token 1, a ring through the C-element's feedback.)
  This is exact in this run family (boundary holds, boundary + 1 fails).

## The five `bdc_muxn` entries of `formal/out/cell_constraints.json` (JSON NOT edited)

Notation (all lower bounds over the three inputs unless indexed):
`Kz = wo + Lo.lo + Dl + Es` (selected join node edge → server's z_ack edge:
j → `|j` pin wire, `|j` LUT3 arc, line (stage-0 composite path / taps, min),
server); `Kj = wc + ls + wsj + lj` (ctl_req at its driver → selected join
node: wire to `sel_m.I2` + SP, decode arc, wire `sel_m → uj_m.I1` + SP, join
arc); `Kc = Wzc.lo + Ec + Kj` (z_ack edge → next join node through the
control sender). Proposed EndpointOK forms (data path hi + margin ≤ request
path lo, from the common launch), each proved SUFFICIENT inside the whole
cell theorem with lumped LUT arcs (pin windows carry site pins):

| JSON id | Lean field | EndpointOK form | status |
|---|---|---|---|
| `bdc_muxn.rtz` | `MN3Static.S_A_RTZ` (→ `MN3Timing.H_DEP_A`, 2nd half, odd `j`) | launch: z_ack edge at its driver. data: z_ack → `ua_k.I1` wire + SP (hi) + `ua_k` arc (hi) + feedback wire + SP `ua_k.O6 → ua_k.I2` (hi). request: z_ack → `ua_k.I1` (lo) + `Wzc` (z_ack → ctl sender, lo) + `Ec` + ctl_req → `sel_m.I2` + decode arc + `sel_m → uj_m.I1` + `uj_m` arc (`Kj`, lo) + `uj_m → |j` wire + `|j` arc + line (lo) + `Es`. Margin 0. Per `k`, `m` any. | **proved sufficient** (`muxn3_timing_of_static` + `muxn3_ok`). Same arc set as the JSON's transcription (which has `|j → uor → udly` where the Lean has the line's composite stage-0 path). Note `rtz_of_fork_j`: with z_ack-branch spread ≤ j-branch spread, it is implied by `S_A_FORK` + `S_A_J`; so no transport-delay run violates it alone. Necessity: untimed only (`MuxN3Proof.muxn3_needs_rtz`); no timed counter-run (impossible in the sufficient static family, by that lemma) |
| `bdc_muxn.s_setup` (decode form) | `muxn3_s_pin_of_static` `S_S_SETUP` | launch: index settled at the control sender's driver (`Lsd` before its ctl_req rise). data: `s{0,1}` wire → `sel_i.{I0,I1}` + SP (hi). request: `Lsd` + ctl_req wire → `sel_i.I2` + SP (lo). Per decode `i`, per bit | **proved sufficient** (lumped decode arc: the per-pin arc difference `sel_i.I{0,1}→O` vs `sel_i.I2→O` must be added as margin). **Exact** in `Mn3Cex` (one tick: `bnd_ok` / `cex_fails`) |
| `bdc_muxn.s_setup` (data LUT5 form) | `MN3DataStatic.S_Z_S` | launch: index settled at the driver. data: s wire → `zdat.{I3,I4}` + SP + LUT5 arc (hi) + `Mz`. request: `Lsd` + `Kj` + `wo` + `Lo.lo` + `Dl` (ctl_req → decode → join → `|j` → line, lo) | **proved sufficient** (`muxn3_data_ok`, non-vacuous `data_witness`); no counter-run |
| (new) `bdc_muxn.bundled_z_data` | `MN3DataStatic.S_Z_D` | launch: input `i`'s data settled at its driver (`Ld` before in_i_req rises). data: data wire → `zdat.I{2-i}` + SP + arc (hi) + `Mz`. request: `Ld` + in_i_req → `uj_i.I0` + `uj_i` arc + `uj_i → |j` + `|j` + line (lo) | **missing in JSON**; proved sufficient. As Lt3 found for bd_mux's S_Z_X, probably only sufficient as stated (the join waits for the later of request and decode) |
| `bdc_muxn.s_hold` | `muxn3_s_pin_of_static` `S_S_HOLD` | launch: ctl_req fall at the sender. data: ctl_req wire → `sel_i.I2` + SP (hi). request: `Kj` (ctl_req fall → selected decode → join, lo) + `Kz` (join fall → `|j` → line fall → server z_ack fall) + `Wzc.lo` (sender sees ctl_ack fall; the header's hold contract) + s wire → `sel_i.{I0,I1}` + SP (lo). Per decode, per bit | **proved sufficient** under the header's contract (index held until ctl_ack fall seen). Not shown necessary. The data-LUT hold needs no inequality beyond the contract (`S_HM` are pure hold margins: sums of MIN delays) |
| `bdc_muxn.iso_ctl` | `MN3Static.S_J_C` (per `i`) and nothing else | `ctl_req → {sel_0, sel_1, sel_2}`: **no skew bound** under FIFO wires (the selected-edge order follows from causality, `E_step`; the unselected decodes stay low by H_S_PIN + `selF_off`). Its only timed content is the join env latency through the control sender, per branch: launch: join `i`'s node edge. data: `uj_i` arc (hi) + feedback wire (hi). request: `uj_i` arc (lo) + `Kz` + `Wzc.lo` + `Ec` + ctl_req → `sel_i.I2` + decode arc + `sel_i → uj_i.I1` (lo, branch `i`) | **proved sufficient**; refines the JSON's "branch skew < half a handshake" (as for `bd_mux.isochronic_forks`' ctl branch). Not shown necessary |
| `bdc_muxn.iso_zack` | `MN3Static.S_A_FORK` (+ `S_A_J`) per `i` | `z_ack → {ua_0, ua_1, ua_2, ctl sender}`: launch: z_ack edge at its driver. data: z_ack → `ua_i.I1` + SP (hi) + `ua_i` arc + feedback (hi). request: `Wzc.lo` + `Ec` + `Kj` (z_ack → ctl sender → ctl_req → decode → next join node, lo) + `j_i → ua_i.I0` wire + SP (`Wja.lo`). `S_A_J`: launch: j_i edge; data: `Wja.hi` + `ua_i` loop (hi); request: `Kz + Kc + Wja.lo`, and `2Kz + Kc + Wza.lo` | **proved sufficient**. For an `i` the next token does not select, `S_A_FORK` constrains a bookkeeping edge (j_i does not move); like Lt3's skew results it may be a proof artefact there. Not shown necessary |
| (new) `bdc_muxn.uj_env_latency_req` | `MN3Static.S_J_X` | launch: join `i`'s node edge. data: `uj_i` arc + feedback (hi). request: `uj_i` arc + `j_i → ua_i` + `ua_i` arc + `ua_i → client` (lo) + `Ex` + in_i_req → `uj_i.I0` (lo) | missing in JSON (bd_mux analogue `bd_mux.uj_env_latency_req`) |

Also as Lt: reset sequencing (`H_RST_LONG`, `H_RST_EARLY`) and the line's
`H_FLUSH_STAGE` (existing `bd_delay[FASTFALL].flush_per_stage`) are taken in
event form.

## What did not work / not done

* **rtz counter-run**: not possible as Lt3-style "violate exactly this one"
  in the static family (`rtz_of_fork_j`); a counter-run violating the
  EVENT-form instance alone needs a run whose sender holds ctl_req long
  (asymmetric `Ec`), so the ack's rise window outlasts its loop while the
  z_ack low pulse does not. Designed in words, not built (time).
* `Dl` is one bound for both line edges; rise edges could use the slower
  chain bound (a refinement of Kz in the rtz request path; the JSON says
  "rise").
* Per-pin LUT arcs: decode and data LUT arcs are lumped (pin windows for the
  data LUT); the decode's s-pin vs ctl-pin arc difference is a margin to add.
* Necessity of S_S_HOLD, S_J_C, S_A_FORK, S_Z_S, S_Z_D: not probed.
* No composition with the amerge3 index producer / link `n_index_97`
  (H_S_RANGE and the sender contracts are where it plugs in).
* Pulse non-emptiness for the acks (Lt2 `mux_pulses` analogue): not written.

## Verdict

**Works.** `bdc_muxn3_32` has a kernel-checked timed theorem at gate level
(real inferred INITs for the three decode LUT3s, the `|j` LUT3 and the data
LUT5; bd_c2 INIT for the six C-elements; FIFO arcs; window feedback; Lt2's
FASTFALL line), in causal/static form, with a unit-delay witness that selects
every input and delivers non-degenerate data, and a one-tick counter-run that
shows the decode's select setup is exact. All five unproved `bdc_muxn`
entries get timed sufficient EndpointOK forms; `iso_ctl` reduces to a per-branch
env latency (no skew bound); `rtz` turns out redundant in the sufficient
static set when the z_ack branch's spread is at most the j branch's. Effort to
finish the leftovers (rtz event-form counter-run, hold/fork necessity,
per-pin arcs, rise-edge line bound): about 1 day. What it buys: the loop
header can enter C's gcd_hw composition as an operator with a proved timed
contract, and the checker gets concrete forms for the 5 entries plus 2 new
ones (`bundled_z_data`, `uj_env_latency_req`).

## Fidelity per primitive

* decode LUT3s, `|j` LUT3, `uor`/line LUT1/LUT2 (control): binary function of
  the REAL INIT, lumped FIFO arc (H_LUT_FIFO); grade B (no per-pin arcs, no X).
* `bd_c2` (joins, acks): as above plus own-output window channel (H_FB).
* data LUT5: Kleene window relation over per-pin windows (H_KLEENE_LUT),
  output unconstrained when the closure is `x`; grade A-.
* wires: FIFO per fork branch (control), window per pin (data); the two delay
  parameters of one net must be filled from the same route.
* partners: abstract four-phase parties with causal latencies and data
  contracts.
* Time: ℕ ticks.
