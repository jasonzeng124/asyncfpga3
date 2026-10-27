# gcd_hw end to end: shard C's hypothesis list

Shard C, probe 8l, 2026-10-27. This is shard C's input to the all-shard list
`formal/out/gcd_hw_hypotheses.md`. Shard C does not write that file. Rows owned by shard B
(cells) and shard A (LUT, delay and corner model) are cited by their IDs, not restated; their
grades are the owners' grades.

## 0. The target statement and how far the Lean chain reaches

**Target.** The routed gcd_hw (`cells/hw/gcd_hw.v` → `gcd_rig.v` → `bdc_gcd`, emitted by `bdc/emit.py`
from Dynamatic's gcd fixture). For every input `0 <= a, b < 2^31`, every value the circuit latches on
`out0` is `Nat.gcd a b`, and the circuit does latch one.

The chain, with each link's status:

| # | link | Lean | status |
|---|---|---|---|
| T1 | the graph bdc emits computes `Nat.gcd` on every schedule and every arbitration; it is live and bounded (token level, unbounded FIFOs) | `GcdHw.Gcd.gcd_hw_graph_computes_gcd`, `gcd_hw_graph_live`, `gcd_hw_graph_no_infinite_run` (C-8i, C-8k) | **proved** |
| T2 | each cell kind meets the network's protocol and token-equation spec (SI/DI gate models) | `fork_op`, `join_op`, `steer_op`, `mux_op` (8f); `amerge_op` (8j, 2 inputs); `sink_op` (8f); **`Link.link_op`** and **`MuxN.muxn_op`** (8l, new); the 3-input control_merge is two `amerge_op` stages (**`Capstone.amerge3_cascade`**, 8l); `bd_src` is **`CapstoneSrc.src_op`** (8l) | **proved** for every cell kind gcd_hw instantiates, in the Ops SI/DI models (binding to the generated cells: O4) |
| T3 | any network of such operators, with every channel bundled, refines every solution of its token equations: at every time, each channel's latched values are a prefix of that solution's stream | `Ops.net_refines`, `net_prefix` (8f) | **proved** (any graph, cycles allowed) |
| T4 | T3 instantiated on bdc's gcd_hw network, with bdc's link placement | `CapstoneLinks` exports the placement (100 linked channels, 175 stages) | **open**. See §5: O1 (cm winner forcing), O2 (stream solution from the token run) and O4 (binding the Ops SI models to the generated cells). The reduction itself is proved: `Capstone.latched_const` / `gcd_hw_conditional` (if the network's equations have a solution with `out0` constantly `gcd a b`, every latched `out0` value is `gcd a b`) |
| T2' | non-vacuity of the new cell models | **`Link.link_witness`**, **`MuxN.muxn_witness`**: explicit unit-delay runs meeting every gate-model field and the protocol, delivering a token | **proved** |
| T5 | storage on every ring (the 8j deadlock cannot recur) | **`gcdhw_ring_ge3`**: every cycle of bdc's gcd_hw graph carries ≥ 3 bd_link stages; `gcdhw_cycle_linked`; `gcdhw_has_cycle` (non-vacuity) | **proved** (structural) |
| T6 | circuit liveness (a token reaches out0) | none | **open**. See §5, O5 |
| T7 | every timing obligation of T2 holds on the routed bitstream | tcheck: `pot_sound`, `cverdict_sound` (10h); per-route verdicts on 4 seeds | proved sound for each obligation it checks; per-obligation status in §3 |
| T8 | each cell's gates are the synthesized netlist's LUTs | Gen (11d): every cell generated from the RTL and equal to B's specs; `bd_link_ctl_gate_B` = `ctlB`, which `OpsLink` uses directly | **proved** for the INITs. The Ops SI models of fork, join, steer and mux are hand models. Their equality to B's generated-cell specs is not mechanised (O4) |

So no end-to-end theorem exists yet. What exists is every token-level and cell-level piece, the
generic glue (T3), and the structural ring fact. The missing middle (T4, T6) is listed in §5 with
estimates.

Grades (as in the fidelity tables):
- **A**: exact, or strictly more general than the fabric (proved, or true by construction).
- **B**: plausible and physically motivated, not tested on this silicon.
- **C**: a known idealisation or a known gap. It can be false in some regime, or it is an
  obligation with failing instances on some route or corner.

## 1. Token level (shard C; T1)

| id | statement | where | grade | test |
|---|---|---|---|---|
| H_INPUT_RANGE | `a, b < 2^31` (non-negative i32) | precondition of T1, not a hypothesis | n/a | negative inputs loop in the C and in the graph (C-8i `#eval`) |
| H_OPS_VERILOG | each op's Nat-mod-2^w semantics is bdc's Verilog (`compute.BINARY`/`CMPI`); equal to MLIR `arith` wherever MLIR is defined | `GcdHw.Ops` | A (by construction; shifts ≥ w follow Verilog) | `bdc/test_compute.py`-style exhaustive vectors on the generated cell |
| H_FUSED_EXACT | a fused region is one strict node computing its expression DAG | `Rule.comp` | A at token level | GLS of the fused cell against its expression |
| H_SOURCE_ETERNAL | 4 source→fork→constant chains (plus bdc's absorbed pairs) are always-valid literals. 9 of bdc's linked values sit on these chains and are not channels in the model (`CapstoneLinks` header) | importer (C-8i) | B (it is a wire with `bd_src` holding req high) | GLS on gcd_hw: those bd_src req nets stay high; the links on them fill once and never drain |
| H_ONE_INVOCATION | one token on the control spine | **proved** from the initial store (`closed_of_check`) | A | none needed |
| H_FIFO_UNBOUNDED | token channels are unbounded FIFOs | T1's model | C for the circuit (links hold one token per stage, wires zero). It is bridged only by T4 (refinement is capacity-independent) plus T6 (liveness needs capacity). | `link_capacity` (8l) gives the per-link bound the bridge has to use |
| H_DRIFT | the exported graph is what bdc emits now | `formal/tools/dfimport/check.sh`; `Wip/C8l/linkexport.py` for the links | A while the drift check passes | rerun on every bdc change |

## 2. Network composition (shard C; T2 and T3): primitive models

These are the hypotheses inside the Ops cell models. Every one is a field of a gate-model
structure (`Fork`, `Join`, `Steer`, `Mux`, `MuxN`, `AMerge`, `Link`, `Sink`).

| id | model | grade | why / test |
|---|---|---|---|
| H_CEL_SI | a C-element (or C-tree, H_CTREE_ATOMIC) output moves only to the value all its inputs had one tick earlier; unbounded inertial delay | A for the protocol: it is more general than any bounded delay. It holds of the real LUT only under B's C1-C4 (pulse width, feedback first, per-pin order, FIFO LUT) | B's C1-C4; rule R (RT_FB) for C2 |
| H_LUT_SI | a combinational control LUT (steer, mux join select AND) moves only to its function of the previous tick's inputs | B (no hazard model at Ops level; B's Kleene/mux-tree work covers hazards) | B's H_KLEENE_LUT (grade B); A's X audit |
| H_WIRE_DI | each fan-out branch of a request/ack wire has its own unbounded inertial delay (forks not isochronic) | A for the protocol (more general) | B's X4/M3 show some cells NEED weak isochrony (mux z_ack fork, ctl_req fork), which Ops does not use because its cells are modelled as one SI unit; see O4 |
| H_DELAY_LUMPED | OR + matched delay line = one unbounded inertial node | A for the protocol; the LENGTH matters only for H_BUNDLE | rule A |
| H_DATA_COMB | data paths are zero-delay functions; every real data delay is pushed into H_BUNDLE of the channel it feeds | C (an idealisation, discharged channel by channel by §3) | §3 |
| H_LATCH_COMB (new, 8l) | bd_link's latch is a zero-delay transparent latch on the node `c` | C (idealisation); discharged by the link's 8a obligations Sep/Hold/SetupHold, i.e. B's L1-L3, P1-P4 | rules I, H, W |
| H_WIRE_DI (link, new) | `ack_in` and `req_out` each follow `c` through their own unbounded inertial delay (the DACK and DELAY lines) | A for the protocol | none needed |
| H_BUNDLE(c) | per channel: the bus does not move while the channel is mid-transaction | C as a model; it is THE per-channel timing obligation (§3). For a link's output it is derived (`link_held`) from the input's bundling plus H_LATCH_COMB | §3 |
| H_ARB, H_ARB_EXCL | arbiter grant moves only to its request, rises only with the other grant and A0 low; never both grants | B's R1, R2, A1-A6 | rule J; B-amerge (`amerge2_ok`, `amerge3_ok`) |
| H_AMERGE_RTZ (8j) | the previous winner's A_k falls before z_req rises again | C: unchecked by every rule | none yet; a tcheck obligation is easy to add (two-path race from A0↓) |
| H_EXCL_REQ(m) | a 2-input loop-header control_merge never has both requests high | an open proof obligation (O1), not a silicon hypothesis | follows at token level from H_ONE_INVOCATION |
| H_MUXN_SEL (new) | the index `s` of bdc_muxn3 is held by H_BUNDLE of its control channel. Values ≥ 3 select nothing (modelled; safe) | as H_MUX_SEL | rule E on `umux21`'s select (fed by `ULINK_N_INDEX_97`, DELAY 8) |
| H_RESET | every channel starts at req = ack = 0 and every C-element node at 0 | B (B's C5, P4: reset long enough) | testbench reset is µs scale |
| H_SRC / H_ENV_OUT | the rig offers `a`, `b`, `start` by the four-phase protocol and acknowledges `out0`/`end` | B (the rig's `uenv0/uenv1` are a bare Muller ring: thinnest RT_FB, see §3 R) | board: gcd_hw's measured results; GLS of the rig |

## 3. Timing obligations per channel and link, and what discharges them on the 4 routes

The routes are gcd_hw R5 seeds d, 2, 3 and 4 (C-10e/10g/10h). Verdicts are tcheck's at fastG and
slowG, i.e. H_ONE_CORNER plus the 0.772/1.155 band. Counts are "agree/disagree/not comparable"
against the project rule (C-10h table). Every disagreement is "project PASS, tcheck FAIL only under
the band"; the unguarded fast and slow corners pass on every one.

| obligation (Ops/8a name) | where in gcd_hw | tcheck rule | 4-route result | grade |
|---|---|---|---|---|
| H_BUNDLE at a compute/fused-region output (H_COMPUTE_DELAY): data cone settles before the matched delay's request | every comp rule (29) | **A** (bundled: H_BUNDLED_T0) | 199/200 agree. Seed 3 `shrsi1`: fastG −339 ps, unguarded fast +2512 | C until H_BUNDLED_T0 is composed with the upstream rule (open) |
| H_MUX_SEL / H_STEER_SEL / H_MUXN_SEL: select settled at the join/steer LUT pins before the request | 22 mux, 38 branch, `umux21` | **E** (skew.py; E0 = no credit) | E 465/472, E0 460/472; failures band-only | B. E needs H_LEVEL and H_CLEAN_EDGE at X (252 X's are LUT outputs) |
| link capture: Sep + latch setup (8a `Sep`, `SetupHold`; B's L1, L2, P1, P2) | every link stage (175) | **I** | 300/300 (75 per route compared, 104 not comparable) | B. I's request side rests on H_SEGMENT. B's L1 says rule I omits the feedback-pin IOPATH and SP[fb]: a MISSING TERM |
| link hold (8a `Hold`; B's L3, D4): DACK | every link stage | **H** (Hc cert) | 630/632 (2 band findings: −28/−9, −1/−74) | A for the check (cert, H_EXTRACT_MIN removed); B for the model |
| latch enable pulse / open width (B's L2, 8e W) | every link stage | **W** | unchecked by the project. tcheck min +346 ps fastG, +832 slowG | B (H_SEGMENT) |
| FASTFALL / RFAST line drain (B's D2) | `bd_delay_gated` request lines (matched delays) | **F** (Fc cert) | 113/116: seed d `ucmpi8` (fastG −498, unguarded +941/+2300) and `merge12` on seeds 3 and 4, all band-only. (Seed 2 `uselect1.udly`'s −141 ps is tcheck's looser data side, not a disagreement) | B (H_CONTROLLING argued by hand) |
| arbiter A0 fork (H_ARB; B's A1) | 8 control_merges (`uarb*`) | **J** (Jx exact shared prefix) | Jx 71/72; J0 57/72 | B (H_ONE_SAMPLE_PER_WIRE) |
| C-element feedback first (H_CEL_SI's premise; B's C2/C3) | 363 C-elements per route | **R** (Rc cert) | kernel: 0 failures at fast/slow/fastE/slowE (C-10f). Rig `urig.uenv1`: −117/−221 (seed 2), −86/−243 (seed 4) under the band | C: the rig's 2-cell Muller ring is the thinnest real race. Per-pin term (C3) is invisible to the SDF |
| H_AMERGE_RTZ, H_MUX_RTZ (B's X1) | 8 amerges, 22 muxes, `umux21` | none | UNCHECKED | C |
| mux isochrony (B's X4: z_ack→{uxa,uya,ctl}, ctl_req→{uj0,uj1}); merge M3 | every mux | none | UNCHECKED | C |
| H_FORK_DATA (data wire vs req wire per fork branch) | forks not fused away | covered by A or I wherever the branch ends at a cell or a link | no separate row | B |
| C-tree depth latency (B's C7) | wide joins | none | UNCHECKED | C |
| reset (B's C5, P4) | all | none (testbench) | n/a | B |

Model hypotheses tcheck itself rests on (C-10e/10g/10h). They are global, not per channel:

| id | statement | grade | test |
|---|---|---|---|
| H_NETLIST | the checked graph is the routed circuit: SDF arcs, false arcs cut by INIT, storage census | B | fasm2lean round trip (C-11b/11c) |
| H_ONE_CORNER (+ band κ) | the die sits at one prjxray corner; each element is within 0.772/1.155 of it | B (silicon rings at 0.61-0.68 × slow_max lie inside; within-die scatter per route unmeasured) | two-path on-die measurements, shard A's κ estimator |
| H_RC_EXACT (Elmore) | wire delay = Elmore RC per sink arc, intrinsic from prjxray | B | per-route ring periods inside the summed bands (n = 128) |
| H_FALLBACK_BAND | the remaining arcs with no prjxray number (FF, CARRY4 CIN, non-SLICE) lie in the SDF band | C (no disagreeing row uses one) | add the arcs (≈ ½ day) |
| H_BIDIR | a long line driven from its far end uses the `dst_to_src` delay | B | — |
| Run semantics (10a): H_LAUNCH, H_BOUNDED_DELAY, H_QUIESCENT, H_LOCAL, H_ZERO_DELAY_FN, H_COMMON_LAUNCH | bounded transport per arc, OR-causal under quiescence | B | GLS at the corners |
| H_SEGMENT, H_CONTROLLING, H_BUNDLED_T0, H_LEVEL, H_CLEAN_EDGE, H_ONE_SAMPLE_PER_WIRE, H_POLARITY, H_OWN_LATCH_CLOSED, H_F_THROUGH_TAIL | per-rule shape assumptions | B (H_CLEAN_EDGE at a LUT output: C) | see C-10g/10h |
| identification | obligation shapes come from tighten.py's helpers; linked to 8e's races by hand | C | emit 8e `race2` instances per stage (Phase 3 item, open) |

## 4. Cell level (shard B; cited, not restated)

From `notes/B-obligations.md` (§§1-8, 11) and `notes/B-amerge.md`. Every cell gcd_hw instantiates:
`bd_c2/bd_c2n/bd_ctree` (C1-C8), `bd_latch` (L1-L5), `bd_link` (P1-P5), `bd_delay` (D1-D4),
`bd_arbiter` (R1-R5, A1-A7), `bdc_amerge2/3` and `bdc_muxn3` (B-amerge: `amerge2_ok`, `amerge3_ok`,
`muxn3_ok`, with H_BUNDLED_IDX, H_IDX_ACK_FORK, H_ARB_RESOLVED, H_RT, H_S_RANGE, H_CTL_HOLD,
H_YOSYS_MAP), `bd_mux`/`bd_steer` (X1-X6), `bd_fork`, `bd_join`, `bd_snk`/`bd_src`.

Cross-cutting, all grade B: H_KLEENE_LUT (one 2:1 mux; board glitch-counter experiment), H_RF_ASYM
(unmeasured), H_WIRE_RATIO, H_DW/H_DL.

Ranked most likely to bite (B §12): C2/C3 feedback-first (rule R covers C2 on the 4 routes, C3 is
unchecked); L1's missing feedback-pin term in rule I; L2 enable pulse width (no rule).

## 5. What stays open between the pieces (proof obligations, not silicon hypotheses)

| id | what | why it is open | estimate |
|---|---|---|---|
| O1 | **cm winner forcing.** *Interface now fixed in Lean:* `CapstoneCM.amerge_op_forced` restates the control_merge operator with the oracle fixed in advance (the token run's labels `ω`) and the equation restricted to offered tokens, under **H_CM_FORCED** (the circuit's winner of every OFFERED token is `ω`). The unrestricted form could not be used: `winner` is `false` on never-offered indices, so "winners = labels for all k" would be false for every real circuit (a vacuity trap). Its token half is proved: `CapstoneExcl.cm_inputs_exclusive` (in every reachable token store, two control_merge inputs are never both non-empty). What remains open is the circuit half of H_CM_FORCED. In detail: Each 2-input control_merge's winner stream equals the token run's label stream (H_EXCL_REQ plus the order). `amerge_op`'s equation is relative to the circuit's winner `ω`; for an arbitrary `ω` the stream equations of a loop can have NO solution (`z0 = f(z0)`), so T3 cannot be instantiated without it | needs a circuit-level ring-counting invariant: the offered history of all channels is a reachable cut of the token LTS. That is a simulation, not the Ops time induction | 1-2 days |
| O2 | **a stream solution from the token run.** T3 needs a TOTAL solution `ref : C → Nat → Nat` of every operator's equation. Plan: the complete run's per-channel histories, repeated periodically (one invocation per period, as the sources repeat), satisfy fork/comp/steer/mux/cm equations because the final store is empty except `out0`/`end`. Then `ref out0 k = gcd a b` for all k, and T3 gives "every latched out0 value is gcd" | generic lemma over GcdHwLib's `Rule.fire` (FIFO histories per rule kind) not written | 0.5-1 day |
| O3 | **3-input control_merge as an Ops operator.** Resolved by composition: `emit_amerge` n = 3 is a cascade of two `bd_arbiter` stages joined by an internal channel `acc` (`R0`/`A0` of `uarb1` = `r1`/`A1` of `uarb2`), so it is two 2-input `AMerge` operators (`Capstone.amerge3_cascade`). bdc's priority index `won2 ? 2 : won1` is a function of the two stage buses at the same tick (H_DATA_COMB) | residual obligations: H_BUNDLE of the virtual `acc` bus (= `won1`; B's H_BUNDLED_IDX), and H_AMERGE_RTZ for stage 1. Stage 1 has NO matched delay between `R0` and `acc_req`, so its race is one C-element LUT (`A0↓ → ua_k → A_k↓`) against `A0↓ → ustate → ugrant → R0`: thinner than stage 2's and unchecked | none for the proof; the stage-1 RTZ race should become a tcheck row |
| O4 | **binding.** Note the subtlety: 8f's H_CEL_SI ("moves only to the value its inputs had ONE TICK earlier") is implied by a bounded-delay gate only under excitation persistence (the inputs do not move while the gate is excited, which is what B's C2 feedback-first buys). So the binding lemma must carry C2, not just the INIT. The Ops SI models of fork, join, steer, mux and amerge are hand models of the RTL; B's generated-cell specs are a different formalism (timed, FIFO LUTs). The link is bound directly (`ctlB` = generated LUT); the others are not | a refinement lemma per cell kind from B's timed spec to the Ops gate-model fields | 1 day |
| O5 | **circuit liveness.** T5 gives storage on every ring; the token run is live (T1). Missing: (i) a progress model (Ops' SI delays are unbounded, so nothing ever HAS to fire: liveness needs H_BOUNDED_DELAY per gate, or weak fairness); (ii) the simulation of O1 to carry the token schedule to the circuit; (iii) capacity: the token schedule must fit 1 token per link stage. 8a has this for pipelines (`muller_live`), 9 for rings | as listed | 2-3 days |
| O7 | **zero-delay renames and sources.** 9 GcdHw comp rules are WIRES in the circuit (`_reshape`, `_op_constant`): `constant2`, `constant18` (control-triggered literals) and `trunci0..4`, `extui0/1` (req/ack pass straight through, only the bus changes). Ops needs strictly causal operators, so these must be removed by identifying the two channels' handshake and folding the data map into the consumer (8f's rename note). The consumers are comps (map folds into `g`), `cond_br17`'s data (folds into the steer's `f`) and `mux3`'s input (`extui` of a 0/1 value, the identity on the values that occur). `bd_src` (`req = ¬ack`, LUT1), which heads the source chains collapsed by H_SOURCE_ETERNAL, is now an operator: **`CapstoneSrc.src_op`** (`σ c k = VAL`) | part of the concrete-network bookkeeping | ½ day, included in "concrete network" |
| O6 | per-route instances of the Ops obligations: tcheck checks tighten's obligation shapes, linked to 8f's H_BUNDLE/H_MUX_SEL by hand (§3 left column) | identification is by hand | 1 day (emit Ops-named obligations from the network) |

## 6. Tests that would grade the B rows up (one per row family)

- GLS (routed, board-fidelity) of gcd_hw on the 4 seeds with transport LUT paths, at both corners:
  checks H_DATA_COMB's discharge (rules A, E, I, H, W, F) end to end, and catches LUT-hazard
  dependence (A-fidelity R5).
- Board: gcd_hw's measured results over the uniform oracle (`cells/hw/uniform_oracle.py k_gcd`),
  for many (a, b), with vectors whose answer is not a failure value. This is the end-to-end test of
  the whole list. It cannot separate the rows.
- Board: B's glitch-counter (H_KLEENE_LUT) and the arbiter MTBF rig (R3) for the 8 arbiters. Under
  O1's H_EXCL_REQ the arbiters never see a contest, so R3 should never be exercised in gcd_hw.
  Counting contested grants on the board would test that claim directly.
- tcheck: add H_AMERGE_RTZ and H_MUX_RTZ as two-path races (they are the only UNCHECKED rows with a
  mux-like shape), and the C3 per-pin term to rule R.

## 7. The capstone statement as it will read once O1 and O2 are closed

For `a, b < 2^31` and every circuit run `ch` (traces of every request, acknowledge and bus of
bdc's gcd_hw network, link stages included):

* if every operator instance's internal traces satisfy its gate model (`Fork`, `Join`,
  `Steer`, `Mux`, `MuxN`, `AMerge` ×2 per 3-input cm, `Link`, `Sink`, source/env), which brings
  in §2's primitive hypotheses and, through O4, B's cell rows of §4;
* and every channel satisfies H_BUNDLE (§3's per-channel and per-link rows, discharged on the 4
  routes by tcheck under §3's global hypotheses);
* and H_CM_FORCED holds for the 8 multi-input control_merges (O1, to be proved, not assumed);

then every value latched on `out0` is `Nat.gcd a b`. With O5, `out0` also latches at least one
value.

The proof would be `Capstone.latched_const`, applied to the O2 solution (with
`amerge_op_forced` for the control_merges and the other `*_op` theorems for the remaining
operators). Everything named in that chain exists and checks except O1, O2 and the concrete
network term (½ day of bookkeeping once O2 fixes the value conventions).

## Status update after probe 10k (lead, merged)

The timing hypotheses this list marked "no tcheck rule checks this yet" are now
rows of the proved checker on the 4 gcd_hw routes (d, 2, 3, 4); full per-row
table in `formal/notes/C-10k-fbfirst.md`, data in
`formal/tools/tcheck/results/r10k_rows.tsv`. Summary:
- H_FB_FIRST / H_FB_SETTLED: implied by RT_FB (`FbFirstRt.fbFirst_of_resp`,
  plus protocol fact H_RESP_ONLY); holds wherever Rc passes, i.e. everywhere
  except the rig's urig.uenv1 under the band on seeds 2 and 4.
- H_AMERGE_RTZ (rule Z): holds on all routes, all models (worst +383 ps),
  except cm12 on seeds 3/4 under the band (through H_FF_DRAINED).
- H_FF_DRAINED (rule Fd; rule F is NOT sufficient, incomparable): passes
  unguarded everywhere; band failures on cm12 (seeds 3, 4) and ushrsi3 (seed 4).
- H_MUX_RTZ / X1 / A3 pulse (rules X, Xi): 0 failures at sdf/fast/slow; band
  failures only on muxes whose z_ack is a steer OR (umux10, umux16 on seeds
  3/4, worst -2208 ps; shared DACK ripple charged twice -- shared-prefix
  credit open). Xi adds H_OR_IDLE.
- Still unchecked: X4 ctl_req->uj fork, M3, C7.
Every row passes at sdf, fast and slow; all remaining failures are band-only.
