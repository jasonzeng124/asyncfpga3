# B-gcd-cells: which cells gcd_hw uses, and what shard B covers of each

Probe Bg2 (shard B, Phase 3 capstone support), 2026-10-27. One new Lean file,
`formal/lean/Formal/Cells/GcdCells.lean` (timing of `bd_delay_gated`, checked
clean, section 5). No route, no board, no toolchain run: `$TC` does not exist
in this container, so nothing below is a routed number and no nextpnr
fingerprint applies. Instance counts are from bdc's emitted Verilog; leaf
counts are my hand expansion of the `generate` blocks in `cells/rtl/` (no
yosys here), not a synthesized netlist.

`formal/out/gcd_hw_hypotheses.md` (named in PROGRAM.md) does not exist yet.

## 1. How gcd_hw is built

- `cells/hw/gcd_hw.v` (JTAG readback, window sequencer) wraps
  `cells/hw/gcd_rig.v` (the ring environment), which instantiates `bdc_gcd`.
- `bdc_gcd` is emitted by `cells/hw/build_hw.sh gcd_hw`:
  `python3 bdc/emit.py build/frontend/gcd/comp/handshake_transformed.mlir
  --no-top --probe n138 -o build/gen/gcd_kernel.v`. The MLIR is Dynamatic's
  integration-test gcd (fixture `cloud/fixtures/frontend/gcd/comp/`; no
  `kernels/` source). A bare `build_hw.sh gcd_hw` hands off to
  `verify/converge.sh`; C-10e's routes used
  `BDC_SELECT_PADS=cells/hw/gcd_hw_pads.json BD_RLOC=v4`.
- I re-emitted it (read-only use of bdc, output in my scratchpad) both ways,
  with the bdc knobs unset as `formal/tools/dfimport/check.sh` pins them
  (`BDC_OP_FUSION` default on, `BDC_LINK_FASTFALL` unset, so every `bd_link`
  has RFAST=0 and every `bd_mux` FASTFALL=0; `BD_LINK_DC` not defined, so
  `bd_link` = `bd_link_ctl` + `bd_latch`). The pads file changes only three
  DELAY values (link n166_0 8 -> 13, n166_1 8 -> 14, n32_2 8 -> 13); cell
  types and counts are identical. The table uses the pads values.
- 331 matched delays. `BD_SIZES` unset (sizes file off by default).

## 2. Instances in the emitted design

### 2a. Direct instances of `bdc_gcd` (307)

| type | count | parameters (pads build) |
|---|---|---|
| `bd_pipe` | 63 | W=32 N=2 DELAY=0 SDELAY=3 DACK=6: 38; W=32 N=3 DELAY=0 SDELAY=3 DACK=6: 7; W=1 N=2 DACK=6, DELAY 0/8/13/14: 1/8/2/1; W=1 N=3 DELAY=0 SDELAY=3 **DACK=0**: 5; W=2 N=2 DELAY=8 DACK=6: 1 |
| `bd_fork` | 52 | N=2: 32, N=3: 9, N=4: 8, N=5: 2, N=6: 1 |
| `bd_link` | 46 | W=32 DELAY=0 DACK=6: 32; W=1 DELAY=4 DACK=6: 10; W=1 DELAY=0 DACK=6: 4 |
| `bd_join` | 38 | N=2 (all) |
| `bd_steer` | 38 | (no parameters; every `cond_br`, behind a `bd_join(cond, data)`) |
| `bd_mux` | 21 | W=32 DELAY=12 FASTFALL=0 |
| `bd_snk` | 16 | W=32: 10, W=1: 6 |
| `bd_src` | 4 | W=1 VAL=0 (Dynamatic `source`) |
| `bdc_fused_*` (generated) | 20 | compute units: cmpi x7, ori x5, shrsi x5, addi, shli, select x2 (`uselect1` = abs(a-b), the n138 probe); DELAY 16..94; inner `bd_join` N=1: 4, N=2: 13, N=4: 3 |
| `bdc_amerge2_0` (generated) | 7 | control_merge, 2 inputs, W=1, DELAY=12: one `bd_arbiter`, index = `g2 \| in1_ack`, data mux, `uor`, `bd_delay_gated` |
| `bdc_amerge3_0` (generated) | 1 | control_merge, 3 inputs, DELAY=24: two `bd_arbiter` CASCADED (`uarb2.r1` = `uarb1.R0`) |
| `bdc_muxn3_32` (generated) | 1 | 3-way loop-header mux, W=32, DELAY=12: three join `bd_c2` on decoded selects `ctl_req & (s == k)`, three ack `bd_c2`, `bd_delay_gated` |

Not emitted for gcd_hw: `bd_merge`, `bd_latch_rst`, any `_set` cell,
`bd_mlink`/`bd_flink`, `bd_mem`, `bd_link_dc`, `bd_bd2dr`/`bd_dr2bd`. The
kernel has NO initial token: every stage resets empty, and the loop headers
take their first token from the entry path through the arbitrated
control_merges. The one token of the whole system is in the rig.

### 2b. Leaf cells (hand-expanded)

| leaf | count | from |
|---|---|---|
| `bd_c2n` (`bd_link_ctl`) | 184 | 138 pipe stages + 46 links |
| `bd_latch` | 184 | W=32: 129 (16 LUT6_2 pairs each); W=1: 53 (odd LUT); W=2: 2 |
| `bd_delay` FASTRISE (uack, DACK=6) | 169 | 15 stages of the DACK=0 pipes have none |
| `bd_delay` sym (rdly) | 75 SDELAY=3 internal + 22 last/standalone with DELAY 4..14 | the other 87 are N=0 wires |
| `bd_c2` | 153 | fork trees 36, join trees 51 (38 + 13 in fused units), `bd_mux` uxa/uya 42, `bdc_muxn3` 6, arbiter ua1/ua2 18 |
| `bd_c3` | 9 | fork N=3 |
| `bd_c4` | 14 | fork N=4: 8, N=5: 2, N=6: 1, fused join N=4: 3 |
| `bd_mux` join LUTs `uj0`/`uj1` | 42 | |
| `bd_steer` LUT6_2 + ack LUT2 | 38 + 38 | |
| `bd_datamux` | 21 x W=32 | inside `bd_mux` |
| `bd_delay` sym N=12 | 21 | `bd_mux.udly` |
| `bd_arbiter` (`ustate`, `ugrant`, ua1, ua2) | 9 | 7 x amerge2, 2 x amerge3 |
| `bd_delay_gated` | 29 | 20 fused + 8 amerge + 1 muxn3 (N 12..94) |
| `bd_src` LUT1 | 4 | |
| yosys-inferred LUTs (no cell) | ? | fused datapaths (32-bit add, sub, shifts, compares, select), amerge index/data mux, muxn3 decode and data mux |

### 2c. Rig cells around the kernel (`gcd_rig.v`)

`bd_fork` N=3 (`ufork`, c3), `bd_c2n` (`uenv0`), `bd_c2n_set` (`uenv1`: THE
initial token of the ring), `bd_delay` CMPD (`urdly`, request pad before the
compare), `bd_delay` N=2 (`upsnk`, p_end sink), plus WFILT/PRBD filter delays
of the instrumentation (not on the ring).

## 3. Coverage per cell type

Columns: **F** functional/INIT (gate equations from the real INIT and pin
map); **SI** handshake (speed-independent / protocol); **T** timed; **ids**
`formal/out/cell_constraints.json`; **missing** for the capstone. Lean names
are files in `formal/lean/Formal/`. C = shard C's work, quoted, not re-checked.

| cell (count in gcd_hw) | F | SI | T | ids | missing for the capstone |
|---|---|---|---|---|---|
| `bd_c2n` link ctl (184 + rig 1) | CElemFn, CElemTiming.c2n_eq, Gen ProofsCE/ProofsLink | LinkHandshake (fb_refines), MullerSI (C) | CElemTiming/OnNetlistTimed (follow_hold, four_phase), FifoFidelity.sel_phase, OnNetlistTimed2 reset | bd_c2n.pulse_width, .env_latency, .sel_order, .reset_width (all proved) | the INSTANCES: C2/C3 (RT_FB, H_SEL_ORDER with site pins) checked on no route of gcd_hw by any rule; C-10d found RT_FB failures on muller64 |
| `bd_c2n_set` rig `uenv1` (1) | CElemFn INIT_c2n_set, Gen bd_c2n_set_gate | as c2n | via "also_applies_to" of the bd_c2n ids (rst=0 function equal) | bd_c2n.* | reset release ordering of the rig ring (the one initial token) is not stated anywhere |
| `bd_c2` (153) | CElemTiming.c2_eq, Gen | CElemCore | c2_follow_hold, c2_four_phase, c2_reset | bd_c2.pulse_width, .env_latency, .reset_width proved; **.sel_order unproved in the JSON** | now proved by `Cells/ConstraintsSel.lean` (probe P3a, another agent, UNTRACKED; I checked it compiles clean, `#print axioms` standard only); the JSON is not updated |
| `bd_c3` (9 + rig 1), `bd_c4` (14) | CTree c3r_ce/c4r_ce, Gen | CTree | CTreeTimed c3/c4_follow_hold, _four_phase, _reset | bd_c3.*, bd_c4.* (sel_order unproved in JSON) | as bd_c2: closed by P3a's untracked file |
| `bd_ctree` (fork/join N>4: 3) | Gen ProofsCE (N1/N3/N5/N8 shapes) | CTree.reachable_eq_flat | CTreeTimed.tree_four_phase | bd_ctree.node_fork, .ack_wait | C7 tree latency UNCHECKED on routes |
| `bd_fork` (52 + rig 1) | via ctree; Gen | OpsFork.fork_op (C, lumped tree, DI wires) | per C-element only | none of its own | H_FORK_DATA (data wire before req wire per branch) is a pure route obligation, no B theorem, no id |
| `bd_join` (38 + 20 in fused) | via ctree; Gen | OpsJoin.join_op (C) | per C-element only | none of its own | H_JOIN_TWO_REQ data: max over all operands vs the matched delay (rule A, compute units) |
| `bd_link` (46) / `bd_pipe` (63) | Gen ProofsLink (bd_link_W2_step, bd_pipe_W1_N2_step) | LinkHandshake, Handshake/PerLink (C) | LinkTimed, PipeTimed, PipeTimedN (any N), PipePerPin | bd_pipe.sel_order, .lat_lumped, .boundary_I, .boundary_H, .rst_lines, .data_lead, .output (proved; "also bd_link (N=1)") | L1 rule I missing the feedback-pin term; L2 enable pulse width unchecked; L3 rule H missing site pins (B-obligations ranks 2-4). DACK=0 on 5 pipes: boundary_H then rests on the ripple alone |
| `bd_latch` (184, W=1/2/32) | Gen ProofsLatch, Latch | n/a | Bundling.capture, Latch.holds_value | bd_latch[odd/pair.O5/pair.O6].setup_data/.setup_pulse/.hold, .loop_bound | as above (per bit, at the pins) |
| `bd_delay` sym / FASTRISE (rdly 97, uack 169, mux udly 21) | Gen delay_luts/delay_outs | n/a | Bundling.sym_chain; PipeTimedN.fastrise_or | bd_delay[sym].pulse_width, [FASTRISE].ack_flush | none blocking (FASTFALL unused here: RFAST=0) |
| `bd_steer` (38) | LibCtlMergeMux steer_req0/1, steer_excl(_K), steer_tied_dontcare; Gen bd_steer_gate_K | OpsSteer.steer_op (C) under `Held` | **none** | **none** (only a mention under bd_mux X3) | the select-before-request at the steer's `s` pin (setup) and s-still-while-req-high (hold), per pin; LUT6_2 O5/O6 shared read (cf. B's H_LUT62_SHARED_READ); rule E checks the setup half without site pins. 38 instances, every loop exit |
| `bd_mux` (21) | LibCtlMergeMux j0/j1/c2/or2_spec; Gen bd_mux_W2_step | MergeMuxSI.mux_ok (needs H_BUNDLED_S, iso forks, H_RTZ); OpsMux.mux_op (C) | MuxRtzTimed.rtz_safe, mux_rtz_env_safe (uxa) | bd_mux.uxa_rtz, .uxa_rtz_env, .uya_rtz proved; **.uya_rtz_env, .bundled_s_setup, .bundled_s_hold, .bundled_z, .isochronic_forks unproved** | uya mirror now in P3d's untracked `ConstraintsMux.lean` (checked clean by me); the select at uj0/uj1 per pin (timed, setup+hold); bundled_z is rule A; uj0/uj1 feedback C2/C3 not formalised (X6). `fast_adv_N0_fails` shows the env RTZ can be negative |
| `bdc_muxn3_32` (1, the gcd loop header) | **none** (generated module; decode LUTs inferred by yosys) | **none** (C-8f open item 4) | only via "also bdc_muxn" on bd_mux ids (not instantiated) | bd_mux.uya_rtz_env / bundled_s_setup list it as "also" | everything: gate equations of the inferred decode `ctl_req & (s == k)` (a 3-input LUT per select feeding a keep C-element: hazard-freedom of the decode while s moves with ctl_req low), 3-way exclusion, SI spec, RTZ for 3 acks, select timing |
| `bd_arbiter` (9) | ArbBinary, Gen ProofsArb (arbiter_kleene_exclusion) | ArbBinary.arbiter_alternates, ArbHeldTimed | ArbHeldTimed(2), ArbA0Fork, ArbCorners, ArbInvolution, ArbResolve | bd_arbiter.* (14, all proved), bd_arbcell.* (5) | R3 MTBF parameters unmeasured (zero-failure only); rule J' site pins; A5 server/client hypotheses (H_SERVER_MIN) unchecked; the CASCADE in amerge3 (an arbiter as the client of another) is not in any theorem |
| `bdc_amerge2_0` (7), `bdc_amerge3_0` (1) | **none** for the wrapper (index `won = g2 \| in1_ack`, data mux, inferred) | **none**: control_merge operator open in C-8f (item 2); C-8b covers control_merge at token level under H_ONE_INVOCATION | arbiter rows only; matched delay now `GcdCells` (below) | none of its own | index/data bundling against R0 (the cell's whole obligation per its own header: grants leave with R0, so data is NOT valid at R0's rise); refinement of the arbiter handshake to a control_merge OpProto with an index oracle; cascade timing |
| `bd_delay_gated` (29) | Gen delay_gated_outs_B; LibEndMemMlink.gated_gate_low (Kleene) | n/a | **`GcdCells.no_early`, `rises`, `rise_by`, `fast_fall` (this probe)** | bd_delay_gated.gate (unproved in JSON; proved concurrently by P3c's untracked `ConstraintsFastFall.lean` `gated_not_early`/`gated_fast_edge`/`gated_dip_glitch`, window model, and by this probe in the per-pin FIFO model) | the per-stage flush is checked by rule F without its in-flight term (same gap as D2) |
| `bdc_fused_*` compute (20) | **none**: the datapath is yosys-inferred from `+`, `-`, `>>>`, `<<`, compares, `?:` | OpsJoin.join_op (C, data as zero-time function) | matched delay = `bd_delay_gated` (above) | none | H_COMPUTE_FN: the synthesized LUT/CARRY netlist equals the MLIR op (32-bit; the abs path `uselect1` is exactly where gcd_rig's GLS saw `cmpi sgt` misbehave); H_COMPUTE_DELAY: cone max <= matched delay min (rule A) |
| `bd_src` (4) | Gen bd_src_W2_spec; LibEndMemMlink src_K, src_no_fixed | trivially four-phase with its consumer | none needed beyond the consumer's | none | a LUT1 inverter ring with the consumer: its pulse widths are the consumer's C-element C1 obligation |
| `bd_snk` (16) | Gen bd_snk_W2_spec | OpsGcd Sink (C) | wire | none | none |

## 4. Ranked gaps for the capstone

Ordered by what the capstone theorem needs first (a missing operator model
blocks the composition outright; a missing timing theorem only leaves a
hypothesis ungraded).

1. **control_merge = `bdc_amerge2_0`/`bdc_amerge3_0` (8 instances) and the
   3-way header `bdc_muxn3_32` (1).** No gate-level spec, no SI proof, no
   OpProto: C-8f items 2 and 4 are open, and B has no theorem about either
   wrapper (only the bare arbiter). Without them the emitted graph cannot be
   composed at all. B's part: the wrapper equations (inferred LUTs, so they
   must come from the synthesized netlist, not the Verilog), the index/data
   bundling against R0 through `bd_delay_gated`, and the arbiter-of-arbiter
   cascade in `amerge3`. C's part: control_merge as an operator with an
   oracle index, and the one-token-per-loop invariant (C-8b's H_ONE_INVOCATION
   at handshake level).
2. **Compute datapaths (`bdc_fused_*`, 20; plus the amerge/muxn data muxes).**
   H_COMPUTE_FN has no proof route yet: the gate netlist is inferred by
   yosys from Verilog operators. The capstone needs the synthesized (or
   bitstream-read) LUT/CARRY4 function of each unit equal to its MLIR op, the
   kind of check C-11 (import, gen) already does for library cells. The
   abs-difference unit is where the gcd_rig GLS located the board failure.
3. **The emitted graph itself (C-8i).** The importer exists
   (`formal/tools/dfimport/mlir2lean.py`, `check.sh`), but no
   `Formal/Net/GcdHw*.lean` is in the tree, and C-8j showed that the
   hand-drawn gcd graph is live only for `a = 0` (no storage on the data
   loop). The capstone must use the emitted graph WITH its 184 link stages.
4. **`bd_mux` timed handshake (21 instances, the loop headers):** (uya
   RTZ-env mirror: P3d, untracked), the per-pin select setup and hold at uj0/uj1
   (`bundled_s_*`), the uj0/uj1 feedback (X6), weak isochrony. The RTZ race
   already has a negative corner-consistent estimate (`fast_adv_N0_fails`).
5. **`bd_steer` (38 instances) has no constraint entry at all.** Its
   handshake needs the select still at the LUT pins while the joined request
   is high (OpsSteer's `Held`), which is a per-pin setup/hold just like X3,
   plus the O5/O6 shared-read restriction. Small: a select-level theorem in
   the style of `FifoFidelity.sel_phase` on INIT `8888_8888_2222_2222`.
6. **Instance checks, not theorems:** C2/C3 (C-element feedback before the
   environment, with site pins) on all 184 + 153 + 23 C-elements; L1-L3
   latch setup/pulse/hold terms missing from rules I/H; rule F's in-flight
   term (also for the 29 gated lines); rule J' for the 9 arbiters. These
   are the B-obligations ranking 1-7; the capstone grades them as
   hypotheses until a rule checks them on the gcd_hw routes.
7. **Closed by concurrent, still UNTRACKED probes** (I compiled each clean):
   `bd_c2/c3/c4.sel_order` (P3a `ConstraintsSel.lean`), `bd_mux.uya_rtz_env`
   (P3d `ConstraintsMux.lean`), `bd_delay_gated.gate` (P3c
   `ConstraintsFastFall.lean`, and this probe's `GcdCells.lean`). The JSON
   still says unproved for all of them.
8. **Rig:** the initial token (`uenv1`, `bd_c2n_set`), the reset contract
   (idx moves only under rst), and the p_end sink delay are environment
   hypotheses the capstone has to state; covered functionally by the c2n
   proofs, not as a ring-with-token theorem on these instances (C's
   Ring.lean is the generic one).

Not a gap: `bd_latch_rst` and `_set` initial-token cells in the kernel (none
emitted), `bd_merge` (not emitted), `bd_mlink`/`bd_mem` (not emitted),
FASTFALL lines other than the gated ones (RFAST=0).

## 5. What I proved: `Formal/Cells/GcdCells.lean`

`bd_delay_gated` was the one cell on every generated unit of gcd_hw (29
instances) with no timing theorem (D5). The file models it per pin as bdc
instantiates it (`gate` -> `uor` LUT1 -> `g[0]` LUT1 -> `g[i]` = AND(chain,
gate) for i >= 1; each pin through its own FIFO read map `PipeTimed.Ret`):

- `no_early`: gate low on `[F, T)`; under **H_GFLUSH i**
  (`(p i).fst (V i) <= (q i).fst T`: the stale stage value is gone from the
  next LUT's chain pin before the new gate rise reaches that LUT's tap pin),
  stage `i` is high after `V i` only from `T + L i` on (`L` = sum of the
  chain's lower bounds). The matched delay survives reuse.
- `fast_fall`: `V (i+1) <= F + (q i).hi` (the output clears one tap read
  after the gate falls, as the cell intends).
- `rises`, `rise_by`: gate high on `[T, F2)` gives stage `i` high on
  `[A i, B i)`, `A i <= T + H i`; no extra hypothesis.
- `gflush1_of_lat`, `gflush_of_lat`: H_GFLUSH from delays. Stage 1:
  `F + r0.hi + r1.hi + (p 1).hi <= T + (q 1).lo` (the gate's low phase must
  outlast the two UNGATED hops, `uor` and `g[0]`); stage `i >= 2`:
  `F + (q (i-1)).hi + (p i).hi <= T + (q i).lo`. tighten.py rule F
  (`audit_fastfall`) checks these at the stage outputs and lacks the
  in-flight term `(p i).hi - (q i).lo`, as row D2.
- `flush_needed` (negative control that fails): N = 2, gate dip `[10, 12)`,
  H_GFLUSH 1 false (17 > 13): `z` is high at 13 < 19 = `T + L 2`.
- `long_dip_no_early`, `long_dip_rises`: a concrete run meets every
  hypothesis and `z` does rise at 37: not vacuous.

Check: `cd formal/lean && PATH=$HOME/.elan/bin:$PATH
LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/GcdCells.lean`
(about 8 s, no output). No sorry/admit/native_decide; `#print axioms`:
propext, Classical.choice, Quot.sound (the latter two from `Ret.fst`).

What it does not show: that H_GFLUSH holds on any gcd_hw route (no route
here); the AND gate's static-hazard freedom when the chain and tap pins move
together (H_TREE_FIFO is folded into the per-pin maps, as in
`FifoFidelity`); the bundling of the data the request covers (that is rule A
on the compute cone, gap 2). A first draft of this file re-proved the
`bd_c2/c3/c4` sel_order; it was replaced when I found P3a's
`ConstraintsSel.lean` doing the same, more completely. **Overlap:** after
writing this file I found P3c's untracked `ConstraintsFastFall.lean` proving
`bd_delay_gated` too (`gated_not_early`, window channels with the Kleene
closure of the real INITs, Bundling's model). The two are independent
models of the same obligation: P3c's is the house window model and should be
the one the JSON cites; `GcdCells` adds the explicit `uor` anchor hop in the
flush (`gflush1_of_lat`), the per-pin FIFO reads of `FifoFidelity`, a failing
negative control and a non-vacuity run. Drop it if one model is enough.

Suggested JSON update (not made: another agent owns the file):
`bd_delay_gated.gate` -> proved (sufficient), lean
`GcdCells.no_early`/`rises`/`gflush*_of_lat`, counter-trace
`GcdCells.flush_needed`, rule F verdict `missing_term`
`(p i).hi - (q i).lo`; and `bd_c2/c3/c4.sel_order` -> proved by
`ConstraintsSel` once that file is committed.
