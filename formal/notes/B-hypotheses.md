# B-hypotheses: shard B's hypotheses under the gcd_hw capstone (refresh)

Probe Bhyp2 (shard B), 2026-10-29. Notes only: no Lean was written or run, and no route, board or
toolchain was used. This replaces the 2026-10-27 11:40 ledger (probe Bhyp). That ledger's rows
are kept where they still hold, renumbered, and re-pointed at the capstone theorems as they
stand at `398ee1d`.

Sources read:
- the capstone files: `Formal/Net/Capstone*.lean`, `GcdHw*.lean`, `OpsGen.lean`, `Ops*.lean`;
- B's files that touch them: `Cells/RigSrc.lean`, `RigToken.lean`, `LinkHandshake.lean`, and
  every B file cited below at the line given;
- `notes/C-gcd_hw-hypotheses.md` (C-8l, plus the 10k and 8r updates);
- `out/gcd_hw_hypotheses.md` (A, 2026-10-27 11:00);
- `FEASIBILITY.md` ("Fidelity per primitive" and the status block);
- the verdict blocks of JOURNAL-B and JOURNAL-C, and the latest session of each;
- `out/cell_constraints.json` (131 entries; 8 `hypotheses_not_inequalities`).

Name check: every `File:line name` below was grepped as a `theorem|def|structure` declaration in
the working tree. Hypothesis names (H_*) were grepped as text. Where a name exists only in a note
or a docstring, the row says **prose only**.

Grades, as the probe brief defines them:
- **A**: follows from data or is proved.
- **B**: a credible physical hypothesis, not yet tested on this silicon.
- **C**: doubtful, contradicted, failing on some route or corner, or resting on an unmeasured value
  that the verdict depends on.

"Discharged" names the theorem that derives the row. "Open" means nothing derives it.

---

## 0. The structural fact: where B's hypotheses enter the capstone

**What the capstone chain imports from B.** I computed the import closure of `CapstoneWalk`,
`CapstoneLiveNdWalk`, `CapstoneRig`, `CapstoneCut`, `CapstoneWitness` and `CapstoneWitness3`:
69 modules, with the scratch script `/tmp/claude-0/probes/Bhyp2/clos.py`. It contains exactly one
B module, `Formal.Cells.LinkHandshake` (plus `Formal.Cells.Prelim`, which LinkHandshake imports).
From that module the chain uses one **definition**, `LinkHandshake.lean:65 ctlB`: the bd_link_ctl
LUT function inside `Link.H_CEL_SI`. That definition carries no hypothesis.

**So no B cell hypothesis is a Lean hypothesis of any capstone theorem.** The Lean hypotheses are
C's:
- `H_CELLS`: the gate models;
- `H_BUNDLE`: `Held`;
- `H_START_ONCE`;
- `H_ENV`;
- for liveness, `H_BOUNDED_DELAY'`, `H_START_ENV`, `H_ARB_UNCONTESTED_BOUNDED` and
  `H_NO_DEADLOCK'`.

B's hypotheses are what a physical discharge of C's hypotheses would rest on. That discharge goes
through four bridges. **None of the four is mechanised:**

| bridge | what it would prove | Lean today |
|---|---|---|
| **Br1** (C's O4) | each of the 367 operators' gate-model fields from the real LUTs | `OpsGen.lean` binds the cell kinds `fork2_cel` :166, `join2_cel` :181, `steer_bound` :257, `mux_bound` :309, `muxn_bound` :344, `amerge_ack_bound` :379, `link_bound` :405 and `src_bound` :413. Each assumes the physical step form `LutFb` :86 / `LutSI` :90 and `FbFirst` :95. These bindings are not instantiated on `CapstoneNet`. No B file derives `LutFb`/`LutSI` from a timed or Kleene LUT model (grep: no B file mentions `LutFb` or `OpsGen`). Not bound at all: forks with N ≥ 3, C-trees with N ≥ 4, and the arbiter grants `H_ARB1/2`, `H_ARB_EXCL`. |
| **Br2** (C's 8x) | physical circuit → the zero-delay traces on which `Held` and the `dat`/`H_LATCH_*` fields are stated | `CapstoneBundle.lean` (8w): on those traces `Held` is a protocol consequence cell by cell, so tcheck verdicts cannot discharge it directly. 8x exists only as `Wip/C8x` (unclaimed). |
| **Br3** (A's M6, H_SEP) | a physical run sampled on ticks is an SI run | `Bridge*`: proved for persistent NoOvertake networks; not applied to `CapstoneNet` |
| **Br4** (probe Brz, running) | the B reset run (`gNet`) gives the Ops initial state (`init*`, `i*`, `ic`, `io`, …) | none. A different model (gNet, 3322 nodes) |

**The one B theorem that is on a capstone chain:** `RigSrc.lean:500 gcd_rig_first_env`. It is
C's `gcd_rig_first` (`CapstoneRig.lean:267`) with `H_ENV` and the three sources' `SrcR`
discharged from the rig's env cells, through `rig_cellR` :404 and `env_H_ENV` :342. Its B
hypotheses are listed in row **BH24**. They are real Lean hypotheses of a capstone-chain theorem.

### 0.1 The capstone theorems and their Lean hypotheses

| id | theorem | Lean hypotheses | conclusion | non-vacuity |
|---|---|---|---|---|
| S | `CapstoneWalk.lean:636 gcd_hw_circuit_safe3` | `a, b < 2^31`; `H_CELLS : ∀ o, Cell …`; `H_BUNDLE : ∀ c, Held (ch c)`; `H_START_ONCE` | every out0 latch is `Nat.gcd a b` | `CapstoneWitness3.lean:15 gcd_hw_joint_witness3` (a = 12, b = 18, one unit-delay run) |
| R | `CapstoneRig.lean:267 gcd_rig_first` | `H_CELLS_R` (`CellR`: `Src` without `iz`), `H_BUNDLE`, `H_ENV` | first out0 offer and first latch are gcd | **no joint witness** found |
| R' | `RigSrc.lean:500 gcd_rig_first_env` (B) | `H_KER` (C's `Cell` on non-source operators), `H_BUNDLE`, the env hypotheses of BH24 | as R | **no joint witness**. `RigSrc.W.env_nonvacuous` covers only the env lemmas, not the kernel together with the env |
| L | `CapstoneLiveNdWalk.lean:120 gcd_hw_live_final` | `CellI`, `H_BUNDLE`, `H_START_ONCE`, `H_BOUNDED_DELAY'`, `H_START_ENV`, `H_ARB_UNCONTESTED_BOUNDED`, **`H_NO_DEADLOCK'` (open)** | first out0 token within `(1168(8·Lrun+23)+1)(H+1)` ticks, carrying gcd | **none** (C-8z). Its predecessor, 8u's `gcd_hw_live`, is likely vacuous (`CapstoneLiveNdStart.lean:84 start_never_closes`). |
| U | `gcd_hw_arbiters_uncontended3` (CapstoneWalk), `CapstoneLiveArb.lean:161 gcd_hw_never_contested` | as S | no arbiter stage ever faces a free contest | via S's witness |

**Fields of `H_CELLS`** (`CapstoneNetDef.lean:373 Cell`), each with the B rows that would
discharge it physically:

| structure | fields | B rows (via Br1/Br2) |
|---|---|---|
| `Fork.Fork` (OpsFork:29) | `wire`, `cel`, `dat`, `initA`, `initO` | BH6, BH7 (cel); BH3 (wire, FIFO); BH8 (dat, via Br2); BH9 (init, via Br4) |
| `Join.Join` (OpsJoin:35) | `cel`, `wire`, `dat`, inits | BH6, BH7; BH8/BH14 (dat) |
| `Steer.Steer` (OpsSteer:39) | `lut` (request and select read at the same tick), `orr`, `dat`, inits | BH10, BH4, BH5 |
| `Mux.Mux` (OpsMux:257) | `cj0`/`cj1` (isochronic ctl_req fork), `zr`, `xa`, `ya`, `ca`, `dat`, inits | BH11, BH13, BH15 |
| `MuxN.MuxN` (OpsMuxNOp:35) | `cj`, `zr`, `xa`, `ca`, `dat` | BH12, BH13 |
| `CM.AMerge` (OpsCM:163) | `H_ARB1`, `H_ARB2`, `H_ARB_EXCL`, `zr`, `H_AMERGE_RTZ`, `xa`, `ya`, `dat` | BH17-BH20, BH13, BH14 |
| `Link.Link` (OpsLink:130) | `H_CEL_SI` (= `ctlB`), `H_ACK_DI`, `H_REQ_DI`, `H_LATCH_OPEN`, `H_LATCH_HOLD`, `ic`, `ii`, `io` | BH1 (ctlB, discharged), BH6, BH8, BH9, BH16 |
| `Capstone.Src` (CapstoneSrc:19) | `H_LUT_SI`, `dat`, `iz` | BH24 (rig form: `SrcR` proved by `rig_cellR`; `iz` false, `iz_fails` :647) |
| `Ops.Gcd.Sink` (OpsGcd:43) | `wire`, `init` | H_SINK_SI (**prose only**, B-rig-src; open) |

---

## 1. The ledger

Column key:
- **chain**: the capstone hypothesis the row would discharge, and through which bridge;
- **side**: the row is used only by results that are not on the capstone's Lean path.

### 1a. LUT and primitive fidelity

**BH1. The LUT computes its INIT on its real pin map** (H_LUT_FN; A's M4/M5).
- *Lean:*
  - `LinkHandshake.lean:65 ctlB` (used by `Link.H_CEL_SI`);
  - `OpsGen.lean:397 link_gate`: the generated bd_link_ctl LUT equals `ctlB`;
  - CElemFn, Latch, ArbKleene, Lib1/Lib2 (each INIT equals its header equation);
  - `Formal/Gen` (163 theorems; `formal/tools/gen/gen.sh --check`);
  - OnNetlist (link/arb bits read back on 4 seeds).
- *Statement:* each control LUT's output is its INIT's function of its physical pins.
- *Grade:* A per cell. B for the whole gcd_hw bitstream (M5: research's `fasm2net` reports
  11619/11619 LUT functions equal; that check is not in Lean).
- *Status:* discharged for `ctlB` (`link_gate`, kernel decide); open for the whole bitstream.
- *Use:* **chain** (`Link.H_CEL_SI`'s function; Br1 for the other kinds).
- *Test:* `formal/tools/gen/gen.sh --check`. Extend `formal/tools/fasm2lean2/check.sh` to the
  gcd_hw FASM (3-5 d).
- *Vacuity:* none (a function identity).

**BH2. H_KLEENE_LUT: one 2:1 pass-transistor mux with a mid-rail select passes equal legs.**
- *Lean:*
  - `Core/LutTree.lean:279 H_mux_kleene` (A), with `node_sound` :296 and `root_sound` :323;
  - `MuxTree.lean:101 muxTree_eq_lutK` (tree = closure semantics in any pin order);
  - the timed per-pin form H_MUX_KLEENE (text in `CElemStrict`, `CElemStrict2`, `LibGapLatch`,
    `NoRevert`);
  - KleeneBox `*_K` (the select boxes are unchanged in K3).
- *Statement:* a mux whose select is X and whose legs agree outputs the legs' value.
- *Grade:* B. Credible for clean or late selects. Doubtful for a mid-rail select while the legs
  move. Audit row 88: the "optimistic hazard-free extension" (probe Bpess running).
- *Status:* open (unmeasured).
- *Use:* **side**. It is used by the ternary reset certificates (ResetGcd*), by KleeneBox, by
  tcheck's Fd/H_CLEAN_EDGE arguments, and by A's Events8. It sits under Br1/Br3 only as hazard
  freedom.
- *Note:* it does NOT give H_NO_REVERT (`NoRevert.lean:561 kleene_revert`: one moving pin, the
  root shows `0,1,0,1`).
- *Test:* a board glitch counter on a LUT with equal legs and a slowly ramped select.
- *Vacuity:* A's exact Kleene timed tree meets it (`NoRevert.exact_mux_mono`, A's
  `sic_glitch_free`).

**BH3. H_NO_REVERT and the FIFO family: one input edge gives one output edge.**
- *Names:*
  - H_NO_REVERT: `WinFifoCausal.lean:64 NoRevertI` and `WinFifo.NoRevert`;
  - the FIFO hypotheses H_LUT_FIFO, H_PIN_FIFO, H_TREE_FIFO, H_WIRE_FIFO (`PipeTimed.Ret` form);
  - H_MUX_MONO + H_PIN_MONO (`NoRevert.lean:517 root_mono`), a sufficient per-mux form;
  - A's NoOvertake;
  - the monotone causal read maps (`Mono`, `hβm`/`hγm`/`hφ*m`) of the per-pin box files and of
    RigSrc.
- *Statement:* inside one input edge's uncertainty zone, once the output shows the new value it
  keeps it. Pins and wires deliver edges in order.
- *Lean:*
  - `WinFifo.lean:151 win_glitch_not_fifo`: `Win` alone is never FIFO once `hi ≥ lo + 2`;
  - `:405 no_revert_of_ret`;
  - `WinFifoCausal.lean:438 stage_fifo`, `:810 pipe_fifo`, `:1127 no_revert_needed`;
  - `WinFifoN.lean:623 pipe_ctl_w`;
  - the NoRevert channel table: inertial, transport and event channels give it; `Win` and C's
    `BoundedDelay` do not.
- *Grade:* B (an inertial-type CMOS property).
- *Status:* open on silicon. It is reduced to `Win` + H_NO_REVERT for the pipe LUTs and the
  steer. H_TREE_FIFO is not reducible (the select excitation glitches).
- *Use:*
  - **chain**: R' (the env read maps of `gcd_rig_first_env` are monotone, i.e. H_PIN_FIFO /
    H_WIRE_FIFO on uenv0, uenv1 and c3; `RigSrc.c3_move` also needs H_LUT_FIFO);
  - Br1/Br3 (Bridge needs NoOvertake);
  - **side**: every B timed cell theorem (PipeTimedN, OpsTimed*, ContractsTruncCel, CTreeExact,
    ArbPin2, NecessityMerge, ConstraintsSel).
- *Test:* a LUT-ring or chain edge count (no extra edge per revolution). Routed GLS with
  `GLS_MODEL=fid` (transport per level): count output edges per input edge.
- *Vacuity:* `NoRevert.lean:256 transport_witness`.

**BH4. H_LUT62_SHARED_READ: O5 and O6 read a shared pin at one instant.**
- *Lean:* `TernaryOnBits2.lean:325 SiteSync`; ArbOverlapRace `Decomp`.
- *Grade:* B.
- *Status:* open. CElemStrict2's per-output latch theorems do not need it.
- *Use:* **chain via Br1**, for the steer `lut` field (bd_steer is a LUT6_2 pair) and the
  arbiter's ustate/ugrant. Otherwise side.
- *Test:* a CARRY4 TDC on the O5 vs O6 skew from one pin.
- *Vacuity:* none known.

**BH5. The select X window: H_ATOMIC_LUT, `wa`, H_X_UNIFORM.**
- *Lean:*
  - `CElemStrict.lean:288 env_latency_iff` (exact, with `wa`), `:297 env_latency_strict`
    (`wa = 1`), `:306 env_latency_atomic` (`wa = 0`);
  - KleeneBox **H_X_UNIFORM** (text, `KleeneBox.lean:29`): every binary edge carries an X window
    `[T−a, T+c)` with the same `w = a + c` on every edge. Then every setup and hold gains `+w`:
    `:195 steer_edges_K`, `:401 join_edges_K`, `:520 latch_edges_uniform`.
- *Statement:* a moving select is X for a window of width `w ≥ 1` tick, the same width at every
  edge.
- *Grade:*
  - B for "some `w ≥ 1` tick exists";
  - **C for "uniform"** (the slew differs per net and is unmeasured; probe Bxw on non-uniform
    windows is running).
- *Status:* open. No gcd_hw margin is within a few ps of 0, so no verdict depends on `w`
  (Rc worst +55 ps guarded, Br).
- *Use:* **side**. It decides only `≤` vs `<` in B's exact iffs, which sit under Br1/Br2.
- *Test:* a TDC on a LUT select ramp, to measure the X width per net.
- *Vacuity:* `KleeneBox.lean:278 steer_witness_K` and `join_witness_K` (X on every edge, strict).

### 1b. C-element and latch races

**BH6. Feedback first: H_FB_FIRST / H_ENV_LATENCY / H_SEL_ORDER / RT_FB.**
- *Lean:*
  - C: `OpsGen.lean:95 FbFirst`, `Timing/FbFirstRt.lean:136 fbFirst_of_resp` (from RT_FB under
    H_RESP_ONLY, **prose**), `fbFirst_witness` :193, `OpsGen.fb_stale_breaks` :216;
  - B: the exact strict race `CElemStrict.env_latency_iff` and `CElemStrict2.lean:323 c2n_all`
    (with `c3_all`, `c4_all`, `c2set_all`);
  - per pin: `ConstraintsSel.lean:237` (H_SEL_ORDER as a hypothesis), `:272 sel_order_of_lat_gen`,
    `FifoFidelity.lean:173 sel_phase`.
- *Statement:* when a C-element's output changes, its own feedback reaches its select before any
  response the output provokes reaches a non-feedback pin. Strict form:
  `dlmax + dwmax + wa ≤ dlmin + E`. Per pin: `w_hi + SP[fb].hi ≤ E + min SP[dep].lo`.
- *Grade:*
  - kernel C-elements: B (tcheck Rc passes on all 363 per route at fast, slow, fastG and slowG);
  - **rig uenv1: C**. The banded Rc is −117/−221 ps on seed 2 and −86/−243 ps on seed 4
    (C-10h:168-170).
- *Status:* discharged per route by tcheck Rc, modulo hand identification (8w matches it as data).
  Open at uenv1.
- *Use:*
  - **chain**: Br1, for every `cel`, `H_CEL_SI` and `cj` field;
  - R', where it appears as the step-form hypotheses `H_UENV1_B` and `M1`. These are false when
    uenv1's feedback is stale: `RigToken.lean:765 stale_fb_extra_start` gives 3 start offers
    against 1 result.
- *Test:*
  - `formal/tools/tcheck/run10k.sh d 2 3 4` (Rc rows);
  - routed GLS of `gcd_rig` on seeds 2 and 4 at the fast corner: exactly one `start_req` rise
    between consecutive `res_req` rises;
  - the fix candidate: LOCK_PINS uenv1's feedback to A5/A6.
- *Vacuity:* the hypotheses are witnessed (`fbFirst_witness`; CElemStrict2's per-INIT runs).

**BH7. C-tree latency and atomicity: H_CTREE_ATOMIC vs H_CTREE_LOOP.**
- *Lean:*
  - C: H_CTREE_ATOMIC is **prose only** (`OpsFork.lean:13`, OpsJoin, OpsGen). The model treats a
    C-tree as one C-element.
  - B: `CTreeExact.lean:969 tree_box_exact` (any shape and depth, real bd_c2/c3/c4 INITs, per-pin
    box). It is exact iff **H_CTREE_LOOP**: for every node n and child c,
    `Qhi(n) ≤ dist_min(n→root) + E + MaxMin(c) + lo(c→n)`.
  - `CTreeTimed.lean:1174 tree_four_phase` (sufficient).
- *Grade:* B.
- *Status:* exact in Lean, **unchecked on every route**. 8w: C7 has no tcheck rule.
- *Use:* **chain via Br1**, for the forks with N ≥ 3 and the joins with N ≥ 4. OpsGen does not
  bind these.
- *Test:* a tcheck row for H_CTREE_LOOP per tree node (from `bd_ctree` instances in the routed
  netlist).
- *Vacuity:* `tree_box_exact` has both sides witnessed (B-ctree-exact).

**BH8. Latch capture: setup data, setup pulse, hold, loop bound, fork data.**
- *Names:* H_SETUP/H_PW/H_HOLD/H_LOOP (L1-L4); `H_FORK_DATA_W`; C's H_LATCH_OPEN/H_LATCH_HOLD.
- *Lean:*
  - `Bundling.lean:601 capture`;
  - `ForkData.lean:140 fork_capture`, `:235 fork_data_needed` (a 1 ps violation leaves the latch
    stale);
  - `OnNetlistTimed2.lean:82 latch_rule_h_net`;
  - LibGapLatch (box exact);
  - LinkExact `exact` :804 (one link stage, scope `Wf`/`Split`);
  - KleeneBox `latch_edges_uniform`.
- *Statement:*
  - setup data: `Td + dhi + fhi ≤ Tr + rlo + wlo + elo` (+1 strict);
  - setup pulse: `ehi + fhi ≤ wlo + elo`;
  - hold: `ehi ≤ alo + dlo`.
- *Grade:* B.
- *Status:* rule-checked per tcheck route: I 300/300, H 630/632 (2 band-only), W min +346 ps
  fastG. Rule I lacks the latch's I2 feedback-pin arc (audit row 82; covered by the guard band).
- *Use:* **chain via Br2**: the zero-delay `Link.H_LATCH_OPEN/HOLD` and `Held` downstream of a
  latch. This is NOT a direct discharge of `H_BUNDLE` (8w).
- *Test:* `formal/tools/tcheck/run10k.sh` (I/H/W rows), with the I2 arc added (rule I').
- *Vacuity:* LinkExact `witness` :917.

**BH9. Reset: per-cell width and the design reset.**
- *Names:* H_RST_PULSE / H_RST_LONG (C5); H_RST_HELD; H_HOLD_LONG; H_RST_LOW; H_RST_BEFORE_LOOP;
  H_STEER_HOLD; H_NO_RETURN.
- *Lean:*
  - `CElemStrict2.lean:510 reset_width_iff`, `:519 reset_width_strict`;
  - `ResetGcd.lean:199 gcd_reset_binary`;
  - `ResetGcdWave.lean:447 gcd_first_wave` (H_NO_RETURN for the release window, for every rst
    waveform);
  - `:694 gcd_loop_late`, `:726 gcd_clean_release`;
  - `ResetGcdVec2.lean:734 gcd_reset_vec_of_net`;
  - NecessityReset.
- *Grade:*
  - B. In `gcd_hw.v`, rst is `~por_done | rst_sr[15]`, about 16 hk cycles or 121 ns, against a
    23(D+W+1)+W step bound.
  - The residual H_RST_BEFORE_LOOP (`W < 34` GMW steps) is unchecked.
- *Status:* proved in **gNet**, a different model. **Not linked** to the Ops `init*`/`i*`
  fields (Br4; probe Brz running).
- *Use:*
  - **chain via Br4**: every init field of `H_CELLS`;
  - otherwise side.
- *Test:* routed SDF: max rst-pin delay < 34 fast-min LUT+wire steps on
  `ulink_n1__1 → ucmpi0 → join → steer`; GLS of the housekeeping logic (`por_done` never rises
  on the edge where `rst_sr[15]` falls).
- *Vacuity:* `SelfAuditB2.wave_witness`.

### 1c. Select, RTZ and index at the steer, mux, muxn and amerge

**BH10. Steer select at the pins (setup and hold).**
- *Lean:* `LibGapSteer.lean:188 steer_box_exact` (iff: `S0 + Shi ≤ R + Rlo` and
  `F + Rhi ≤ S1 + Slo`), `:224 spurious_token`; KleeneBox `steer_box_exact_K`.
- *Grade:* B.
- *Status:*
  - setup: rule E 465/472, band-only failures. Rule E has no site pins, so it is optimistic in
    the box by up to `SP[s].hi − SP[req].lo`.
  - **hold: no rule** (unchecked).
- *Use:* **chain via Br1/Br2**: `Steer.lut` reads the request and the select at the same tick.
- *Test:* `cells/verify/skew.py` (rule E) with FASM site pins (E'); a new steer-hold row in
  tcheck.
- *Vacuity:* `steer_witness_K`.

**BH11. Mux join select and the ctl_req fork (X3, X4).**
- *Lean:* `LibGapMux.lean:393 join_box_exact` (the request and feedback pins drop out),
  `:439 wrong_branch_latched`; KleeneBox `join_box_exact_K`.
- *Statement:* `s` is settled before `ctl_req` is read at uj0/uj1, and held past its fall. The
  `ctl_req` fork to uj0/uj1 is (weakly) isochronic, as `Mux.cj0/cj1` model it.
- *Grade:* **C pending**.
- *Status:* rule K (C-10l, WIP) FAILS 16-26 of 42 rows per seed at every corner, unguarded too,
  worst about −5.9..−9 ns. Undiagnosed (10l2 has not landed).
- *Use:* **chain via Br1** (`Mux.cj0/cj1`).
- *Test:* `formal/tools/tcheck/run10l.sh` (rule K); a GLS monitor at each `umux*.uj0/uj1` (the
  ctl_req pulse has ended before `s` changes).
- *Vacuity:* n/a. Note that an over-conservative late side and a real violation are both still
  possible readings of rule K.

**BH12. bdc_muxn3 select and decode.**
- *Names:* H_MUXN_SEL; **H_YOSYS_MAP** (the inferred decode LUT3 INITs).
- *Lean:* `LibGapMuxN.lean:324 join_exact_fixed`; KleeneBox `muxn_sel_box_exact_K`.
- *Grade:* B.
- *Status:* **unchecked**. 8w found no rule-E row for `umux21`'s select, although C's ledger says
  rule E covers it.
- *Use:* **chain via Br1** (`MuxN.cj`).
- *Test:* add `umux21` (select from `ULINK_N_INDEX_97`) to the rule-E/tcheck rows.
- *Vacuity:* none known.

**BH13. Return to zero at the mux and amerge ack C-elements.**
- *Names:* H_MUX_RTZ (X1); A3; C's `Mux.xa/ya` and `AMerge.H_AMERGE_RTZ`.
- *Lean:* `MuxRtzTimed.lean:113 rtz_safe`, `mux_rtz_env_safe`; NecessityMuxRtz.
- *Grade:* B.
- *Status:*
  - X and Xi: 0 failures unguarded; band failures on the steer-OR muxes.
  - Z: all 9 stages pass, worst +383 ps (C-10k).
  - Xc/Xm: 1-2 band failures (`umux11`).
- *Use:* **chain via Br1**.
- *Test:* `run10k.sh` (X, Z); `run10l.sh` (Xc, Xic, Xm); a GLS monitor that x_ack and y_ack are
  low at every z_ack↑.
- *Vacuity:* none known.

**BH14. Amerge index bundling (`won = g2 | in1_ack`).**
- *Names:* H_AMERGE_IDX = H_BUNDLED_IDX.
- *Lean:* `ForkData.lean:360 amerge_idx_sufficient`, `:384 amerge_idx_necessary`.
- *Grade:* B.
- *Status:* rule Z passes. `idx_ack_fork` has no rule. 8w: the stage-1 bus `acc251` of the
  amerge3 cascade has no rule.
- *Use:* **chain via Br2** (`AMerge.dat`, `Held` on the index channels).
- *Test:* `run10k.sh` (Z); a new row for `acc251`.
- *Vacuity:* none known.

### 1d. Matched delay lines

**BH15. Gated delay flush.**
- *Names:* H_GFLUSH; H_LO_ORDER; H_BAL_HI; H_START; H_SHORT; C's H_FF_DRAINED.
- *Lean:*
  - `GcdCells.lean:151 no_early`;
  - `LibGapDelay.lean:282 flush_of_gflush`;
  - `:490 box_exact_flushed` (exact under the side conditions);
  - `:571 rescue_flushed` (per-stage H_GFLUSH is not necessary without H_LO_ORDER).
- *Grade:* B unguarded; **C under the band**.
- *Status:*
  - Fd: 29/29 per route unguarded.
  - Band failures: `ucontrol_merge12` (seed 3 −343, seed 4 −522 ps slowG) and `ushrsi3`
    (seed 4 −160).
  - H_LO_ORDER: unchecked on every route.
  - Rule F is not sufficient (C-10k).
- *Use:* **chain via Br1/Br2** (`Mux.zr`/`AMerge.zr` is H_DELAY_LUMPED, grade A by construction;
  the flush is what makes the physical request not early).
- *Test:* `run10k.sh` (Fd); a per-route H_LO_ORDER row; T1 for the band.
- *Vacuity:* none known.

**BH16. FASTFALL / FASTRISE line flush in links.**
- *Names:* H_FLUSH; H_ACK_FLUSH; H_RST_LINES.
- *Lean:* `Bundling.slow_not_early`; PipeTimedN; ConstraintsFastFall.
- *Grade:* B.
- *Status:* rule F lacks the in-flight term (audit row 83). FASTRISE is **unchecked**.
- *Use:* **chain via Br1** (`Link.H_ACK_DI`/`H_REQ_DI` are A by construction; the flush is the
  physical premise).
- *Test:* rule F with the in-flight term; a FASTRISE dual row.
- *Vacuity:* none known.

### 1e. Arbiter

These rows are the physical content of `AMerge.H_ARB1`, `H_ARB2` and `H_ARB_EXCL`. None of the
three is bound in OpsGen.

**BH17. H_A0_FORK: A0's fall reaches ua_k before A0 → ustate → q → ugrant → g_k does.**
- *Lean:*
  - `ArbA0Fork.lean:258 no_early_ack_iff`, `:398 box_safe_iff`;
  - gcd_hw: `OnGcdArbA0.lean:175 fork1_box_iff`, `fork2_box_iff`, and
    `:2963 gcd_corner_srv` (every corner row: both forks safe);
  - κ: `OnGcdArbKappa.lean:3052 design_lit_safe` (`H_KAPPA : κ ≤ 16587/374773 ≈ 0.0443`, lit
    reading).
- *Grade:* B at one consistent corner. **C** in the independent box (the client-1 fork is
  negative on some rows; `boxRows_okSrv_count` = 20/36) and for κ > 0.0443 (κ is unmeasured).
- *Status:* **proved on the routed gcd_hw numbers at each corner** (36 arbiters × 4 corners;
  untrusted extraction `Bar/a0extract.py`). Jx 72/72 unguarded, 71/72 under the band.
- *Use:* **chain via Br1** (`H_ARB_EXCL`, `H_ARB1/2`); **side**: OnGcdArbKappa.
- *Test:* `cells/verify/arb_fork.py` (rule J) with site pins (J'); T5 (arbiter handover on one
  die, q on A3 vs A5); a κ measurement on the A0-branch vs ustate/ugrant tails.
- *Vacuity:* `design_gate_nonvacuous` :3352, `row_safe_nonvacuous` :245. Audit row 19: "tight" is
  mildly OVERSTATED and is withdrawn.

**BH18. RT1/RT1b: grant exclusion across a handover.**
- *Lean:* `OnGcdArbFix.lean:1080 gcd_rt1_all`, `:1088 gcd_rt1b_all` (every server);
  `ArbHeldTimed.rt1_exclusion`, `ArbHeldTimed2.rt1_exclusion2`; OnGcdArbKappa `rt1_gate`.
- *Grade:* A at one corner (proved on routed numbers). C in the box (server-free negative on most
  box rows; the box needs a server path ≥ 711 ps).
- *Status:* proved per corner, 36 × 4 × 2 directions. Seed 2 `merge10.uarb1` RT1 is the
  thinnest (172 ps FMIN).
- *Use:* **chain via Br1** (`H_ARB_EXCL`).
- *Test:* T5; a lower bound on the routed server path.
- *Vacuity:* as BH17.

**BH19. RT2/RT2b and the server minimum.**
- *Names:* H_SERVER_MIN; H_SERVER_GRAPH (`srv`); `Scn`.
- *Lean:* `OnGcdArbA0.lean:437 rt2_box_iff`; `gcd_corner_srv` (needs `r.srv ≤ D.smin`); 
  `cornerRows_allOk_count` = 141/144 server-free, `cornerRows_okSrv_count` = 144/144 with the
  server bound.
- *Grade:* B.
- *Status:* proved per corner row with the graph server bound. The bound `srv ≤ D.smin` is
  itself an environment hypothesis that is not checked on the route.
- *Use:* **chain via Br1** (`H_ARB_EXCL`, `H_ARB1/2`).
- *Test:* a routed number for the ustate O5 → A0 driver path, against `srv`; T5.
- *Vacuity:* row witnesses in OnGcdArbA0.

**BH20. No free contest (the request-separation, tie and metastability tier).**
- *Names:* H_REQ_SEP; H_GRANT_SKEW; H_BBM1/2; H_EXCL_REQ; the R3 tier.
- *Lean:* `ArbBinary.lean:435 exclusion_transport`; `CElemInvolution.c2_eternal`,
  `ArbInvolution.arb_grants_eternal` (why no deadline exists).
- *Grade:* A within the model.
- *Status:* **discharged in the model** by U (`gcd_hw_arbiters_uncontended3`,
  `gcd_hw_never_contested`). This removes only this tier: the handover rows BH17-BH19 are still
  needed for `H_ARB_EXCL`. Physically the discharge rests on Br3 (A's D2 H_SEP).
- *Liveness counterpart:* `H_ARB_UNCONTESTED_BOUNDED` (`CapstoneLiveArb.lean:71 ArbUnc`): an
  uncontested request is granted within `H`. B has no separate theorem for it. It follows from
  bounded LUT delays.
- *Use:* chain (S and U conclusions; L's hypothesis).
- *Test:* board: count contested grants; GLS monitor for both requests high with no grant held.
  `cells/hw/arb_mtbf.v` + `arb_mtbf_measure.py` for the tier itself.
- *Vacuity:* n/a.

### 1f. Delay and corner model (under every numeric row above)

**BH21. One shared corner, per-arc scatter κ, endpoints.**
- *Names:* H_SHARED_CORNER; H_SCATTER κ; H_ENDPOINTS; H_AFFINE; H_DISJ; H_DIV; H_ONE_CORNER; the
  band 0.772/1.155.
- *Lean:*
  - `Core/Substrate/CornerNat.lean:21-23, :118` (A);
  - `ConstraintsKappa.lean:310 allOK_iff_gen` (exact under H_DISJ + H_DIV);
  - `:450 box_unsound_with_kappa`, `:458 one_corner_unsound_with_kappa`, `:470 slow_only_unsound`;
  - OnNetlistArbKappa (link_arb); OnGcdArbKappa (gcd_hw).
- *Statement:* every arc of a margin sits at one die corner, within `1 ± κ` of its interpolated
  nominal.
- *Grade:* B for the form. **C for the value**: κ is unmeasured, one silicon ring was measured,
  A withdrew 0.311.
- *Status:* open.
  - Every residual C of this ledger is band- or κ-only: Rc uenv1, Fd cm12/ushrsi3, Xc umux11,
    Jx merge12, A shrsi1.
  - Audit row 18: the link_arb "exact per-pair thresholds" are OVERSTATED, because the gap
    κ*..κ*+6/(E+L) is undecided (probe Bkx18 running).
  - `out/cell_constraints.json` `conventions.corner_rule` still says the box is "always sound".
    That is false for κ > 0 (stale; probe Bj5).
- *Use:* under every numeric verdict (chain via Br1/Br2); side for the κ files.
- *Test:* T1, an on-die differential two-path measurement. It gives κ and decides every band-only
  C row.
- *Vacuity:* `design_gate_nonvacuous`.

**BH22. Site pins and the pin permutation.**
- *Names:* H_PIN_READ (`Rd` maps); A's S6.
- *Lean:* LibGap* `Rd`; PinAssign; ArbCornersPin; OnGcdArbA0 (physical pin per element).
- *Grade:* A as a fact (read from the bits).
- *Status:* tcheck and Bar use prjxray site pins. The shipped rules J and E do not.
- *Use:* every numeric row.
- *Test:* LOCK_PINS, or a FASM-pin site-pin table in `arb_fork.py`/`skew.py` (about 0.5 d).
- *Vacuity:* n/a.

**BH23. H_RF_ASYM: rise = fall within a corner column.**
- *Lean:* text in MuxRtzTimed, ArbHandover, ArbHeldTimed, ArbCorners.
- *Grade:* B. Unmeasured.
- *Use:* every numeric row.
- *Test:* a CARRY4 TDC.

### 1g. The rig environment (on the R' chain)

**BH24. The env ring as the source model.**
The hypotheses of `RigSrc.lean:500 gcd_rig_first_env`, all real Lean binders:

| binder | plain statement | grade | discharged? |
|---|---|---|---|
| `H_FORK_WIRE` | a/b/start req = `env_c` (`bd_fork #(3)` is wires) | A (RTL: the fork's req outputs are wires) | by construction; not checked in Lean against the netlist |
| `H_DAT` | the a/b buses are constant `srcV a b` | B (the idx-under-rst contract; `RigIdx.lean:314 idx_setup_iff` exact) | open on a route (margin about 16 hk cycles) |
| `H_REL`, `H_REL0` | at release `env_c = 1`, `in_ack = 0`, `env_c0 = 0` | B (`RigToken.uenv1_release`, `uenv0_release`, under H_UENV1_HOLD exact: `:663 short_rst_many_starts`) | proved from the reset hypotheses, which are open (BH9) |
| `H_OUT0_ACK` | `out0.ack = env_c0` | A (RTL wire) | by construction |
| `H_UENV1_B`, `M1`, `M0` | uenv1/uenv0 move only to their C-element function of pins read through monotone causal maps | B for the form. **C at uenv1**, whose feedback-first race (BH6) fails under the band on seeds 2 and 4 | open |
| `H_C3` | the fork's `bd_c3` moves to its inputs read through monotone maps (`c3_move`, under H_LUT_FIFO, H_FB_FIRST, H_RST_ONE_FALL) | B | open |
| monotonicity/causality of `β, γ, φ1, φ0` | H_PIN_FIFO / H_WIRE_FIFO (BH3) | B | open |

- *Not covered:*
  - laps ≥ 2. C proves re-arming fails at every re-offer (`CapstoneRig.rearm_fails_at_reoffer`);
    probe Blap is running.
  - **H_SINK_SI** (**prose only**): the rig's out0 capture against C's `Sink` model.
  - `Src.iz` is false at release (`RigSrc.lean:647 iz_fails`). C's `preRun` supplies it, so this
    is not a gap.
- *Vacuity:* **no joint witness for `gcd_rig_first_env`**. `W.env_nonvacuous` witnesses only the
  env lemmas. A witness would be C's `chW` re-timed with an env lap (estimate ½ d).
- *Test:* routed GLS of `gcd_rig` on seeds 2 and 4 at the fast corner (one `start_req` rise
  between consecutive `res_req` rises); board #1, `cells/hw/board.sh python3
  cells/hw/gcd_measure.py` (16/16 vectors, `err_sticky=0`).

**BH25. Rig idx setup and verdict hygiene.**
- *Names:* H_IDX_SETUP; H_ARM_BEFORE_IDX; H_RESULT_FRESH; C_STALE.
- *Lean:* `RigIdx.idx_setup_iff`; `RigContract.verdict_current`.
- *Grade:* B.
- *Status:* open on a route.
- *Use:* **side** (measurement, outside the theorem).
- *Test:* routed SDF of idx → d pins vs 16 hk periods; GLS of the errv capture.

### 1h. Contract route (side only)

**BH26.** These are not applied to gcd_hw:
- `Contracts.net_refines_ports`, `ContractsTrunc.net_refines_causal`;
- the hypotheses they add: H_X_LEAD, H_ROUT/H_AIN, the mux identification hypotheses, and
  `Port`'s infinitely many edges (gap G4: under H_START_ONCE, `start` has one token).
- Grade B. **Side.**

---

## 2. Summary: chain vs side

| row | chain (bridge) | side only |
|---|---|---|
| BH1 | yes (`ctlB` discharged; Br1 for the rest) | |
| BH2 | (Br1/Br3, hazard freedom) | reset certificates, KleeneBox, tcheck Fd, A's Events8 |
| BH3 | **R' (Lean binders)**, Br1/Br3 | all timed cell files |
| BH4 | Br1 (steer, arbiter) | |
| BH5 | | yes (`≤` vs `<` only) |
| BH6 | Br1; **R' (`H_UENV1_B`, `M1`)** | |
| BH7, BH10-BH19 | Br1/Br2 | the κ files |
| BH8, BH14 | Br2 | |
| BH9 | Br4; R' (`H_REL`) | ResetGcd* (gNet) |
| BH20 | discharged in model (U); L's `H_ARB_UNCONTESTED_BOUNDED` | |
| BH21-BH23 | under every numeric verdict | |
| BH24 | **R' (Lean binders)** | |
| BH25, BH26 | | yes |

Open Lean work that would put B rows on a Lean chain, cheapest first:
1. a joint witness for R' (½ d);
2. a B lemma deriving OpsGen's `LutFb` from `Win` + H_NO_REVERT + FbFirst for one bd_c2n, which
   is the first step of Br1;
3. H_SINK_SI;
4. Br4 (probe Brz).

---

## 3. Contradictions between B's ledger and C's (and A's `out/gcd_hw_hypotheses.md`)

K1. **Where B's rows sit.** C-ledger §2/§4 and A's tree (§1) draw "⇐" arrows from B's C1-C4 and
L1-L5 to `H_CELLS`, through O4. In Lean the capstone imports only `ctlB` from B. The OpsGen
bindings are not instantiated, and no B theorem derives their premise `LutFb`/`LutSI`. Those
arrows are unmechanised (§0, Br1).

K2. **H_BUNDLE.**
- The claim: C-ledger §3 and A's tree say "H_BUNDLE ⇐ rules A, E, I, H, W, F/Fd, X".
- The conflict: C's own 8w (the `CapstoneBundle.lean` header) says tcheck cannot discharge
  `Held` on the capstone's zero-delay traces. There it is a protocol consequence, and the timing
  content is in the 8x refinement (WIP, unclaimed).
- B's capture and select theorems (BH8, BH10, BH11, BH14) feed that refinement, not `Held`
  directly.

K3. **H_START_ONCE is stale as the rig's hypothesis.**
- The claim: A's §2.6 says "env ring not modelled; Lean: model the env ring (~0.5 d)", and C's
  8r update says the same.
- The conflict: C's `gcd_rig_first` replaces H_START_ONCE by `H_ENV` for the first result. B's
  `RigSrc.gcd_rig_first_env` discharges `H_ENV` and the sources' `SrcR` from the env cells.
- What remains open: laps ≥ 2 and H_SINK_SI.

K4. **uenv1.** A's §2.2 says uenv1's RT_FB failure "hits H_START_ONCE's realisation, not
H_CELLS". On R' it hits the Lean binders `H_UENV1_B`/`M1` of `gcd_rig_first_env`, so it is a
capstone-chain hypothesis, graded C.

K5. **H_AMERGE_RTZ.**
- C-ledger §2: grade C, "unchecked by every rule". C-ledger §3: "UNCHECKED".
- C's 10k update in the same file: rule Z passes on all 9 stages (worst +383 ps). A grades it B.
- The body of C's ledger is stale. B: grade B.

K6. **The X4 ctl_req fork.** C-ledger §3 says "UNCHECKED". Rule K exists (10l) and FAILS 16-26
of 42 per seed, unguarded too. B grades it C pending (BH11).

K7. **H_MUXN_SEL.** C-ledger §2 says rule E covers `umux21`'s select. C's 8w found no rule-E row
for it. B: unchecked (BH12).

K8. **Reset.**
- C-ledger §2 H_RESET says "testbench reset is µs scale". gcd_hw's rst is about 16 hk cycles
  (≈ 121 ns; B-reset-gcd).
- C grades the init fields B without noting that they are not linked to any reset proof. B's
  proofs are in gNet (Br4 open).
- `Src.iz` is false for the rig (`iz_fails`).

K9. **"FIFO LUT" under H_CEL_SI.**
- C-ledger §2 says the C-element model holds of the real LUT under B's C1-C4, citing
  H_KLEENE_LUT as the test of H_LUT_SI.
- B: the FIFO premise (C4) is H_NO_REVERT. It is not derivable from `Win`
  (`win_glitch_not_fifo`) and not implied by H_KLEENE_LUT (`kleene_revert`).
- It needs its own test (a LUT-ring edge count), separate from the glitch counter.

K10. **The arbiter.**
- A's §2.3 says "contention: discharged by proof", and C-ledger §2 says H_ARB_EXCL rests on
  "rule J".
- B: contest-freedom (U) removes only the tie and metastability tier (BH20).
- `H_ARB_EXCL` still needs the handover rows A0 fork, RT1/RT1b, RT2/RT2b and the server bound.
  These are proved per corner on the routed numbers (OnGcdArbFix; OnGcdArbA0 `gcd_corner_srv`,
  144/144 with `srv`, 141/144 server-free).
- They are C in the box (`okSrv` 20/36) and for κ > 16587/374773.

K11. **The Jx count.** C says 71/72; B's old ledger said 72/72. Same data: 72/72 unguarded and
71/72 under the band (guarded worst −9 ps, seed 4 merge12.uarb2 client 2).

K12. **Rule F vs Fd.** C-ledger §3 grades the drain row through rule F ("113/116"). C-10k shows F
is not sufficient for H_FF_DRAINED (incomparable to Fd). B's `no_early` premise is Fd's form, and
its exact version needs H_LO_ORDER, which is unchecked. Cite Fd.

K13. **C3 per pin.** C-ledger §4 says "C3 is unchecked". tcheck's Rc uses prjxray site pins, and
Br found 0 per-pin negatives at one corner on the `--freq 100` routes. C3 is covered within
tcheck's site-pin model, and still open at the box and the band.

K14. **The corner rule.** C-ledger §3 grades H_ONE_CORNER plus the band as B. The JSON (B's own
file) still calls the box "always sound". Under A's model, the box, one-corner and SLOW-only checks
are all unsound for κ > 0 (`ConstraintsKappa`). The JSON field is stale (probe Bj5).

K15. **RigContract.** A's §0.3 item 7, §3 last row and §8 row 48 say RigContract "does not
compile". It was fixed in 807448a and Bsa confirmed it. Still stale in A's doc.

K16. **The headline theorem.** A's §0.1 has `gcd_hw_circuit_safe''` with H_WALK. The current
theorems are `gcd_hw_circuit_safe3` (H_WALK proved), `gcd_rig_first` / `gcd_rig_first_env` and
`gcd_hw_live_final` (§0.1 here).

---

## 4. B-side findings (for the lead; no edits made)

1. **`cell_constraints.json` `conventions.corner_rule` is still stale** ("box … always sound").
   The `H_NO_RETURN` entry is now current (it cites `gcd_first_wave`).
2. **No joint witness exists for `gcd_rig_first_env`.** It is the only B theorem on a capstone
   chain. It is the cheapest Lean item here.
3. **No B lemma reaches OpsGen's `LutFb`/`LutSI`.** Until one does, B's cell theorems support the
   capstone only through prose.
