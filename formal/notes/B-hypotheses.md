# B-hypotheses: the ledger of physical hypotheses under shard B's part of the gcd_hw argument

Probe Bhyp (shard B), 2026-10-27, about 11:40 UTC. Read-only. No Lean was written or run;
no route, board or toolchain was used.

Sources:
- JOURNAL-B.md: verdict block, findings, and the session starting 10:48 (progress 10:54-11:23).
- The B notes changed since 10:48: B-celem-strict(2), B-win-fifo(-causal), B-lib-gap(-mux,
  -delay), B-fork-data, B-rig-idx, B-rig-contract (correction block), B-rig-token, B-gcd-arb,
  B-arb-kappa, B-constraints-kappa, B-constraints-update, B-self-audit, B-port-core2.
- Older B notes where a row still rests on them: B-gcd-routes, B-gcd-cells, B-reset-gcd(-wave),
  B-obligations.
- `formal/out/cell_constraints.json`: 128 entries and 8 `hypotheses_not_inequalities`.
- For context: shard A's `formal/out/gcd_hw_hypotheses.md` (the 10:54 file, "rewritten at about
  11:00"), C-10h and C-10k.

**Name check.** Every Lean name below as `File:line name` was grepped as a
`theorem|def|structure` declaration in that file in the working tree at about 11:35.
- Hypothesis names (H_*) were grepped as text in the files listed. Where a name exists only in
  prose (a note or a docstring), the row says **prose only**.
- Three files are in the tree but no probe has reported them yet: `OnGcdArbA0.lean` (probe Bar),
  `LibGapMuxN.lean` (Bmn) and `NecessityReset.lean` (Bsx), plus `LibGapLatch.lean`. Their
  contents are marked **in progress, not claimed**: I did not check them and no journal entry
  claims them.

Grades follow shard A's doc:
- **A**: proved, true by construction, or measured.
- **B**: credible and physically motivated, untested on this silicon.
- **C**: doubtful, contradicted, or failing on some route or corner.

Status words:
- **proved-on-routes**: a Lean theorem instantiated on routed gcd_hw numbers;
- **rule-checked**: a tcheck/cells-verify rule passes on the gcd_hw routes;
- **unchecked**: nothing evaluates it on gcd_hw;
- **failing**: some route or corner gives a negative margin.

Routes. Two sets are in play and are not interchangeable:
- C-10e/10h **tcheck routes**: seeds d, 2, 3, 4, no `--freq`. Bag and Bar use these.
- Br's **`--freq 100` routes**: seeds 1-4 (B-gcd-routes).

Both were built with nextpnr 9c732bc6303458df. Neither is the board bitstream
`gcd_hw_03e82630.bit`. All the route artefacts except Bar's rebuild are gone from this
container (B-gcd-arb "Blocked").

gcd_hw instance counts (B-gcd-cells, B-gcd-routes):

| cell | instances |
|---|---|
| C-elements per route | 363: 185 bd_c2n, 153 bd_c2, 14 bd_c4, 10 bd_c3, 1 bd_c2n_set (the rig's uenv1) |
| bd_latch | 184 |
| bd_delay | 287 |
| bd_delay_gated | 29 |
| bd_steer | 38 |
| bd_mux | 21 |
| bdc_muxn3 | 1 |
| bd_arbiter | 9 (7 amerge2 + 2 amerge3 stages) |
| bd_fork | 52 |
| bd_join | 38 |
| fused compute units | 20 |
| bd_link | 46 |
| bd_pipe | 63 |

---

## 1. The ledger

There is one row per physical assumption. Every name used for that assumption is listed in the
row.

### 1a. LUT and primitive fidelity

**BH1. The LUT computes its INIT function on its real pin map.**
- *Names:* H_LUT_FN (implicit), M4/M5 in A's doc.
- *Lean:* CElemFn, Latch, LinkHandshake, ArbKleene, Lib1/Lib2 (INIT = header equation);
  OnNetlist (the INITs equal those read back from 4 link/arb bitstreams).
- *gcd_hw use:* every control LUT.
- *Grade:* A for the cells and the 4 read-back bitstreams. For gcd_hw itself, M5 is B (C's
  fasm2lean covers only link and arbiter).
- *Status:* proved (cells). gcd_hw bits: research's fasm2net has 11619/11619 LUT functions equal
  (audit row 23).
- *Test:* extend fasm2lean to gcd_hw (C-11c).

**BH2. Kleene pass-transistor mux.** A single 2:1 mux with a mid-rail select passes equal legs.
More generally, each mux is Kleene-sound at every instant.
- *Names:* H_KLEENE_LUT; A's `H_mux_kleene`; B's H_MUX_KLEENE (per-pin, timed form); JSON
  `H_LUT_FIFO / H_PIN_FIFO / H_TREE_FIFO` (catalogue C4), whose "statement" is this hypothesis.
- *Lean:* `Core/LutTree.lean:279 H_mux_kleene` (A); `Cells/MuxTree.lean:101 muxTree_eq_lutK`,
  `:290 evalK_order_indep` (every pin order gives the same value); CElemStrict's H_MUX_KLEENE
  (text in `CElemStrict.lean`).
- *gcd_hw use:*
  - every ternary/Kleene result: the ResetGcd ternary certificates, TernaryOnBits, Fd's "held
    controlling 0";
  - the strict feedback race (BH6);
  - the `_K` forms of LibGapSteer/LibGapMux.
- *Grade:* B. Credible for clean or late selects; doubtful for a mid-rail select while the legs
  move (NMOS-only tree).
- *Status:* unchecked on silicon. Note: under closure semantics single-X glitch freedom holds for
  every INIT (Lib2), so all per-cell glitch content sits in this one hypothesis.
- *Test:* board glitch counter on a LUT with equal legs and a slow select ramp, or a LUT ring
  counting extra edges per revolution.

**BH3. One input edge gives one output edge: no revert inside the uncertainty zone.**
This is FIFO / no overtaking.
- *Names:*
  - H_NO_REVERT (`NoRevertI`);
  - B's FIFO family, all one form (`PipeTimed.Ret`): H_LUT_FIFO, H_WIRE_FIFO, H_LINE_FIFO,
    H_PIN_FIFO, H_TREE_FIFO, H_REQ_LINE/H_ACK_LINE;
  - A's `NoOvertake` and S3 ("H_LUT_FIFO / NoOvertake");
  - catalogue C4, P5.
- *Lean:*
  - `WinFifo.lean:151 win_glitch_not_fifo`: no spacing makes `Win` FIFO once `hi ≥ lo+2`;
  - `:395 win_fifo_of_no_revert`, `:405 no_revert_of_ret`: under H_SPREAD_PULSE, FIFO ⟺ `Win`
    + H_NO_REVERT;
  - `spread_of_loop`;
  - `WinFifoCausal.lean:438 stage_fifo`, `:810 pipe_fifo`: H_LUT_FIFO derived for one stage and
    the 2-stage pipe from `Win` + H_NO_REVERT;
  - `:1127 no_revert_needed`: it cannot be dropped;
  - `PipeTimed.lean:264 Ctl` (the consumer).
- *gcd_hw use:*
  - B's timed cell theorems: PipeTimed(N), OpsTimed* (SteerGates), OpsTimedMux, ContractsTruncCel
    (the contract route, A's §7);
  - `RigToken.set_move` / `rig_token` (uenv0/uenv1 and their wires);
  - not the capstone's H_CELLS, which is SI (`LutSI`/`LutFb`).
- *Grade:* B. It is an inertial-type property: a single-input CMOS chain given one monotone edge
  makes one edge. It is not derivable from `Win` (A, and Bw).
- *Status:*
  - The FIFO hypotheses are reduced to H_NO_REVERT for the two pipe LUTs and the steer's H_WQ.
  - The pipe's lines and PipeTimedN are not done.
  - H_TREE_FIFO is not reducible: the select excitation is glitchy (`sel_runt`, `ce_not_fifo`).
  - The power-up prefix is excluded, except where reset forces the excitation (`witness1`).
  - Unchecked on silicon.
- *Test:*
  - a LUT ring or chain with transport-per-level GLS (`GLS_MODEL=fid`): count output edges per
    input edge;
  - board: a LUT ring never shows an extra edge per revolution.

**BH4. LUT6_2 shared read.** O5 and O6 read each shared physical pin at one instant.
- *Names:* H_LUT62_SHARED_READ; A's S2; `SiteSync`.
- *Lean:* `TernaryOnBits2.lean:325 SiteSync`; ArbOverlapRace `Decomp`; `Latch.pair_o5_kleene`.
- *gcd_hw use:* bd_steer (38), the bd_latch pairs, the arbiter's ugrant/ustate, bd_datamux.
- *Grade:* B.
- *Status:* unchecked. CElemStrict2's `pair_o5_clean_iff` / `pair_o6_clean_iff` do not need it for
  the latch setup race: each output is exact on its own pins.
- *Test:* CARRY4 TDC on O5 vs O6 skew from one pin.

**BH5. Atomic LUT read, or select X width.** Either all pins of a LUT are read at one instant
(atomic), or each moving select is X for a window `wa ≥ 1`.
- *Names:* H_ATOMIC_LUT (A: `Events*.Beh.hc`); the zero-width-select assumption under every
  B `≤` race theorem; `wa`.
- *Lean:*
  - `CElemStrict.lean:288 env_latency_iff` (the exact condition with `wa`);
  - `:297 env_latency_strict` (`wa = 1`, so `<`); `env_latency_atomic` (`wa = 0`, so `≤`);
  - `:388 boundary_x`, `binary_glitch` (the counter-traces);
  - A's `Events2Strict.lean:374 safe_strict` agrees (A-contradictions X2).
- *gcd_hw use:* every own-feedback race (BH6, BH7, BH13, the reset width BH20).
- *Grade:* B. One tick is the grid minimum, not a measured slew; the physical margin is the
  departing select's X width.
- *Status:*
  - Resolved in the model in favour of the strict form.
  - The JSON carries `strict` on 59 entries and `strict_pending` on 20.
  - No route margin on gcd_hw is near 1 ps (kernel Rc worst is +55 ps guarded, Br), so no
    verdict flips.
- *Test:* none needed for gcd_hw's verdicts. To measure the slew, use a TDC on a LUT select ramp.

### 1b. C-element and latch races (own feedback)

**BH6. The C-element's feedback arrives first.**
- *Statement:* the C-element's own feedback reaches its select before any response the output
  provokes arrives back at a non-feedback pin. Strictly: `dlmax + dwmax + wa ≤ dlmin + E`. Per
  pin: `w_hi + SP[fb].hi ≤ E_τ + min(SP[req].lo, SP[ack].lo)`.
- *Names:*
  - B: H_ENV_LATENCY (C2), H_FB_FAST, H_SEL_ORDER / H_SELORD (C3, per pin), "C-element fork
    wait" (`E ≥ dwmax + dlmax − dlmin`, audit row 84);
  - C: H_FB_FIRST (`FbFirst`), RT_FB, tcheck rule R/Rc;
  - JSON: `bd_c{2,2n,3,4}.env_latency`, `.sel_order`, `bd_ctree.node_fork`, the C-element parts
    of the `bd_mux`/`bd_merge`/`bdc_muxn`/arbiter entries.
- *Lean:*
  - `CElemTiming.lean:399 c2_four_phase`;
  - `FifoFidelity.lean:173 sel_phase`;
  - `ConstraintsSel.lean:272 sel_order_of_lat_gen`;
  - PipePerPin `pipe_ctl`;
  - the CElemStrict family (BH5): `clean_iff :219`; `CElemStrict2.lean:323 c2n_all`; `c3_all`,
    `c4_all`, `c2set_all` (every cycle of every C-element INIT);
  - C: `Net/OpsGen.lean:95 FbFirst`, `Timing/FbFirstRt.lean:136 fbFirst_of_resp` (under
    H_RESP_ONLY), `OpsGen.lean:216 fb_stale_breaks`.
- *gcd_hw use:* all 363 C-elements: link controllers, C-trees of forks and joins, the mux joins
  `uj0/uj1`, the arbiter's `ua_k`, and the rig's uenv0/uenv1.
- *Grade:*
  - kernel: B (rule-checked with margin);
  - rig uenv1: **C**.
- *Status:*
  - Kernel: Rc passes on all kernel C-elements, 4 tcheck routes, fast/slow/fastG/slowG (C-10h,
    C-10k).
  - Br, per pin with site pins, on the `--freq 100` routes: 0 negative at any one-corner reading;
    box reading 5-10 negative per seed (worst −585 ps).
  - **uenv1: failing.** banded Rc on tcheck seed 2 is −117 (fastG) / −221 (slowG) ps; seed 4 is
    −86 / −243 ps. Unguarded it is +44/+162 and +94/+161 (C-10h:168-170, which includes the
    LUT→xMUX hop).
  - `RigToken.lean:765 stale_fb_extra_start` shows what that failure allows: 3 start offers
    against 1 result.
  - JOURNAL-B's findings block quotes −114/−219 and −81/−201. Those numbers are stale; C-10h is
    the source.
- *Test:*
  - GLS of `gcd_rig` on seeds 2 and 4 at the fast corner: exactly one `start_req` rise between
    consecutive `res_req` rises;
  - T2 (own feedback vs neighbour response, board + GLS);
  - fix candidate: LOCK_PINS uenv1's feedback to A5/A6.

**BH7. C-element pulse width, C-tree depth latency, atomic tree.**
- *Statement:* an enabling combination is held for `Dmax` (+1, strict). Each tree node's latency
  fits inside the root's environment latency (C7). The tree acts as one C-element.
- *Names:* H_PULSE (C1); `bd_c*.pulse_width`; C7 LatOK; C6; C's H_CTREE_ATOMIC.
- *Lean:* `CTreeTimed.lean:1174 tree_four_phase`; `CTree.lean:802 reachable_eq_flat` (an atomic
  cell model only); `c3_all` / `c4_all` (node races, strict).
- *gcd_hw use:* 3 bd_ctree; the fork and join C-trees (52 + 38; N ≥ 4 for the large forks).
- *Grade:* B.
- *Status:*
  - pulse width: implied inside a four-phase run;
  - C7: **unchecked** on routes (no tcheck row);
  - H_CTREE_ATOMIC: proved only as reachable-set equality.
- *Test:* a tcheck row for tree depth (A's doc, "C7; not done").

**BH8. Latch capture: setup data, setup pulse, hold, loop bound.**
- *Statement:*
  - setup data: `Td + dhi + fhi ≤ Tr + rlo + wlo + elo` (+1 strict);
  - setup pulse: `ehi + fhi ≤ wlo + elo` (+1);
  - hold: `ehi ≤ alo + dlo`;
  - loop bound: `1 ≤ loop ≤ L`.
- *Names:*
  - B: H_SETUP (L1), H_PW (L2), H_HOLD / H_RULE_H (L3), H_LOOP_MIN/MAX (L4);
  - B's fork forms: H_FORK_DATA, H_FORK_DATA_W, H_FORK_PULSE, H_FORK_HOLD (old A row C14);
  - C: H_LATCH_OPEN / H_LATCH_HOLD;
  - JSON: `bd_latch[*].setup_data/_pulse/hold`, `bd_latch.loop_bound`, `bd_fork.branch_data`,
    `_edge`, `bd_pipe.boundary_I/_H`.
- *Lean:*
  - `Bundling.lean:601 capture`;
  - `OnNetlistTimed2.lean:82 latch_rule_h_net`;
  - `ForkData.lean:140 fork_capture`;
  - `:235 fork_data_needed` (H_FORK_DATA_W exact: 1 ps violation gives a stale latch);
  - `edge_form_not_needed` (C-8f's "data before req" is sufficient, not needed);
  - `CElemStrict.latch_facts`; `CElemStrict2` `pair_o5_clean_iff` / `pair_o6_clean_iff`
    (strict, per output).
- *gcd_hw use:* 184 bd_latch. Census of fork branches: 53 end at link/pipe latches, 59 at joins,
  12 at nested forks, 6 at bd_snk, 9 are control-only.
- *Grade:* B.
- *Status:*
  - rule-checked per tcheck route: I 300/300, H 630/632 (2 band-only), W min +346 ps fastG.
  - Rule I lacks the latch's I2 feedback-pin arc (covered by the guard).
  - Br, corrected with site pins: rule I ≥ +1288 ps guarded; rule H +40 ps guarded (thinnest).
  - Setup-pulse has no project rule; tcheck W covers it.
- *Test:* the tcheck I/H/W rows with the I2 arc added (rule I').

### 1c. Select and bundling at the steer, mux and muxn

**BH9. Steer select at the pins.**
- *Statement:* the steer's `s` pin is settled before the request is read, and held until the
  request falls as read, per pin and per output: `S0 + Shi ≤ R + Rlo` and `F + Rhi ≤ S1 + Slo`.
- *Names:* C: H_SEL_PIN; B: H_SETUP_PIN / H_HOLD_PIN, H_BUNDLED_S_PIN (X3), H_STEER_SEL; JSON
  `bd_steer.bundled_s_setup` / `_hold` (exact since Bj).
- *Lean:*
  - `LibGapSteer.lean:188 steer_box_exact` (iff over the box);
  - `steer_pin_exact`, `setup_needed :139`, `:154 hold_needed`;
  - `spurious_token`: setup short by 100 ps sends a token down the wrong loop exit;
  - `steer_pin_ok_K`.
- *gcd_hw use:* 38 bd_steer, on every loop exit.
- *Grade:* B.
- *Status:*
  - setup: rule E, 465/472 agree (band-only disagreements). Rule E omits site pins: in the box it
    is optimistic by up to `SP[s].hi − SP[req].lo` plus the arc difference;
  - **hold: unchecked**, no rule.
- *Test:* rule E' with site pins from FASM; a hold rule (no tcheck row yet).

**BH10. Mux join select and the ctl_req fork.**
- *Statement:* at each mux join, `s` is settled before `ctl_req` is read and held past its fall,
  per pin (the request and feedback pins drop out). The `ctl_req` fork to uj0/uj1 is weakly
  isochronic.
- *Names:*
  - C: H_SEL_PIN (mux part), Mux `cj0`/`cj1`, rule K;
  - B: X3, X4 (`mux_needs_iso_cr`);
  - JSON: `bd_mux.bundled_s_setup/_hold` (exact), `bd_mux.isochronic_forks`, `bdc_muxn.s_setup`,
    `s_hold`, `iso_ctl`.
- *Lean:*
  - `LibGapMux.lean:393 join_box_exact`, `join_pin_exact`, `dev_iff`, `mux_joins`;
  - `wrong_branch_latched`;
  - muxn: `LibGapMuxN.lean:321 join_exact_fixed` (in progress, not claimed; adds **H_YOSYS_MAP**,
    the inferred decode LUT3 INITs).
- *gcd_hw use:* 21 bd_mux, 1 bdc_muxn3.
- *Grade:* select B; ctl_req fork **C pending**.
- *Status:*
  - setup: rule E (no site pins);
  - hold: unchecked;
  - **ctl_req fork: failing.** Rule K FAILs 16-26/42 per route at every corner (C-10l, WIP).
    Whether this is a real isochrony violation or over-conservatism is undecided.
- *Test:* GLS monitor at `umux*.uj0/uj1`: the ctl_req pulse has ended before `s` changes; finish
  C-10l's verdict.

**BH11. Return to zero at the mux and arbiter ack C-elements.**
- *Statement:* `z_ack`'s low pulse at the ack C-element outlasts that C-element's own fall.
- *Names:* B: H_RTZ / H_MUX_RTZ (X1), A3 "pulse"; C: Mux/AMerge `xa`/`ya`, rules X, Xi, Xc, Xic,
  Xm; JSON `bd_mux.uxa_rtz(_env)`, `uya_rtz(_env)`, `bdc_muxn.rtz`.
- *Lean:* `MuxRtzTimed.lean:113 rtz_safe`, `mux_rtz_env_safe`.
- *gcd_hw use:* 63 ack C-elements per route.
- *Grade:* B.
- *Status:* rule-checked. X has 0 fails unguarded; the band fails only on steer-OR'ed muxes.
  Xc/Xm have 1-2 band fails (`umux11`, −350 slowG) (C-10k, C-10l WIP).
- *Test:* GLS monitor: x_ack and y_ack low at every z_ack↑.

**BH12. Control_merge index bundling.** The amerge index (`won = g2 | in1_ack`) is settled
before the consumer closes.
- *Names:*
  - H_AMERGE_IDX (= BidxA ∧ BidxB ∧ IdxAckFork); C's H_BUNDLED_IDX; old A row C11;
  - JSON `bdc_amerge.idx_bundle`, `bundled_idx_*`, `idx_ack_fork`, `bdc_amerge3.bundled_idx0_grant`.
- *Lean:* `ForkData.lean:360 amerge_idx_sufficient`, `amerge_idx_necessary`; AMergeTimed (Cm2).
- *gcd_hw use:* 8 control_merges. All have width 0, so only the index matters. Every index goes
  through the `_f` fork into Muller links.
- *Grade:* B.
- *Status:*
  - At gcd_hw's consumers the exact form is BH8's H_FORK_DATA_W with `Td` = index settle time;
    Cm2's legs are sufficient there.
  - Rule Z passes on all 9 stages (C-10k); rule I covers link consumers.
  - `idx_ack_fork`: no shipped rule.
- *Test:* tcheck Z / I rows.

### 1d. Matched delay lines

**BH13. Gated delay flush.**
- *Statement:* the gate's low phase flushes each stage before the next token, per pin:
  - stage 1: `F + r0.hi + r1.hi + (p 1).hi ≤ T + (q 1).lo`;
  - stage i: `F + (q(i−1)).hi + (p i).hi ≤ T + (q i).lo`.
- *Names:*
  - B: H_GFLUSH i (`GF i`), D2, side conditions H_BAL_HI, H_LO_ORDER, H_START, H_SHORT;
  - C: H_FF_DRAINED, rule Fd;
  - JSON `bd_delay_gated.gate` (exact, with `exact_under`).
- *Lean:*
  - `GcdCells.lean:151 no_early`;
  - `LibGapDelay.lean:282 flush_of_gflush` (sufficient for any maps);
  - `:490 box_exact_flushed`, `box_exact_no_early` (exact under the side conditions);
  - `:571 rescue_flushed`: without H_LO_ORDER per-stage H_GFLUSH is not necessary;
  - `real_bad`: a 1 ps shortfall gives an early request 620 ps ahead.
- *gcd_hw use:* 29 bd_delay_gated, on the fused compute units' matched delays.
- *Grade:* B unguarded; **C** under the band.
- *Status:*
  - Fd passes 29/29 per route unguarded.
  - Band fails: `ucontrol_merge12` (seed 3 −343, seed 4 −522 slowG) and `ushrsi3` (seed 4 −160).
  - Rule F lacks the in-flight term `(p i).hi − (q i).lo`.
  - H_LO_ORDER is unchecked on every route.
- *Test:* T1 (decides the band); a per-route H_LO_ORDER check.

**BH14. FASTFALL and FASTRISE line flush in links.**
- *Names:* H_FLUSH (D2 uniform and per stage), H_ACK_FLUSH (P3), H_RST_LINES (P4); JSON
  `bd_delay[FASTFALL].flush_*`, `[FASTRISE].ack_flush`, `bd_pipe.rst_lines`.
- *Lean:* `Bundling.slow_not_early`; PipeTimed / PipeTimedN `H_ACK_FLUSH`, `H_RST_LINES`;
  ConstraintsFastFall.
- *gcd_hw use:* 287 bd_delay in links and pipes.
- *Grade:* B.
- *Status:* rule F (missing term) passes on Br's routes (min +463). FASTRISE: **unchecked**.
  `strict_pending`.
- *Test:* rule F with the in-flight term; a FASTRISE dual rule.

### 1e. Arbiter (digital race only)

**BH15. A0 fork: A0's fall reaches ua_k before A0 → ustate → q → ugrant → g_k does.**
- *Names:* H_A0_FORK (A1), rule J / J' / Jx; JSON `bd_arbiter.a0_fork_client1/2`.
- *Lean:*
  - `ArbA0Fork.lean:258 no_early_ack_iff`, `box_safe_iff`;
  - `ArbCornersPin.ruleJ_seed`;
  - κ model, on link_arb: `OnNetlistArbKappa.lean:80 fork_le_of_endpoint`, `:174 counter_core`,
    `verdict_s1c2_cons_κE`;
  - gcd_hw: `OnGcdArbA0.lean gcd_corner_all`, `fork1_box_iff` (in progress, not claimed).
- *gcd_hw use:* 9 bd_arbiter × 2 clients.
- *Grade:* B at one consistent corner; C in the independent box.
- *Status:*
  - rule-checked: Jx passes 72/72 clients within each column; guarded worst −9 ps (seed 4
    merge12.uarb2 client 2, fastG).
  - Rule J lacks site pins, and is 8 ps optimistic with q on A5.
  - On link_arb under A's κ model: safe on 8/8 at κ = 1/11. At κE = 0.1988, 7/8 in the
    side-pessimistic reading (s1 c2 unsafe from κ* = 197/1103 ≈ 0.1786).
  - In progress (Bar): seed d corner rows all safe; 3 of 9 box rows have the client-1 fork
    negative.
- *Test:* T5 (handover on one die, q on A3 vs A5); a κ measurement on the A0-branch vs
  ustate/ugrant tails (is κ < 0.178?).

**BH16. RT1/RT1b grant exclusion across a handover.**
- *Names:* RT1 (A2), RT1b (A4); H_R_SHARED, H_Q_PREFIX, H_FLAT_O6 (Bag's modelling names); JSON
  `bd_arbiter.rt1`, `rt1b`; C's H_ARB_EXCL (part).
- *Lean:* `OnGcdArb.lean:782 gcd_rt1_all`, `:790 gcd_rt1b_all`, `rt1_iff`, `:281 box_rt1`,
  `allRows_sat`; `ArbHeldTimed.rt1_exclusion`, `ArbHeldTimed2.rt1_exclusion2`.
- *gcd_hw use:* 9 bd_arbiter.
- *Grade:* A at one corner (proved on routed numbers, server-free); C in the box.
- *Status:*
  - **proved-on-routes**: 36 arbiters × 4 tcheck routes × FMIN/FMAX/SMIN/SMAX, worst +33 ps
    (seed 3 merge12.uarb1 RT1b FMIN).
  - The data is C's RuntAckInst rows, extracted by an untrusted front end.
  - Box: negative on 64/72 rows server-free. It needs server + A0 branch + ustate arc + q prefix
    ≥ 711 ps (exact).
- *Test:* the corner model (T1); a lower bound on the server path.

**BH17. RT2/RT2b ack exclusion, and the server minimum.**
- *Names:* RT2 (A3), RT2b; H_SERVER_MIN (A5); `Scn.H_SETTLED`; H_REQ_STEADY; JSON
  `bd_arbiter.rt2_*`, `rt2b_*`, `server_min`, `bdc_amerge3.rt2_cascade_*`.
- *Lean:* `ArbHeldTimed.rt2_exclusion_arcs`; `OnGcdArbA0.rt2_box_iff` (in progress).
- *gcd_hw use:* 9 arbiters, plus the amerge3 cascade.
- *Grade:* B.
- *Status:* unchecked on gcd_hw until Bar is claimed (Bar: corner rows `allOk` 36/36 for seed d,
  for every server). H_SERVER_MIN is an environment hypothesis.
- *Test:* T5.

**BH18. No free contest.**
- *Statement:* the request-edge separation, the break-before-make of O5/O6, and metastability are
  never exercised.
- *Names:* H_REQ_SEP, H_GRANT_SKEW, H_BBM1/2 (R2, R4); the metastability tier R3; H_EXCL_REQ;
  H_Q_BEFORE_REREQ (A6).
- *Lean:* `ArbBinary.lean:435 exclusion_transport`, `arbiter_alternates`; `CElemInvolution.c2_eternal`,
  `ArbInvolution.arb_grants_eternal` (why no deadline exists).
- *gcd_hw use:* 9 arbiters.
- *Grade:* A within the model: C's `gcd_hw_arbiters_uncontended'` (`CapstoneCut.lean:547`) shows
  no free contest, so none of these is needed for the safety theorem. Physically B: it rests on
  the model's SI discretisation (A's M6 / D2 H_SEP).
- *Status:* discharged by proof in the model.
- *Test:* board: count contested grants; a GLS monitor for both requests high with no grant held.

### 1f. Delay and corner model

**BH19. One corner, the band, and κ.**
- *Statement:* every delay of a margin sits at one die corner, with per-arc scatter `1 ± κ`
  around the corner's interpolated nominal. The independent box is the pessimistic alternative.
- *Names:*
  - H_ONE_CORNER, H_DIE_SLOW/FAST, H_INDEP (box);
  - A's H_SHARED_CORNER, H_SCATTER κ, H_ENDPOINTS, H_AFFINE (D11, D12, D15);
  - B's H_DISJ, H_DIV;
  - H_SAME_TRAVERSAL (**prose only**, ConstraintsKappa note);
  - H_WIRE_RATIO (D16, withdrawn for A-model checks).
- *Lean:*
  - `ConstraintsKappa.lean:310 allOK_iff_gen` (exact under H_DISJ + H_DIV), `:329 allOK_cancel`;
  - `:450 box_unsound_with_kappa`, `:458 one_corner_unsound_with_kappa`, `slow_only_unsound`,
    `endpointNat_not_sufficient`;
  - `Core/Delay/Corner.lean:342 guard_kappa_iff` (band 0.772/1.155 ⟺ κ = 383/1927);
  - OnNetlistArbKappa.
  - These files import CornerNat, so they need Mathlib. Bk1 and Bk2 checked them only through
    core mirrors with 4 sorried CornerNat lemmas; neither is lake-checked yet.
- *gcd_hw use:* every numeric margin of every row above.
- *Grade:* B, contested. κ is unmeasured on the current toolchain (A withdrew 0.311).
- *Status:*
  - Every unguarded tcheck row passes except rule K.
  - Every residual C is band-only: Rc uenv1, Fd cm12/ushrsi3, Xc umux11, Jx merge12, A shrsi1.
  - **The JSON's corner rule is stale.** It still says "box … always sound", which is false under
    A's model for κ > 0 (Bk2's `kappa_check.patch` is not applied).
- *Test:* T1 (on-die differential two-path), which gives κ and decides every band-only C.

**BH20. Site pins and the pin permutation.**
- *Statement:* each physical LUT input adds its own site-pin delay (up to about 0.5 ns, pin 1
  slowest). This is not in nextpnr's SDF.
- *Names:* A's S6; H_PIN_READ (B's per-pin read-map model); "flat 25 ps site pip".
- *Lean:* LibGapSteer/LibGapMux/LibGapDelay `Rd` maps; PinAssign; ArbCornersPin.
- *gcd_hw use:* every row. Feedback is on pin 1 for 12/36 fixtures (Bp), and for uenv1 on every
  seed.
- *Grade:* A as a fact (measured from the bits). The rules that ignore it (J, E, I, H) are
  optimistic or conservative per row.
- *Status:* tcheck uses prjxray site pins. The shipped rules J and E do not.
- *Test:* a site-pin table in arb_fork.py/skew.py with pins read from FASM (about 0.5 d), or
  LOCK_PINS.

**BH21. Rise = fall within a corner column.**
- *Names:* H_RF_ASYM (A's D7/S7).
- *Lean:* named in MuxRtzTimed, ArbHandover, ArbHeldTimed, ArbCorners (text).
- *gcd_hw use:* all.
- *Grade:* B.
- *Status:* unmeasured.
- *Test:* CARRY4 TDC.

### 1g. Reset and the first wave (gNet, the elaborated RTL; not linked to the Ops model)

**BH22. The reset source and its hold.**
- *Statement:* rst is 1 from power-up for at least `23(D+W+1) + W` GMW steps. It has one clean
  falling edge, then stays 0 through the first wave.
- *Names:* H_RST_HELD, H_HOLD_LONG, H_RST_CLEAN, H_RST_LOW, H_RST_HIGH; JSON `design.rst_hold`
  (strict) and `design.rst_flush`.
- *Lean:*
  - `ResetGcd.lean:198 gcd_reset_binary`;
  - `ResetGcdWave.lean:572 gcd_boot`, `:726 gcd_clean_release`, `:586 rst_reads_low`;
  - `SelfAuditB2.wave_witness`.
- *gcd_hw use:* all 423 rst pins of the kernel and the rig.
- *Grade:* B. In `gcd_hw.v` rst is `~por_done | rst_sr[15]`, held for 16 hk cycles (≈ 121 ns),
  against a 23-step bound.
- *Status:*
  - The hold margin is unchecked but huge.
  - H_RST_CLEAN can fail only if `por_done` rises on the edge where `rst_sr[15]` falls.
- *Test:* GLS of the housekeeping logic; check that `por_done` never rises on that edge.

**BH23. Per-cell reset width.**
- *Statement:* rst at each pin is held at least `Dhi + wa` (strict `Dhi < P`). The race is real
  where the cell's data pins sit at a hold vector at release. For gcd_hw's 185 bd_c2n link
  controllers (req = ack = 0) they do.
- *Names:* H_RST_PULSE, H_RST_LONG (C5), H_UENV1_HOLD (the rig instance), H_IN_HELD; JSON
  `bd_c*.reset_width`, `bd_mux/bd_merge.reset_first`.
- *Lean:*
  - `CElemStrict2.lean:510 reset_width_iff`, `:519 reset_width_strict`, `rst_boundary_x`;
  - `CElemTiming.c2_reset`;
  - `NecessityReset.lean ResetOK` (in progress, not claimed).
- *gcd_hw use:* every rst-carrying C-element and link controller.
- *Grade:* B (exact in the model).
- *Status:* unchecked per pin. The margin is about 16 hk cycles against one LUT loop.
- *Test:* routed SDF: max rst-pin loop bound vs the reset width.

**BH24. Release skew and lost events.**
- *Statement:* nothing is still held in reset when the loop starts. The physical form: max rst-net
  wire delay < 34 GMW steps (one step ≤ the minimum LUT+wire delay) along the 34-LUT path
  `ulink_n1__1 → ucmpi0 → join → steer`.
- *Names:*
  - H_NO_RETURN, H_RST_SKEW, H_RST_BEFORE_LOOP (`W < 34`);
  - `Bounded D W` = H_GATE_BOUND + H_WIRE_BOUND; H_GMW_GATE; H_SETTLED;
  - H_STEER_HOLD (the segment end, not physical);
  - JSON `design.rst_release_skew`, and H_NO_RETURN under `hypotheses_not_inequalities`.
- *Lean:* `ResetGcd.lean:341 gcd_release_quiet`; `ResetGcdWave.lean:447 gcd_first_wave`,
  `:694 gcd_loop_late`.
- *gcd_hw use:* the whole control network.
- *Grade:* B.
- *Status:*
  - H_NO_RETURN is **proved for the reset-release window** (`gcd_first_wave`, any rst waveform).
    The residual is `W < 34`, which is unchecked (no routed number).
  - **The JSON's H_NO_RETURN entry is stale.** It says "argued, not proved" and cites only
    `gcd_release_quiet`.
  - Bsa caveat: for D+W > 0, H_STEER_HOLD past `F + 34` is an assumption.
- *Test:* routed SDF: max over the rst pins (slow) vs 34 fast-min LUT+wire delays on that path,
  guardbanded.

**BH25. No read before first write.**
- *Statement:* data latches are not reset. Every reader of an unreset latch is a guard that is
  definite at the reset value, or the next latch closed.
- *Names:* NRBW (JSON `hypotheses_not_inequalities`); H_GUARD_MAP (not needed, B-reset-gcd).
- *Lean:* Rst2 / ResetGcd ternary certificates (`gcd_reset_ternary`).
- *gcd_hw use:* 184 latches.
- *Grade:* A for (a) GUARD (decided on the imported network); B for (b) write-before-read
  (the latch rows).
- *Status:* decided (a); rule-checked via I (b).
- *Test:* none extra.

### 1h. The rig (outside the Ops network; it realises H_START_ONCE and the measurement)

**BH26. The env ring gives one start per result.**
- *Statement:*
  - uenv1 is held in reset for its loop bound;
  - the kernel does not ack before it sees start;
  - rst does not come back;
  - each cell is a FIFO LUT; the wires are FIFO;
  - uenv1's feedback wins (BH6).
  - Then: the ring releases with `start.req = 1` in any rst order, and
    `#start ≤ #results + 1` for every lap.
- *Names:*
  - H_UENV1_HOLD (exact), H_ACK_QUIET, H_RST1_ONE_FALL, H_UENV0_FORCE, H_RES_QUIET;
  - H_FB_FIRST (uenv1), H_LUT_FIFO, H_WIRE_FIFO;
  - H_ENV_REFINES_SRC (**prose only**, B-rig-token: uenv1 + fork c3 refine C's `Src`);
  - C: H_START_ONCE; old A row C16 ("uenv1 release order").
- *Lean:*
  - `RigToken.lean:409 uenv1_release`, `uenv0_release`, `ring_alternation`, `:236 set_move`;
  - `:355 start_per_result`, `:381 start_once_prefix`, `:463 rig_token`, `rig_token_nonvacuous`;
  - `:663 short_rst_many_starts` (H_UENV1_HOLD exact), `no_rst_no_token`;
  - `:765 stale_fb_extra_start`.
- *gcd_hw use:* `urig.uenv0`, `urig.uenv1`, `ufork`, and `in_ack`'s bd_c3.
- *Grade:* B. **C** for its H_FB_FIRST leg.
- *Status:*
  - The env side is proved.
  - H_FB_FIRST at uenv1 fails under the band on seeds 2 and 4 (BH6).
  - Missing bridges to C's global H_START_ONCE: (1) a T-bounded capstone; (2) laps ≥ 2; (3) the
    time origin (`start.req = 1` at release vs `Src.iz`); (4) H_ENV_REFINES_SRC. None is
    mechanised.
  - H_START_ONCE as stated is false over a whole rig run.
- *Test:* GLS: one `start_req` rise between consecutive `res_req` rises, seeds 2 and 4, fast
  corner.

**BH27. Rig operand setup.**
- *Statement:* the vector reaches the frontier latch `su` before F opens:
  `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`. The reset outlasts F's loop. The token is needed only
  until F's first fire.
- *Names:* H_IDX_SETUP, H_RST_LONG (H_RST_LONG_EN), H_HK_PERIOD, H_PATH_RST, H_PATH_IDX, H_EN,
  H_RST_ONE_FALL, H_TOKEN_FIRST (replaces H_TOKEN_STATIC); JSON `gcd_rig.idx_setup` (exact),
  `gcd_rig.token_static`.
- *Lean:*
  - `RigIdx.lean:145 idx_setup_suff`, `:314 idx_setup_iff`, `:171 idx_fire`, `cex_rig`,
    `idx_nonvacuous`;
  - `RigContract.lean:512 idx_setup`: superseded. Its H_TOKEN_STATIC is false in the running
    ring.
- *gcd_hw use:* `ulink_n1__1` (F), `ucmpi0`.
- *Grade:* B. The margin is about 118 ns on illustrative bands.
- *Status:* unchecked on a route; it would take a gross error to fail.
- *Test:* routed SDF of idx → d pins vs 16 hk periods.

**BH28. Rig verdict hygiene.**
- *Statement:* the arm reaches every sticky before an idx-derived change does. No pre-reset result
  survives. The result is bundled. The hold bits are static. Synchronisers resolve. The steady
  paths do not glitch.
- *Names:* H_ARM_BEFORE_IDX, H_RESULT_FRESH, H_NOGLITCH_STEADY (Lean text); H_RES_BUNDLED,
  H_HOLD_STATIC, H_SYNC_RESOLVES (**prose only**, B-rig-contract §3); C_STALE (unproved).
- *Lean:* `RigContract.lean:425 verdict_current`, `verdict_attrib`, `stale_window`;
  `SelfAuditB3.idx_setup_witness`.
- *gcd_hw use:* the rig's stickies, `errv`, the vector ROM.
- *Grade:* B. H_SYNC_RESOLVES is excluded by the digital-only north star.
- *Status:*
  - `verdict_current` is confirmed (Bsa).
  - "Refuted / explained exactly" is downgraded to "excluded given H_RESULT_FRESH".
  - The `errv` capture race (`err_flt` rise + setup ≤ BUFG insertion) is unverified and may fail.
    It affects only the diagnostic word.
- *Test:* EndpointOK on H_ARM_BEFORE_IDX (margin about one hk period); GLS of the errv capture.

### 1i. Contract route only (A's §7; not on the capstone's path)

**BH29. Contract-route hypotheses.**
- *Names:*
  - H_X_LEAD (`ContractsLink.link_x_lead`, no rule checks it);
  - H_ROUT / H_AIN;
  - the mux identification hypotheses;
  - `Port`'s infinite edge sequences (gap G4);
  - ContractsTrunc's edge times given up front (liveness assumed, Bsa).
- *Lean:* `Contracts.net_refines_ports`, `ContractsTrunc.net_refines_causal`;
  `SelfAuditB.net_refines_causal_witness`, `SelfAuditB4.steer_contract_witness`.
- *gcd_hw use:* not applied to gcd_hw.
- *Grade:* B.
- *Status:* the witnesses exist. `ContractsMux.mux_contract`'s "joint witness" wording is
  OVERSTATED: two select traces drive one physical `s` net.
- *Test:* —

---

## 2. Findings for B's own files (not edits; for the lead)

1. **The JSON `hypotheses_not_inequalities` H_NO_RETURN entry is stale.** It says "argued, not
   proved". `ResetGcdWave.gcd_first_wave` proves it for the reset-release window. The residual is
   H_RST_BEFORE_LOOP (`W < 34`).
2. **The JSON `conventions.corner_rule` still says the box is "always sound".** That is false for
   κ > 0 under A's model (`box_unsound_with_kappa`). It also says a SLOW_MAX-only check plus the
   guard works, which is the H_WIRE_RATIO model only (`slow_only_unsound`). Bk2's patch applies
   cleanly (Bj) but is held until ConstraintsKappa is lake-checked.
3. **JOURNAL-B's uenv1 RT_FB numbers (−114/−219, −81/−201) do not match C-10h:168-170**
   (−117/−221, −86/−243). B-rig-token already uses C-10h's.
4. **The JSON `rule` fields mean the shipped cells/verify rules.** For gcd_hw, tcheck's
   Rc/Z/Fd/X/W rows check several entries marked "UNCHECKED": `bd_c*.env_latency`/`sel_order`
   (Rc), `bdc_amerge` (Z), `bd_delay_gated.gate` (Fd), `bd_mux.uxa_rtz` (X), latch
   `setup_pulse` (W). A `tcheck_rule` field per entry would stop readers taking "UNCHECKED"
   literally for gcd_hw.
5. **Four files are in the tree but no probe has reported them** (`OnGcdArbA0`, `LibGapMuxN`,
   `NecessityReset`, `LibGapLatch`). Nothing above depends on them.

---

## 3. Changes for gcd_hw_hypotheses.md

The ids below are the current file's. It is the 10:54 rewrite: §2.x rows by hypothesis name,
§3 by obligation, §5 S*/D* (kept from the 06:40 draft). The 06:40 ids that B notes still cite
map as follows:
- C11 → §2.4 H_BUNDLED_IDX;
- C14 → §2.4 latch row (H_FORK_DATA);
- C16 → §2.6 H_START_ONCE;
- "X1/X2 (§7)" → A-contradictions X1/X2, now §5 S3/S4;
- N* → no B content.

**§0.3 item 7 (rig), §3 last row ("rig sticky race, idx setup"), §8 row 48, §9 "Dropped as
evidence: RigContract".** All four are stale: RigContract compiles now.
- §0.3 item 7, replacement: "The rig. Result capture, `ok`/`err` and the vector ROM are not
  composed with §0.1. `RigContract.lean` compiles under the lakefile options since the 10:54 fix
  of `stale_window`'s auto-bound `e` (JOURNAL-B 10:54; Bsa: 19 B files OK). `verdict_current` is
  confirmed. `RigContract.idx_setup` assumes H_TOKEN_STATIC, which the running ring breaks, and
  is superseded by `RigIdx.idx_setup_iff` (exact: `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`).
  'Refuted' in B-rig-contract reads 'excluded given H_RESULT_FRESH'. The env ring's start
  discipline is `RigToken` (§2.6)."
- §3 last row, replacement: `| rig idx setup; verdict | outside §0.1 | RigIdx / RigContract |
  idx_setup exact, unevaluated on a route (margin about 16 hk cycles); verdict_current proved;
  C_STALE and the errv capture race unproved | B | open |`.
- §8 row 48 status, replacement: "Fixed at 10:54 (autoImplicit). Compiles; claims corrected in
  B-rig-contract's correction block."

**§2.2 H_FB_FIRST row.** Append to evidence:
- "B's exact form is strict. In the per-pin Kleene model the race is clean iff
  `dlmax + dwmax + wa ≤ dlmin + E` with `wa ≥ 1` tick (`CElemStrict.env_latency_iff`,
  `env_latency_strict`). It holds on every cycle of every C-element INIT (`CElemStrict2.c2n_all`,
  `c3_all`, `c4_all`). No kernel margin is within 1 ps.
- Per pin with site pins on Br's `--freq 100` seeds 1-4: 0 negative at any one corner; 5-10 per
  seed negative in the independent box.
- The uenv1 failure is formal in its consequence: `RigToken.stale_fb_extra_start` gives 3 start
  offers against 1 result."

Grade unchanged.

**§2.2 H_SEL_PIN row.** Replace "The hold half is unchecked (B's `bundled_s_hold`)" with:
- "Setup and hold are exact per pin and per output:
  - `LibGapSteer.steer_box_exact`: `S0 + Shi ≤ R + Rlo` and `F + Rhi ≤ S1 + Slo`;
  - counter-trace `spurious_token`: a token goes down the wrong loop exit.
- For bd_mux joins, `LibGapMux.join_box_exact`: the request and feedback pins drop out of the
  exact condition.
- Rule E checks setup without site pins. In the box it is optimistic by up to
  `SP[s].hi − SP[req].lo` plus the arc difference.
- The hold half has an exact theorem but no rule.
- bdc_muxn3: `LibGapMuxN` in progress, adding H_YOSYS_MAP."

Rule K text unchanged.

**§2.2 H_LUT_SI row.** Append:
- "B's WinFifo: `Win` alone never gives FIFO for a band ≥ 2 ticks (`win_glitch_not_fifo`). Under
  the protocol spacing, FIFO ⟺ `Win` + **H_NO_REVERT** (`win_fifo_of_no_revert`,
  `no_revert_of_ret`), and H_NO_REVERT cannot be dropped (`WinFifoCausal.no_revert_needed`).
- A derivation of `LutSI` from a window channel will likely need the same inertial-type premise.
  H_NO_REVERT is the candidate name for the physical row."

**§2.2 H_CTREE_ATOMIC row.** Append:
- "Timed tree latency: `CTreeTimed.tree_four_phase` (C7, sufficient). Node races strict:
  `CElemStrict2.c3_all`/`c4_all`. Still no route row."

**§2.3 arbiter row.** Replace the evidence after "RT1/RT2 and H_GRANT_FORK." with:
- "RT1/RT1b are **proved on the routed gcd_hw numbers**. `OnGcdArb.gcd_rt1_all`/`gcd_rt1b_all`
  cover 36 arbiters × 4 tcheck routes × 4 one-corner readings, for every server, worst +33 ps.
  In the independent box they need an on-chip server path of up to 711 ps (exact, `box_rt1` +
  `_cex`).
- A0 fork: Jx 72/72 within each column; guarded worst −9 ps (seed 4 merge12.uarb2 c2).
  `OnGcdArbA0` (in progress) instantiates 7g's exact condition per pin.
- Under A's κ model on link_arb (not gcd_hw), `OnNetlistArbKappa`: safe on 8/8 at κ = 1/11. At
  κE = 0.1988 it is 7/8 in the side-pessimistic reading, with s1 c2 unsafe from κ* ≈ 0.1786.
  Not yet lake-checked (needs Mathlib)."

Then keep the rule J / H_GRANT_FORK sentences.

**§2.4 latch row.** Append:
- "Setup data and pulse are strict (+1 tick; `CElemStrict.latch_facts`,
  `CElemStrict2.pair_o5_clean_iff`/`pair_o6_clean_iff`).
- At fork branches, the exact obligation is H_FORK_DATA_W
  (`Td + dhi + fhi ≤ Tr + rlo + wlo + elo`, `ForkData.fork_capture`, `fork_data_needed`). That is
  rule I's form. C-8f's 'data before req' is sufficient only (`edge_form_not_needed`).
- Br, with site pins at a consistent corner: rule I ≥ +1288 ps guarded; rule H +40 ps guarded on
  its worst bit."

**§2.4 H_BUNDLED_IDX row.** Append:
- "gcd_hw's control_merges are width 0, so the index is the only data. Its consumers are Muller
  links through the `_f` fork. There the exact condition is H_FORK_DATA_W with `Td` = index
  settle time (`ForkData.amerge_idx_sufficient`/`_necessary`). Cm2's edge-sampling legs are
  sufficient there."

**§2.5 initial state row.** Replace "One routed check remains: rst wire delay W < 34 LUT steps" with:
- "H_NO_RETURN is proved for the reset-release window (`gcd_first_wave`, every rst waveform). The
  remaining routed check is H_RST_BEFORE_LOOP, max rst-net delay < 34 GMW steps (`gcd_loop_late`,
  `rst_reads_low`).
- Per-cell reset width is exact and strict (`CElemStrict2.reset_width_iff`/`_strict`). It binds
  for the 185 bd_c2n link controllers, whose reset vector is a hold vector."

Add: "The uenv1 token (1) is produced in any rst order (`RigToken.uenv1_release`). The time-origin
correspondence (`start.req = 1` at release vs `Src.iz`) is stated in B-rig-token §4.3 and not
mechanised."

**§2.6 H_START_ONCE row.** Replace the evidence with:
- "Necessary with `Src` (C-8r, argued).
- B proves the rig's form: `RigToken.start_once_prefix` (H_START_ONCE before the first returned
  result) and `start_per_result` (`#start ≤ #results + 1` on every lap). The premises are
  H_UENV1_HOLD (exact: `short_rst_many_starts`), H_ACK_QUIET, H_RST1_ONE_FALL, H_FB_FIRST at
  uenv1, FIFO LUTs and wires.
- The global form is false over a whole rig run.
- Missing bridges: a T-bounded capstone, laps ≥ 2, the time origin, H_ENV_REFINES_SRC (prose).
- uenv1's H_FB_FIRST fails under the band on seeds 2 and 4."

Grade: B for lap 1, **C** while uenv1's RT_FB fails under the band. Test unchanged, plus "on seeds
2 and 4 at the fast corner".

**§3 "matched-delay drain" row.** Append:
- "B's exact form: `LibGapDelay.box_exact_flushed` / `box_exact_no_early`, under H_BAL_HI,
  H_LO_ORDER, H_START, H_SHORT.
- Per-stage H_GFLUSH is not necessary without H_LO_ORDER (`rescue_flushed`).
- Rule F lacks the in-flight term `(p i).hi − (q i).lo`.
- H_LO_ORDER is unchecked on every route."

**§3 "merge M3, C-tree depth (C7), steer select hold" row.** Replace with:
- "C-tree depth (C7, `CTreeTimed.tree_four_phase`); steer and mux select hold (exact:
  `steer_box_exact`, `join_box_exact`); M3 (bdc emits no bd_merge, so not in gcd_hw). No rule for
  any of them. UNCHECKED, grade B."

**§3 new row.**
- `| arbiter RT1/RT1b | H_ARB_EXCL (grant part) | Lean on routed rows (OnGcdArb) | 144/144
  one-corner rows proved, worst +33; box needs server ≥ 711 ps | A one corner / C box | proved
  per route (one corner) |`

**§5 D12 H_ONE_CORNER.** Append:
- "ConstraintsKappa: a one-corner (κ = 0) check is unsound for κ > 0
  (`one_corner_unsound_with_kappa`). Under A's model the box is unsound too, unless κ is applied
  (`box_unsound_with_kappa`). A SLOW-only check is unsound even at κ = 0. The exact closed form is
  `GenOK` (`allOK_iff_gen`, under H_DISJ + H_DIV); a shared prefix cancels (`allOK_cancel`)."

**§5 D15.** Append: "The band is exactly κ = 383/1927 under A's model (`Corner.guard_kappa_iff`)."

**§5 D11.** Append: "B's arbiter verdicts at κ = 1/11 and κE (link_arb, OnNetlistArbKappa) need
κ < 0.178 on the A0 tails."

**§5 S1 H_KLEENE_LUT.** Append:
- "Its timed per-pin form (H_MUX_KLEENE, X for `wa ≥ 1`) is what makes every own-feedback race
  strict (CElemStrict).
- A's statement is `Core/LutTree.lean:279 H_mux_kleene`; MuxTree reduces the tree to it."

**§5 S3 H_LUT_FIFO / NoOvertake.** Replace "B's timed cells and contracts (§7)" with:
- "B's timed cells and contracts (§7), and RigToken.
- Not derivable from `Win` (`win_glitch_not_fifo`). Equivalent to `Win` + H_NO_REVERT under the
  protocol spacing. Derived for the pipe LUTs (`WinFifoCausal.pipe_fifo`), not for the lines or
  H_TREE_FIFO.
- Grade B (inertial-type)."

**§5 S4 H_ZERO_DELAY_FN / H_ATOMIC_LUT.** Append: "B: with atomic selects (`wa = 0`) equality is
safe; otherwise only the strict form is (`env_latency_atomic` vs `env_latency_strict`, agreeing
with A's `safe_strict`)."

**§5 S6 site pins.** Append: "Rule E optimism quantified per pin (LibGapSteer note §3). Feedback
on pin 1 at uenv1 on every seed (B-gcd-routes)."

**§6 tests.** Add:
- rig GLS: one `start_req` rise between consecutive `res_req` rises on seeds 2 and 4 at the fast
  corner (H_START_ONCE, H_FB_FIRST at uenv1);
- routed SDF check of H_RST_BEFORE_LOOP (max rst-pin delay < 34 fast-min LUT+wire steps on
  `ulink_n1__1 → ucmpi0 → join → steer`);
- per-route H_LO_ORDER on the 29 gated lines;
- rule E' and J' with FASM site pins (or LOCK_PINS on feedback and select pins);
- a LUT-ring edge count for H_NO_REVERT.

**§7.** Add:
- "B's FIFO fields reduce to `Win` + H_NO_REVERT (WinFifo, WinFifoCausal).
- Non-vacuity of `net_refines_causal` on a 1-channel net (`SelfAuditB.net_refines_causal_witness`)
  and of `steer_contract` (`SelfAuditB4.steer_contract_witness`).
- `mux_contract`'s 'joint witness' drives two select traces for one physical `s` net (Bsa:
  OVERSTATED wording)."

**§9.** Add: "B since 10:48:
- strict feedback race (CElemStrict/2);
- per-pin exact steer, mux and gated-delay conditions (LibGap*);
- fork data (ForkData);
- FIFO ⟺ Win + H_NO_REVERT (WinFifo*);
- RT1/RT1b proved on gcd_hw routes (OnGcdArb);
- κ verdicts (OnNetlistArbKappa, ConstraintsKappa; Mathlib pending);
- rig start discipline (RigToken) and idx setup (RigIdx);
- RigContract compiles."
