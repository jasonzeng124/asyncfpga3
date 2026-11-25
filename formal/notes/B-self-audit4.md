# B-self-audit4 (probe Bsa4): adversarial audit of shard B's 2026-10-29 commits

2026-10-29. Scope: `git log --since='2026-10-29 07:00' -- formal/lean/Formal/Cells formal/out`,
commits 9372e3b (Bj5), b734c0a (Bxw KleeneWin), 681cd3b (Bsa3 SelfAuditB6), 0941be2 (Bipw
IpowCells), 3e63dc1 (Bnx5 Necessity5*, Bfb LutFbBridge, Bpess KleenePess, Bjw RigSrcWitness),
00b81d2 (Bkx19 OnGcdArbKappaTight(+A), Blap RigLaps), 7307ca7 (Bnx4 Necessity4Mux*), 14005d2
(Bshp KappaCPPR), 260e219 (Brz ResetCapstone*, Bzd ZeroDelayRefine, Bj6 JSON). Claims checked
against JOURNAL-B.md progress 07:50 ... 11:05, the commit messages and the file headers.

Every check went through `/tmp/claude-0/btools/bcheck.py` (lean -DautoImplicit=false).

## Files

- `formal/lean/Formal/Cells/SelfAuditB7.lean` -> **OK** (core + the audited files; no sorry/axiom/
  native_decide).
- mutants `formal/lean/Wip/Bsa4/M01..M17_*.lean` (not built; each is a full copy of the shipped
  file with ONE change, named in its first line); `Wip/Bsa4/Ax.lean` (axiom printout).
- scratch: `/tmp/claude-0/probes/Bsa4/` (check logs, JSON regeneration).

Re-checked as shipped (all OK): KleeneWin, KleenePess, LutFbBridge, Necessity5Arb,
Necessity5Delay, Necessity5Mem, Necessity4Mux, OnGcdArbKappaTight, OnGcdArbKappaTightA (Mathlib),
RigLaps, ZeroDelayRefine, ResetCapstoneWit, ResetCapstone, KappaCPPR (Mathlib), IpowCells.
JSON: regenerated in scratch with `cell_constraints.gen.py` (runs `cell_constraints.bj5.py`):
**byte-identical** to the committed `cell_constraints.json`; validator: 0 errors; 137 rows, 40
exact; `kleene_dependence` on 72 rows (64 both / 6 reset value / 2 pass0), as the journal says.

## New in SelfAuditB7 (checked)

| theorem | what it settles |
|---|---|
| `flush_not_necessary_all` | H_ACK_FLUSH not necessary for EVERY DACK = m+1 ≥ 3 (line `δ k = m+1-k`, w = 1, point delays). The shipped `flush_not_necessary` is only DACK = 3; the journal/JSON say "DACK ≥ 3". Gap closed. |
| `steer_win_bound` (+ `_witness`) | the JSON `strict.x_window` text "Sufficient without the split: +W under H_W_BOUND" had NO Lean theorem. Proved for bd_steer only; join/muxn/latch/C-element NOT written. |
| `μW_not_wiring` | the joint witness's map μW reads req AND ack of channels 7 and 8 from one node (65) and still meets `MapOK`: H_MAP does not encode wiring. |
| `wv_frozen` | the "non-degenerate" D = 40 reset witness shows the reset value on every node at every step k ≤ E: nothing moves before E. |
| `abs_run_indep` | ZeroDelayRefine's zero-delay link run depends on the physical behaviour only through one bit (`swOf`). |
| `spread_corr_iff` | `H_SPREAD_CORRELATED arc ↔ arc = litArc`: the named hypothesis IS the lit model. |

Axioms (`Wip/Bsa4/Ax.lean`, ends in a deliberate failing `example` so the checker prints):
`flush_not_necessary_all`, `steer_win_bound`, `steer_win_bound_witness`: propext, Classical.choice,
Quot.sound; `μW_not_wiring`, `spread_corr_iff`: propext, Quot.sound; `wv_frozen`: propext;
`abs_run_indep`, `dU_two`: none.

## Verdicts: Lean files

| file | claim (journal / commit / header) | verdict | evidence |
|---|---|---|---|
| KleeneWin | per-edge iffs `steer_win_exact`, `join_win_exact`, `muxn_win_exact`, `latch_win_exact`, `cel_edges_iff`, `cel_env_iff`: each race gains c(first)+a(after), "exactly" | **CONFIRMED** | read; iffs with the stated side conditions (widths ≥ 0, `R - aR < F + cF`, ...). `latch_win_exact` is `LibGapLatch.box_exact` with renamed parameters (no new semantics). The necessity halves use a binary trace over the OUTER window edges, which the model allows ("anything inside"). M01 (c2 hazard point 421→422) FAIL, M02 (+1 slack on steer setup) FAIL |
| KleeneWin | `steer_split_matters`: "+1 strict" comes from H_X_UNIFORM | **CONFIRMED** (for bd_steer) | the two parameter points are decided through `steer_win_exact`; no instance for join/latch/C-element (by the same formula, not instantiated) |
| KleeneWin | H_FB_WIN: CElemStrict's strict point is a hazard at wq = 1 (`c2_fbwin_hazard`) | **CONFIRMED** | real bd_c2 INIT (via `c2Cycle`), D = 420 (`sim_loopW` with d = 419). Remark: in `box_iffW` the window enters exactly like extra loop delay (`tb + Dhi + Wq + wb ≤ slo`); H_FB_WIN is indistinguishable from a larger D in these theorems |
| KleeneWin / JSON | "Sufficient without the split: +W under H_W_BOUND" (JSON strict.x_window, 71 rows) | **OVERSTATED** as shipped (no theorem); now proved for steer only | `SelfAuditB7.steer_win_bound`; other cells open |
| KleenePess | bracket, `lutP_definite` (any per-pin policy, any order), safety transfers | **CONFIRMED** | read; M03 (C2N_INIT `00B2..`→`00B3..`) FAIL at `c2nM_restore` |
| KleenePess | journal: "join +w fails under every pessimistic model (explicit runs)" | **OVERSTATED** | `JoinEdgesM`/`jKM` take ONE uniform `Pol`; `join_fails_weak1` + `join_fails_weak0` (p0 = false) cover the three uniform pessimistic policies only; per-pin policies (the file's own general family) are not covered. The header says "uniform" correctly |
| KleenePess | INITs | **CONFIRMED** | C2N `00B2..` = bd_ce.v:49 (bd_c2n); C2 `00E8..` = :34; ODD `B8B8..` = bd_latch.v:44; GR `0C0C_0C0C_A0A0_A0A0`, ST `FFF0_FFB2_ACAC_ACAC` = bd_arb.v:245/249 |
| LutFbBridge | `link_lutFb`, `c2_lutFb` + instances: C's LutFb/FbFirst from B's physical model + env | **CONFIRMED** (implications, named H_LUT_POS, H_PWR, Env1/EnvC, Timing1) | read; M04 (EnvC `Es` 2→3 in `c2w_env`) FAIL |
| LutFbBridge | witnesses "LUT bands [1,3]/[1,2], wire 1" | **CONFIRMED**, with degeneracy | `c2_witness` is a fixed transport delay of exactly 1 (`hx`: `sq 6 t = exC (t-1)`) inside the [1,2] band; wire fixed 1. The band width is a parameter, not exercised. `link_witness` (Wx.witness1) does use the 2-tick-wide window |
| Necessity5Arb | `grant_skew_exact`: exclusion iff `|d6-d5| ≤ L`, every delay triple | **CONFIRMED** | for constant transport delays and `0 < L` (stated). M05 (`formA_run` hypothesis weakened to `d5 + L ≤ d6`) FAIL |
| Necessity5Arb | `settled_iff` | **CONFIRMED** | Boolean identity over 4 cases |
| Necessity5Delay | `two_exact` (DACK = 2 exact), `pulse_iff` | **CONFIRMED** (point delays, line level) | M06 (two_exact at m = 2) FAIL (structurally, at a rewrite; the mutated statement is false by `flush_not_necessary`); M17 (copies (3,2,1)→(5,3,1) in `flush_not_necessary`) FAIL (semantic) |
| Necessity5Delay | journal/JSON: "NOT necessary for DACK ≥ 3" | **OVERSTATED** as shipped (one instance, DACK = 3); **CONFIRMED** now | `SelfAuditB7.flush_not_necessary_all` (every m ≥ 2) |
| Necessity5Mem | setup/hold/rdata/clk_high/clk_low exact in the event model | **CONFIRMED** | `fast m0` realises every minimum; M07 (`tSU ≤ dsLo + 1`) FAIL |
| Necessity5Flink/Link/PipeRst | boundary-tight at one parameter point each (Lean ≤, guard 0) | **CONFIRMED** (read, not mutated) | statements are `¬ Claim 1` against the shipped hypothesis sets, as the journal says; not iffs |
| Necessity4Mux | `pass8` (S_J0_X not necessary, violated by 3), `fail10`/`claimX1_false` (max form tight at slack 1) | **CONFIRMED** | read; M08 (`fail10` with `MuxStaticN … 0 0`) FAIL. Mostly unit-delay run (one 8/10-tick feedback net) |
| Necessity4MuxC | `claimC1_false`: S_J0_C necessary at the boundary | **CONFIRMED** (read) | one point; not mutated |
| Necessity4MuxN | `pass8` (bdc_muxn S_J_X not necessary) | **CONFIRMED** (read) | boundary of the max form not shown (stated) |
| OnGcdArbKappaTight | `rt1b_safe` ≤ κS, `rt1b_unsafe` ≥ κU, gap 1/749546000000 ≈ 1.3e-12 | **CONFIRMED** | certificate + soundness; M09 (κS numerator +1, = κU) FAIL at `cert_ok` (kernel decide) |
| OnGcdArbKappaTight | journal: "The whole κ_ex − κ* (~3.9e-6) is the 1 fs grid" | **OVERSTATED** (not proved) | the note itself says "(not proved here)"; the journal states it as fact |
| OnGcdArbKappaTight | `rt1b_gate_unsafe`: gate-level overlap, real INITs, all t | **CONFIRMED**, degenerate witness (as stated) | `DU`: smin = wa0s = qr = 0, every client-1 arc and both ua_k arcs 0, wfb = 1 fs; the server lowers A0 in 0 fs and re-raises it 1 fs later. The journal names the first three zeros; the rest are stated only in the header |
| OnGcdArbKappaTight | "Lit safety now carries the named hypothesis H_SPREAD_CORRELATED" | **CONFIRMED** as wording; (e) the hypothesis is definitionally the lit model | `SelfAuditB7.spread_corr_iff`; `spread_correlated_safe` is `rt1b_safe` after `subst` |
| OnGcdArbKappaTight(+A) | headers: bridge "Wip/Bkx19/... written, NOT checked" / "WIP: NOT checked" | **STALE header** (the code is better than the header) | `OnGcdArbKappaTightA.lean` is in Formal/Cells and checks OK here (Mathlib built) |
| OnGcdArbKappaTight | "credited threshold 0.651 (design min 0.0802)" | **CONFIRMED by citation only** | numbers are OnGcdArbKappa's existing rows (`rt1bs` 3.merge12.uarb1 0.651; `lit_srv_min` 0.0802); nothing new in this file |
| KappaCPPR | `allOK_net` (common arcs cancel exactly), `genOK_full_iff` (pessimism exactly 2κ·C_s) | **CONFIRMED**; (e) the cancellation is definitional under H_ONE_DELAY (one number per arc id on both sides) | read. M11 (drop `.cr2` from uRT1b's Q) FAIL at `fulls_common` |
| KappaCPPR | "Bk3's forms ARE the CPPR forms" (`fulls_net`) | **CONFIRMED relative to the hand-written `fulls`** | the 18 un-netted conditions are a transcription in this file ("transcribed from their definitions"), not derived from the source files' path accounting in Lean: transcription UNVERIFIED |
| KappaCPPR | design threshold unchanged, split rows ≥ 0.2004 | **CONFIRMED** | `design_cppr_safe/_tight` at Bk3's bracket (16587/374773, 33181/749546), `split_fork2_*` |
| RigLaps | lap contract (`lap_offer`, `lap_close`, `lap_result`), H_SINK_SI with FIFO read map | **CONFIRMED** | read; M10 (`r + dF + dP ≤ T` in `lapinv_fails_pend_fast`) FAIL |
| RigLaps | `gcd_rig_every` given LapInv; no witness | **CONFIRMED** (honestly stated as unwitnessed) | LapInv at every close is a hypothesis; `lap_cut_fails` shows it fails under H_PEND_FAST |
| RigLaps | `pend_fast_nonvacuous` | **degenerate** | every wire constant true, dF = dP = 0, not a rig run (no joint witness with `Ring`) |
| RigLaps | "H_PEND_FAST, expected on silicon: 2 LUTs vs 16 delay elements" | **not Lean** (argument) | |
| ResetCapstone | `rtl_not_idle`; commit: "C's idle init is unreachable for the RTL"; journal: "The RTL never reaches that state" | **OVERSTATED** | proved only for shifts T0 ∈ [23(D+W+1), E] with rst held (and, via `rtl_env_high_release`, until a frontier link moves); nothing for T0 < 23(D+W+1) or after the frontier moves |
| ResetCapstone | `gcd_hw_safe_after_reset` (headline) | **CONFIRMED** as an implication; weak B-side content | H_MAP = `MapOK` + values at T0. `SelfAuditB7.μW_not_wiring`: the witness map sends 458 cold channels' req and ack to ONE node; MapOK constrains only which nodes are in `onesL`. So the headline is C's `gcd_hw_safe_from_reset` from `AtS`, with `AtS` read through any value-consistent map. M12 (μW ack of channel 3 → node 65) FAIL at `μW_ok_b` |
| ResetCapstone | `reset_capstone_nonvac` "all hypotheses jointly" | **CONFIRMED, doubly degenerate** | frozen C family (stated) AND the degenerate map μW (not stated) |
| ResetCapstoneWit | journal: "nonvac_net2 (D=40, W=1, H_STEER_HOLD live on 6 steps) replacing the degenerate D=W=0 reset witness" | **OVERSTATED** | `SelfAuditB7.wv_frozen`: power-up = reset state and every gate holds until E, so no node moves before E; H_STEER_HOLD holds on (1001, 1007] because nothing moves. The delays are nonzero, the behaviour is the all-quiet one. Bsa3's R5/Re witnesses move (all-zero start) but have D = W = 0: no witness has both. M13b (F 967→966) FAIL at `w_hold_long` |
| ResetCapstoneGlue | `glue_cells`, `cap_idle0` | **CONFIRMED** (read; covered by M12's dependency build) | 3 virtual ticks, `side_chk` decided |
| ZeroDelayRefine | `link_refines`, `link_ref_iff` ("link exact iff its six rows") | **CONFIRMED**; (e) content is LinkExact.exact | `link_ref_iff` → uses only `linkRef_spec` (LinkRef ⇒ LinkExact.Spec); `LinkRef.req_in/ack_out` are copies of `Beh.env`; the abstract run is fixed (`SelfAuditB7.abs_run_indep`). M14 (`kA true` 3→4) FAIL |
| ZeroDelayRefine | steer/mux counter-runs refute every retiming | **CONFIRMED** (read) | via `steer_unsel_never`/`mux_unsel_never` |
| IpowCells | `ipow_safe_of_contracts`, `cell_of_contract` | **CONFIRMED**; (e) much of each `Contract` is C's Cell verbatim | src/sink/muxn contracts ARE C's models (`exact h`); every `init*`, H_WIRE_DI, H_DATA_*, H_ARB1/2/EXCL, H_AMERGE_RTZ fields are copied; H_CTREE_ATOMIC is built into the definition of `cgate` (arity ≥ 5 ↦ flat `celL`), not a field. The journal's list of uncited hypotheses omits H_WIRE_DI and the init fields. M15 (`dvL` first value 3→4) FAIL |
| IpowCells | non-vacuity "all-quiet only" | **CONFIRMED** (stated plainly) | quiet `FbCel` uses `BoundedDelay 0 0` |
| SelfAuditB6 | `rig_env_feeds`, `rig_env_latch` (474, 6), `rig_env_relap` (432) | **CONFIRMED** | read; unit delays, identity maps (stated) |
| RigSrcWitness | lagged joint witness: out0 offered 438, latches 6 at 489 | **CONFIRMED** | constant lags (β = t-3, φ1 = t-5, φ0 = t-4, γ = t-2/3/5), urdly 7; kernel gates delay 1; the env is stopped after uenv1's second rise (stated in the header) |

## Verdicts: cell_constraints.json (rows changed today, sample of 19)

| row | label / claim | verdict | evidence |
|---|---|---|---|
| bd_link.stage (new) | exact, six rows | **CONFIRMED** | LinkExact.exact under Wf + Split (cited) |
| bd_mux.uj0_env_latency_req_max (new) | sufficient+necessary_at_boundary, `Lj0.hi + wj0h + 1 ≤ Lj0.lo + max(W0x.lo, W0o.lo+Lor.lo+Dz.lo+Es+Wzx.lo) + …` | inequality **CONFIRMED** (= `S_J0_XR` + strict +1); label **OVERSTATED** for the form as written | `fail10` refutes the BINARY form at slack 1; the JSON form (+1) is 2 ticks from that point (the note says so: audit P8 item 1 caveat) |
| bd_mux.uj1_env_latency_req_max (new) | sufficient | **CONFIRMED** | `mux_ok_staticN` |
| bdc_muxn.uj_env_latency_req_max (new) | sufficient | **CONFIRMED** | `muxn3_ok_staticN`, `S_J_XR` |
| bd_delay[FASTRISE].ack_succ (new) | exact (point delays) | **CONFIRMED** | `pulse_iff`; scope says point delays |
| bd_mem.clk_high_width_exact (new) | exact, `tPWH ≤ dcLo + dsLoF` | **CONFIRMED** | `clk_high_exact` |
| bd_mux.uj_env_latency_req | not_necessary | **CONFIRMED** | `pass8`; note keeps Lt4's stale "No counter-run" sentence before the Bnx4 text |
| bd_mux.uj_env_latency_ctl | sufficient+necessary_at_boundary | label as for uj0 max (**OVERSTATED** for the +1 form); note **inconsistent** | note still says "Sufficient; necessity not shown" before "Bnx4 … refuted by one run" |
| bdc_muxn.uj_env_latency_req | not_necessary | **CONFIRMED** | Necessity4MuxN.pass8; note keeps "not probed for muxn" (stale) |
| bd_arbcell.grant_skew | exact `|d6-d5| ≤ L` | **CONFIRMED** | `grant_skew_exact` (constant transport delays, 0 < L) |
| bd_arbcell.settled_exclusion | exact on its precondition | **CONFIRMED** | `settled_iff` |
| bd_delay[FASTRISE].ack_flush | not_necessary; note "NOT necessary for DACK >= 3 (flush_not_necessary, dack3_clean)" | **OVERSTATED** as cited (DACK = 3 only); **CONFIRMED** with `SelfAuditB7.flush_not_necessary_all` | |
| bd_mem.setup | exact `tSU ≤ dsLo` | **CONFIRMED** | `setup_exact` |
| bd_mem.clk_high_width | not_necessary | **CONFIRMED** | `clk_high_not_necessary` |
| bd_arbiter.rt1b | inequality credits `smin + wa0s + qr`; row `hypotheses`: "server-free form (smin, A0 route to ustate, ustate O6 not credited)" | **inconsistent** (OVERSTATED as a row-level hypothesis) | the server-free caveat belongs to the κ sub-result (`corner.kappa.results`); the row's own inequality is the server-credited RT1b of ArbHeldTimed2 |
| bd_flink.qfb_first | sufficient+necessary_at_boundary, `fhi + 1 ≤ …` | label **OVERSTATED** for the +1 form; note **stale** ("no flink counter-trace") | `q1_false` is the binary form at slack 1 |
| bd_link_dc.rule_K_corrected | sufficient+necessary_at_boundary | **CONFIRMED** (guard 0) | `k1_false`; strict only when guard ≥ 1 (stated) |
| bd_pipe.rst_lines | sufficient (kept) | **CONFIRMED** (conservative) | per-pin H_RST_SEL terms not covered, so not upgraded |
| bd_steer.bundled_s_setup | exact (+1 under H_X_UNIFORM, listed in `hypotheses`) | **CONFIRMED** | KleeneBox `steer_strict_K`; per-edge iff `steer_win_exact` cited |

71 of 75 strict rows carry the H_X_UNIFORM text (the other 4 are "already strict" / "strict when
guard ≥ 1", margin 0): CONFIRMED.

## Mutants (`formal/lean/Wip/Bsa4/`)

| mutant | change | result |
|---|---|---|
| M01 KleeneWin | `c2_fbwin_hazard` at s = 422 (the clean point) | FAIL (l.639) |
| M02 KleeneWin | `steer_win_exact` setup side `+ 1` slack | FAIL (l.161) |
| M03 KleenePess | `C2N_INIT` 00B2→00B3 (×4) | FAIL (l.352, `c2nM_restore`) |
| M04 LutFbBridge | `c2w_env` Es 2→3 | FAIL (l.514) |
| M05 Necessity5Arb | `formA_run` needs only `d5 + L ≤ d6` | FAIL (l.119) |
| M06 Necessity5Delay | `two_exact` at m = 2 | FAIL (structural, l.119; statement false anyway) |
| M07 Necessity5Mem | `setup_exact` RHS `+ 1` | FAIL (l.96) |
| M08 Necessity4Mux | `fail10` with `MuxStaticN … 0 0` | FAIL (l.879) |
| M09 OnGcdArbKappaTight | κS := κU | FAIL (l.549, `cert_ok`) |
| M10 RigLaps | H_PEND_FAST without the `+ 1` | FAIL (l.887) |
| M11 KappaCPPR | `.cr2` dropped from uRT1b's request side | FAIL (l.340 `fulls_common`, l.344 `fulls_net`) |
| M12 ResetCapstone | μW channel-3 ack 3257→65 | FAIL (l.355 `μW_ok_b`) |
| M13 ResetCapstoneWit | F 967→966 | FAIL, but only at the restatement `eF : F = 967 := rfl` (weak) |
| M13b ResetCapstoneWit | F 967→966 and `eF` restated | FAIL at `w_hold_long` (l.217) and `w_steer_window` (l.232): semantic |
| M14 ZeroDelayRefine | `kA true` 3→4 | FAIL (l.242, `link_mono`) |
| M15 IpowCells | `dvL` first value 3→4 | FAIL (l.546, `dataOK_all`, kernel) |
| M16 SelfAuditB7 | `flush_not_necessary_all` with `1 ≤ m` | FAIL (l.74) |
| M17 Necessity5Delay | `flush_not_necessary` copies (5,3,1), `fmax` restated | FAIL (l.141: no later copy within w) |

## Summary of findings

No theorem was REFUTED. OVERSTATED (journal/commit/JSON vs Lean): (1) "NOT necessary for
DACK ≥ 3" (one instance; now closed by `flush_not_necessary_all`); (2) "join +w fails under
every pessimistic model" (uniform policies only); (3) "κ_ex − κ* is the 1 fs grid" (not proved);
(4) "C's idle init is unreachable / the RTL never reaches that state" (one window only);
(5) the D = 40 reset witness called non-degenerate (frozen until E); (6) JSON "+W under
H_W_BOUND sufficient" had no theorem (steer proved here); (7) JSON necessary_at_boundary labels
on +1 forms (2 ticks from the refuted binary point; disclosed in the notes); (8) bd_arbiter.rt1b's
row-level server-free hypothesis contradicts its own inequality. Stale: OnGcdArbKappaTight(+A)
headers say the bridge is unchecked; three JSON notes keep superseded sentences. Hypotheses that
are the conclusion's model or verbatim C fields: H_SPREAD_CORRELATED (= lit), IpowCells'
Contract (C's Cell fields copied; H_CTREE_ATOMIC in `cgate`'s definition), ZeroDelayRefine's
LinkRef env fields (= Beh.env), H_MAP (`MapOK`, not a wiring map).
