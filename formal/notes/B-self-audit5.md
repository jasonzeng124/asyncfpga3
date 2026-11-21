# B-self-audit5 (probe Bsa5): adversarial audit of shard B's work since self-audit 4

2026-10-29. Method as in B-self-audit4.md. Scope: the commits after Bsa4 (af3be4d Bsrv/Bfb2,
d5b7ef2 Bfc, 637efa8 Bj7, f05a8d1 Bzd2, 1d2124d Bwit, 2e7221d Bbare, 60aee11 Bmap, 84bc9e4
Bnx6, 135f125 Barb2, af3de3e Bzd3/Bnet, e8f6a1e Bset, 9f97aa7 Bj8). Claims checked against the
JOURNAL-B.md progress entries 08:35 ... 09:45, the commit messages, the file headers and notes.
Every compile went through `/tmp/claude-0/btools/bcheck.py` (lean -DautoImplicit=false).

## Files

- `formal/lean/Formal/Cells/SelfAuditB8.lean`: **OK** (core only; no sorry/axiom/native_decide).
- mutants `formal/lean/Wip/Bsa5/M01..M14_*.lean` (not built; each a full copy of the shipped file
  with ONE change, named in its first line); `Wip/Bsa5/Ax.lean` (axiom printout, ends in a
  deliberate failing `example` so the checker prints).
- scratch: `/tmp/claude-0/probes/Bsa5/` (check logs, regenerations).

## Re-runs

- All 26 in-scope files re-check as shipped: OK (OnGcdArbKappaSrv, LutFbBridge2(+Env),
  IpowCellsT, ZeroDelayNet{,Phys,Tok,Wit}, ResetWitness2(+Data), ArbNoWithdraw,
  ResetCapstoneMap(+Data), Necessity6{Mux,MuxJ,MuxN,PipeSel}, ArbMultiToken,
  ZeroDelayTok{,Chain,Wit}, AssumeGuarantee{,Links,Fork,Cap}, ArbSettled).
- `python3 -B formal/tools-B/gcdnet_gen.py net <scratch>`: **IDENTICAL** to the committed
  `ResetGcdNet.lean` (3322 nodes, kernel sha256 65e61848...). `gcdnet_gen.py map` on that
  directory: **IDENTICAL** to the committed `ResetCapstoneMapData.lean`; C's netgen output equal
  to `CapstoneNet.lean`.
- Generator read for copying: `gcdnet_gen.py` opens the committed file only for the comparison
  (`COMMITTED`, l.499); `capmap.py` opens `CapstoneNet.lean` only for the comparison and uses the
  hard-coded reset-1 list `ONES` only in its self-check print (l.148). Hard-coded CONVENTIONS
  (not data): node order of the rig (`RING`, `PROBES`), name rules (`DROP_LABELS`, `CELEM`), the
  INIT name table. Dependency: the map calls C's `formal/lean/Wip/C8m/netgen.py` (a C WIP script).
  Nothing copies the committed term.
- JSON: `cell_constraints.gen.py` (runs `cell_constraints.bj5.py` on its own output, IN = OUT)
  regenerates the committed `cell_constraints.json` **byte-identical**; validator 0 errors; 139
  rows, 41 exact, 45 boundary-tight, 10 sufficient (as the journal says).

## New in SelfAuditB8 (checked)

| theorem | what it settles |
|---|---|
| `physLink_req_alternates` | Bfb2's `PhysLink i o` (it replaces `H_CELLS` for every link in `gcd_hw_safe_phys_links`, and `InChain` produces it in `gcd_hw_safe_chains`) forces `i.req` high at some `t ≥ T` and low at some `t ≥ T`, for every `T`. `eventually_const_not_physLink`: an eventually constant request has no `PhysLink`. |
| `chW_not_physLink`, `chW_not_inChain` | C's witness run `Wit.chW` (finite event lists) meets `PhysLink` / `InChain` on NO channel pair. |
| `chW_fails_H_LINKS`, `chW_fails_H_LINKS_chain` | C's witness violates `H_LINKS` of both end-to-end link theorems. Neither has a joint non-vacuity witness; every run in which some gcd_hw link stops handshaking (e.g. one gcd, then quiet) is outside both. |
| `μS_wire`, `μS_ne`, `wireOK_not_unique` | the generated table with the requests of channels 13 and 14 swapped also meets `WireOK` (and `MapOK`): the strengthened predicate does not pin the identification (consistent with ResetCapstoneMap's own NOT-covered line). |

Axioms (`Wip/Bsa5/Ax.lean`): `physLink_req_alternates`, `eventually_const_not_physLink`,
`chW_not_physLink`, `chW_fails_H_LINKS`: propext, Quot.sound; `chW_not_inChain`,
`chW_fails_H_LINKS_chain`, `μS_wire`, `wireOK_not_unique`: propext, Classical.choice, Quot.sound;
`μS_ne`: propext.

## Verdicts: Lean files

| file | claim (journal / commit / header) | verdict | evidence |
|---|---|---|---|
| OnGcdArbKappaSrv | D1 exact at κS1 = 0.080163500491 (h21), D2 exact at κS2 = 0.216552148868 (fork2), both tight to 1e-12 | **CONFIRMED** | `h21_safe/_unsafe`, `fork2_safe/_unsafe` (certificates, kernel decide). M12 (kS2 numerator +1) FAIL at `cert2` (l.749) |
| OnGcdArbKappaSrv | `h21_7j_bare`: "the same race as a run of 7j's gate relations with EVERY delay, server included (3.8 ns)" | **OVERSTATED** (degenerate, server inert) | in `S7` A0, A1, A2 are constant false and r1 constant true; 7h's `Server` constrains only A0 edges, so `H_SRV` holds vacuously (`intro t h; exact absurd rfl h`) and `smin` plays no role in the run. "A0 never rises" is stated; that the server credit is inert is not |
| OnGcdArbKappaSrv | `cons_srv_neg`: exactly g2 merge3.uarb1 h21 and o1x fail at κ = 0 | **CONFIRMED** | decide over `rows` |
| LutFbBridge2 | `celG_lutFb` and the bd_c3 / uj0 / uj1 / steer / src bridges to C's LutFb / FbFirst / LutSI | **CONFIRMED** (implications, named hypotheses) | read; `CelLaw` decided per real INIT |
| LutFbBridge2 | "non-vacuity with nonzero delays (LUT band [1,2], wire 1)" | **OVERSTATED** (degenerate, undisclosed) | every witness LUT is a fixed transport delay of 1 inside the band (`ex3_w`, `muxj_w`); the select is constant 0 (`s0`) in `muxJ0_witness` and `steer_witness` (never steers the other way); in `join3_witness` pins 0 and 2 are the same trace (`sq 4`); `muxJ1_lutFb` has no witness. M14 (no select glitch) FAIL, structurally, at `exG` (l.724) |
| LutFbBridge2Env | `gcd_hw_safe_phys_links`: C's gcd_hw safety with H_CELLS of all 175 links replaced by B's physical model | **CONFIRMED as an implication; UNWITNESSED** | `SelfAuditB8.chW_fails_H_LINKS`: C's only witness run violates H_LINKS; `physLink_req_alternates`: only runs where every link handshakes infinitely often. The header and the journal (08:35, "infinite runs only") state the restriction; neither names a joint witness, and none exists in the repo |
| IpowCellsT | `gap_exact`: transport route d ≥ 1 meets FbCelT iff d ≤ g; SI/FbCel hold for every g | **CONFIRMED** (one run family) | the gap run feeds the SAME trace to both C-element pins (`p g t = [x g t, x g t]`), so the C-element acts as a buffer (`cgate_dup`); stated in the header ("both inputs rise at g+1"). M13 (`d ≤ g + 1`) FAIL at H_RT_FB (l.204) |
| IpowCellsT | `ipow_contractsT_satisfiable` for every pinned bound | **CONFIRMED, degenerate (disclosed)** | the all-quiet run; route trace constant false |
| ZeroDelayNet* | `chain_refines`: physical N-stage chain refines ONE zero-delay C run; Causal derived | **CONFIRMED** | the C-side conjuncts are `chain_abstract`, from the parameters `ChainPar` only (the traces enter only `NetRef`), as Bsa4 found for ZeroDelayRefine (`abs_run_indep`); one token, stated. M08 (stage 1's Ra 3400 → 3399) FAIL at `pw_cell` (l.83) |
| ResetWitness2 | moving, nonzero-delay GMW reset witness (1593 wrong nodes, link_moves, delays 1/2/3) meeting every reset hypothesis; H_HOLD_LONG tight at F = 93 | **CONFIRMED** | read; periodic-sampling family and frozen C side / μW disclosed. M01 (F 93 → 92) FAIL at `w_hold_long` (l.172) and the step check `sa0` (l.207): semantic |
| ArbNoWithdraw | `gcd_hw_arb_no_withdraw`, link / steer no-withdrawal, `steer_withdraws` (100 ps pulse) | **CONFIRMED** | corollary of C's `gcd_hw_protocol` (one-instant model, stated). M02 (pulse window end 1400 → 1401) FAIL (l.256) |
| ArbNoWithdraw | `settled_L0_fails`: L = 0 fails on 65/72 clients; max L 1590.934 ps | **CONFIRMED** | `setRows_len = 65`; the 7 others have L = 0 in `setTbl` |
| ArbNoWithdraw | `design_gate_held_causal` = D2 "with H_SETTLED discharged by L ≥ setTbl" | **CONFIRMED, decoupled** | the causal history is a SEPARATE run `sr` sharing only (D, ta, t0) with the idealized `s` (s itself cannot have one, `scn_excludes_caus`); the package only yields the number `T + L ≤ t0`. Docstring says "ANY run sr" |
| ResetCapstoneMap | generator byte-identical; `μT_ok` (H_MAP a theorem); `WireOK` strengthened (`μW_not_wire`) | **CONFIRMED** | re-run IDENTICAL; M03 (hot ack channel 3 → 4) FAIL at `μT_ok_b` (l.64). `WireOK`'s link exception reads `μ` itself (`if μ.μA i == μ.μR o`) |
| ResetCapstoneMap | `WireOK` as a "wiring-faithful predicate" | **CONFIRMED with limit (disclosed)** | `SelfAuditB8.wireOK_not_unique`: a swapped table is also WireOK; the header already says the identification is the generator's claim |
| ResetCapstoneMap | `reset_capstone_map_nonvac`: "(B's wRun, D = 40, W = 1, E = 967, the frozen C family)" | **OVERSTATED (minor)** | B's side is ResetCapstoneWit's run, frozen until E (`SelfAuditB7.wv_frozen`), not ResetWitness2's moving run; only the C side is called frozen |
| Necessity6Mux | `claimY1_false`: uj1 max form boundary (z_ack branch) | **CONFIRMED** | unit delays, open-loop periodic env (stated). M04 (slack 0) FAIL, structurally (l.292) |
| Necessity6MuxN | `claimN1_false` (S_J_C met with equality, max form off by 1) | **CONFIRMED** (read) | not mutated |
| Necessity6MuxJ | `claimJ1_false`: S_XA_J.2 necessary at the boundary | **CONFIRMED** | M06 (j0 → uxa wire 12 → 11) FAIL: the hand-built run's H_W0X (l.215) and `failJ` (l.529) |
| Necessity6PipeSel | `rst_sel_boundary`: all four H_RST_SEL terms at the boundary | **CONFIRMED** | (c), (d) refute only event times (one-tick shifts), stated in file, note and journal. M05 (slack 0) FAIL, structurally (l.224) |
| ArbMultiToken | `mt_exclusion`: grants never both high for t ≥ B0 over infinitely many handovers | **CONFIRMED** | M10 (H_SLOW_REREQ 4M → 3M) FAIL in `step1` (l.724) and `step2` (l.757): the 4M is used. Witness: every route and arc exactly 1 ps, server 3, period 48 (uniform unit delays) |
| ArbMultiToken | journal: "C's H_ARB_EXCL holds AS C STATES IT for the held arbiter" | **OVERSTATED** | `H_ARB_EXCL_of_mt` holds for samples `σ n ≥ B0` of a run in perpetual alternating contention (`MTRun`: H_INIT settled with both clients requesting at B0, H_HOLD for every k); C's field covers every tick of a run from reset. The open list (from reset / idle / solo) is stated; "as C states it" is not right |
| ZeroDelayTok | `exact_rearm`: SafeK iff H_REARM, given WfK, GapK, the six rows | **CONFIRMED** (relative to SpecK) | M07 (D 2979 → 2980) FAIL at `rearm_one_tick` (l.570) and `rearm_breaks` (l.577) |
| ZeroDelayTok | "if it fails ... the stage breaks" (`rearm_breaks` docstring), new safety row | **OVERSTATED** (reading, not Lean) | `need_rearm`'s failure is that at `U1 (j+1)` the real INIT still holds 0 while the previous ack is read high: the node rises later than SpecK's request-derived window, not a hazard shown. The header itself says a spec with the rise window `max(request rise, previous ack fall)` would absorb H_REARM |
| ZeroDelayTokChain / Wit | `chain_specK`, `chain2_witness` (2 stages x 2 tokens) | **CONFIRMED** (read) | |
| AssumeGuarantee | `ag_time` sound only with strict causality (`zero_delay_cex`) | **CONFIRMED** | M09 (non-strict side condition) FAIL in `ag_time` (l.56) |
| AssumeGuaranteeLinks | `chain_env1` for chains of any length, `ring_dead` | **CONFIRMED** | witness `wD N`: shifted square waves (period 8), LUT delay exactly 1 inside the [1, 3] band |
| AssumeGuaranteeCap | 100 chains, head/tail classes (43 steer, 72 mux, 32 join, 44 forks, 5 amerge, 4 muxn) | **CONFIRMED** | decide; the journal's class sums match `head_classes` + `tail_classes` (= 200) |
| AssumeGuaranteeCap | `gcd_hw_safe_chains`: every link's Env1 derived | **CONFIRMED as an implication; UNWITNESSED** | `SelfAuditB8.chW_fails_H_LINKS_chain`; `inChain_witness` is one chain in isolation, data constant 0; InChain per link (stated) |
| ArbSettled | H_PIN strictly weaker than H_SETTLED; setTbl2 max 502.361 ps, 21/72 clients, exact to 10 fs | **CONFIRMED** | `ofScn`, `strict_witness`, `settledP_tight`. M11 (63855 → 63845 fs) FAIL at `set2_cert` (l.828) |
| ArbSettled | "Link-driven clients: discharged with NO latency hypothesis on 18 of 20" | **CONFIRMED, decoupled** | `LinkRel` is an existential LinkExact behaviour tied to the arbiter runs only through `T = Rb` and `t0`; its node is not identified with `r_k` in `s` or `sr`. H_ACK_RB, H_ACK_READ, H_SAME_CORNER, H_LUT6_O6 named in the journal |

## Verdicts: cell_constraints.json (rows changed by Bj7 / Bj8, sample of 17)

| row | claim | verdict | evidence |
|---|---|---|---|
| bd_link.stage_rearm (new) | exact for H_REARM alone (exact_scope) | **CONFIRMED** (as a SpecK row) | `exact_rearm`; see the ZeroDelayTok remark: the violation is a late rise w.r.t. SpecK's window |
| bd_arbiter.settled_rise (new) | sufficient; necessary for the q trace only | **CONFIRMED** | `q_glitch`, `q_glitch2`; necessity_scope says exclusion is not shown |
| bd_pipe.rst_lines | relabelled sufficient+necessary_at_boundary; refuted_by b_false | **CONFIRMED** (binary forms) | `rst_sel_boundary`; (c)/(d) event-time only (exactness_note) |
| bd_mux.uj1_env_latency_req_max | boundary-tight, z_ack branch | **CONFIRMED** | `claimY1_false`; form 0 has no run (stated) |
| bdc_muxn.uj_env_latency_req_max | boundary-tight, one point | **CONFIRMED** | `claimN1_false` |
| bd_mux.uxa_join_latency | stays sufficient; boundary_tight_terms S_XA_J.2 | **CONFIRMED** | `claimJ1_false` |
| bd_arbiter.rt1b | c_contract needs_extra_hypothesis; row hypothesis H_SERVER_MIN | status **CONFIRMED**; basis "DERIVABLE as C states it" **OVERSTATED** | as for ArbMultiToken above; the Bsa4 inconsistency (server-free text) is fixed |
| bd_arbiter.rt1 | same c_contract | same | same |
| bd_arbiter.a0_fork_client1 | handover_scope "FIRST HANDOVER: 7j's Scn2 assert the settled state on the whole past" | **OVERSTATED** (basis misattributed) | the row's exact theorems are 7g's `ArbA0Fork.Run` (A0 high from t = 0, one fall, `A 0 = false`), not Scn2; also one handover, for that reason |
| bd_arbiter.server_min | handover_scope (first handover) | **CONFIRMED** | 7h/7j Scn |
| bd_arbcell.handover_overlap | H_ARB_EXCL not_derivable for the bare cell | **CONFIRMED** | `ContractBridge.arb_excl_not_derivable` |
| bd_c2.env_latency | cites `IpowCellsT.gap_exact` as `exact_inner` | **OVERSTATED** (role) | one run family with identical C-element inputs, about C's FbCelT, not an iff over this row's box; the same citation is `context` on bd_c3 / bd_c4 |
| bd_delay[FASTRISE].ack_flush | not necessary for every DACK ≥ 3 | **CONFIRMED** | `SelfAuditB7.flush_not_necessary_all` |
| bd_mux.uj_env_latency_ctl | boundary_point, refuted_by claimC1_false | **CONFIRMED** | Necessity4MuxC |
| bd_steer.bundled_s_setup | "+W under H_W_BOUND" proved for steer | **CONFIRMED** | `SelfAuditB7.steer_win_bound` |
| bd_mux.bundled_s_setup | c_contract H_SEL_STABLE needed | **CONFIRMED** | `sel_glitch_breaks_uj0`; cited `muxJ1_lutFb` has no witness |
| bd_link.stage | one-token iff unchanged, k tokens via stage_rearm | **CONFIRMED** | |

## Mutants (`formal/lean/Wip/Bsa5/`), all FAIL

| mutant | change | result |
|---|---|---|
| M01 ResetWitness2 | F 93 → 92 | FAIL l.172 `w_hold_long`, l.207 `sa0` (semantic) |
| M02 ArbNoWithdraw | steer pulse [1300,1400) → [1300,1401) | FAIL l.256 (semantic) |
| M03 ResetCapstoneMap | hot ack channel 3 → 4 in `μT_ok_b` | FAIL l.64 (kernel decide) |
| M04 Necessity6Mux | `claimY1_false` at slack 0 | FAIL l.292 (structural) |
| M05 Necessity6PipeSel | `a_false` at slack 0 | FAIL l.224 (structural) |
| M06 Necessity6MuxJ | j0 → uxa wire 12 → 11 | FAIL l.215 (hand-built run's H_W0X), l.529 |
| M07 ZeroDelayTok | D 2979 → 2980 (all 16 uses) | FAIL l.570, l.577 (semantic) |
| M08 ZeroDelayNetWit | stage 1 Ra 3400 → 3399 | FAIL l.83 `pw_cell` |
| M09 AssumeGuarantee | `ag_time` with `≤` side condition | FAIL l.56 |
| M10 ArbMultiToken | H_SLOW_REREQ 4M → 3M | FAIL l.724, l.757 |
| M11 ArbSettled | setTbl2 63855 → 63845 fs | FAIL l.828 `set2_cert` (semantic, 10 fs tightness) |
| M12 OnGcdArbKappaSrv | kS2 numerator +1 | FAIL l.749 `cert2` |
| M13 IpowCellsT | `gap_accept` with `d ≤ g + 1` | FAIL l.204 (H_RT_FB) |
| M14 LutFbBridge2 | no select glitch | FAIL l.724 `exG` (structural) |

## Summary

Nothing REFUTED; every file re-checks; generator, map and JSON regenerate byte-identically.
New (Lean): neither end-to-end link theorem (`gcd_hw_safe_phys_links`, `gcd_hw_safe_chains`) has
a joint witness, and `PhysLink` admits only runs in which every link handshakes forever; C's
witness provably violates both H_LINKS. `WireOK` does not pin the channel table. OVERSTATED:
(1) h21_7j_bare's server credit is inert (A0 never moves); (2) LutFbBridge2's witnesses are
fixed-delay, constant-select, two identical join pins, uj1 unwitnessed; (3) "H_ARB_EXCL as C
states it" (journal and two JSON rows): only from B0 in perpetual contention; (4) H_REARM's
"stage breaks": a late edge relative to SpecK (reading); (5) a0_fork rows' handover_scope basis
cites Scn2, the theorems are 7g's; (6) gap_exact as exact_inner on bd_c2.env_latency;
(7) reset_capstone_map_nonvac's B run is the frozen one. Decoupled-trace hypotheses (separate
`sr`, `LinkRel`) are correctly worded in the files but carry less than "discharged" suggests.
