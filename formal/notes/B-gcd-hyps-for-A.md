# For shard A: shard B's rows for `out/gcd_hw_hypotheses.md` (paste block)

Probe Bhyp2, 2026-10-29. The source, with full rows, Lean locations and vacuity notes, is
`formal/notes/B-hypotheses.md`. The text between the two rules below is meant to be pasted as a
new section, "Shard B's cell hypotheses". The corrections after it are for the existing sections.

---

### Shard B's cell hypotheses (B ledger BH1-BH26, 2026-10-29)

**Where they enter.**
- The capstone chain imports one B module, `Cells/LinkHandshake`, and from it uses one
  definition, `ctlB`, inside `Link.H_CEL_SI`. The chain is the import closure of `CapstoneWalk`,
  `CapstoneLiveNdWalk`, `CapstoneRig` and `CapstoneWitness3`: 69 modules.
- So no B hypothesis is a Lean hypothesis of `gcd_hw_circuit_safe3`, `gcd_rig_first` or
  `gcd_hw_live_final`.
- B's rows are the physical premises for C's `H_CELLS`, `H_BUNDLE`, `H_ENV` and init fields,
  through four unmechanised bridges:
  - **Br1** (O4): the OpsGen bindings, not instantiated, with premise `LutFb`/`LutSI`, which no
    B theorem derives;
  - **Br2** (8x): physical → zero-delay traces. `Held` and the `dat`/`H_LATCH_*` fields live on
    the zero-delay traces (8w);
  - **Br3** (M6): SI discretisation;
  - **Br4**: gNet reset → the Ops initial state (probe Brz).
- The one exception is `Cells/RigSrc.lean:500 gcd_rig_first_env`: C's `gcd_rig_first` with
  `H_ENV` and the sources' `SrcR` proved from the rig's env cells. Its binders (BH24) are Lean
  hypotheses of a capstone-chain theorem. **It has no joint non-vacuity witness yet.**

**Update 2026-10-31 (shard B): the gate-level network theorem, driver-bound, with a joint
witness.** `Cells/FiniteNetBound.lean:gcd_hw_safe_fin_netB` is C's gcd_hw safety (every out0
token carries gcd a b) with the `H_CELLS` of all 175 LINKS discharged by one gate-level network
of B's cell models (`FGcdNetOKB`), whose tied cells' pin drivers are bound to the cells the
netlist names (63 links bound on both sides, 64 request side only, 23 acknowledge side only, 25
neither: `bound_census`). Its hypotheses: `FGcdNetOKB` (B's gate models, wires, edge-time
bounds, finite edge counts, truncated contracts on untied cells), C's `H_CELLS` for the other
192 operators (`H_OTHER`), H_BUNDLE, H_CM_FORCED. Joint witness:
`Cells/BWitNet.lean:gcd_hw_fin_netB_witness` (a = 12, b = 18, a gate-timed run in which B's tied
cells drive each other; unit LUT delays, wire delays 1-3, one run). It replaces, for links, the
chain/elaboration theorems that the audit (P12b) found did not bind drivers. Suggested row:
"H_CELLS (links) <- FGcdNetOKB: B gate models of links/forks N<=4/2-joins/steers/ORs with
netlist-bound drivers; grade B (model), witness: one gate-timed run; test: routed GLS of the
same cells with per-arc bands".


| B id | hypothesis (Lean) | plain statement | grade | status | test | chain? |
|---|---|---|---|---|---|---|
| BH1 | INIT = function: `LinkHandshake:65 ctlB`, `OpsGen:397 link_gate`, Gen | LUT output = INIT of its physical pins | A cell / B whole bits | `ctlB` discharged (kernel decide) | `formal/tools/gen/gen.sh --check`; extend `fasm2lean2/check.sh` to gcd_hw | chain |
| BH2 | H_KLEENE_LUT (`Core/LutTree:279 H_mux_kleene`) | mid-rail select, equal legs ⇒ output = legs | B (audit row 88: optimistic) | open | board glitch counter | side (reset certs, KleeneBox, Fd); Br1/Br3 only as hazard freedom |
| BH3 | H_NO_REVERT (`WinFifoCausal:64 NoRevertI`), H_LUT/PIN/TREE/WIRE_FIFO, monotone read maps | one input edge ⇒ one output edge; pins and wires keep order | B; not from `Win` (`WinFifo:151`), not from H_KLEENE_LUT (`NoRevert:561 kleene_revert`) | open | LUT-ring edge count; GLS `GLS_MODEL=fid` edges per edge | **R' binders** (β, γ, φ monotone); Br1/Br3 |
| BH4 | H_LUT62_SHARED_READ (`TernaryOnBits2:325 SiteSync`) | O5 and O6 read a shared pin together | B | open | CARRY4 TDC O5/O6 skew | Br1 (steer, arbiter) |
| BH5 | select X window `wa` (`CElemStrict:288`), **H_X_UNIFORM** (KleeneBox) | a moving select is X for `w ≥ 1` tick, the same `w` on every edge | B (exists) / C (uniform) | open; no gcd_hw verdict depends on it | TDC on a select ramp | side |
| BH6 | H_FB_FIRST (`OpsGen:95 FbFirst`), H_ENV_LATENCY (`CElemStrict:288`), H_SEL_ORDER (`ConstraintsSel:237`) | own feedback reaches the select before any provoked response | B kernel; **C at rig uenv1** (−117/−221, −86/−243 ps, seeds 2/4, band) | kernel: tcheck Rc per route (`fbFirst_of_resp`, H_RESP_ONLY prose) | `formal/tools/tcheck/run10k.sh d 2 3 4`; rig GLS seeds 2/4 fast: one `start_req`↑ per `res_req`↑ | Br1; **R' (`H_UENV1_B`, `M1`)** |
| BH7 | H_CTREE_ATOMIC (C, prose) ⇐ H_CTREE_LOOP (`CTreeExact:969 tree_box_exact`) | each tree node's loop fits the root's environment latency | B | exact in Lean; **no route row** | new tcheck row per `bd_ctree` node | Br1 (forks N ≥ 3, joins N ≥ 4) |
| BH8 | latch L1-L3, H_FORK_DATA_W (`ForkData:140, :235`), `Bundling:601 capture` | data before the enable closes; enable pulse; hold | B | I 300/300, H 630/632, W +346 ps; rule I lacks the I2 arc | `run10k.sh` I/H/W (+ I2 arc) | Br2 (not `Held` directly) |
| BH9 | reset: `CElemStrict2:510 reset_width_iff`, `ResetGcdWave:447/694/726` | rst held long enough; final before the loop (`W < 34` steps) | B | proved in gNet only; not linked (Br4) | SDF: max rst-pin delay < 34 fast-min steps | Br4; R' (`H_REL`) |
| BH10 | steer select (`LibGapSteer:188 steer_box_exact`) | `S0 + Shi ≤ R + Rlo`, `F + Rhi ≤ S1 + Slo` | B | setup rule E 465/472 (no site pins); **hold: no rule** | `skew.py` with FASM site pins; a steer-hold row | Br1/Br2 |
| BH11 | mux select + ctl_req fork (`LibGapMux:393 join_box_exact`; `Mux.cj0/cj1`) | `s` settled at uj0/uj1 before `ctl_req` and held past it; fork isochronic | **C pending** | rule K FAILS 16-26/42 per seed, unguarded too (10l WIP) | `run10l.sh`; GLS monitor at `umux*.uj0/uj1` | Br1 |
| BH12 | muxn select (`LibGapMuxN:324 join_exact_fixed`), H_YOSYS_MAP | index settled at the decode pins | B | **no rule-E row for `umux21`** (8w) | add `umux21` to rule E | Br1 |
| BH13 | RTZ (`MuxRtzTimed:113 rtz_safe`; `Mux.xa/ya`, `AMerge.H_AMERGE_RTZ`) | previous acks low before the next z_ack↑ / z_req↑ | B | X/Xi 0 unguarded fails; Z all pass (+383); Xc/Xm 1-2 band fails | `run10k.sh` X/Z; `run10l.sh` Xc/Xic/Xm | Br1 |
| BH14 | amerge index (`ForkData:360/:384`) | `won` settled before the consumer closes | B | Z passes; `acc251` and `idx_ack_fork` have no row | new row for `acc251` | Br2 |
| BH15 | H_GFLUSH, H_LO_ORDER (`GcdCells:151 no_early`; `LibGapDelay:490`) | gated line flushed before the next token | B / **C band** (cm12 −343/−522, ushrsi3 −160) | Fd 29/29 unguarded; H_LO_ORDER unchecked | `run10k.sh` Fd; per-route H_LO_ORDER row | Br1/Br2 |
| BH16 | FASTFALL/FASTRISE flush (`Bundling:366 slow_not_early`) | link lines flushed | B | rule F lacks the in-flight term; FASTRISE unchecked | rule F'; FASTRISE row | Br1 |
| BH17 | H_A0_FORK (`ArbA0Fork:258`; `OnGcdArbA0:175/195`, `:2963 gcd_corner_srv`) | A0↓ reaches ua_k before A0 → q → g_k | B one corner / **C box, κ > 16587/374773** | proved per corner on 36 routed arbiters; box `okSrv` 20/36; κ: `OnGcdArbKappa:3052` | `arb_fork.py` with site pins (J'); T5; κ on the A0 tails | Br1 (`H_ARB_EXCL`, `H_ARB1/2`) |
| BH18 | RT1/RT1b (`OnGcdArbFix:1080/1088`) | no grant overlap across a handover | A one corner / C box | proved, 36 × 4 × 2, every server | T5 | Br1 (`H_ARB_EXCL`) |
| BH19 | RT2/RT2b + server bound (`OnGcdArbA0:437`; `srv ≤ D.smin`) | ack exclusion; server not faster than `srv` | B | 144/144 with `srv`; `srv` unchecked on routes | routed ustate O5 → A0 path vs `srv`; T5 | Br1 |
| BH20 | no free contest (R2-R4) | the arbiter never resolves a tie | A in model | **discharged** (`gcd_hw_arbiters_uncontended3`, `gcd_hw_never_contested`); does NOT discharge `H_ARB_EXCL` | board contested-grant count; `cells/hw/arb_mtbf.v` | chain (U); L's `H_ARB_UNCONTESTED_BOUNDED` |
| BH21 | H_SHARED_CORNER, H_SCATTER κ (`Core/Substrate/CornerNat:21-23,118`); `ConstraintsKappa:310/450/458/470` | one die corner; each arc within `1 ± κ` | B form / **C value** (κ unmeasured) | box, one-corner and SLOW-only checks unsound for κ > 0 | T1 (on-die two-path) | under every numeric verdict |
| BH22 | site pins (`Rd` maps; PinAssign) | each physical pin adds its own delay (≤ ~0.5 ns) | A (fact) | tcheck/Bar use them; rules J/E do not | LOCK_PINS or a FASM site-pin table | every numeric row |
| BH23 | H_RF_ASYM | rise = fall per corner column | B | unmeasured | CARRY4 TDC | every numeric row |
| BH24 | `gcd_rig_first_env` binders: `H_FORK_WIRE`, `H_DAT`, `H_REL`, `H_REL0`, `H_OUT0_ACK`, `H_UENV1_B`, `H_C3`, `M1`, `M0`, monotone maps | the env ring (uenv0, uenv1, ufork c3) obeys its cells' step forms; buses constant | B; **C for uenv1's `H_UENV1_B`/`M1`** | open; **no joint witness**; laps ≥ 2 open; H_SINK_SI prose only | rig GLS seeds 2/4; board #1 `cells/hw/board.sh python3 cells/hw/gcd_measure.py` | **R' (Lean binders)** |
| BH25 | rig idx setup / verdict (`RigIdx:314`, `RigContract:425`) | operands settle before F opens; verdict fresh | B | open on routes | SDF idx → d vs 16 hk periods | side |
| BH26 | contract route (`Contracts.net_refines_ports`) | — | B | not applied to gcd_hw | — | side |

---

### Corrections to the current `out/gcd_hw_hypotheses.md` (2026-10-27 11:00 text)

1. **§0.1/§0.2.** The best statements are now:
   - `CapstoneWalk.lean:636 gcd_hw_circuit_safe3` (H_WALK proved; witness `gcd_hw_joint_witness3`);
   - `CapstoneRig.lean:267 gcd_rig_first` and B's `RigSrc.lean:500 gcd_rig_first_env` (first rig
     result, no H_START_ONCE);
   - `CapstoneLiveNdWalk.lean:120 gcd_hw_live_final` (H_NO_DEADLOCK' open, no joint witness).
2. **§1 tree and §3 header ("H_BUNDLE ⇐ rules …").** Per C-8w (`CapstoneBundle.lean` header),
   tcheck cannot discharge `Held` on the capstone's zero-delay traces. Write "⇐ (via the 8x
   physical → zero-delay refinement, unmechanised) rules …".
3. **§2.2 H_FB_FIRST.** Replace "this hits H_START_ONCE's realisation, not H_CELLS" with: "at the
   rig it is the Lean binders `H_UENV1_B`/`M1` of `gcd_rig_first_env` (grade C)".
4. **§2.3 contention row.** Add: "contest-freedom discharges only the tie and metastability tier.
   `H_ARB_EXCL` still rests on BH17-BH19:
   - they are proved per corner on the routed numbers (OnGcdArbFix, OnGcdArbA0 `gcd_corner_srv`);
   - they are C in the box and for κ > 16587/374773."
5. **§2.6 H_START_ONCE.** Replace "not modelled / model the env ring (~0.5 d)" with "the first
   result is covered without it (`gcd_rig_first`, `gcd_rig_first_env`). Laps ≥ 2 are open (C:
   `rearm_fails_at_reoffer`; probe Blap)".
6. **§0.3 item 7, §3 last row, §8 row 48.** RigContract compiles (fixed 807448a, Bsa).
7. **§3 rows.**
   - Rule K: unguarded failures too, not band-only.
   - `umux21` has no rule-E row (8w).
   - C-tree depth: B's exact condition is H_CTREE_LOOP (`CTreeExact.tree_box_exact`); it is
     still unchecked.
   - The drain row: cite Fd, not F (C-10k: F is not sufficient).
8. **§5 S3.** H_LUT_FIFO / NoOvertake = `Win` + H_NO_REVERT. H_NO_REVERT is not implied by
   H_KLEENE_LUT (`NoRevert.kleene_revert`), so S1's glitch counter does not test it. Add a
   LUT-ring edge count.
9. **§5 S4.** Add "H_X_UNIFORM (KleeneBox): with a uniform X width `w` every setup and hold gains
   `+w`. Uniformity is graded C (unmeasured). No gcd_hw verdict depends on it."
10. **§5 D11/D12.** Add: "the box, one-corner and SLOW-only checks are unsound for κ > 0
    (`ConstraintsKappa:450/458/470`). The gcd_hw arbiters are safe for κ ≤ 16587/374773
    (`OnGcdArbKappa:3052`, lit reading). 'tight' is withdrawn (audit row 19)."
