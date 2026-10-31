# gcd_hw: the end-to-end statement and every hypothesis under it

Shard A (probe FeasDraft), refreshed 2026-10-29 ~09:00 UTC from:
- `notes/B-gcd-hyps-for-A.md` and `notes/B-hypotheses.md` (Bhyp2: B ledger BH1-BH26, with
  contradictions K1-K16);
- JOURNAL-B's 2026-10-29 entries after Bhyp2 (Bfb, Bzd, Brz, Bsa3, Bjw, Blap, Bbr, Bkx19, Bsrv,
  Bfb2, Bsa4);
- `notes/C-gcd_hw-hypotheses.md` §0 (C-aud2, rebuilt against the Lean on 2026-10-29) and
  JOURNAL-C;
- the audit REPORT.md at `origin/claude/audit` `83b1290`.

It replaces the 2026-10-27 11:00 text, which predated 8s, 8t, 8z and B's bridges. How to read
it:
- The full rows, with Lean line numbers and vacuity notes, are in the two shard ledgers. This
  file is the short index across them.
- **No Lean was run for this file.** The theorem names were checked by grep, and four statements
  were read in the Lean: `gcd_hw_circuit_safe3`, `gcd_hw_live_final`, `gcd_hw_safe_phys_links`
  and `gcd_hw_joint_witness3`.
- Grades: **A** = proved in Lean, true by construction, or measured in the repo. **B** = credible
  and physically motivated, but untested on this silicon. **C** = doubtful, contradicted by
  evidence, or failing on some route, corner or reading.

## 0. The statements

| theorem (file) | says | hypotheses | non-vacuity |
|---|---|---|---|
| **`gcd_hw_circuit_safe3`** (`Net/CapstoneWalk.lean:636`) | For a, b < 2^31, every value latched on out0 of bdc's concrete 465-channel / 367-operator gcd_hw network is `Nat.gcd a b`, and the closed list is `gcd a b` repeated | H_CELLS, H_BUNDLE, H_START_ONCE (H_WALK is proved: `gcd_hw_walk` :627) | `gcd_hw_joint_witness3` (`Net/CapstoneWitness3.lean:15`): one run, a=12, b=18, unit delays, zero-delay buses, sources offer once, latches 6 (audit `299a16f` CONFIRMED) |
| `gcd_rig_first` (`Net/CapstoneRig.lean:267`); B's `gcd_rig_first_env` (`Cells/RigSrc.lean:500`) | The rig re-offers start; the FIRST out0 result is `gcd a b` | CellR, H_BUNDLE, H_ENV; the `_env` form proves H_ENV and the sources from the env cells, under the BH24 binders | `gcd_rig_first_env`: `SelfAuditB6.rig_env_feeds` (degenerate delays), `RigSrcWitness.gcd_rig_first_env_joint` (lagging read maps). `gcd_rig_first`: none |
| B's `gcd_rig_every` (`Cells/RigLaps.lean`) | EVERY out0 result of the rig is `gcd a b` | LapInv at release and after every close (+ H_BUNDLE, H_ENV) | none. `lap_cut_fails`: LapInv fails at a close when the p_end loop beats out0's return (H_PEND_FAST, expected on silicon); C's `rearm_fails_at_reoffer` refutes re-arming |
| `gcd_hw_live_final` (`Net/CapstoneLiveNdWalk.lean:120`) | The first out0 token closes within (1168(8 Lrun+23)+1)(H+1) ticks, carrying `gcd a b` | H_CELLS (CellI), H_BUNDLE, H_START_ONCE, H_BOUNDED_DELAY', H_START_ENV, H_ARB_UNCONTESTED_BOUNDED, **H_NO_DEADLOCK' (open)** | none: the 8t run violates H_BOUNDED_DELAY' (audit `fccbd1b`) |
| B's `gcd_hw_safe_phys_links` (`Cells/LutFbBridge2Env.lean:436`) | As 8m's `gcd_hw_circuit_safe`, with H_CELLS for the 175 links replaced by B's physical link model | PhysLink per link (each link's Env1 assumed), H_CELLS for the other operators, H_BUNDLE, **H_CM_FORCED** | none stated |
| B's `gcd_hw_safe_after_reset` (`Cells/ResetCapstone.lean`) | B's GMW reset + C's safety: every out0 latch is gcd from T0 = 23(D+W+1) | H_MAP (channel → gNet node map, no mechanised table; MapOK too weak, Bsa4), H_CELLS_AFTER (assumed), H_START_AFTER, C's bundling | the joint witness is frozen (vacuous conclusion); `nonvac_net2` is frozen until E (Bsa4) |
| A's `design_verdict8` (`Core/XAudit/Events8Beh.lean:79`) | The routed control skeleton (4 seeds) is CLEAN at the slow and fast corners | SatPin, constant wires and reset, HARB7, SelOK, SelPart, HDsub (HDsub discharged by Events9; **HARB7 false on real uncontested runs, so the verdict currently covers no real run**: `Events8Arb.unc_not_harb`) | audit `eb346fb`: CONFIRMED conditional; Lean certificates UNVERIFIED |

**Do not cite:**
- `Capstone.gcd_hw_conditional` / `latched_const`: no gcd content (audit `eecc6f7`);
- 8u's `gcd_hw_live`: likely vacuous (`start_never_closes`);
- `gcd_circuit` on the hand-drawn loop: vacuous for a ≠ 0.

**Not covered by any of them:**
- inputs outside [0, 2^31);
- laps after the first (except `gcd_rig_every`, which has no witness);
- the rig's result capture;
- the data-path functions (H_COMPUTE_FN) -- now proved by C for all 20 units (2026-10-31), but not yet a hypothesis discharged inside these theorems (H_MAP, constants open);
- metastability (contest-freedom is proved in the model: `gcd_hw_never_contested`,
  `gcd_hw_arbiters_uncontended3`).

## 1. Where the hypotheses sit

- **B's hypotheses are not Lean hypotheses of the capstone.** No B cell hypothesis is a Lean
  hypothesis of `gcd_hw_circuit_safe3`, `gcd_rig_first` or `gcd_hw_live_final`. Their import
  closure (69 modules) uses one B definition, `ctlB` (Bhyp2).
- **The one exception** is `gcd_rig_first_env`, whose env binders (BH24) are real hypotheses.
- **Everything else** reaches the capstone only through four bridges. Their status today:

| bridge | from → to | status |
|---|---|---|
| Br1 / O4 | B's physical cell models → C's H_CELLS fields (OpsGen `LutFb`/`LutSI`) | **Proved per cell kind:** link bd_c2n, every bd_c2 in OpsGen, bd_c3, mux uj0/uj1, LutSI for steer/src (LutFbBridge, LutFbBridge2; needs H_NO_REVERT, H_LUT_POS, H_PWR, H_SEL_STABLE); H_CTREE_ATOMIC, H_SEL_PIN, ungated H_DELAY_LUMPED (ContractBridge). **Not composed** into `gcd_hw_circuit_safe3`: only the links (`gcd_hw_safe_phys_links`, Env1 assumed). **Not derivable as stated:** H_ARB_EXCL (`arb_excl_not_derivable`) |
| Br2 / 8x | physical traces → the zero-delay traces of H_CELLS/H_BUNDLE | **Cell half, one token:** `ZeroDelayRefine` (link exact iff its six rows; steer/mux). **Network half and multi-token: open** (C-8x running). Until then no tcheck verdict discharges `Held` (C-8w) |
| Br3 / M6 | SI discretisation (no two causally linked edges in one tick) | open; `Core/Discretize` and `Net/Bridge` give the pieces, not applied to this network |
| Br4 | gNet reset → the Ops initial state | `ResetCapstone` (3-tick virtual glue). The RTL never reaches C's all-idle state (`rtl_not_idle`, for T0 in [23(D+W+1), E] with rst held). H_MAP and H_CELLS_AFTER open |

## 2. Every hypothesis

"Used by" names the theorem whose statement or bridge carries it.

| hypothesis | plain statement | grade | used by | status / evidence | test that would settle it |
|---|---|---|---|---|---|
| range | a, b < 2^31 | A (precondition) | all | outside it, `gcdC` returns on some negative pairs and loops on others; no theorem either way | none needed |
| **H_CELLS** | each of the 367 operators meets its unit-time Ops gate model (SI/DI step relations, zero-delay data, ideal link latch, all channels idle at 0) | **C** as a whole (zero-delay data and latch); B for control | safe3, live_final, (CellR) rig_first | per cell kind via Br1; not composed (except the links) | routed GLS, 4 seeds, both corners, `GLS_MODEL=fid`; tcheck rows below |
| **H_BUNDLE** (`Held`) | every channel's bus is stable through each transaction, on the zero-delay traces | **C** until Br2 | safe3, rig_first, live_final | physical-bus form proved (`held_of_tx`/`held_of_cert` under TxCover); tcheck rows A/E/I/H/W (1212 Ops obligations, 4500/4572 rows matched by hand, 8w) | tcheck on the 4 routes; routed GLS |
| **H_START_ONCE** | start is requested at most once | **C** for the rig (false by design: it re-offers start), A for a one-shot harness | safe3, live_final | necessary with the free-running source (8r, argued) | rig GLS: start_req rises per res_req |
| H_ENV / BH24 binders (H_FORK_WIRE, H_DAT, H_REL, H_REL0, H_OUT0_ACK, H_UENV1_B, H_C3, M0, M1, monotone read maps) | the env ring (uenv0, uenv1, ufork c3) obeys its cells' step forms; buses constant | B; **C for uenv1's H_UENV1_B/M1** (RT_FB fails under the band, seeds 2/4) | rig_first(_env) | joint witnesses for the `_env` form (above). H_SINK_SI proved with a FIFO read map (`sink_si`) | rig GLS seeds 2/4 fast; board #1 |
| LapInv / H_KER_REARM | the cell models hold again on the run shifted to each close | **C** (`lap_cut_fails` under H_PEND_FAST) | rig_every | open; needs a re-entrant window theorem (C) | — (proof obligation) |
| H_BOUNDED_DELAY', H_START_ENV | every non-start gate settles within H once excited; start is offered within H | B | live_final | no witness | GLS max settle time per gate; STA max arcs |
| H_ARB_UNCONTESTED_BOUNDED | uncontested grants settle within H | B | live_final | contest never occurs in the model (`gcd_hw_never_contested`) | board: count contested grants (expect 0) |
| **H_NO_DEADLOCK'** | no quiet state before out0's first close | open proof obligation | live_final | 56 random-delay simulations, no deadlock (evidence only); C-8z2 running | prove it |
| H_CM_FORCED | each arbiter stage's winner is the token run's label | A (proved from H_CELLS + H_BUNDLE + H_START_ONCE: `gcd_hw_forced3`) | safe_phys_links (as a binder) | proved, but only with H_CELLS for all operators | — |
| H_MAP, H_CELLS_AFTER | C channels ↔ gNet nodes; cell models after release | B / open | safe_after_reset | no table; MapOK admits a non-wiring map (Bsa4) | Lean: a wiring table from the yosys JSON |
| HARB7, SelOK, SelPart, HDsub; SatPin, constant wires, reset | A's event checker's premises | **HARB7: C (refuted in its current encoding, 2026-10-29: `Events8Arb.unc_not_harb` -- an uncontested real bd_arbiter run with exclusive grants that the virtual core cannot match; fix in progress, E8ArbFix)**; HDsub: discharged (`Events9.design_verdict9`); others B | design_verdict8 | E8Hyp (unclaimed): SelOK bridged from B's `LibGapSteer.steer_pin_ok`; SatPin + constants + reset jointly satisfiable iff a reset fixpoint exists (one exists on all 4 seeds, untrusted script). HDsub = 126 count judgements (2 per guarded pin) | finish W-E4g (HDsub); GLS |
| ArbEdge (2026-10-31: replaces HARB7/HARB7' and HRst in `Events9FullArb.design_verdict9_full_arb`): QClean, quiet start to T0, settle bound H, per-reader edge windows; plus the checked ArbRowsOK | the arbiter's q makes clean transitions (no metastable runt); requests quiet until T0; each A0-low phase ends within H; no re-request while the arbiter switches away; reads settle in the B2 windows; A0 high around each request fall | **C** as a whole: ArbRowsOK (checked) FAILS on 2-9 of 9 arbiters per gcd_hw row (B1, the real grant can fall via q; an abstraction limit); QClean and H are the no-metastability / uncontested-schedule hypotheses | design_verdict9_full_arb, design_verdict9arbnet_ord (with ArbOrd in place of the B1 rows: 10 of 16 gcd_hw rows meet every checked premise) | xarbnet on 16 rebuilt rows (`tools-A/xaudit/arbnet/results/rows_table_1031.txt`) | QClean: GLS/board runt counter on q; H: max A0-low phase in GLS |
| ArbOrd (2026-10-31; as first stated it could not be discharged at B1-failing readers: it constrained the classically chosen SatPin warps, audit P15a. Since SatPinW (same day) it is a condition on the behaviour the user supplies; `arbOrd_of_transport`: for fixed per-pin delays it follows from four path-delay rows per arbiter. It is still NOT true for every behaviour in the bands) | at each arbiter reader, ustate's request read at the reader's q-read time is no later than the reader's own request read 2 ps earlier | B: automatic where the band row holds (`ord_of_row`); at the B1-failing readers it needs the in-corner spread to be shared and path scatter κ ≤ ~0.047 (`corner_ord`; numbers untrusted). Holds with the GLS's SDF delays on 4 seeds (≥ 278 ps over 72 reader pairs incl. R0); FAILS under GLS scatter in 3 of 5 draws (σ 0.05: -12 ps; σ 0.10: -410/-346 ps, R0 reader) while every one of those runs computes all 16 vectors, so it is stricter than the circuit needs | design_verdict9arbnet_ord | T1 (on-die differential two-path, κ); a GLS/board check that the grant's request pin is not >50 ps slower than ustate's request + q path |
| QQuiet after S (2026-10-31; replaces QClean in `design_verdict9arbnet_ordS`) and q settled on (S - phi PqQ, S] | after reset, each change of an arbiter's state q is followed by one q-loop delay with no change of ustate's request/reset/A0 reads | B: corrected GLS monitors (audit P15a fixed; `formal/tools-A/xaudit/glsq/out2/`): 0 violations after reset on all 4 gcd_hw seeds and in 5 scatter draws (σ 0.05/0.10), ~20k q flips each; violations only during power-up; GLS at 520a43f, window = GLS loop delay, not phi; false during power-up while rst is high, hence 'after S' | design_verdict9arbnet_ordS | `formal/tools-A/xaudit/glsq` monitors; board: a contested-grant counter |
| **H_FB_FIRST** (BH6: H_ENV_LATENCY, H_SEL_ORDER) | own feedback reaches the select before any provoked response | B kernel; **C at rig uenv1** | Br1 | tcheck Rc passes on every kernel C-element per route. uenv1 band FAIL: C-10h (`aa5919c`) seed 2 −117/−221, seed 4 −86/−243 ps; audit (`83b1290`, row `1e7947a`) −114/−219, −81/−201. Bare Muller rings fail (C-10f) | `formal/tools/tcheck/run10k.sh d 2 3 4`; T2 board/GLS |
| H_NO_REVERT + H_LUT/PIN/TREE/WIRE_FIFO (BH3) | one input edge gives at most one output edge; pins and wires keep order | B; not implied by `Win` or by H_KLEENE_LUT (`NoRevert.kleene_revert`) | Br1, Br3, R' binders | open; without it both LutFb premises fail (LutFbBridge counter-runs) | LUT-ring edge count; fid GLS edges per edge |
| H_KLEENE_LUT (BH2) | a mid-rail select with equal legs passes the legs | B (optimistic: the hazard-free extension, audit `abe7d25`) | reset certs, Fd, H_CLEAN_EDGE | `KleenePess`: safety/exclusion results do not need it; definite-output (hold, restore, reset) results need pass(v) instead | board glitch counter / runt-flag pass matrix (6 pins × 2 values) |
| X windows (BH5: H_X_UNIFORM, H_FB_WIN) | a moving input is X for a window | B (exists) / C (uniform, unmeasured) | side | `KleeneWin` drops H_X_UNIFORM (per-edge windows, exact); no gcd_hw verdict depends on it | XW-1: MMCM-swept bd_c2 race |
| H_LUT62_SHARED_READ (BH4) | O5 and O6 read a shared pin together | B | Br1 (steer, arbiter) | open | CARRY4 TDC O5/O6 skew |
| H_CTREE_ATOMIC ⇐ H_CTREE_LOOP (BH7) | each tree node's loop fits the root's environment latency | B | Br1 (forks N ≥ 3, joins N ≥ 4) | exact in Lean (`tree_box_exact`); **no route row** | new tcheck row per bd_ctree node |
| latch L1-L3 (BH8) | data before the enable closes; enable pulse; hold | B | Br2 | tcheck I 300/300, H 630/632, W min +346 ps; rule I lacks the I2 feedback-pin arc (audit CONFIRMED, guard covers it) | `run10k.sh` I/H/W + I2 arc |
| steer select (BH10) | select set up before and held after the request | B | Br1/Br2 | setup rule E 465/472 (band-only); **hold: no rule** | skew.py with FASM site pins; a steer-hold row |
| mux select + ctl_req fork (BH11) | `s` settled at uj0/uj1 before ctl_req and held past it; fork isochronic | **C pending** | Br1 | rule K FAILS 16-26 of 42 rows per route, unguarded too (10l WIP; C-10l2 running) | `run10l.sh`; GLS monitor at `umux*.uj0/uj1` |
| muxn select (BH12) | index settled at the decode pins | B | Br1 | **no rule-E row for `umux21`** (8w) | add `umux21` to rule E |
| RTZ (BH13; H_AMERGE_RTZ, Mux xa/ya) | previous acks low before the next z_ack↑ / z_req↑ | B | Br1 | X/Xi 0 unguarded fails; Z all pass (worst +383 ps); Xc/Xm 1-2 band fails | `run10k.sh` X/Z; `run10l.sh` |
| amerge index (BH14) | `won` settled before the consumer closes | B | Br2 | Z passes; `acc251` and `idx_ack_fork` have no row | new row for `acc251` |
| H_GFLUSH, H_LO_ORDER (BH15) | gated delay line flushed before the next token | B; **C under the band** (cm12 −343/−522, ushrsi3 −160 ps) | Br1/Br2 | Fd 29/29 unguarded (cite Fd, not F); H_LO_ORDER unchecked | `run10k.sh` Fd |
| FASTFALL/FASTRISE flush (BH16) | link delay lines flushed | B | Br1 | rule F lacks the in-flight term (audit CONFIRMED; the guard does not cover it); FASTRISE unchecked | rule F'; FASTRISE row |
| **H_ARB_EXCL** ⇐ H_A0_FORK, RT1/RT1b, RT2/RT2b + server (BH17-19) | never both grants; A0↓ reaches ua_k first; ack exclusion; server not faster than `srv` | B per corner; **C in the box**; κ: see next row | H_CELLS (AMerge) | proved per corner on 36 routed arbiters (OnGcdArbFix, `OnGcdArbA0.gcd_corner_srv`); box `okSrv` 20/36; NOT derivable from B's per-pin arbiter as stated (`arb_excl_not_derivable`: holds per arbitration inside QUIET/COMMIT only); `srv` unchecked on routes; arc data provenance UNVERIFIED (audit `7c4df29`) | `arb_fork.py` with site pins (rule J'); T5 |
| corner model: H_SHARED_CORNER, H_SCATTER κ (BH21), H_SPREAD_CORRELATED | one die corner; each arc within 1 ± κ | B form / **C value** (κ unmeasured) | every numeric verdict | gcd_hw arbiters: 0.0443 (16587/374773) is the server-free arc form, tight on the 1 fs grid (`OnGcdArbKappaTight`), not a gate-level threshold; server-credited (`OnGcdArbKappaSrv`): D1 bare cell 0.0802 (needs a non-four-phase withdrawal), D2 held four-phase 0.2166; which applies is open. The cons reading fails at κ = 0 on two rows. H_SPREAD_CORRELATED is the lit model renamed (Bsa4). Box, one-corner and SLOW-only checks are unsound for κ > 0 (`ConstraintsKappa`; SLOW-only even at κ = 0, audit) | T1: on-die differential two-path (A-kappa) |
| site pins (BH22) | each physical pin adds its own delay (≤ ~0.5 ns) | A (fact) | every numeric row | tcheck and Bar use them; rules J/E do not (audit CONFIRMED) | LOCK_PINS or a FASM site-pin table |
| H_RF_ASYM (BH23) | rise = fall per corner column | B | every numeric row | unmeasured; prjxray has no rise/fall split | CARRY4 TDC |
| tcheck model (H_NETLIST, H_ONE_CORNER + band, H_RC_EXACT, H_FALLBACK_BAND, run semantics; rule shapes incl. H_CLEAN_EDGE) | the routed netlist and its RC delays are as extracted | B (H_FALLBACK_BAND C; H_CLEAN_EDGE C at LUT outputs) | every tcheck row | core proved (`pot_sound`, `verdict_sound`); front end untrusted Python. OUTMUX/xMUX driver hop in `extract.py` since C-10h; 10m's cross-check and rerun pending | `formal/tools/prjxdelay/run.sh`; 10m |
| H_COMPUTE_FN | the yosys fused-unit netlists compute bdc's expressions | **A for the function** (C-hcf, 2026-10-31: all 20 gcd_hw units proved for every input on the committed synthesis, identical on all 4 routed seeds; `GcdJoin.j2..j162`: each of the capstone's 20 join functions `jg e js` equals its unit's function on bdc's port wiring; ranges: 32-bit tokens for uselect0, shift < 32 for ushli0, shift = 1 for the ushrsi units as gcd_hw feeds them) | `Join.dat` | still assumed: H_MAP (which unit is which join), the constant ports' values, primitive Boolean models; timing is H_COMPUTE_DELAY (rule A) | C's negative controls (one-bit INIT mutations falsify the certificates) |
| H_GHOST, H_FOLD | real index/control buses are images of the model's ghost buses; zero-delay reshapes fold | B (prose) | H_CELLS | no theorem maps a real run to the ghost run | Lean (modelling) |
| rig idx setup / verdict (BH25) | operands settle before F opens; verdict fresh | B | side (rig) | open on routes; RigContract compiles (audit `807448a`), its claims conditional on H_RESULT_FRESH | SDF idx → d vs 16 hk periods |

## 3. The model is the circuit (steps outside Lean)

| # | step | grade | evidence | test |
|---|---|---|---|---|
| M1 | GcdHw graph = bdc's graph | A while the drift check passes | audit: re-export byte-identical | `formal/tools/dfimport/check.sh --lean` |
| M2 | CapstoneNet = that graph + bdc's link placement | A | `OpChk` kernel check; `formal/tools/capnet` regenerates byte-identical (audit `8965ea0`) | capnet regeneration |
| M3 | bdc's Verilog implements the graph | B | no structural diff | structural diff of `bdc_gcd` vs `GcdHw.rules` |
| M4 | synthesized cells = RTL cells | A per cell | Gen, 36 modules (audit: 76 constants, 0 mismatches) | `formal/tools/gen/gen.sh --check` |
| M5 | routed bits = synthesized netlist | B | fasm2lean for link + arbiter (4 seeds); research fasm2net 11619/11619 LUTs on a gcd_hw route, 3 harmless A6 ties (audit `4a44aef`); 11f (whole design) running | extend fasm2lean2 to gcd_hw |
| M6 | SI discretisation | B (Br3) | pieces only | GLS gap histogram per excitation |
| M7 | omitted source chains (4 bd_src + their link stages) don't matter for safety | B (prose) | C-8m | Lean: add them as Src + Link operators |

## 4. Tests, cheapest first

1. **Board #1** (`research/BOARD-QUEUE.md` §1): `hw/board.sh python3 hw/gcd_measure.py`, which
   expects 16/16 vectors and `err_sticky=0`. It is end-to-end and cannot separate rows. It also
   exercises laps the theorems do not cover.
2. **Routed GLS with monitors** on seeds d, 2, 3, 4, both corners, `GLS_MODEL=fid`. Monitors:
   - start_req per res_req;
   - ctl_req ended at `uj0/uj1` before `s` changes (rule K);
   - both requests high with no grant (contest);
   - x/y_ack low at z_ack↑;
   - the minimum inter-transition gap (M6);
   - LUT edges to a value ≠ F(pins).
3. **Lean, no board:**
   - H_NO_DEADLOCK' plus a witness (8z2);
   - the network half of Br2 (8x);
   - composing Br1 over all 367 operators;
   - an H_MAP wiring table;
   - rule K's verdict (10l2);
   - HDsub (W-E4g).
4. **T1** (on-die differential two-path): decides κ / κd and every "C under the band" row.
5. **T2** (C-element own feedback vs neighbour response): H_FB_FIRST and uenv1.
6. **T5** (arbiter handover on one die, q on A3 vs A5): H_ARB_EXCL, H_A0_FORK, H_GRANT_FORK.
7. **Kleene/edge tests:** the runt-flag pass matrix (H_KLEENE_LUT), the LUT-ring edge count
   (H_NO_REVERT) and XW-1 (X windows).
