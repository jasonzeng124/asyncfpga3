# B-self-audit (probe Bsa): adversarial statement audit of shard B's post-07:45 files

2026-10-27. Scope: ContractsTrunc*, OpsHold, ContractsMux, ContractsLink, OpsExact2,
ResetGcdWave, RigContract, Contracts, ContractsB, ContractsOps, OpsCounter, OpsExact,
MuxN3Timed, ResetContract, ResetGcd, ResetGcdNet (formal/lean/Formal/Cells/) and their notes.
Every check goes through the lakefile's options (`-DautoImplicit=false`) via
`scratchpad/bchk.sh`. No route, no toolchain run.

## 1. Compilation under autoImplicit=false

All 19 files check: `bchk.sh Formal/Cells/<F>.lean` printed `[bchk] OK` for each (Contracts,
ContractsOps, ContractsB, ContractsTrunc, ContractsTruncCel, ContractsTruncSteer,
ContractsTruncWit, OpsCounter, OpsExact, OpsExact2, MuxN3Timed, OpsHold, ContractsMux,
ContractsLink, ResetContract, RigContract, ResetGcdNet, ResetGcd, ResetGcdWave). RigContract
now compiles (only `if_pos`/`if_neg` deprecation warnings): the audit row 48 fix
(`{e : Nat → Nat}` bound in `stale_window`) holds.

## 2. New non-vacuity witnesses (all check, core Lean, no sorry/axiom/native_decide)

| file | theorem | what it shows |
|---|---|---|
| `SelfAuditB.lean` | `net_refines_causal_witness` | every hypothesis of `ContractsTrunc.net_refines_causal` at once on a 1-channel source→sink net (`Witness.wch`). Consistency only: base and steps come from the whole-run port via `port_iff`. |
| `SelfAuditB2.lean` | `wave_witness` | 7f's unit-delay run of the 3322-node `gNet` from ANY power-up state, rst 1 on `[1,F]` (`F ≥ 23`): meets `gcd_reset_binary`, `gcd_loop_late` and `gcd_wave_settled` jointly; conclusion: every control node = `sigB` at step `F+34`. |
| `SelfAuditB3.lean` | `idx_setup_witness` | `RigContract.idx_setup` had no witness. 7600 ps hk, transport paths 600/1500 ps, real `bd_c2n` INIT with unit LUT arc and feedback wire: every hypothesis holds for every load edge `n0`; controller high from `r+1` to window end. Caveat: lo = hi paths, so `PathOK`'s band and `H_RST_ONE_FALL` are exercised only trivially. |
| `SelfAuditB4.lean` | `steer_contract_witness` | `ContractsB.steer_contract` had no witness. Run of ContractsTruncWit; `SteerCausal`, `SteerStatic` (decide), quiet/first-edge facts, C's channel maps. |

Note (corrected by probe Bsw): `OpsTimed.SteerWit` witnesses `steer_ok` and
`steer_ok_static` (all their hypotheses hold) and was never meant to witness
`steer_contract`; it does not meet `steer_contract`'s `H_T1` (`T1 0 = 5 > R0 0 = 4`,
`OpsTimed.SteerWit.not_H_T1`). Not a defect: `steer_contract` simply had no witness
until SelfAuditB4.

Observation (SelfAuditB2): with D = W = 0 the steers are 0 exactly through `F+34`
(`gcd_loop_late`) and the wave settles exactly at `F + 34(D+W+1) = F+34`, so
`gcd_wave_settled` speaks about ONE step of the unit-delay run. For D+W > 0 nothing proved keeps
the loop entry after `F + 34(D+W+1)`; there the settled-state conclusion needs H_STEER_HOLD as an
assumption about the run (the note says the capstone must then carry the `sA`/`sB m` cover).

## 3. Mutation tests (copies under `Formal/Cells/_Mut/`, for the lead to delete)

| mutant | change | result |
|---|---|---|
| MutRigA | sticky INIT `0xEC00 → 0xEE00` (sets with arm 0) | FAIL: `sticky_holds_K` (638), `sticky_sets_only` (644), `stale_err_vectors` closed-arm conjunct (683) |
| MutRigB | `verdict_current`: `H_ARM_BEFORE_IDX` weakened to `ahi ≤ Tlo + vlo + 1` | FAIL: omega in `verdict_current` (idx window end) |
| ResetGcdNet/ResetGcd | `ulink_n1__1` INIT bit 1 cleared (`…00B0`: no fire at a=1,b=0) | FAIL: `ck4` (chunkOK 1600 400), `gcd_frontier_fire`, `gcd_census` |
| MutSteerA | `steer_pinN`: `S_SETUP0` to `Ws.hi ≤ Wq.lo + 1` | FAIL: omega in `steer_pinN` |
| MutSteerB | `steer_pinN`: `S_HOLD_RT` RHS `+1` | FAIL: omega in `steer_pinN` |
| MutWave | `gcd_loop_late`: `j ≤ T + 34` to `T + 35` | FAIL: omega at the chain index (34-LUT path) |

7/7 mutants break, each at the mutated obligation's use site.

## 4. Statement audit

| theorem | claim (note/journal) | verdict | evidence |
|---|---|---|---|
| RigContract `verdict_current` | "the verdict cannot be stale in the current RTL, given `H_ARM_BEFORE_IDX`" | CONFIRMED | statement quantifies every t in the tile with arm ≠ 0; `verdict_nonvacuous`; MutRigB |
| RigContract `idx_setup` | "`gcd_rig.idx_setup` is now a composed theorem" | CONFIRMED (witness added) | SelfAuditB3 |
| RigContract `stale_window`, `stale_err_vectors` | "ok+err pairs explained exactly … from the one hk cycle p = 1"; "the comment's drain mechanism is refuted" | OVERSTATED | Lean shows the old arm open at p = 1 with new idx, and the steady-state detector values. That a stale result is on `res_req` (C_STALE, through the width filter) is NOT proved (note §2d says so), and "refuted" rests on `gcd_reset_binary` (GMW model) plus `H_RESULT_FRESH`, cited by shape. A model explanation and a model counter-argument, not a refutation |
| RigContract `verdict_attrib` | verdict judges the kernel's answer to the same vector | CONFIRMED, conditional | its content is `H_RESULT_FRESH` + `H_IDX_BEFORE_RELEASE`; nearly definitional, as worded |
| Contracts `opSpec_of_ports`, `net_refines_ports` | Port + EarlierDet ⇒ C's OpSpec / net_refines | CONFIRMED | `Witness.port`; whole-run ports assumed (note's G1, disclosed) |
| ContractsB `steer_contract` | steer_ok_static's hypotheses ⇒ steer's halves + SteerEv | CONFIRMED (witness added) | SelfAuditB4; see H_T1 finding |
| ContractsTrunc `net_refines_causal` | "No port is assumed for the whole run" | CONFIRMED with caveat | true of `Port`; but ρ, α, v (all edge times, for all indices) are given up front, i.e. liveness assumed (note item 2) |
| ContractsTruncSteer `steer_step_ports` | the steer's causal step, non-vacuous at every N | CONFIRMED | ContractsTruncWit `step_witness`; MutSteerA/B |
| ContractsMux `mux_contract` | "Both contracts are witnessed jointly on unit-delay runs" | OVERSTATED (wording) | the 2-way witness drives the joins' select (`sx`) and the datamux select (`sF`) with different traces; `bd_mux` has ONE `s` net. Sound (theorem more general) and disclosed in the file, but not a joint witness of the physical cell |
| ContractsLink `no_lead_breaks` | "NOT a Port for ANY request/acknowledge traces" | CONFIRMED (scope) | ∀ r a, but with the edge sequences fixed (`Wr = shift 1` τ, γ) |
| ContractsLink `pipe_witness` | every hypothesis of `pipe_contract`, every N ≥ 1 | CONFIRMED | in file |
| OpsHold `mux_data_hold_fall` etc. | hold to the z_ack fall | CONFIRMED with caveat | mux witness instantiates the data half only (disclosed); negative controls in file |
| OpsExact / OpsExact2 "exact" rows | e.g. `S_XA_RTZ` exact, `S_Z_S1` exact individually | CONFIRMED in the stated sense | "exact" = sufficient in general + a run violating only that inequality by 1 tick whose conclusion fails. Checked `cex_S_XA_RTZ` (gates/env/causal/hRL/hRE for all e, `static_but_rtz` lists every other field, conclusion refuted) and `cex_S_Z_S1` (all other `MuxDataStatic` fields hold at (10,1,1), conclusion refuted). Not "iff" |
| ResetGcd `gcd_reset_binary` | "ANY power-up state … data arbitrary" | CONFIRMED | `v` arbitrary `Run`; inputs constrained only via `gA` (rst t, data x); SelfAuditB2; mutant breaks ck4 |
| ResetGcd `gcd_release_quiet` | "whatever rst and data do from k0 on" | CONFIRMED | no rst/data hypothesis after k0 |
| ResetGcdWave `gcd_wave_settled` | "for EVERY rst waveform in the window" | CONFIRMED with caveat | rst free on (S, F]; needs H_STEER_HOLD to `F+34(D+W+1)`, guaranteed only to `F+34` (observation above) |
| ResetGcdWave `gcd_loop_late` | no steer leaves 0 before T+35 | CONFIRMED | MutWave; tightness (a run firing at T+35) not exhibited |
| MuxN3Timed, OpsCounter, ResetContract | witnesses / counter-runs in file | not re-audited in depth (time) | compile OK; witnesses present (`Mn3Wit.witness`, `MuxCex`, `MergeCex`, `rig_spec`) |

## 5. Not done
- No mutation of OpsExact2/MuxN3Timed INITs (they live in shared files; a copy chain was not
  built). No tightness run for `gcd_loop_late` (needs ~60 kernel steps of the 3322-node sim).
- The ResetGcd import (Verilog → Lean) is still unverified Python (WL cross-check only).
