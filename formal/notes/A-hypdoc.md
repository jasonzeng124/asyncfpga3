# A-hypdoc: rewrite of formal/out/gcd_hw_hypotheses.md

Shard A probe HypDoc, 2026-10-27, about 10:40-11:30 UTC. Only Markdown was written. No Lean was
run, because Mathlib was still building (`setup.log`: building from source) and no `Formal/Net`
oleans existed.

## What was read

- JOURNAL-B.md and JOURNAL-C.md, in full.
- Shard C's notes: C-gcd_hw-hypotheses, C-8m, C-8q, C-8r, C-8n, C-10k, C-10l.
- Shard B's notes: B-reset-gcd, B-reset-gcd-wave, B-rig-contract, B-contracts-link and B-gcd-cells
  (inventory).
- The audit: `REPORT.md` at `origin/claude/audit` 1f6a9a1, plus its journal and its build log of
  f4696cc.
- The tcheck results `summary10l.txt` and `extract.py:340-358` (the OUTMUX hop).

## Lean statements opened and checked by hand

| file:line | what |
|---|---|
| `CapstoneCut.lean:492,507,535,547` | `gcd_hw_forced`, `gcd_hw_cut`, `gcd_hw_circuit_safe''`, `gcd_hw_arbiters_uncontended'` |
| `CapstoneSafe.lean:43,47` | `cm_oracle_exists`, `gcd_hw_circuit_safe` |
| `CapstoneO1.lean` | the whole file |
| `Capstone.lean:40,59` | `latched_const`, `gcd_hw_conditional` |
| `CapstoneSafeHist.lean:456,466` | `Good`, `good_exists` |
| `CapstoneCutSpine.lean:39,100` | `start`, `WalkOK` |
| `CapstoneNetDef.lean:373` | `Cell` |
| gate-model structures | `Fork` (OpsFork:29), `Join` (OpsJoin:35), `Steer` (OpsSteer:39), `Mux` (OpsMux:257), `MuxN` (OpsMuxNOp:35), `AMerge` (OpsCM:163), `Link` (OpsLink:130), `Sink` (OpsGcd:43), `Src` (CapstoneSrc:18) |
| `Ops.lean:81` | `Held` |
| `OpsGen.lean:86-99` | `LutFb`, `LutSI`, `FbFirst`, `Gap` |
| `ResetGcd.lean:198,392` | `gcd_reset_binary`, `gcd_reset_release` |
| `ResetGcdWave.lean:572,726` | `gcd_boot`, `gcd_clean_release` |
| `Contracts.lean:170` | `Port` |
| headers | GcdCells, ResetContract, ContractsOps, ContractsLink, ContractsMux, ContractsTrunc, Bridge |

## Findings worth the lead's attention

1. **Rule K (the mux ctl_req fork, C-10l, WIP) fails at every corner, including sdf.** It fails on
   16-26 of 42 rows per route, worst −8987 ps slow. Every other capstone row passes unguarded.
   C-10l's verdict section is unwritten. Until shard C interprets it, H_SEL_PIN for muxes is
   graded "C pending".
2. **The safety theorem is vacuous for liveness**, and shard C says so. The all-quiet run meets
   every hypothesis. No network-level witness exists.
3. **H_START_ONCE covers one rig lap.** The rig re-offers start every lap. My unmechanised reading:
   a frozen run still meets every gate model, so the theorem covers tokens closed before the
   second start request.
4. **B's Port route (§7) cannot carry the capstone as stated.** `Port` needs infinitely many
   edges on every channel (G4), and `start` has one token.
5. **The OpsGen bindings are per cell kind.** No theorem instantiates them over the 367
   operators. Forks with N ≥ 3 and C-trees are unbound.
6. **RigContract.lean still does not compile at HEAD** (audit REPORT.md:48; the file is unchanged
   since 3e00ce4). Every module under Formal/ is claimed by the lakefile glob, so the tree's full
   `check.sh` will fail until it is fixed or moved to Wip.
7. **Reset (B, `gNet`) and the capstone (C, Ops `ch`) use different models with different initial
   states.** The `bd_src` req and `uenv1` are 1 under reset in `gNet`, while `Src.iz` says
   `req 0 = false`. Nothing links the two.
8. **The OUTMUX hop is fixed in C-10h's `extract.py`** (audit REPORT.md:38). The audit has not
   re-run 10h.

## UNCONFIRMED items (marked in the doc)

- That no `Good` run exists for inputs ≥ 2^31: a doc claim only.
- That `LutSI` follows from Bridge's `Inertial` for this network.
- H_GHOST and H_FOLD: prose only.
- That omitting the source chains is safe: prose only.
- Rule K's interpretation.
- The 10j arbiter grant-fork Lean, which I did not open.
- RigContract's claims.

## Requests for the lead

None for the lakefile or root imports: only Markdown was written.
