# Audit P7: capstone non-vacuity, liveness, ipow, rig, Bnet (formal head 6863284)

Auditor files are in `audit/lean/P7/`:
- `AuditP7.lean` + `.out`: statements, `#print axioms`, `joint_feeds_safety`, the 8t mutants, `witness_not_bounded`, `witness_not_env` and `step0_only_src`.
- `IpowWit.lean` + `.out` (b=3, e=7) and `IpowWit2.lean` + `.out` (b=0xFFFFFFFF, e=3): an auditor-built joint witness for `ipow_circuit_safe3`.
- `mut/IpowWitMut.lean` + `.out` and `mut/ResetGcdNetReMut.lean` + `.out`: mutants. Both must FAIL, and both fail.
- `tools/`: `catobj.py` (reads git objects without the git binary), `treediff.py`, `closure.txt` (the import closure that was grepped), `ipow_vec.py`/`.out` and `ipow_c.c`/`.out` (C semantics), `ipowwit/` (generator for the ipow witness).
- Bnet reproduction: scratch tree `/root/audit-scratch/p7/` (`repo/`, `out/`, `mutflat.json`).

Setup:
- Lean 4.35.0 against the clean `lake build` of 6863284 (log `audit/logs/formal_build_6863284.log`).
- No `lake build` was started by me, no file in ~/wt-f7 was edited, and no git command was run.
- Commit messages were read from the object store with `tools/catobj.py`.

## Verdict table

| commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|
| 299a16f (C-8t) | "gcd_hw_joint_witness: one explicit run of the concrete 465-channel network (a=12, b=18) satisfies H_CELLS (367 operators), H_BUNDLE (465 channels), H_START_ONCE and H_WALK at once and latches 6 on out0" | **CONFIRMED** | `AuditP7.joint_feeds_safety`: destructures the witness and feeds `w_cells/w_held/w_start_once/(yW, Good, WalkOK)` straight into `gcd_hw_circuit_safe''`, so the hypotheses are the same constants, not copies. out0 (ch 416) first token (k=0) closes at tick 473 with dat 6 = gcd 12 18. I regenerated `CapstoneNet.lean` with `capnet.py`: byte-identical. Mutants: `mut_src` (same run, b=24) and `mut_toggle` (one toggle of ch 7 moved one tick) are REJECTED by the kernel checker. Axioms: propext, Classical.choice, Quot.sound | Answers P5's open point: an actual latch exists. Limits: one input, one unit-delay schedule; sources a/b offer once and stop |
| fccbd1b (C-8z) | "gcd_hw_live_final: first out0 closes within (1168(8 Lrun+23)+1)(H+1) ticks with value gcd a b, under cell/env/bounded-delay hypotheses + H_NO_DEADLOCK' (open)" | **CONFIRMED as a conditional reduction; joint satisfiability UNVERIFIED** | Statement read (below). Axioms clean (`gcd_hw_live_final`, `walk_ends`). `AuditP7.witness_not_bounded`: the 8t witness does NOT meet H_BOUNDED_DELAY' for any H (the `a` source stops after tick 138), so 8t gives no non-vacuity here. I re-ran `ndsim.py` (8 vectors × 3 seeds, free-running a/b sources): 0 deadlocks. That is evidence only | H_NO_DEADLOCK' is not the conclusion restated. It says "no global quiescence before the first close". The theorem adds termination of activity (the offer certificate 4L+11 rules out livelock), the time bound and the value. It does, however, assume exactly the deadlock-freedom half of liveness. `Lrun y` is the length of an existentially chosen token run; no number is computed. C's journal also says there is no Lean witness |
| 2092f12 (C) | "verdict on liveness corrected (8z; 8u's gcd_hw_live not to be cited)" | **CONFIRMED** | `treediff.py fccbd1b..2092f12`: only `JOURNAL-C.md` and `LOCK-C` change. `start_never_closes` / `src_once_never_closes` exist as theorems (CapstoneLiveNdStart.lean:34,84) | Journal-only correction. FEASIBILITY item 2 cites live_final with "(open)" and does not cite gcd_hw_live |
| 8965ea0 (C-8y) | "ipow_circuit_safe3: every out0 latch of the concrete ipow network (101 channels, 83 operators ...) is ipowSpec b e under H_CELLS, H_BUNDLE, H_START_ONCE (+ e < 2^32)" | **CONFIRMED** (incl. non-vacuity, built by me) | `ipowSpec b e = if e < 2^31 then b^e % 2^32 else 1`. It matches `ipow.c` and cf_transformed.mlir with 32-bit wrap: 6014 vectors, 0 mismatches (`ipow_vec.out`; gcc -fwrapv spot vectors `ipow_c.out`, e.g. ipow(2,32)=0, ipow(5,0x80000000)=1, ipow(0xFFFFFFFF,3)=0xFFFFFFFF). `IpowWit`/`IpowWit2`: kernel-checked runs of the 101-ch network, out0 latches 2187 (3^7) and 0xFFFFFFFF (overflow wrap), and `ipow_circuit_safe3` applied to them agrees. Mutant `IpowWitMut` (srcV 3 8 on the e=7 run) is rejected. `capnet.py` regenerates IpowCapNet/IpowCapLinks byte-identically. Independently from the bdc-emitted Verilog: 7 bd_link + 14 bd_pipe = 36 stages = 36 links, 4 mux, 2 amerge, 8 steer = 2+6, 13 bd_join = 5+8 | C signed overflow is UB in ISO C. The spec is the wrapped (-fwrapv / MLIR i32) semantics, which is what the hardware computes. Not covered (stated): liveness, DSP48E1 modelled as combinational |
| ae791b6 (C-8s2) | "gcd_rig_first: for the rig's env (H_ENV ...) with H_CELLS minus the src reset field and H_BUNDLE, the first value offered and latched on out0 is gcd a b" | **CONFIRMED** (statement + axioms); non-vacuity **argued, partly kernel-checked** | Statement as claimed (below). `witness_not_env`: the 8t run itself violates H_ENV (start rises at 0 while out0.ack is low). Indeed no run with every signal low at 0 can meet H_ENV and ever offer out0. My witness X = 8t's run shifted by one tick (chW(t+1)): `step0_only_src` (kernel) shows only the three source requests toggle at step 0. So every non-source reset field of X holds, every guard of X at t is chW's at t+1, and start.req in X is high at 0 and only falls (98): H_ENV holds vacuously. The CellR proof for X is not mechanised | Safety of the first result only. "Every result" is open (stated; `rearm_fails_at_reoffer`) |
| 824f130 (B, RigSrc) | "gcd_rig_first_env: the first out0 offer and first latched value are gcd a b with H_ENV and the sources discharged" | **CONFIRMED** (statement + axioms); joint non-vacuity **UNVERIFIED** | Statement (below): H_ENV and the sources' SrcR are derived from B's env step relations (H_UENV1_B, H_C3, M1, M0, H_FORK_WIRE, H_REL, H_REL0) through monotone causal read maps. B's own `W.env_nonvacuous` covers the env lap alone, not the env together with the 367-op network. Argument: M0+M1 force `e` (start) to re-rise after out0.ack falls, so any witness is a ≥ 2-lap run with a/b/start requests equal to one trace `e`. The 8t run (a,b requests [0,41], start [0,99]) cannot be one | Open items (stated by B): laps ≥ 2, H_SINK_SI, kernel reset joined to ResetGcd, uenv1 RT_FB |
| f832d38 (B, Bnet) | "gcd_hw's control-network term regenerated from the SYNTHESIZED netlist by a committed, re-runnable generator ... gen.py reproduces ResetGcdNetRe.lean byte for byte" | **CONFIRMED** (independently reproduced from RTL) | Steps: bdc/emit.py with BDC_SELECT_PADS=gcd_hw_pads.json, --probe n138, on the gcd fixture MLIR; then build_hw.sh's exact yosys script (audit-tc yosys 0.62); then rloc_stamp v4. My netlist's sha256 is `f0a7f326…a420`, the hash recorded in ResetGcdNetRe.lean, after replacing the toolchain path in yosys `src` attributes (/root/audit-tc → /root/dev2/lib/fpgatoolchain). gen.py net/match/lean on it gives ResetGcdNetRe.lean identical except line 8 (the sha). Mutants: one INIT bit of `ucontrol_merge2.uarb1.ustate` flipped in the netlist makes gen.py abort (assertion). The same bit flipped in a Lean copy (`r287`) breaks `cs0` and `re_census` in the kernel. Axioms: re_matches propext, Quot.sound; re_reset_* propext, Classical.choice, Quot.sound; re_census none | The routed-bits claim is Python only (routed.py, not a theorem; stated) and UNVERIFIED here (no routed builds). gen.py's `match` renumbering is untrusted, but the Lean equality is checked node by node |

Side finding (not in scope, needs follow-up): the clean `lake build` of 6863284 ends with `EXIT 1`.
- `Formal.Core.Delay.GLSPass` has a real elaboration error at 336:33, 337:21 and 385:24 (`Unknown identifier d`, `Invalid argument name d for skew_fval`).
- `Formal.Net.MullerSI` was killed (exit 137, probably memory pressure on this shared 15 GB host).
- Every module on the proof paths above built.

## (c) Hygiene

- I grepped all 102 modules in the import closure (`tools/closure.txt`) for sorry, admit, native_decide, implemented_by, extern, unsafe, axiom, opaque, decide +native, ofReduceBool, skipKernel, csimp and macro/elab. There are no code hits: only comments, and ResetContract docstrings that use the word "opaque latch".
- Kernel computations are `decide +kernel`. `#print axioms` of every headline theorem and every auditor theorem gives a subset of {propext, Classical.choice, Quot.sound} (`AuditP7.out`, `IpowWit*.out`).

## Details

**8t `gcd_hw_joint_witness`** (CapstoneWitness.lean:62):
`∃ ch, (∀ o, Cell ch (srcV 12 18) (opAt o)) ∧ (∀ c, Held (ch c)) ∧ (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧ (∃ y, Good 12 18 y ∧ WalkOK (σY 12 18 y) (omOf 12 18 y)) ∧ (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6)`.
- The run `chW` is event-list data from `capwit/gen_data.py` (untrusted).
- `kChk_sound` proves the checker sound against `Cell` (12 kinds). Event lists make signals piecewise constant, so checking at the toggle points covers all t.
- The witness proves "latches", not "offers only": `TokAt` = ack fall and count. The value 6 is read at the close tick.

**8z `gcd_hw_live_final`** (CapstoneLiveNdWalk.lean:120). In plain words: take any run with internal gate traces `itr` such that
- every operator meets its gate model, every channel is bundled, and start rises at most once;
- every gate except start's LUT settles within H when it stays excited for H+1 ticks, start is offered within H of being enabled, and every uncontested arbiter grants within H;
- before out0's first close, the network is never globally quiescent (ignoring start's LUT once start has been offered).

Then the first out0 token closes before `(1168(8·Lrun y+23)+1)(H+1)` and carries gcd a b, for a complete token run y of (a, b).

The bounded-delay part also forces the a/b sources to be free-running (`req` follows `¬ack`). That is why the 8t run, whose sources stop, fails it (`witness_not_bounded`). A Lean witness would need a free-running unit-delay run plus checkers for BndG/ArbUnc/StartEnv/Quiet2. That is not built (UNVERIFIED). It looks plausible: ndsim with q=1 is such a run, and the a/b sources are throttled by the joins waiting on start, so the run eventually quiesces.

**8y**:
- `ipow_circuit_safe3 (b e) (he : e < 2^32) ch H_CELLS H_BUNDLE H_START_ONCE : (∀ k v, TokAt (ch out0) k v → (ch out0).dat v = ipowSpec b e) ∧ closedVals…`.
- Same `CapNet.Cell` and `Held` as gcd. `ipow_ports` decides that start is `.src start 2 0` and out0 is `.hist 57 1`.
- e ≥ 2^32 makes it vacuous (stated). b is not range-restricted; this is harmless because the spec is mod 2^32.

**8s2 / Bsrc**:
- `gcd_rig_first a b (ha hb) ch (H_CELLS_R : ∀ o, CellR ch (srcV a b) (opAt o)) H_BUNDLE (H_ENV : ∀ t, riseB (ch start).req t → (ch out0).ack t) : (∀ r, OffAt (ch out0) 0 r → dat (r+1) = gcd a b) ∧ (∀ e, TokAt (ch out0) 0 e → dat e = gcd a b)`.
- `gcd_rig_first_env` replaces H_CELLS_R/H_ENV with H_KER (Cell for non-source ops), H_FORK_WIRE (all 3 source requests = e), H_DAT, H_REL, H_REL0, H_OUT0_ACK, monotone causal read maps β, γ, φ1, φ0, and the env step relations H_UENV1_B, H_C3, M1, M0. The proof composes `rig_cellR` and `env_H_ENV` into C's theorem. There is no circularity: the kernel ack rule comes from `gcd_hw_protocol` on a frozen run.

**Bnet**: the input really is the yosys output of the RTL (shown above), not a hand-edited JSON. Seed independence ("identical for seeds d/2/3/4") is trivially true, because synthesis precedes nextpnr.
