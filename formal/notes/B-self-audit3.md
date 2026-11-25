# B-self-audit3 (probe Bsa3): adversarial audit of shard B's "formal B" Cells commits since 10-27 12:20

2026-10-29. Scope: `git log --since='2026-10-27 12:20' -- formal/lean/Formal/Cells`, commits whose
message starts "formal B" (861de85, abe7d25, 824f130, bb4738c, 555a875, 3dc88a4, f832d38, 5fd1767,
d06d30c, 08938de). The independent audit (/tmp/claude-0/report.md) already CONFIRMED, with
mutants, Necessity2*/3*, KleeneBox, CTreeExact, ArbPin2, ResetGcdVec2, ConstraintsKappa,
OnNetlistArbKappa, OnGcdArbKappa. I re-read nothing there that changes those rows, so they are
skipped. Left in scope: **RigSrc** (824f130; audit row: joint non-vacuity UNVERIFIED),
**ResetGcdNetR5** (f832d38; not covered by the audit), **ResetGcdNetRe** (f832d38; audit
CONFIRMED, but without a run witness), **ArbHeldTimed2** (d06d30c; comment only).

Every check went through `/tmp/claude-0/btools/bcheck.py` (lean -DautoImplicit=false, private
oleans). New files:
- `formal/lean/Formal/Cells/SelfAuditB6.lean` -> OK
- `formal/lean/Formal/Cells/SelfAuditB6Data.lean` (generated data, untrusted, checked by B6) -> OK
- mutants in `formal/lean/Wip/Bsa3/` (not built): `R5Mut.lean`, `RigMut.lean`; `Ax.lean`
  (axiom printout; ends with a deliberate `example : False` so the checker shows its output).
- scratch generator: `/tmp/claude-0/probes/Bsa3/sim/rigsim.py`, `gen.py` (C's `capwit/sim.py`
  with the rig environment in place of C's one-shot sources).

Re-checked as shipped: `RigSrc.lean` OK, `ResetGcdNetR5.lean` OK.

## Verdicts

| file | claim (journal / note / header) | verdict | evidence |
|---|---|---|---|
| RigSrc | `gcd_rig_first_env`: C's `gcd_rig_first` with H_ENV and the sources' SrcR discharged from the env cells' step forms through monotone causal read maps | **CONFIRMED** (statement); joint non-vacuity now **CONFIRMED** (was UNVERIFIED) | Statement read: implication, quantifiers as in the note; first result only (stated). NEW `SelfAuditB6.rig_env_feeds`: one run `chS` of C's 465-channel network (a=12, b=18) discharges EVERY hypothesis (H_KER for all 367-3 non-source ops via C's `kChk`, H_BUNDLE, H_FORK_WIRE, H_DAT, H_REL, H_REL0, H_OUT0_ACK, H_UENV1_B, H_C3, M1, M0; all read maps `id`) and is fed to `gcd_rig_first_env` itself; out0's first token closes at tick 474 with value 6 (`rig_env_latch`); the env completes lap 1 and re-offers (`riseB e 432`, `rig_env_relap`), as M0/M1 force. Needed a new generic lemma `cell_sh1` (C's `cell_rt` needs `phi 0 = 0`; shifting by one tick needs every reset field at tick 1, derived per kind from the cell's own tick-0 step) |
| RigSrc | `W.env_nonvacuous` cited as non-vacuity | **OVERSTATED as cited for §4** (correct for §3) | the lap witnesses `env_lut_si`/`env_H_ENV` only; the note says so ("a witness for those would be a full gcd_hw run"). Superseded by `rig_env_feeds` |
| RigSrc | witness degeneracy | (e) the new witness is **degenerate in delays**: unit-delay gates, every wire/pin read map `id`, uenv0's `urdly` delay 0, one input pair. Not degenerate in behaviour (out0 latches; second lap starts). Real-delay maps and H_SINK_SI / RT_FB remain open as stated |
| RigSrc | `c3_move` uses the real bd_c3 INIT | **CONFIRMED** | `CElemFn.INIT_c3 = 0x0000FE800000FE80` = cells/rtl/bd_ce.v:62 |
| RigSrc | `CX.ker_ack_needed` (H_KER_ACK cannot be dropped) | **CONFIRMED** | read; a concrete 8-tick counter-run, decided |
| ResetGcdNetR5 | journal 12:35: "reset contract re-proved ... on the R5 board build"; note: "the same reset contract for the R5-sized board build (1826 nodes)" | **CONFIRMED** as a theorem about the transcribed term `rNet`; transcription UNVERIFIED (R5 netlist JSON not on disk; generator untrusted, no Lean link to ResetGcdNet) | compiles; `re_spec`, `re_reset_*`, frontier, census (same 153/185/1/10/14/21/21/9/9, 423 rst pins), maxRank 21. NEW `r5_reset_witness`: unit-delay run from the ALL-ZERO state, rst held, data 0, meets `Bounded 0 0` and H_RST_HELD; node 287 (reset value 1) starts at 0 (`r5_moves`). Mutant R5Mut (INIT bit 40 of r287, a reset row, `FFB2`->`FEB2`) FAILS at `ck0` and line 3644 (`re_frontier_fire`) |
| ResetGcdNetR5 | generated header: "Indices below 3322 follow ResetGcdNet (renumbering by gen.py match: an untrusted certificate, **checked below node by node**)" and "1540 indices are no node of the real network: committed data inputs that the synthesized netlist merges into one net (phiL)" | **OVERSTATED** (header wording) | part 1 (the comparison) is omitted in this file ("-- (part 1 ... omitted)"); `diffT = permT = []` are unused. Of the 1540 "no node" indices only 29 are phi merges; ~1511 are delay-chain elements removed by the R5 sizes, mislabeled in their per-line comment "committed data input identified by phi". Harmless for soundness: I checked (Python over the file) that no gate pin reads any of these indices; only the 35 named data inputs are read. The README says it correctly ("does not match ResetGcdNet node for node") |
| ResetGcdNetR5 | (d) INITs vs cells/rtl | **not checkable here** beyond the census | census counts the 9 cell INITs by value (I_c2 ... I_arb5), same as committed; LUT1 delay elements INIT 2 |
| ResetGcdNetRe | re_* re-proved on the synthesized C-10e network; note: "No new non-vacuity witness was built" | **CONFIRMED**; non-vacuity now built | NEW `re_reset_witness` (same all-zero unit-delay run). Audit's own INIT mutant and byte-identical regeneration stand. Routed-bits table (routed.py) remains Python, UNVERIFIED |
| ResetGcdNetRe/R5 | `re_reset_release` (H_FRONT_HOLD) | **not witnessed** (open) | no run satisfying H_FRONT_HOLD past release was built here |
| ArbHeldTimed2 | comment: the runt hole "circulates for ever (proved for the boundary runs in Necessity2Arb)" | **CONFIRMED** | `SG1c_run` is a `Run` for all t (closed-form traces), `G1c_both k`: A1·A2 at 22+4k for every k. "a simulation also finds a non-decaying train with c1r < c1f": simulation only, UNVERIFIED (stated as simulation) |

No theorem was REFUTED. No checking file uses sorry/admit/axiom/native_decide.

## Mutants (`formal/lean/Wip/Bsa3/`)

| mutant | change | result |
|---|---|---|
| R5Mut | r287 INIT bit 40 (I3=rst=1, I5=1) flipped | FAIL at `ck0` (kernel), and l.3644 |
| RigMut.mut_k | in_ack toggles 99 -> 100 in `envOK` | FAIL (uenv1 b half) |
| RigMut.mut_k2 | same shift in `srcOK` (H_C3 only) | **PASSES**: H_C3 alone does not see a 1-tick later in_ack rise (the acks stay high 40..140 / 98..198). Weak mutant; the env check as a whole (mut_k) catches it |
| RigMut.mut_a | source value a = 13 | FAIL (H_DAT) |
| RigMut.mut_t | out0 close at 473 instead of 474 | FAIL |

## Axioms (`Wip/Bsa3/Ax.lean`)

cell_sh1: propext, Quot.sound. rig_env_feeds, r5_reset_witness, re_reset_witness: propext,
Classical.choice, Quot.sound. rig_env_latch, rig_env_relap, r5_moves: propext.

## Notes for the lead

- Another probe's untracked `Formal/Cells/RigSrcWitness*.lean` appeared in the tree during this
  session (not mine, not read); it may duplicate `rig_env_feeds`. Keep one.
- Suggested fix (generator template, not done: not my file): R5 header should say "part 1 not
  checked" and label removed delay elements as such.
