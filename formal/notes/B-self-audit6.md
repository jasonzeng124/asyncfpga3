# B-self-audit6 (probe Bsa6): adversarial audit of shard B's work since self-audit 5

2026-10-29. Method as in B-self-audit5.md: re-check every in-scope file through
`/tmp/claude-0/btools/bcheck.py` (lean -DautoImplicit=false), read each headline statement
against its JOURNAL-B.md entry (10:05 ... 11:33), its note and its header, build mutants that
must fail, and add Lean checks where a claim can be settled in Lean. Scope: commits 7b7df9b
(Bnx7), 66a33f4 (Bwb), 37f2f0e (Bring), 1b8bfc0 (Barb3), 9f53c21 (Bj9), ddd4616 (Bfin), c8561f0
(Bedge), 47a6e76 (Bmux2), 9bb61b6 (Bj10), 14484c2 (Bfin2), 31368db (Bcr), c1ed5e6 (Bmn),
52d4fee (Barb4), 650987d (Bj11); ArbSettled (e8f6a1e) is unchanged since Bsa5 and was only
re-checked.

## Files

- `formal/lean/Formal/Cells/SelfAuditB9.lean`: **OK** (core only; no sorry/axiom/native_decide).
- mutants `formal/lean/Wip/Bsa6/M01..M10_*.lean` (not built; each a full copy of the shipped
  file with ONE change, named in its first line); `Wip/Bsa6/Ax.lean` (axiom printout, ends in a
  deliberate failing `example` so the checker prints).
- scratch: `/tmp/claude-0/probes/Bsa6/` (check logs, regenerated JSON, JSON mutants V1-V3,
  `iffs.py` that prints each exact row's cited iffs).

## Re-runs

- All 35 committed in-scope files re-check as shipped: **OK** (ArbAMerge, ArbAMergeRun{,Stitch,Wit},
  ArbCounterRuns{,AM}, ArbSettled, AssumeGuaranteeMux{,Or,Net}, AssumeGuaranteeMuxN{,Tree,Fin,
  FinWit,Net}, EdgeTimes{,Net,Ring}, FiniteRuns{,Wit,WitData}, FiniteNet{,Cells,Mixed,Wit},
  KleeneWinBound, Necessity7Mux{,N,NRuns,Runs,RunsN}, RingPhys{,Stage,Wit,Wit2}). The
  uncommitted `FiniteNetWit2*` (running probe Bfin3) is not audited (its parts that the glob
  caught also check).
- JSON: `python3 -I formal/out/cell_constraints.gen.py <scratch>` (it runs `bj5.py` itself)
  regenerates the committed `cell_constraints.json` **byte-identical**; validator 0 errors;
  151 rows: 38 exact, 56 sufficient+necessary_at_boundary, 10 sufficient (as journal 11:33).
- No forbidden token in any in-scope file (the hits for "unsafe"/"extern" are prose).

## New in SelfAuditB9 (checked)

| theorem | what it settles |
|---|---|
| `fcellOK_of_gph`, `seg_of_clean` | every truncated contract (`FCellOK`, used by `H_REST` of `FGcdNetOK`/`FGcdNetOK3`; and FChain's `SRC_SEG`/`SNK_SEG`, same shape) holds on a run as soon as its conclusion (the node is clean) holds, whatever its pins do |
| `fcellOK_nil_iff` | for a cell with NO pins, the contract IS the bare assertion that its node is clean. `GD`, `GcdNet` and `FGcdNetOK(3)` allow such cells: `ι` is free, `H_REST` covers every untied cell, and no field fixes `D.pins` of an untied cell or `GPin.drv` of a tied cell's pin |
| `pin_of_pinless`, `flink_env1_local` | a link cell whose two pins are driven by pinless cells gets Bfin's `FEnv1` and `Timing1` from those two drivers' contracts plus `FNetW` alone: no other cell of the network enters. So in `gcd_hw_safe_fin_net`/`_net3` the "derived" link environment may be, for every link, the assumed contract of a private driver that just asserts the link's request and acknowledge are clean |
| `htok_iff_D`, `pring_D_pos` | `PRing.H_TOK` is `0 < Ring.D N b`; the `0 < D` half of `ring_run_iff`'s forward direction is a hypothesis field (no dynamics); only `D < N` (and `3 ≤ N`) is derived |

Axioms (`Wip/Bsa6/Ax.lean`): `fcellOK_of_gph`, `seg_of_clean`: none; `fcellOK_nil_iff`,
`htok_iff_D`, `pring_D_pos`: propext, Quot.sound; `pin_of_pinless`, `flink_env1_local`:
propext, Classical.choice, Quot.sound. In-scope headlines re-printed (`gcd_hw_safe_fin_net3`,
`gcd_hw_safe_fin_chains`, `gcd_hw_fin_chains_witness`, `ring_run_iff`, `amerge_of_plan`,
`amerge_witness`, `sep_cex_run`, `rt1_counter_run`): propext, Classical.choice, Quot.sound.

## (a) The network theorems

- **Hypotheses restating the conclusion?** No. The conclusion is C's gcd_hw safety (out0
  carries gcd a b); the hypotheses are B's per-cell models plus C's `H_OTHER`, `H_BUNDLE`,
  `H_CM_FORCED`. All three theorems are one-line reductions to Bfin's
  `gcd_hw_safe_fin_links` through `fphysLink_of_inChain` / `fphysLink_of_net` (and
  `FGcdNetOK3.toOK`, which only turns each new spec into an `FCellOK`).
- **Contracts vacuous?** Each assumed contract is an implication whose conclusion is "my node
  is clean", so it holds whenever the node happens to be clean (`fcellOK_of_gph`). On chW the
  `FInChain` end contracts hold for exactly that reason (disclosed in FiniteNetWit and journal
  11:11).
- **chW witness degeneracy.** Disclosed: one link per chain (`chD.N := 1`), end contracts true
  because their conclusions are, unit delays, `R = 2`. Not stated: the end nodes are not gcd_hw
  cells at all (`O 0 := cL x.rq`, `O 2 := cL y.ak`: the link's own pin traces one tick early),
  and `FInChainC` is a per-link existential, so different links' chains share nothing (no
  coherence with `AssumeGuaranteeCap`'s 100 chains is required). With `N = 1` and those end
  nodes, the end contract asserts the link's request/acknowledge cleanness, i.e. the content of
  `FEnv1`. "Derived" on this witness is a re-labelling.
- **"Derived" environment secretly assumed (net, net3).** `FGcdNetOK`/`FGcdNetOK3` tie the PIN
  TRACES of tied cells to C's channels but never their DRIVERS, and allow any number of untied
  cells (`ι` free). A pinless untied cell's contract is the bare cleanness claim
  (`fcellOK_nil_iff`), and a link fed by two such cells has its `FEnv1` from them alone
  (`flink_env1_local`). So the hypotheses admit an elaboration in which every link's
  environment is assumed outright and no fork/join/steer/mux/muxn/tree gate model lies on any
  link's input path. The uncommitted Bfin3 witness (`FiniteNetWit2`, header) builds exactly
  this elaboration for `FGcdNetOK` on chW ("one contract cell per channel signal ... no pins";
  "the gate-modelled ... nodes DRIVE NOTHING"), and says so. The committed notes say only "the
  elaboration (which cell drives which pin) is abstract" (B-assume-guarantee-muxn.md l.134,
  B-assume-guarantee-mux.md l.104); journal 11:30's "gcd_hw_safe_fin_net3 leaves ONLY muxn's
  |j, the 3 sources and the 9 amerges" counts the intended tied classes, not what the
  hypothesis enforces.

## (b) amerge_of_plan

- The 13 fields are C's: the result type is `Formal.Net.Ops.CM.AMerge` imported from
  `Formal.Net.OpsCM` (no restated copy); the `refine` fills 7 step fields from `run_fields`,
  `dat` with `H_DAT`, the 5 init fields from the reset epoch. `H_DAT` is literally C's `dat`
  field (with `z.dat = zd`, `y.ack = A2`); beyond `Run`, `MB`, `ZLine`, `Plan` it is the only
  hypothesis. It constrains only the free bus `zd`, so it is satisfiable on every run (choose
  `zd` by it), as the witness does.
- `Plan` is a parametric class (epoch kinds with inequality-constrained times, rows, races),
  not the witness's schedule; but it has ONE exhibited inhabitant (`Wplan`: 1 ps routes and
  arcs, smin 3, finite activity then idle forever, client-1-first one-sided class), so
  non-vacuity is shown at one point on a unit grid, not at routed numbers (stated in the file).

## (c) ring_run_iff

Quantifiers are right: `(∃ D : RingData, D.N = N ∧ D.b = b ∧ PRing D ∧ PRingT D) ↔ 0 < D ∧ D < N`
for every `N`, `b`; the right-to-left witness is `wR N b` (band [1,3], realised `1 + i % 3`).
But `PRing.H_TOK` is `0 < D` (`htok_iff_D`), so that half of "→" is assumed; the derived content
is `D < N` (and `3 ≤ N`, via `ring_frozen_D`). Disclosed in RingPhys's header ("H_TOK ... D > 0"),
not in `ring_run_iff`'s docstring or journal 10:19/10:48.

## (d) The validator's iff check (Bj10)

The check is syntactic: some citation with role `exact` whose Lean text from `theorem name` to
the first `:=` contains `↔` or `Iff`. Three JSON mutants (scratch, not committed) all pass with
**0 errors**: V1 `bd_link.stage_rearm` citing `EdgeTimesRing.ring_run_iff` (unrelated iff); V2
`bd_mem.setup` citing `FiniteNetMixed.flink_spec_env1` (its only `↔` is inside the hypothesis
`hn`); V3 `bd_arbiter.rt1` relabelled exact with `Necessity5Arb.settled_iff` appended. The
convention text says what the check does ("cites ... a theorem whose statement is an iff"), so
it is not misdescribed, but it does not establish relevance. Sample of 12 exact rows, cited iffs
read against the row's inequality: all are about the row (bd_c3.pulse_width, bd_mux.uxa_rtz:
generic CElemStrict iffs with the `c2_all` instance; bd_ctree.ack_wait: `reachable_eq_flat`, a
protocol-level row; bd_delay_gated.gate; bd_arbcell.settled_exclusion; bd_merge.uxa_loop;
bdc_muxn.no_third_branch; bd_mem.setup and clk_high_width_exact (iffs over an abstract timing
record `MemPort`, no gate model, disclosed); gcd_rig.idx_setup; bd_delay[FASTRISE].ack_succ;
bd_link.stage_rearm).

## Verdicts: Lean files

| file | claim (journal / commit / header) | verdict | evidence |
|---|---|---|---|
| FiniteNet | `ag_trunc` sound with `lo ≥ 1`, unsound at 0 (`ag_trunc_zero_cex`) | **CONFIRMED** | M03 (`0 ≤ lo`) FAIL l.124 (omega), l.157, l.543 |
| FiniteNet | `gcd_hw_safe_fin_chains`: every link's FEnv1 DERIVED (`fchain_env1`) | **CONFIRMED as implication; "derived" OVERSTATED** | `FInChainC` is a per-link existential chain with free end traces; end contracts hold when their conclusion does (`seg_of_clean`) |
| FiniteNetWit | joint witness on chW (a=12, b=18, out0 = 6), degenerate in 3 disclosed ways | **CONFIRMED; degeneracy beyond the journal** | `chD`: `N := 1`, end nodes = the link's own pin traces one tick early, no chain coherence; M06 (6 → 4) FAIL l.340 |
| FiniteNetMixed / MuxNNet | `gcd_hw_safe_fin_net`, `_net3`: links' H_CELLS discharged by ONE gate-level network; contracts remain ONLY on |j, 3 sources, 9 amerges | **OVERSTATED** | `fcellOK_nil_iff`, `flink_env1_local`: pinless driver contracts can carry every link's environment; drivers free (notes: "elaboration is abstract", consequence not stated); Bfin3's uncommitted witness uses exactly that |
| FiniteNetCells | truncated cell lemmas incl. ORs (`tor_ex`, `tor_witness` finite run) | **CONFIRMED** (re-check) | |
| FiniteRuns(Wit) | FEnv1/FPhysLink finite forms; joint witness of fin_links (unit delays, disclosed) | **CONFIRMED** | re-check |
| EdgeTimes / EdgeTimesNet | constructed chain solutions for every N and in-band constant delays; chain departure bounds derived | **CONFIRMED** | header NOT-covered (constant delays, concrete ends) matches |
| EdgeTimesRing | `ring_run_iff`: run iff 0 < D < N | **CONFIRMED; `0 < D` half is H_TOK (minor OVERSTATED)** | `pring_D_pos`; M02 (`D ≤ N`) FAIL l.759 (structural), l.761 (`wR_band` needs `D < N`); M08 (band hi 3 → 2) FAIL l.726 (structural `show`) |
| RingPhys* | live iff C's 3 ≤ N, 0 < D < N; N = 2 dead; refinement onto Ring | **CONFIRMED** (re-check; same H_TOK remark) | witnesses: actual delay 1 in band [1,3] (stated) |
| KleeneWinBound | +W sufficient and needed (pair reading); C-element +W+Wq; bd_c2 clean at 3, hazard at 2 | **CONFIRMED** | `races_suff/need` are one-line consequences of KleeneWin's iffs ("needed" = some pair attains W, stated). M01 (margin 2 claimed unsafe) FAIL l.145; M10 (clean at the hazard margin) FAIL l.507 |
| Necessity7Mux* | S_XA_FORK, J.1, S_A_FORK not necessary; S_XA_SEQ/S_XA_R/S_A_SEQ boundary-tight | **CONFIRMED** (binary forms, one point each, stated) | M07 (`passA5` on the slack -1 run 6) FAIL l.462 (omega), l.463 |
| AssumeGuaranteeMux / Or / Net | mux cells gate-modelled; ORs not closable by end-ordered rule (`or_not_causal`) | **CONFIRMED** (re-check) | same driver-freedom remark as net3 for `gcd_hw_safe_net2` (segment form; Bseg's note states "not the pins' drivers") |
| AssumeGuaranteeMuxN* | decode/joins/acks/trees/FASTFALL; tree/decode witnesses infinite only (stated) | **CONFIRMED** (re-check) | `tand_fin_witness`, `tmuxa_fin_witness` are finite runs |
| ArbAMerge | races Q/R/G exact per field; C's fields on handover windows | **CONFIRMED** (re-check; Bsa5-style reading) | |
| ArbAMergeRun* | `amerge_of_plan`: C's AMerge, 13 fields, H_DAT the only extra | **CONFIRMED** | (b) above; M04 (server answers in 2 ps under smin 3) FAIL l.136, l.153, l.177 (decide) |
| ArbAMergeRunWit | `amerge_witness` from reset, every epoch kind; `sep_cex_run` | **CONFIRMED, degenerate (disclosed)** | 1 ps grid, smin 3, idle forever after 300 ps, one-sided class |
| ArbCounterRuns(AM) | 1-ps violating runs for rt1, handover_overlap, six re-request races | **CONFIRMED** | M05 (D1S smin 171 → 170) FAIL l.205, l.239, l.268; off-box fields free and H_RF_ASYM needed (stated) |
| ArbSettled | unchanged since Bsa5 | **CONFIRMED** (re-check) | Bsa5 verdicts stand |

## Verdicts: cell_constraints.json (Bj9 / Bj10 / Bj11)

| row / item | claim | verdict | evidence |
|---|---|---|---|
| generator + validator | byte-identical regeneration, 0 errors, 151 rows, 38/56/10 | **CONFIRMED** | re-run |
| validator (Bj10) | every exact row cites an iff with role exact | **CONFIRMED (syntactic only)** | V1-V3 pass with unrelated / hypothesis-only iffs |
| 12 sampled exact rows | cited iff is about the row | **CONFIRMED** | (d) above |
| C-element rows (Bj9) | "+W + Wq" on the 51 C-element-backed rows | **CONFIRMED** (bd_c2.env_latency read) | `cel_env_win_bound/need` |
| bd_arbiter.rt1 (Bj11) | boundary-tight, race disjunct only, on rt1_counter_run | **CONFIRMED** | free A0 route / qf / smin disclosed |
| bd_arbcell.handover_overlap (Bj11) | boundary-tight for the deficit form; needs H_RF_ASYM | **CONFIRMED** | `ho_overlap_iff` is an iff on one constructed trace family; "= 0 at consistent corners" stays sufficient (stated) |
| rereq_Q/R/Q2/R2/G2 (Bj11), rereq_G fall view | boundary-tight on constructed runs, one C field each | **CONFIRMED** (re-check) | small-integer grid, not routed (stated) |

## Mutants (`formal/lean/Wip/Bsa6/`), all FAIL

| mutant | change | result |
|---|---|---|
| M01 KleeneWinBound | steer witness: margin 2 claimed unsafe (1001 → 1002) | FAIL l.145 (decide) |
| M02 EdgeTimesRing | `ring_run_iff` with `D ≤ N` | FAIL l.759 (structural), l.761 (`wR_band`) |
| M03 FiniteNet | `ag_trunc` with `0 ≤ lo` | FAIL l.124, l.157, l.543 |
| M04 ArbAMergeRunWit | server `A0 t = R0 (t - 2)` under smin 3 | FAIL l.136, l.153, l.177 (decide) |
| M05 ArbCounterRuns | D1S smin 171 → 170 | FAIL l.205, l.239, l.268 |
| M06 FiniteNetWit | out0 carries 4 | FAIL l.340 |
| M07 Necessity7MuxRuns | `passA5` on run 6 | FAIL l.462, l.463 |
| M08 EdgeTimesRing | witness band hi 3 → 2 | FAIL l.726 (structural `show`) |
| M09 SelfAuditB9 | `pin_of_pinless` without the pinless hypothesis | FAIL l.74 (structural) |
| M10 KleeneWinBound | `c2_win_clean` one tick earlier | FAIL l.507 |

## Summary

Nothing REFUTED; every committed in-scope file re-checks; the JSON regenerates byte-identically.
Main finding (Lean): the hypotheses of `gcd_hw_safe_fin_net` / `_net3` do not fix which cell
drives a tied cell's pin, and a pinless contract cell's contract is the bare cleanness claim,
so every link's "derived" `FEnv1` can come from private assumed drivers
(`flink_env1_local`); the gate models of forks/joins/steers/muxes need not lie on any link's
input path. "Contracts remain only on |j, sources, amerges" is the intended elaboration, not
what the theorem enforces. The chW witness of `gcd_hw_safe_fin_chains` is degenerate beyond the
journal (end nodes are the link's own pin traces; per-link chains share nothing).
`ring_run_iff`'s `0 < D` half is the hypothesis `H_TOK`. The Bj10 validator's iff check is
syntactic (three unrelated-iff mutants pass). `amerge_of_plan` instantiates C's own `AMerge`
with `H_DAT` the only extra hypothesis, on a parametric class with one unit-grid inhabitant.
