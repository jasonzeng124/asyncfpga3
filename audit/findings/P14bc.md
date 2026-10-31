# P14bc: audit of formal shards B and C, commits 5a1ee8d2..0780fd30

Code under test: clean checkout of formal commit 0780fd30 in /root/wt-f14 (read only). Auditor
files: /home/user/asyncfpga3/audit/lean/P14/BC_*. git not touched.

STATUS: final. Clean lake build of 0780fd30: EXIT 0, "Build completed successfully (3636 jobs)", 0 `error:` lines
(audit/logs/formal_build_0780fd30.log). Auditor Lean files compile (rc 0) with `lake env lean`.

## Summary table

| # | claim | verdict | one-line reason |
|---|---|---|---|
| C1 | d63d5221 TxWin indexed by occurring transactions + finite and real-gcd_hw-run DAG witnesses | CONFIRMED (repair) / OVERSTATED ("real-run DAG certificate") | `count`/`idle`/`win` now conditioned on `HasOff`; P12a row 18 obstruction gone; but `out0_dag_witness`'s obligation netlist is invented to reproduce the observed bus (BCert.dag does not bind the netlist), covers 1 of 26 roots, and phys4/phys5 still have only exempt/ghost witnesses (disclosed in journal/note, not in commit message) |
| C2 | c04f525a/0780fd30 H_COMPUTE_FN for 14/20 units, every input; shifters with e1 = 1 | CONFIRMED | statements `∀ a b`; spec = pre-existing `Ops.*`; own extractor: Lean data = committed fixture AND an independent build, cell for cell; own simulator 0 mismatches; e1 is a constant-1 token in gcd_kernel.v; INIT mutant rejected by kernel. Not linked to capstone `Join.dat` (disclosed); fixture not certified by its sha256 line |
| B1 | 8bb6d160/e20eb4cb/a0337827 Bwit joint witness of `gcd_hw_safe_fin_netB` | CONFIRMED with precision notes | genuine closed gate-level run (tied nodes drive pins of netlist-named cells, real gate functions, out0 = 6 for a=12, b=18); but one run, unit delays, width-0 windows; binding only where netlist names a B cell: 63/175 links both sides, 223 of 729 tied-cell pins driven by pinless contract cells; "112 link sides" miscount (137 sides); H_OTHER/H_BUNDLE still assumed; negative control only tests data consistency |
| B2 | fa430509/65522b83 FiniteNetBoundM 124/175, Bwit2 | CONFIRMED | census kernel-checked; no FGcdNetOKBM witness exists, as stated ("possibly vacuous") |
| B3 | 3aed4ede chW_net_not_bound; 629c4401 caveats | CONFIRMED | real proof (axioms: propext); 8 theorem-docstring caveats present; module headers of FiniteNetMixed/FiniteOrN still carry old wording |

## C1. d63d5221: "TxWin indexed by the transactions that occur (audit P12a row 18) + finite and real-gcd_hw-run DAG-certificate witnesses"

(a) Claims.
- Commit d63d5221 message (quoted above).
- JOURNAL-C.md, progress 08:45: "TxWin repair (audit row 18) + `CapstoneRefineFinWit.fin_witness`
  (finite channel, DAG BCert) + `CapstoneRefineOut0Wit.out0_dag_witness`: on C-8t's REAL gcd_hw run
  `chW`, out0 (offered once) carries a `BCert.dag` whose obligation netlist is hand-made (5 nodes,
  fixed delays, 3 bus bits; NOT the routed netlist) ... The phys4/phys5 witnesses themselves still
  use exempt/ghost on every root."
- notes/C-8x4-refine.md (row-18 answer): same, plus "Still NOT shown: tcheck's real rows meeting
  `TxWin` on a gcd_hw run; the other 25 roots; phys5's `Row` hypotheses on any gcd_hw run".
- FEASIBILITY.md goal 2, 2026-10-31 entry (written by A): "C repaired TxWin (audit P12a row 18: the
  old form forced infinitely many offers, so phys4/phys5 were vacuous on terminating runs) with a
  finite witness".

(b) Lean, in plain words.
- New `TxWin P sig data R` (CapstoneRefine.lean:200-206): `HasOff P k := ∃ r, OffAt P k r`
  (a k-th offer happens). `idle` and `count` are now required only for k with `HasOff P k`;
  `win k u` only for occurring k, and its right end `u < τ (k+1)` is required only if a (k+1)-th
  offer exists, so the LAST transaction's window runs to infinity (the bus must equal the
  obligation run's bus forever after τ_last). `reqIn` is unchanged (already conditioned on OffAt).
  `HasOff` is downward closed (cnt is monotone), so "the transactions that occur" is an initial
  segment. This removes exactly the P12a obstruction (`count : ∀ k` forced infinitely many offers).
  `off_in_win`, `sampled_eq_zd`, `idle_until`, `held_dag` re-prove with the weaker hypothesis;
  the soundness argument is preserved (the build compiles them).
- `FinWit.fin_witness` (CapstoneRefineFinWit.lean:125): a toy channel `wF`, offered exactly twice
  (`wF_hasOff_iff : HasOff wF k ↔ k < 2`), idle from 32 on, carries `BCert.dag` over the toy
  netlist `wnet` of the older periodic witness; Held + sampled = zero-delay value follow.
- `Out0Wit.out0_dag_witness` (CapstoneRefineOut0Wit.lean:205): on C-8t's run `chW` (a=12, b=18),
  `BCert (chW out0) ∧ Held (chW out0) ∧ every in-transaction sample of out0 = Nat.gcd 12 18`. The
  BCert is `BCert.dag oNet 4 [1,2,3] 0 oSig ...`; `oNet` = 4 arcs from launch node 0 (data nodes
  1,2,3 at delay [2,2], request node 4 at [5,5]); `oSig` is the run "bus bits 1,2 rise at 3, bit 0
  stays 0, request at 6"; `oG` (node functions) makes node 1 constant false and nodes 2,3 copies of
  the launch. `oX : TxWin (chW out0) oSig [1,2,3] _` with τ = 424.

(c)/(d) Findings.
1. The TxWin repair is correct and does remove P12a row 18's vacuity: with one offer, `count` and
   `idle` are demanded for k = 0 only, and `win` for k = 0 with an unbounded window. Both witnesses
   are genuine `BCert.dag` instances on finitely-offered channels; the out0 one is on the real
   chW channel (o_hasOff_iff: offered exactly once, at 429). CONFIRMED as Lean.
2. What the witness does NOT instantiate. No headline theorem's hypotheses are instantiated with a
   non-exempt certificate: `gcd_hw_circuit_safe_phys4` needs `BCert (ch c)` on all 26 roots
   (`isRoot3`, CapstoneRefine3.lean:100) jointly with H_CELLS_B and H_START_ONCE; the committed
   `gcd_hw_phys4_witness` still uses `exempt` on every root, and phys5_cls/_gen (Row hypotheses)
   still have no gcd_hw witness. `out0_dag_witness` is a single-channel statement (one of 26 roots)
   and is not plugged into phys4. This is disclosed in the journal, the note and the file's
   docstring ("Only out0 is certified this way").
3. The DAG certificate's obligation netlist is unconstrained, so `BCert.dag` on its own carries
   no physical content. `BCert.dag` (CapstoneRefineNet.lean:33-36) quantifies existentially over
   `net`, `sig`, `runs`: nothing ties `net` to the routed gcd_hw netlist, to tcheck's actual row,
   or to prjxray delays. The out0 witness shows how weak this is: `oNet`'s data nodes are constant
   functions of the launch, chosen so that the obligation bus reproduces the OBSERVED bus value 6,
   i.e. the "certificate" is a relabelling of the observed data (the same pattern as P12b's Bfin2
   chain witness). For a channel that is offered finitely often and whose bus is constant from
   some time before each offer until the next transaction, an obligation net of this shape exists,
   so on such channels `BCert.dag` is no stronger than the observed bundling it is meant to derive.
   The formal text discloses "hand-made, NOT the routed netlist", but the commit message ("real-gcd_hw-run
   DAG-certificate witnesses") reads as if a real tcheck row were certified.
4. FEASIBILITY.md's paraphrase "phys4/phys5 were vacuous on terminating runs" is itself
   inaccurate in the other direction: P12a found phys5_cls/_gen vacuous (Row forced); phys4 and
   phys5 were satisfiable with `exempt`/ghost. Minor.

Verdict C1: CONFIRMED for the repair (P12a row 18's obstruction is gone and the finite witness is
real); OVERSTATED for "real-gcd_hw-run DAG-certificate witness" in the commit message: the
certificate's netlist is invented to reproduce the observed bus, `BCert.dag` does not bind it to
the routed netlist, and no headline theorem (phys4/phys5) has a witness with a non-exempt
certificate. The journal/note text discloses both limits.

## C2. c04f525a / 0780fd30: H_COMPUTE_FN for 9 + 5 of gcd_hw's 20 compute units

(a) Claims.
- c04f525a: "H_COMPUTE_FN for 9 of gcd_hw's 20 compute units (uori0/1, ucmpi0/1/2/3/8/10, uaddi0)
  on the committed yosys netlist, for every input".
- 0780fd30: "H_COMPUTE_FN for gcd_hw's five shifters ushrsi0-4 ($signed(a) >>> 1 for every a, with
  e1 = 1 as gcd_hw feeds it)".
- JOURNAL-C.md progress 08:27 and 09:13 (same content; 09:13: "the five arithmetic shifts ushrsi0..4
  compute `$signed(a) >>> 1` for every `a` when their `e1` port carries 1 (the only value it carries
  in gcd_hw ...) ... NOT shown: other shift amounts. 14 of 20 units done").
- notes/C-hcf-compute.md (table of units, Assumed / Not covered).

(b) Lean statements (all universally quantified over Nat inputs):
- `uori0_fn (a b) : unitVal Uori0.cells Uori0.outs [a, b] = Ops.ori 32 a b` (also uori1);
  `ucmpi2_fn : ... [a, b] = Ops.cmpi .eq 1 (Ops.andi 1 a 1) b`; `ucmpi3_fn : ... = Ops.cmpi .eq 1
  (Ops.andi 1 a b) 0`; `ucmpi{0,1,8,10}_fn (a) : ... [a] = Ops.cmpi .eq 32 a 0`;
  `uaddi0_fn (a b) : ... = Ops.addi 32 a b`; `ushrsi{0..4}_fn (a) : unitVal ... [a, 1] = Ops.shrsi 32 a 1`.
- `unitVal cells outs xs` (Compute/Word.lean:47) = the number whose bit i is the evaluation of
  output wire i, with input port p bit k = `xs[p].testBit k` (`inEnv`). Evaluation (`run`,
  Compute/Basic.lean) runs the cell list in order from all-zero nets; LUT = `lutB INIT` (bit
  `Σ I_k·2^k` of INIT), MUXF = `S ? I1 : I0`, CARRY4 = shard A's `bout` with c0 = CI | CYINIT.
- The specs `Ops.ori/addi/cmpi/shrsi` are the capstone's pre-existing integer semantics
  (Formal/Net/GcdHwLib.lean:35-62), not derived from the netlist. So the spec is independent of
  the implementation (not checked against itself). `Ops.shrsi` = `~((~x) >> b)` for negative x,
  the Verilog `>>>` semantics.

(c) Auditor checks.
1. Provenance of the netlist. The Lean data (Formal/Gen/Compute/GcdD/*.lean) is extracted from
   `formal/tools/fasm2lean3/fixture/gcd_hw_d.synth.json.xz`, a hierarchical yosys netlist
   committed by shard C itself (155639fa) as a "trimmed" (non-blackbox modules) copy of the JSON
   nextpnr read. Its sha256 (decompressed: cb3fadb8...) does NOT match the `gcd_hw_d.json` line of
   `gcd_hw_d.sha256` (f0a7f326...), which presumably hashes the untrimmed file, so the fixture
   cannot be tied to the routed design by that hash. I therefore compared against an independent
   build: /root/wt-r14/cells/build/hw/gcd_hw/gcd_hw.json (synthesised 2026-10-31 08:04 with the
   audit toolchain /root/audit-tc, from `rtl/*.v ../build/gen/gcd_kernel.v hw/gcd_rig.v hw/gcd_hw.v`).
2. Transcription, own script (`audit/lean/P14/BC_netcmp.py`, written from scratch, does not use
   extract.py): for each unit it parses the Lean `cells`/`outs`, finds the yosys cell driving each
   output net, and compares cell type, LUT INIT (as an integer), every pin I0..In / MUXF I0,I1,S /
   CARRY4 CI, CYINIT, DI, S, O, CO, the output bit order, and checks that the Lean cell set equals
   the whole combinational cone of z_data. Result: all 14 units (uori0, uori1, ucmpi0/1/2/3/8/10,
   uaddi0, ushrsi0-4) match the committed fixture exactly; uori0, ucmpi0, uaddi0, ushrsi0, ushrsi3
   also match the independent wt-r14 build exactly (same INITs, same net numbers). Cone sizes
   (LUT, CARRY4, MUXF): uori 32/0/0, ucmpi2/3 2/0/0, ucmpi0/1/8/10 6/0/12, uaddi0 32/8/0,
   ushrsi 215/0/179.
3. Independent semantics: the same script simulates each yosys module recursively (own LUT,
   MUXF and UNISIM CARRY4 semantics) on 3000 random vectors per unit against a Python spec
   written from bdc's Verilog (`$signed(e0) >>> e1`, `e0 | e1`, `(e0 & 1'h1) == e1`,
   `(e0 & e1) == 0`, `e0 == 0`, `e0 + e1`, read in /root/wt-r14/build/gen/gcd_kernel.v): 0
   mismatches for every unit; the shifters also match `>>>` for random shift amounts 0..31
   (so the e1 = 1 restriction is a proof-method limit, not a netlist defect).
4. RTL check of "e1 = 1 as gcd_hw feeds it": in gcd_kernel.v every ushrsi's e1 comes from a
   `bd_link` whose input is a fork of a channel with `assign nXX_data = 32'h1` (ushrsi0/1 from
   n35 via fork n36, ushrsi2 from n67/n68, ushrsi3 from n93/n94, ushrsi4 from n154/n155). So e1 is
   1 in every token gcd_hw offers; at the token level the hypothesis is justified. (The latch
   content before the first token is not 1, but no token is consumed then.)
5. Lean (BC_ComputeMut.lean, rc 0): `#check` confirms the four statement shapes quoted in (b);
   axioms of all nine headline theorems checked are within [propext, Classical.choice,
   Quot.sound]; mutation: uori0's bit-5 LUT INIT 14 (OR) -> 6 (XOR) gives
   `uori0_mut_rejected : ¬ BitLocal mutCells Uori0.outs orS orSpec` by `decide +kernel` (axioms
   propext, Quot.sound), and `#eval` shows the mutant computes 0 instead of 32 at a = b = 32.
   Spot evaluations of the Lean evaluator (ucmpi0, uori1) agree with the Python simulator. (An
   `#eval` of the shifter/adder cones did not finish in 20 min: `run` is closure-based and
   exponential under `#eval`; their proofs use cut points, so this does not affect them.)

(d) Wording. "e1 = 1" is stated in the commit message, the journal (09:13) and each
Compute/GcdShrsi*.lean docstring ("NOT shown: other shift amounts"). notes/C-hcf-compute.md was
NOT updated by 0780fd30: it still lists ushrsi0-4 under "Not covered" (stale, conservative), and
out/gcd_hw_hypotheses.md:101 and FEASIBILITY.md:163 still say H_COMPUTE_FN is "open"/"not
proved" (also conservative). No place repeats the shifter claim without "e1 = 1". The remaining
scope limits are disclosed in the note: Boolean function only (no timing, glitches, X), shard
A's primitive models, and no link from these unit theorems to the capstone's `Join.dat` (the
RTL-unit <-> Ops-join map), so the capstone still assumes H_COMPUTE_FN as before.

Verdict C2: CONFIRMED (14 of 20 units: transcription exact against the committed fixture and an
independent build; quantifier is over every input; spec independent; e1 = 1 justified by the RTL
and stated wherever the shifter claim appears). Caveats: the unit theorems are not yet connected
to the capstone (H_COMPUTE_FN remains an assumption of every capstone theorem), and the fixture's
own sha256 line does not certify it (independent build used instead).

## B1. 8bb6d160 / e20eb4cb / a0337827: Bwit, joint witness of the driver-bound theorem

(a) Claims.
- 8bb6d160: "Bwit -- joint witness of the driver-bound gate-level gcd_hw theorem
  (gcd_hw_fin_netB_witness): tied cells drive the network through netlist-named wires on a
  gate-timed run that also meets C's hypotheses; out0 = 6."
- e20eb4cb: "gate-timed gcd_hw run chB meets C's H_CELLS/H_BUNDLE/H_START_ONCE/H_CM_FORCED jointly".
- a0337827: "Bwit negative control (wire delay mutant rejected by kernel)"; JOURNAL-B: "channel
  20's request wire delay 2 -> 1 in BWitNData makes bw_c1 fail by kernel".
- JOURNAL-B status table (Phase 3 row): "FiniteNetBound.FGcdNetOKB binds every tied pin's driver
  to the cell the netlist names (63/175 links bound on both sides); gcd_hw_safe_fin_netB has a
  JOINT WITNESS on a gate-timed run in which the tied cells drive each other".
- FEASIBILITY.md goal 2 (A, 2026-10-31): "`gcd_hw_safe_fin_netB` (every tied cell's pins driven by
  the netlist-named cell) now has a joint witness (... one run a=12, b=18, unit LUT delay, wire
  delays 1-3, out0 latches 6); C's H_OTHER for the 192 non-link operators is still a hypothesis."

(b) What the Lean says, in plain words.
- `gcd_hw_safe_fin_netB a b ch N L n H H_OTHER H_BUNDLE H_CM_FORCED` (FiniteNetBound.lean:362):
  IF (H) there is a gate-level elaboration N of gcd_hw on the channel traces `ch` in which every
  link, 2..4-way fork acknowledge C-element, 2-input join request C-element, steer branch and
  steer acknowledge OR satisfies B's gate model (finite edge counts, H_TIMES at existing edges,
  wires, departure bounds), every pin of these cells whose driver the netlist determines
  (`reqSrc`/`ackSrc`) has exactly that cell as `drv`, every other cell meets its truncated
  contract (H_REST); AND C's operator model `Cell` holds for all 192 non-link operators
  (H_OTHER); AND every channel is bundled (H_BUNDLE: `Held`, assumed); AND C's H_CM_FORCED;
  THEN every out0 token carries gcd a b. The proof is the old `gcd_hw_safe_fin_net` applied to
  the forgetful `H.toOK`: the binding restricts the hypothesis and adds no derivation (stated in
  the note).
- `gcd_hw_fin_netB_witness` (BWitNet.lean:333): there EXIST ch, N, L, n with FGcdNetOKB, H_OTHER,
  H_BUNDLE and H_CM_FORCED for a = 12, b = 18 (A0/B0, CapstoneWitnessData.lean:24-25), and out0 has
  a token (k = 0, closing at t = 585) carrying 6. The witness is ch = chB (BWitData, generated by
  tools-B/bwit/gen_cdata.py from a Python simulation), N = NBn (BWitNDefs): each tied cell's node
  is the event list of the channel signal it drives (one tick earlier), each pin's trace is the
  channel signal, and `wireChk` (kernel, BWitNChk) checks that this trace is the netlist-named
  driver's node shifted by the declared wire delay wR/wA in {1,2,3}. `opChkB` (kernel) runs B's
  checkers (linkB, celB with cel2/3/4, stB, orB) on the real gate functions. C's checkers (kChk,
  heldChk) give H_OTHER (in fact all 367 operators) and H_BUNDLE on chB.

(c)/(d) Findings. Census by the auditor (BC_BwitCensus.lean, `#eval` on their definitions, rc 0):
- tied cells with pins: 391; their pins: 729, of which 506 driven by tied cells and 223 (31%)
  driven by pinless contract cells; channels whose request driver the netlist leaves to a contract
  cell: 140 of 465; acknowledge: 123 of 465;
- wire delays: request 438 x1, 24 x2, 3 x3; acknowledge 377 x1, 86 x2, 2 x3;
- activity: 1126 request edges in total, 407 of 465 channels toggle, last edge at 584; out0
  request edges [530, 584], acknowledge [531, 585]: one token, value 6;
- negative controls (kernel): `orig_20 : wireChk 20 = true`, `mut_20 : wireChk' 20 = false`
  (channel 20 request wire 2 -> 1, the journal's mutant, reproduced without editing their data);
  gate mutant: fork op 0 (outputs = channels 3, 4) `fork0_orig : celB Gf2 ... = true` and
  `fork0_mut_or : celB GfOr ... = false` (the same traces fail when the C-element is replaced by
  an OR), so the gate checks discriminate the gate function;
- axioms: gcd_hw_fin_netB_witness, gcd_hw_fin_netB_consistent, bwit_ok, gcd_hw_safe_fin_netB:
  [propext, Classical.choice, Quot.sound]; Rej.chW_net_not_bound: [propext].

1. Not degenerate in the sense asked. Cells are not "tied to constants": "tied" means a gate-model
   cell whose pins are tied to C's channel traces. In the witness each tied cell's output node IS
   the channel signal it drives, and each of its pins is (kernel-checked) the node of the cell the
   netlist names, delayed by wR/wA. So links feed links, steer branches feed links, fork
   C-elements feed link acknowledges, etc., in one closed simulated run that the gate checkers
   (real cel2/cel3/cel4, bd_steer OR, link LUT functions) accept, and C's operator models hold on
   the same traces; the computation reaches out0 = 6 = gcd(12, 18) at t = 585. This is a genuine
   improvement over Bfin3's relabelling (P12b): `Rej.chW_net_not_bound` proves the old chW network
   violates the binding.
2. Degenerate in the disclosed ways: one run, one input pair (12, 18); all LUT delays lo = hi = 1,
   wire delays fixed (1..3) with windows of width 0, so no delay band is exercised; R = 2.
3. Coverage of the binding. The binding is enforced only where `reqSrc`/`ackSrc` return a cell:
   63/175 links are bound on both sides (kernel census `bound_census`: 63 both, 64 request only,
   23 acknowledge only, 25 neither). Unbound link SIDES = 64 + 23 + 2*25 = 137. The BWitNet
   docstring and JOURNAL-B 08:12 say "the 112 link sides `bound_census` counts as unbound"; 112 is
   the number of LINKS not bound on both sides (175 - 63), not of sides. Miscount (minor). On
   those sides, and on every pin whose netlist driver is a mux, muxn, amerge, source, sink, wide
   join or fork tree, the driver is a pinless contract cell (`rq c`/`ak c`) whose contract holds
   because its node is clean (`cell_okB`), i.e. the old P12b weakness persists there (disclosed
   as item (ii) in BWitNet's docstring).
4. The commit message and the status table give the 63/175 figure (status table) or none (commit);
   FEASIBILITY.md's paraphrase "(every tied cell's pins driven by the netlist-named cell)" omits
   "where the netlist names a B cell" and the 63/175 figure; read literally it overstates (A's
   paraphrase, marked "not re-checked by A").
5. What the theorem still assumes, also on the witness: H_OTHER (C's `Cell` for the 192 non-link
   operators) and H_BUNDLE (`Held` on every channel) are hypotheses; on chB they are discharged by
   C's checkers on that single run, not by B's gate models. The gate-level network is used only
   to derive the links' `Cell` (`toOK` -> `gcd_hw_safe_fin_net`); in the witness even that is
   redundant, since `b_cells` gives C's `Cell` for all 367 operators including links. Disclosed
   (item (iv) and the note).
6. Negative control (a0337827). It is journal-only (no committed file). I reproduced it without
   editing their tree (BC_BwitCensus.lean: `wireChk'` with channel 20's request wire 2 -> 1):
   result below. It is a real mutation of the witness data and makes the witness proof fail
   (bw_c1 -> bwit_ok), but it tests only the consistency of the declared wire delay with the
   pre-computed traces; it cannot "break the theorem" (an implication) and it does not test that
   the gate checks or the binding reject a wrong circuit. The binding side is covered by
   `chW_net_not_bound`; for the gate side my fork mutant (C-element checked as OR) is rejected.

Plain words of `gcd_hw_fin_netB_witness`: "for a = 12, b = 18 there is ONE concrete set of
finite channel traces and ONE gate-level elaboration such that: every link / small fork / 2-input
join / steer cell obeys its LUT gate function with delay exactly 1, reading its inputs through
wires of fixed delay 1-3 from the cells the netlist names (or from a free contract cell where the
netlist names a mux, amerge, source, sink, wide join or fork tree); C's operator models and
bundling hold on the same traces; and out0 delivers one token with value 6."

Verdict B1: CONFIRMED that the driver-bound theorem is jointly satisfiable by a real
(non-relabelled) gate-level run; OVERSTATED only in details: "112 link sides" (137), and
FEASIBILITY's "every tied cell's pins driven by the netlist-named cell" without the 63/175 and
contract-cell (223/729 pins) qualification. The single-run / unit-delay / width-0-window /
H_OTHER / H_BUNDLE limits are disclosed.

## B2. fa430509 / 65522b83: FiniteNetBoundM (124/175) and Bwit2

(a) fa430509: "FiniteNetBoundM -- muxes gate-modelled and bound (124/175 links bound both sides,
kernel census); gcd_hw_safe_fin_netBM, NO witness yet"; 65522b83: "Bwit2 steps 2-3 --
mux-gate-modelled run chB2 meets C's hypotheses (BWit2Cells, kernel); mux cell checkers
bufB/mjB/maB with soundness (BWit2Lib)". JOURNAL-B 08:41: "NOT yet: a joint witness of
FGcdNetOKBM ... Until then gcd_hw_safe_fin_netBM is reported as possibly vacuous."

(b)/(d) `bound_censusM` (FiniteNetBoundM.lean:309-312, kernel): 124 both, 25 request only, 25
acknowledge only, 1 neither. BWit2Cells proves only C's hypotheses on the run chB2 (`b_cells`,
`b_held`, `b_forced`, `b_out0`) and BWit2Lib proves soundness lemmas of the mux checkers; no file
instantiates `FGcdNetOKBM` (grep: the name occurs only in FiniteNetBoundM.lean). So at HEAD
`gcd_hw_safe_fin_netBM` has NO witness, exactly as stated. The headline "124/175" therefore belongs
to a theorem that may be vacuous; the witnessed theorem is the 63/175 one. The prose says so in
fa430509 and the journal; the 65522b83 message does not claim an FGcdNetOKBM witness.
Verdict B2: CONFIRMED (accurately scoped; "Bwit2 step 3" is checker soundness, not a witness).

## B3. 3aed4ede chW_net_not_bound and 629c4401 docstring caveats

- `Rej.chW_net_not_bound : ¬ FGcdNetOKB chW NW LW nW` (BWitNet.lean:362): link 194 reads channel
  13 (`lkIO`, kernel), the netlist names link 193 as channel 13's request driver (`reqSrc`, kernel),
  while Bfin3's network has pin list `[pR 13, ...]` whose driver is the contract cell `rq 13`; the
  constructor mismatch `Cl.rq _ = Cl.lk _` closes it. A genuine proof that the binding excludes
  the P12b relabelling, for the specific witness `fgcdNetOK_chW`. CONFIRMED.
- 629c4401: CAVEAT paragraphs added to exactly 8 theorem docstrings (AssumeGuaranteeCap:146,
  AssumeGuaranteeEndsCap:220, AssumeGuaranteeMuxNNet:199 and :332, AssumeGuaranteeMuxNet:430,
  FiniteNet:646, FiniteNetMixed:395, FiniteOrN:452); the JOURNAL-B status table preamble now says
  151/38/56/10 and the Phase 3 row carries the driver caveat. Residual: the old wording ("every
  cell carries B's gate model except ...", "contracts remain on ...") is kept in front of each
  caveat, and the MODULE headers FiniteNetMixed.lean:20-26 and FiniteOrN.lean:28-35 still carry
  it with no caveat in that bullet. Minor. CONFIRMED (with that nit).

## Auditor files and runs

All run after the clean build (EXIT 0) with
`export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH; cd /root/wt-f14/formal/lean && lake env lean <file>`,
one process at a time. Outputs saved next to each file (`.out`).

| file | purpose | exit |
|---|---|---|
| audit/lean/P14/BC_TxWinAxioms.lean | C1: new `TxWin.count` statement, `out0_dag_witness` statement, axioms (out0_dag_witness, fin_witness, out0_dag_cert: propext, Classical.choice, Quot.sound) | 0 |
| audit/lean/P14/BC_ComputeMut.lean | C2: statement shapes, axioms, uori0 INIT mutant rejected (kernel), Lean-vs-Python spot evaluations | 0 |
| audit/lean/P14/BC_BwitCensus.lean | B1/B3: axioms, pin/driver census, wire-delay histogram, activity, wire-delay mutant and fork-OR gate mutant (kernel) | 0 |
| audit/lean/P14/BC_netcmp.py | C2: independent extraction/compare of Lean unit data vs yosys JSON + independent simulation (`python3 -I BC_netcmp.py <synth.json> <GcdD dir> <units...>`), run on the fixture and on /root/wt-r14/cells/build/hw/gcd_hw/gcd_hw.json | 0 |

No sorry, no native_decide in the audited files' axioms (all within propext / Classical.choice /
Quot.sound).

## Auditor's re-check (main session)
- Re-ran BC_BwitCensus.lean, BC_ComputeMut.lean, BC_TxWinAxioms.lean: rc 0 each, no errors, no sorry.
- Read CapstoneRefineOut0Wit.lean:100-235 myself. oNet/oG is a 5-node chain (v1 := false, v2 := p1, v3 := p2,
  v4 := p3) with oSig fixing data bits 1,2,3 to 0,1,1, so zdBus = 6 by construction (o_zdBus). The certificate
  netlist is not the gcd_hw datapath, so the relabelling finding is CONFIRMED.
- The fixture "hash mismatch" in C2 is NOT a defect. trim.py:5/32 writes gcd_hw_<s>.synth.json containing only
  non-blackbox modules, while the .sha256 json line is the untrimmed nextpnr input, so they cannot match. The fasm
  and fromBit.fasm hashes match (b73e1ba0, a93664d1). Withdrawn as a caveat.
