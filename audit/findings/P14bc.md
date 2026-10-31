# P14bc: audit of formal shards B and C, commits 5a1ee8d2..0780fd30

Code under test: clean checkout of formal commit 0780fd30 in /root/wt-f14 (read only). Auditor
files: /home/user/asyncfpga3/audit/lean/P14/BC_*. git not touched.

STATUS: in progress (sections are written as each claim is finished).

## Summary table

(filled at the end)

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
5. Lean mutation (BC_ComputeMut.lean, results below): uori0's bit-5 LUT INIT 14 (OR) changed to 6
   (XOR) is rejected by the kernel certificate.

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
