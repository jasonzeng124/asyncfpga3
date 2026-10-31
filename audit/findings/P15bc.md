# P15bc: audit of formal shards B and C, commits 0780fd30..f40e003a

Code under test: checkout of formal commit f40e003a in /root/wt-f14 (read only). Auditor files:
/home/user/asyncfpga3/audit/lean/P15/BC_*. git not touched.

STATUS: final.

Build: `lake build` of f40e003a (log /root/formal_build_f40e003a.log) ended **EXIT 1**. The only failure is
`Formal.Cells.BWitNChk`: "Lean exited with code 137" (OOM kill while BWit2NChk built in parallel; not a Lean
error); its sole dependent `BWitNet` was skipped. Every other module built, including all `Formal/Net/Compute/*`,
`GcdJoin`, `FiniteNetBoundM(Census)`, `BWit2NChk`, `BWit2Net`. I then compiled `BWitNChk.lean` and
`BWitNet.lean` myself (`lean -o` into a scratchpad olean overlay, nothing written into /root/wt-f14):
both rc 0; `gcd_hw_fin_netB_witness`, `bwit_ok`: axioms [propext, Classical.choice, Quot.sound]. Nothing
imports BWitNet, so the whole tree checks. The auditor files below were run after the build with
`lake env lean`, one process at a time.

## Summary table

| # | claim | verdict | one-line reason |
|---|---|---|---|
| C1 | e6f97308/502da4fe: H_COMPUTE_FN for all 20 gcd_hw units (ushli0 for k<32), every input | **CONFIRMED** | statements `∀` inputs against the capstone's pre-existing `Ops` (axioms standard); own extractor: all 20 Lean netlists = committed fixture AND the independent build, cell for cell; own simulator 0 mismatches against specs written from bdc's Verilog; k<32 stated everywhere and justified by the MLIR (k ≤ 31 for any nonzero 32-bit a, b), but not proved in Lean |
| C2 | e6f97308: GcdJoin "20 joins = unit functions" | **CONFIRMED as stated; does NOT link H_COMPUTE_FN into the capstone** | 20 equalities `jgAt p xs = unitVal U ports`, port constants match the RTL; `jgAt` agrees with my own reading of cf.mlir on 3560 vectors. GcdJoin is imported by nothing; every capstone theorem still takes `H_CELLS` whose join clause is `Join.Join (jg e js)`, i.e. still assumes H_COMPUTE_FN |
| C3 | d699b3b8: xorshift's 5 units, every input | **CONFIRMED** (fixture level) | Lean = committed xorshift fixture (4 seeds md5-identical), 0 sim mismatches against xorshift.c; no independent xorshift synthesis to compare with |
| C4 | 927ece3d/85f065da: Wip/Chcf/Neg.lean, both mutations falsify | **CONFIRMED** (narrow) | ran it: rc 0, silent; the mutated LUT patterns occur once and the originals pass, so the mutants are real; but they test only the BitLocal and AddOK-slice kinds (already tested in P14). My controls for the NEW kinds (Slt sign bit, FixShOK pin swap) are also rejected |
| B1 | 6a490ebd/22c1807e: Bwit2 joint witness; 124 -> 136/175 links bound both sides | **CONFIRMED (witness, counts) / OVERSTATED (one modelling sentence)** | the HEAD witness is of the 136 version (its drivers come from HEAD `reqSrcM`); own Python census reproduces 63, 124, 136; but 2 of the 12 newly bound links (233, 234) are bound by tracing a REQUEST back through the 1-input joins 41/43 (ushrsi0/1), which the emitted Verilog drives by a 32-LUT gated delay chain after a 2-input C-element, not by a wire ("1-input join is a wire both ways, it has no cell" is false on the request side). RTL-faithful: 134/175. notes/ still say 124 (stale) |
| B2 | e722adbf: 39 unbound sides (amerge 28, muxn 4, fork trees 6, source 1) | **CONFIRMED** | kernel theorems (axioms [propext]); reproduced exactly by own census (req: amerge 23, src 1; ack: muxn 4, amerge 5, forkH5 4, forkH6 2) |
| B3 | 076af340: steer/mux selects bound to bit 0 of the control bus; both witnesses meet it | **CONFIRMED** | `H_STEER`/`H_MUXJ` now require `s = fun t => (ch j).dat t % 2 == 1`; both witnesses discharge it by `rfl`; BWit2Net built by lake, BWitNet checked by my own compile (the lake build OOM-killed it) |
| B4 | f5040d10: Bwit2 negative control rejected by kernel | **CONFIRMED** (data-consistency control) | reproduced without editing their tree: mux 37's first uj0 edge 46 -> 47 makes the mux check false, the original is true; my gate mutation (select polarity inverted) is rejected too. As in P14, a control on witness data cannot refute an implication |

## C1. H_COMPUTE_FN for the 20 gcd_hw units (502da4fe, e6f97308)

(a) Claims. 502da4fe: "H_COMPUTE_FN for uori2/3/4, uselect0, uselect1 (signed compare, abs difference) on
gcd_hw's synthesis, every input; 19/20 units claimed". e6f97308: "H_COMPUTE_FN complete for gcd_hw (ushli0
for k<32)". JOURNAL-C 10:36: "ushli0 computes `e0 << k` for every e0 and every k < 32". notes/C-hcf-compute.md
table (all 20 units, ranges).

(b) Lean (printed by BC_GcdJoin.lean):
- `uori2_fn (a b c d) : unitVal Uori2.cells Uori2.outs [a,b,c,d] = Ops.ori 1 (Ops.cmpi .ne 1 (Ops.andi 1 c d) 0) (Ops.cmpi .slt 32 a b)` (same for uori3, uori4);
- `uselect0_fn (a b) : … = (if Ops.flip 32 a < Ops.flip 32 b then a else b) % 2^32`;
- `uselect1_fn (a b) : … = Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295) (Ops.subi 32 a b) (Ops.subi 32 0 (Ops.subi 32 a b))`;
- `ushli0_fn (a k) (hk : k < 32) : … [a, k] = Ops.shli 32 a k`.
In words: for every input value (k < 32 for the shifter), the evaluation of the unit's z_data cone, as yosys
mapped it, equals the capstone's integer semantics of the op. The specs are the pre-existing `GcdHw.Ops`
(GcdHwLib.lean:35-62; uselect0's is inline `flip`-compare + mod, which `j117` ties to `Ops.select/cmpi`), not
derived from the netlist. Axioms: uselect1_fn, uori3_fn, uori4_fn [propext, Classical.choice, Quot.sound];
ushli0_fn [propext, Quot.sound].

(c) Own checks.
1. Transcription (BC_netcmp2.py, extends P14's BC_netcmp.py: INV cells, CARRY4 with unconnected O, 4-port
   units; does not use formal's extract.py). For each unit: the yosys cell driving each Lean output net,
   type, INIT, every pin, output order, and Lean cell set = the whole z_data cone. **All 20 units match the
   committed fixture** (`gcd_hw_d.synth.json`, md5 e81e3f53; the 4 seeds' synth JSONs are md5-identical, so
   "holds for all four routes' logical netlist" is right) **and the independent build**
   /root/wt-r14/cells/build/hw/gcd_hw/gcd_hw.json (research flow, BQ#2 recipe, seed-5 route; same synthesis
   for any seed), with identical INITs and net numbers. Cone sizes (LUT/CARRY4/MUXF/INV): uori2-4 29/3/0/0,
   uselect0 58/3/0/0, uselect1 71/18/0/32, ushli0 192/0/220/0.
2. Semantics: own recursive simulation of each yosys module (own LUT/MUXF/INV/UNISIM CARRY4) on 4000 random +
   corner vectors per unit against specs written from bdc's Verilog in gcd_kernel.v
   (`((e2&e3)!=0) | slt(e0,e1)`, `slt ? e0 : e1`, `d=e0-e1; d > -1 ? d : 0-d`, `e0 << e1`, …): 0 mismatches
   for all 20 units on both netlists. The harness detects wrong specs (BC_netcmp2_negctl.py: unsigned
   compare/absdiff, k+1 shift: 260-989 mismatches per 1000).
3. ushli0 outside the proved range: the netlist also gives the Verilog value 0 for k >= 32 (0/500
   mismatches), so `k < 32` is a proof-method limit, not a netlist defect.
4. Is k < 32 justified by how gcd_hw drives it? From bdc's cf.mlir: k = %14 is 0 if (a|b) is odd, else the
   number of bb3 iterations, each shifting both operands right (arithmetic) once while both stay even;
   bb0/bb1 exit before the shift when a = 0 or b = 0. For nonzero 32-bit a, b the loop runs min(tz a, tz b)
   <= 31 times (an arithmetic shift of a nonzero value stays nonzero), so k <= 31 for EVERY 32-bit input
   pair, and <= 30 under the capstone's a, b < 2^31. The fact is not proved in Lean (the GcdShli0 docstring
   says so: "a token-level fact not restated here"). The restriction is stated in the commit headline, the
   journal, the note's table and Not-covered list, GcdShli0's docstring, GcdJoin's docstring and `j162`'s
   hypothesis; I found no place that repeats the ushli0 claim without it.

(d) Verdict C1: **CONFIRMED.** Stale but conservative: out/gcd_hw_hypotheses.md:103 still grades
H_COMPUTE_FN "B … open" and FEASIBILITY.md:182 says "not proved" (shard A's files; the FOR SHARD A text in
JOURNAL-C 09:22 is not yet applied).

## C2. GcdJoin: "20 joins = unit functions" (e6f97308)

(a) Claim: "GcdJoin (20 joins = unit functions)"; JOURNAL-C 10:36: "`GcdJoin.j2..j162`: each of the capstone
network's 20 join functions `jg e js` equals the function of the unit with that operation, on bdc's port
wiring (32-bit tokens for uselect0, shift < 32 for ushli0). `joins_listed`: the capstone has exactly those
20 joins."

(b) Precisely: for each of the 20 `K.join` operators p of the capstone's `ops`, `jgAt p xs` (its data
function `jg e js`, CapstoneNetDef.lean:256) equals `unitVal U.cells U.outs ports` where `ports` puts the
join's inputs on the unit's ports and the folded constants on the others, e.g.
`j27 : jgAt 27 [v, w] = unitVal Ucmpi2 … [Ops.trunci 1 v, 0]`, `j66 : jgAt 66 [v, w] = unitVal Uori2 … [v, 1, Ops.trunci 1 w, 1]`,
`j117 (hv : v < 2^32) (hw : w < 2^32)`, `j162 (hw : w < 32)`. `joins_listed` (kernel): the `.join` operators
are exactly [2, 13, 26, 27, 41, 43, 45, 46, 47, 66, 68, 87, 89, 104, 117, 118, 135, 142, 144, 162].
Axioms: j2…j135 [propext, Classical.choice, Quot.sound], j162 [propext, Quot.sound], joins_listed [propext].

(c) Own checks.
1. The capstone's 38 `bjoin`s are not compute units (steer-internal joins `bg ec ed = 2·d + c%2`); the RTL
   top has exactly 20 `bdc_fused_*` instances, so "20" is right.
2. Port constants against the RTL (BC_constports.py traces each e-port of each `bdc_fused_*` instance in
   gcd_kernel.v back through assigns and bd_link data paths): ucmpi2 e1 = 1'h0; ucmpi3 e1 = 1'h1; ushrsi0-4,
   uaddi0 e1 = 32'h1; uori2/3/4 e1 = 32'h1, e3 = 1'h1; ucmpi2/3 e0 and uori2-4 e2 are bit-0 slices. All agree
   with the constants and `trunci 1` placements in j27/j47/j41…/j45/j66/j87/j142. (Outside Lean; GcdJoin
   lists "the constant ports carry those constants" as not shown.)
3. Independent spec of `jg`: BC_GcdJoin.lean evaluates `jgAt p` on 3560 vectors (corner + mixed values,
   k in {0,1,2,5,17,30,31} for 162) against my own 32-bit reading of cf.mlir (written without `Ops`):
   **0 mismatches**. So the capstone's join functions are bdc's ops, and with C1 the units compute them.
4. Pairing (H_MAP): units of the same op class have identical netlists and each is proved separately, so
   pairing by operation cannot pick a wrong function; the RTL-net to Ops-channel map is not in Lean
   (disclosed).
5. **Link to the capstone: none.** `grep` finds no importer of `Formal.Net.Compute.GcdJoin` and no use of
   `jgAt`. The capstone theorems (`gcd_hw_circuit_safe3`, CapstoneWalk.lean:636; `gcd_hw_circuit_safe3B`,
   CapstoneRefine2Cut.lean:420; B's `gcd_hw_safe_fin_netB(M)`) take `H_CELLS : ∀ o, Cell ch (srcV a b) (opAt o)`,
   whose join clause is `Join.Join (jg e js) (ins.map ch) (ch o)` (CapstoneNetDef.lean:376): the physical
   join's output data is still ASSUMED to be `jg` of its inputs. That assumption is H_COMPUTE_FN in the
   capstone's own terms; P14's caveat stands. What GcdJoin does is reduce its content to: (i) the physical
   unit outputs `unitVal` of its yosys netlist (shard A's primitive Boolean models, placed = yosys netlist via
   11f/11g, settling inside the matched delay = H_COMPUTE_DELAY); (ii) the constant ports carry the folded
   constants (RTL-true, check 2); (iii) the range side conditions at joins 117 (32-bit tokens) and 162
   (k < 32), true by the MLIR argument of C1 item 4 but not derived from the capstone's walk in Lean. No theorem combines
   these into the capstone. The commit message and journal do not claim a capstone discharge; the proposed
   row text for A ("**A for the function**") should keep "not linked to the capstone's H_CELLS".

(d) Verdict C2: **CONFIRMED** for the equalities as stated; **the capstone does NOT discharge H_COMPUTE_FN**
(no theorem; remaining hypotheses: H_CELLS' join clause itself, i.e. (i)-(iii) above, plus H_BUNDLE,
H_START_ONCE as before).

## C3. xorshift's 5 units (d699b3b8)

(a) "H_COMPUTE_FN for xorshift's 5 compute units (add 1, signed >/<, two xor-shift units), every input".
(b) `xs_uaddi0_fn (a) : … [a] = Ops.addi 32 a 1`; `xs_ucmpi0_fn (a b) : … = Ops.cmpi .sgt 32 a b`;
`xs_ucmpi1_fn : … = Ops.cmpi .slt 32 a b`; `xs_uxori2_fn (a) : … = Ops.xori 32 a (Ops.shli 32 a 5)`;
`xs_uxori1_fn (a) : … = xori (xori a (shli a 13)) (shrui (xori a (shli a 13)) 17)`. Axioms standard.
(c) BC_netcmp2.py --xs on `xorshift_1.synth.json` (md5 9d030789, identical for the 4 seeds): all 5 Lean
netlists equal their yosys cones; simulation 0/4000 mismatches against specs from kernels/xorshift/xorshift.c
(x ^ x<<13, ^ x>>17 logical, ^ x<<5; signed compares; +1). No independent xorshift synthesis was available, so
transcription is checked against their fixture only.
(d) **CONFIRMED** (fixture level). It is a second design on the same machinery; no link to any xorshift
capstone is claimed.

## C4. Negative controls Wip/Chcf/Neg.lean (927ece3d, 85f065da)

(a) "Wip/Chcf/Neg.lean … (ran rc 0: both mutations falsify their certificates)"; JOURNAL-C 09:46: uori0
bit 3 OR LUT -> AND (INIT 14 -> 8) makes `BitLocal` false; uaddi0 bit 5 XOR -> XNOR (INIT 6 -> 9) makes the
bit-5 slice check false; "The controls cover two units, not every certificate kind."
(c) Wip/ is excluded from lake (lakefile `globs = ["Formal", "Formal.+"]`). I ran
`lake env lean Wip/Chcf/Neg.lean`: rc 0, no output (the two `example`s are kernel-checked). Each mutated
pattern occurs exactly once in the generated data (grep), and the original data satisfies the same checks
(`uori0_cert`, `AddBit 5` in GcdAdd), so both mutants are genuine one-LUT function changes that the checks
reject. They exercise only the BitLocal and AddOK-slice kinds, which P14 already tested. My controls for the
new kinds (BC_NegNew.lean, rc 0):
- Slt: uori2 with e0[31]/e1[31] exchanged at every LUT pin (signed -> unsigned on the sign bit):
  `aud_uori2_orig_gt : NetOK Uori2.cells [] 79 (grpS 29 3) (gtSpecG 29 3)` and
  `aud_uori2_sw_rejected : ¬ NetOK uori2Sw [] 79 …` (kernel);
- FixShOK: ushli0 LUT 76 with shift-amount pins I2/I3 swapped (Python: changes bit 5 for k in {4,5,8,9}):
  `aud_ush_mut_k0_b5_holds : ShlBitM 0 5`, `aud_ush_mut_k4_b5_rejected : ¬ ShlBitM 4 5`, while formal's
  `shl_k4_b5 : ShlBit0 4 5` holds on the original.
(d) **CONFIRMED** (narrow scope, as disclosed).

## B1. Bwit2 and the 124 -> 136 census (6a490ebd, 22c1807e)

(a) 6a490ebd: "Bwit2 -- joint witness of the mux-extended driver-bound gcd_hw theorem (124/175 links bound
both sides): all link/fork/join/steer/OR and bd_mux cells drive each other on a gate-timed run that meets C's
hypotheses; out0 = 6". 22c1807e: "bound drivers traced through 1-input joins (wires): 136/175 links bound both
sides, 0 neither; mux-extended witness re-checks". FiniteNetBoundM docstring (HEAD): "a 1-input join is a
wire both ways in the emitted Verilog (it has no cell)". JOURNAL-B status table: "136/175 links bound both
sides; joint witness on one gate-timed run".

(b) Plain words of `gcd_hw_fin_netBM_witness`: for a = 12, b = 18 there is one concrete set of finite channel
traces `chB` and one gate-level elaboration `NBm` such that every link, 2-4-way fork C-element, 2-input join
C-element, steer branch, steer OR and every bd_mux's 7 cells (2 joins, 2 acks, uor, 2 udly buffers) obey their
gate functions with delay exactly 1 (R = 2), each of their pins being the node of the cell `reqSrcM`/`ackSrcM`
names, delayed by a fixed wire of 1-3 ticks (or a pinless contract cell where those return none: amerge,
muxn, fork trees N>=5, source); steer/mux selects are bit 0 of the control bus; C's operator models (all
non-link operators), bundling (`Held`) and H_CM_FORCED hold on the same traces; out0 carries one token of
value 6. `gcd_hw_safe_fin_netBM` (the implication) concludes every out0 token = gcd a b from FGcdNetOKBM +
H_OTHER + H_BUNDLE + H_CM_FORCED. Axioms of witness, consistency, bwitM_link_env: [propext,
Classical.choice, Quot.sound].

(c) Own checks.
1. Which network does the witness cover? `dR c := match reqSrcM FU c …` (BWit2NDefs.lean:54) uses the HEAD
   `reqSrcM`, and 22c1807e regenerated the wire table (`wRT`/`wAT`) so that `wireChk` passes; the lake build
   kernel-checks `bw_c1/c2`, `bop_c1..6`. So the HEAD witness is of the **136** version. The prose that says
   so: JOURNAL-B 09:59 ("re-checks"), the status table, the BWit2Net docstring. Stale: notes/B-finite-net-bound.md,
   notes/B-gcd-hyps-for-A.md:40 and notes/B-hypotheses.md still say 124/175; BWit2Net's NOT-covered list
   still names "contract cells at … 1-input joins", contradicting its own first paragraph.
2. Census (BC_census.py; own parser of the generated `ops`, own producer/consumer maps, own re-implementation
   of reqSrc/ackSrc in three versions): FiniteNetBound 63/64/23/25 (137 unbound sides), FiniteNetBoundM before
   22c1807e 124/25/25/1, at HEAD **136/15/24/0** (39 unbound sides). All of B's kernel counts reproduce.
3. The 12 newly bound links: 10 gain their ACK side through a 1-input join (RTL: `ack_out = {N{ack}}`, a wire:
   correct); **2 (link ops 233, 234) gain their REQUEST side by tracing back through joins 41/43 = ushrsi0/1**
   (channel 109 <- fork 42 <- join 41 <- channel 85 <- link 220). In bdc's emitted Verilog
   `bdc_fused_ushrsi0` drives `z_req` by `bd_delay_gated #(.N(32))` after a `uor` LUT1 after a **2-input**
   `bd_join` of e0_req and the folded constant channel's e1_req (gcd_kernel.v:915ff; the capstone folded that
   constant). So on the request side the 1-input capstone join is neither a wire nor cell-free; the netlist
   names ushrsi0's last delay LUT as the driver, not link 220. With RTL-faithful request drivers the census is
   134/175. On the witness the unit is a 2-tick wire: (cdB 85).rq = [54, 197], (cdB 109).rq = [56, 199]
   (BC_Bwit2.out), versus >= 34 LUT stages in the real unit. Related, pre-existing since the 63 version: 4
   link request sides are bound to a 2-input COMPUTE join's C-element `jr` (joins 26, 46, 135, 162), whose real
   output request also passes uor + the matched delay; B's network has no cells for the compute units'
   matched delays at all.
4. Degeneracy (BC_Bwit2.lean #eval): 407/465 channels toggle, 1126 request edges, last edge 686, out0 request
   edges [626, 686], ack [627, 687]: one token; all 21 muxes have toggling internal joins. Same kind of
   witness as Bwit (P14 B1): a real closed gate-level run, not a relabelling, but one run, one input pair,
   unit LUT delays, width-0 windows, and H_OTHER/H_BUNDLE discharged by C's checkers on that run.

(d) Verdict B1: **CONFIRMED** that the 136-version theorem has a joint witness and that 124 and 136 follow
from kernel computation on their definitions; **OVERSTATED** in one modelling sentence: "a 1-input join is a
wire both ways (it has no cell)" is false on the request side for the fused units (2 of the 12 new links;
RTL-faithful 134/175). Notes still quote 124 (stale, not overclaiming).

## B2. FiniteNetBoundMCensus (e722adbf)

`unbound_req_classes : census unboundReq = [("src", 1), ("amerge", 23)]`, `unbound_ack_classes : … =
[("muxn", 4), ("amerge", 5), ("forkH5", 4), ("forkH6", 2)]`, kernel, axioms [propext]. Commit total "amerge 28,
muxn 4, fork trees 6, source 1" = 39. Reproduced exactly by BC_census.py. The end classes follow the same
1-input-join rule as B1, so they inherit B1's caveat (2 request sides that end at ushrsi0/1's delay chain are
counted as bound). **CONFIRMED.**

## B3. Selects bound to bit 0 (076af340)

`FGcdNetOKB.H_STEER` and `FGcdNetOKBM.H_STEER/H_MUXJ` now end with `s = fun t => (ch j).dat t % 2 == 1`
(control channel j / cc); before, s was a free existential. For steerD, j is the bjoin channel with data
`2·d + c%2`, so bit 0 is the condition. Both witnesses discharge it by `rfl` (`selB j` unfolds to chB's bus).
BWit2Net is built by lake; BWitNet (OOM-killed in the lake build) compiles under my own `lean -o` run (rc 0,
axioms standard). **CONFIRMED.**

## B4. Bwit2 negative control (f5040d10)

(a) JOURNAL-B 10:08: "the first uj0 node edge of the first mux in BWit2NData moved by +1 tick makes
BWit2NChk's bop_c1 fail by kernel". Journal/notes only; no committed file.
(c) BC_Bwit2.lean (no edit of their tree): `aud_mux37_orig : muxChk ⟨37,_⟩ = true` and
`aud_mux37_mjEdge_rejected : muxChkM ⟨37,_⟩ = false` with mux op 37's uj0 list [46, 189] -> [47, 189]
(op 37 is the first mux, within bop_c1's range 0..59). Gate mutation of my own:
`aud_mux37_selinv_rejected : mjSelInv ⟨37,_⟩ = false` (uj0 checked with the select inverted).
(d) **CONFIRMED.** It is a real mutation of the witness's internal-node data and shows the mux checkers
bite; like P14's Bwit control it tests consistency of the witness data, not the theorem.

## Auditor files and runs

Lean runs: `export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH; cd /root/wt-f14/formal/lean && lake env lean <file>`,
after the build finished, one at a time. Python: `python3 -I`.

| file | purpose | exit |
|---|---|---|
| audit/lean/P15/BC_netcmp2.py (+ .out) | C1/C3 own extraction + simulation; runs: fixture (20 units), /root/wt-r14/cells/build/hw/gcd_hw/gcd_hw.json (20 units), xorshift_1 fixture (5 units, --xs) | 0, 0, 0 |
| audit/lean/P15/BC_netcmp2_fixture_new.out | first run on the 5 new units only | 0 |
| audit/lean/P15/BC_netcmp2_negctl.py (+ .out) | harness detects wrong specs | 0 |
| audit/lean/P15/BC_constports.py (+ .out) | constant ports of the 20 fused instances in gcd_kernel.v | 0 |
| audit/lean/P15/BC_census.py (+ .out) | B1/B2 independent census 63/124/136, end classes, 1-input-join dependence | 0 |
| audit/lean/P15/BC_GcdJoin.lean (+ .out) | C1/C2/C3 statements, axioms, jgAt vs own cf.mlir reading (3560 vectors, 0 bad) | 0 |
| audit/lean/P15/BC_NegNew.lean (+ .out) | C4 own negative controls for Slt and FixShOK | 0 (first attempt rc 1: missing Decidable instance in an aux lemma, fixed) |
| audit/lean/P15/BC_WipNeg_run.out | `lake env lean Wip/Chcf/Neg.lean` | 0 (empty output) |
| audit/lean/P15/BC_Bwit2.lean (+ .out) | B1/B3/B4 statements, axioms, activity, mux-37 controls | 0 (earlier attempts rc 1: comment syntax, fixed) |
| audit/lean/P15/BC_BwitNetAx.lean (+ .out) | BWitNet after 076af340, against own oleans of BWitNChk/BWitNet in the scratchpad | 0 (BWitNChk compile rc 0, BWitNet compile rc 0) |
