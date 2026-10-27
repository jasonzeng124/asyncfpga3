# C-11d: importing the whole cell library into Formal/Gen/

## Verdict: works

One command, `formal/tools/gen/gen.sh [--check]`, synthesizes 63 targets with the project's yosys
flow: every one of the 36 modules of `cells/rtl/*.v` (yosys `ls` enumerates them and the script
checks coverage), plus 5 primitive fixtures. It writes the trimmed JSON and generates one Lean
`Netlist` per target in `formal/lean/Formal/Gen/Cells.lean`. A single interpreter
(`Formal/Gen/Netlist.lean`) covers every primitive that appears: LUT1-6, LUT6_2, MUXF7/8,
CARRY4, FDRE/FDSE/FDCE/FDPE, LDCE/LDPE, BUFG, and RAMB18E1 (opaque).

163 theorems (590 declarations, all `decide +kernel` or symbolic `rfl`) prove that the generated
netlists equal shard B's hand transcriptions. They cover every cell for which B has an INIT
constant or a cell function in the tree, binary and Kleene wherever B has Kleene. Theorems also
cover shard A's `Core.Lut.Init`/`Core.LutCells` INITs and the RTL header equations for the cells
B has not transcribed. There is no sorry, no axiom and no native_decide. The audit
(`collectAxioms` over all `Formal.Gen.*`) shows only propext, Quot.sound and Classical.choice.
`formal/scan.py` passes.

**Negative control.** I flipped INIT bit 7 of `bd_c2` in a copy of the JSON and regenerated:
9 theorems of `ProofsCE` then fail ("decide proved that the proposition ... is false"). So a
changed INIT does break the build. Separately, `gen.sh --check` reports any yosys or generator
drift as DRIFT.

## Run

```
formal/tools/gen/gen.sh --check        # drift check: re-synth all 63 targets (~7 min on a loaded
                                       # 4-core box), diff JSON + Lean, check module coverage
formal/tools/gen/gen.sh --check-json   # generator only, from committed JSON (seconds, no yosys)
formal/tools/gen/gen.sh                # regenerate (writes json/*.json and Formal/Gen/Cells.lean)

cd formal/lean && export PATH=$HOME/.elan/bin:$PATH   # oleans: B's Cells/* and A's Core/{Kleene,Lut,LutCells}
for f in Netlist Cells ProofsCE ProofsLatch ProofsLink ProofsCtl ProofsArb ProofsMisc ProofsPrims All; do
  ../slot.sh lean -o .lake/build/lib/lean/Formal/Gen/$f.olean Formal/Gen/$f.lean; done
```

I checked everything in a private olean tree (scratchpad), because `.lake/build` did not have
B's LinkHandshake/LibCtlMergeMux/CTree/Arb*/Bundling oleans or A's Core ones. Measured times on
the loaded machine:

| file | time |
|---|---|
| ProofsCE | 76-91 s |
| ProofsLatch | 9-21 s |
| ProofsLink | 37 s |
| ProofsCtl | 8 s |
| ProofsArb | 170 s |
| ProofsMisc | 20 s |
| ProofsPrims | 166-181 s |

Peak memory is a few GB each.

**For the lead:**
- add `import Formal.Gen.All` to the root `Formal.lean`;
- optionally run `formal/tools/gen/gen.sh --check-json` (cheap) from `check.sh`.

`Formal/Gen` imports `Formal.Cells.Prelim` (`lutB`/`lutK`), as 11a did. When B deletes
`Prelim` (Phase 1 B), the semantics import and the matched names must move to wherever B puts
them; see "Coupling to B's port" below.

## Files (all mine)

- `formal/tools/gen/gen.sh`: the one command. It enumerates modules with yosys, synthesizes
  each target (parallel, `JOBS=4`), trims the JSON to the top module and generates Lean.
- `formal/tools/gen/targets.txt`: 63 targets, each `<lean name> <top> [P=V ...] [+DEFINE]`.
- `formal/tools/gen/yosys2lean.py`: the generator, extended from 11a's.
- `formal/tools/gen/test/prims.v`: primitive fixtures, not library cells.
- `formal/tools/gen/json/*.json`: the yosys output that was imported (0.5 MB).
- `formal/lean/Formal/Gen/Netlist.lean`: types, primitive models, interpreter (gate view and
  step view).
- `formal/lean/Formal/Gen/Cells.lean`: GENERATED, 63 netlists and `all`.
- `formal/lean/Formal/Gen/Proofs{CE,Latch,Link,Ctl,Arb,Misc,Prims}.lean` and `All.lean`.
- `formal/lean/Wip/C11d/`: empty. Nothing is unfinished.

## Synthesis flow (fidelity of the input)

Each target uses `cells/flow.sh`'s flow, out of context: `read_verilog -lib -specify cells_sim.v;
read_verilog [-D…] rtl/*.v; chparam …; synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram
-noclkbuf -noiopad -top T; write_json`.

- **`-noiopad` is the one deliberate difference from flow.sh.** A library cell is never a top
  level, so pads do not exist in any real design. 11a imported the pads and needed
  H_PAD_IDENTITY; with `-noiopad` that hypothesis is gone. Logic and INITs are unchanged:
  they are the same INITs as 11a's, and every `_lut` theorem checks them.
- **Producer:** `Yosys 0.62 (git sha1 7326bb7d6)` at `$TC/openxc7/bin/yosys`. The string is in
  the generated header.
- **`+BD_LINK_DC`** corresponds to `BD_SYN_DEFS=-DBD_LINK_DC` in flow.sh. It makes
  `bd_link_W2_DC` the decoupled family.
- **Port order is declaration order** (yosys JSON order). I had to remove a `sort_keys` that
  had reordered the ports alphabetically. **Net names:** an input port name, else an output
  port name, else the shortest top-level public name, else the shortest hierarchical one.

## Targets and parameter choices

The rule: each generate branch is exercised by some target, and exhaustive checks stay cheap.

| module | targets (params) | imported |
|---|---|---|
| bd_c2, _set, n, n_set, c3, c4, c2_norst, c3_norst | as is | fully |
| bd_ctree | N=1 (wire), 3, 5 (C2(C4,a4)), 8 (C2(C4,C4)) | fully; N=2/4 are bd_c2/bd_c4, covered via fork/join N=2 |
| bd_latch | W=1 (odd), 2 (pair), 3 (both) | fully |
| bd_latch_rst | W=1; W=2 RESET_VALUE=2 (per-bit polarity) | fully |
| bd_delay | N=0 (bypass), 3, 3 FASTFALL, 3 FASTRISE | fully |
| bd_delay_gated | N=3 | fully |
| bd_datamux | W=3 (pair + odd LUT3) | fully |
| bd_link_ctl | as is | fully |
| bd_link_dctl | BROAD=1 LDN=0; BROAD=0 LDN=0; BROAD=0 LDN=2 | fully |
| bd_link_dc | W=2 DELAY=1 DACK=1 | fully |
| bd_link | W=2; W=2 DELAY=2 DACK=2; W=2 DELAY=2 RFAST=1; W=2 with `-DBD_LINK_DC` | fully |
| bd_pipe | W=1 N=1; W=1 N=2 | fully |
| bd_pipe_dc | W=1 N=2 | fully |
| bd_fork, bd_join | N=2, 5 / N=2, 3 | fully |
| bd_steer, bd_bd2dr | as is | fully |
| bd_dr2bd | DELAY=2 HOLD=0; HOLD=1 | fully |
| bd_src, bd_snk | W=2 VAL=2'b10; W=2 | fully (constant output ports supported) |
| bd_merge | W=2 DELAY=2 | fully |
| bd_mux | W=2 DELAY=2; FASTFALL=1 | fully |
| bd_mlink_ctl | NOPEN=1, 3 | fully |
| bd_mlink | W=2 DELAY=2 | fully |
| bd_flink_ctl | as is | fully |
| bd_flink | W=2 DELAY=1 | fully, under H_FF_MS (two FDRE) |
| bd_mem | DSETUP=DCO=2; DSETUP=DCO=1 USE_BUFG=1 | **partly**: the RAMB18E1 is opaque (see below) |
| bd_arbcell, bd_arbiter | as is | fully |

**Nothing is "not imported".** No cell needs an x/z constant or an unmodelled primitive. The
generator rejects any unknown type, x/z constant, multiply driven net, undriven read, wrong pin
set, malformed INIT, or inversion on a non-FF pin, with exit 1. I tested DSP48E1, an `x` tie
and a duplicated driver on mutated copies of the JSON: each gives exit 1 with the reason.

## Primitive models (fidelity)

All primitives are evaluated through one `Sem.lut` table lookup. So the binary reading
(`lutB`) and the Kleene reading (`lutK`, H_KLEENE_LUT) come from the same code, and every
primitive table is checked against its equation (`prim_tables`, `mux_kleene`).

| primitive | model | fidelity / hypothesis | checked against |
|---|---|---|---|
| LUT1-6, LUT6_2 | INIT table; O5 = INIT[31:0] over I0..I4 (I5 tied 1) | B's model, H_KLEENE_LUT for Kleene. The logic is exact; the mux tree's glitches are the delay layer's job | every `_lut`/`_gate` theorem |
| MUXF7/MUXF8 | `S ? I1 : I0`, Kleene = `K3.mux` | a real 2:1 mux, so the Kleene reading is H_KLEENE_LUT's per-mux form | `prims_mux8_spec` (all 2048), `prims_muxf8_spec`, `prims_muxf_kleene` |
| CARRY4 | cells_sim.v, gate by gate: cin = CI\|CYINIT, CO = S?c:DI, O = S xor c | **H_CARRY4_SIM**: the silicon CYINIT is a static mux, not an OR; they agree when one input is tied 0, which is how yosys uses it | `prims_add_spec` (all 512: `s = a+b+ci`) |
| FDRE/FDSE/FDCE/FDPE | **H_FF_MS**: master-slave latch pair, synthetic master net `M`; sync R/S through D, async CLR/PRE force both | ideal edge-triggered flop. Setup/hold, CK->Q and metastability are not modelled; INIT (power-up) is recorded, not used | `prims_ff_next`; `prims_ff_edge` (low then high = the Verilog `always @(posedge)` result from any state) |
| LDCE/LDPE | `CLR/PRE ? 0/1 : (G&GE ? D : Q)`; `IS_*_INVERTED` = pin read inverted | the slice has a programmable G/CK inverter. Level semantics, no timing | `prims_lat_next` (yosys used IS_G_INVERTED behind a NOR) |
| BUFG | identity, **H_BUF_IDENTITY** | logic only; the ~ns insertion delay is a timing fact | `bd_mem_ack` (bufg variant) |
| RAMB18E1 | **OPAQUE**: all pins and nets recorded, outputs `none` | not modelled | `bd_mem_rdata_opaque`: for every input, rdata is `none`, so no claim can rest on it by accident |

**Step view.** State is the set of FF/latch outputs (plus masters), plus LUT outputs read back
by their own cell (the library's deliberate loops). A DFS-back-edge cut follows, but for every
target the DFS cut is empty (`cut := []`). Delay lines are wires in this reading. This is the
unit-step reading of 11a/B, with H_FB settled. The gate view (`Netlist.gate`/`gateN`) has no
such reading: every gate output is a variable. That is the interface for the trace and delay
proofs.

## Theorems matched to shard B (names as in the tree today, all on `Formal.Cells.Prelim`)

B has not started its Core port yet: every `Formal/Cells/*.lean` still imports `Prelim`.

- **CElemFn** (`ProofsCE`):
  - `INIT_c2..INIT_c3_norst` (8): `bd_c*_lut`;
  - `c2B c2setB c2nB c2nsetB c3B c4B c2norstB c3norstB`: `*_gate_B`;
  - the matching `…K` functions: `*_gate_K`;
  - `cSpec`/`clr`/`set`: `bd_c*_next`;
  - `c2K`, `c4K` on the whole netlist: `bd_c2_next_K`, `bd_c4_next_K`;
  - `c3B` (join N=3), `c2B` (fork N=2): `bd_join_N3_spec`, `bd_fork_N2_spec`.
- **CTree**: `INIT_C2/C3/C4` (`ce_inits_B`); `c2r`/`c4r` and the shapes `t5`/`t8` (=`gen 5`,
  `gen 8`) in `bd_ctree_N5_shape`, `bd_ctree_N8_shape`, `bd_ctree_N5_next`, `bd_ctree_N8_next`;
  `bd_fork_N5_shape`.
- **CElemTiming**: `INIT_c2`, `INIT_c2_set`, `INIT_c2n` (`ce_inits_B`).
- **Latch** (`ProofsLatch`): `ODD PAIR RST0 RST1` (`bd_latch_*_lut`); `bmux` in
  `bd_latch_W1_gate_B`, `bd_latch_W3_next`, `bd_latch_rst_W2_R2_next`; Kleene `K3.mux` in
  `bd_latch_W2_gate_K` and `bd_latch_W2_next_K`.
- **LinkHandshake**:
  - `INIT_LAT`, `INIT_PAIR` (`latch_inits_other`); `latK` (`bd_latch_W1_gate_K`);
  - `INIT_C2N`, `ctlB` (`bd_link_ctl_*`, `bd_link_W2_step`, `bd_pipe_*_step`);
  - `INIT_DB/DA/DLD/DLT` (`bd_link_dctl_B1_lut`);
  - **`dNext true` / `dNext false`**: every gate of the synthesized controller, in all 64 of
    B's states (`bd_link_dctl_B1_dNext`, `bd_link_dctl_B0_dNext`). So B's
    `dctl_ok1`/`dctl_ok0` are about the synthesized cell.
  - **`diNext 2`**: both controller gates of the synthesized 2-stage pipe, in all 1024 of B's
    states, with each net read from the copy B's model hands that gate
    (`bd_pipe_W1_N2_diNext`).
  - `pair_eq`, `lat_eq` are used in the `_DC`/`_dc`/`pipe_dc` step proofs.
- **Bundling**: `BUF FF_SIDE FR_SIDE ODD PAIR` (`delay_luts`, `latch_inits_other`, link/mlink
  `_lut`).
- **LibCtlMergeMux** (`ProofsCtl`):
  - `INIT_steer`, `req0B/K`, `req1B/K`, `INIT_or2`, `or2B/K` (steer, bd2dr);
  - `INIT_dr`, `dNextB/K`, `eitherB/K` (dr2bd HOLD=1); `dBare` (HOLD=0);
  - `INIT_c2`, `c2K`, `selK` (merge, `bd_merge_W2_gate_K`); `c2B`, `selB`, `or2B`
    (`bd_merge_W2_step`);
  - `INIT_j0/j1`, `j0B/K`, `j1B/K` (`bd_mux_W2_lut`, `bd_mux_W2_gate_K`, `bd_mux_W2_step`).
- **ArbKleene** (`ProofsArb`): `ST_INIT GR_INIT CS_INIT C2_INIT`, `g1K g2K qArbK r0K qCellK cK`
  (gates and whole netlist, all 3^7); `kleene_exclusion` is transferred to the generated
  arbiter (`arbiter_kleene_exclusion`).
- **ArbBinary**: `C2N_SET GRANT ARB_ST C2`, `stF gr1 gr2 stA r0A c2`.
- **ArbHandover**: `INIT_C2N_SET INIT_GRANTS INIT_HELD INIT_C2_RST`, `stateF g1F g2F`.
  `INIT_UNHELD` is proved NOT to be the synthesized INIT (`arb_unheld_not_synthesized`).
- **ArbHeldTimed**: `INIT_HELD INIT_GRANTS INIT_C2`, `FS FR FG1 FG2 CE`.
- **ArbA0Fork**: `ST_INIT GR_INIT C2_INIT`, `cel F1 F2 G1 G2`.
- **Shard A**: `Formal.Core.Init.{bd_c2..bd_c3_norst, arb_grant, arb_state, latch_pair,
  latch_odd, latch_rst0/1, delay_buf/and/or, datamux_pair/odd}` (BitVec INITs, and `Lut.eval`
  equality in `bd_c2_gate_core`, `bd_c4_gate_core`). `Formal.Core.LutCells` is A's regex
  extraction from the Verilog; it agrees with yosys for every cell I compared.

**Cells without a B transcription**, checked against their RTL header equations instead:
`bd_datamux`, `bd_src`, `bd_snk`, `bd_mem` (LUT part plus the header's clock design rules:
one explicit clock driver, no inferred BUFG, the ack tap on the same net, the address and WE
wiring), `bd_mlink_ctl`/`bd_mlink`, `bd_flink_ctl`/`bd_flink`.

## Coupling to B's port (to do when B lands Core)

The matched constants and functions are referenced by full name (`Formal.Cells.CElemFn.c2B`, …),
and the semantics comes from `Formal.Cells.Prelim` (`lutB`, `lutK`, `K3`). When B deletes
`Prelim`:
1. switch `Netlist.lean`'s `boolSem`/`kleeneSem` to B's new LUT functions, or to Core's
   `Lut.eval`/`keval` via A's `cells_lutB_eq_eval`/`cells_lutK_eq_keval`;
2. rename the opens.

Every theorem is `decide +kernel` or `rfl` over generated data, so nothing else should need
editing. About 1-2 h.

## What does not work / limits

- **Kernel memory.** A 2^14-case `decide +kernel` (bd_mux step) used more than 10 GB and was
  OOM-killed. Fix: for big netlists, prove the step by **symbolic evaluation**. `rfl` reduces
  the interpreter on the generated data to B's LUT terms (`j0B …`, `lutB INIT_DA …`), and small
  exhaustive lemmas (`pair_eq`, `lat_eq`, `dmux_pair`, FF tables) finish. bd_mux takes 8 s this
  way. Use this pattern for anything bigger.
- **Not exhaustive:** prims_mux16 (2^20) was replaced by the smaller explicit
  MUXF7/MUXF8 fixtures. Kleene whole-netlist checks were done for the C-elements, latches and
  arbiter only; for the trees and links, Kleene holds per gate.
- **The step view is a modelling choice** (unit step, feedback read as an independent input,
  delay lines are wires). It says nothing about races: that is the trace layer's job. The gate
  view is the interface for it.
- **What the JSON loses** (11a's list): placement, routing, LUT pin permutation (the router
  rewrites INITs; FASM INITs differ), and how tied pins are physically realized. Matching
  routed/FASM netlists against these generated ones is 11b's job (function equality up to
  pin permutation, not INIT equality).
- **Opaque RAMB18E1.** Modelling it properly would mean the RAMB18E1 TDP read/write semantics,
  WRITE_FIRST, and a clock edge (master-slave as for FFs): about 1 day. Its timing (setup to
  CLK, clk-to-out) belongs to the timing checker.

## Effort to finish / what it buys

- Done for Phase 1 C, except wiring it into the root import and check.sh (lead).
- **Buys:**
  - every shard-B cell theorem now applies to what yosys actually emitted, by rewriting with
    a named theorem;
  - a changed INIT, pin or generate branch in `cells/rtl/` fails `gen.sh --check`, and after
    regeneration fails the proofs (negative control above);
  - the interpreter now covers every primitive the flow emits for the library (RAMB opaque),
    so whole-design import (`soak.json`) is down to scale (compositional matching, about a
    week, 11a's estimate) rather than missing primitives;
  - for Phase 2 (timing checker), the gate view and pin maps are the per-arc structure that
    rules A/E/F/H/I/J need.
