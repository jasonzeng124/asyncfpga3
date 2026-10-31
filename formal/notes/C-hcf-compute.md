# C-hcf: H_COMPUTE_FN -- the synthesized compute units of gcd_hw compute their ops

Shard C, 2026-10-31. Core Lean only (no Mathlib), no sorry/axiom/native_decide; kernel `decide`
(`decide +kernel`) for the exhaustive local checks.

## Problem statement

The capstone treats every bdc compute unit (`bdc_fused_*`) as an ideal zero-time function of its
input tokens (`OpsJoin`, `Join.dat`). The hypothesis that the synthesized gate netlist computes
that function, **H_COMPUTE_FN**, was open (graded B; "the yosys fused-unit LUT/CARRY4 netlists
compute bdc's expressions"; `formal/out/gcd_hw_hypotheses.md`). gcd_hw has 20 such units.

**Proved (for every input value, not sampled):** for the units listed below, the combinational
cone of `z_data` in the committed yosys `synth_xilinx` netlist of gcd_hw
(`tools/fasm2lean3/fixture/gcd_hw_d.synth.json.xz`, route d's synthesis, extracted by
`tools/compute/extract.py` into `Formal/Gen/Compute/GcdD/*.lean`) evaluates to the operation bdc
wrote in that unit's Verilog (`bdc/emit.py` on `cloud/fixtures/frontend/gcd`), stated with the
capstone's integer semantics (`GcdHw.Ops`).

| unit | bdc Verilog | theorem | method |
|---|---|---|---|
| uori0, uori1 | `e0 \| e1` (32 b) | `GcdD.uori0_fn`, `uori1_fn` = `Ops.ori 32` | per-bit exhaustive (support 2) |
| ucmpi2 | `(e0 & 1) == e1` (1 b) | `ucmpi2_fn` | exhaustive |
| ucmpi3 | `(e0 & e1) == 0` (1 b) | `ucmpi3_fn` | exhaustive |
| ucmpi0, 1, 8, 10 | `e0 == 32'h0` | `ucmpi*_fn` = `Ops.cmpi .eq 32 a 0` | `EqZOK`: 4 groups of 8 bits as cut points |
| uaddi0 | `e0 + e1` (32 b) | `uaddi0_fn` = `Ops.addi 32` | `AddOK`: ripple adder, the 8 CARRY4 carry-outs as cut points |
| ushrsi0..4 | `$signed(e0) >>> e1`, with `e1 = 1` (the only value gcd_hw feeds it) | `ushrsi*_fn` = `Ops.shrsi 32 a 1` | `ShrOK`: port 1 fixed to 1 and folded through LUT cofactors / MUXF selects (`Fold.lean`) |
| uori2, 3, 4 | `((e2 & e3) != 0) \| slt(e0, e1)` | `uori*_fn` | `SltOK` (signed compare: 22 group LUTs exhaustive, CARRY4 chain structural via `run_cell`, final over cuts) + output over the compare net |
| uselect0 | `slt(e0, e1) ? e0 : e1` | `uselect0_fn` | `SltOK` + per-bit mux over the compare net |
| ushli0 | `e0 << e1`, every `e0`, every shift amount `k < 32` | `ushli0_fn` = `Ops.shli 32 a k` | 32 `FixShOK` certificates (`e1 = k` folded), `GcdShli0K0..3` |
| uselect1 | `d = e0 - e1; d > -1 ? d : 0 - d` | `uselect1_fn` | two `RipOK` chains (`a + ~b + 1`; `~d + 1` over the 32 difference nets as cuts), sign test over cuts, per-bit mux |

The four routed gcd_hw seeds (d, 2, 3, 4) have byte-identical synthesis JSON (md5 e81e3f53...),
so every unit theorem holds for all four routes' logical netlist.

**Assumed:** the Boolean semantics of LUT (its INIT table), MUXF7/8 and CARRY4 (shard A's
`Formal.Core.Prims` models; CARRY4 `c0 = CI | CYINIT` as in UNISIM); that the netlist is the one
placed and routed (the bitstream import 11f/11g proves each placed instance computes its yosys
cell under the checked renaming).

**Not covered:** timing (H_COMPUTE_DELAY: the cone settles inside the matched delay, rule A);
glitches and X; ushli0 for shift amounts `k >= 32` (gcd_hw's `k` stays below 31: a token-level
fact, not restated here); the shifters ushrsi* for shift amounts other than 1; uselect1's board failure was a
timing/GLS event, which a function theorem does not address (it only rules out a wrong
synthesized function as the cause); the link from these unit
theorems to the capstone's `Join.dat` (the RTL unit <-> Ops join map); the other routes' and
kernels' syntheses (the extractor runs on any of them).

## Method (Formal/Net/Compute/)

- `Basic.lean`: cells, `run` (cells in list order; a CUT net takes a free leaf value), computed
  supports. `support_sound` (a wire depends only on its support), `cut_sound` (if each cut leaf
  carries the real value of its net and no net has two drivers, the cut evaluation is the real
  one), `local_sound` (an exhaustive check over a leaf list covering the support proves the
  spec for every environment), `eval_filt` (evaluating only a net's cone gives its value).
- `Word.lean`: numbers on ports, `unitVal`, `BitLocal`, `cert_val`.
- `Adder.lean`: `AddOK` + `add_sound` (generic ripple-carry arithmetic proved once).
- `EqZero.lean`: `EqZOK` + `eqz_sound`.
A certificate does not have to be trusted: any cut set is sound, every check is kernel-decided.
Cost: one 512-assignment slice check takes ~5 s in the kernel; uaddi0 ~2.5 min, the four zero
tests 15 s together.

## Run

    formal/tools/compute/gen.sh --check          # regenerate the unit netlists, compare (drift)
    cd formal && ./check.sh Formal/Net/Compute/*.lean Formal/Gen/Compute/GcdD/*.lean
