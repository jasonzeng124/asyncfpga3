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

**Assumed:** the Boolean semantics of LUT (its INIT table), MUXF7/8 and CARRY4 (shard A's
`Formal.Core.Prims` models; CARRY4 `c0 = CI | CYINIT` as in UNISIM); that the netlist is the one
placed and routed (the bitstream import 11f/11g proves each placed instance computes its yosys
cell under the checked renaming).

**Not covered:** timing (H_COMPUTE_DELAY: the cone settles inside the matched delay, rule A);
glitches and X; the remaining 11 units (uori2/3/4 and uselect0: signed compare; uselect1:
abs-difference, where the gcd_rig GLS located the board failure; ushli0, ushrsi0-4: barrel
shifters, whose `e1` is a full 32-bit port fed by a constant token); the link from these unit
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
