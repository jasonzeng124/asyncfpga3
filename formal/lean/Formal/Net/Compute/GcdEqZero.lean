import Formal.Net.Compute.EqZero
import Formal.Gen.Compute.GcdD.Ucmpi0
import Formal.Gen.Compute.GcdD.Ucmpi1
import Formal.Gen.Compute.GcdD.Ucmpi8
import Formal.Gen.Compute.GcdD.Ucmpi10

/-!
# H_COMPUTE_FN for gcd_hw's zero tests `ucmpi0`, `ucmpi1`, `ucmpi8`, `ucmpi10`

Problem statement. Each of these four `bdc_fused_*` units (bdc Verilog `z = (e0 == 32'h0)`,
through bdc's kept LUT1 buffer), as yosys synthesized it (four LUT6 + MUXF7/MUXF8 groups of 8
bits, a LUT4 AND, the LUT1 buffer), computes `Ops.cmpi .eq 32 a 0` for EVERY input `a`.

Proof: `EqZOK` (each 8-bit group net checked over its 256 assignments; the output, with the
group nets as cut points, over 16), then `eqz_sound`. The four netlists are identical (same
yosys output); each gets its own certificate, checked on its own generated cells.

Assumed / not covered: LUT and MUXF Boolean semantics (shard A's models); that this is the
placed netlist (11f/11g); timing; glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

def zGroups : List (Nat × List Nat) :=
  [(39, List.range' 16 8), (40, List.range' 24 8), (41, List.range' 0 8), (42, List.range' 8 8)]

set_option maxRecDepth 100000 in
theorem ucmpi0_cert : EqZOK Ucmpi0.cells Ucmpi0.outs 38 zGroups := by decide +kernel
set_option maxRecDepth 100000 in
theorem ucmpi1_cert : EqZOK Ucmpi1.cells Ucmpi1.outs 38 zGroups := by decide +kernel
set_option maxRecDepth 100000 in
theorem ucmpi8_cert : EqZOK Ucmpi8.cells Ucmpi8.outs 38 zGroups := by decide +kernel
set_option maxRecDepth 100000 in
theorem ucmpi10_cert : EqZOK Ucmpi10.cells Ucmpi10.outs 38 zGroups := by decide +kernel

/-- **ucmpi0 computes `e0 == 0`** for every input. -/
theorem ucmpi0_fn (a : Nat) : unitVal Ucmpi0.cells Ucmpi0.outs [a] = Ops.cmpi .eq 32 a 0 :=
  eqz_sound ucmpi0_cert a
/-- **ucmpi1 computes `e0 == 0`** for every input. -/
theorem ucmpi1_fn (a : Nat) : unitVal Ucmpi1.cells Ucmpi1.outs [a] = Ops.cmpi .eq 32 a 0 :=
  eqz_sound ucmpi1_cert a
/-- **ucmpi8 computes `e0 == 0`** for every input. -/
theorem ucmpi8_fn (a : Nat) : unitVal Ucmpi8.cells Ucmpi8.outs [a] = Ops.cmpi .eq 32 a 0 :=
  eqz_sound ucmpi8_cert a
/-- **ucmpi10 computes `e0 == 0`** for every input. -/
theorem ucmpi10_fn (a : Nat) : unitVal Ucmpi10.cells Ucmpi10.outs [a] = Ops.cmpi .eq 32 a 0 :=
  eqz_sound ucmpi10_cert a

end Formal.Net.Compute.GcdD
