import Formal.Net.FasmDesign.Xorshift4.All

/-!
# Probe C-11g: the routed xorshift kernel (route 4), read back from its bitstream

Route 4 = the compiled xorshift kernel STANDALONE (bdc/emit.py's soak top
`bdc_xorshift_top`, research's `xorshift_sizes_T3.vh`), placed and routed by
`cells/flow.sh` with NEXTPNR_SEED=4 and `--freq 100` (the design has no clock),
nextpnr 9c732bc6303458df (`formal/tools/fasm2lean3/kroute.sh xorshift 4`; fixture
`formal/tools/fasm2lean3/fixture/xorshift_4.*`). The physical netlist is decoded
from the FASM read back from the `.bit` (`fasm2lean3.py`); the logical netlist is
the yosys netlist nextpnr was given (flattened by `gen3.py`). See
`formal/notes/C-11g-seeds.md`.

Statements (no hypotheses; what they rest on is the decoders and the input-pad
reading H_IBUF, see the note):

* `xorshift_4_netlist`: every one of the 1043 instances is `Inst.Sound` for the
  renaming `Xorshift4.rho`.
* `xorshift_4_ports`: the output pad's physical source renames to the logical
  OBUF input.
* `xorshift_4_count`: 1043 instances, 988 of them carry a logical cell (every
  logical cell of the yosys netlist; the other 55 are nextpnr's route-through and
  constant LUTs).
* `xorshift_4_cells_init`: every bound library-cell LUT (832) has the kind and
  INIT of the `Formal.Gen.Cells` cell generated from the same `cells/rtl` line.

NOT covered: timing, glitches, X (this kernel is all combinational loops and
C-elements: the statement is about gate functions only, not about the
asynchronous behaviour); the RTL-to-yosys step; the soak top is not the rig or
the PS7 bench the kernel is measured in on the board.
-/

namespace Formal.Net.FasmXorshift4
open Formal.Gen Formal.Net.FasmDesign

theorem xorshift_4_netlist : ∀ i ∈ Xorshift4.insts, i.Sound Xorshift4.rho := Xorshift4.sound

theorem xorshift_4_ports : ∀ x ∈ Xorshift4.ports, ren Xorshift4.rho x.2.1 = some x.2.2 := by
  intro x hx
  have h := Xorshift4.ports_ok
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h x hx

theorem xorshift_4_count :
    Xorshift4.insts.length = 1043 ∧ (Xorshift4.insts.filter (·.log.isSome)).length = 988 := by
  decide +kernel

theorem xorshift_4_cells_init :
    ∀ c ∈ Xorshift4.chunks, ∀ k nl nm, (k, nl, nm) ∈ c.2 → ∃ i l g, c.1[k]? = some i ∧
      i.log = some l ∧ nl.cell? nm = some g ∧ g.kind = l.kind ∧ g.init = l.init := by
  intro c hc
  have h := Xorshift4.cells_init
  simp only [List.all_eq_true] at h
  exact bindsOk_sound c.1 c.2 (h c hc)

theorem xorshift_4_chunks :
    (Xorshift4.chunks.map Prod.fst).flatten = Xorshift4.insts ∧
    (Xorshift4.chunks.map (fun c => c.2.length)).sum = 832 :=
  ⟨Xorshift4.chunks_insts, Xorshift4.binds_count⟩

end Formal.Net.FasmXorshift4
