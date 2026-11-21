import Formal.Net.FasmDesign.GcdD.All

/-!
# Probe C-11f: the whole routed gcd_hw (route d), read back from its bitstream

Route d = `cells/hw/build_hw.sh gcd_hw` with no `--seed`, `--freq 100`, nextpnr
9c732bc6303458df (fixture `formal/tools/fasm2lean3/fixture/gcd_hw_d.*`). The
physical netlist is decoded from the FASM read back from the `.bit`
(`fasm2lean3.py`); the logical netlist is the yosys netlist nextpnr was given
(flattened by `gen3.py`). See `formal/notes/C-11f-design-import.md`.

Statements (no hypotheses; what they rest on is the decoders, see the note):

* `gcd_hw_d_netlist`: every one of the 10629 instances is `Inst.Sound` for the
  renaming `GcdD.rho` (H_NETLIST, connectivity and function half, for route d).
* `gcd_hw_d_ports`: the two output pads' physical sources rename to the logical
  OBUF inputs.
* `gcd_hw_d_count`: 10629 instances, 9622 of them carry a logical cell (the 9623rd
  logical cell, a MUXF7 whose output nothing reads, is reported by gen3).
* `gcd_hw_d_cells_init`: every bound library-cell LUT (5645) has the kind and
  INIT of the `Formal.Gen.Cells` cell generated from the same `cells/rtl` line.

NOT covered: timing, glitches, X; the RTL-to-yosys step; injectivity of `rho`;
the trust in the FASM-to-site decoding (H_SITE_DECODE) and in the yosys JSON
flattening; routes other than d (checked by the Python mirror only).
-/

namespace Formal.Net.FasmGcd
open Formal.Gen Formal.Net.FasmDesign

theorem gcd_hw_d_netlist : ∀ i ∈ GcdD.insts, i.Sound GcdD.rho := GcdD.sound

theorem gcd_hw_d_ports : ∀ x ∈ GcdD.ports, ren GcdD.rho x.2.1 = some x.2.2 := by
  intro x hx
  have h := GcdD.ports_ok
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h x hx

theorem gcd_hw_d_count :
    GcdD.insts.length = 10629 ∧ (GcdD.insts.filter (·.log.isSome)).length = 9622 := by
  decide +kernel

/-- H_CELLS (INIT half), route d: in every chunk, every binding `(k, nl, name)` says that
instance `k` carries a logical cell whose kind and INIT are those of cell `name` of the
generated library netlist `nl`. -/
theorem gcd_hw_d_cells_init :
    ∀ c ∈ GcdD.chunks, ∀ k nl nm, (k, nl, nm) ∈ c.2 → ∃ i l g, c.1[k]? = some i ∧
      i.log = some l ∧ nl.cell? nm = some g ∧ g.kind = l.kind ∧ g.init = l.init := by
  intro c hc
  have h := GcdD.cells_init
  simp only [List.all_eq_true] at h
  exact bindsOk_sound c.1 c.2 (h c hc)

/-- The chunks are the instances, and they carry 5645 bindings (= every library-cell LUT). -/
theorem gcd_hw_d_chunks :
    (GcdD.chunks.map Prod.fst).flatten = GcdD.insts ∧
    (GcdD.chunks.map (fun c => c.2.length)).sum = 5645 :=
  ⟨GcdD.chunks_insts, GcdD.binds_count⟩

end Formal.Net.FasmGcd
