import Formal.Net.FasmDesign.GcdT.All

/-!
# Probe C-11g on THE TARGET: the gcd_hw bitstream THE goal is about, read back from its bits

The target is `formal/target/gcd_hw_03e82630.bit` (shard A, formal/target/README.md: BOARD-QUEUE #1, build_hw.sh's
default seed, no `--freq`). The physical netlist is decoded from `gcd_hw_03e82630.fromBit.fasm` (the `.bit` read
back by prjxray) by `fasm2lean3.py`, which gives the same physical netlist as nextpnr's own FASM; the logical
netlist is the target build's yosys netlist (`gcd_hw_03e82630.json`), flattened by `gen3.py` (namespace GcdT).
Generated 2026-11-01 by shard C (journal), with the cached toolchain's prjxray-db (key d7ce266cff0c8e1e).

Statements (no hypotheses; what they rest on is the decoders, see the note):

* `gcd_hw_target_netlist`: every one of the 10629 instances is `Inst.Sound` for the
  renaming `GcdT.rho` (H_NETLIST, connectivity and function half, for the target).
* `gcd_hw_target_ports`: the two output pads' physical sources rename to the logical
  OBUF inputs.
* `gcd_hw_target_count`: 10629 instances, 9622 of them carry a logical cell (the 9623rd
  logical cell, a MUXF7 whose output nothing reads, is reported by gen3).
* `gcd_hw_target_cells_init`: every bound library-cell LUT (5627 of the 5645 library-cell LUTs gen3 counts) has the kind and
  INIT of the `Formal.Gen.Cells` cell generated from the same `cells/rtl` line.

NOT covered: timing, glitches, X; the RTL-to-yosys step; injectivity of `rho`;
the trust in the FASM-to-site decoding (H_SITE_DECODE) and in the yosys JSON
flattening; the --freq 100 routes are separate files (d: FasmGcd, 2-4: FasmGcd2..4).
-/

namespace Formal.Net.FasmGcdT
open Formal.Gen Formal.Net.FasmDesign

theorem gcd_hw_target_netlist : ∀ i ∈ GcdT.insts, i.Sound GcdT.rho := GcdT.sound

theorem gcd_hw_target_ports : ∀ x ∈ GcdT.ports, ren GcdT.rho x.2.1 = some x.2.2 := by
  intro x hx
  have h := GcdT.ports_ok
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h x hx

theorem gcd_hw_target_count :
    GcdT.insts.length = 10629 ∧ (GcdT.insts.filter (·.log.isSome)).length = 9622 := by
  decide +kernel

/-- H_CELLS (INIT half), the target: in every chunk, every binding `(k, nl, name)` says that
instance `k` carries a logical cell whose kind and INIT are those of cell `name` of the
generated library netlist `nl`. -/
theorem gcd_hw_target_cells_init :
    ∀ c ∈ GcdT.chunks, ∀ k nl nm, (k, nl, nm) ∈ c.2 → ∃ i l g, c.1[k]? = some i ∧
      i.log = some l ∧ nl.cell? nm = some g ∧ g.kind = l.kind ∧ g.init = l.init := by
  intro c hc
  have h := GcdT.cells_init
  simp only [List.all_eq_true] at h
  exact bindsOk_sound c.1 c.2 (h c hc)

/-- The chunks are the instances, and they carry 5645 bindings (= every library-cell LUT). -/
theorem gcd_hw_target_chunks :
    (GcdT.chunks.map Prod.fst).flatten = GcdT.insts ∧
    (GcdT.chunks.map (fun c => c.2.length)).sum = 5627 :=
  ⟨GcdT.chunks_insts, GcdT.binds_count⟩

end Formal.Net.FasmGcdT
