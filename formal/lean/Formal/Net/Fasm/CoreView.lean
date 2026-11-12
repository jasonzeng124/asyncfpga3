import Formal.Net.Fasm.Basic
import Formal.Net.CoreLutPrelim

/-!
# Probe 11e: the FASM netlist's LUT function in shard A's Core semantics

`Formal.Net.Fasm.Basic` keeps `PLut.fn` on shard B's Prelim `o6B`/`o5B`,
because shard B's `Formal/Cells/OnNetlist*.lean` unfold `PLut.fn` to `o5B`
in their proofs (and shard C may not edit them). This file gives the Core
reading `PLut.fnCore` (`Lut62.o6`/`o5` through `Formal.Net.CoreLut`) and proves
it is the same function on every 6-pin vector, the only kind `Behaves` and
`PNet.exc` apply it to (`(List.range 6).map ...`, and every generated `PLut`
has 6 pins). When B ports OnNetlist*, `PLut.fn` can be redefined as
`fnCore` and this file deleted.
-/

namespace Formal.Net.Fasm
open Formal.Net.CoreLut Formal.Net.CoreLutPrelim

/-- Core reading of a physical LUT: O6 = `Lut62.o6`, O5 = `Lut62.o5` on `[A1..A6]`. -/
def PLut.fnCore (L : PLut) : LOut → List Bool → Bool
  | .o6, v => o6L L.init v
  | .o5, v => o5L L.init v

theorem PLut.fn_eq_fnCore (L : PLut) (o : LOut) (v : List Bool) (h : v.length = 6) :
    L.fn o v = L.fnCore o v := by
  cases o
  · exact o6B_eq_o6L _ _ h
  · exact o5B_eq_o5L _ _ h

/-- The pin vector `Behaves.H_LUT` evaluates has 6 entries. -/
theorem range6_length (f : Nat → Bool) : ((List.range 6).map f).length = 6 := by simp

end Formal.Net.Fasm
