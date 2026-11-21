import Formal.Net.Import.Netlist
import Wip.LutList.trial.CoreLutPrelim

/-!
# Probe 11e: the Prelim-valued Kleene reading of the imported netlists (11a)

Porting aid, **to be deleted together with `Formal/Cells/Prelim.lean`**.
`Formal.Net.Import.Netlist` now reads LUTs with shard A's Core semantics
(`kleeneSem` on `Formal.Core.K3`). The theorems of `Formal.Net.Import.Proofs`
that compare with shard B's still-Prelim Kleene transcriptions (`c2K`, `g1K`,
`K3.mux`, ...) use `kleeneSemP` below: the same interpreter with Prelim's
`lutK`, i.e. exactly their pre-port statements. `kleeneSemP_lut` /
`kleeneSemP_const` show the two readings agree through `toP`. When B ports,
replace `kleeneSemP` by `kleeneSem` there and delete this file.
-/

namespace Formal.Net.Import
open Formal.Net.CoreLut Formal.Net.CoreLutPrelim

/-- Kleene reading with shard B's Prelim `lutK` (pre-port `kleeneSem`). -/
def kleeneSemP : Sem Formal.Core.LutList.K3 := ⟨Formal.Core.LutList.lutK, Formal.Core.LutList.K3.ofBool⟩

/-- Binary reading with Prelim's `lutB`. It IS `boolSem` (`boolSem_eq_boolSemP`,
`Bool` is shared), so a theorem about one is a theorem about the other; it is
only here so that proofs by `rfl` against B's `lutB`-valued lemmas keep working. -/
def boolSemP : Sem Bool := ⟨Formal.Core.LutList.lutB, id⟩

theorem boolSem_eq_boolSemP : boolSem = boolSemP := by
  unfold boolSem boolSemP
  congr 1
  funext init ins
  exact (lutB_eq_evalL init ins).symm

theorem kleeneSemP_lut (init : Nat) (ins : List Formal.Core.K3) :
    kleeneSemP.lut init (ins.map toP) = toP (kleeneSem.lut init ins) :=
  lutK_eq_kevalL init ins

theorem kleeneSemP_const (b : Bool) : kleeneSemP.const b = toP (kleeneSem.const b) :=
  (toP_ofBool b).symm

end Formal.Net.Import
