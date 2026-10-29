import Formal.Net.GenWitOx

/-!
# Probe C-witgen (2/4): the generated-level run meets `GenCell` on operators 0..183

Kernel checks (`decide +kernel`) of `kChkG` (GenWitLib) on the run `gcdA`/`goxA` of
`GenWitData`/`GenWitOx` (a = 12, b = 18), in chunks of 92 operators.
-/

namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Wit Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

/-- The per-operator claim checked by the kernel. -/
def gP (i : Nat) : Bool := kChkG gcdA (goxA i) (srcV 12 18) (ops.getD i (K.sink 0))

theorem chunk_of {a k : Nat} (h : (List.range' a k).all gP = true) :
    ∀ i, a ≤ i → i < a + k → gP i = true :=
  fun i h1 h2 => List.all_eq_true.mp h i (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem gcells1 : (List.range' 0 92).all gP = true := by decide +kernel
theorem gcells2 : (List.range' 92 92).all gP = true := by decide +kernel

end Formal.Net.CellBind.GenWit
