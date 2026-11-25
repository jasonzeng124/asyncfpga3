import Formal.Net.CapstoneWitness

/-! C-8t negative control: H_WALK's checker with the oracle of arbiter stage 0 inverted
(the walk does reach stage 0 on a = 12, b = 18) must FAIL. -/

namespace Formal.Net.CapNet.Wit.Neg
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd Formal.Net.CapNet.Wit

set_option maxRecDepth 100000

def omBad (w k : Nat) : Bool := if w = 0 then !omOf A0 B0 yW w k else omOf A0 B0 yW w k

-- MUST FAIL
theorem neg_walk : walkChk (σY A0 B0 yW) omBad 80 (walk (σY A0 B0 yW) 0) = true := by decide +kernel

end Formal.Net.CapNet.Wit.Neg
