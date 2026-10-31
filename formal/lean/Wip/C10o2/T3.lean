import Formal.Timing.ChainSettleExeGcdDData7
namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe
theorem v1151 :
    verdict r1151 = ⟨true, true, 1, 4256, 55658, 48022, true, true, true⟩ ∧
    (verdict { r1151 with T := 4380 }).exact = true ∧
    (verdict { r1151 with T := 4379 }).exact = false ∧
    (verdict { r1151 with T := 4741 }).bridge = true ∧
    (verdict { r1151 with T := 4740 }).bridge = false := by decide +kernel
end Formal.Timing.ChainSettleExe.GcdD
