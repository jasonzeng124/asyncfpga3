import Formal.Net.CViewPS.RIslBndDefs

/-! Shard C: delay bounds of reset-island block 32, quarter 1 (generated; split 2026-11-10 for memory). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rbb32_ok_q1 : ((rb32.drop 13).take 13).all rBndOK = true := by decide +kernel

end Formal.Net.CViewPS
