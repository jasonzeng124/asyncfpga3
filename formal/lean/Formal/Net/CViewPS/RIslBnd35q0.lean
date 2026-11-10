import Formal.Net.CViewPS.RIslBndDefs

/-! Shard C: delay bounds of reset-island block 35, quarter 0 (generated; split 2026-11-10 for memory). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rbb35_ok_q0 : ((rb35.drop 0).take 13).all rBndOK = true := by decide +kernel

end Formal.Net.CViewPS
