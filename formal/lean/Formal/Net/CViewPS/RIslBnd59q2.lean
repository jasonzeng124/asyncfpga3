import Formal.Net.CViewPS.RIslBndDefs

/-! Shard C: delay bounds of reset-island block 59, quarter 2 (generated; split 2026-11-10 for memory). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rbb59_ok_q2 : ((rb59.drop 26).take 13).all rBndOK = true := by decide +kernel

end Formal.Net.CViewPS
