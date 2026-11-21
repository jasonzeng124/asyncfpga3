import Formal.Net.CViewPS.RIslBndDefs

/-! Shard C: delay bounds of reset-island block 37, quarter 2 (generated; split 2026-11-10 for memory). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rbb37_ok_q2 : ((rb37.drop 26).take 13).all rBndOK = true := by decide +kernel

end Formal.Net.CViewPS
