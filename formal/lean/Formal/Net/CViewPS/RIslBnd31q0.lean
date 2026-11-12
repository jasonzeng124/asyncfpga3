import Formal.Net.CViewPS.RIslBndDefs

/-! Shard C: delay bounds of reset-island block 31, quarter 0 (generated; split 2026-11-10 for memory). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rbb31_ok_q0 : ((rb31.drop 0).take 13).all rBndOK = true := by decide +kernel

end Formal.Net.CViewPS
