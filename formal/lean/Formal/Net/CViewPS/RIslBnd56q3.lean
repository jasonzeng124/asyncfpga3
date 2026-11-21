import Formal.Net.CViewPS.RIslBndDefs

/-! Shard C: delay bounds of reset-island block 56, quarter 3 (generated; split 2026-11-10 for memory). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rbb56_ok_q3 : ((rb56.drop 39).take 13).all rBndOK = true := by decide +kernel

end Formal.Net.CViewPS
