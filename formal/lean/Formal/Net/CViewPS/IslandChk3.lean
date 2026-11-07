import Formal.Net.CViewPS.IslandDefs

/-! Shard C: kernel check of island chunk 3. -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem isl3_ok : isl3.all entryOK = true := by decide +kernel

end Formal.Net.CViewPS
