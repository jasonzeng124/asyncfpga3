import Formal.Net.CViewPS.IslandDefs

/-! Shard C: kernel check of island chunk 6. -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem isl6_ok : isl6.all entryOK = true := by decide +kernel

end Formal.Net.CViewPS
