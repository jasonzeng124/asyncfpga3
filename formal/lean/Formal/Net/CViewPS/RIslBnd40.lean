import Formal.Net.CViewPS.RIslBnd40q0
import Formal.Net.CViewPS.RIslBnd40q1
import Formal.Net.CViewPS.RIslBnd40q2
import Formal.Net.CViewPS.RIslBnd40q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 40, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb40_ok : rb40.all rBndOK = true :=
  all_quarters rBndOK rb40 (by decide) rbb40_ok_q0 rbb40_ok_q1 rbb40_ok_q2 rbb40_ok_q3

end Formal.Net.CViewPS
