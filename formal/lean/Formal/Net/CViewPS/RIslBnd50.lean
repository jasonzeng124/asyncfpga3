import Formal.Net.CViewPS.RIslBnd50q0
import Formal.Net.CViewPS.RIslBnd50q1
import Formal.Net.CViewPS.RIslBnd50q2
import Formal.Net.CViewPS.RIslBnd50q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 50, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb50_ok : rb50.all rBndOK = true :=
  all_quarters rBndOK rb50 (by decide) rbb50_ok_q0 rbb50_ok_q1 rbb50_ok_q2 rbb50_ok_q3

end Formal.Net.CViewPS
