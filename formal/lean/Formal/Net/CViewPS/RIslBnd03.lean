import Formal.Net.CViewPS.RIslBnd03q0
import Formal.Net.CViewPS.RIslBnd03q1
import Formal.Net.CViewPS.RIslBnd03q2
import Formal.Net.CViewPS.RIslBnd03q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 3, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb3_ok : rb3.all rBndOK = true :=
  all_quarters rBndOK rb3 (by decide) rbb3_ok_q0 rbb3_ok_q1 rbb3_ok_q2 rbb3_ok_q3

end Formal.Net.CViewPS
