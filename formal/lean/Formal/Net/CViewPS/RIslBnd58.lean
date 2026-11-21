import Formal.Net.CViewPS.RIslBnd58q0
import Formal.Net.CViewPS.RIslBnd58q1
import Formal.Net.CViewPS.RIslBnd58q2
import Formal.Net.CViewPS.RIslBnd58q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 58, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb58_ok : rb58.all rBndOK = true :=
  all_quarters rBndOK rb58 (by decide) rbb58_ok_q0 rbb58_ok_q1 rbb58_ok_q2 rbb58_ok_q3

end Formal.Net.CViewPS
