import Formal.Net.CViewPS.RIslBnd32q0
import Formal.Net.CViewPS.RIslBnd32q1
import Formal.Net.CViewPS.RIslBnd32q2
import Formal.Net.CViewPS.RIslBnd32q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 32, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb32_ok : rb32.all rBndOK = true :=
  all_quarters rBndOK rb32 (by decide) rbb32_ok_q0 rbb32_ok_q1 rbb32_ok_q2 rbb32_ok_q3

end Formal.Net.CViewPS
