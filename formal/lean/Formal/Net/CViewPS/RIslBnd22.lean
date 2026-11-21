import Formal.Net.CViewPS.RIslBnd22q0
import Formal.Net.CViewPS.RIslBnd22q1
import Formal.Net.CViewPS.RIslBnd22q2
import Formal.Net.CViewPS.RIslBnd22q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 22, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb22_ok : rb22.all rBndOK = true :=
  all_quarters rBndOK rb22 (by decide) rbb22_ok_q0 rbb22_ok_q1 rbb22_ok_q2 rbb22_ok_q3

end Formal.Net.CViewPS
