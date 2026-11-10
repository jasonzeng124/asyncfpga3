import Formal.Net.CViewPS.RIslBnd31q0
import Formal.Net.CViewPS.RIslBnd31q1
import Formal.Net.CViewPS.RIslBnd31q2
import Formal.Net.CViewPS.RIslBnd31q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 31, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb31_ok : rb31.all rBndOK = true :=
  all_quarters rBndOK rb31 (by decide) rbb31_ok_q0 rbb31_ok_q1 rbb31_ok_q2 rbb31_ok_q3

end Formal.Net.CViewPS
