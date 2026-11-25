import Formal.Net.CViewPS.RIslBnd45q0
import Formal.Net.CViewPS.RIslBnd45q1
import Formal.Net.CViewPS.RIslBnd45q2
import Formal.Net.CViewPS.RIslBnd45q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 45, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb45_ok : rb45.all rBndOK = true :=
  all_quarters rBndOK rb45 (by decide) rbb45_ok_q0 rbb45_ok_q1 rbb45_ok_q2 rbb45_ok_q3

end Formal.Net.CViewPS
