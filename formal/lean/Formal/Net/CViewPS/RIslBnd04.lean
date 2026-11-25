import Formal.Net.CViewPS.RIslBnd04q0
import Formal.Net.CViewPS.RIslBnd04q1
import Formal.Net.CViewPS.RIslBnd04q2
import Formal.Net.CViewPS.RIslBnd04q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 4, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb4_ok : rb4.all rBndOK = true :=
  all_quarters rBndOK rb4 (by decide) rbb4_ok_q0 rbb4_ok_q1 rbb4_ok_q2 rbb4_ok_q3

end Formal.Net.CViewPS
