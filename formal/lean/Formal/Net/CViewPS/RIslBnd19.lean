import Formal.Net.CViewPS.RIslBnd19q0
import Formal.Net.CViewPS.RIslBnd19q1
import Formal.Net.CViewPS.RIslBnd19q2
import Formal.Net.CViewPS.RIslBnd19q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 19, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb19_ok : rb19.all rBndOK = true :=
  all_quarters rBndOK rb19 (by decide) rbb19_ok_q0 rbb19_ok_q1 rbb19_ok_q2 rbb19_ok_q3

end Formal.Net.CViewPS
