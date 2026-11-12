import Formal.Net.CViewPS.RIslBnd38q0
import Formal.Net.CViewPS.RIslBnd38q1
import Formal.Net.CViewPS.RIslBnd38q2
import Formal.Net.CViewPS.RIslBnd38q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 38, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb38_ok : rb38.all rBndOK = true :=
  all_quarters rBndOK rb38 (by decide) rbb38_ok_q0 rbb38_ok_q1 rbb38_ok_q2 rbb38_ok_q3

end Formal.Net.CViewPS
