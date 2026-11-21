import Formal.Net.CViewPS.RIslBnd59q0
import Formal.Net.CViewPS.RIslBnd59q1
import Formal.Net.CViewPS.RIslBnd59q2
import Formal.Net.CViewPS.RIslBnd59q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 59, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb59_ok : rb59.all rBndOK = true :=
  all_quarters rBndOK rb59 (by decide) rbb59_ok_q0 rbb59_ok_q1 rbb59_ok_q2 rbb59_ok_q3

end Formal.Net.CViewPS
