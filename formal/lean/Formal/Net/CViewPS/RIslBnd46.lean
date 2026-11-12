import Formal.Net.CViewPS.RIslBnd46q0
import Formal.Net.CViewPS.RIslBnd46q1
import Formal.Net.CViewPS.RIslBnd46q2
import Formal.Net.CViewPS.RIslBnd46q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 46, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb46_ok : rb46.all rBndOK = true :=
  all_quarters rBndOK rb46 (by decide) rbb46_ok_q0 rbb46_ok_q1 rbb46_ok_q2 rbb46_ok_q3

end Formal.Net.CViewPS
