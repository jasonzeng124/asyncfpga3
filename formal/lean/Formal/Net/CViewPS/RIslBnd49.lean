import Formal.Net.CViewPS.RIslBnd49q0
import Formal.Net.CViewPS.RIslBnd49q1
import Formal.Net.CViewPS.RIslBnd49q2
import Formal.Net.CViewPS.RIslBnd49q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 49, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb49_ok : rb49.all rBndOK = true :=
  all_quarters rBndOK rb49 (by decide) rbb49_ok_q0 rbb49_ok_q1 rbb49_ok_q2 rbb49_ok_q3

end Formal.Net.CViewPS
