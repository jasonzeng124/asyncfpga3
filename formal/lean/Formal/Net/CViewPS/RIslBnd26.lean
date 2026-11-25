import Formal.Net.CViewPS.RIslBnd26q0
import Formal.Net.CViewPS.RIslBnd26q1
import Formal.Net.CViewPS.RIslBnd26q2
import Formal.Net.CViewPS.RIslBnd26q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 26, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb26_ok : rb26.all rBndOK = true :=
  all_quarters rBndOK rb26 (by decide) rbb26_ok_q0 rbb26_ok_q1 rbb26_ok_q2 rbb26_ok_q3

end Formal.Net.CViewPS
