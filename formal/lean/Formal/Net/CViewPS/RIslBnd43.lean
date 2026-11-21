import Formal.Net.CViewPS.RIslBnd43q0
import Formal.Net.CViewPS.RIslBnd43q1
import Formal.Net.CViewPS.RIslBnd43q2
import Formal.Net.CViewPS.RIslBnd43q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 43, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb43_ok : rb43.all rBndOK = true :=
  all_quarters rBndOK rb43 (by decide) rbb43_ok_q0 rbb43_ok_q1 rbb43_ok_q2 rbb43_ok_q3

end Formal.Net.CViewPS
