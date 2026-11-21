import Formal.Net.CViewPS.RIslBnd10q0
import Formal.Net.CViewPS.RIslBnd10q1
import Formal.Net.CViewPS.RIslBnd10q2
import Formal.Net.CViewPS.RIslBnd10q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 10, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb10_ok : rb10.all rBndOK = true :=
  all_quarters rBndOK rb10 (by decide) rbb10_ok_q0 rbb10_ok_q1 rbb10_ok_q2 rbb10_ok_q3

end Formal.Net.CViewPS
