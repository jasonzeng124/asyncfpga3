import Formal.Net.CViewPS.RIslBnd29q0
import Formal.Net.CViewPS.RIslBnd29q1
import Formal.Net.CViewPS.RIslBnd29q2
import Formal.Net.CViewPS.RIslBnd29q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 29, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb29_ok : rb29.all rBndOK = true :=
  all_quarters rBndOK rb29 (by decide) rbb29_ok_q0 rbb29_ok_q1 rbb29_ok_q2 rbb29_ok_q3

end Formal.Net.CViewPS
