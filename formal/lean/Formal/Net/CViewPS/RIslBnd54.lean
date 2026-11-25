import Formal.Net.CViewPS.RIslBnd54q0
import Formal.Net.CViewPS.RIslBnd54q1
import Formal.Net.CViewPS.RIslBnd54q2
import Formal.Net.CViewPS.RIslBnd54q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 54, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb54_ok : rb54.all rBndOK = true :=
  all_quarters rBndOK rb54 (by decide) rbb54_ok_q0 rbb54_ok_q1 rbb54_ok_q2 rbb54_ok_q3

end Formal.Net.CViewPS
