import Formal.Net.CViewPS.RIslBnd55q0
import Formal.Net.CViewPS.RIslBnd55q1
import Formal.Net.CViewPS.RIslBnd55q2
import Formal.Net.CViewPS.RIslBnd55q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 55, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb55_ok : rb55.all rBndOK = true :=
  all_quarters rBndOK rb55 (by decide) rbb55_ok_q0 rbb55_ok_q1 rbb55_ok_q2 rbb55_ok_q3

end Formal.Net.CViewPS
