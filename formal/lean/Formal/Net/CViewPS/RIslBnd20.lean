import Formal.Net.CViewPS.RIslBnd20q0
import Formal.Net.CViewPS.RIslBnd20q1
import Formal.Net.CViewPS.RIslBnd20q2
import Formal.Net.CViewPS.RIslBnd20q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 20, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb20_ok : rb20.all rBndOK = true :=
  all_quarters rBndOK rb20 (by decide) rbb20_ok_q0 rbb20_ok_q1 rbb20_ok_q2 rbb20_ok_q3

end Formal.Net.CViewPS
