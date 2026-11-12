import Formal.Net.CViewPS.RIslBnd33q0
import Formal.Net.CViewPS.RIslBnd33q1
import Formal.Net.CViewPS.RIslBnd33q2
import Formal.Net.CViewPS.RIslBnd33q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 33, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb33_ok : rb33.all rBndOK = true :=
  all_quarters rBndOK rb33 (by decide) rbb33_ok_q0 rbb33_ok_q1 rbb33_ok_q2 rbb33_ok_q3

end Formal.Net.CViewPS
