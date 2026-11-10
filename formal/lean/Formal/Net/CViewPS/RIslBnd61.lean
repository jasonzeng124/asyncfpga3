import Formal.Net.CViewPS.RIslBnd61q0
import Formal.Net.CViewPS.RIslBnd61q1
import Formal.Net.CViewPS.RIslBnd61q2
import Formal.Net.CViewPS.RIslBnd61q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 61, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb61_ok : rb61.all rBndOK = true :=
  all_quarters rBndOK rb61 (by decide) rbb61_ok_q0 rbb61_ok_q1 rbb61_ok_q2 rbb61_ok_q3

end Formal.Net.CViewPS
