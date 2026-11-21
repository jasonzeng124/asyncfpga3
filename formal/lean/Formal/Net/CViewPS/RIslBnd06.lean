import Formal.Net.CViewPS.RIslBnd06q0
import Formal.Net.CViewPS.RIslBnd06q1
import Formal.Net.CViewPS.RIslBnd06q2
import Formal.Net.CViewPS.RIslBnd06q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 6, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb6_ok : rb6.all rBndOK = true :=
  all_quarters rBndOK rb6 (by decide) rbb6_ok_q0 rbb6_ok_q1 rbb6_ok_q2 rbb6_ok_q3

end Formal.Net.CViewPS
