import Formal.Net.CViewPS.RIslBnd18q0
import Formal.Net.CViewPS.RIslBnd18q1
import Formal.Net.CViewPS.RIslBnd18q2
import Formal.Net.CViewPS.RIslBnd18q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 18, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb18_ok : rb18.all rBndOK = true :=
  all_quarters rBndOK rb18 (by decide) rbb18_ok_q0 rbb18_ok_q1 rbb18_ok_q2 rbb18_ok_q3

end Formal.Net.CViewPS
