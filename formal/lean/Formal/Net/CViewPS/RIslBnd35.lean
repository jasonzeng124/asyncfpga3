import Formal.Net.CViewPS.RIslBnd35q0
import Formal.Net.CViewPS.RIslBnd35q1
import Formal.Net.CViewPS.RIslBnd35q2
import Formal.Net.CViewPS.RIslBnd35q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 35, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb35_ok : rb35.all rBndOK = true :=
  all_quarters rBndOK rb35 (by decide) rbb35_ok_q0 rbb35_ok_q1 rbb35_ok_q2 rbb35_ok_q3

end Formal.Net.CViewPS
