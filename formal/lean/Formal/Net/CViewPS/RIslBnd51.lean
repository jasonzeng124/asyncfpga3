import Formal.Net.CViewPS.RIslBnd51q0
import Formal.Net.CViewPS.RIslBnd51q1
import Formal.Net.CViewPS.RIslBnd51q2
import Formal.Net.CViewPS.RIslBnd51q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 51, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb51_ok : rb51.all rBndOK = true :=
  all_quarters rBndOK rb51 (by decide) rbb51_ok_q0 rbb51_ok_q1 rbb51_ok_q2 rbb51_ok_q3

end Formal.Net.CViewPS
