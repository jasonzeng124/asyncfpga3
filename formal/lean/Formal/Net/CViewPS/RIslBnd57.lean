import Formal.Net.CViewPS.RIslBnd57q0
import Formal.Net.CViewPS.RIslBnd57q1
import Formal.Net.CViewPS.RIslBnd57q2
import Formal.Net.CViewPS.RIslBnd57q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 57, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb57_ok : rb57.all rBndOK = true :=
  all_quarters rBndOK rb57 (by decide) rbb57_ok_q0 rbb57_ok_q1 rbb57_ok_q2 rbb57_ok_q3

end Formal.Net.CViewPS
