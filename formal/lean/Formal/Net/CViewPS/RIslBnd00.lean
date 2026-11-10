import Formal.Net.CViewPS.RIslBnd00q0
import Formal.Net.CViewPS.RIslBnd00q1
import Formal.Net.CViewPS.RIslBnd00q2
import Formal.Net.CViewPS.RIslBnd00q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 0, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb0_ok : rb0.all rBndOK = true :=
  all_quarters rBndOK rb0 (by decide) rbb0_ok_q0 rbb0_ok_q1 rbb0_ok_q2 rbb0_ok_q3

end Formal.Net.CViewPS
