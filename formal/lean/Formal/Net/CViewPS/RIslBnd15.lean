import Formal.Net.CViewPS.RIslBnd15q0
import Formal.Net.CViewPS.RIslBnd15q1
import Formal.Net.CViewPS.RIslBnd15q2
import Formal.Net.CViewPS.RIslBnd15q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 15, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb15_ok : rb15.all rBndOK = true :=
  all_quarters rBndOK rb15 (by decide) rbb15_ok_q0 rbb15_ok_q1 rbb15_ok_q2 rbb15_ok_q3

end Formal.Net.CViewPS
