import Formal.Net.CViewPS.RIslBnd08q0
import Formal.Net.CViewPS.RIslBnd08q1
import Formal.Net.CViewPS.RIslBnd08q2
import Formal.Net.CViewPS.RIslBnd08q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 8, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb8_ok : rb8.all rBndOK = true :=
  all_quarters rBndOK rb8 (by decide) rbb8_ok_q0 rbb8_ok_q1 rbb8_ok_q2 rbb8_ok_q3

end Formal.Net.CViewPS
