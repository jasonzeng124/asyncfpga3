import Formal.Net.CViewPS.RIslBnd16q0
import Formal.Net.CViewPS.RIslBnd16q1
import Formal.Net.CViewPS.RIslBnd16q2
import Formal.Net.CViewPS.RIslBnd16q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 16, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb16_ok : rb16.all rBndOK = true :=
  all_quarters rBndOK rb16 (by decide) rbb16_ok_q0 rbb16_ok_q1 rbb16_ok_q2 rbb16_ok_q3

end Formal.Net.CViewPS
