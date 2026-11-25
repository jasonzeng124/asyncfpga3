import Formal.Net.CViewPS.RIslBnd41q0
import Formal.Net.CViewPS.RIslBnd41q1
import Formal.Net.CViewPS.RIslBnd41q2
import Formal.Net.CViewPS.RIslBnd41q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 41, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb41_ok : rb41.all rBndOK = true :=
  all_quarters rBndOK rb41 (by decide) rbb41_ok_q0 rbb41_ok_q1 rbb41_ok_q2 rbb41_ok_q3

end Formal.Net.CViewPS
