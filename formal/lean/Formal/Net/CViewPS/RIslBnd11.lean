import Formal.Net.CViewPS.RIslBnd11q0
import Formal.Net.CViewPS.RIslBnd11q1
import Formal.Net.CViewPS.RIslBnd11q2
import Formal.Net.CViewPS.RIslBnd11q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 11, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb11_ok : rb11.all rBndOK = true :=
  all_quarters rBndOK rb11 (by decide) rbb11_ok_q0 rbb11_ok_q1 rbb11_ok_q2 rbb11_ok_q3

end Formal.Net.CViewPS
