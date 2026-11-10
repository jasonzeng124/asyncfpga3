import Formal.Net.CViewPS.RIslBnd24q0
import Formal.Net.CViewPS.RIslBnd24q1
import Formal.Net.CViewPS.RIslBnd24q2
import Formal.Net.CViewPS.RIslBnd24q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 24, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb24_ok : rb24.all rBndOK = true :=
  all_quarters rBndOK rb24 (by decide) rbb24_ok_q0 rbb24_ok_q1 rbb24_ok_q2 rbb24_ok_q3

end Formal.Net.CViewPS
