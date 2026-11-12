import Formal.Net.CViewPS.RIslBnd48q0
import Formal.Net.CViewPS.RIslBnd48q1
import Formal.Net.CViewPS.RIslBnd48q2
import Formal.Net.CViewPS.RIslBnd48q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 48, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb48_ok : rb48.all rBndOK = true :=
  all_quarters rBndOK rb48 (by decide) rbb48_ok_q0 rbb48_ok_q1 rbb48_ok_q2 rbb48_ok_q3

end Formal.Net.CViewPS
