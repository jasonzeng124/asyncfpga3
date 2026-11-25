import Formal.Net.CViewPS.RIslBnd60q0
import Formal.Net.CViewPS.RIslBnd60q1
import Formal.Net.CViewPS.RIslBnd60q2
import Formal.Net.CViewPS.RIslBnd60q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 60, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb60_ok : rb60.all rBndOK = true :=
  all_quarters rBndOK rb60 (by decide) rbb60_ok_q0 rbb60_ok_q1 rbb60_ok_q2 rbb60_ok_q3

end Formal.Net.CViewPS
