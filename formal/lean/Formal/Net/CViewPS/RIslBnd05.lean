import Formal.Net.CViewPS.RIslBnd05q0
import Formal.Net.CViewPS.RIslBnd05q1
import Formal.Net.CViewPS.RIslBnd05q2
import Formal.Net.CViewPS.RIslBnd05q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 5, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb5_ok : rb5.all rBndOK = true :=
  all_quarters rBndOK rb5 (by decide) rbb5_ok_q0 rbb5_ok_q1 rbb5_ok_q2 rbb5_ok_q3

end Formal.Net.CViewPS
