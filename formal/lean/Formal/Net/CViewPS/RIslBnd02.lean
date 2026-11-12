import Formal.Net.CViewPS.RIslBnd02q0
import Formal.Net.CViewPS.RIslBnd02q1
import Formal.Net.CViewPS.RIslBnd02q2
import Formal.Net.CViewPS.RIslBnd02q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 2, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb2_ok : rb2.all rBndOK = true :=
  all_quarters rBndOK rb2 (by decide) rbb2_ok_q0 rbb2_ok_q1 rbb2_ok_q2 rbb2_ok_q3

end Formal.Net.CViewPS
