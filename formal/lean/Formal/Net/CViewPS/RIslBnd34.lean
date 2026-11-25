import Formal.Net.CViewPS.RIslBnd34q0
import Formal.Net.CViewPS.RIslBnd34q1
import Formal.Net.CViewPS.RIslBnd34q2
import Formal.Net.CViewPS.RIslBnd34q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 34, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb34_ok : rb34.all rBndOK = true :=
  all_quarters rBndOK rb34 (by decide) rbb34_ok_q0 rbb34_ok_q1 rbb34_ok_q2 rbb34_ok_q3

end Formal.Net.CViewPS
