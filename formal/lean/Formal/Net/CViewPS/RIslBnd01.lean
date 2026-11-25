import Formal.Net.CViewPS.RIslBnd01q0
import Formal.Net.CViewPS.RIslBnd01q1
import Formal.Net.CViewPS.RIslBnd01q2
import Formal.Net.CViewPS.RIslBnd01q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 1, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb1_ok : rb1.all rBndOK = true :=
  all_quarters rBndOK rb1 (by decide) rbb1_ok_q0 rbb1_ok_q1 rbb1_ok_q2 rbb1_ok_q3

end Formal.Net.CViewPS
