import Formal.Net.CViewPS.RIslBnd39q0
import Formal.Net.CViewPS.RIslBnd39q1
import Formal.Net.CViewPS.RIslBnd39q2
import Formal.Net.CViewPS.RIslBnd39q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 39, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb39_ok : rb39.all rBndOK = true :=
  all_quarters rBndOK rb39 (by decide) rbb39_ok_q0 rbb39_ok_q1 rbb39_ok_q2 rbb39_ok_q3

end Formal.Net.CViewPS
