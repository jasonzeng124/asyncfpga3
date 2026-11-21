import Formal.Net.CViewPS.RIslBnd13q0
import Formal.Net.CViewPS.RIslBnd13q1
import Formal.Net.CViewPS.RIslBnd13q2
import Formal.Net.CViewPS.RIslBnd13q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 13, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb13_ok : rb13.all rBndOK = true :=
  all_quarters rBndOK rb13 (by decide) rbb13_ok_q0 rbb13_ok_q1 rbb13_ok_q2 rbb13_ok_q3

end Formal.Net.CViewPS
