import Formal.Net.CViewPS.RIslBnd52q0
import Formal.Net.CViewPS.RIslBnd52q1
import Formal.Net.CViewPS.RIslBnd52q2
import Formal.Net.CViewPS.RIslBnd52q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 52, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb52_ok : rb52.all rBndOK = true :=
  all_quarters rBndOK rb52 (by decide) rbb52_ok_q0 rbb52_ok_q1 rbb52_ok_q2 rbb52_ok_q3

end Formal.Net.CViewPS
