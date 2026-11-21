import Formal.Net.CViewPS.RIslBnd25q0
import Formal.Net.CViewPS.RIslBnd25q1
import Formal.Net.CViewPS.RIslBnd25q2
import Formal.Net.CViewPS.RIslBnd25q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 25, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb25_ok : rb25.all rBndOK = true :=
  all_quarters rBndOK rb25 (by decide) rbb25_ok_q0 rbb25_ok_q1 rbb25_ok_q2 rbb25_ok_q3

end Formal.Net.CViewPS
