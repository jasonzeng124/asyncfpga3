import Formal.Net.CViewPS.RIslBnd27q0
import Formal.Net.CViewPS.RIslBnd27q1
import Formal.Net.CViewPS.RIslBnd27q2
import Formal.Net.CViewPS.RIslBnd27q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 27, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb27_ok : rb27.all rBndOK = true :=
  all_quarters rBndOK rb27 (by decide) rbb27_ok_q0 rbb27_ok_q1 rbb27_ok_q2 rbb27_ok_q3

end Formal.Net.CViewPS
