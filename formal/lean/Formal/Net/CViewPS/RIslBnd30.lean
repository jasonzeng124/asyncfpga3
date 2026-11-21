import Formal.Net.CViewPS.RIslBnd30q0
import Formal.Net.CViewPS.RIslBnd30q1
import Formal.Net.CViewPS.RIslBnd30q2
import Formal.Net.CViewPS.RIslBnd30q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 30, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb30_ok : rb30.all rBndOK = true :=
  all_quarters rBndOK rb30 (by decide) rbb30_ok_q0 rbb30_ok_q1 rbb30_ok_q2 rbb30_ok_q3

end Formal.Net.CViewPS
