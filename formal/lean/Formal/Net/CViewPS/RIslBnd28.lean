import Formal.Net.CViewPS.RIslBnd28q0
import Formal.Net.CViewPS.RIslBnd28q1
import Formal.Net.CViewPS.RIslBnd28q2
import Formal.Net.CViewPS.RIslBnd28q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 28, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb28_ok : rb28.all rBndOK = true :=
  all_quarters rBndOK rb28 (by decide) rbb28_ok_q0 rbb28_ok_q1 rbb28_ok_q2 rbb28_ok_q3

end Formal.Net.CViewPS
