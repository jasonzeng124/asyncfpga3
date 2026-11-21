import Formal.Net.CViewPS.RIslBnd56q0
import Formal.Net.CViewPS.RIslBnd56q1
import Formal.Net.CViewPS.RIslBnd56q2
import Formal.Net.CViewPS.RIslBnd56q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 56, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb56_ok : rb56.all rBndOK = true :=
  all_quarters rBndOK rb56 (by decide) rbb56_ok_q0 rbb56_ok_q1 rbb56_ok_q2 rbb56_ok_q3

end Formal.Net.CViewPS
