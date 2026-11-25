import Formal.Net.CViewPS.RIslBnd37q0
import Formal.Net.CViewPS.RIslBnd37q1
import Formal.Net.CViewPS.RIslBnd37q2
import Formal.Net.CViewPS.RIslBnd37q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 37, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb37_ok : rb37.all rBndOK = true :=
  all_quarters rBndOK rb37 (by decide) rbb37_ok_q0 rbb37_ok_q1 rbb37_ok_q2 rbb37_ok_q3

end Formal.Net.CViewPS
