import Formal.Net.CViewPS.RIslBnd23q0
import Formal.Net.CViewPS.RIslBnd23q1
import Formal.Net.CViewPS.RIslBnd23q2
import Formal.Net.CViewPS.RIslBnd23q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 23, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb23_ok : rb23.all rBndOK = true :=
  all_quarters rBndOK rb23 (by decide) rbb23_ok_q0 rbb23_ok_q1 rbb23_ok_q2 rbb23_ok_q3

end Formal.Net.CViewPS
