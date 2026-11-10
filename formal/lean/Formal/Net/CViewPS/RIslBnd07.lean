import Formal.Net.CViewPS.RIslBnd07q0
import Formal.Net.CViewPS.RIslBnd07q1
import Formal.Net.CViewPS.RIslBnd07q2
import Formal.Net.CViewPS.RIslBnd07q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 7, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb7_ok : rb7.all rBndOK = true :=
  all_quarters rBndOK rb7 (by decide) rbb7_ok_q0 rbb7_ok_q1 rbb7_ok_q2 rbb7_ok_q3

end Formal.Net.CViewPS
