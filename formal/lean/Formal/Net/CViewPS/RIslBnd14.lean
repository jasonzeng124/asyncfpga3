import Formal.Net.CViewPS.RIslBnd14q0
import Formal.Net.CViewPS.RIslBnd14q1
import Formal.Net.CViewPS.RIslBnd14q2
import Formal.Net.CViewPS.RIslBnd14q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 14, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb14_ok : rb14.all rBndOK = true :=
  all_quarters rBndOK rb14 (by decide) rbb14_ok_q0 rbb14_ok_q1 rbb14_ok_q2 rbb14_ok_q3

end Formal.Net.CViewPS
