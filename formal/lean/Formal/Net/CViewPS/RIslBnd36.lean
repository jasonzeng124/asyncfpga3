import Formal.Net.CViewPS.RIslBnd36q0
import Formal.Net.CViewPS.RIslBnd36q1
import Formal.Net.CViewPS.RIslBnd36q2
import Formal.Net.CViewPS.RIslBnd36q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 36, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb36_ok : rb36.all rBndOK = true :=
  all_quarters rBndOK rb36 (by decide) rbb36_ok_q0 rbb36_ok_q1 rbb36_ok_q2 rbb36_ok_q3

end Formal.Net.CViewPS
