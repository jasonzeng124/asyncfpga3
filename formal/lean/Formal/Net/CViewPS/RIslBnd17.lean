import Formal.Net.CViewPS.RIslBnd17q0
import Formal.Net.CViewPS.RIslBnd17q1
import Formal.Net.CViewPS.RIslBnd17q2
import Formal.Net.CViewPS.RIslBnd17q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 17, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb17_ok : rb17.all rBndOK = true :=
  all_quarters rBndOK rb17 (by decide) rbb17_ok_q0 rbb17_ok_q1 rbb17_ok_q2 rbb17_ok_q3

end Formal.Net.CViewPS
