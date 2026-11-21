import Formal.Net.CViewPS.RIslBnd44q0
import Formal.Net.CViewPS.RIslBnd44q1
import Formal.Net.CViewPS.RIslBnd44q2
import Formal.Net.CViewPS.RIslBnd44q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 44, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb44_ok : rb44.all rBndOK = true :=
  all_quarters rBndOK rb44 (by decide) rbb44_ok_q0 rbb44_ok_q1 rbb44_ok_q2 rbb44_ok_q3

end Formal.Net.CViewPS
