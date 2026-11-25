import Formal.Net.CViewPS.RIslBnd47q0
import Formal.Net.CViewPS.RIslBnd47q1
import Formal.Net.CViewPS.RIslBnd47q2
import Formal.Net.CViewPS.RIslBnd47q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 47, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb47_ok : rb47.all rBndOK = true :=
  all_quarters rBndOK rb47 (by decide) rbb47_ok_q0 rbb47_ok_q1 rbb47_ok_q2 rbb47_ok_q3

end Formal.Net.CViewPS
