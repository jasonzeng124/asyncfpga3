import Formal.Net.CViewPS.RIslBnd12q0
import Formal.Net.CViewPS.RIslBnd12q1
import Formal.Net.CViewPS.RIslBnd12q2
import Formal.Net.CViewPS.RIslBnd12q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 12, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb12_ok : rb12.all rBndOK = true :=
  all_quarters rBndOK rb12 (by decide) rbb12_ok_q0 rbb12_ok_q1 rbb12_ok_q2 rbb12_ok_q3

end Formal.Net.CViewPS
