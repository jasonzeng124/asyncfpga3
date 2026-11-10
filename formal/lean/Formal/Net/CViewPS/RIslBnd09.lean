import Formal.Net.CViewPS.RIslBnd09q0
import Formal.Net.CViewPS.RIslBnd09q1
import Formal.Net.CViewPS.RIslBnd09q2
import Formal.Net.CViewPS.RIslBnd09q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 9, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb9_ok : rb9.all rBndOK = true :=
  all_quarters rBndOK rb9 (by decide) rbb9_ok_q0 rbb9_ok_q1 rbb9_ok_q2 rbb9_ok_q3

end Formal.Net.CViewPS
