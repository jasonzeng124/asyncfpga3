import Formal.Net.CViewPS.RIslBnd53q0
import Formal.Net.CViewPS.RIslBnd53q1
import Formal.Net.CViewPS.RIslBnd53q2
import Formal.Net.CViewPS.RIslBnd53q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 53, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb53_ok : rb53.all rBndOK = true :=
  all_quarters rBndOK rb53 (by decide) rbb53_ok_q0 rbb53_ok_q1 rbb53_ok_q2 rbb53_ok_q3

end Formal.Net.CViewPS
