import Formal.Net.CViewPS.RIslBnd42q0
import Formal.Net.CViewPS.RIslBnd42q1
import Formal.Net.CViewPS.RIslBnd42q2
import Formal.Net.CViewPS.RIslBnd42q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 42, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb42_ok : rb42.all rBndOK = true :=
  all_quarters rBndOK rb42 (by decide) rbb42_ok_q0 rbb42_ok_q1 rbb42_ok_q2 rbb42_ok_q3

end Formal.Net.CViewPS
