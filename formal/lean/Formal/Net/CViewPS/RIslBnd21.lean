import Formal.Net.CViewPS.RIslBnd21q0
import Formal.Net.CViewPS.RIslBnd21q1
import Formal.Net.CViewPS.RIslBnd21q2
import Formal.Net.CViewPS.RIslBnd21q3
import Formal.Net.CViewPS.RIslBndQ

/-! Shard C: delay bounds of reset-island block 21, from its four quarters (generated). -/

namespace Formal.Net.CViewPS

theorem rbb21_ok : rb21.all rBndOK = true :=
  all_quarters rBndOK rb21 (by decide) rbb21_ok_q0 rbb21_ok_q1 rbb21_ok_q2 rbb21_ok_q3

end Formal.Net.CViewPS
