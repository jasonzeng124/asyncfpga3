import Formal.Cells.ArbClean

/-!
# Formal.Cells.ArbCleanPS — the table facts of THE target gcd_ps's nine arbiter state LUTs

Shard B, THE goal (target `gcd_ps_e6bb4aec`, since 2026-11-01 19:35).

## Problem, plainly
`ArbClean.q_clean_set_gen` decides a separated arbitration from two facts about the state LUT's
table (set: r1 = 1, r2 = 0, rst = 0, A0 = 0 forces q = 1; conflict: r1 = 1, q = 1, rst = 0 keeps
q = 1). Do the nine state LUTs decoded from the gcd_ps bitstream have these facts, with the pin roles
read off their tables?

## Result
`targetQPS_facts`: yes, all nine (kernel `decide`). `targetQPS_swap_fails`: negative control.

## Not shown
The rows are GENERATED data (tools-B/target/gen_targetq.py on tools-B/target/lean2json.py output of
`Formal/Target/NetPS`); that they ARE gates of `Formal.Target.DecodedPS.net` is a separate link
(as `TargetLink` does for the previous target). The pin roles come from the generator's tracing.
Nothing about timing: separation of the two requests at each arbiter is still to be derived.
-/

namespace Formal.Cells.ArbCleanPS
open Formal.Cells.ArbClean

/-- (name, k, INIT, roles ⟨r1, r2, fb, rst, a0, tied⟩) of each gcd_ps ustate O6 gate. -/
def targetQPS : List (String × Nat × Nat × Roles) := [
  ("SLICE_X38Y51.BLUT.O6", 6, 0xffffaab2e4e4e4e4, ⟨2, 1, 0, 4, 3, [(5, true)]⟩),
  ("SLICE_X39Y24.ALUT.O6", 6, 0xffefaaaeccccf0f0, ⟨1, 2, 4, 0, 3, [(5, true)]⟩),
  ("SLICE_X16Y25.BLUT.O6", 6, 0xffffaba2ee44ee44, ⟨3, 1, 0, 4, 2, [(5, true)]⟩),
  ("SLICE_X16Y31.ALUT.O6", 6, 0xfffbf1f0ff00cccc, ⟨3, 1, 4, 2, 0, [(5, true)]⟩),
  ("SLICE_X16Y18.DLUT.O6", 6, 0xffefff02aaaaf0f0, ⟨0, 2, 4, 3, 1, [(5, true)]⟩),
  ("SLICE_X14Y18.ALUT.O6", 6, 0xffefccceaaaaf0f0, ⟨0, 2, 4, 1, 3, [(5, true)]⟩),
  ("SLICE_X14Y19.ALUT.O6", 6, 0xfcfcfddcfa0afa0a, ⟨3, 0, 2, 1, 4, [(5, true)]⟩),
  ("SLICE_X18Y24.ALUT.O6", 6, 0xfffdcdccff00aaaa, ⟨3, 0, 4, 1, 2, [(5, true)]⟩),
  ("SLICE_X39Y21.CLUT.O6", 6, 0xffabff8afafa5050, ⟨4, 2, 0, 3, 1, [(5, true)]⟩)]

/-- **All nine gcd_ps ustates meet both table facts.** -/
theorem targetQPS_facts :
    targetQPS.all (fun r => setFact r.2.1 r.2.2.1 r.2.2.2 && confFact r.2.1 r.2.2.1 r.2.2.2) = true := by
  decide +kernel

/-- Negative control: swapping r1 and r2 of the first gate breaks the set fact. -/
theorem targetQPS_swap_fails :
    setFact 6 0xffffaab2e4e4e4e4 ⟨1, 2, 0, 4, 3, [(5, true)]⟩ = false := by decide +kernel

end Formal.Cells.ArbCleanPS
