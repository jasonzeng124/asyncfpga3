import Formal.Core.XAudit.Events2PinDesign

/-!
# Wip/Events2Pin — open statements left by the per-pin race checker (shard A)

NOT BUILT, NOT CLAIMED. Every `sorry` below is open. Notes: `formal/notes/A-events2pin.md`.
The proved part is `Formal/Core/XAudit/Events2PinDesign.lean` (`design_behP`,
`design_safe_pin`) and `Events2Pin.lean` (`sound_pin`, executable `xevents2pin`).

1. (closed) the per-window bound is now proved: `Events2PinDesign.cycle_le_pin`.
   Open: the long-run certificates (`Events2Time.UpCert`/`LoCert`) for `BehP`.

2. `gcd_pin` (the gcd_hw control). `xevents2pin`'s domain is `Events2` (C-elements,
   buffer chains, eager environment); gcd_hw's control has merges, arbiters and guarded
   pins (A-events4), whose per-behaviour theorem `Beh4.safe` is itself open
   (`Wip/Events4.lean`). The per-pin version is that theorem with `BehP`'s per-pin
   warps; the gcd per-pin margins in the notes are from the untrusted analysis.
-/

namespace Formal.Wip.Events2Pin

open Formal.Core.XAudit.Events2 Formal.Core.XAudit.Events2Strict

/-- (2) gcd_hw: shape only. -/
theorem gcd_pin : True := by
  sorry -- OPEN: needs Beh4.safe (Wip/Events4.lean) restated over per-pin warps

end Formal.Wip.Events2Pin
