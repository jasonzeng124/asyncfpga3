import Formal.Core.XAudit.Events2Pipe3

/-!
# Wip/Events2 — open items of probe A-events2 (NOT claimed; `sorry` marks each)

Proved: `Formal/Core/XAudit/Events2*.lean` (see `formal/notes/A-events2.md`).
None of the statements below is used by a claimed file.
-/

namespace Formal.Core.XAudit.Events2.Wip

open Formal.Core.XAudit.Events2

/-- W1 (about 0.5 day). Event-window certificates for an OPEN-LOOP stimulus
(`designs/pipe3.stim.json`): tables `early j k`, `late j k` checked locally by
`decide` against the recurrences that `windows.py` evaluates
(`early ≥ early(src, k - off) + lo`, `late ≥ late(src, k - off) + hi`, both
proved one-step facts: `Beh.walk_le`, `Beh.ge_pins`) give
`t < early j k → M t j < k` and `late j k ≤ t → k ≤ M t j`. Then (i) the
open-loop sender/receiver satisfy the environment half of `Back` (each edge
after its partner's latest event plus `hiQ - loG`), so `safe` holds for the
stimulus without the channel model, and (ii) the 12 windows that
`windows.py` prints (identical to XSim's) become a theorem. Needs the
environment as a count-carrying source in `Beh` (a third pin kind) in place of
the channel. -/
theorem openloop_windows_shape : True := by
  sorry -- W1

/-- W2 (about 0.5 day). Per-window LOWER bound (at least `k` events in every
window of length `L` after `R`), not only the long-run rate of `rate_lower`:
needs a max-plus "cycle time" argument with a transient bound (the potentials
give it with an additive constant; a per-window statement needs the
transient to be bounded by the potential span, as in `EventsRing.hops_lower`). -/
theorem window_lower_shape : True := by
  sorry -- W2

/-- E5 (research, 3-5 days, unchanged from A-events): data-dependent choice
(mux/steer/merge, `bd_arbiter`). A count per CHANNEL; the token's path depends
on data, so the counter graph is no longer a marked graph. -/
theorem choice_shape : True := by
  sorry -- E5

/-- E6 (2-3 days, unchanged): bundling inside loops — data valid before the
latch-enable event, as a separation from the request event, using that the
state at each event is a function of the counts (`Beh.safe`). -/
theorem bundling_shape : True := by
  sorry -- E6

end Formal.Core.XAudit.Events2.Wip
