import Formal.Core.XAudit.EventsDesign

/-!
# Wip/Events — open items of probe A-events (NOT claimed; `sorry` marks each)

What is proved is in `Formal/Core/XAudit/Events*.lean` (see
`formal/notes/A-events.md`). The statements below are the next steps, as
shapes. None of them is used by a claimed file.
-/

namespace Formal.Core.XAudit.Events.Wip

open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Transport)

/-- E1 (about 0.5 day). Buffer CHAINS on a pin (bdc's `bd_delay` LUT1 lines
between stages, as in pipe3's `r[i]`): a chain of `IsBuf` gates from the
source node to the LUT pin is one transport channel with the summed band
(`TraceDiscrete.transport_comp`), so `Recog` can accept it and `design_beh`
goes through unchanged with `loG`/`hiG` = sums. Shape only. -/
theorem buf_chain_transport : True := by
  sorry -- E1: induction on the chain with transport_comp

/-- E2 (about 1 day). OPEN networks (pipes): a pin read from an environment
port. The environment is a handshake partner with a count `Me` and two
hypotheses: it is never more than one phase ahead of the stage it talks to,
read through a round trip no faster than that stage's own feedback
(`Me s ≤ M (Q j s) j + 1`, the env half of `pin_le_q`), and (for liveness)
it answers within a bound. `safe` then holds for every internal stage of a
pipe with the same proof (only `pin_le_q` changes for env pins). The
stimulus of `designs/pipe3.stim.json` would discharge these by `decide`. -/
theorem open_safe_shape : True := by
  sorry -- E2: Beh with env pins; pin_le_q from the env hypothesis

/-- E3 (about 1-2 days). Period bounds for every recognised net, not only
ring3: the counter inequalities `M t j ≤ M (t - d) (src j p) + off j p` and
(after reset) `min_p (M t (src j p) + off j p) ≤ M (t + D) j` give, for every
simple cycle `C`, `Σ_{C} M` grows by at most `tok(C)` per `Σ_C lo` and the
max-ratio cycle grows by at least `tok(C)` per `Σ_C hi`: the event spacing of
every node lies in the max-cycle-ratio interval that `xevents` prints (today
computed, proved for ring3 only, `EventsRing.node_period`). -/
theorem period_general_shape : True := by
  sorry -- E3: max-plus cycle-ratio bounds for strongly connected nets

end Formal.Core.XAudit.Events.Wip
