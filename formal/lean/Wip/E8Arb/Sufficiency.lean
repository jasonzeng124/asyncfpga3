import Formal.Core.XAudit.Events9Arb

/-!
# Wip/E8Arb/Sufficiency.lean — NOT BUILT, NOT CLAIMED (probes E8Arb, E8ArbFix)

The open part of the sufficiency direction, against the CORRECTED core (`Events9Arb.CoreOf`).
`Events9Arb.core_of_en` (proved) reduces "the real cell is a corrected-core behaviour" to the
existence of ONE `ctl` (a `VCtl (loCtl B) 10^12` of `A0`) and selects `sv1 … sv4` satisfying the
pointwise enable conditions `EnOK` at the four readers (g1, g2, the two R0 terms). What is open is
the ROUND CONSTRUCTION of that enable from the environment's behaviour:

  round k = the k-th low phase `[a_k, b_k)` of `A0`; winner `w_k` = the sense of `q` after the
  round's flip (or the current sense if `q` does not move); ctl rises at
  `c_k = max (a_k + loCtl + 1) (tq_k + K)` (`tq_k` = the flip time), falls at
  `e_k ∈ [b_k + loCtl + 1, …]` after every reader's rise of round k and before every reader's
  fall of round k, each read at its own `q`-pin time plus `K`; `σ` = `w_k` while ctl is in round k.

`arbfix/member.py` performs exactly this construction on recorded per-pin runs and checks the
virtual equations at every ps (untrusted): 9/9 arbiters MEMBER on every base run.

The hypotheses the construction needs (each is used by one of the three `EnOK` cases):
* (P-rise) a request-caused rise of reader X in round k comes at least `DA0lo + Dq(X)` after `a_k`
  (the corrected `PortProto.g_rise_late`; old core needed 2 more steps);
* (P-fall) a request-caused fall of reader X in round k comes at least `DA0lo + Dq(X)` after `b_k`
  and after every rise of round k, in q-read time (corrected `g_fall_late`);
* (RT1/RT1b, B) the falling grant's request read beats the `q` flip at that grant, so no reader
  falls by a `q` flip while its request is high;
* (Unc W) one `q` move per round, a clean transition (no runt: B's `fix_at_redge` regime);
* settled reset: all outputs low on `[0, T0 + 2]`, `T0 ≥` every `q`-pin band.
-/

namespace Formal.Core.XAudit.Events9Arb.Wip
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events8Arb
open Formal.Core.XAudit.Events9Arb

/-- OPEN (the round construction). Statement shape only: the protocol and RT1 hypotheses are
abstracted as `Hyp`; a usable version must spell them out (see the module doc). -/
theorem en_exists (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig) (W : Nat)
    (hP : ArbPin B r1 r2 rs a q R0 g1 g2) (hU : Unc W r1 r2 g1 g2) (Hyp : Prop) (hH : Hyp) :
    CoreOf B r1 r2 a R0 g1 g2 := by
  sorry

end Formal.Core.XAudit.Events9Arb.Wip
