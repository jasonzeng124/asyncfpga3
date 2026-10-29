import Formal.Core.XAudit.Events8Arb

/-!
# Wip/E8Arb/Sufficiency.lean — NOT BUILT, NOT CLAIMED (probe E8Arb)

The sufficiency direction, as statements only. Everything below is OPEN (`sorry`).
See `formal/notes/A-e8arb.md` §4–§6.

Why the target is NOT `HARB7` itself: `Events8Arb.unc_not_harb` (proved) gives an
uncontested behaviour of the real cell that is not a behaviour of HARB7's virtual core as
events4/model.py / cert8 encode it (R0 = OR of the grants after the grants, and the ctl band
2 steps late). So the target is a CORRECTED virtual core `VCore'`:

* ctl: `VCtl (lo_c - 2) 10^12` with `lo_c` = cert8's value (A0 pin + state LUT + q pin lower
  ends) — the `(1,1)` stage band of ctl and the `(1,1)` filtered-pin band take 2 steps;
* grants: `VGrant` unchanged;
* R0: NOT an OR of the grants. A merge of two SHADOW grants `g'_b` (virtual C-elements of the
  same shape as `g_b`, but with the request band of `ustate`'s `r_b` pin and stage band of
  `ustate` O5), so `R0` can rise before or after `g_b`, as the real `r_b·q` / `r_b·¬q` at the
  two LUTs do.
-/

namespace Formal.Core.XAudit.Events8Arb.Wip
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events8Arb

/-- Cell-level environment protocol of the arbiter's ports (assumed on the real wires; what
the verdict's counts would supply under a prefix induction, notes §5): A0 rises only while R0
is high, falls only while R0 is low; a request falls only after its ack, i.e. after A0 rose
(stated with the latency `dA` = cert8's `lo_c + loF + 2`, the corrected ctl band). -/
structure PortProto (dA : Nat) (r1 r2 a R0 g1 g2 : Sig) : Prop where
  a_up : ∀ t, a t = false → a (t + 1) = true → R0 t = true
  a_dn : ∀ t, a t = true → a (t + 1) = false → R0 t = false
  g_fall_late : ∀ t, (g1 t = true ∧ g1 (t + 1) = false) ∨ (g2 t = true ∧ g2 (t + 1) = false) →
    ∃ u, u + dA ≤ t ∧ a u = true
  g_rise_late : ∀ t, (g1 t = false ∧ g1 (t + 1) = true) ∨ (g2 t = false ∧ g2 (t + 1) = true) →
    ∀ u, t + 1 ≤ u + dA → u ≤ t + 1 → a u = false

/-- OPEN: an uncontested real `bd_arbiter` core (per-pin, real INITs), settled at time 0 with
`q = 1`, with B's handover conditions (RT1 / RT1b: the falling grant's request read beats the
q flip at the other grant) and the port protocol, is a behaviour of the corrected virtual core
(ctl at `lo_c - 2`, grants, shadow-grant R0), with `σ` = the winner of each ctl round. Only the
grant part is stated here. AS WRITTEN THE STATEMENT IS INCOMPLETE (probably false): it still
lacks W ≥ W_arb (notes §2), the time-0 settledness / reset, RT1 / RT1b, the band containment
`B.g_b pin 0 ⊆ [loR + loF, hiR + hiF]`, and `σ`'s SelOK; it is a target, not a claim. -/
theorem arb_virtual_of_unc (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig) (W dA : Nat)
    (hP : ArbPin B r1 r2 rs a q R0 g1 g2) (hU : Unc W r1 r2 g1 g2) (hE : PortProto dA r1 r2 a R0 g1 g2)
    (loF hiF loR hiR lo : Nat) (hsplit : loF + lo + 2 ≤ dA) :
    ∃ ctl, VCtl lo (10 ^ 12) a ctl ∧ VGrant loF hiF loR hiR true r1 ctl g1 ∧
      VGrant loF hiF loR hiR false r2 ctl g2 := by
  sorry

end Formal.Core.XAudit.Events8Arb.Wip
