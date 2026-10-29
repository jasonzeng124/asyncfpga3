import Formal.Core.XAudit.Events7Beh

namespace Formal.Core.XAudit.Events8Bridge

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7

/-- **What HARB7 asserts about a virtual stage (an arbiter grant).** Its value at `t` is
fixed by its pin reads at `F t` whenever they agree (and reset is off): it follows them,
with no hold of its own. -/
theorem nd7_follow {N : Nat} {net : Net4 N} {b : Bands4 net} {cc : Fin N → Sig} {j : Fin N}
    (nd : ND7 net b cc j) (hm : net.mg j = false) (t : Nat) (y : Bool)
    (hr : nd.r (nd.F t) = false) (hall : ∀ p, (nd.pin p (nd.F t) ^^ net.neg j p) = y) :
    cc j t = y := by
  rw [nd.hc t]
  simp only [hm, Bool.false_eq_true, ite_false, hr]
  exact Events2.cel_all _ _ _ (net.ar_pos j) hall

/-- **Bounded response (no eternal oscillation).** If from `t0` on reset is off and every
pin read of a virtual stage is steady at `y`, the stage is `y` from `t0 + hiF` on. A grant's
pins are its request and `ctl` filtered by the free select `sv` (σ); with SelOK on that pin
σ is fixed per `ctl` transaction, so with steady requests and a steady `ctl` the virtual
grants are steady. B's `ArbInvolution.arb_grants_eternal` (the decision element's grants
pulse forever at the critical request gap, requests steady) is not such a behaviour:
HARB7 + SelOK can hold only on traces where that contest does not occur. -/
theorem nd7_steady {N : Nat} {net : Net4 N} {b : Bands4 net} {cc : Fin N → Sig} {j : Fin N}
    (nd : ND7 net b cc j) (hm : net.mg j = false) (y : Bool) (t0 : Nat)
    (hr : ∀ s, t0 ≤ s → nd.r s = false)
    (hp : ∀ s, t0 ≤ s → ∀ p, (nd.pin p s ^^ net.neg j p) = y) :
    ∀ t, t0 + b.hiF j ≤ t → cc j t = y := by
  intro t ht
  have := nd.wF.early_le t
  exact nd7_follow nd hm t y (hr _ (by omega)) (hp _ (by omega))

end Formal.Core.XAudit.Events8Bridge
