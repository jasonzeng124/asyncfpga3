import Formal.Net.MullerTimed
import Formal.Net.MullerSI

/-!
# Probe 8g: instances (n = 1, 2, 3)

`checkT n = true` by `decide +kernel` (kernel evaluation of the BFS
certificate and the per-state checks of `MullerTimed`; no native code),
then the generic theorems of `MullerTimed` with 8c's `rt_good_n`.

For n = 1, 2, 3 stages, every timed trace of the real chain (every LUT,
wire, feedback route and the environment an inertial channel with its own
bounds, the feedback route a free wire) that satisfies `FbBound` is a run of
8c's rt semantics, hence: four-phase protocol on every link, token order,
and no glitch on any node. n = 4 is not attempted (8c's rt n = 4 BFS runs out
of memory in the kernel; `#eval checkT 4` is `true`, uncertified).
-/

namespace Formal.Net.MullerTimed
open Formal.Net Formal.Net.Muller

theorem checkT_1 : checkT 1 = true := by decide +kernel
theorem checkT_2 : checkT 2 = true := by decide +kernel
theorem checkT_3 : checkT 3 = true := by decide +kernel

theorem cert_1 : Cert 1 := checkT_sound checkT_1
theorem cert_2 : Cert 2 := checkT_sound checkT_2
theorem cert_3 : Cert 3 := checkT_sound checkT_3

variable {lo hi : Nat → Nat} {x : Nat → Nat}

/-! ## n = 3: the main statements -/

/-- **H_FB_BEFORE_INPUT from delay bounds (n = 3).** Every timed state is
reachable in 8c's relative-timing semantics. -/
theorem timed3_reach (hT : Timed 3 lo hi x) (hB : FbBound 3 lo hi) (t : Nat) :
    Reach .rt 3 (x t) := timed_reach hT cert_3 hB.guards t

/-- Every ps of a timed trace, serialized, is an rt run (n = 3). -/
theorem timed3_step_run (hT : Timed 3 lo hi x) (hB : FbBound 3 lo hi) (t : Nat) :
    RunL 3 (x t) (chg 3 x t) ∧ finalL (x t) (chg 3 x t) = x (t + 1) :=
  timed_step_run hT cert_3 hB.guards t

/-- Four-phase protocol on every link, for every timed trace (n = 3). -/
theorem timed3_protocol (hT : Timed 3 lo hi x) (hB : FbBound 3 lo hi) {X Y : Nat}
    (hp : (X, Y) ∈ pairs 3) :
    Handshake.Protocol ⟨fun t => get (x t) X, fun t => get (x t) Y, fun _ => 0⟩ :=
  timed_protocol hT cert_3 hB.guards rt_good_3 hp

/-- Token order between consecutive stages, for every timed trace (n = 3). -/
theorem timed3_token_order (hT : Timed 3 lo hi x) (hB : FbBound 3 lo hi) {k : Nat}
    (hk1 : 1 ≤ k) (hkn : k < 3) (t : Nat) :
    tog (fun t => get (x t) (c k)) t ≤ tog (fun t => get (x t) (c (k - 1))) t ∧
    tog (fun t => get (x t) (c (k - 1))) t ≤ tog (fun t => get (x t) (c k)) t + 1 :=
  timed_token_order hT cert_3 hB.guards rt_good_3 hk1 hkn t

/-- No glitch on any LUT, wire or environment node, in time (n = 3). -/
theorem timed3_hazard_free (hT : Timed 3 lo hi x) (hB : FbBound 3 lo hi) {t i : Nat}
    (hiN : i < numNodes 3) (he : nextVal .free 3 (x t) i ≠ get (x t) i)
    (hs : get (x (t + 1)) i = get (x t) i) :
    nextVal .free 3 (x (t + 1)) i ≠ get (x (t + 1)) i :=
  timed_hazard_free hT cert_3 hB.guards rt_good_3 hiN he hs

/-! ## n = 1, 2 -/

theorem timed1_protocol (hT : Timed 1 lo hi x) (hB : FbBound 1 lo hi) {X Y : Nat}
    (hp : (X, Y) ∈ pairs 1) :
    Handshake.Protocol ⟨fun t => get (x t) X, fun t => get (x t) Y, fun _ => 0⟩ :=
  timed_protocol hT cert_1 hB.guards rt_good_1 hp

theorem timed1_hazard_free (hT : Timed 1 lo hi x) (hB : FbBound 1 lo hi) {t i : Nat}
    (hiN : i < numNodes 1) (he : nextVal .free 1 (x t) i ≠ get (x t) i)
    (hs : get (x (t + 1)) i = get (x t) i) :
    nextVal .free 1 (x (t + 1)) i ≠ get (x (t + 1)) i :=
  timed_hazard_free hT cert_1 hB.guards rt_good_1 hiN he hs

theorem timed2_protocol (hT : Timed 2 lo hi x) (hB : FbBound 2 lo hi) {X Y : Nat}
    (hp : (X, Y) ∈ pairs 2) :
    Handshake.Protocol ⟨fun t => get (x t) X, fun t => get (x t) Y, fun _ => 0⟩ :=
  timed_protocol hT cert_2 hB.guards rt_good_2 hp

theorem timed2_token_order (hT : Timed 2 lo hi x) (hB : FbBound 2 lo hi) (t : Nat) :
    tog (fun t => get (x t) (c 1)) t ≤ tog (fun t => get (x t) (c 0)) t ∧
    tog (fun t => get (x t) (c 0)) t ≤ tog (fun t => get (x t) (c 1)) t + 1 :=
  timed_token_order hT cert_2 hB.guards rt_good_2 (k := 1) (by decide) (by decide) t

theorem timed2_hazard_free (hT : Timed 2 lo hi x) (hB : FbBound 2 lo hi) {t i : Nat}
    (hiN : i < numNodes 2) (he : nextVal .free 2 (x t) i ≠ get (x t) i)
    (hs : get (x (t + 1)) i = get (x t) i) :
    nextVal .free 2 (x (t + 1)) i ≠ get (x (t + 1)) i :=
  timed_hazard_free hT cert_2 hB.guards rt_good_2 hiN he hs

end Formal.Net.MullerTimed
