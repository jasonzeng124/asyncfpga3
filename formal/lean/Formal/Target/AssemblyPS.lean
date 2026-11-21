import Formal.Target.Assembly
import Formal.Target.SpecMono
import Formal.Target.NetPS.All
import Formal.Target.BoundaryPS

/-!
# Formal.Target.AssemblyPS — the top-level assembly on THE target (gcd_ps_e6bb4aec)

Shard A, 2026-11-06. **Plainly:** THE target's decoded boundary has one request node for `a`, `b`, `start` and the
end channel (`oneReq_PS`), so `Assembly.netCorrectSeq_of_plan` applies to it: THE statement on THE target follows
from a `Plan` (base, quiet, per-pair step) for every behaviour meeting its hypotheses (`the_of_plan`), and then,
by `SpecMono.seq_weaken`, for every smaller `(g, κ)` and `T` and larger `su`, `Δo` (`the_of_plan_weaken`).
What remains for THE theorem is exactly the `Plan` hypothesis below. Not shown: that hypothesis.
-/

namespace Formal.Target.AssemblyPS
open Formal.Target Formal.Target.Assembly Formal.Target.DecodedPS

theorem oneReq_PS : OneReq boundary := ⟨rfl, rfl, rfl⟩

/-- **THE statement on THE target, from a plan.** -/
theorem the_of_plan {p : DelayPar} {T R su Δo : Nat}
    (h : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x → ArbOK T arbs x →
      Env x boundary R su Δo n va vb → SeqEnv x boundary R → ∃ I, Plan x boundary R Δo I) :
    NetCorrectSeq net boundary arbs p T R su Δo :=
  netCorrectSeq_of_plan oneReq_PS h

/-- **THE theorem's shape** (Spec part II, with the Lean round trip `FormalWit.RTPS.Data.roundtrip` in place of a Lean
decoder): the decoded netlist is well formed, its boundary consistent, and THE statement holds, given a plan. -/
theorem the_shape_of_plan {p : DelayPar} {T R su Δo : Nat}
    (h : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x → ArbOK T arbs x →
      Env x boundary R su Δo n va vb → SeqEnv x boundary R → ∃ I, Plan x boundary R Δo I) :
    net.WF ∧ boundary.OK net ∧ NetCorrectSeq net boundary arbs p T R su Δo :=
  ⟨net_wf, boundary_ok, the_of_plan h⟩

/-- The same, carried to every smaller `(g, κ)`, `T` and larger margins. -/
theorem the_of_plan_weaken {p p' : DelayPar} {T T' R su su' Δo Δo' : Nat} (hp : p.LE p') (hT : T ≤ T')
    (hs : su ≤ su') (hd : Δo ≤ Δo')
    (h : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p' (circuit net boundary) x → ArbOK T' arbs x →
      Env x boundary R su Δo n va vb → SeqEnv x boundary R → ∃ I, Plan x boundary R Δo I) :
    NetCorrectSeq net boundary arbs p T R su' Δo' :=
  seq_weaken hp hT hs hd (the_of_plan h)

end Formal.Target.AssemblyPS
