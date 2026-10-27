import Formal.Core.Discretize
import Formal.Core.Trace.Bridge
import Formal.Core.Trace.Event

/-!
# Audit shard A: discretisation and the event-list bridge

Non-vacuity of `circuit_sample` / `transfer` (a concrete circuit, behaviour,
quantum and widened bounds satisfying every field of `Discretizes`), and a
check that `Trace/Bridge`'s `EvTrace` is the same object as `Trace/Event`'s
`Sig` (Bridge redefines it instead of importing it).
-/

noncomputable section

namespace Audit.A

open Formal.Core Formal.Core.Discretize

/-- Net `false`: primary input, a clean step at 2/5. Net `true`: a buffer of
net `false` through a [3/2, 3/2] channel. -/
def C1 : CCircuit Bool where
  drv n := n = true
  f _ v := v false
  lo _ := 3/2
  hi _ := 3/2

def v1 : Bool → ℝ → Bool
  | false => step25
  | true => fun s => step25 (s - 3/2)

theorem v1_beh : C1.Beh v1 := by
  intro n hn
  cases n
  · cases hn
  · exact DelayPure.chan_shift le_rfl le_rfl step25

theorem v1_disc : Discretizes 1 C1 (fun _ => 1) (fun _ => 2) v1 := by
  have hs := (lo_round_down_needed 2).2.1
  have hr := (lo_round_down_needed 2).2.2.1
  refine ⟨one_pos, fun _ _ => by simp [C1]; norm_num, fun _ _ => by simp [C1]; norm_num,
    fun n hn => ?_, fun n hn => ?_⟩
  · show Sep 1 (fun t => v1 false t); exact hs
  · show AtRest (fun t => v1 false t); exact hr

/-- All hypotheses of circuit_sample at once. -/
theorem v1_sampled : (C1.widen (fun _ => 1) (fun _ => 2)).Beh (sampleAll 1 v1) :=
  circuit_sample v1_beh v1_disc

/-- transfer instance: a discrete property (the output sample at step 3 is 1). -/
example : sampleAll 1 v1 true 3 = true := by
  simp [sampleAll, sample, v1, step25]; norm_num

/-! ## Bridge.EvTrace vs Event.Sig: same denotation -/

theorem flips_same : ∀ (l : List ℝ) (t : ℝ),
    Formal.Core.Bridge.flips l t = Formal.Core.TraceEvent.flips l t
  | [], _ => rfl
  | a :: l, t => by
      simp only [Formal.Core.Bridge.flips, Formal.Core.TraceEvent.flips, flips_same l t]


#print axioms Formal.Core.Discretize.chan_sample
#print axioms Formal.Core.Discretize.circuit_sample
#print axioms Formal.Core.Discretize.transfer
#print axioms Formal.Core.Discretize.mutex_between
#print axioms Formal.Core.Discretize.tie_counterexample
#print axioms Formal.Core.Discretize.loop_of_continuous
#print axioms Formal.Core.Bridge.range_toFun
#print axioms v1_sampled

end Audit.A
