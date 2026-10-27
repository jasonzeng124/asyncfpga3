import Formal.Core.XSim
/-! Auditor AB2: XSim non-vacuity witness for `fp_q_concrete`, and a dropped
hypothesis (`1 ≤ lo`) refuting `sound`. -/
namespace AB2.XSimAudit
open Formal.Core Formal.Core.XSim Formal.Core.XSim.Demo Formal.Core.K3
open Formal.Core.TraceDiscrete (Sig delay delay_transport transport_mono)

/-- q under the four-phase stimulus with all delays 1 (closed recursion). -/
def qfp : Nat → Bool
  | 0 => false
  | 1 => !stimFP 2 0 && maj (delay 1 (stimFP 0) 0) (delay 1 (stimFP 1) 0) (qfp 0)
  | t + 2 => !stimFP 2 (t + 1) && maj (delay 1 (stimFP 0) (t + 1)) (delay 1 (stimFP 1) (t + 1)) (qfp t)

def fpBeh : Fin 8 → Sig := fun w =>
  match w.val with
  | 4 => delay 1 (stimFP 0)
  | 5 => delay 1 (stimFP 1)
  | 6 => qfp
  | 7 => delay 1 qfp
  | _ => stimFP w

theorem qfp_eq (t : Nat) : qfp t = (!stimFP 2 (t - 1) && maj (delay 1 (stimFP 0) (t - 1))
      (delay 1 (stimFP 1) (t - 1)) (qfp (t - 1 - 1))) := by
  match t with
  | 0 => decide
  | 1 => rfl
  | t + 2 => simp only [qfp, show t + 2 - 1 = t + 1 by omega, show t + 1 - 1 = t by omega]

theorem fpBeh_sat : Circuit.Sat (toCircuit net) fpBeh := by
  intro g hg
  simp only [toCircuit, net, c2net, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · refine transport_mono (by simp only [buf]; omega) (by simp only [buf]; omega) (?_ : TraceDiscrete.Transport 1 1 _ _)
    have : fpBeh 4 = delay 1 ((buf 0 4 1 3).exc fpBeh) := by
      funext t; simp only [delay, buf_exc]; rfl
    show TraceDiscrete.Transport 1 1 _ (fpBeh 4)
    rw [this]; exact delay_transport _ _
  · refine transport_mono (by simp only [buf]; omega) (by simp only [buf]; omega) (?_ : TraceDiscrete.Transport 1 1 _ _)
    have : fpBeh 5 = delay 1 ((buf 1 5 1 3).exc fpBeh) := by
      funext t; simp only [delay, buf_exc]; rfl
    show TraceDiscrete.Transport 1 1 _ (fpBeh 5)
    rw [this]; exact delay_transport _ _
  · refine transport_mono (by simp only [c2lut]; omega) (by simp only [c2lut]; omega) (?_ : TraceDiscrete.Transport 1 1 _ _)
    have : fpBeh 6 = delay 1 ((c2lut 1 3).exc fpBeh) := by
      funext t; simp only [delay]; rw [c2lut_exc _ _ _ _ rfl]; exact qfp_eq t
    show TraceDiscrete.Transport 1 1 _ (fpBeh 6)
    rw [this]; exact delay_transport _ _
  · refine transport_mono (by simp only [buf]; omega) (by simp only [buf]; omega) (?_ : TraceDiscrete.Transport 1 1 _ _)
    have : fpBeh 7 = delay 1 ((buf 6 7 1 3).exc fpBeh) := by
      funext t; simp only [delay, buf_exc]; rfl
    show TraceDiscrete.Transport 1 1 _ (fpBeh 7)
    rw [this]; exact delay_transport _ _

theorem fpBeh_in : ∀ w, Undriven net w → fpBeh w = stimFP w := by
  intro w hw
  have h4 := net_undriven w hw
  simp only [fpBeh]; split <;> first | omega | rfl

/-- Joint non-vacuity of `fp_q_concrete`'s hypotheses, and its conclusion on the witness. -/
theorem fp_nonvacuous : ∃ x : Fin 8 → Sig, Circuit.Sat (toCircuit net) x ∧
    (∀ w, Undriven net w → x w = stimFP w) :=
  ⟨fpBeh, fpBeh_sat, fpBeh_in⟩

/-- Cross-check: the witness's q, computed directly, agrees with the spec at sample points. -/
example : qfp 17 = false ∧ qfp 22 = true ∧ qfp 33 = true ∧ qfp 38 = false := by decide

/-! ## Dropping `1 ≤ lo` breaks `sound` (zero-delay gate reads the previous row). -/
def zbuf : LGate 2 := { k := 1, lut := Init.delay_buf, ins := fun _ => 0, out := 1, lo := 0, hi := 0 }
def zin : Fin 2 → Sig := fun w t => if w.val = 0 then decide (1 ≤ t) else decide (1 ≤ t)

theorem zsat : ∀ g ∈ [zbuf], g.relW zin := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  intro t
  refine ⟨t, by simp [zbuf], by simp [zbuf], ?_⟩
  simp only [LGate.exc, zbuf, zin]
  cases h : decide (1 ≤ t) <;> simp_all [Lut.eval, Init.delay_buf] <;> decide

theorem sound_needs_lo :
    ¬ (∀ t w, val [zbuf] (fun w t => ofBool (zin w t)) (fun _ => K3.X) t w ⊑ ofBool (zin w t)) := by
  intro h
  have := h 1 1
  revert this; decide

#print axioms fp_nonvacuous
#print axioms sound_needs_lo
end AB2.XSimAudit
