import Formal.Cells.RigLaps

/-!
# Probe Blcw (shard B): `lap_cut_fails` has a joint instance

Audit P13 (5a) found that the library's own non-vacuity lemma `pend_fast_nonvacuous` covers
`lapinv_fails_pend_fast` but NOT `RigLaps.lap_cut_fails` (no `Ring`, no close), and built an
instance in `audit/lean/P13/T5_Laps.lean`. This file takes that instance into the library
(auditor's construction, re-checked here; `R_mono'` is the auditor's lemma).

**Proved:** `lap_cut_fails_instance`: every hypothesis of `lap_cut_fails` holds jointly on the
channel map `chL` (start.req and out0.ack from B's lap witness `W`, second close s = 12, re-offer
r = 11, fork delay dF = 1, upsnk delay dP = 0), so its conclusion `¬ LapInv a b chL 13` is
reached on a concrete map. **NOT covered:** `chL` constrains only start, out0 and p_end; it is
not a gcd_hw circuit run, so this shows consistency of the hypotheses, not that they arise in
a real network run, and "expected on silicon" (FEASIBILITY) stays unproved. Core Lean only.
-/

namespace Formal.Cells.RigLapsWit
open Formal.Cells.RigToken Formal.Cells.RigLaps
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

theorem R_mono' (x : Nat → Bool) (T0 : Nat) {a b : Nat} (h : a ≤ b) : R x T0 a ≤ R x T0 b := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (Nat.le_of_lt_succ h); show _ ≤ R x T0 b + _; omega
    · rw [h]; exact Nat.le_refl _

/-- A channel map carrying the lap witness `W` (start.req = W.e, out0.ack = W.q) and a
p_end loop with fork delay dF = 1 and upsnk delay dP = 0. -/
def chL : Fin NC → Chan := fun c =>
  if c = out0 then ⟨W.e, W.q, fun _ => 0⟩
  else if c = pend then ⟨fun t => W.e (t - 1), fun t => W.e (t - 1), fun _ => 0⟩
  else ⟨W.e, W.e, fun _ => 0⟩

/-- **All hypotheses of `lap_cut_fails` hold jointly** (lap k = 2, close s = 12, re-offer
r = 11), so its conclusion is obtained on a concrete instance. -/
theorem lap_cut_fails_instance (a b : Nat) : ¬ LapInv a b chL 13 := by
  have hs : (chL start).req = W.e := by funext t; rfl
  have ho : (chL out0).ack = W.q := by funext t; rfl
  have hp : chL pend = ⟨fun t => W.e (t - 1), fun t => W.e (t - 1), fun _ => 0⟩ := rfl
  have H : Ring (chL start).req (chL out0).ack 0 0 id id := by rw [hs, ho]; exact W.ring
  refine lap_cut_fails a b chL H 1 0 2 12 (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_
  · rw [ho]; decide
  · rw [ho]; decide
  · intro t _; rw [hp, hs]
  · intro t _; rw [hp]; simp
  · intro r hr hR
    rw [hs] at hr hR
    rcases Nat.lt_or_ge r 12 with hlt | hge
    · omega
    · have h12 : R W.e 0 12 ≤ R W.e 0 r := R_mono' _ _ hge
      have : R W.e 0 12 = 2 := by decide
      omega

end Formal.Cells.RigLapsWit
