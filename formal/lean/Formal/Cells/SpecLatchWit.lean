import Formal.Cells.SpecLatch
import Formal.Cells.SpecCElemWit

/-!
# Formal.Cells.SpecLatchWit — `latch_close` is not vacuous

Shard B, THE goal, S3. A 3-pin latch (INIT 0xD8: pin 0 = enable, pin 1 = data, pin 2 = feedback; output = data
when enabled, else feedback), unit arcs at `ArbTSpec.p1`; enable open on [0, 9] and closed from 10 on; data true
until 12 and false from 13 on; output = true from 1 on. `wit_close`: `latch_close` applies (τ = 10, We = Wd = 10,
A = 1, E = 100) and gives q = true on [1, 101]; `wit_data_falls` shows the data does change after the close, so the
conclusion says the latch HOLDS (it does not just follow a constant input).
-/

namespace Formal.Cells.SpecLatchWit

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain Formal.Cells.SpecLatch
open Formal.Cells.ArbTSpec (p1 e1 adm_e1)
open Formal.Cells.SpecCElemWit (sumAdm_e1)

def En : Sig := fun t => decide (t < 10)
def Dt : Sig := fun t => decide (t < 13)
def Q : Sig := fun t => decide (1 ≤ t)
def x : Beh := fun n => if n = 0 then En else if n = 1 then Dt else Q
def gL : Gate := ⟨"L", 3, 0xD8, [0, 1, 2], [e1, e1, e1], 2⟩
def arcs : Nat → List Arc := fun _ => [e1]

theorem bands : CBands p1 1 gL.k arcs (fun _ => 1) (fun _ => 1) := by
  intro i _ D hD
  rw [arcs, sumAdm_e1] at hD; subst hD; exact ⟨le_rfl, le_rfl⟩

theorem mux (a b c : Bool) :
    (0xD8 : Nat).testBit (addr 3 fun i => if i = 0 then a else if i = 1 then b else c) = (if a then b else c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem wit_gate : CGateOK p1 1 gL (fun i => i) arcs 1 x := by
  refine ⟨fun _ t => t - 1, fun _ _ _ _ h => Nat.sub_le_sub_right h 1, fun t ht => ⟨fun i _ => ?_, ?_⟩⟩
  · show t - 1 ≤ t ∧ SumAdm p1 1 (arcs i) (t - (t - 1))
    exact ⟨by omega, (sumAdm_e1 _).2 (by omega)⟩
  · have hx : (fun i => x i (t - 1)) = fun i => if i = 0 then En (t - 1) else if i = 1 then Dt (t - 1) else
        Q (t - 1) := by
      funext i; simp only [x]; split <;> [rfl; split <;> rfl]
    show x 2 t = (0xD8 : Nat).testBit (addr 3 fun i => x i (t - 1))
    rw [hx, mux]
    simp only [x, Q, En, Dt, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false]
    by_cases h1 : t - 1 < 10 <;> by_cases h2 : t - 1 < 13 <;> by_cases h3 : 1 ≤ t - 1 <;> simp [h1, h2, h3] <;> omega

theorem wit_close : ∀ s, 1 ≤ s → s ≤ 100 + 1 → x gL.out s = true :=
  latch_close wit_gate bands (e := 0) (d := 1) (j := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl le_rfl false false (fun _ => false) (fun _ => false)
    (fun v h _ => by
      have h0 : v 0 = true := by simpa using h
      show (0xD8 : Nat).testBit (addr 3 v) = (v 1 ^^ false)
      simp only [addr, h0]
      cases h1 : v 1 <;> cases h2 : v 2 <;> decide)
    (fun v h _ => by
      have h0 : v 0 = false := by simpa using h
      show (0xD8 : Nat).testBit (addr 3 v) = v 2
      simp only [addr, h0]
      cases h1 : v 1 <;> cases h2 : v 2 <;> decide)
    10 100 10 10 1 1 true (fun _ _ => le_rfl)
    (fun i _ h => by simp at h)
    (fun t _ h => by simp [x, En]; omega)
    (fun t h _ => by simp [x, En]; omega)
    (fun t _ h => by simp [x, Dt]; omega)
    le_rfl (by decide) (by decide) (by decide)

/-- The data falls after the close (at 13), while the latch output stays true. -/
theorem wit_data_falls : x 1 13 = false ∧ x 2 50 = true := by decide

end Formal.Cells.SpecLatchWit
