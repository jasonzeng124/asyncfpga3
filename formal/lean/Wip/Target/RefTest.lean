import Formal.Target.Wit.V9V4.Top
import Formal.Target.WitBoundary
import Mathlib.Tactic.IntervalCases

namespace Formal.Target.Wit.V9V4.Test
open Formal.Target Formal.Target.Wit Formal.Target.Decoded Formal.Target.Wit.V9V4

theorem hP : 0 < P := by decide
theorem hPb : P + Dm ≤ b := by decide
theorem hPlo : P ≤ b - Dm := by decide

theorem arbChk : ∀ a ∈ arbs, (D a.q).ok = true ∧ (∀ n ∈ a.ins, (D n).ok = true) ∧
    arbFlipsOK 656 (D a.q) (a.ins.map D) = true ∧ (∀ τ ∈ (D a.q).ts, τ + P < b) ∧
    (∀ n ∈ a.ins, ∀ τ ∈ (D n).ts, τ + P < b) := by decide +kernel

theorem quiet_eq (n : Nat) (h : ∀ τ ∈ (D n).ts, τ + P < b) : ext D b P n = (D n).val :=
  funext (ext_eq_val D hP (by have := hPb; omega) h)

/-- **H_ARB(656) holds in the witness.** -/
theorem arb_ok : ArbOK 656 arbs (ext D b P) := by
  intro a ha t1 t2 hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := arbChk a ha
  rw [quiet_eq _ h4]
  exact arbOK_one 656 _ _ h1 (fun d hd => by obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hd; exact h2 n hn) h3 t1 t2
    (fun d hd => by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hd
      have := hc n hn; rw [quiet_eq _ (h5 n hn)] at this; exact this)

/-- The boundary nodes and their flips. -/
def bnodes : List Nat := [boundary.rst, boundary.a.req, boundary.a.ack, boundary.b.ack, boundary.start.ack,
  boundary.out0.req, boundary.out0.ack, boundary.pend.ack] ++ boundary.a.data ++ boundary.b.data ++ boundary.out0.data

noncomputable def bp : List Nat := bnodes.flatMap fun n => (D n).ts

theorem bchk : ∀ n ∈ bnodes, (D n).ok = true ∧ (∀ τ ∈ (D n).ts, τ + P < b) ∧ (∀ τ ∈ (D n).ts, τ ∈ bp) := by
  decide +kernel

theorem bcap : ∀ x ∈ bp, x < b := by decide +kernel

theorem bq (n : Nat) (hn : n ∈ bnodes) : ext D b P n = beh D n := quiet_eq n (bchk n hn).2.1

def va (k : Nat) : Nat := if k = 0 then 65536 else if k = 1 then 1 else 0
def vb (k : Nat) : Nat := if k = 0 then 4096 else if k = 1 then 1 else 0

theorem env_a : EnvIn (beh D) boundary.a 20000 0 (some 2) va :=
  envIn_of D bp b 10000000 20000 _ _ _ (by decide +kernel) (by decide +kernel) bcap (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem env_b : EnvIn (beh D) boundary.b 20000 0 (some 2) vb :=
  envIn_of D bp b 10000000 20000 _ _ _ (by decide +kernel) (by decide +kernel) bcap (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem env_s : EnvIn (beh D) boundary.start 20000 0 (some 2) (fun _ => 0) :=
  envIn_of D bp b 10000000 20000 _ _ _ (by decide +kernel) (by decide +kernel) bcap (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem env_o : EnvOut (beh D) boundary.out0 20000 2999 :=
  envOut_of D bp b 10000000 20000 _ _ (by decide +kernel) (by decide +kernel) bcap (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem env_p : EnvOut (beh D) boundary.pend 20000 2999 :=
  envOut_of D bp b 10000000 20000 _ _ (by decide +kernel) (by decide +kernel) bcap (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **The environment of the witness obeys H_ENV** (pipelined, broad data rule). -/
theorem env_ok : Env (ext D b P) boundary 20000 0 2999 (some 2) va vb := by
  have hrst : (D boundary.rst).ok = true ∧ (D boundary.rst).v0 = true ∧ (D boundary.rst).ts = [20000] := by decide +kernel
  have er : ext D b P boundary.rst = (D boundary.rst).val := bq _ (by decide +kernel)
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [er, val_before _ (T := 19999) (by rw [hrst.2.2]; simp) t (by omega)]; decide +kernel
  · rw [er, val_after _ (T := 20000) (by rw [hrst.2.2]; simp) t ht]; decide +kernel
  · simp only [Offered] at hk; interval_cases k <;> decide
  · exact envIn_congr _ _ _ _ _ _ _ (fun v hv => bq v (by revert v; decide +kernel) |>.trans rfl) env_a
  · exact envIn_congr _ _ _ _ _ _ _ (fun v hv => bq v (by revert v; decide +kernel) |>.trans rfl) env_b
  · exact envIn_congr _ _ _ _ _ _ _ (fun v hv => bq v (by revert v; decide +kernel) |>.trans rfl) env_s
  · exact envOut_congr _ _ _ _ _ (fun v hv => bq v (by revert v; decide +kernel) |>.trans rfl) env_o
  · exact envOut_congr _ _ _ _ _ (fun v hv => bq v (by revert v; decide +kernel) |>.trans rfl) env_p

/-- **`Correct` fails**: the first out0 value is not gcd of the first pair. -/
theorem not_correct : ¬ Correct (ext D b P) boundary 20000 2999 (some 2) va vb := by
  intro hC
  have eR : ext D b P boundary.out0.req = (D boundary.out0.req).val := bq _ (by decide +kernel)
  have eA : ext D b P boundary.out0.ack = (D boundary.out0.ack).val := bq _ (by decide +kernel)
  have hok : (D boundary.out0.req).ok = true := (bchk _ (by decide +kernel)).1
  have hgap : ∀ s, 861822 ≤ s → s ≤ 864821 → ext D b P boundary.out0.req s = true ∧ ext D b P boundary.out0.ack s = false := by
    intro s h1 h2
    rw [eR, eA]
    rw [(D boundary.out0.req).val_const h1 (fun y hy h3 => by
          have := (show ∀ y ∈ (D boundary.out0.req).ts, 861822 < y → 864821 < y by decide +kernel) y hy h3; omega),
        (D boundary.out0.ack).val_const (Nat.zero_le s) (fun y hy h3 => by
          have := (show ∀ y ∈ (D boundary.out0.ack).ts, 864821 < y by decide +kernel) y hy; omega)]
    decide +kernel
  have hd := hC.2.2.2.2.2.1 861821 864821 (by norm_num) (by rw [eR]; decide +kernel) (by rw [eR]; decide +kernel)
    (by norm_num) hgap
  rw [busVal_congr _ (beh D) _ _ (fun v hv => congrFun (bq v (by revert v; decide +kernel)) _), eR,
    rises_eq _ hok] at hd
  revert hd; decide +kernel

end Formal.Target.Wit.V9V4.Test
