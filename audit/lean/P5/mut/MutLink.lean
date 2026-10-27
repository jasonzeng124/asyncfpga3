import Formal.Cells.ContractsLink
namespace Formal.Cells.ContractsLink.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.Contracts
open Formal.Cells.OpsTimed (Tok)
open Formal.Cells.LinkTimed (CtlEnv DataPath cph Vph Vph_e Vph_o par_cases)
open Formal.Cells.PipeTimed (Ret fifo_hold)
open Formal.Net.Ops.Link (linkEq)
open Formal.Cells.PipeTimedN Formal.Cells.PipeTimedN.Wit Formal.Cells.PipeTimed.Wit
theorem pipe_witness_mut (N : Nat) (hN : 1 ≤ N) :
    Port ⟨rW 0, ainW, fun t => busVal 1 (fun _ => dW t)⟩ (Pw N).ρ
      (fun j => (Ret.shift 1).fst ((Pw N).τ 0 j)) (fun k => busVal 1 (valW k)) ∧
    Port ⟨routW N, aW ((Pw N).N - 1), fun t => busVal 1 (fun b => xpinW N b t)⟩
      (fun j => (Ret.shift 2).fst ((Pw N).τ ((Pw N).N - 1) j)) (Pw N).γ
      (fun k => busVal 1 (valW k)) ∧
    LinkEv (ρCW N) vCW false true ∧
    busVal 1 (valW 0) ≠ busVal 1 (valW 1) := by
  obtain ⟨p1, p2, _, p4⟩ := pipe_contract (gates_w N) (env_w N hN) (timing_w N hN) (data_w N)
    (fun _ _ => by show 1 ≤ 1; exact Nat.le_refl 1)
    (ain := ainW) (rout := routW N) (Ret.shift 1) (Ret.shift 2)
    (fun t ht => by show sq (5 + 1) t = sq 5 (t - 1); exact sq1 5 t ht)
    (fun t ht => by
      show sq (5 + 2 * N) t = sq (5 + 2 * (N - 1)) (t - 2)
      have ht' : 2 ≤ t := ht
      have := sq_shift (5 + 2 * (N - 1)) 2 (t - 2)
      rw [show 5 + 2 * (N - 1) + 2 = 5 + 2 * N by omega, show t - 2 + 2 = t by omega] at this
      exact this)
    (by show 1 ≤ 4 ∧ 2 ≤ 4; decide)
    (Qa := 2) (Qr := 3)
    (by show 1 ≤ 2 ∧ (Ret.shift 1).fst 1 ≤ 2; rw [Ret.fst_shift 1 1 (by decide)]; decide)
    (by show 2 ≤ 3 ∧ (Ret.shift 2).fst 1 ≤ 3; rw [Ret.fst_shift 2 1 (by decide)]; decide)
    (fun t ht => sq_pre 6 t (by omega))
    (fun t ht => sq_pre _ t (by omega))
    (fun t ht => by show sq (4 + 2 * 0) t = false; have h4 : t < 4 := ht; exact sq_pre _ t (by omega))
    (fun t ht => by
      show sq (8 + 2 * (N - 1)) t = false
      have h4 : t < 4 := ht; exact sq_pre _ t (by omega))
    (fun j => by
      rw [τ_w, Ret.fst_shift 1 _ (by omega)]; show 5 + 2 * 0 + 4 * j + 1 < 4 + 4 * (j + 1); omega)
    (fun j => by
      rw [τ_w, Ret.fst_shift 2 _ (by omega)]
      show 5 + 2 * (N - 1) + 4 * j + 2 < 6 + 2 * N + 4 * j; omega)
    (fun k => by show 2 + 8 * k ≤ 4 + 4 * (2 * k); omega)
    (fun k => by
      rw [τ_w, Ret.fst_shift 1 _ (by omega)]; show 5 + 2 * 0 + 4 * (2 * k + 1) + 1 ≤ 10 + 8 * k
      omega)
    (xpin := xpinW N) (xlo := fun _ => 1) (xhi := fun _ => 2)
    (fun _ _ => CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
      (fun t => by show xW (N - 1) (t + 1 - 1) = xW ((Pw N).N - 1) t; rfl))
    (fun b _ => by rw [Dl_w]; show (1 : Int) + ((1 : Nat) : Int) ≤ ((2 : Nat) : Int); decide)
    (Ch := Bool) (ρC := ρCW N) (vC := vCW) (ci := false) (co := true) rfl rfl
    (fun _ => rfl) (fun _ => rfl)
  exact ⟨p1, p2, p4, by decide⟩
end Formal.Cells.ContractsLink.Wit
#print axioms Formal.Cells.ContractsLink.Wit.pipe_witness
#print axioms Formal.Cells.ContractsLink.link_contract
#print axioms Formal.Cells.Contracts.net_refines_ports
#print axioms Formal.Cells.ContractsLink.Wit.no_lead_breaks
