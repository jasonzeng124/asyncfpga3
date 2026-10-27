import Formal.Cells.ContractsTruncWit
/-!
# Self-audit of shard B (probe Bsa), part 4: a witness for `ContractsB.steer_contract`

`steer_contract` (B-contracts.md) had no run meeting all of its hypotheses.
`OpsTimed.SteerWit` (the witness of `steer_ok_static`) does NOT meet it: its
first branch request is at `R0 0 = 4` while `H_T1` needs `T1 0 = 5 ≤ R0 0`
(the clean window of the FIFO model starts too late). Here the run of
`ContractsTruncWit` (first request at 9) is used: every hypothesis of
`steer_contract`, including `SteerCausal`, `SteerStatic` (by `decide`), the
reset-quiet and first-edge facts and C's channel identifications (C = `Option
Bool`: `none` the input, `some b` branch `b`; values: token `i` carries `i`),
holds, and the conclusion follows.
-/
namespace Formal.Cells.SelfAuditB4
open Formal.Net Formal.Net.Handshake
open Formal.Cells.Contracts
open Formal.Cells.Contracts.TruncWit
open Formal.Cells.OpsTimed (Tok Enum rx SteerRun SteerCausal SteerStatic)
open Formal.Cells.OpsTimed.SteerWit (u sv)

theorem causalW : SteerCausal run (fun k => 16 * k + 9) (fun k => 16 * k + 25) 1 1 0 8 where
  H_RCV j := by
    unfold SteerRun.Rsel; rw [R0_eq, R1_eq]; show _ ≤ 8 * j + 13; split <;> omega
  H_SND j := by rw [K_eq]; show _ ≤ 8 * (j + 1) + 9; omega
  H_S_LEAD k := by show _ ≤ 8 * (2 * k) + 9; omega
  H_S_HOLD k := by show 8 * (2 * k + 1) + 9 + 8 ≤ _; omega
  H_POS j := ⟨by show 1 ≤ 8 * j + 9; omega, by show 1 ≤ 8 * j + 13; omega⟩

theorem staticW : SteerStatic run u 1 1 2 1 0 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem quiet_ack10 : ∀ t, t < run.T2 6 → ack t = false := by
  show ∀ t, t < 10 → ack t = false
  decide

def ρC : Option Bool → Nat → Nat
  | none => run.ρ
  | some b => rx (Rb run b) (κ b)
def vC : Option Bool → Nat → Nat
  | none => fun i => i
  | some b => fun m => κ b m

/-- **Every hypothesis of `steer_contract` holds** on the ContractsTruncWit run. -/
theorem steer_contract_witness :
    Tok 0 ack run.K (fun _ => true) ∧
    Tok 0 r0 (rx run.R0 (κ false)) (fun _ => true) ∧ Tok 0 r1 (rx run.R1 (κ true)) (fun _ => true) ∧
    (∀ j, run.ρ j < run.K j ∧ run.K j < run.ρ (j + 1)) ∧
    (∀ b j, rx (Rb run b) (κ b) j < rx run.A (κ b) j ∧ rx run.A (κ b) j < rx (Rb run b) (κ b) (j + 1)) ∧
    SteerEv ρC vC (fun i => decide (i % 2 = 1)) id none some :=
  steer_contract (P := run) (s := s) (Lm := 2) (Wm := 1) u (fun k => 16 * k + 9)
    (fun k => 16 * k + 25) gates (fun _ _ => rfl)
    (fun k t h1 h2 => by show sv ((t - 9) / 16) = sv k; rw [show (t - 9) / 16 = k by omega])
    req_tok a0_tok a1_tok causalW staticW (by decide) (by decide) (by decide)
    κ enum0 enum1 quiet_ack10
    (by rw [K_eq]; decide)
    quiet_fwd
    (by rw [R0_eq, R1_eq]; decide)
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

end Formal.Cells.SelfAuditB4
