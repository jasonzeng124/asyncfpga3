import Formal.Cells.ContractsTrunc
/-!
# Self-audit of shard B (probe Bsa), part 1: joint witness for the causal composition

`ContractsTrunc.net_refines_causal` / `ports_of_causal` had no witness in which
ALL their hypotheses hold at once (the file's notes say no closed graph is
instantiated). Here: a one-channel net (a counting source feeding a sink) on
`Contracts.Witness.wch`. The base and every causal step are discharged from
the whole-run port (`port_iff`), so this is a CONSISTENCY witness only: it
shows the hypotheses are jointly satisfiable (the closure is not vacuous); it
does not show that any B cell supplies the step (that is the steer's
`steer_step_ports`, witnessed in `ContractsTruncWit`).
-/
namespace Formal.Cells.SelfAuditB
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.Contracts

/-- One channel `()`, produced by operator `true` (a source of the values
`0, 1, 2, …`), consumed by operator `false` (a sink). -/
def net1 : Net Unit Bool where
  ins o := if o then [] else [()]
  outs o := if o then [()] else []
  prod _ := true
  cons _ := false
  prod_iff c o := by cases c; cases o <;> simp
  cons_iff c o := by cases c; cases o <;> simp

/-- Token equations: the source's k-th token is `k`; the sink is unconstrained. -/
def E1 (o : Bool) (σ : Unit → Nat → Nat) : Prop := if o then ∀ k, σ () k = k else True

def ch1 (_ : Unit) : Chan := Witness.wch
def ρ1 (_ : Unit) : Nat → Nat := fun j => 4 * j + 1
def α1 (_ : Unit) : Nat → Nat := fun j => 4 * j + 3
def v1 (_ : Unit) : Nat → Nat := fun k => k

theorem port1 (c : Unit) : Port (ch1 c) (ρ1 c) (α1 c) (v1 c) := Witness.port

/-- **Every hypothesis of `net_refines_causal` holds at once** (driver type
`Unit`, delay 1, base at `N0 = 0`), and its conclusion follows. -/
theorem net_refines_causal_witness :
    ∀ c k, (fun (_ : Unit) (k : Nat) => k) c k = v1 c k :=
  net_refines_causal (D := Unit) net1 ch1 E1 ρ1 α1 v1 0
    (fun c => port_iff.1 (port1 c) 0)
    (fun _ => ()) (fun _ => 1) (fun _ => Nat.le_refl 1)
    (fun N _ _ w => by
      have h := fun c => port_iff.1 (port1 c) (N + 1)
      cases w with
      | rq c => exact (h c).rq
      | dt c => exact (h c).dt
      | ak c => exact (h c).ak)
    (fun o => by
      cases o
      · intro c hc; simp [net1] at hc
      · intro c _ k σ _ hE
        cases c
        exact hE k)
    (fun _ k => k)
    (fun o => by cases o <;> simp [E1])

end Formal.Cells.SelfAuditB
