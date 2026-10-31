import Formal.Cells.FiniteNetMixed

/-!
# Probe Bcomb (shard B): a truncated spec for a LUT whose excitation is clean

A building block for gate-modelling the cells whose correctness is a RACE, not a handshake
law (the arbiter's `ustate`/`ugrant`, see `notes/B-arb-bind-plan.md`): the cell is its real LUT
`F` of its pins through a `Win` channel with H_NO_REVERT, and the race content is ONE named
hypothesis, `H_EXC_CLEAN`: whenever the pins are clean step signals on `[0, T)`, the excitation
`t ↦ F (pins t)` is a clean step signal on `[0, T)` with the stated edge times `e` and edge set
`Le` (no runt, no hazard). Everything else is the network rule.

**Proved:** `fcomb_spec_cell`: such a cell meets its truncated contract (`FCellOK`), so it can
sit in `FiniteNetMixed`'s networks next to the handshake cells. `fcomb_of_buf`: a 1-pin buffer
(`F = id`) is an `FCombSpec` whose `H_EXC_CLEAN` is the pin's own cleanliness, so the hypothesis
is not vacuous. **Assumed:** the fields. **NOT covered:** no arbiter cell instantiated yet;
`H_EXC_CLEAN` is where the arbitration windows (`ArbAMergeRun`'s H_SEP, RA1, the Rows) must be
proved or assumed. Core Lean only.
-/

namespace Formal.Cells.FiniteNetComb
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.WinFifo (Win)
open Formal.Cells.WinFifoCausal (NoRevertI nt)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.FiniteRuns (fe)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)

variable {ι : Type}

/-- The excitation of a LUT `F` over its pin list. -/
def exc (F : List Bool → Bool) (ps : List (GPin ι)) (t : Nat) : Bool := F (ps.map fun p => p.P t)

/-- **A LUT cell with a clean excitation** (truncated form). -/
structure FCombSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (F : List Bool → Bool)
    (ps : List (GPin ι)) (e : Nat → Nat) (Le : Nat → Prop) : Prop where
  H_PINS : D.pins c = ps
  H_LUT_WIN : Win (D.lo c) (D.hi c) (exc F ps) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (exc F ps) (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  /-- **H_EXC_CLEAN**: clean pins on `[0, T)` give a clean excitation on `[0, T)`. -/
  H_EXC_CLEAN : ∀ T, (∀ p ∈ ps, GPhT p.P (gE D.τ p) (L p.drv) T) → GPhT (exc F ps) e Le T
  H_TIMES : ∀ j, L c j → D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (e j) (Vph j)
  H_CNT : ∀ j, L c j ↔ Le j
  H_FLOOR : ∀ j, Le j → D.hi c ≤ e j + D.lo c

/-- **The cell meets its truncated contract.** -/
theorem fcomb_spec_cell {D : GD ι} {L : ι → Nat → Prop} {c : ι} {F : List Bool → Bool}
    {ps : List (GPin ι)} {e : Nat → Nat} {Le : Nat → Prop} (S : FCombSpec D L c F ps e Le) :
    FCellOK D L c := by
  intro T hA
  have hx := S.H_EXC_CLEAN T (fun p hp => hA p (by rw [S.H_PINS]; exact hp))
  have hL : L c = Le := funext fun j => propext (S.H_CNT j)
  refine gphT_congr (c' := fe (D.O c) (D.lo c) (D.hi c) e) (fun j hj => S.H_TIMES j hj) ?_
  rw [hL]
  exact tnode S.H_LUT_WIN S.H_NO_REVERT hx S.H_FLOOR S.H_PWR

/-- The identity LUT on one pin. -/
def idF : List Bool → Bool
  | [b] => b
  | _ => false

/-- **Non-vacuity of the form**: a 1-pin buffer (`F = id`) is an `FCombSpec` whose
`H_EXC_CLEAN` is just the pin's cleanliness. -/
theorem fcomb_of_buf {D : GD ι} {L : ι → Nat → Prop} {c : ι} {p : GPin ι}
    (hP : D.pins c = [p]) (hW : Win (D.lo c) (D.hi c) p.P (D.O c))
    (hN : NoRevertI (D.lo c) (D.hi c) p.P (D.O c)) (hPw : ∀ t, t < D.hi c → D.O c t = false)
    (hT : ∀ j, L c j → D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gE D.τ p j) (Vph j))
    (hC : ∀ j, L c j ↔ L p.drv j) (hF : ∀ j, L p.drv j → D.hi c ≤ gE D.τ p j + D.lo c) :
    FCombSpec D L c idF [p] (gE D.τ p) (L p.drv) where
  H_PINS := hP
  H_LUT_WIN := hW
  H_NO_REVERT := hN
  H_PWR := hPw
  H_EXC_CLEAN := fun T h => h p (List.mem_singleton.2 rfl)
  H_TIMES := hT
  H_CNT := hC
  H_FLOOR := hF

end Formal.Cells.FiniteNetComb
