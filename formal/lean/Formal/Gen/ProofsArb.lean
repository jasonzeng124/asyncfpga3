import Formal.Gen.Cells
import Formal.Gen.PrelimSem
import Formal.Cells.CElemFn
import Formal.Cells.ArbKleene
import Formal.Cells.ArbBinary
import Formal.Cells.ArbHandover
import Formal.Cells.ArbHeldTimed
import Formal.Cells.ArbA0Fork
import Formal.Core.Lut
import Formal.Core.LutCells

/-!
# 11d: the generated arbiter (`bd_arb.v`)

Every arbiter transcription in shard B's tree is matched gate by gate against
the synthesized netlist:
* `ArbKleene`: `ST_INIT GR_INIT CS_INIT C2_INIT`, `g1K g2K qArbK r0K qCellK cK`
  (Kleene, all inputs);
* `ArbBinary`: `C2N_SET GRANT ARB_ST C2`, `stF gr1 gr2 stA r0A c2`;
* `ArbHandover`: `INIT_C2N_SET INIT_GRANTS INIT_HELD INIT_C2_RST`, `stateF g1F g2F`;
* `ArbHeldTimed`: `INIT_HELD INIT_GRANTS INIT_C2`, `FS FR FG1 FG2 CE`;
* `ArbA0Fork`: `ST_INIT GR_INIT C2_INIT`, `cel F1 F2 G1 G2`;
* shard A: `Formal.Core.Init.arb_grant`, `arb_state`, `Formal.Core.LutCells`.
`arbiter_kleene_exclusion` transfers B's `kleene_exclusion` to the generated
netlist (as 11a did for its own import).
-/

namespace Formal.Gen.ProofsArb
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.CElemFn (cSpec clr)
open Formal.Cells.ArbKleene (g1K g2K qArbK r0K qCellK cK kleene_exclusion ST_INIT GR_INIT CS_INIT C2_INIT)

/-! ## Structure -/

theorem bd_arbcell_lut :
    bd_arbcell.cellNames = ["ugrant", "ustate.u"] ∧
    bd_arbcell.lutIs "ugrant" .lut6_2 GR_INIT ["r1", "r2", "q", "0", "0", "1"] ["g1", "g2"] ∧
    bd_arbcell.lutIs "ustate.u" (.lut 6) CS_INIT ["r1", "r2", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel

theorem bd_arbiter_lut :
    bd_arbiter.cellNames = ["ua1.u", "ua2.u", "ugrant", "ustate"] ∧
    bd_arbiter.lutIs "ustate" .lut6_2 ST_INIT ["r1", "r2", "q", "rst", "A0", "1"] ["R0", "q"] ∧
    bd_arbiter.lutIs "ugrant" .lut6_2 GR_INIT ["r1", "r2", "q", "0", "0", "1"] ["g1", "g2"] ∧
    bd_arbiter.lutIs "ua1.u" (.lut 6) C2_INIT ["g1", "A0", "A1", "rst", "0", "0"] ["A1"] ∧
    bd_arbiter.lutIs "ua2.u" (.lut 6) C2_INIT ["g2", "A0", "A2", "rst", "0", "0"] ["A2"] := by
  decide +kernel

theorem arb_inits_other :
    bd_arbiter.initOf "ustate" = some Formal.Cells.ArbBinary.ARB_ST ∧
    bd_arbiter.initOf "ugrant" = some Formal.Cells.ArbBinary.GRANT ∧
    bd_arbcell.initOf "ustate.u" = some Formal.Cells.ArbBinary.C2N_SET ∧
    bd_arbiter.initOf "ua1.u" = some Formal.Cells.ArbBinary.C2 ∧
    bd_arbcell.initOf "ustate.u" = some Formal.Cells.ArbHandover.INIT_C2N_SET ∧
    bd_arbiter.initOf "ugrant" = some Formal.Cells.ArbHandover.INIT_GRANTS ∧
    bd_arbiter.initOf "ustate" = some Formal.Cells.ArbHandover.INIT_HELD ∧
    bd_arbiter.initOf "ua2.u" = some Formal.Cells.ArbHandover.INIT_C2_RST ∧
    bd_arbiter.initOf "ustate" = some Formal.Cells.ArbHeldTimed.INIT_HELD ∧
    bd_arbiter.initOf "ugrant" = some Formal.Cells.ArbHeldTimed.INIT_GRANTS ∧
    bd_arbiter.initOf "ua1.u" = some Formal.Cells.ArbHeldTimed.INIT_C2 ∧
    bd_arbiter.initOf "ustate" = some Formal.Cells.ArbA0Fork.ST_INIT ∧
    bd_arbiter.initOf "ugrant" = some Formal.Cells.ArbA0Fork.GR_INIT ∧
    bd_arbiter.initOf "ua1.u" = some Formal.Cells.ArbA0Fork.C2_INIT ∧
    bd_arbiter.initOf "ugrant" = some Formal.Core.Init.arb_grant.init.toNat ∧
    bd_arbiter.initOf "ustate" = some Formal.Core.Init.arb_state.init.toNat ∧
    bd_arbiter.initOf "ustate" = some Formal.Core.LutCells.bd_arbiter_ustate.init ∧
    bd_arbiter.initOf "ugrant" = some Formal.Core.LutCells.bd_arbiter_ugrant.init ∧
    bd_arbcell.initOf "ugrant" = some Formal.Core.LutCells.bd_arbcell_ugrant.init := by
  decide +kernel

/-- `ArbHandover.INIT_UNHELD` (B's counterfactual "unheld" state LUT) is NOT
what was synthesized: a negative control that the `initOf` checks can fail. -/
theorem arb_unheld_not_synthesized :
    bd_arbiter.initOf "ustate" ≠ some Formal.Cells.ArbHandover.INIT_UNHELD := by decide +kernel

/-! ## Gates = B's functions -/

def aEnv {V : Type} (r1 r2 q rst a0 a1 a2 g1 g2 : V) : List (String × V) :=
  [("r1", r1), ("r2", r2), ("q", q), ("rst", rst), ("A0", a0), ("A1", a1), ("A2", a2),
   ("g1", g1), ("g2", g2)]

theorem bd_arbiter_gates_K : ∀ r1 r2 q rst a0 : K3,
    let e := aEnv r1 r2 q rst a0 .f .f .f .f
    bd_arbiter.gateN kleeneSemP "ustate" .O6 e = some (qArbK r1 r2 q rst a0) ∧
    bd_arbiter.gateN kleeneSemP "ustate" .O5 e = some (r0K r1 r2 q rst a0) ∧
    bd_arbiter.gateN kleeneSemP "ugrant" .O5 e = some (g1K r1 r2 q) ∧
    bd_arbiter.gateN kleeneSemP "ugrant" .O6 e = some (g2K r1 r2 q) := by decide +kernel

theorem bd_arbiter_ack_gates_K : ∀ g a0 a rst : K3,
    bd_arbiter.gateN kleeneSemP "ua1.u" .O (aEnv .f .f .f rst a0 a .f g .f) = some (cK g a0 a rst) ∧
    bd_arbiter.gateN kleeneSemP "ua2.u" .O (aEnv .f .f .f rst a0 .f a .f g) = some (cK g a0 a rst) := by
  decide +kernel

theorem bd_arbcell_gates_K : ∀ r1 r2 q rst : K3,
    let e := aEnv r1 r2 q rst .f .f .f .f .f
    bd_arbcell.gateN kleeneSemP "ustate.u" .O e = some (qCellK r1 r2 q rst) ∧
    bd_arbcell.gateN kleeneSemP "ugrant" .O5 e = some (g1K r1 r2 q) ∧
    bd_arbcell.gateN kleeneSemP "ugrant" .O6 e = some (g2K r1 r2 q) := by decide +kernel

/-- Binary, with `rst = 0`: `ArbBinary`, `ArbHandover`, `ArbHeldTimed`. -/
theorem bd_arb_gates_B : ∀ r1 r2 q a0 : Bool,
    let e := aEnv r1 r2 q false a0 false false false false
    bd_arbcell.gateN boolSem "ustate.u" .O e = some (Formal.Cells.ArbBinary.stF r1 r2 q) ∧
    bd_arbcell.gateN boolSem "ustate.u" .O e = some (Formal.Cells.ArbHandover.stateF r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O5 e = some (Formal.Cells.ArbBinary.gr1 r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O6 e = some (Formal.Cells.ArbBinary.gr2 r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O5 e = some (Formal.Cells.ArbHandover.g1F r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O6 e = some (Formal.Cells.ArbHandover.g2F r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O5 e = some (Formal.Cells.ArbHeldTimed.FG1 r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O6 e = some (Formal.Cells.ArbHeldTimed.FG2 r1 r2 q) ∧
    bd_arbiter.gateN boolSem "ustate" .O6 e = some (Formal.Cells.ArbBinary.stA r1 r2 q a0) ∧
    bd_arbiter.gateN boolSem "ustate" .O5 e = some (Formal.Cells.ArbBinary.r0A r1 r2 q a0) ∧
    bd_arbiter.gateN boolSem "ustate" .O6 e = some (Formal.Cells.ArbHeldTimed.FS r1 r2 q a0) ∧
    bd_arbiter.gateN boolSem "ustate" .O5 e = some (Formal.Cells.ArbHeldTimed.FR r1 r2 q) := by
  decide +kernel

theorem bd_arb_ack_gates_B : ∀ g a0 a : Bool,
    bd_arbiter.gateN boolSem "ua1.u" .O (aEnv false false false false a0 a false g false) =
      some (Formal.Cells.ArbBinary.c2 g a0 a) ∧
    bd_arbiter.gateN boolSem "ua1.u" .O (aEnv false false false false a0 a false g false) =
      some (Formal.Cells.ArbHeldTimed.CE g a0 a) ∧
    bd_arbiter.gateN boolSem "ua2.u" .O (aEnv false false false false a0 false a false g) =
      some (Formal.Cells.ArbA0Fork.cel g a0 a) := by decide +kernel

/-- `ArbA0Fork`'s one-client restrictions `F1 F2 G1 G2` are the generated gates
with the other request held at its idle value. -/
theorem bd_arb_a0fork : ∀ q a0 : Bool,
    bd_arbiter.gateN boolSem "ustate" .O6 (aEnv true false q false a0 false false false false) =
      some (Formal.Cells.ArbA0Fork.F1 q a0) ∧
    bd_arbiter.gateN boolSem "ustate" .O6 (aEnv false true q false a0 false false false false) =
      some (Formal.Cells.ArbA0Fork.F2 q a0) ∧
    bd_arbiter.gateN boolSem "ugrant" .O5 (aEnv true false q false a0 false false false false) =
      some (Formal.Cells.ArbA0Fork.G1 q) ∧
    bd_arbiter.gateN boolSem "ugrant" .O6 (aEnv false true q false a0 false false false false) =
      some (Formal.Cells.ArbA0Fork.G2 q) := by decide +kernel

/-! ## Whole netlist, unit step (11a's statements on the new import) -/

theorem arb_iface :
    bd_arbiter.inputNames = ["rst", "r1", "r2", "A0"] ∧
    bd_arbiter.outputNames = ["A1", "A2", "R0", "g1", "g2"] ∧
    bd_arbiter.stateNames = ["A1", "A2", "q"] ∧
    bd_arbcell.inputNames = ["r1", "r2", "rst"] ∧ bd_arbcell.stateNames = ["q"] := by decide +kernel

theorem bd_arbiter_next_spec : ∀ rst r1 r2 a0 a1 a2 q : Bool,
    bd_arbiter.next boolSem [rst, r1, r2, a0] [a1, a2, q] =
      some [clr rst (cSpec [r1 && q, a0] a1),
            clr rst (cSpec [r2 && !q, a0] a2),
            rst || (if a0 then q else ((r1 && !r2) || (q && (r1 || !r2))))] := by decide +kernel

theorem bd_arbiter_outs_spec : ∀ rst r1 r2 a0 a1 a2 q : Bool,
    bd_arbiter.outs boolSem [rst, r1, r2, a0] [a1, a2, q] =
      some [a1, a2, (r1 && q) || (r2 && !q), r1 && q, r2 && !q] := by decide +kernel

/-- Kleene, all 3^7 inputs. -/
theorem bd_arbiter_next_K : ∀ rst r1 r2 a0 a1 a2 q : K3,
    bd_arbiter.next kleeneSemP [rst, r1, r2, a0] [a1, a2, q] =
      some [cK (g1K r1 r2 q) a0 a1 rst, cK (g2K r1 r2 q) a0 a2 rst, qArbK r1 r2 q rst a0] := by
  decide +kernel

theorem bd_arbiter_outs_K : ∀ rst r1 r2 a0 a1 a2 q : K3,
    bd_arbiter.outs kleeneSemP [rst, r1, r2, a0] [a1, a2, q] =
      some [a1, a2, r0K r1 r2 q rst a0, g1K r1 r2 q, g2K r1 r2 q] := by decide +kernel

theorem bd_arbcell_step_K : ∀ r1 r2 rst q : K3,
    bd_arbcell.next kleeneSemP [r1, r2, rst] [q] = some [qCellK r1 r2 q rst] ∧
    bd_arbcell.outs kleeneSemP [r1, r2, rst] [q] = some [g1K r1 r2 q, g2K r1 r2 q] := by
  decide +kernel

/-- B's `kleene_exclusion`, transferred: the generated arbiter's grant ports
are never both a definite 1, whatever the ternary inputs and state. -/
theorem arbiter_kleene_exclusion (rst r1 r2 a0 a1 a2 q : K3) (vs : List K3)
    (h : bd_arbiter.outs kleeneSemP [rst, r1, r2, a0] [a1, a2, q] = some vs) :
    ¬ (vs[3]? = some .t ∧ vs[4]? = some .t) := by
  rw [bd_arbiter_outs_K] at h
  cases h
  simpa using kleene_exclusion r1 r2 q

end Formal.Gen.ProofsArb
