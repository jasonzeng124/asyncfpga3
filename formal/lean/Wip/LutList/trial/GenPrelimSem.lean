import Formal.Gen.Cells
import Wip.LutList.trial.CoreLutPrelim

/-!
# Probe 11e: the Prelim-valued Kleene reading of the generated netlists

Porting aid, **to be deleted together with `Formal/Cells/Prelim.lean`**.

`Formal.Gen.Netlist` reads every netlist with shard A's Core semantics
(`boolSem` = `Lut.eval`, `kleeneSem` = `Lut.keval` on `Formal.Core.K3`). Shard
B's hand transcriptions (`CElemFn.c2K`, `ArbKleene.g1K`, `Latch`, ...) are
still valued in Prelim's `Formal.Cells.K3`, so the `Proofs*` theorems that say
"generated gate = B's Kleene function" are stated with `kleeneSemP` below,
which is the same interpreter with Prelim's `lutK`. They keep their exact
pre-port statements. When B ports to Core, replace `kleeneSemP` by
`kleeneSem` in those files and delete this one.

`kleeneSemP_lut` / `kleeneSemP_const`: the two semantics agree through the
constructor bijection `toP` (`Formal.Net.CoreLutPrelim.lutK_eq_kevalL`), so
nothing differs but the names of the three values. `prim_tables_prelim` and
`mux_kleene_prelim` are the pre-port forms of `prim_tables` / `mux_kleene`,
derived from the Core ones through the bridge.
-/

namespace Formal.Gen
open Formal.Net.CoreLut Formal.Net.CoreLutPrelim

/-- Decidability of `∀` over Prelim's `K3` (Prelim has none). -/
instance K3.decForall {P : Formal.Core.LutList.K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
  if h : P .f ∧ P .t ∧ P .x then
    isTrue (fun k => by cases k <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _⟩)

/-- Kleene reading with shard B's Prelim `lutK` (pre-port `kleeneSem`). -/
def kleeneSemP : Sem Formal.Core.LutList.K3 := ⟨Formal.Core.LutList.lutK, Formal.Core.LutList.K3.ofBool⟩

/-- Binary reading with Prelim's `lutB`. It IS `boolSem` (`boolSem_eq_boolSemP`,
`Bool` is shared), so a theorem about one is a theorem about the other; it is
only here so that proofs by `rfl` against B's `lutB`-valued lemmas keep working. -/
def boolSemP : Sem Bool := ⟨Formal.Core.LutList.lutB, id⟩

theorem boolSem_eq_boolSemP : boolSem = boolSemP := by
  unfold boolSem boolSemP
  congr 1
  funext init ins
  exact (lutB_eq_evalL init ins).symm

theorem kleeneSemP_lut (init : Nat) (ins : List Formal.Core.K3) :
    kleeneSemP.lut init (ins.map toP) = toP (kleeneSem.lut init ins) :=
  lutK_eq_kevalL init ins

theorem kleeneSemP_const (b : Bool) : kleeneSemP.const b = toP (kleeneSem.const b) :=
  (toP_ofBool b).symm

/-- `prim_tables` in Prelim's `lutB`, from the Core statement. -/
theorem prim_tables_prelim :
    (∀ a b s : Bool, Formal.Core.LutList.lutB MUX_INIT [a, b, s] = (if s then b else a)) ∧
    (∀ a b : Bool, Formal.Core.LutList.lutB OR2_INIT [a, b] = (a || b)) ∧
    (∀ a : Bool, Formal.Core.LutList.lutB NOT_INIT [a] = !a) ∧
    (∀ a b : Bool, Formal.Core.LutList.lutB XOR2_INIT [a, b] = (a ^^ b)) := by
  simp only [lutB_eq_evalL]
  exact ⟨prim_tables.1, prim_tables.2.1, prim_tables.2.2.1, prim_tables.2.2.2.1⟩

/-- `mux_kleene` in Prelim's terms (`lutK`, `K3.mux`), from the Core statement. -/
theorem mux_kleene_prelim : ∀ a b s : Formal.Core.LutList.K3,
    Formal.Core.LutList.lutK MUX_INIT [a, b, s] = Formal.Core.LutList.K3.mux s a b := by
  intro a b s
  have h := lutK_eq_kevalL MUX_INIT [ofP a, ofP b, ofP s]
  simp only [List.map, toP_ofP] at h
  rw [h, mux_kleene, toP_kmux]
  simp

/-- Pre-port form of `ProofsPrims.prims_muxf_kleene` (Prelim `K3`, `K3.mux`). -/
theorem prims_muxf_kleene_prelim : ∀ a b s : Formal.Core.LutList.K3,
    Cells.prims_muxf8.gateN kleeneSemP "u0" .O [("l[0]", a), ("l[1]", b), ("sel[0]", s)] =
        some (Formal.Core.LutList.K3.mux s a b) ∧
    Cells.prims_muxf8.gateN kleeneSemP "u2" .O [("m0", a), ("m1", b), ("sel[1]", s)] =
        some (Formal.Core.LutList.K3.mux s a b) := by
  decide +kernel

end Formal.Gen
