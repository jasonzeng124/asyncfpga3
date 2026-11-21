import Formal.Cells.BWit3Data
import Formal.Net.CapstoneWitness

/-!
# Probe Bwit3 (shard B): the gate-timed gcd_hw run (muxes and arbiters gate-modelled) meets C's hypotheses

Kernel checks, with C's own event-list checkers (`CapstoneWitnessLib.kChk`, `heldChk`,
`once_of`), of the gate-timed run `chB` (`BWit3Data`, a = 12, b = 18; B-tied operators, every bd_mux cell and every bd_arbiter cell take
two ticks channel to channel):
* `b_cells`: every one of the 367 operators meets C's gate model (`Cell chB (srcV 12 18)`);
* `b_held`: every channel is bundled (`Held`); `b_start_once`;
* `b_forced`: H_CM_FORCED, from C's `gcd_hw_forced` with C's token-level walk `yW`;
* `b_out0`: out0's first token closes at `out0CloseB` and carries 6.
So C's operator models (speed-independent) accept a run whose tied gates have B's
LUT + wire delay; C's own run chW is not the only witness. Core Lean only.
-/

namespace Formal.Cells.BWit3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit Formal.Net.CapSafe

set_option maxRecDepth 100000

theorem bcells1 : (ops.take 90).all (fun k => kChk cdB (srcV A0 B0) k) = true := by decide +kernel
theorem bcells2 : ((ops.drop 90).take 90).all (fun k => kChk cdB (srcV A0 B0) k) = true := by
  decide +kernel
theorem bcells3 : (((ops.drop 90).drop 90).take 90).all (fun k => kChk cdB (srcV A0 B0) k) = true := by
  decide +kernel
theorem bcells4 : (((ops.drop 90).drop 90).drop 90).all (fun k => kChk cdB (srcV A0 B0) k) = true := by
  decide +kernel

theorem bcells_all : ops.all (fun k => kChk cdB (srcV A0 B0) k) = true := by
  rw [← List.take_append_drop 90 ops, List.all_append, bcells1, ← List.take_append_drop 90 (ops.drop 90),
    List.all_append, bcells2, ← List.take_append_drop 90 ((ops.drop 90).drop 90), List.all_append,
    bcells3, bcells4]; rfl

/-- C's H_CELLS on the gate-timed run. -/
theorem b_cells : ∀ o : Fin NO, Cell chB (srcV A0 B0) (opAt o) := fun o =>
  kChk_sound (srcV A0 B0) (opAt o) (List.all_eq_true.mp bcells_all _ getD_mem)

theorem cdsB_len : cdsB.length = NC := by decide +kernel

theorem bheld_all : cdsB.all heldChk = true := by decide +kernel

/-- C's H_BUNDLE on the gate-timed run. -/
theorem b_held : ∀ c : Fin NC, Held (chB c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp bheld_all
  unfold cdB
  have h : c.val < cdsB.length := by rw [cdsB_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem bstart_rq : (cdB start).rq = [startRiseB, startFallB] := by decide +kernel

theorem b_start_once : ∀ t, cnt (riseB (chB start).req) t ≤ 1 :=
  once_of bstart_rq (by decide)

/-- H_CM_FORCED on the gate-timed run (C's lemma, C's token walk). -/
theorem b_forced : ∀ o : Fin NO, Forced chB (omOf A0 B0 yW) (opAt o) :=
  gcd_hw_forced A0 B0 chB yW yW_good b_cells b_held b_start_once yW_walk

/-- out0's first token closes at `out0CloseB`, and carries 6. -/
theorem b_out0 : TokAt (chB out0) 0 out0CloseB ∧ (chB out0).dat out0CloseB = 6 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

/-- **C's capstone hypotheses hold jointly on the gate-timed run**, and out0 carries 6. -/
theorem b_joint :
    (∀ o : Fin NO, Cell chB (srcV 12 18) (opAt o)) ∧ (∀ c, Held (chB c)) ∧
    (∀ t, cnt (riseB (chB start).req) t ≤ 1) ∧
    (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced chB (omOf 12 18 y) (opAt o)) ∧
    TokAt (chB out0) 0 out0CloseB ∧ (chB out0).dat out0CloseB = 6 :=
  ⟨b_cells, b_held, b_start_once, ⟨yW, yW_good, b_forced⟩, b_out0⟩

end Formal.Cells.BWit3
