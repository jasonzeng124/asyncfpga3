import Formal.Net.GenWitCells1

/-!
# Probe C-witgen (3/4): operators 184..366, H_BUNDLE, H_START_ONCE, out0's close

Kernel checks on the run of `GenWitData`/`GenWitOx`: `GenCell` on the remaining operators
(chunks of 92 and 91), `Held` on all 465 channels, start's request toggles exactly twice
(rises once), and out0's first token closes at `gOut0Close` carrying 6.
-/

namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit Formal.Net.CapNet.Gcd
open Formal.Net.CellBind.Ops

set_option maxRecDepth 100000

theorem gcells3 : (List.range' 184 92).all gP = true := by decide +kernel
theorem gcells4 : (List.range' 276 91).all gP = true := by decide +kernel

/-- The run, as channel traces. -/
def gch (c : Fin NC) : Chan := wch gcdA c

/-- Internal nodes: operator `o`'s record. -/
def gox (o : Fin NO) : OX := goxA o.val

/-- **H_GEN for the run**: every one of the 367 operators obeys its generated netlist. -/
theorem g_gen : ∀ o : Fin NO, GenCell gch (srcV 12 18) (opAt o) := by
  intro o
  have hP : gP o.val = true := by
    have h := o.isLt
    change o.val < 367 at h
    by_cases h1 : o.val < 92
    · exact chunk_of gcells1 _ (Nat.zero_le _) h1
    by_cases h2 : o.val < 184
    · exact chunk_of gcells2 _ (by omega) h2
    by_cases h3 : o.val < 276
    · exact chunk_of gcells3 _ (by omega) h3
    · exact chunk_of gcells4 _ (by omega) (by omega)
  exact kChkG_sound (goxA o.val) (srcV 12 18) (opAt o) hP

theorem gcds_len : gcds.length = NC := by decide +kernel

theorem gheld_all : gcds.all heldChk = true := by decide +kernel

/-- **H_BUNDLE for the run.** -/
theorem g_held : ∀ c : Fin NC, Held (gch c) := by
  intro c
  apply held_of
  apply List.all_eq_true.mp gheld_all
  unfold gcdA
  have h : c.val < gcds.length := by rw [gcds_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem gstart_rq : (gcdA start).rq = [gStartRise, gStartFall] := by decide +kernel

/-- **H_START_ONCE for the run.** -/
theorem g_start_once : ∀ t, cnt (riseB (gch start).req) t ≤ 1 :=
  once_of gstart_rq (by decide)

/-- out0's first token closes at `gOut0Close`, carrying 6. -/
theorem g_out0 : TokAt (gch out0) 0 gOut0Close ∧ (gch out0).dat gOut0Close = 6 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

end Formal.Net.CellBind.GenWit
