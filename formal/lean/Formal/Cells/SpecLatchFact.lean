import Formal.Cells.SpecLatch
import Formal.Cells.SpecCElemFact

/-!
# Formal.Cells.SpecLatchFact — the INIT facts of `SpecLatch.latch_close` as a decidable check

Shard B, THE goal, S3. `lfact k init e d j pe pd held ov` checks all `2^k` addresses; `hopen_of_lfact` /
`hclosed_of_lfact` give exactly `latch_close`'s `hopen` / `hclosed`. `lat2271_fact`: a latch of THE target
(SLICE_X0Y47.ALUT.O5 class "HH01", the most common latch INIT shape: enable pin 2, data pin 3, feedback pin 4) passes;
`lat2271_swapped` (enable and data exchanged) fails, a negative control.
-/

namespace Formal.Cells.SpecLatchFact

open Formal.Target Formal.Timing.SpecLoop Formal.Cells.SpecCElemFact

def heldAt (k : Nat) (held ov : Nat → Bool) (a : Nat) : Bool :=
  (List.range k).all fun i => !held i || (a.testBit i == ov i)

def lfactAt (k init e d j : Nat) (pe pd : Bool) (held ov : Nat → Bool) (a : Nat) : Bool :=
  (!((a.testBit e ^^ pe) && heldAt k held ov a) || (init.testBit a == (a.testBit d ^^ pd))) &&
  (!(!(a.testBit e ^^ pe) && heldAt k held ov a) || (init.testBit a == a.testBit j))

def lfact (k init e d j : Nat) (pe pd : Bool) (held ov : Nat → Bool) : Bool :=
  (List.range (2 ^ k)).all (lfactAt k init e d j pe pd held ov)

theorem heldAt_of {k : Nat} {held ov : Nat → Bool} {v : Nat → Bool}
    (h : ∀ i, i < k → held i = true → v i = ov i) : heldAt k held ov (addr k v) = true := by
  simp only [heldAt, List.all_eq_true, List.mem_range]
  intro i hi
  rw [addr_testBit k v i hi]
  cases hh : held i
  · simp
  · simp [h i hi hh]

theorem hopen_of_lfact {k init e d j : Nat} {pe pd : Bool} {held ov : Nat → Bool}
    (h : lfact k init e d j pe pd held ov = true) (he : e < k) (hd : d < k) :
    ∀ v : Nat → Bool, (v e ^^ pe) = true → (∀ i, i < k → held i = true → v i = ov i) →
      init.testBit (addr k v) = (v d ^^ pd) := by
  intro v hve hh
  simp only [lfact, List.all_eq_true, List.mem_range] at h
  have ha := h _ (addr_lt k v)
  simp only [lfactAt, Bool.and_eq_true] at ha
  have h1 := ha.1
  rw [addr_testBit k v e he, addr_testBit k v d hd, hve, heldAt_of hh] at h1
  simpa using h1

theorem hclosed_of_lfact {k init e d j : Nat} {pe pd : Bool} {held ov : Nat → Bool}
    (h : lfact k init e d j pe pd held ov = true) (he : e < k) (hj : j < k) :
    ∀ v : Nat → Bool, (v e ^^ pe) = false → (∀ i, i < k → held i = true → v i = ov i) →
      init.testBit (addr k v) = v j := by
  intro v hve hh
  simp only [lfact, List.all_eq_true, List.mem_range] at h
  have ha := h _ (addr_lt k v)
  simp only [lfactAt, Bool.and_eq_true] at ha
  have h2 := ha.2
  rw [addr_testBit k v e he, addr_testBit k v j hj, hve, heldAt_of hh] at h2
  simpa using h2

theorem lat2271_fact : lfact 5 0xff0ff000 2 3 4 false false (fun _ => false) (fun _ => false) = true := by decide

theorem lat2271_swapped : lfact 5 0xff0ff000 3 2 4 false false (fun _ => false) (fun _ => false) = false := by decide

end Formal.Cells.SpecLatchFact
