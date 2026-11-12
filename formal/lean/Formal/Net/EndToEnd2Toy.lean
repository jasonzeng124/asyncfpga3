import Formal.Net.EndToEnd2
import Formal.Net.EndToEndToy

/-!
# Probe C-8h: what the per-link, per-edge check buys, on toy routes

Units of 10 ps, ILLUSTRATIVE delays (not prjxray data), as in 8e's toy.

1. `split`: a 2-stage pipe with a FAST source request and a short data wire
   into stage 0, but a long data wire into stage 1 (covered by the SDELAY
   line). 8e's global-margin check rejects it for EVERY `(m, h)`
   (`split_global_rejects`: one `m` must exceed the stage-1 data wire and be
   below the source's request path); the per-link check accepts it
   (`split_check2`), so `end_to_end2` proves it a FIFO (`split_fifo`).
2. 8e's `bad` (no SDELAY) is still rejected (`bad_check2`), and 8e's
   counterexample run stays a counterexample; `good` is accepted
   (`good_check2`).
3. `dack`: stage 0 has a wide enable fan-out (2..14) and a short data wire
   (2..4), so the hold race needs the acknowledge FALL to be slow, which is
   what a `bd_delay #(.FASTRISE(1))` DACK line does (fall 11..13, rise one hop
   1..2). With per-edge intervals the route passes (`dack_check2`); with the
   single band an edge-blind checker must use (1..13) it fails
   (`dack_band_rejects`).
-/

namespace Formal.Net.PerLink.Toy
open Formal.Net Formal.Net.Handshake Formal.Timing Formal.Net.EndToEnd Formal.Net.EndToEnd.Toy
  Formal.Net.PerLink

def split : Route where
  req := fun k => match k with
    | 1 => [(2, 3), (1, 2)]
    | 2 => [(2, 3), (10, 12), (1, 3), (1, 2)]
    | 3 => [(10, 12), (1, 2)]
    | _ => []
  ack := fun _ => [(1, 2), (1, 2)]
  en := fun j _ => match j with | 0 => [(2, 5)] | _ => [(2, 14)]
  dat := fun j _ => match j with | 0 => [(2, 4)] | _ => [(12, 14)]

/-- Per-link check accepts `split` (kernel `decide`). -/
theorem split_check2 : checkPipe2 (symR split) 2 2 = true := by decide

/-- A delay assignment inside `split`'s intervals (traces irrelevant). -/
def splitP : Pipe where
  x := fun _ _ => false
  Q := fun _ _ _ => false
  dR := fun k => match k with | 1 => 3 | 2 => 14 | 3 => 11 | _ => 0
  dA := fun _ => 2
  dG := fun _ _ => 2
  dD := fun j _ => match j with | 0 => 2 | _ => 14

theorem splitP_realizes : Realizes split 2 2 splitP := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k k1 k2
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact ⟨[2, 1], by simp [split, inPath], rfl⟩
    · exact ⟨[2, 10, 1, 1], by simp [split, inPath], rfl⟩
    · exact ⟨[10, 1], by simp [split, inPath], rfl⟩
  · intro k _; exact ⟨[1, 1], by simp [split, inPath], rfl⟩
  · intro j hj b _
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact ⟨[2], by simp [split, inPath], rfl⟩
    · exact ⟨[2], by simp [split, inPath], rfl⟩
  · intro j hj b _
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact ⟨[2], by simp [split, inPath], rfl⟩
    · exact ⟨[14], by simp [split, inPath], rfl⟩

/-- **8e's global check rejects `split` for every margin choice**: the source
setup needs `m ≤ dR 1 + 2 = 5`, the stage-1 latch setup `m ≥ 15`. -/
theorem split_global_rejects : ∀ m h, checkPipe split 2 2 m h = false := by
  intro m h
  apply Classical.byContradiction; intro hc
  have hc' : checkPipe split 2 2 m h = true := by
    cases h' : checkPipe split 2 2 m h <;> simp_all
  have T := timing_of_check hc' splitP_realizes
  have h1 := T.src_setup
  have h2 := T.lat_setup 1 (by decide) 0 (by decide)
  simp [splitP] at h1 h2
  omega

/-- ...while the per-link theorem proves it a FIFO, for every run whose pins
are ordered per-event, per-edge copies with bounds inside the intervals. -/
theorem split_fifo {P : Pipe2} (H : PipeRun2 2 2 P) (HR : Realizes2 (symR split) 2 2 P) :
    (∀ j, j ≤ 2 → Protocol (ch2 2 P j)) ∧
    (∀ t, cnt (fallB (ch2 2 P 2).ack) t ≤ cnt (fallB (ch2 2 P 0).ack) t) ∧
    (∀ k e', TokAt (ch2 2 P 2) k e' →
      ∃ e, e < e' ∧ TokAt (ch2 2 P 0) k e ∧ (ch2 2 P 2).dat e' = (ch2 2 P 0).dat e) :=
  end_to_end2 split_check2 H HR (by decide)

/-- 8e's routes: `good` passes the per-link check, `bad` (no SDELAY) fails it,
and 8e's `bad_counterexample` shows that failure is real. -/
theorem good_check2 : checkPipe2 (symR good) 2 2 = true := by decide
theorem bad_check2 : checkPipe2 (symR bad) 2 2 = false := by decide

/-! ## A FASTRISE DACK line needs per-edge intervals -/

/-- `split` with stage 0's enable fan-out widened to 2..14 and a DACK
`bd_delay #(.N(5), .FASTRISE(1))` on every acknowledge: rise one hop (1..2 on
top of the wire and pin), fall the whole chain (11..13). -/
def dack : Route2 :=
  { symR split with
    ackR := fun _ => [(1, 2), (1, 2), (1, 2)]
    ackF := fun _ => [(1, 2), (11, 13), (1, 2)]
    enR := fun _ _ => [(2, 14)]
    enF := fun _ _ => [(2, 14)] }

theorem dack_check2 : checkPipe2 dack 2 2 = true := by decide

/-- The same line seen as one band covering both edges (what a single
interval per arc gives): the hold race fails. -/
def dackBand : Route2 :=
  { dack with
    ackR := fun _ => [(1, 2), (1, 13), (1, 2)]
    ackF := fun _ => [(1, 2), (1, 13), (1, 2)] }

theorem dack_band_rejects : checkPipe2 dackBand 2 2 = false := by decide

end Formal.Net.PerLink.Toy
