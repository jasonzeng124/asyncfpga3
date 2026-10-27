import Formal.Net.EndToEnd

/-!
# Probe C-8e: the end-to-end theorem on a toy 2-stage, 2-bit `bd_pipe`

Delays are ILLUSTRATIVE (not prjxray data), in units of 10 ps (1 tick = 10 ps
in this file only; nothing in the model depends on the unit).

Routed paths (arc intervals, in routing order):
* `req 1` source → stage 0 req pin: wire 6..8, DELAY line LUT 6..8, LUT pin 1..2
* `req 2` stage 0 → stage 1 req pin: wire 2..3, SDELAY LUT 10..12, wire 1..3, LUT pin 1..2
* `req 3` stage 1 → sink: wire 10..12, pin 1..2
* `ack k` (DACK = 0): wire 1..2, LUT pin 1..2
* `en j b` latch enable (fan-out of the node to each latch LUT): 2..14
* `dat j b` data bus wire into the latch LUT: 12..14

`good` passes `checkPipe` with setup `m = 15`, hold `h = 2` (every race has
zero slack, the margins were chosen at the edge). `bad` is `good` without
the SDELAY line (`req 2` = wire 2..3, pin 1..2), i.e. `bd_pipe` with
`SDELAY = 0`: it is rejected for EVERY `(m, h)` (`bad_rejects`), and it has a
run (`cex`, delays inside the routed intervals, every gate hypothesis true)
in which token 0 (value 1) reaches the sink as 0 (`bad_counterexample`): stage 1
closes before the data from stage 0's latch has crossed the data wire, the
LIBRARY.md "closing wave outruns the data wave" failure of `tb_link`. With
the SDELAY line the same delays (`run_good`) deliver 1 (`good_delivers`),
so the hypotheses of `end_to_end` are satisfiable on the accepted route.
-/

namespace Formal.Net.EndToEnd.Toy
open Formal.Net Formal.Net.Handshake Formal.Timing Formal.Net.EndToEnd

def good : Route where
  req := fun k => match k with
    | 1 => [(6, 8), (6, 8), (1, 2)]
    | 2 => [(2, 3), (9, 12), (1, 3), (1, 2)]
    | 3 => [(10, 12), (1, 2)]
    | _ => []
  ack := fun _ => [(1, 2), (1, 2)]
  en := fun _ _ => [(2, 14)]
  dat := fun _ _ => [(12, 14)]

def bad : Route := { good with
  req := fun k => match k with
    | 1 => [(6, 8), (6, 8), (1, 2)]
    | 2 => [(2, 3), (1, 2)]
    | 3 => [(10, 12), (1, 2)]
    | _ => [] }

/-- The verified checker accepts the toy (kernel `decide`). -/
theorem good_check : checkPipe good 2 2 15 2 = true := by decide

/-- ...and rejects the SDELAY-less one at the same margins. -/
theorem bad_check : checkPipe bad 2 2 15 2 = false := by decide

/-- **The toy is a FIFO**: `end_to_end` instantiated. Every run of the 2-stage
pipe whose delays lie in `good`'s intervals obeys the protocol and delivers
the source's tokens in order. -/
theorem good_fifo {P : Pipe} (H : PipeRun 2 2 P) (HR : Realizes good 2 2 P) :
    (∀ j, j ≤ 2 → Protocol (ch 2 P j)) ∧
    (∀ t, cnt (fallB (ch 2 P 2).ack) t ≤ cnt (fallB (ch 2 P 0).ack) t) ∧
    (∀ k e', TokAt (ch 2 P 2) k e' →
      ∃ e, e < e' ∧ TokAt (ch 2 P 0) k e ∧ (ch 2 P 2).dat e' = (ch 2 P 0).dat e) :=
  end_to_end good_check H HR (by decide)

/-! ## Concrete runs (one token, value 1 on bit 0) -/

def on (a b t : Nat) : Bool := decide (a ≤ t ∧ t < b)
def from_ (a t : Nat) : Bool := decide (a ≤ t)

theorem on_after {a b t : Nat} (h : b ≤ t) : on a b t = false := by simp [on]; omega
theorem from_after {a t : Nat} (h : a ≤ t) : from_ a t = true := by simp [from_]; omega

/-- Delays of both runs (sums of per-arc delays inside the intervals);
`r2` is the stage 0 → stage 1 request path: 3 without SDELAY, 14 with it. -/
def mk (r2 : Nat) (x : Nat → Trace) (Q : Nat → Nat → Trace) : Pipe where
  x := x
  Q := Q
  dR := fun k => match k with | 1 => 13 | 2 => r2 | 3 => 11 | _ => 0
  dA := fun _ => 2
  dG := fun j _ => match j with | 0 => 14 | _ => 2
  dD := fun j _ => match j with | 0 => 12 | _ => 14

/-- The bad route's run (ASAP firing; events: src req 0↑ 17↓, c0 14↑ 31↓,
c1 18↑ 35↓, sink ack 30↑ 47↓; Q1 bit 0 rises at 29, Q2 never). -/
def xb : Nat → Trace := fun k => match k with
  | 0 => on 1 18 | 1 => on 15 32 | 2 => on 19 36 | 3 => on 31 48 | _ => fun _ => false
def Qb : Nat → Nat → Trace := fun j b => match j, b with
  | 0, 0 => from_ 1 | 1, 0 => from_ 30 | _, _ => fun _ => false
def cex : Pipe := mk 3 xb Qb

/-- The good route's run: same delays, SDELAY path 14 (c1 29↑, Q2 bit 0 at 44). -/
def xg : Nat → Trace := fun k => match k with
  | 0 => on 1 18 | 1 => on 15 33 | 2 => on 30 48 | 3 => on 42 60 | _ => fun _ => false
def Qg : Nat → Nat → Trace := fun j b => match j, b with
  | 0, 0 => from_ 1 | 1, 0 => from_ 30 | 2, 0 => from_ 45 | _, _ => fun _ => false
def run_good : Pipe := mk 14 xg Qg

theorem cel_late (r a q : Bool) (hr : r = false) (hq : q = false) : celN r a q = false := by
  subst hr; subst hq; cases a <;> decide

theorem cex_run : PipeRun 2 2 cex where
  H_RESET := by
    intro k hk
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    all_goals decide
  H_CEL := by
    intro k h1 h2 t
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    all_goals
      by_cases ht : t < 64
      · revert t; decide
      · left
        simp (disch := omega) only [cex, mk, xb, on_after]
  H_SRC := by
    intro t
    by_cases ht : t < 64
    · revert t; decide
    · intro h; exfalso; apply h
      simp (disch := omega) only [cex, mk, xb, on_after]
  H_SNK := by
    intro t
    by_cases ht : t < 64
    · revert t; decide
    · intro h; exfalso; apply h
      simp (disch := omega) only [cex, mk, xb, on_after]
  H_SRC_DATA := by
    intro b hb t
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    · by_cases ht : t < 64
      · revert t; decide
      · intro h; exfalso; apply h
        simp (disch := omega) only [cex, mk, Qb, from_after]
    · intro h; exfalso; exact h rfl
  H_LATCH_CELL := by
    intro j hj b hb t
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals
      by_cases ht : t < 64
      · revert t; decide
      · simp (disch := omega) only [cex, mk, xb, Qb, shift_eq, on_after, from_after]
        decide

theorem good_run : PipeRun 2 2 run_good where
  H_RESET := by
    intro k hk
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    all_goals decide
  H_CEL := by
    intro k h1 h2 t
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    all_goals
      by_cases ht : t < 80
      · revert t; decide
      · left
        simp (disch := omega) only [run_good, mk, xg, on_after]
  H_SRC := by
    intro t
    by_cases ht : t < 80
    · revert t; decide
    · intro h; exfalso; apply h
      simp (disch := omega) only [run_good, mk, xg, on_after]
  H_SNK := by
    intro t
    by_cases ht : t < 80
    · revert t; decide
    · intro h; exfalso; apply h
      simp (disch := omega) only [run_good, mk, xg, on_after]
  H_SRC_DATA := by
    intro b hb t
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    · by_cases ht : t < 80
      · revert t; decide
      · intro h; exfalso; apply h
        simp (disch := omega) only [run_good, mk, Qg, from_after]
    · intro h; exfalso; exact h rfl
  H_LATCH_CELL := by
    intro j hj b hb t
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals
      by_cases ht : t < 80
      · revert t; decide
      · simp (disch := omega) only [run_good, mk, xg, Qg, shift_eq, on_after, from_after]
        decide

/-- The per-arc delays (each inside its interval) that sum to the run's path delays. -/
theorem realizes (R : Route) (r2 : List Nat) (hr2 : inPath r2 (R.req 2))
    (h1 : R.req 1 = [(6, 8), (6, 8), (1, 2)]) (h3 : R.req 3 = [(10, 12), (1, 2)])
    (ha : ∀ k, R.ack k = [(1, 2), (1, 2)]) (he : ∀ j b, R.en j b = [(2, 14)])
    (hd : ∀ j b, R.dat j b = [(12, 14)]) (x : Nat → Trace) (Q : Nat → Nat → Trace) :
    Realizes R 2 2 (mk r2.sum x Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k k1 k2
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact ⟨[6, 6, 1], by rw [h1]; simp [inPath], rfl⟩
    · exact ⟨r2, hr2, rfl⟩
    · exact ⟨[10, 1], by rw [h3]; simp [inPath], rfl⟩
  · intro k _; exact ⟨[1, 1], by rw [ha]; simp [inPath], rfl⟩
  · intro j hj b _
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact ⟨[14], by rw [he]; simp [inPath], rfl⟩
    · exact ⟨[2], by rw [he]; simp [inPath], rfl⟩
  · intro j hj b _
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact ⟨[12], by rw [hd]; simp [inPath], rfl⟩
    · exact ⟨[14], by rw [hd]; simp [inPath], rfl⟩

theorem cex_realizes : Realizes bad 2 2 cex :=
  realizes bad [2, 1] (by simp [bad, inPath]) rfl rfl (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) xb Qb

theorem good_realizes : Realizes good 2 2 run_good :=
  realizes good [2, 10, 1, 1] (by simp [good, inPath]) rfl rfl (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) xg Qg

/-- The bad route is rejected for every choice of margins: `Sep` needs
`m ≤ 4` on the SDELAY-less link, the stage-1 latch setup needs `m ≥ 15`. -/
theorem bad_rejects : ∀ m h, checkPipe bad 2 2 m h = false := by
  intro m h
  apply Classical.byContradiction; intro hc
  have hc' : checkPipe bad 2 2 m h = true := by
    cases h' : checkPipe bad 2 2 m h <;> simp_all
  have T := timing_of_check hc' cex_realizes
  have h1 := T.sep 0 (by decide)
  have h2 := T.lat_setup 1 (by decide) 0 (by decide)
  simp [cex, mk] at h1 h2
  omega

/-- **The rejection is real**: a run of the rejected route, with every gate
hypothesis of `end_to_end` true and every delay inside the routed intervals,
in which the sink's token 0 (closing at tick 47) is NOT the source's token 0:
the source sent 1, the sink receives 0. -/
theorem bad_counterexample :
    PipeRun 2 2 cex ∧ Realizes bad 2 2 cex ∧ TokAt (ch 2 cex 2) 0 47 ∧
    (ch 2 cex 2).dat 47 = 0 ∧
    (∀ e, TokAt (ch 2 cex 0) 0 e → (ch 2 cex 0).dat e = 1) ∧
    ¬ (∀ k e', TokAt (ch 2 cex 2) k e' →
        ∃ e, e < e' ∧ TokAt (ch 2 cex 0) k e ∧ (ch 2 cex 2).dat e' = (ch 2 cex 0).dat e) := by
  have htok : TokAt (ch 2 cex 2) 0 47 := ⟨by decide, by decide⟩
  have hd2 : (ch 2 cex 2).dat 47 = 0 := by decide
  have hsrc : ∀ e, TokAt (ch 2 cex 0) 0 e → (ch 2 cex 0).dat e = 1 := by
    intro e ⟨hf, _⟩
    have he : 1 ≤ e := by
      apply Classical.byContradiction; intro h0
      rw [show e = 0 by omega] at hf; revert hf; decide
    show enc 2 (fun b => Qb 0 b e) = 1
    simp [enc, Qb, from_, he]
  refine ⟨cex_run, cex_realizes, htok, hd2, hsrc, fun hf => ?_⟩
  obtain ⟨e, _, he, hv⟩ := hf 0 47 htok
  rw [hd2, hsrc e he] at hv
  exact absurd hv (by decide)

/-- The accepted route's run delivers the source's value 1 at the sink's
first close (tick 59): the hypotheses of `good_fifo` are satisfiable. -/
theorem good_delivers :
    PipeRun 2 2 run_good ∧ Realizes good 2 2 run_good ∧ TokAt (ch 2 run_good 2) 0 59 ∧
    (ch 2 run_good 2).dat 59 = 1 := by
  refine ⟨good_run, good_realizes, ⟨by decide, by decide⟩, by decide⟩

end Formal.Net.EndToEnd.Toy
