import Formal.Net.Muller
import Formal.Net.MullerRun

/-!
# Track 8, probe 8c: speed-independence of the `bd_pipe` control chain, instances

Model and checker: `Formal/Net/Muller.lean`. Trace corollaries:
`Formal/Net/MullerRun.lean`. All instance proofs are `decide +kernel` on
`check` (in-kernel BFS + closure check), then `check_sound`. No
native code, no axiom beyond Lean's standard ones.

* `free_hazard_n1`, `free_hazard_n2`: with the feedback wire treated as just
  another wire of unknown delay, the REAL `bd_c2n` LUT glitches. n = 1: after
  `src↑ c0↑ b0↑ snk↑` with the feedback still in flight, pin I2 still reads 0,
  the inputs are `a=1, b=1` (hold), so the LUT re-computes 0: `c0` is
  excited to fall while `w0` (ack to the source) has not yet seen the rise.
  n = 2 (other side): `src↑ c0↑ w0↑ src↓` with the feedback in flight.
  So the C-element is NOT speed-independent on its own: its feedback wire
  must win a race against the loop through its neighbours.
* `iso_good_n` (n = 1..4): with the feedback isochronic (pin I2 reads O), every
  reachable state is hazard-free and every link obeys the pair rules.
* `rt_good_n` (n = 1..3): feedback is an ordinary wire, plus the relative
  timing hypothesis H_FB_BEFORE_INPUT (see `Muller.allowed`): same result.
* `*_protocol`, `*_token_order` (n as above): the trace corollaries for every
  execution (four-phase protocol on every link, token order between stages).

Larger instances: `rt` n = 4 (6076 states, 18 nodes) runs out of memory with
the in-kernel BFS on this 15 GB sandbox and a literal-certificate variant is
slow in the kernel (see `formal/notes/C-8c-muller.md`); `iso` n = 5 is not
attempted in the claimed file.
-/

namespace Formal.Net.Muller

/-! ## The hazard of a free feedback wire -/

def runPath (m : Mode) (n : Nat) : Nat → List Nat → Option Nat
  | s, [] => some s
  | s, y :: ys => if enabled m n s y then runPath m n (fire s y) ys else none

theorem runPath_reach {m n} : ∀ {s s' : Nat} (p : List Nat), Reach m n s →
    runPath m n s p = some s' → Reach m n s'
  | s, s', [], hs, h => by simp only [runPath, Option.some.injEq] at h; exact h ▸ hs
  | s, s', y :: ys, hs, h => by
    simp only [runPath] at h
    split at h
    · exact runPath_reach ys (Reach.step hs ⟨y, by assumption, rfl⟩) h
    · cases h

/-- n = 1: `src↑ c0↑ b0↑ snk↑`, then `c0` fires (falls) and withdraws the
excitation of `w0` (a runt on `ack_in`). -/
theorem free_hazard_n1 : Reach .iso 1 15 ∧ ¬ HazardFree .iso 1 15 := by
  refine ⟨runPath_reach [src, c 0, b 0, snk] Reach.init (by decide), fun h => ?_⟩
  have := h (w 0) (c 0) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- n = 2: `src↑ c0↑ w0↑ src↓`, then `c0` falls and withdraws the excitation of
`b0` (a runt on the req to stage 1). -/
theorem free_hazard_n2 : Reach .free 2 20 ∧ ¬ HazardFree .free 2 20 := by
  refine ⟨runPath_reach [src, c 0, w 0, src] Reach.init (by decide), fun h => ?_⟩
  have := h (b 0) (c 0) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-! ## Isochronic feedback: speed-independent, n = 1..4 -/

theorem iso_check_1 : check .iso 1 = true := by decide +kernel
theorem iso_check_2 : check .iso 2 = true := by decide +kernel
theorem iso_check_3 : check .iso 3 = true := by decide +kernel
theorem iso_check_4 : check .iso 4 = true := by decide +kernel

theorem iso_good_1 : ∀ s, Reach .iso 1 s → Good .iso 1 s := check_sound iso_check_1
theorem iso_good_2 : ∀ s, Reach .iso 2 s → Good .iso 2 s := check_sound iso_check_2
theorem iso_good_3 : ∀ s, Reach .iso 3 s → Good .iso 3 s := check_sound iso_check_3
theorem iso_good_4 : ∀ s, Reach .iso 4 s → Good .iso 4 s := check_sound iso_check_4

/-! ## Free feedback wire + H_FB_BEFORE_INPUT: speed-independent, n = 1..3 -/

theorem rt_check_1 : check .rt 1 = true := by decide +kernel
theorem rt_check_2 : check .rt 2 = true := by decide +kernel
theorem rt_check_3 : check .rt 3 = true := by decide +kernel

theorem rt_good_1 : ∀ s, Reach .rt 1 s → Good .rt 1 s := check_sound rt_check_1
theorem rt_good_2 : ∀ s, Reach .rt 2 s → Good .rt 2 s := check_sound rt_check_2
theorem rt_good_3 : ∀ s, Reach .rt 3 s → Good .rt 3 s := check_sound rt_check_3

/-! ## Trace corollaries (stated for the largest instances; the smaller ones
are the same one-liners) -/

/-- Four-stage chain, isochronic feedback: every link is a four-phase channel
on every execution. Link `k` (`1 ≤ k < 4`): req `b (k-1)`, ack `c k` (driver)
or `w k` (at stage k-1's pin); link 0: `src`/`c 0`, `src`/`w 0`; link 4:
`b 3`/`snk`. -/
theorem iso4_protocol {σ} (hr : Run .iso 4 σ) {X Y : Nat} (hp : (X, Y) ∈ pairs 4) :
    Handshake.Protocol (chanOf σ X Y) := run_protocol iso_good_4 hr hp

theorem iso4_token_order {σ} (hr : Run .iso 4 σ) {k : Nat} (hk1 : 1 ≤ k) (hkn : k < 4)
    (t : Nat) :
    tog (nodeTrace σ (c k)) t ≤ tog (nodeTrace σ (c (k - 1))) t ∧
    tog (nodeTrace σ (c (k - 1))) t ≤ tog (nodeTrace σ (c k)) t + 1 :=
  run_token_order iso_good_4 hr hk1 hkn t

theorem rt3_protocol {σ} (hr : Run .rt 3 σ) {X Y : Nat} (hp : (X, Y) ∈ pairs 3) :
    Handshake.Protocol (chanOf σ X Y) := run_protocol rt_good_3 hr hp

theorem rt3_token_order {σ} (hr : Run .rt 3 σ) {k : Nat} (hk1 : 1 ≤ k) (hkn : k < 3)
    (t : Nat) :
    tog (nodeTrace σ (c k)) t ≤ tog (nodeTrace σ (c (k - 1))) t ∧
    tog (nodeTrace σ (c (k - 1))) t ≤ tog (nodeTrace σ (c k)) t + 1 :=
  run_token_order rt_good_3 hr hk1 hkn t

end Formal.Net.Muller
