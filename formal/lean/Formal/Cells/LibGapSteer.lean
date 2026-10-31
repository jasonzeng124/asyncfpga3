import Formal.Cells.LibCtlMergeMux
open Formal.Core.LutList

/-!
# LibGapSteer: `bd_steer`'s select timing, per pin, sufficient AND necessary

Probe Blt (shard B, Phase 2 library gap). `bd_steer` (`cells/rtl/bd_ctl.v`) is
on every loop exit of gcd_hw (38 instances, every `cond_br`). Before this file
its two JSON rows (`bd_steer.bundled_s_setup`, `.bundled_s_hold`) were proved
**sufficient only**, with **lumped** LUT arcs (`OpsTimed.SteerGates.H_U5/H_U6`
read `req` and `s` at the same instant), and the per-pin arc difference
`u.I1` vs `u.I0` charged as an unproved margin.

    LUT6_2 #(.INIT(64'h8888_8888_2222_2222)) u (.I0(req), .I1(s), .I2(0),
           .I3(0), .I4(0), .I5(1), .O5(req0), .O6(req1));

## Model (named hypotheses)

* **H_PIN_READ** (per-pin LUT model): output `O_b` (`b = false`: `O5 = req0`,
  `b = true`: `O6 = req1`) at time `t` is the REAL INIT function
  (`LibCtlMergeMux.req0B/req1B`) of `req` at its driver read at `pr.σ t` and
  `s` at its driver read at `ps.σ t`, where each read map lies in a delay
  window `[t - hi, t - lo]` (wire + site pin + that pin's own LUT arc to that
  output; `Rd.comp` composes them). The two pins are read at DIFFERENT
  instants: input skew can glitch the output (the digital hazard PROGRAM.md
  asks for). Read maps need not be monotone (no FIFO assumption is used).
  Internal mux-tree delay after the pin buffers is folded into the per-pin
  arcs. Kleene version (section 5): an X on `s` is allowed at any time
  outside the window.
* **H_REQ_PULSE**: one token: `req` at its driver is high exactly on `[R, F)`.
* **H_S_STABLE** (env): `s` at its driver equals the token's condition `v` on
  `[S0, S1)`, and is ARBITRARY outside it (any binary glitching, or X).

## Spec (`SpecOK`, = `OpsSteer`'s `lut` field for one token)

`O_b t = req(pr.σ t) && (v == b)`: the selected branch is the request read
through its own pin, the unselected branch is constantly 0 (no spurious
token), exactly as if `s` were read at the request's instant.

## Results

* `steer_pin_ok` (sufficient, any read maps): H_SETUP_PIN
  `S0 + ps.hi ≤ R + pr.lo` and H_HOLD_PIN `F + pr.hi ≤ S1 + ps.lo` give SpecOK.
* `steer_pin_exact` (fixed delays `dr`, `ds`): SpecOK for every admissible `s`
  **iff** `S0 + ds ≤ R + dr ∧ F + dr ≤ S1 + ds`.
* `steer_box_exact` (headline): SpecOK for every read-map pair inside the box
  `pr ∈ [Rlo, Rhi]`, `ps ∈ [Slo, Shi]` and every admissible `s` **iff**
  `S0 + Shi ≤ R + Rlo ∧ F + Rhi ≤ S1 + Slo`.
* `spurious_token`: concrete counter-trace (setup violated by 100 ps): the
  UNSELECTED branch rises. `late_hold_glitch`: hold violated, unselected
  branch rises at the end of the pulse.
* `steer_tokens`: multi-token form (any number of tokens, per-token windows).
* `steer_pin_ok_K`: the sufficient half with `s : Int → K3` (X outside the
  window), through `req0K/req1K` (H_KLEENE_LUT).
* `witness_*`: non-vacuity: concrete numbers meeting every hypothesis, the
  selected branch does rise and fall.

NOT covered: the `uack` OR (`OpsTimed.steer_back`, H_ACK_SKEW); data
bundling at the receivers (their latch rows); the source of `S0`/`S1` (the
library contract: `S1` is the ack fall seen by the sender,
`OpsTimed2.steer_hold_of_ackfall`); a mid-rail select inside the mux tree
(H_KLEENE_LUT grade B); correlated corners: the box form is the box corner
(always sound); for a corner model apply `steer_pin_exact` per realisation.
-/

namespace Formal.Cells.LibGapSteer
open Formal.Cells
open Formal.Cells.LibCtlMergeMux (req0B req1B req0K req1K steer_req0 steer_req1)

/-- A per-pin read map in Int ps: at `t` the pin shows its driver at `σ t`,
`σ t ∈ [t - hi, t - lo]` (**H_PIN_READ**). -/
structure Rd where
  σ : Int → Int
  lo : Int
  hi : Int
  ge : ∀ t, t - hi ≤ σ t
  le : ∀ t, σ t ≤ t - lo

/-- A fixed transport delay `d`. -/
def Rd.const (d : Int) : Rd :=
  ⟨fun t => t - d, d, d, fun t => by omega, fun t => by omega⟩

/-- Wire `w` then arc `a`: the arc's output at `t` reads its pin at `a.σ t`,
which shows the driver at `w.σ (a.σ t)`. Bounds add. -/
def Rd.comp (w a : Rd) : Rd :=
  ⟨fun t => w.σ (a.σ t), w.lo + a.lo, w.hi + a.hi,
   fun t => by have := w.ge (a.σ t); have := a.ge t; omega,
   fun t => by have := w.le (a.σ t); have := a.le t; omega⟩

/-- Branch `b` of the steer from the REAL INIT: `b = false` is `O5 = req0`,
`b = true` is `O6 = req1`. -/
def outB (b r s : Bool) : Bool := if b then req1B r s else req0B r s

theorem outB_eq : ∀ b r s : Bool, outB b r s = (r && (s == b)) := by decide

/-- **H_REQ_PULSE**: one token's request at its driver. -/
def pulse (R F : Int) (t : Int) : Bool := decide (R ≤ t ∧ t < F)

/-- **H_S_STABLE**: `s` shows `v` on `[S0, S1)`; nothing is said outside. -/
def Stable (s : Int → Bool) (v : Bool) (S0 S1 : Int) : Prop :=
  ∀ t, S0 ≤ t → t < S1 → s t = v

/-- The spec: the branch output equals `OpsSteer`'s `lut` field for a token
with condition `v`: the request read through its pin, gated by `v == b`. -/
def SpecOK (b v : Bool) (pr ps : Rd) (R F : Int) (s : Int → Bool) : Prop :=
  ∀ t, outB b (pulse R F (pr.σ t)) (s (ps.σ t)) = (pulse R F (pr.σ t) && (v == b))

/-! ## 1. Sufficient, any read maps -/

theorem steer_pin_ok (b v : Bool) (pr ps : Rd) (R F S0 S1 : Int) (s : Int → Bool)
    (H_S_STABLE : Stable s v S0 S1)
    (H_SETUP_PIN : S0 + ps.hi ≤ R + pr.lo)
    (H_HOLD_PIN : F + pr.hi ≤ S1 + ps.lo) :
    SpecOK b v pr ps R F s := by
  intro t
  rw [outB_eq]
  by_cases h : R ≤ pr.σ t ∧ pr.σ t < F
  · have hp : pulse R F (pr.σ t) = true := by simp [pulse, h]
    have g1 := pr.ge t; have g2 := pr.le t; have g3 := ps.ge t; have g4 := ps.le t
    have hs : s (ps.σ t) = v := H_S_STABLE _ (by omega) (by omega)
    rw [hp, hs]
  · have hp : pulse R F (pr.σ t) = false := by simp [pulse, h]
    rw [hp]; rfl

/-! ## 2. Exact, fixed delays -/

/-- The adversarial select: `v` inside the window, `!v` outside (it CHANGED
at `S0` and again at `S1`: the physical case, not an artificial glitch). -/
def sAdv (v : Bool) (S0 S1 : Int) (t : Int) : Bool :=
  if S0 ≤ t ∧ t < S1 then v else !v

theorem sAdv_stable (v : Bool) (S0 S1 : Int) : Stable (sAdv v S0 S1) v S0 S1 := by
  intro t h1 h2; simp [sAdv, h1, h2]

theorem wrong_val (b v : Bool) : ((!v) == b) ≠ (v == b) := by
  cases b <;> cases v <;> decide

/-- Setup violated ⇒ SpecOK fails at `t = R + dr` (any branch: the
unselected one rises, the selected one is late). -/
theorem setup_needed (b v : Bool) (dr ds R F S0 S1 : Int) (hRF : R < F)
    (hbad : R + dr < S0 + ds) :
    ¬ SpecOK b v (Rd.const dr) (Rd.const ds) R F (sAdv v S0 S1) := by
  intro h
  have := h (R + dr)
  simp only [Rd.const] at this
  have e1 : R + dr - dr = R := by omega
  rw [e1] at this
  have hp : pulse R F R = true := by simp [pulse]; omega
  have hs : sAdv v S0 S1 (R + dr - ds) = !v := by
    simp [sAdv]; intro h1; omega
  rw [hp, hs, outB_eq] at this
  exact wrong_val b v (by simpa using this)

/-- Hold violated ⇒ SpecOK fails at `t = F - 1 + dr`. -/
theorem hold_needed (b v : Bool) (dr ds R F S0 S1 : Int) (hRF : R < F)
    (hbad : S1 + ds < F + dr) :
    ¬ SpecOK b v (Rd.const dr) (Rd.const ds) R F (sAdv v S0 S1) := by
  intro h
  have := h (F - 1 + dr)
  simp only [Rd.const] at this
  have e1 : F - 1 + dr - dr = F - 1 := by omega
  rw [e1] at this
  have hp : pulse R F (F - 1) = true := by simp [pulse]; omega
  have hs : sAdv v S0 S1 (F - 1 + dr - ds) = !v := by
    simp [sAdv]; intro _; omega
  rw [hp, hs, outB_eq] at this
  exact wrong_val b v (by simpa using this)

/-- **Exact condition, fixed delays.** -/
theorem steer_pin_exact (b v : Bool) (dr ds R F S0 S1 : Int) (hRF : R < F) :
    (∀ s, Stable s v S0 S1 → SpecOK b v (Rd.const dr) (Rd.const ds) R F s) ↔
    (S0 + ds ≤ R + dr ∧ F + dr ≤ S1 + ds) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction; intro hn
      exact setup_needed b v dr ds R F S0 S1 hRF (by omega) (h _ (sAdv_stable v S0 S1))
    · apply Classical.byContradiction; intro hn
      exact hold_needed b v dr ds R F S0 S1 hRF (by omega) (h _ (sAdv_stable v S0 S1))
  · rintro ⟨h1, h2⟩ s hs
    exact steer_pin_ok b v _ _ R F S0 S1 s hs (by simpa [Rd.const] using h1)
      (by simpa [Rd.const] using h2)

/-! ## 3. Exact over the delay box (the JSON form) -/

/-- **Headline.** For a nonempty box, SpecOK holds for every pair of read
maps inside it and every admissible select **iff** H_SETUP_PIN at
(`Shi`, `Rlo`) and H_HOLD_PIN at (`Rhi`, `Slo`). -/
theorem steer_box_exact (b v : Bool) (Rlo Rhi Slo Shi R F S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R < F) :
    (∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
      ∀ s, Stable s v S0 S1 → SpecOK b v pr ps R F s) ↔
    (S0 + Shi ≤ R + Rlo ∧ F + Rhi ≤ S1 + Slo) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := (steer_pin_exact b v Rlo Shi R F S0 S1 hRF).mp
        (fun s hs => h (Rd.const Rlo) (Rd.const Shi)
          (by simp [Rd.const]) (by simp [Rd.const]; omega)
          (by simp [Rd.const]; omega) (by simp [Rd.const]) s hs)
      exact this.1
    · have := (steer_pin_exact b v Rhi Slo R F S0 S1 hRF).mp
        (fun s hs => h (Rd.const Rhi) (Rd.const Slo)
          (by simp [Rd.const]; omega) (by simp [Rd.const])
          (by simp [Rd.const]) (by simp [Rd.const]; omega) s hs)
      exact this.2
  · rintro ⟨h1, h2⟩ pr ps a1 a2 a3 a4 s hs
    exact steer_pin_ok b v pr ps R F S0 S1 s hs (by omega) (by omega)

/-- Both branches of one `bd_steer` (O5 and O6 have their own per-pin arcs):
the four inequalities give the whole token. -/
theorem steer_both (v : Bool) (pr0 ps0 pr1 ps1 : Rd) (R F S0 S1 : Int)
    (s : Int → Bool) (hs : Stable s v S0 S1)
    (H_SETUP_O5 : S0 + ps0.hi ≤ R + pr0.lo) (H_HOLD_O5 : F + pr0.hi ≤ S1 + ps0.lo)
    (H_SETUP_O6 : S0 + ps1.hi ≤ R + pr1.lo) (H_HOLD_O6 : F + pr1.hi ≤ S1 + ps1.lo) :
    SpecOK false v pr0 ps0 R F s ∧ SpecOK true v pr1 ps1 R F s :=
  ⟨steer_pin_ok false v pr0 ps0 R F S0 S1 s hs H_SETUP_O5 H_HOLD_O5,
   steer_pin_ok true v pr1 ps1 R F S0 S1 s hs H_SETUP_O6 H_HOLD_O6⟩

/-! ## 4. Counter-traces and non-vacuity (concrete ps) -/

/-- Setup violated by 100 ps: `s` (token condition `true`) reaches the LUT
through 600 ps, `req` through 300 ps, `s` settled at 800, `req` rises at 1000.
At 1300 the UNSELECTED branch `O5 = req0` is high: a spurious token. -/
theorem spurious_token :
    outB false (pulse 1000 2000 ((Rd.const 300).σ 1300))
      (sAdv true 800 5000 ((Rd.const 600).σ 1300)) = true ∧
    (pulse 1000 2000 ((Rd.const 300).σ 1300) && (true == false)) = false := by
  decide

/-- Hold violated: `s` changes at 2100, read through 300 ps; `req` falls at
2000, read through 600 ps. At 2599 the unselected branch is high. -/
theorem late_hold_glitch :
    outB false (pulse 1000 2000 ((Rd.const 600).σ 2599))
      (sAdv true 0 2100 ((Rd.const 300).σ 2599)) = true := by
  decide

/-- Non-vacuity: `R = 1000, F = 3000, S0 = 500, S1 = 4000`, box
`req ∈ [200, 400]`, `s ∈ [300, 600]` meets both box inequalities. -/
theorem witness_box : (500 : Int) + 600 ≤ 1000 + 200 ∧ (3000 : Int) + 400 ≤ 4000 + 300 := by
  decide

/-- ... and in that run (`dr = 300`, `ds = 450`, `s = sAdv true 500 4000`)
the SELECTED branch `O6` is low at 1200, high at 1400 and low again at 3400,
while `O5` stays low at all three instants. -/
theorem witness_run :
    outB true (pulse 1000 3000 ((Rd.const 300).σ 1200)) (sAdv true 500 4000 ((Rd.const 450).σ 1200)) = false ∧
    outB true (pulse 1000 3000 ((Rd.const 300).σ 1400)) (sAdv true 500 4000 ((Rd.const 450).σ 1400)) = true ∧
    outB true (pulse 1000 3000 ((Rd.const 300).σ 3400)) (sAdv true 500 4000 ((Rd.const 450).σ 3400)) = false ∧
    outB false (pulse 1000 3000 ((Rd.const 300).σ 1200)) (sAdv true 500 4000 ((Rd.const 450).σ 1200)) = false ∧
    outB false (pulse 1000 3000 ((Rd.const 300).σ 1400)) (sAdv true 500 4000 ((Rd.const 450).σ 1400)) = false ∧
    outB false (pulse 1000 3000 ((Rd.const 300).σ 3400)) (sAdv true 500 4000 ((Rd.const 450).σ 3400)) = false := by
  decide

/-- The witness run satisfies every hypothesis of `steer_box_exact`'s right
side and of `steer_pin_ok` (so its conclusion is not vacuous). -/
theorem witness_hyps : SpecOK true true (Rd.const 300) (Rd.const 450) 1000 3000 (sAdv true 500 4000) :=
  steer_pin_ok true true _ _ 1000 3000 500 4000 _ (sAdv_stable true 500 4000)
    (by simp [Rd.const]) (by simp [Rd.const])

/-! ## 5. Multi-token, and Kleene select -/

/-- Any number of tokens: `req` high only inside token windows `[R k, F k)`;
`s` shows `v k` on `[S0 k, S1 k)`. Per-token H_SETUP_PIN / H_HOLD_PIN give:
whenever the branch's request read is inside token `k`'s pulse, the branch
shows `v k == b`; when the request read is low, the branch is low. -/
theorem steer_tokens (b : Bool) (pr ps : Rd) (req s : Int → Bool)
    (R F S0 S1 : Nat → Int) (v : Nat → Bool)
    (H_REQ_TOK : ∀ t, req t = true → ∃ k, R k ≤ t ∧ t < F k)
    (H_S_STABLE : ∀ k, Stable s (v k) (S0 k) (S1 k))
    (H_SETUP_PIN : ∀ k, S0 k + ps.hi ≤ R k + pr.lo)
    (H_HOLD_PIN : ∀ k, F k + pr.hi ≤ S1 k + ps.lo) (t : Int) :
    (req (pr.σ t) = false → outB b (req (pr.σ t)) (s (ps.σ t)) = false) ∧
    (req (pr.σ t) = true → ∃ k, R k ≤ pr.σ t ∧ pr.σ t < F k ∧
       outB b (req (pr.σ t)) (s (ps.σ t)) = (v k == b)) := by
  refine ⟨fun h => by rw [outB_eq, h]; rfl, fun h => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := H_REQ_TOK _ h
  refine ⟨k, hk1, hk2, ?_⟩
  have g1 := pr.ge t; have g2 := pr.le t; have g3 := ps.ge t; have g4 := ps.le t
  have := H_SETUP_PIN k; have := H_HOLD_PIN k
  have hs : s (ps.σ t) = v k := H_S_STABLE k _ (by omega) (by omega)
  rw [outB_eq, h, hs]; rfl

def outK (b : Bool) (r s : K3) : K3 := if b then req1K r s else req0K r s

/-- Kleene facts of the real INIT used below: request low ⇒ 0 whatever `s`
(even X); request high with a definite select ⇒ the Boolean value. -/
theorem outK_low : ∀ (b : Bool) (s : K3), outK b .f s = .f := by decide
theorem outK_def : ∀ b r s : Bool, outK b (.ofBool r) (.ofBool s) = .ofBool (outB b r s) := by
  decide

/-- **Kleene sufficient half**: `s` may be X (or anything) outside its window;
under H_SETUP_PIN / H_HOLD_PIN the branch output is DEFINITE at every instant
and equals the spec. -/
theorem steer_pin_ok_K (b v : Bool) (pr ps : Rd) (R F S0 S1 : Int) (sK : Int → K3)
    (H_S_STABLE_K : ∀ t, S0 ≤ t → t < S1 → sK t = .ofBool v)
    (H_SETUP_PIN : S0 + ps.hi ≤ R + pr.lo)
    (H_HOLD_PIN : F + pr.hi ≤ S1 + ps.lo) (t : Int) :
    outK b (.ofBool (pulse R F (pr.σ t))) (sK (ps.σ t)) =
      .ofBool (pulse R F (pr.σ t) && (v == b)) := by
  by_cases h : R ≤ pr.σ t ∧ pr.σ t < F
  · have hp : pulse R F (pr.σ t) = true := by simp [pulse, h]
    have g1 := pr.ge t; have g2 := pr.le t; have g3 := ps.ge t; have g4 := ps.le t
    have hs : sK (ps.σ t) = .ofBool v := H_S_STABLE_K _ (by omega) (by omega)
    rw [hp, hs, outK_def, outB_eq]
  · have hp : pulse R F (pr.σ t) = false := by simp [pulse, h]
    rw [hp]
    exact outK_low b _

end Formal.Cells.LibGapSteer
