import Formal.Core.Prims.Carry

/-!
# Formal.Cells.HPrimWin — H_PRIM in window form: the bounded-delay Kleene semantics

Shard B, THE goal (owner 2026-10-31): H_PRIM for every primitive the target uses,
with prjxray arcs. Core Lean only (no Mathlib). Notes: `formal/notes/B-hprim.md`.

## Problem, plainly

PROGRAM.md's H_PRIM asks each primitive to behave as its Core digital model "with
the delay semantics (transport, inertial or involution) that is pessimistic for
what is being proved, or prove the result for all three". Core's primitive
files (`Muxf`, `Carry`, `Lut62`) state their timing as per-pin transport with ONE
fixed delay per arc (`MuxTimed.H`, `Timed.H`). A theorem about the bitstream must
hold for every delay in the band, and for every way a real gate can respond to
pin skew, short pulses and slowly varying delays. Which single relation, used as
H_PRIM, is implied by all of these, so that a proof from it covers them all?

## The relation (`WinH`)

Arc `i` of an `n`-pin output has a band `[lo i, hi i]` (integer ps). At instant
`τ` pin `i` is "seen" over the whole window `[τ - hi i, τ - lo i]`. If `v i` is
any Kleene value that abstracts pin `i` on its window (`AbsOn`: the pin is
`v i` throughout, or `v i = X`), then the output at `τ` is at least as defined
as `f v`:

  `WinH f pin lo hi y  :=  ∀ τ v, (∀ i, AbsOn (v i) (pin i) (τ - hi i) (τ - lo i)) → f v ⊑ y τ`.

So the output is forced only when every relevant pin has been steady for its
whole window; while any pin is in flight the output may do anything that `f`'s
Kleene value allows (`X` = any binary waveform, runts and ringing included).
`f` is the primitive's Kleene function (the LUT mux tree, `mux2`, the CARRY4
chain), so internal hazards of the function are kept.

## Results

* `win_of_varTransport` : per-pin transport whose delay may change at every
  instant, each delay in its band (`lo i ≤ d i τ ≤ hi i`), implies `WinH`
  (for monotone `f`). Core's fixed-delay models are the special case:
  `win_of_timed` (`Carry.Timed.H`, used for CARRY4 and LUT outputs) and
  `win_of_mux` (`MuxTimed.H`, MUXF7/MUXF8).
* `win_widen` : `WinH` on a band implies `WinH` on every wider band. So a
  proof made under the guarded bands of H_DELAY(g) holds for all narrower ones;
  guard widening never needs a new proof of the primitive.
* `win_forced`, `win_settles` : the liveness half. If every pin is steady
  (Boolean `x i`) on its window, the output equals `f (ofBool ∘ x)` when that
  is defined; if every pin is steady from `s` on, the output is the Boolean
  value from `s + H` on, `H ≥ hi i` for every `i`.
* `win_sic` : single-input change with equal old/new value of a function whose
  Kleene value with that pin `X` is defined: no glitch, for every delay
  behaviour allowed by the window.
* `win_inertial` : a per-pin bounded-inertial behaviour (the output, at each
  instant, equals `f` of pin values each read at SOME instant inside the pin's
  window — which covers pulse swallowing, since a swallowed pulse is the output
  reading the older value) implies `WinH`. Proved as `win_of_sampled`.
* Involution: see `formal/lean/Formal/Cells/HPrimInv.lean` (needs ℝ): the window
  relation covers an involution channel when its `δmin` is at least the band's
  lower end, and NOT otherwise (a concrete trace).

## What this does NOT show

* That the silicon is one of these behaviours (H_PRIM itself, with
  H_KLEENE_LUT / H_MUXF_PASS / H_C4_PERPIN inside it).
* Flops: `WinH` is for combinational outputs. FDRE/FDSE use Core's
  `SeqFlop` relation, which carries its own hypothesis H_FF_RESOLVE (a bound on
  how long a disturbed flop stays undecided). That is NOT one of the five
  hypotheses THE goal allows, unless the theorem's boundary excludes every flop
  that can see an asynchronous input (see notes/B-hprim.md).
-/

namespace Formal.Cells.HPrimWin

open Formal.Core Formal.Core.K3 Formal.Core.Prims

/-- `v` abstracts the waveform `w` on the closed window `[a, b]`. -/
def AbsOn (v : K3) (w : Wave) (a b : Int) : Prop := ∀ t, a ≤ t → t ≤ b → v ⊑ w t

theorem absOn_X (w : Wave) (a b : Int) : AbsOn .X w a b := fun _ _ _ => X_le _

/-- A pin that is the Boolean `c` throughout the window is abstracted by `c`. -/
theorem absOn_const {w : Wave} {a b : Int} {c : Bool} (h : ∀ t, a ≤ t → t ≤ b → w t = ofBool c) :
    AbsOn (ofBool c) w a b := fun t h1 h2 => by rw [h t h1 h2]; exact le_refl _

/-- A smaller window is abstracted by whatever abstracts a larger one. -/
theorem absOn_sub {v : K3} {w : Wave} {a b a' b' : Int} (h : AbsOn v w a b) (ha : a ≤ a')
    (hb : b' ≤ b) : AbsOn v w a' b' := fun t h1 h2 => h t (by omega) (by omega)

variable {n : Nat}

/-- **The window semantics of one primitive output** (H_PRIM, window form). -/
def WinH (f : (Fin n → K3) → K3) (pin : Fin n → Wave) (lo hi : Fin n → Int) (y : Wave) : Prop :=
  ∀ τ (v : Fin n → K3), (∀ i, AbsOn (v i) (pin i) (τ - hi i) (τ - lo i)) → f v ⊑ y τ

/-- `f` is monotone in the information order. -/
def Mono (f : (Fin n → K3) → K3) : Prop := ∀ u v, VLe u v → f u ⊑ f v

/-! ## Transport and sampled behaviours imply the window relation -/

/-- **Sampled behaviour.** At each instant the output is at least as defined as `f`
of the pins, pin `i` read at some instant `s i τ` inside its window. -/
theorem win_of_sampled {f : (Fin n → K3) → K3} (hf : Mono f) {pin : Fin n → Wave}
    {lo hi : Fin n → Int} {y : Wave} (s : Fin n → Int → Int)
    (hs : ∀ i τ, τ - hi i ≤ s i τ ∧ s i τ ≤ τ - lo i)
    (h : ∀ τ, f (fun i => pin i (s i τ)) ⊑ y τ) : WinH f pin lo hi y := by
  intro τ v hv
  exact le_trans (hf _ _ (fun i => hv i _ (hs i τ).1 (hs i τ).2)) (h τ)

/-- **Time-varying transport.** Pin `i` reaches the output with delay `d i τ`,
which may change at every instant but stays in the band. -/
theorem win_of_varTransport {f : (Fin n → K3) → K3} (hf : Mono f) {pin : Fin n → Wave}
    {lo hi : Fin n → Int} {y : Wave} (d : Fin n → Int → Int)
    (hd : ∀ i τ, lo i ≤ d i τ ∧ d i τ ≤ hi i)
    (h : ∀ τ, f (fun i => pin i (τ - d i τ)) ⊑ y τ) : WinH f pin lo hi y :=
  win_of_sampled hf (fun i τ => τ - d i τ)
    (fun i τ => ⟨by have := (hd i τ).2; omega, by have := (hd i τ).1; omega⟩) h

/-- Core's fixed-delay per-pin transport (`Carry.Timed.H`), delays in band. -/
theorem win_of_timed {f : (Fin n → K3) → K3} (hf : Mono f) (T : Timed n)
    {lo hi : Fin n → Int} (hd : ∀ i, lo i ≤ T.d i ∧ T.d i ≤ hi i) (h : T.H f) :
    WinH f T.pin lo hi T.y :=
  win_of_varTransport hf (fun i _ => T.d i) (fun i _ => hd i) h

/-- The MUXF7/MUXF8 Kleene function on pins `0 = I0`, `1 = I1`, `2 = S`. -/
def muxF (v : Fin 3 → K3) : K3 := mux2 (v 2) (v 0) (v 1)

/-- The three pin waveforms of a `MuxTimed`, in `muxF`'s order. -/
def muxPins (M : MuxTimed) : Fin 3 → Wave := fun i =>
  if i.val = 0 then M.i0 else if i.val = 1 then M.i1 else M.s

/-- The three arc delays of a `MuxTimed`, in `muxF`'s order. -/
def muxD (M : MuxTimed) : Fin 3 → Int := fun i =>
  if i.val = 0 then M.d0 else if i.val = 1 then M.d1 else M.dS

theorem muxF_mono : Mono muxF := fun _ _ h => mux2_mono (h 2) (h 0) (h 1)

/-- Core's MUXF model (`MuxTimed.H`, fixed delays) with delays in band implies `WinH`. -/
theorem win_of_mux (M : MuxTimed) {lo hi : Fin 3 → Int}
    (hd : ∀ i, lo i ≤ muxD M i ∧ muxD M i ≤ hi i) (h : M.H) : WinH muxF (muxPins M) lo hi M.y := by
  apply win_of_varTransport muxF_mono (fun i _ => muxD M i) (fun i _ => hd i)
  intro τ
  exact h τ

/-- **Bounded inertial (sampled) behaviour.** The output at each instant EQUALS `f`
of pin values each taken at some instant inside the pin's window. A pulse the gate
swallows is the output still reading the older value; so swallowing, pulse
shrinking and delay jitter inside the band are all instances. -/
theorem win_inertial {f : (Fin n → K3) → K3} (hf : Mono f) {pin : Fin n → Wave}
    {lo hi : Fin n → Int} {y : Wave}
    (h : ∀ τ, ∃ s : Fin n → Int, (∀ i, τ - hi i ≤ s i ∧ s i ≤ τ - lo i) ∧
      y τ = f (fun i => pin i (s i))) : WinH f pin lo hi y := by
  intro τ v hv
  obtain ⟨s, hs, hy⟩ := h τ
  rw [hy]
  exact hf _ _ (fun i => hv i _ (hs i).1 (hs i).2)

/-! ## Guard widening -/

/-- **A wider band gives a weaker relation.** Anything proved from `WinH` on the
guarded bands holds for every behaviour in narrower bands. -/
theorem win_widen {f : (Fin n → K3) → K3} {pin : Fin n → Wave} {lo hi lo' hi' : Fin n → Int}
    {y : Wave} (hlo : ∀ i, lo' i ≤ lo i) (hhi : ∀ i, hi i ≤ hi' i) (h : WinH f pin lo hi y) :
    WinH f pin lo' hi' y := by
  intro τ v hv
  exact h τ v (fun i => absOn_sub (hv i) (by have := hhi i; omega) (by have := hlo i; omega))

/-! ## Liveness: steady pins force the output -/

/-- Every pin Boolean-steady on its window, `f` defined there: the output is forced. -/
theorem win_forced {f : (Fin n → K3) → K3} {pin : Fin n → Wave} {lo hi : Fin n → Int}
    {y : Wave} (h : WinH f pin lo hi y) (τ : Int) (x : Fin n → Bool)
    (hx : ∀ i t, τ - hi i ≤ t → t ≤ τ - lo i → pin i t = ofBool (x i)) {c : Bool}
    (hc : f (ofBoolVec x) = ofBool c) : y τ = ofBool c := by
  have := h τ (ofBoolVec x) (fun i => absOn_const (hx i))
  rw [hc] at this
  exact ofBool_le_iff.mp this

/-- **Settling.** Every pin steady (Boolean `x i`) from `s` on, `H` at least every
arc's upper end, `0 ≤ lo i`: from `s + H` on the output is `f`'s Boolean value. -/
theorem win_settles {f : (Fin n → K3) → K3} {pin : Fin n → Wave} {lo hi : Fin n → Int}
    {y : Wave} (h : WinH f pin lo hi y) (s H : Int) (hH : ∀ i, hi i ≤ H) (x : Fin n → Bool)
    (hx : ∀ i t, s ≤ t → pin i t = ofBool (x i)) {c : Bool} (hc : f (ofBoolVec x) = ofBool c)
    (τ : Int) (hτ : s + H ≤ τ) : y τ = ofBool c :=
  win_forced h τ x (fun i t h1 _ => hx i t (by have := hH i; omega)) hc

/-- **Single-input change, any delay behaviour in the window.** All pins but `j`
are Boolean-steady (`x`); pin `j` may do anything. If `f` with pin `j` at `X` is
the defined value `c`, the output is `c` at every instant. -/
theorem win_sic {f : (Fin n → K3) → K3} {pin : Fin n → Wave} {lo hi : Fin n → Int}
    {y : Wave} (h : WinH f pin lo hi y) (x : Fin n → Bool) (j : Fin n)
    (hpins : ∀ i, i ≠ j → ∀ t, pin i t = ofBool (x i)) {c : Bool}
    (hc : f (setAt (ofBoolVec x) j .X) = ofBool c) (τ : Int) : y τ = ofBool c := by
  have hv : ∀ i, AbsOn (setAt (ofBoolVec x) j .X i) (pin i) (τ - hi i) (τ - lo i) := by
    intro i t _ _
    by_cases e : i = j
    · simp only [setAt, e, ite_true]; exact X_le _
    · simp only [setAt, e, ite_false, ofBoolVec]; rw [hpins i e t]; exact le_refl _
  have := h τ _ hv
  rw [hc] at this
  exact ofBool_le_iff.mp this

/-! ## The window relation is strictly weaker than fixed-delay transport -/

/-- A one-pin buffer with band `[1, 2]`: the output may switch at delay 1 for one
edge and 2 for the next (pulse widened by one), which no fixed-delay transport
model allows, but `WinH` does. Concretely: input high on `[0, 3)`; output high on
`[1, 5)`. -/
def bufIn : Wave := fun t => if 0 ≤ t ∧ t < 3 then .one else .zero
def bufOut : Wave := fun t => if 1 ≤ t ∧ t < 5 then .one else .zero

theorem buf_win : WinH (n := 1) (fun v => v 0) (fun _ => bufIn) (fun _ => 1) (fun _ => 2) bufOut := by
  apply win_of_varTransport (fun u v huv => huv 0) (fun _ τ => if τ ≤ 3 then 1 else 2)
  · intro i τ; split <;> omega
  · intro τ
    by_cases h : τ ≤ 3 <;> simp only [h, ite_true, ite_false, bufIn, bufOut] <;> split <;> split <;>
      first | exact le_refl _ | omega

theorem buf_not_fixed : ¬ ∃ d : Int, ∀ τ, bufOut τ = bufIn (τ - d) := by
  rintro ⟨d, hd⟩
  have h1 : bufIn (1 - d) = .one := by rw [← hd 1]; decide
  have h4 : bufIn (4 - d) = .one := by rw [← hd 4]; decide
  simp only [bufIn] at h1 h4
  split at h1 <;> split at h4 <;> first | omega | exact absurd h1 (by decide) | exact absurd h4 (by decide)

end Formal.Cells.HPrimWin
