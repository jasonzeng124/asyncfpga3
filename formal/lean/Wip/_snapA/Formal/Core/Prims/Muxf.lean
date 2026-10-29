import Formal.Core.Kleene
import Formal.Core.Prims.XrayData

/-!
# Formal.Core.Prims.Muxf — MUXF7 / MUXF8 as the slice's 2:1 pass-transistor mux

Shard A, probe PrimsComb (north-star goal 1). Core Lean only (no Mathlib).
Notes: `formal/notes/A-prims-comb.md`.

## Model

A 7-series slice has two `F7MUX`es (F7AMUX: A6LUT/B6LUT, F7BMUX: C6LUT/D6LUT)
and one `F8MUX` (over the two F7 outputs), each `O = S ? I1 : I0`
(UG474 "Multiplexers"). Modelled, like one node of the LUT mux tree, as a
**2:1 pass-transistor mux** (hypothesis **H_MUXF_PASS**, see below):

* static value `mux2 s a b` over `Formal.Core.K3`: select `0` passes `I0`,
  `1` passes `I1`, and a select that is `X` (mid-rail, in transit) passes the
  common value when `I0 = I1` and gives `X` otherwise (`K3.merge`). This is the
  same node as Core's LUT `kevalT` and shard C's `Formal.Net.CoreLut.kmux`
  (equality with shard C's model checked in `Formal.Core.Prims.GenCheck`).
* timing: **per-pin transport** arcs `I0 -> O`, `I1 -> O`, `S -> O` from
  prjxray-db (`XrayData.selmux st fm`, generated), one band per arc for both edges
  (prjxray has no rise/fall split), corners never mixed. `MuxTimed.H` asks the
  output to be at least as defined as `mux2` of the three pins, each delayed by
  its own arc; `MuxTimed.exact` is the instance where it is equal (pure transport
  per pin, as the research GLS's `FID_MUX2` under `GLS_MODEL=fid`).

## Results

* Static: `mux2_ofBool` (Boolean agreement), `mux2_mono` (monotone in the
  information order), `mux2_contain` (X containment: a defined output is the
  Boolean mux of every resolution), `mux2_exact` (it is the *most* defined
  monotone extension: defined exactly when all resolutions agree),
  `mux2_X_same` (X select, equal data → the data).
* Pass-transistor vs AND-OR: `aoMux` (the gate realisation `¬s·a + s·b`) is
  strictly less defined (`aoMux_le_mux2`, `aoMux_hazard`): an AND-OR mux has
  the classic static-1 hazard on a select change, the pass-transistor mux does
  not. Which one the silicon is decides hazard freedom; this is H_MUXF_PASS.
* Timed, any delays: `MuxTimed.sound` (every instant ⊒ static Kleene value of the
  pins' abstraction), `sel_change_glitch_free` (select changes, data equal:
  no glitch, for ANY delays and any select waveform, even mid-rail or ringing),
  `unselected_glitch_free`, `sic_glitch_free` (any single-input change whose
  old and new outputs agree).
* Timed hazard (proved glitch trace): `data_first_glitch`. S rises and the
  deselected data pin I0 changes at the same pin instant. Then for EVERY
  admissible delay pair of F7AMUX, F7BMUX or F8MUX at EITHER corner, the output
  shows the wrong value on `[d0, dS)`, which is never empty because prjxray's select arc
  is always slower than its data arcs (`sel_slowest`, all six SLICEL/SLICEM muxes). The mirror case
  (`late_select_no_glitch`: the newly selected pin changes with S) never glitches
  at any admissible delays.
* MUXF8 tree (two MUXF7 under one MUXF8, as yosys maps an 8:1 mux, see shard C's
  `prims_muxf8`): `F8Timed.sound`, `F8Timed.sic_glitch_free`.

## Hypotheses (named; what would test them)

* **H_MUXF_PASS**: F7MUX/F8MUX are pass-transistor (or transmission-gate)
  muxes whose output is Kleene-sound at every instant: with a mid-rail select
  and equal data, the output stays at the data level. Not documented by Xilinx;
  a static-hazard GLS against silicon or a board experiment (toggle S with
  I0 = I1 = 1 at full rate, count output pulses with a ring counter) would test it.
* **H_PERPIN_TRANSPORT**: each arc is a pure transport delay, inside its
  prjxray band at the analysis corner, constant over the analysed interval.
  Pulse shrinking/swallowing (inertial or involution behaviour) is not modelled
  here; `Core/Delay/{Inertial,Involution}` have those channels.

## Not covered

Slews, charge sharing, metastable select dwell (any select waveform is allowed;
only the output's soundness is assumed), the routing into and out of the mux
(the routing-BEL arcs `a6lut -> f7amux` etc. are separate prjxray `ROUTING_BEL`
entries, 9-24 ps, `XrayData.f7Hop`; they add to the data arcs and are charged in
`Formal.Core.Prims.Hops`, not here).
-/

namespace Formal.Core.Prims

open Formal.Core K3

/-- `∀` over `K3` is decidable (for `decide` on Kleene statements). -/
instance decForallK3 {P : K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
  if h : P .zero ∧ P .one ∧ P .X then
    isTrue (fun k => by cases k <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _⟩)

/-! ## Static Kleene semantics -/

/-- The 2:1 pass-transistor mux: `S ? I1 : I0`, select `X` gives `merge I0 I1`. -/
def mux2 : K3 → K3 → K3 → K3
  | .zero, a, _ => a
  | .one, _, b => b
  | .X, a, b => merge a b

/-- Boolean mux. -/
def bmux (s a b : Bool) : Bool := if s then b else a

theorem mux2_ofBool (s a b : Bool) :
    mux2 (ofBool s) (ofBool a) (ofBool b) = ofBool (bmux s a b) := by
  cases s <;> cases a <;> cases b <;> rfl

theorem mux2_mono {s a b s' a' b' : K3} (hs : s ⊑ s') (ha : a ⊑ a') (hb : b ⊑ b') :
    mux2 s a b ⊑ mux2 s' a' b' := by
  revert hs ha hb
  cases s <;> cases a <;> cases b <;> cases s' <;> cases a' <;> cases b' <;> decide

theorem mux2_X_same (a : K3) : mux2 .X a a = a := by cases a <;> decide

/-- X containment: whatever Boolean values the pins resolve to, a defined
output is their Boolean mux. -/
theorem mux2_contain {s a b : K3} {s' a' b' : Bool} (hs : s ⊑ ofBool s')
    (ha : a ⊑ ofBool a') (hb : b ⊑ ofBool b') :
    mux2 s a b ⊑ ofBool (bmux s' a' b') :=
  mux2_ofBool s' a' b' ▸ mux2_mono hs ha hb

/-- `mux2` is the exact (most defined) Kleene extension of `bmux`: it is the
Boolean `c` iff every resolution of the pins gives `c`. -/
theorem mux2_exact : ∀ (s a b : K3) (c : Bool),
    mux2 s a b = ofBool c ↔
      ∀ s' a' b' : Bool, s ⊑ ofBool s' → a ⊑ ofBool a' → b ⊑ ofBool b' → bmux s' a' b' = c := by
  decide

/-! ## Pass-transistor versus AND-OR -/

/-- The gate-level AND-OR realisation of a 2:1 mux, `¬s·a + s·b`, in
strong-Kleene logic. NOT the slice's F7/F8 mux (H_MUXF_PASS); here to show what the
choice decides. -/
def aoMux (s a b : K3) : K3 := K3.or (K3.and (K3.not s) a) (K3.and s b)

theorem aoMux_ofBool (s a b : Bool) :
    aoMux (ofBool s) (ofBool a) (ofBool b) = ofBool (bmux s a b) := by
  cases s <;> cases a <;> cases b <;> rfl

/-- The AND-OR mux is never more defined than the pass-transistor mux. -/
theorem aoMux_le_mux2 : ∀ s a b : K3, aoMux s a b ⊑ mux2 s a b := by decide

/-- ...and strictly less defined exactly on a select in transit with equal
data `1`: the static-1 hazard of the AND-OR mux. (With equal data `0` both are `0`.) -/
theorem aoMux_hazard :
    aoMux .X .one .one = .X ∧ mux2 .X .one .one = .one ∧ aoMux .X .zero .zero = .zero ∧
    (∀ s a b : K3, aoMux s a b ≠ mux2 s a b ↔ (s = .X ∧ a = .one ∧ b = .one)) := by
  decide

/-! ## Timed model: per-pin transport arcs -/

/-- A 3-valued waveform over integer time (ps). (Plain `Int`, not an abbreviation:
`omega` does not see through one.) -/
abbrev Wave := Int → K3

/-- A timed slice mux: pin waveforms, the three arc delays, and the output. -/
structure MuxTimed where
  i0 : Wave
  i1 : Wave
  s : Wave
  d0 : Int
  d1 : Int
  dS : Int
  y : Wave

namespace MuxTimed

variable (M : MuxTimed)

/-- **H_MUXF_PASS + H_PERPIN_TRANSPORT**: at every instant the output is at least as
defined as the Kleene mux of the three pins, each delayed by its own arc. -/
def H : Prop :=
  ∀ τ, mux2 (M.s (τ - M.dS)) (M.i0 (τ - M.d0)) (M.i1 (τ - M.d1)) ⊑ M.y τ

/-- The exact instance: the output IS the Kleene mux of the delayed pins. -/
def exact (i0 i1 s : Wave) (d0 d1 dS : Int) : MuxTimed :=
  ⟨i0, i1, s, d0, d1, dS, fun τ => mux2 (s (τ - dS)) (i0 (τ - d0)) (i1 (τ - d1))⟩

theorem exact_H (i0 i1 s : Wave) (d0 d1 dS : Int) : (exact i0 i1 s d0 d1 dS).H :=
  fun _ => le_refl _

/-- A static `K3` value abstracts a waveform: the waveform is always at least as
defined (X = "may do anything, including dwell mid-rail or ring"). -/
def Abs (v : K3) (w : Wave) : Prop := ∀ τ, v ⊑ w τ

theorem abs_X (w : Wave) : Abs .X w := fun _ => X_le _

theorem abs_const (b : Bool) : Abs (ofBool b) (fun _ => ofBool b) := fun _ => le_refl _

/-- Soundness for ANY delays: every instant is at least as defined as the static
Kleene mux of the pins' abstractions. -/
theorem sound (h : M.H) {v0 v1 vs : K3} (h0 : Abs v0 M.i0) (h1 : Abs v1 M.i1)
    (hs : Abs vs M.s) (τ : Int) : mux2 vs v0 v1 ⊑ M.y τ :=
  le_trans (mux2_mono (hs _) (h0 _) (h1 _)) (h τ)

/-- A defined static value forces the output, at every instant. -/
theorem forced (h : M.H) {v0 v1 vs : K3} (h0 : Abs v0 M.i0) (h1 : Abs v1 M.i1)
    (hs : Abs vs M.s) {c : Bool} (hc : mux2 vs v0 v1 = ofBool c) (τ : Int) :
    M.y τ = ofBool c := by
  have := M.sound h h0 h1 hs τ
  rw [hc] at this
  exact ofBool_le_iff.mp this

/-- **Select change, equal data: no glitch, for any delays.** The select may do
anything (switch either way, dwell mid-rail, ring); `I0 = I1 = c` throughout. -/
theorem sel_change_glitch_free (h : M.H) (c : Bool) (h0 : ∀ τ, M.i0 τ = ofBool c)
    (h1 : ∀ τ, M.i1 τ = ofBool c) (τ : Int) : M.y τ = ofBool c :=
  M.forced h (v0 := ofBool c) (v1 := ofBool c) (vs := .X)
    (fun τ => by rw [h0]; exact le_refl _) (fun τ => by rw [h1]; exact le_refl _)
    (abs_X _) (by cases c <;> rfl) τ

/-- The deselected data pin may do anything: the output follows nothing but the
selected one. -/
theorem unselected_glitch_free (h : M.H) (c : Bool) (hs : ∀ τ, M.s τ = .zero)
    (h0 : ∀ τ, M.i0 τ = ofBool c) (τ : Int) : M.y τ = ofBool c :=
  M.forced h (v0 := ofBool c) (v1 := .X) (vs := .zero)
    (fun τ => by rw [h0]; exact le_refl _) (abs_X _)
    (fun τ => by rw [hs]; exact le_refl _) rfl τ

/-- `K3` abstraction of a single-input change `old → new` of one pin. -/
def hull (a b : Bool) : K3 := if a = b then ofBool a else .X

theorem abs_hull {a b : Bool} {w : Wave} (_hw : ∀ τ, w τ = ofBool a ∨ w τ = ofBool b ∨ w τ = .X)
    (hab : a = b → ∀ τ, w τ = ofBool a) : Abs (hull a b) w := by
  intro τ
  unfold hull
  split
  · rename_i e; rw [hab e τ]; exact le_refl _
  · exact X_le _

/-- No function hazard in a single-input change of a 2:1 mux: if at most one pin
differs between `old` and `new` and the outputs agree, the hull is defined. -/
theorem mux2_sic : ∀ s a b s' a' b' : Bool,
    ((s = s' ∧ a = a') ∨ (s = s' ∧ b = b') ∨ (a = a' ∧ b = b')) →
    bmux s a b = bmux s' a' b' →
    mux2 (hull s s') (hull a a') (hull b b') = ofBool (bmux s a b) := by
  decide

/-- **Single-input-change glitch freedom, any delays.** Steady pins hold
their value, the changing pin may do anything in between (any edge shape, mid-rail,
ringing). If old and new outputs agree, the output never leaves that value. -/
theorem sic_glitch_free (h : M.H) (s a b s' a' b' : Bool)
    (hone : (s = s' ∧ a = a') ∨ (s = s' ∧ b = b') ∨ (a = a' ∧ b = b'))
    (hsame : bmux s a b = bmux s' a' b')
    (hS : Abs (hull s s') M.s) (h0 : Abs (hull a a') M.i0) (h1 : Abs (hull b b') M.i1)
    (τ : Int) : M.y τ = ofBool (bmux s a b) :=
  M.forced h h0 h1 hS (mux2_sic s a b s' a' b' hone hsame) τ

end MuxTimed

/-! ## The hazard: data first -/

/-- A pin that steps from `a` to `b` at pin time `t`. -/
def step (a b : Bool) (t : Int) : Wave := fun τ => if τ < t then ofBool a else ofBool b

/-- **Proved glitch trace.** I1 holds `v`; S rises (deselecting I0) and I0 changes
`v → ¬v`, both at pin time 0. Old and new outputs are both `v`, but the static
abstraction (S = X, I0 = X) is `X`, and in the exact per-pin transport model the
output shows `¬v` on the whole interval `[d0, dS)`. -/
theorem data_first_glitch (v : Bool) (d0 d1 dS : Int) (h : d0 < dS) :
    let M := MuxTimed.exact (step v (!v) 0) (fun _ => ofBool v) (step false true 0) d0 d1 dS
    mux2 .X .X (ofBool v) = .X ∧
    (∀ τ, τ < d0 → M.y τ = ofBool v) ∧
    (∀ τ, d0 ≤ τ → τ < dS → M.y τ = ofBool (!v)) ∧
    (∀ τ, max d0 dS ≤ τ → M.y τ = ofBool v) := by
  refine ⟨by cases v <;> rfl, ?_, ?_, ?_⟩
  · intro τ hτ
    have e1 : τ - d0 < 0 := by omega
    by_cases e2 : τ - dS < 0
    · simp [MuxTimed.exact, step, e1, e2, mux2]
    · simp [MuxTimed.exact, step, e1, e2, mux2]
  · intro τ h1 h2
    have e1 : ¬ τ - d0 < 0 := by omega
    have e2 : τ - dS < 0 := by omega
    simp [MuxTimed.exact, step, e1, e2, mux2]
  · intro τ hτ
    have e2 : ¬ τ - dS < 0 := by omega
    simp [MuxTimed.exact, step, e2, mux2]

/-- In every slice mux (F7AMUX, F7BMUX, F8MUX of SLICEL and SLICEM), at both
corners, the select arc is the slowest: its minimum exceeds both data arcs' maxima. -/
theorem sel_slowest (st : SiteType) (fm : FMux) (c : Corner) :
    (selmux st fm).i0.hi c < (selmux st fm).s.lo c ∧
    (selmux st fm).i1.hi c < (selmux st fm).s.lo c := by
  cases st <;> cases fm <;> cases c <;> decide

/-- Every generated mux band is well formed. -/
theorem selmux_ok : ∀ st fm, ((selmux st fm).i0.ok && (selmux st fm).i1.ok &&
    (selmux st fm).s.ok) = true := by
  intro st fm; cases st <;> cases fm <;> decide

/-- With prjxray's arcs this glitch is unavoidable: for every slice mux, at
either corner, EVERY admissible pair `(d0, dS)` has `d0 < dS`, so the glitch of
`data_first_glitch` is at least `S.lo - I0.hi` wide. -/
theorem data_first_glitch_xray (st : SiteType) (fm : FMux) (c : Corner) (d0 dS : Int)
    (h0 : (selmux st fm).i0.In c d0) (hS : (selmux st fm).s.In c dS) :
    (selmux st fm).s.lo c - (selmux st fm).i0.hi c ≤ dS - d0 ∧ 0 < dS - d0 := by
  have := (sel_slowest st fm c).1
  obtain ⟨_, h0'⟩ := h0
  obtain ⟨hS', _⟩ := hS
  omega

/-- The guaranteed glitch widths (`S.lo - I0.hi`), ps: SLICEL F7AMUX 18 fast / 32 slow;
the smallest over all six muxes is 16 (fast; SLICEL and SLICEM F7BMUX) and 22 (slow;
SLICEL F7BMUX). (The mirror case, S falling while I1 changes, has `S.lo - I1.hi`,
as small as 12 fast / 16 slow on SLICEL F7BMUX; not stated as a theorem here.) -/
theorem glitch_width_table :
    (selmux .slicel .f7a).s.lo .fast - (selmux .slicel .f7a).i0.hi .fast = 18 ∧
    (selmux .slicel .f7a).s.lo .slow - (selmux .slicel .f7a).i0.hi .slow = 32 ∧
    (∀ st fm, 16 ≤ (selmux st fm).s.lo .fast - (selmux st fm).i0.hi .fast) ∧
    (∀ st fm, 22 ≤ (selmux st fm).s.lo .slow - (selmux st fm).i0.hi .slow) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> intro st fm <;> cases st <;> cases fm <;> decide

/-- The mirror case does not glitch at prjxray delays: S rises and the newly
selected pin I1 changes `¬v → v`, both at pin time 0, I0 holds `v`. Whenever
`d1 < dS` (true for every admissible pair, `sel_slowest`), the output is `v`
throughout. -/
theorem late_select_no_glitch (v : Bool) (d0 d1 dS : Int) (h : d1 < dS) (τ : Int) :
    (MuxTimed.exact (fun _ => ofBool v) (step (!v) v 0) (step false true 0) d0 d1 dS).y τ =
      ofBool v := by
  by_cases e2 : τ - dS < 0
  · simp [MuxTimed.exact, step, e2, mux2]
  · have e1 : ¬ τ - d1 < 0 := by omega
    simp [MuxTimed.exact, step, e1, e2, mux2]

/-! ## The MUXF8 tree: two MUXF7 under one MUXF8 -/

/-- Static Kleene value of `F8(s8; F7(s7a; a, b), F7(s7b; c, d))`. -/
def mux4K (s8 s7a s7b a b c d : K3) : K3 := mux2 s8 (mux2 s7a a b) (mux2 s7b c d)

/-- Boolean 8:1-style reference. -/
def bmux4 (s8 s7a s7b a b c d : Bool) : Bool := bmux s8 (bmux s7a a b) (bmux s7b c d)

/-- A timed F8 tree: three timed muxes, the F7 outputs wired to the F8 data pins
(the in-slice F7->F8 wire is part of the F8 data arc in prjxray). -/
structure F8Timed where
  ma : MuxTimed
  mb : MuxTimed
  m8 : MuxTimed
  wa : ∀ τ, m8.i0 τ = ma.y τ
  wb : ∀ τ, m8.i1 τ = mb.y τ

namespace F8Timed

open MuxTimed

/-- Soundness of the tree for any delays of the three muxes. -/
theorem sound (F : F8Timed) (ha : F.ma.H) (hb : F.mb.H) (h8 : F.m8.H)
    {vs8 vsa vsb va vb vc vd : K3}
    (hs8 : Abs vs8 F.m8.s) (hsa : Abs vsa F.ma.s) (hsb : Abs vsb F.mb.s)
    (hA : Abs va F.ma.i0) (hB : Abs vb F.ma.i1) (hC : Abs vc F.mb.i0) (hD : Abs vd F.mb.i1)
    (τ : Int) : mux4K vs8 vsa vsb va vb vc vd ⊑ F.m8.y τ := by
  have h0 : Abs (mux2 vsa va vb) F.m8.i0 := fun τ => by
    rw [F.wa]; exact F.ma.sound ha hA hB hsa τ
  have h1 : Abs (mux2 vsb vc vd) F.m8.i1 := fun τ => by
    rw [F.wb]; exact F.mb.sound hb hC hD hsb τ
  exact F.m8.sound h8 h0 h1 hs8 τ

/-- Number of pins on which two Boolean 7-tuples differ. -/
def ndiff7 (x y : Bool × Bool × Bool × Bool × Bool × Bool × Bool) : Nat :=
  let (a1, a2, a3, a4, a5, a6, a7) := x
  let (b1, b2, b3, b4, b5, b6, b7) := y
  (if a1 = b1 then 0 else 1) + (if a2 = b2 then 0 else 1) + (if a3 = b3 then 0 else 1) +
  (if a4 = b4 then 0 else 1) + (if a5 = b5 then 0 else 1) + (if a6 = b6 then 0 else 1) +
  (if a7 = b7 then 0 else 1)

/-- No function hazard on any single-input change of the F8 tree (all 128 × 7
cases): the mux tree is read-once, so its pin-wise Kleene value is exact. -/
theorem mux4K_sic : ∀ s8 sa sb a b c d s8' sa' sb' a' b' c' d' : Bool,
    ndiff7 (s8, sa, sb, a, b, c, d) (s8', sa', sb', a', b', c', d') ≤ 1 →
    bmux4 s8 sa sb a b c d = bmux4 s8' sa' sb' a' b' c' d' →
    mux4K (hull s8 s8') (hull sa sa') (hull sb sb') (hull a a') (hull b b') (hull c c')
      (hull d d') = ofBool (bmux4 s8 sa sb a b c d) := by
  decide

/-- **SIC glitch freedom of the MUXF8 tree, any delays.** -/
theorem sic_glitch_free (F : F8Timed) (ha : F.ma.H) (hb : F.mb.H) (h8 : F.m8.H)
    (s8 sa sb a b c d s8' sa' sb' a' b' c' d' : Bool)
    (hone : ndiff7 (s8, sa, sb, a, b, c, d) (s8', sa', sb', a', b', c', d') ≤ 1)
    (hsame : bmux4 s8 sa sb a b c d = bmux4 s8' sa' sb' a' b' c' d')
    (hs8 : Abs (hull s8 s8') F.m8.s) (hsa : Abs (hull sa sa') F.ma.s)
    (hsb : Abs (hull sb sb') F.mb.s)
    (hA : Abs (hull a a') F.ma.i0) (hB : Abs (hull b b') F.ma.i1)
    (hC : Abs (hull c c') F.mb.i0) (hD : Abs (hull d d') F.mb.i1) (τ : Int) :
    F.m8.y τ = ofBool (bmux4 s8 sa sb a b c d) := by
  have := F.sound ha hb h8 hs8 hsa hsb hA hB hC hD τ
  rw [mux4K_sic s8 sa sb a b c d s8' sa' sb' a' b' c' d' hone hsame] at this
  exact ofBool_le_iff.mp this

end F8Timed

end Formal.Core.Prims
