import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-!
# Bounded pure (transport) delay channel, continuous time

Probe A / track 3 / channel (a).  Self-contained: the signal type is the
minimal `ℝ → Bool`; nothing here depends on the final trace representation.

## The model

A channel with delay bounds `[lo, hi]` relates input `x` to output `y` iff
there is a *read-time map* `σ : ℝ → ℝ` such that

* `y s = x (σ s)` for every output time `s`  (the output at `s` shows the
  input as it was at time `σ s`),
* `s - hi ≤ σ s ≤ s - lo`                   (the age of what is shown is in
  `[lo, hi]`),
* `σ` is nondecreasing                       (**FIFO**: the output never shows
  an older input after a newer one, so transitions cannot overtake).

An input transition at time `t` appears at the output where `σ` crosses `t`,
so with a delay in `[lo, hi]`.  When `σ` jumps over an input interval the
input's behaviour inside it is never shown: two transitions that "would
cross" annihilate instead (pulse collapse).  This is the FIFO choice; the
non-FIFO alternative (each transition delayed independently, the output
defined by parity of arrived transitions) would turn a collapsed pulse into an
inverted one, which a buffered CMOS wire cannot do.  See
`formal/notes/A-delay-pure.md`.

All results are for arbitrary real bounds; where a result needs `lo ≤ hi`
it says so as an explicit hypothesis.
-/
namespace Formal.Core.DelayPure

/-- A binary signal in continuous time. -/
abbrev Sig := ℝ → Bool

/-- A read-time map for a FIFO channel with delay bounds `[lo, hi]`. -/
structure Retime (lo hi : ℝ) where
  σ : ℝ → ℝ
  mono : ∀ a b, a ≤ b → σ a ≤ σ b
  ge : ∀ s, s - hi ≤ σ s
  le : ∀ s, σ s ≤ s - lo

/-- The bounded pure-delay (transport) channel, FIFO, as a relation. -/
def Chan (lo hi : ℝ) (x y : Sig) : Prop :=
  ∃ r : Retime lo hi, ∀ s, y s = x (r.σ s)

/-! ## Basic structure -/

/-- Fixed shift by `d ∈ [lo, hi]` is a valid retiming. -/
def Retime.shift (lo hi d : ℝ) (h1 : lo ≤ d) (h2 : d ≤ hi) : Retime lo hi where
  σ s := s - d
  mono a b h := by linarith
  ge s := by linarith
  le s := by linarith

/-- Any fixed delay inside the band is a behaviour of the channel. -/
theorem chan_shift {lo hi d : ℝ} (h1 : lo ≤ d) (h2 : d ≤ hi) (x : Sig) :
    Chan lo hi x (fun s => x (s - d)) :=
  ⟨Retime.shift lo hi d h1 h2, fun _ => rfl⟩

/-- The channel has some behaviour for every input iff `lo ≤ hi`
(nonempty band). -/
theorem chan_total_iff {lo hi : ℝ} :
    (∀ x : Sig, ∃ y, Chan lo hi x y) ↔ lo ≤ hi := by
  constructor
  · intro h
    obtain ⟨_, r, _⟩ := h (fun _ => false)
    have := r.ge 0; have := r.le 0; linarith
  · intro h x; exact ⟨_, chan_shift (le_refl lo) h x⟩

/-- Fixed delay is the special case `lo = hi`: then the channel is the
function `y s = x (s - d)`. -/
theorem chan_fixed_iff {d : ℝ} {x y : Sig} :
    Chan d d x y ↔ ∀ s, y s = x (s - d) := by
  constructor
  · rintro ⟨r, hr⟩ s
    have h1 := r.ge s; have h2 := r.le s
    rw [hr s]; congr 1; linarith
  · intro h
    refine ⟨Retime.shift d d d le_rfl le_rfl, fun s => ?_⟩
    exact h s

/-- Monotonicity in the bounds: widening the band only adds behaviours. -/
theorem chan_mono {lo hi lo' hi' : ℝ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    {x y : Sig} (h : Chan lo hi x y) : Chan lo' hi' x y := by
  obtain ⟨r, hr⟩ := h
  exact ⟨⟨r.σ, r.mono, fun s => by have := r.ge s; linarith,
    fun s => by have := r.le s; linarith⟩, hr⟩

/-! ## Series composition -/

/-- Series composition: `[lo1,hi1] ; [lo2,hi2] ⊆ [lo1+lo2, hi1+hi2]`. -/
theorem chan_comp {lo1 hi1 lo2 hi2 : ℝ} {x y z : Sig}
    (h1 : Chan lo1 hi1 x y) (h2 : Chan lo2 hi2 y z) :
    Chan (lo1 + lo2) (hi1 + hi2) x z := by
  obtain ⟨r1, e1⟩ := h1
  obtain ⟨r2, e2⟩ := h2
  refine ⟨⟨fun s => r1.σ (r2.σ s), fun a b h => r1.mono _ _ (r2.mono a b h),
    fun s => ?_, fun s => ?_⟩, fun s => by simp [e2 s, e1 (r2.σ s)]⟩
  · have := r1.ge (r2.σ s); have := r2.ge s; linarith
  · have := r1.le (r2.σ s); have := r2.le s; linarith

/-- The converse: every behaviour of `[lo1+lo2, hi1+hi2]` factors through
an intermediate signal as `[lo1,hi1] ; [lo2,hi2]` (needs both bands
nonempty).  The split is
`σ2 s = max (s - hi2) (σ s + lo1)`,
`σ1 u = max (u - hi1) (min (u - lo1) (σ (u + hi2)))`. -/
theorem chan_decomp {lo1 hi1 lo2 hi2 : ℝ} (hb1 : lo1 ≤ hi1) (hb2 : lo2 ≤ hi2)
    {x z : Sig} (h : Chan (lo1 + lo2) (hi1 + hi2) x z) :
    ∃ y, Chan lo1 hi1 x y ∧ Chan lo2 hi2 y z := by
  obtain ⟨r, e⟩ := h
  let σ2 : ℝ → ℝ := fun s => max (s - hi2) (r.σ s + lo1)
  let σ1 : ℝ → ℝ := fun u => max (u - hi1) (min (u - lo1) (r.σ (u + hi2)))
  have key : ∀ s, σ1 (σ2 s) = r.σ s := by
    intro s
    have g := r.ge s; have l := r.le s
    simp only [σ1, σ2]
    rcases le_total (s - hi2) (r.σ s + lo1) with hc | hc
    · rw [max_eq_right hc]
      have hm : r.σ s ≤ r.σ (r.σ s + lo1 + hi2) := r.mono _ _ (by linarith)
      rw [show r.σ s + lo1 - lo1 = r.σ s by linarith, min_eq_left hm]
      exact max_eq_right (by linarith)
    · rw [max_eq_left hc, show s - hi2 + hi2 = s by linarith]
      rw [min_eq_right (by linarith)]
      exact max_eq_right (by linarith)
  let r1 : Retime lo1 hi1 :=
    { σ := σ1
      mono := fun a b hab => by
        simp only [σ1]
        have := r.mono (a + hi2) (b + hi2) (by linarith)
        apply max_le_max (by linarith)
        exact min_le_min (by linarith) this
      ge := fun u => le_max_left _ _
      le := fun u => max_le (by linarith) (min_le_left _ _) }
  let r2 : Retime lo2 hi2 :=
    { σ := σ2
      mono := fun a b hab => by
        simp only [σ2]
        exact max_le_max (by linarith) (by have := r.mono a b hab; linarith)
      ge := fun s => le_max_left _ _
      le := fun s => max_le (by linarith) (by have := r.le s; linarith) }
  refine ⟨fun u => x (σ1 u), ⟨r1, fun _ => rfl⟩, ⟨r2, fun s => ?_⟩⟩
  show z s = x (σ1 (σ2 s))
  rw [key, e s]

/-- Series composition is exact: the series of two bands is the sum band. -/
theorem chan_comp_iff {lo1 hi1 lo2 hi2 : ℝ} (hb1 : lo1 ≤ hi1) (hb2 : lo2 ≤ hi2)
    (x z : Sig) :
    (∃ y, Chan lo1 hi1 x y ∧ Chan lo2 hi2 y z) ↔
      Chan (lo1 + lo2) (hi1 + hi2) x z :=
  ⟨fun ⟨_, h1, h2⟩ => chan_comp h1 h2, chan_decomp hb1 hb2⟩

/-! ## Stability windows and transitions -/

/-- `x` holds value `v` on the closed interval `[a, b]`. -/
def StableOn (x : Sig) (a b : ℝ) (v : Bool) : Prop :=
  ∀ t, a ≤ t → t ≤ b → x t = v

/-- `x` holds value `v` from time `a` on. -/
def StableFrom (x : Sig) (a : ℝ) (v : Bool) : Prop :=
  ∀ t, a ≤ t → x t = v

/-- `x` holds value `v` strictly before time `a`. -/
def StableBefore (x : Sig) (a : ℝ) (v : Bool) : Prop :=
  ∀ t, t < a → x t = v

/-- A stable input window `[a, b]` gives a stable output window
`[a + hi, b + lo]` (it shrinks by `hi - lo`). -/
theorem stableOn_out {lo hi a b : ℝ} {v : Bool} {x y : Sig}
    (h : Chan lo hi x y) (hx : StableOn x a b v) :
    StableOn y (a + hi) (b + lo) v := by
  obtain ⟨r, e⟩ := h
  intro s h1 h2
  rw [e s]
  exact hx _ (by have := r.ge s; linarith) (by have := r.le s; linarith)

theorem stableFrom_out {lo hi a : ℝ} {v : Bool} {x y : Sig}
    (h : Chan lo hi x y) (hx : StableFrom x a v) : StableFrom y (a + hi) v := by
  obtain ⟨r, e⟩ := h
  intro s h1
  rw [e s]; exact hx _ (by have := r.ge s; linarith)

theorem stableBefore_out {lo hi a : ℝ} {v : Bool} {x y : Sig}
    (h : Chan lo hi x y) (hx : StableBefore x a v) :
    StableBefore y (a + lo) v := by
  obtain ⟨r, e⟩ := h
  intro s h1
  rw [e s]; exact hx _ (by have := r.le s; linarith)

/-- A single transition: input `b` before `t0` and `¬b` from `t0` on.  The
output still shows `b` before `t0 + lo`, shows `¬b` from `t0 + hi` on, and
(FIFO) changes exactly once: once it shows `¬b` it never goes back. -/
theorem step_out {lo hi t0 : ℝ} {b : Bool} {x y : Sig} (h : Chan lo hi x y)
    (hb : StableBefore x t0 b) (ha : StableFrom x t0 (!b)) :
    StableBefore y (t0 + lo) b ∧ StableFrom y (t0 + hi) (!b) ∧
      ∀ s s', s ≤ s' → y s = !b → y s' = !b := by
  refine ⟨stableBefore_out h hb, stableFrom_out h ha, ?_⟩
  obtain ⟨r, e⟩ := h
  intro s s' hss hs
  rw [e] at hs ⊢
  by_cases hlt : r.σ s < t0
  · rw [hb _ hlt] at hs; cases b <;> simp at hs
  · exact ha _ (le_trans (not_lt.mp hlt) (r.mono _ _ hss))

/-! ## Pulses -/

/-- A positive pulse of width `w` starting at `0`: high on `[0, w)`. -/
noncomputable def pulse (w : ℝ) : Sig := fun t => if 0 ≤ t ∧ t < w then true else false

/-- Pulse-width upper bound: an output high time `s` reads the input inside
the pulse, so `s ∈ [lo, w + hi)`: the output is high only inside a window of
width `w + (hi - lo)`. -/
theorem pulse_out_support {lo hi w s : ℝ} {y : Sig} (h : Chan lo hi (pulse w) y)
    (hs : y s = true) : lo ≤ s ∧ s < w + hi := by
  obtain ⟨r, e⟩ := h
  rw [e s] at hs
  simp only [pulse] at hs
  split_ifs at hs with hc
  · have := r.ge s; have := r.le s; constructor <;> linarith [hc.1, hc.2]

/-- Pulse-width lower bound: the output is high on all of `[hi, w + lo)`;
this window is nonempty exactly when `w > hi - lo`. -/
theorem pulse_out_core {lo hi w s : ℝ} {y : Sig} (h : Chan lo hi (pulse w) y)
    (h1 : hi ≤ s) (h2 : s < w + lo) : y s = true := by
  obtain ⟨r, e⟩ := h
  rw [e s]
  have := r.ge s; have := r.le s
  simp only [pulse]
  rw [if_pos ⟨by linarith, by linarith⟩]

/-- A pulse wider than `hi - lo` always survives (the output is high at
time `hi`). -/
theorem pulse_survives {lo hi w : ℝ} (hw : hi - lo < w) {y : Sig}
    (h : Chan lo hi (pulse w) y) : y hi = true :=
  pulse_out_core h le_rfl (by linarith)

/-- **Pulse collapse.** A pulse no wider than `hi - lo` may vanish entirely:
the constant-low output is a behaviour of the channel.  Witness: read
`s - hi` before time `hi` (still before the pulse) and `s - lo` from `hi` on
(already after it): the leading edge is delayed by `hi`, the trailing edge
by `lo`, and they annihilate. -/
theorem pulse_can_vanish {lo hi w : ℝ} (hlh : lo ≤ hi) (hw : w ≤ hi - lo) :
    Chan lo hi (pulse w) (fun _ => false) := by
  let r : Retime lo hi :=
    { σ := fun s => if s < hi then s - hi else s - lo
      mono := fun a b hab => by
        by_cases ha : a < hi
        · by_cases hb : b < hi
          · simp only [if_pos ha, if_pos hb]; linarith
          · simp only [if_pos ha, if_neg hb]; linarith
        · have hb : ¬ b < hi := fun hb => ha (lt_of_le_of_lt hab hb)
          simp only [if_neg ha, if_neg hb]; linarith
      ge := fun s => by split_ifs <;> linarith
      le := fun s => by split_ifs <;> linarith }
  refine ⟨r, fun s => ?_⟩
  show false = pulse w (if s < hi then s - hi else s - lo)
  simp only [pulse]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith [h2.1, h2.2])

/-- The same pulse may also pass unchanged (fixed delay `lo`): the channel is
genuinely nondeterministic on pulses of width `≤ hi - lo`. -/
theorem pulse_can_pass {lo hi w : ℝ} (hlh : lo ≤ hi) :
    Chan lo hi (pulse w) (fun s => pulse w (s - lo)) :=
  chan_shift le_rfl hlh _

/-- Exact dichotomy for the pulse `[0, w)` with `0 < w`: it can vanish iff
`w ≤ hi - lo`. -/
theorem pulse_vanish_iff {lo hi w : ℝ} (hlh : lo ≤ hi) :
    Chan lo hi (pulse w) (fun _ => false) ↔ w ≤ hi - lo := by
  constructor
  · intro h
    by_contra hc
    have := pulse_survives (not_le.mp hc) h
    simp at this
  · exact pulse_can_vanish hlh

/-! ## Bundled-data condition: the request arrives after the data -/

/-- The request input changes away from `b` at launch time `t0`
(`StableBefore reqIn t0 b`).  Any output time at which the request channel
already shows the change is at least `t0 + lo`. -/
theorem req_arrival_lb {lo hi t0 s : ℝ} {b : Bool} {reqIn reqOut : Sig}
    (h : Chan lo hi reqIn reqOut) (hb : StableBefore reqIn t0 b)
    (hs : reqOut s ≠ b) : t0 + lo ≤ s := by
  by_contra hc
  exact hs (stableBefore_out h hb s (not_le.mp hc))

/-- **Request arrives after data (generic form).**  Data at the receiver
holds value `v` on `[t0 + td, t1]` (it settles at most `td` after the
request launch `t0`, and is held until `t1`).  The request travels through a
pure-delay channel with lower bound `lo`.  If `td ≤ lo`, then at every time
`s ≤ t1` at which the receiver sees the request, the data is stable at `v`. -/
theorem bundle_req_after_data {lo hi t0 td t1 s : ℝ} {b v : Bool}
    {data reqIn reqOut : Sig}
    (hdata : StableOn data (t0 + td) t1 v) (hreq : Chan lo hi reqIn reqOut)
    (hb : StableBefore reqIn t0 b) (hbundle : td ≤ lo)
    (hs : reqOut s ≠ b) (hs1 : s ≤ t1) : data s = v :=
  hdata s (by have := req_arrival_lb hreq hb hs; linarith) hs1

/-- Same, data held forever after settling. -/
theorem bundle_req_after_data' {lo hi t0 td s : ℝ} {b v : Bool}
    {data reqIn reqOut : Sig}
    (hdata : StableFrom data (t0 + td) v) (hreq : Chan lo hi reqIn reqOut)
    (hb : StableBefore reqIn t0 b) (hbundle : td ≤ lo)
    (hs : reqOut s ≠ b) : data s = v :=
  hdata s (by have := req_arrival_lb hreq hb hs; linarith)

/-- Composed form: data source stable on `[t0 + ts, t1]`, data wire a
pure-delay channel `[loD, hiD]`, request wire `[loR, hiR]`.  Condition
`ts + hiD ≤ loR` (data slow corner before request fast corner); the data is
stable at the receiver whenever the request has arrived, up to `t1 + loD`. -/
theorem bundle_two_wires {loD hiD loR hiR t0 ts t1 s : ℝ} {b v : Bool}
    {src data reqIn reqOut : Sig}
    (hsrc : StableOn src (t0 + ts) t1 v) (hD : Chan loD hiD src data)
    (hR : Chan loR hiR reqIn reqOut) (hb : StableBefore reqIn t0 b)
    (hbundle : ts + loD ≤ loR) (hs : reqOut s ≠ b) (hs1 : s ≤ t1 + loD) :
    data s = v := by
  have hd := stableOn_out hD hsrc
  rw [show t0 + ts + hiD = t0 + (ts + hiD) by linarith] at hd
  exact bundle_req_after_data hd hR hb hbundle hs hs1

/-- Tightness: the request can arrive as early as `t0 + lo` (and no
earlier), so `td ≤ lo` cannot be weakened using the channel bound alone. -/
theorem req_can_arrive_at_lo {lo hi t0 : ℝ} (hlh : lo ≤ hi) {b : Bool}
    {reqIn : Sig} (ha : StableFrom reqIn t0 (!b)) :
    ∃ reqOut, Chan lo hi reqIn reqOut ∧ reqOut (t0 + lo) = !b :=
  ⟨_, chan_shift le_rfl hlh reqIn, ha _ (by linarith)⟩

end Formal.Core.DelayPure
