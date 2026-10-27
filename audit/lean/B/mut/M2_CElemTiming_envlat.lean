import Formal.Cells.Prelim

/-!
# Track 5, probe 5b: timing of the feedback-LUT C-element under bounded delays

The cell is `bd_c2` of `cells/rtl/bd_ce.v`:

    LUT6 #(.INIT(64'h00E8_00E8_00E8_00E8)) u (
        .I0(a), .I1(b), .I2(q), .I3(rst), .I4(1'b0), .I5(1'b0), .O(q));

## Model (gate relations, discrete time)

Time is `Nat` ticks (1 tick = 1 ps is the intended unit; nothing depends on
it). A trace is `Nat → Bool`. Four nets are involved:

* `a`, `b`, `rst` : the input traces **as seen at the LUT pins** (input routing
  delay is part of these traces; it belongs to whoever drives them);
* `qp`  : the feedback trace as seen at pin `I2`;
* `O`   : the LUT output pin (what the rest of the design sees, before its own
  routing).

The loop is the conjunction of two gate relations (`Loop`):

1. `H_LUT`: `O` is a bounded-delay copy, delay in `[dlmin, dlmax]`, of the
   *excitation* `exc t = lutB INIT [a t, b t, qp t, rst t, 0, 0]` (the LUT's
   Boolean function of its current pin values, from the REAL INIT).
2. `H_FB`:  `qp` is a bounded-delay copy, delay in `[dwmin, dwmax]`, of `O`
   (the routed feedback wire `O -> I2`).

The delay channel `WinDelay dmin dmax x y` says: for each `t`, `y t` equals
`x s` for SOME `s` with `t - dmax ≤ s ≤ t - dmin`. This is bounded pure delay
with a delay that may vary from tick to tick (non-FIFO), i.e. the weakest
("most glitchy") bounded channel: it admits every fixed transport delay
`d ∈ [dmin, dmax]` (`transport_winDelay`) and also every reordering a varying
delay can produce. Positive results proved for `WinDelay` therefore hold for
every bounded pure/transport channel; the counter-example is built with a
FIXED transport delay, so it is a legal behaviour of every channel in this
family (and of the window channel in particular).

Inertial delay is NOT a refinement of `WinDelay` (an inertial channel can hold
an arbitrarily old value while its input chatters), so the positive theorems
are not claimed for it. Section 5 proves the one inertial fact we need for
the verdict: an input runt shorter than the inertial threshold of the LUT
never reaches `O` (the event is LOST instead of oscillating).

## Results

* `held_of_forced` (generic, any INIT): if the excitation is *forced* to `v`
  (independent of the feedback value) during `[t0, t0 + dlmax + dwmax)` and `v`
  is a *fixed point* (`exc` with `qp = v` gives `v`) on `[t0, t2]`, then the
  excitation is `v` on all of `[t0, t2]`, `O = v` on `[t0+dlmax, t2+dlmin]`,
  `qp = v` on `[t0+dlmax+dwmax, t2+dlmin+dwmin]`. No assumption on the state
  before `t0` (works from an arbitrary power-up value).
* (a) `c2_follow_hold`: for bd_c2, if `rst = 0`, `a = b = v` for at least the
  loop delay bound `Dmax = dlmax + dwmax` ticks, and afterwards the inputs
  never both go to `!v`, the cell settles to `v` and holds.
  `c2_reset`: `rst = 1` for `Dmax` ticks clears the cell, and it holds 0 after
  release while `a, b` are not both 1.
* (b) `runt_oscillates`: a CONCRETE family of traces (any `dl, dw ≥ 0` with
  `D = dl + dw`, any pulse width `0 < w < D`) satisfying all gate relations
  with fixed transport delays: `a = 1` constant, `b` a pulse of width `w`,
  `rst = 0`; after the pulse the inputs are constant forever, yet `qp` (and
  `O`) oscillate forever with period `D` and high time `w`. So the bound `Dmax`
  in (a) is EXACT (tight for every fixed delay).
* (c) `c2_four_phase`: under the four-phase discipline stated as named
  hypotheses (phase `k` starts at `c k` when both inputs reach the target
  `V k`, targets alternate, until the next phase at least one input keeps
  `V k`, and an input leaves `V k` only `E` ticks after the environment saw
  `O = V k`), with the derived timing condition
  `H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E`, `O` equals the C-element state
  `V k` on `[c k + dlmax, c (k+1) - 1 + dlmin]` for every `k` (`qp` likewise):
  the cell implements the C-element trace spec, each output transition
  confined to a window of `dlmax - dlmin` ticks after its enabling instant.
  The minimum-pulse-width condition of (a) is DERIVED here from the
  environment latency, by induction over phases.
* (inertial) `inertial_runt_lost` (generic channel) and
  `c2_inertial_runt_lost` (the closed loop, inertial LUT + transport wire): an
  input runt shorter than the LUT's inertial threshold never changes `O`: the
  event is lost instead of oscillating.

Core Lean only. Proofs: `omega`, strong induction, `decide` on 16-row tables.
-/

namespace Formal.Cells.CElemTiming
open Formal.Cells

/-! ## 0. Traces, channels, the cell -/

abbrev Trace := Nat → Bool

/-- **Bounded pure delay, varying delay (window channel).** `y t = x s` for some
`s ∈ [t - dmax, t - dmin]`, for every `t ≥ dmax` (before `dmax` the output is
the unconstrained power-up value). -/
def WinDelay (dmin dmax : Nat) (x y : Trace) : Prop :=
  ∀ t, dmax ≤ t → ∃ s, t ≤ s + dmax ∧ s + dmin ≤ t ∧ y t = x s

/-- **Fixed transport delay** `d`: `y (t + d) = x t`; `y` on `[0, d)` is free. -/
def Transport (d : Nat) (x y : Trace) : Prop := ∀ t, y (t + d) = x t

/-- Every fixed transport delay inside the interval is a window-channel behaviour. -/
theorem transport_winDelay {dmin d dmax : Nat} {x y : Trace}
    (h1 : dmin ≤ d) (h2 : d ≤ dmax) (h : Transport d x y) : WinDelay dmin dmax x y := by
  intro t ht
  refine ⟨t - d, by omega, by omega, ?_⟩
  have := h (t - d)
  rw [Nat.sub_add_cancel (by omega)] at this
  exact this

/-- Two window channels in series are a window channel with summed bounds
(LUT delay + feedback wire = loop delay). -/
theorem winDelay_comp {d1 D1 d2 D2 : Nat} {x y z : Trace}
    (h1 : WinDelay d1 D1 x y) (h2 : WinDelay d2 D2 y z) :
    WinDelay (d1 + d2) (D1 + D2) x z := by
  intro t ht
  obtain ⟨s1, hs1a, hs1b, e1⟩ := h2 t (by omega)
  obtain ⟨s2, hs2a, hs2b, e2⟩ := h1 s1 (by omega)
  exact ⟨s2, by omega, by omega, e1.trans e2⟩

/-- The LUT's Boolean function with the pin map of `bd_c2`-style cells:
`I0 = a, I1 = b, I2 = q (feedback), I3 = rst, I4 = I5 = 0`. Evaluated with
`Prelim.lutB` on the real INIT. -/
def exc (init : Nat) (a b q r : Bool) : Bool := lutB init [a, b, q, r, false, false]

/-- `bd_c2`, verbatim from `cells/rtl/bd_ce.v`. -/
def INIT_c2 : Nat := 0x00E800E800E800E8
/-- `bd_c2_set`, verbatim. -/
def INIT_c2_set : Nat := 0xFFE8FFE8FFE8FFE8
/-- `bd_c2n` (C(a, ~b)), verbatim. -/
def INIT_c2n : Nat := 0x00B200B200B200B2

/-- The INIT of `bd_c2` is `~rst · maj(a, b, q)` (proved, not assumed). -/
theorem c2_eq (a b q r : Bool) :
    exc INIT_c2 a b q r = (!r && ((a && b) || (a && q) || (b && q))) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- The INIT of `bd_c2_set` is `rst + maj(a, b, q)`. -/
theorem c2_set_eq (a b q r : Bool) :
    exc INIT_c2_set a b q r = (r || ((a && b) || (a && q) || (b && q))) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- The INIT of `bd_c2n` is `~rst · maj(a, ~b, q)`. -/
theorem c2n_eq (a b q r : Bool) :
    exc INIT_c2n a b q r = (!r && ((a && !b) || (a && q) || (!b && q))) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- **The gate relations of one feedback-LUT cell.** Every field is a named
hypothesis about the fabric. -/
structure Loop (init : Nat) (a b rst O qp : Trace) (dlmin dlmax dwmin dwmax : Nat) : Prop where
  /-- **H_LUT**: the LUT output `O` follows its Boolean function of the pin
  values with a propagation delay in `[dlmin, dlmax]` (prjxray-db LUT
  `I*->O` fast-min / slow-max for xc7z010; a per-tick-varying delay is
  allowed). Binary pins: no X, no runt-shrinking (that is the Kleene and
  involution refinements). Test: GLS of a lone LUT with SDF min/max corners;
  board ring oscillator through one LUT. -/
  H_LUT : WinDelay dlmin dlmax (fun t => exc init (a t) (b t) (qp t) (rst t)) O
  /-- **H_FB**: the routed feedback wire `O -> I2` delays by `[dwmin, dwmax]`
  (prjxray-db min/max of the pips and wires on the routed path, from the
  routed `.fasm`/SDF of the instance). Test: SDF `INTERCONNECT` of the net
  `q` in `cells/gls/`, scatter over >= 4 placer seeds. -/
  H_FB : WinDelay dwmin dwmax O qp
  /-- **H_LOOP_POS**: the loop has strictly positive minimum delay (a real
  LUT plus a real wire never respond in zero time). -/
  H_LOOP_POS : 0 < dlmin + dwmin

/-! ## 1. The generic settle-and-hold lemma (any INIT) -/

section generic
variable {init : Nat} {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- Excitation trace of the loop. -/
def excT (init : Nat) (a b rst qp : Trace) : Trace := fun t => exc init (a t) (b t) (qp t) (rst t)

/-- **Forced, then held.** If the inputs force the LUT to `v` regardless of the
feedback value for `Dmax = dlmax + dwmax` ticks from `t0`, and keep `v` a fixed
point up to `t2`, the excitation is `v` on `[t0, t2]`. No assumption on the
loop's state before `t0`. -/
theorem exc_held (L : Loop init a b rst O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : Nat)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, exc init (a s) (b s) q (rst s) = v)
    (hfix : ∀ s, t0 ≤ s → s ≤ t2 → exc init (a s) (b s) v (rst s) = v) :
    ∀ s, t0 ≤ s → s ≤ t2 → excT init a b rst qp s = v := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro hs0 hs2
    by_cases hlt : s < t0 + (dlmax + dwmax)
    · exact hforce s hs0 hlt (qp s)
    · obtain ⟨s1, h1a, h1b, e1⟩ := L.H_FB s (by omega)
      obtain ⟨s2, h2a, h2b, e2⟩ := L.H_LUT s1 (by omega)
      have hpos := L.H_LOOP_POS
      have hv : excT init a b rst qp s2 = v := ih s2 (by omega) (by omega) (by omega)
      have hq : qp s = v := by rw [e1, e2]; exact hv
      show exc init (a s) (b s) (qp s) (rst s) = v
      rw [hq]; exact hfix s hs0 hs2

/-- Corollary for the LUT output `O`. -/
theorem O_held (L : Loop init a b rst O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : Nat)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, exc init (a s) (b s) q (rst s) = v)
    (hfix : ∀ s, t0 ≤ s → s ≤ t2 → exc init (a s) (b s) v (rst s) = v) :
    ∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = v := by
  intro t h1 h2
  obtain ⟨s, ha, hb, e⟩ := L.H_LUT t (by omega)
  rw [e]; exact exc_held L v t0 t2 hforce hfix s (by omega) (by omega)

/-- Corollary for the feedback pin `qp`. -/
theorem qp_held (L : Loop init a b rst O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : Nat)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, exc init (a s) (b s) q (rst s) = v)
    (hfix : ∀ s, t0 ≤ s → s ≤ t2 → exc init (a s) (b s) v (rst s) = v) :
    ∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = v := by
  intro t h1 h2
  obtain ⟨s, ha, hb, e⟩ := L.H_FB t (by omega)
  rw [e]; exact O_held L v t0 t2 hforce hfix s (by omega) (by omega)

end generic

/-! ## 2. (a) bd_c2 follows and holds; reset -/

section c2
variable {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- **(a) Follow-and-hold for `bd_c2`.** Hypotheses, all on the input traces:
* `H_PULSE` (minimum pulse width): `a = b = v` and `rst = 0` on
  `[t0, t0 + Dmax)`, `Dmax = dlmax + dwmax`: the enabling input pair persists
  for at least the maximum loop delay;
* `H_NORST`: `rst = 0` on `[t0, t2]`;
* `H_NOT_BOTH`: on `[t0, t2]` at least one input equals `v` (the inputs never
  both move to `!v`: `C(a, b)` is `v` or "hold").
Then `O = v` on `[t0 + dlmax, t2 + dlmin]` and `qp = v` on
`[t0 + Dmax, t2 + Dmin]`. -/
theorem c2_follow_hold (L : Loop INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → a s = v ∧ b s = v ∧ rst s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → rst s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → a s = v ∨ b s = v) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = v) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = v) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc INIT_c2 (a s) (b s) q (rst s) = v := by
    intro s h1 h2 q
    obtain ⟨ha, hb, hr⟩ := H_PULSE s h1 h2
    rw [c2_eq, ha, hb, hr]; cases v <;> cases q <;> rfl
  have hfix : ∀ s, t0 ≤ s → s ≤ t2 → exc INIT_c2 (a s) (b s) v (rst s) = v := by
    intro s h1 h2
    rw [c2_eq, H_NORST s h1 h2]
    rcases H_NOT_BOTH s h1 h2 with h | h <;> rw [h] <;> cases v <;> cases a s <;> cases b s <;> rfl
  exact ⟨O_held L v t0 t2 hforce hfix, qp_held L v t0 t2 hforce hfix⟩

/-- **Reset of `bd_c2`.** `H_RST_PULSE`: `rst = 1` for `Dmax` ticks from `t0`
(from ANY power-up value of the loop); `H_RELEASE`: afterwards up to `t2`,
`rst` is free but `a, b` are never both 1. Then the cell reads 0 throughout. -/
theorem c2_reset (L : Loop INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax) (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → a s = false ∨ b s = false) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc INIT_c2 (a s) (b s) q (rst s) = false := by
    intro s h1 h2 q
    rw [c2_eq, H_RST_PULSE s h1 h2]; rfl
  have hfix : ∀ s, t0 ≤ s → s ≤ t2 → exc INIT_c2 (a s) (b s) false (rst s) = false := by
    intro s h1 h2
    rw [c2_eq]
    rcases H_RELEASE s h1 h2 with h | h <;> rw [h] <;> cases a s <;> cases b s <;> cases rst s <;> rfl
  exact ⟨O_held L false t0 t2 hforce hfix, qp_held L false t0 t2 hforce hfix⟩

end c2

/-! ## 3. (b) Runt pulse shorter than the loop delay: perpetual oscillation

Fixed transport delays `dl` (LUT) and `dw` (wire), `D = dl + dw`, pulse width
`0 < w < D`, pulse start `t0`. Traces, given in closed form:
* `a = 1`, `rst = 0`, `b = 1` exactly on `[t0, t0 + w)`;
* excitation `= 1` iff `t ≥ t0` and `(t - t0) mod D < w`;
* `O`  = excitation shifted by `dl`; `qp` = excitation shifted by `D`.
-/

section runt
variable (dl dw w t0 : Nat)

def aR : Trace := fun _ => true
def rstR : Trace := fun _ => false
def bR : Trace := fun t => decide (t0 ≤ t ∧ t < t0 + w)
def gR : Trace := fun t => decide (t0 ≤ t ∧ (t - t0) % (dl + dw) < w)
def OR : Trace := fun t => decide (t0 + dl ≤ t ∧ (t - dl - t0) % (dl + dw) < w)
def qpR : Trace := fun t => decide (t0 + (dl + dw) ≤ t ∧ (t - (dl + dw) - t0) % (dl + dw) < w)

/-- The closed-form excitation is what the LUT computes from the pins. -/
theorem gR_eq (hw : w < dl + dw) (t : Nat) :
    gR dl dw w t0 t = excT INIT_c2 aR (bR w t0) rstR (qpR dl dw w t0) t := by
  simp only [excT, c2_eq, aR, rstR, bR, gR, qpR]
  by_cases h1 : t < t0
  · have : ¬ (t0 + (dl + dw) ≤ t) := by omega
    simp [show ¬ t0 ≤ t by omega, this]
  · by_cases h2 : t < t0 + (dl + dw)
    · have hm : (t - t0) % (dl + dw) = t - t0 := Nat.mod_eq_of_lt (by omega)
      simp [hm, show t0 ≤ t by omega, show ¬ (t0 + (dl + dw) ≤ t) by omega]
      omega
    · have he : t - t0 = (t - (dl + dw) - t0) + (dl + dw) := by omega
      have hm : (t - t0) % (dl + dw) = (t - (dl + dw) - t0) % (dl + dw) := by
        rw [he, Nat.add_mod_right]
      simp [hm, show t0 ≤ t by omega, show t0 + (dl + dw) ≤ t by omega,
        show ¬ (t < t0 + w) by omega]

theorem runt_lut (hw : w < dl + dw) :
    Transport dl (excT INIT_c2 aR (bR w t0) rstR (qpR dl dw w t0)) (OR dl dw w t0) := by
  intro t
  rw [← gR_eq dl dw w t0 hw]
  simp only [OR, gR]
  have : t + dl - dl - t0 = t - t0 := by omega
  rw [this]
  simp only [show (t0 + dl ≤ t + dl) = (t0 ≤ t) from by simp]

theorem runt_wire : Transport dw (OR dl dw w t0) (qpR dl dw w t0) := by
  intro t
  simp only [OR, qpR]
  have h1 : t + dw - (dl + dw) - t0 = t - dl - t0 := by omega
  have h2 : (t0 + (dl + dw) ≤ t + dw) ↔ (t0 + dl ≤ t) := by omega
  rw [h1]; simp only [h2]

/-- **The runt traces satisfy every gate relation** of `bd_c2` (window channel
with `dlmin = dlmax = dl`, `dwmin = dwmax = dw`). -/
theorem runt_loop (hw : w < dl + dw) (hpos : 0 < dl + dw) :
    Loop INIT_c2 aR (bR w t0) rstR (OR dl dw w t0) (qpR dl dw w t0) dl dl dw dw :=
  { H_LUT := transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (runt_lut dl dw w t0 hw)
    H_FB := transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (runt_wire dl dw w t0)
    H_LOOP_POS := hpos }

/-- **(b) Misbehaviour.** After `t0 + w` the inputs are constant forever
(`a = 1`, `b = 0`, `rst = 0`: a C-element must hold), yet the feedback pin is 1
at `t0 + D (n+1)` and 0 at `t0 + D (n+1) + w` for EVERY `n`: it oscillates
forever with period `D`; `O` does the same shifted by `-dw`. -/
theorem runt_oscillates (hw0 : 0 < w) (hw : w < dl + dw) :
    (∀ t, t0 + w ≤ t → aR t = true ∧ bR w t0 t = false ∧ rstR t = false) ∧
    (∀ n, qpR dl dw w t0 (t0 + (dl + dw) * (n + 1)) = true ∧
          qpR dl dw w t0 (t0 + (dl + dw) * (n + 1) + w) = false) ∧
    (∀ n, OR dl dw w t0 (t0 + dl + (dl + dw) * n) = true ∧
          OR dl dw w t0 (t0 + dl + (dl + dw) * n + w) = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp [aR, bR, rstR]; omega
  · intro n
    have e1 : t0 + (dl + dw) * (n + 1) - (dl + dw) - t0 = (dl + dw) * n := by
      rw [Nat.mul_succ]; omega
    have e2 : t0 + (dl + dw) * (n + 1) + w - (dl + dw) - t0 = w + (dl + dw) * n := by
      rw [Nat.mul_succ]; omega
    have hm2 : (w + (dl + dw) * n) % (dl + dw) = w := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
    have hle : t0 + (dl + dw) ≤ t0 + (dl + dw) * (n + 1) := by
      rw [Nat.mul_succ]; omega
    refine ⟨?_, ?_⟩
    · simp only [qpR, e1, Nat.mul_mod_right]; simp [hle, hw0]
    · simp only [qpR, e2, hm2]; simp
  · intro n
    have e1 : t0 + dl + (dl + dw) * n - dl - t0 = (dl + dw) * n := by omega
    have e2 : t0 + dl + (dl + dw) * n + w - dl - t0 = w + (dl + dw) * n := by omega
    have hm2 : (w + (dl + dw) * n) % (dl + dw) = w := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
    refine ⟨?_, ?_⟩
    · simp only [OR, e1, Nat.mul_mod_right]; simp [hw0]
    · simp only [OR, e2, hm2]; simp

/-- A concrete instance: `dl = 120`, `dw = 300` ticks (ps: about one LUT plus a
short local route), runt `w = 200 < 420`. -/
example : qpR 120 300 200 1000 (1000 + 420 * 6) = true ∧
    qpR 120 300 200 1000 (1000 + 420 * 6 + 200) = false := by decide

end runt

/-! ## 4. (c) The four-phase discipline: bd_c2 implements the C-element

Phase `k` starts at `c k`, the instant both inputs have reached the phase's
target `V k`; targets alternate (`H_ALT`). The environment is a four-phase
handshake partner that reads `O` and reacts with latency at least `E`. -/

theorem winDelay_le {dmin dmax : Nat} {x y : Trace} (h : WinDelay dmin dmax x y) : dmin ≤ dmax := by
  obtain ⟨s, h1, h2, _⟩ := h dmax (Nat.le_refl _); omega

section fourphase
variable {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- **(c) Four-phase correctness of `bd_c2`.** Hypotheses (all on the
environment / input traces, except `L`):
* `H_ALT`: the targets alternate, `V (k+1) = !V k`.
* `H_ORDER`: `c` is strictly increasing.
* `H_BOTH`: at `c k` both inputs equal `V k` (definition of the phase start).
* `H_NEXT`: on `[c k, c (k+1))` at least one input still equals `V k`
  (`c (k+1)` is the FIRST instant both reach `V (k+1)`).
* `H_NORST`: `rst = 0` from `c 0` on.
* `H_ACK` (four-phase): from `c k` on, an input differs from `V k` at `s`
  only if the environment saw `O = V k` at some `u ∈ [c k, s - E]`.
* `H_ENV_LATENCY`: `Dmax ≤ dlmin + E`, i.e. `E ≥ dwmax + (dlmax - dlmin)`:
  the environment's ack-to-input latency exceeds the feedback wire's maximum
  delay plus the LUT's delay spread. This is an isochronic-fork-type
  condition (the fork `O -> environment` versus `O -> I2`).
* `H_RESET_DONE`: before phase 0 the cell was cleared: `O = !V 0` on
  `[c 0, c 0 + dlmin)` (`c2_reset` discharges it).
Conclusion: for every phase `k`, `O = V k` on `[c k + dlmax, c (k+1) - 1 + dlmin]`
and `qp = V k` on `[c k + Dmax, c (k+1) - 1 + Dmin]`; between these windows
lies only the transition window `(c k - 1 + dlmin, c k + dlmax)`. -/
theorem c2_four_phase (L : Loop INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax)
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, a (c k) = V k ∧ b (c k) = V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → a s = V k ∨ b s = V k)
    (H_NORST : ∀ s, c 0 ≤ s → rst s = false)
    (H_ACK : ∀ k s, c k ≤ s → (a s ≠ V k ∨ b s ≠ V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E + 1)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + dlmin → O u = !V 0) :
    ∀ k, (∀ t, c k + dlmax ≤ t → t + 1 ≤ c (k + 1) + dlmin → O t = V k) ∧
         (∀ t, c k + (dlmax + dwmax) ≤ t → t + 1 ≤ c (k + 1) + (dlmin + dwmin) → qp t = V k) := by
  have hdl := winDelay_le L.H_LUT
  have hmono : ∀ k j, k ≤ j → c k ≤ c j := by
    intro k j hkj
    induction j with
    | zero => have : k = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with h | h
      · have := ih (by omega); have := H_ORDER j; omega
      · have : k = j + 1 := by omega
        subst this; exact Nat.le_refl _
  -- R k: at the start of phase k, `O` still shows the previous value.
  -- From R k we get ARRIVE k, then the phase result, then R (k+1).
  have step : ∀ k, (∀ u, c k ≤ u → u < c k + dlmin → O u = !V k) →
      (∀ t, c k + dlmax ≤ t → t + 1 ≤ c (k + 1) + dlmin → O t = V k) ∧
      (∀ t, c k + (dlmax + dwmax) ≤ t → t + 1 ≤ c (k + 1) + (dlmin + dwmin) → qp t = V k) ∧
      c k + (dlmax + dwmax) ≤ c (k + 1) := by
    intro k R
    have arrive : ∀ s, c k ≤ s → s < c k + (dlmax + dwmax) → a s = V k ∧ b s = V k := by
      intro s h1 h2
      by_cases hd : a s ≠ V k ∨ b s ≠ V k
      · obtain ⟨u, hu1, hu2, hu3⟩ := H_ACK k s h1 hd
        have := R u hu1 (by omega)
        rw [hu3] at this; cases hv : V k <;> simp [hv] at this
      · simp only [ne_eq, not_or, Decidable.not_not] at hd; exact hd
    have hgap : c k + (dlmax + dwmax) ≤ c (k + 1) := by
      apply Classical.byContradiction; intro hlt
      have h1 := arrive (c (k + 1)) (Nat.le_of_lt (H_ORDER k)) (by omega)
      have h2 := H_BOTH (k + 1)
      rw [H_ALT k] at h2
      rw [h1.1] at h2; cases hv : V k <;> simp [hv] at h2
    have hnr : ∀ s, c k ≤ s → rst s = false := fun s hs => H_NORST s (by have := hmono 0 k (Nat.zero_le _); omega)
    have res := c2_follow_hold L (V k) (c k) (c (k + 1) - 1)
      (fun s h1 h2 => ⟨(arrive s h1 h2).1, (arrive s h1 h2).2, hnr s h1⟩)
      (fun s h1 _ => hnr s h1)
      (fun s h1 h2 => H_NEXT k s h1 (by have := H_ORDER k; omega))
    exact ⟨fun t h1 h2 => res.1 t h1 (by omega), fun t h1 h2 => res.2 t h1 (by omega), hgap⟩
  have R : ∀ k, ∀ u, c k ≤ u → u < c k + dlmin → O u = !V k := by
    intro k
    induction k with
    | zero => exact H_RESET_DONE
    | succ k ih =>
      intro u h1 h2
      have ⟨hO, _, hgap⟩ := step k ih
      rw [H_ALT k, Bool.not_not]
      exact hO u (by omega) (by omega)
  intro k
  have ⟨h1, h2, _⟩ := step k (R k)
  exact ⟨h1, h2⟩

end fourphase

/-! ## 5. Inertial LUT channel: a short runt is lost, not oscillating -/

/-- **Inertial delay `d`** (discrete, VHDL-style): the output takes the
input's value `x t` at `t + d` only if the input stayed equal to `x t` during
`[t, t + d)`; otherwise it holds. -/
def Inertial (d : Nat) (x y : Trace) : Prop :=
  ∀ t, y (t + d) = if (∀ k, k < d → x (t + k) = x t) then x t else y (t + d - 1)

/-- With an inertial channel of threshold `d`, if the input is `v` outside
a pulse `[t0, t0 + w)` with `w < d`, and the output was `v` on `[t0, t0+d)`,
then the output stays `v` forever after: the runt is swallowed. -/
theorem inertial_runt_lost {d w t0 : Nat} {x y : Trace} (v : Bool)
    (hw : w < d) (H : Inertial d x y)
    (hx : ∀ t, ¬ (t0 ≤ t ∧ t < t0 + w) → x t = v)
    (hy0 : ∀ t, t0 ≤ t → t < t0 + d → y t = v) :
    ∀ t, t0 ≤ t → y t = v := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hlt : t < t0 + d
    · exact hy0 t ht hlt
    · have e := H (t - d)
      rw [Nat.sub_add_cancel (by omega)] at e
      rw [e]
      split
      · next hc =>
        -- the input was constant for d ticks from t - d; a window of length
        -- d > w cannot lie inside the pulse, so that constant is v
        by_cases hin : t0 ≤ t - d ∧ t - d < t0 + w
        · -- the window reaches t0 + w, which is outside the pulse
          have h1 := hc (t0 + w - (t - d)) (by omega)
          rw [show t - d + (t0 + w - (t - d)) = t0 + w by omega] at h1
          rw [← h1]; exact hx _ (by omega)
        · exact hx _ hin
      · exact ih (t - 1) (by omega) (by omega)

/-- **bd_c2 with an inertial LUT** (threshold `dl`, transport feedback wire
`dw`): `a = 1`, `rst = 0`, `b` a runt of width `w < dl` at `t0`, the cell at 0
before (`O = 0` on `[0, t0 + dl)`, `qp = 0` on `[0, dw)`). Then `O` and `qp`
stay 0 forever: the event `a = b = 1` is LOST (no oscillation, but the
C-element never acknowledges; the handshake deadlocks or the environment
misreads). Contrast `runt_oscillates` under transport. -/
theorem c2_inertial_runt_lost {dl dw w t0 : Nat} {b O qp : Trace}
    (hw : w < dl)
    (Hb : ∀ t, b t = decide (t0 ≤ t ∧ t < t0 + w))
    (H_LUT_INERTIAL : Inertial dl (excT INIT_c2 aR b rstR qp) O)
    (H_FB : Transport dw O qp)
    (hO0 : ∀ t, t < t0 + dl → O t = false)
    (hq0 : ∀ t, t < dw → qp t = false) :
    ∀ t, O t = false ∧ qp t = false := by
  have hg : ∀ t, qp t = false → excT INIT_c2 aR b rstR qp t = b t := by
    intro t h; simp only [excT, c2_eq, aR, rstR, h]; cases b t <;> rfl
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    -- qp t is O (t - dw), an earlier-or-equal tick; handle O t first
    have hOt : O t = false := by
      by_cases hlt : t < t0 + dl
      · exact hO0 t hlt
      · have e := H_LUT_INERTIAL (t - dl)
        rw [Nat.sub_add_cancel (by omega)] at e
        rw [e]
        have hpast : ∀ s, s < t → excT INIT_c2 aR b rstR qp s = b s :=
          fun s hs => hg s (ih s hs).2
        split
        · next hc =>
          rw [hpast _ (by omega), Hb]
          by_cases hin : t0 ≤ t - dl ∧ t - dl < t0 + w
          · have h1 := hc (t0 + w - (t - dl)) (by omega)
            rw [show t - dl + (t0 + w - (t - dl)) = t0 + w by omega,
              hpast _ (by omega), hpast _ (by omega), Hb, Hb] at h1
            rw [← h1]; simp
          · simp only [decide_eq_false_iff_not]; exact hin
        · exact (ih (t - 1) (by omega)).1
    refine ⟨hOt, ?_⟩
    by_cases hlt : t < dw
    · exact hq0 t hlt
    · have e := H_FB (t - dw)
      rw [Nat.sub_add_cancel (by omega)] at e
      rw [e]
      by_cases h0 : dw = 0
      · subst h0; simpa using hOt
      · exact (ih (t - dw) (by omega)).1

end Formal.Cells.CElemTiming
