import Formal.Cells.LinkTimed
open Formal.Core.LutList

/-!
# Track 6, probe 6e: a timed N-stage `bd_pipe` (N = 2 in full)

Probe 6d (`LinkTimed`) proved one `bd_link` stage against a timed four-phase
environment whose request and acknowledge are CLEAN at the controller pins
(`H_REQ_*`, `H_ACK_*`). Its node, under 5b's non-FIFO window channel, may
glitch inside each transition window, so a downstream stage could not use it
as such an environment. This file closes that gap by route (a) of the 6d
notes:

* **FIFO channel** (`Ret`, `fifo_hold`). The ℕ-time version of shard A's
  `Core/Delay/Pure.lean` channel: the output at `t` shows the input at a
  read time `σ t ∈ [t - hi, t - lo]`, `σ` nondecreasing. A stretch on which
  the input is constant is mapped onto ONE stretch of the output, bounded by
  `fst σ a` (first instant reading at or after `a`).
* **The controller's excitation is clean** (`exc_phase`, `exc_pre`). For the
  real `bd_c2n` INIT, the LUT's Boolean function of its pins is exactly the
  phase value on `[c j, c (j+1))`: the C-element never has a hazard at its
  own pins, provided each input is stable from its arrival until it departs,
  departures come `L.lo + E` after the phase start, and `E` covers the
  feedback wire plus the LUT spread (5b's `H_ENV_LATENCY`). Only the stretch
  of the phase is needed; earlier phases are not.
* Through a FIFO LUT (`H_LUT_FIFO`) the node is then a clean step signal:
  ONE transition per phase, at `τ j = fst σ (c j) ∈ [c j + lo, c j + hi]`
  (`node_phase`). The request line (SDELAY, symmetric LUT1 chain + wires) is
  FIFO, and the DACK FASTRISE line is modelled as the OR of a fast and a slow
  FIFO copy (`or_hold_true/false`); both carry the clean node to a clean
  pin. So stage `i`'s node IS a clean environment for stages `i ± 1`.
* **The two-stage pipe** (`pipe_ctl`): event times of both controllers are
  defined by recursion on the phase index (`cc`) from the delay
  realisation and the environment's times; by induction on the phase,
  every excitation, node and internal pin is a clean step signal with those
  times. Causality across the internal boundary is NOT assumed: the
  departure bounds come out of the definitions (`dep0a`, `dep1r`).
* **Every token's value** (`pipe_token`, `pipe_forward`): 6c's
  `Bundling.capture` applies to both stages unchanged, with the enable times
  derived, and the per-boundary obligations are fields of `Data2`.
* **Non-vacuity** (`Wit.witness`, `Wit.witness_data`): a fixed-delay run
  satisfying every hypothesis (`Gates2`, `Env2`, `Timing2`, `Data2`) at
  every instant, with one data bit whose token values alternate; the latch
  bits are the real `ODD` INIT through 6c's `odd_latch`.

General `N`: the lemmas of sections 2-3 (`fifo_hold`, `fifo_comp`,
`or_hold_*`, `exc_phase`, `exc_pre`, `node_phase`) do not depend on `N`;
only the time recursion `cc` and the induction order of `pipe_ctl` are
written for `N = 2` (see `formal/notes/B-pipe-timed.md` for the general
recursion, on `2j + i`).

Core Lean only.
-/

namespace Formal.Cells.PipeTimed
open Formal.Cells

abbrev Trace := Nat → Bool

/-- The phase value (1 on even phases, 0 on odd), as in 6d. -/
abbrev Vph := LinkTimed.Vph

theorem Vph_succ (j : Nat) : Vph (j + 1) = !Vph j := LinkTimed.Vph_alt j
theorem Vph_even (k : Nat) : Vph (2 * k) = true := LinkTimed.Vph_e k
theorem Vph_odd (k : Nat) : Vph (2 * k + 1) = false := LinkTimed.Vph_o k

/-! ## 1. Bounded search -/

/-- Least `t < n` with `p t`, or `n` if there is none. -/
def lfind (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if lfind p n < n then lfind p n else if p n then n else n + 1

theorem lfind_le (p : Nat → Bool) : ∀ n, lfind p n ≤ n := by
  intro n
  induction n with
  | zero => simp [lfind]
  | succ n ih =>
    by_cases h1 : lfind p n < n
    · have e : lfind p (n + 1) = lfind p n := by simp [lfind, h1]
      omega
    · by_cases h2 : p n = true
      · have e : lfind p (n + 1) = n := by simp [lfind, h1, h2]
        omega
      · have e : lfind p (n + 1) = n + 1 := by simp [lfind, h1, h2]
        omega

theorem lfind_spec (p : Nat → Bool) : ∀ n, lfind p n < n → p (lfind p n) = true := by
  intro n
  induction n with
  | zero => intro h; simp [lfind] at h
  | succ n ih =>
    intro h
    by_cases h1 : lfind p n < n
    · have e : lfind p (n + 1) = lfind p n := by simp [lfind, h1]
      rw [e]; exact ih h1
    · by_cases h2 : p n = true
      · have e : lfind p (n + 1) = n := by simp [lfind, h1, h2]
        rw [e]; exact h2
      · have e : lfind p (n + 1) = n + 1 := by simp [lfind, h1, h2]
        omega

theorem lfind_min (p : Nat → Bool) : ∀ n t, t < lfind p n → p t = false := by
  intro n
  induction n with
  | zero => intro t h; simp [lfind] at h
  | succ n ih =>
    intro t h
    by_cases h1 : lfind p n < n
    · have e : lfind p (n + 1) = lfind p n := by simp [lfind, h1]
      rw [e] at h; exact ih t h
    · have hle := lfind_le p n
      by_cases h2 : p n = true
      · have e : lfind p (n + 1) = n := by simp [lfind, h1, h2]
        rw [e] at h; exact ih t (by omega)
      · have e : lfind p (n + 1) = n + 1 := by simp [lfind, h1, h2]
        rw [e] at h
        by_cases ht : t < n
        · exact ih t (by omega)
        · have : t = n := by omega
          subst this; simpa using h2

/-! ## 2. The FIFO bounded-delay channel (ℕ-time version of shard A's `Pure.Chan`) -/

/-- **A read-time map with delay bounds `[lo, hi]`** (shard A's `Retime`, in ℕ
ticks). The channel output at `t` shows the input as it was at `σ t`;
`σ` nondecreasing is the FIFO property (transitions never overtake; a pulse
shorter than the delay spread can be swallowed but never inverted or split).
The bounds use truncated subtraction; they only constrain the channel from
`t ≥ hi` on, where the channel relation is stated. -/
structure Ret where
  σ : Nat → Nat
  lo : Nat
  hi : Nat
  mono : ∀ a b, a ≤ b → σ a ≤ σ b
  ge : ∀ t, t - hi ≤ σ t
  le : ∀ t, σ t ≤ t - lo

namespace Ret

/-- First output instant that reads the input at or after `c`: an input
edge at `c` reaches the output exactly here. -/
def fst (r : Ret) (c : Nat) : Nat := lfind (fun t => decide (c ≤ r.σ t)) (c + r.hi + 1)

theorem lo_le_hi (r : Ret) : r.lo ≤ r.hi := by
  have h1 := r.ge (r.hi + r.lo); have h2 := r.le (r.hi + r.lo); omega

theorem fst_lt_bound (r : Ret) (c : Nat) : r.fst c < c + r.hi + 1 := by
  apply Classical.byContradiction; intro h
  have hm := lfind_min (fun t => decide (c ≤ r.σ t)) (c + r.hi + 1) (c + r.hi)
    (by unfold fst at h; omega)
  have := r.ge (c + r.hi)
  simp at hm; omega

theorem fst_spec (r : Ret) (c : Nat) : c ≤ r.σ (r.fst c) := by
  have := lfind_spec (fun t => decide (c ≤ r.σ t)) (c + r.hi + 1) (fst_lt_bound r c)
  exact of_decide_eq_true this

theorem fst_le (r : Ret) (c : Nat) : r.fst c ≤ c + r.hi := by
  have := fst_lt_bound r c; omega

theorem fst_after (r : Ret) {c t : Nat} (h : r.fst c ≤ t) : c ≤ r.σ t :=
  Nat.le_trans (fst_spec r c) (r.mono _ _ h)

theorem fst_before (r : Ret) {c t : Nat} (h : t < r.fst c) : r.σ t < c := by
  have := lfind_min (fun t => decide (c ≤ r.σ t)) (c + r.hi + 1) t h
  simp at this; omega

/-- An edge at `c ≥ 1` reaches the output no earlier than `c + lo`. -/
theorem fst_lo (r : Ret) {c : Nat} (hc : 1 ≤ c) : c + r.lo ≤ r.fst c := by
  have h1 := fst_spec r c; have h2 := r.le (r.fst c); omega

theorem fst_ge (r : Ret) (c : Nat) : c ≤ r.fst c := by
  rcases Nat.eq_zero_or_pos c with h | h
  · omega
  · have := fst_lo r (c := c) h; omega

/-- Fixed transport delay `d` is a FIFO read-time map. -/
def shift (d : Nat) : Ret where
  σ t := t - d
  lo := d
  hi := d
  mono a b h := by omega
  ge t := by omega
  le t := by omega

theorem fst_shift (d c : Nat) (hc : 1 ≤ c) : (shift d).fst c = c + d := by
  have h1 : c + d ≤ (shift d).fst c := fst_lo (shift d) hc
  have h2 : (shift d).fst c ≤ c + d := fst_le (shift d) c
  omega

/-- Two FIFO channels in series (e.g. a wire, then each LUT1 of the SDELAY
chain, then a wire) are one FIFO channel with summed bounds. -/
def comp (r1 r2 : Ret) : Ret where
  σ t := r1.σ (r2.σ t)
  lo := r1.lo + r2.lo
  hi := r1.hi + r2.hi
  mono a b h := r1.mono _ _ (r2.mono _ _ h)
  ge t := by have := r1.ge (r2.σ t); have := r2.ge t; omega
  le t := by have := r1.le (r2.σ t); have := r2.le t; omega

end Ret

/-- Series composition of FIFO channel relations: `x → y` through `r1`, then
`y → z` through `r2`, is `x → z` through `Ret.comp r1 r2`. -/
theorem fifo_comp (r1 r2 : Ret) {x y z : Trace}
    (h1 : ∀ t, r1.hi ≤ t → y t = x (r1.σ t)) (h2 : ∀ t, r2.hi ≤ t → z t = y (r2.σ t)) :
    ∀ t, (Ret.comp r1 r2).hi ≤ t → z t = x ((Ret.comp r1 r2).σ t) := by
  intro t ht
  have hh : r1.hi + r2.hi ≤ t := ht
  have g := r2.ge t
  rw [h2 t (by omega), h1 _ (by omega)]; rfl

/-- A FIFO channel is a (degenerate) window channel: every positive result of
5b/6d for `WinDelay` applies to it. -/
theorem fifo_win (r : Ret) {x y : Trace} (hy : ∀ t, r.hi ≤ t → y t = x (r.σ t)) :
    CElemTiming.WinDelay r.lo r.hi x y := by
  intro t ht
  have h1 := r.ge t; have h2 := r.le t; have h3 := r.lo_le_hi
  exact ⟨r.σ t, by omega, by omega, hy t ht⟩

/-- **FIFO transfer.** If the input holds `v` on `[a, b)`, the output holds `v`
on `[fst a, fst b)` (from `hi` on): one stretch in, one stretch out. -/
theorem fifo_hold (r : Ret) {x y : Trace} (hy : ∀ t, r.hi ≤ t → y t = x (r.σ t))
    {a b : Nat} {v : Bool} (hx : ∀ s, a ≤ s → s < b → x s = v) :
    ∀ t, r.fst a ≤ t → t < r.fst b → r.hi ≤ t → y t = v := by
  intro t h1 h2 h3
  rw [hy t h3]; exact hx _ (r.fst_after h1) (r.fst_before h2)

/-- **OR of two FIFO copies, low stretch.** Output low on the intersection of
the two copies' low stretches. -/
theorem or_hold_false (r1 r2 : Ret) {x y : Trace}
    (hy : ∀ t, max r1.hi r2.hi ≤ t → y t = (x (r1.σ t) || x (r2.σ t)))
    {a b : Nat} (hx : ∀ s, a ≤ s → s < b → x s = false) :
    ∀ t, max (r1.fst a) (r2.fst a) ≤ t → t < min (r1.fst b) (r2.fst b) →
      max r1.hi r2.hi ≤ t → y t = false := by
  intro t h1 h2 h3
  rw [hy t h3, hx _ (r1.fst_after (by omega)) (r1.fst_before (by omega)),
    hx _ (r2.fst_after (by omega)) (r2.fst_before (by omega))]; rfl

/-- **OR of two FIFO copies, high stretch.** Output high on the union of the
two copies' high stretches, provided they overlap (`hov1`, `hov2`: each copy
takes the rise before the other takes the fall). -/
theorem or_hold_true (r1 r2 : Ret) {x y : Trace}
    (hy : ∀ t, max r1.hi r2.hi ≤ t → y t = (x (r1.σ t) || x (r2.σ t)))
    {a b : Nat} (hx : ∀ s, a ≤ s → s < b → x s = true)
    (hov1 : r1.fst a ≤ r2.fst b) (hov2 : r2.fst a ≤ r1.fst b) :
    ∀ t, min (r1.fst a) (r2.fst a) ≤ t → t < max (r1.fst b) (r2.fst b) →
      max r1.hi r2.hi ≤ t → y t = true := by
  intro t h1 h2 h3
  rw [hy t h3]
  by_cases c1 : r1.fst a ≤ t ∧ t < r1.fst b
  · rw [hx _ (r1.fst_after c1.1) (r1.fst_before c1.2)]; rfl
  · rw [hx _ (r2.fst_after (by omega)) (r2.fst_before (by omega))]; cases x (r1.σ t) <;> rfl

/-! ## 3. One controller with a FIFO LUT -/

/-- Excitation of `bd_link_ctl` (= `bd_c2n`, REAL INIT `0x00B200B200B200B2`,
evaluated by `Prelim.lutB` through 5b's `exc`): the LUT's Boolean function
of its pins `I0 = req`, `I1 = ack (c_next)`, `I2 = qp`, `I3 = rst`. -/
def ex (req ack qp rst : Trace) (t : Nat) : Bool :=
  CElemTiming.exc CElemTiming.INIT_c2n (req t) (ack t) (qp t) (rst t)

/-- **The gate relations of one controller.** -/
structure Ctl (req ack rst O qp : Trace) (L : Ret) (wl wh : Nat) : Prop where
  /-- **H_LUT_FIFO**: the controller LUT's output is its excitation read
  through a FIFO bounded delay `[L.lo, L.hi]` (prjxray LUT arc min/max).
  Stronger than 5b's `H_LUT` (`ctl_loop`): it rules out the in-window
  glitches of the non-FIFO channel. Physical content: a LUT whose function
  makes ONE transition produces ONE output transition (a pass-transistor mux
  behind input buffers does not reorder edges; delay variation is slow next
  to the edge spacing), and a pin change that leaves the function unchanged
  produces no output glitch (that is what makes `ex` the right input).
  Test: GLS of a lone LUT with an input making a single edge at varying
  times relative to an unrelated pin edge, SDF min/max; board: a ring of
  such LUTs never shows an extra edge per revolution. -/
  H_LUT_FIFO : ∀ t, L.hi ≤ t → O t = ex req ack qp rst (L.σ t)
  /-- **H_FB**: the feedback wire `O → I2`, 5b's window channel (non-FIFO is
  allowed here: only its stable stretches are used). -/
  H_FB : CElemTiming.WinDelay wl wh O qp
  /-- **H_LOOP_POS**: the loop LUT + wire has positive minimum delay. -/
  H_LOOP_POS : 1 ≤ L.lo + wl

/-- A FIFO controller is a 5b `Loop`, so 6d's whole single-stage theory
(`LinkTimed.CtlEnv`) applies to it unchanged. -/
theorem ctl_loop {req ack rst O qp : Trace} {L : Ret} {wl wh : Nat}
    (C : Ctl req ack rst O qp L wl wh) :
    CElemTiming.Loop CElemTiming.INIT_c2n req ack rst O qp L.lo L.hi wl wh where
  H_LUT := fifo_win L C.H_LUT_FIFO
  H_FB := C.H_FB
  H_LOOP_POS := by have := C.H_LOOP_POS; omega

section stage
variable {req ack rst O qp : Trace} {L : Ret} {wl wh : Nat}

/-- **The excitation is clean for a whole phase.** Phase target `v`. The
request holds `v` from its arrival `ρ` until it departs at `ρ'`; the
acknowledge (I1) holds `!v` on `[α, α')`. The phase starts at
`c = max ρ α`. Both departures come at least `L.lo + E` after `c`, and
`E ≥ (L.hi - L.lo) + wh` (`hlat`, 5b's `H_ENV_LATENCY`). Then the LUT's
function of its pins is `v` on all of `[c, max ρ' α')`: no hazard at the
LUT, whatever the inputs do after they depart. -/
theorem exc_phase (C : Ctl req ack rst O qp L wl wh) (v : Bool) (ρ ρ' α α' E : Nat)
    (hreq : ∀ t, ρ ≤ t → t < ρ' → req t = v)
    (hack : ∀ t, α ≤ t → t < α' → ack t = !v)
    (hrst : ∀ t, max ρ α ≤ t → rst t = false)
    (hdr : max ρ α + L.lo + E ≤ ρ') (hda : max ρ α + L.lo + E ≤ α')
    (hlat : L.hi + wh ≤ L.lo + E) (hbig : L.hi + wh ≤ max ρ α) :
    ∀ s, max ρ α ≤ s → s < max ρ' α' → ex req ack qp rst s = v := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h1 h2
    have hr := hrst s h1
    have hq : (ρ' ≤ s ∨ α' ≤ s) → qp s = v := by
      intro hdep
      have hdep' : max ρ α + L.lo + E ≤ s := by omega
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      have hpos := C.H_LOOP_POS
      have g1 := L.ge u; have g2 := L.le u
      rw [e, C.H_LUT_FIFO u (by omega)]
      exact ih (L.σ u) (by omega) (by omega) (by omega)
    unfold ex; rw [CElemTiming.c2n_eq, hr]
    by_cases hr' : s < ρ'
    · by_cases ha' : s < α'
      · rw [hreq s (by omega) hr', hack s (by omega) ha']
        cases v <;> cases qp s <;> rfl
      · rw [hreq s (by omega) hr', hq (Or.inr (by omega))]
        cases v <;> cases ack s <;> rfl
    · have ha' : s < α' := by omega
      rw [hack s (by omega) ha', hq (Or.inl (by omega))]
      cases v <;> cases req s <;> rfl

/-- **Before the first phase.** Reset high on `[0, R)` (from any power-up
state) and the request low on `[R, ρ)`: the excitation is 0 on `[0, ρ)`. -/
theorem exc_pre (C : Ctl req ack rst O qp L wl wh) (R ρ : Nat)
    (hrst : ∀ t, t < R → rst t = true) (hreq : ∀ t, R ≤ t → t < ρ → req t = false)
    (hR : L.hi + wh ≤ R) : ∀ s, s < ρ → ex req ack qp rst s = false := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h
    unfold ex; rw [CElemTiming.c2n_eq]
    by_cases hs : s < R
    · rw [hrst s hs]; rfl
    · obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      have hpos := C.H_LOOP_POS
      have g1 := L.ge u; have g2 := L.le u; have g3 := L.lo_le_hi
      have hq : qp s = false := by
        rw [e, C.H_LUT_FIFO u (by omega)]; exact ih _ (by omega) (by omega)
      rw [hreq s (by omega) h, hq]; cases rst s <;> cases ack s <;> rfl

/-- **One clean transition per phase at the node.** If the excitation is `v`
on `[c, c')`, the node is `v` on `[fst c, fst c')`: through the FIFO LUT the
phase's single excitation edge is a single node edge, at
`fst c ∈ [c + L.lo, c + L.hi]`. -/
theorem node_phase (C : Ctl req ack rst O qp L wl wh) {c c' : Nat} {v : Bool}
    (he : ∀ s, c ≤ s → s < c' → ex req ack qp rst s = v) :
    ∀ t, L.fst c ≤ t → t < L.fst c' → L.hi ≤ t → O t = v :=
  fifo_hold L C.H_LUT_FIFO he

end stage

/-! ## 4. The two-stage pipe: delay realisation and derived event times

`bd_pipe #(.N(2))` (`cells/rtl/bd_link.v`): stage 0's node `O0` drives the
request line `r[1]` (`rdly`, `bd_delay #(.N(SDELAY))`, a symmetric LUT1 chain,
plus wires) into stage 1's I0, and stage 1's node `O1` drives the acknowledge
line `a[1]` (`uack`, `bd_delay #(.N(DACK), .FASTRISE(1))`, plus wires) into
stage 0's I1. The environment drives `r[0]` (stage 0's I0) and `a[2]`
(stage 1's I1).

A run's delays are fixed by its read-time maps (`P2`): the two controller
LUTs, the request line, and the two paths of the acknowledge line (`Ar`: the
fast tap, one LUT + wires, which carries the rise; `Af`: the ripple through
the chain, which carries the fall). Every event time below is DEFINED from
these and from the environment's own event times `ρ` (`r[0]`'s `j`-th edge)
and `γ` (`a[2]`'s `j`-th edge). -/

/-- Delay realisation of one run of the two-stage pipe plus the
environment's event times. -/
structure P2 where
  /-- reset is released at `R` -/
  R : Nat
  /-- stage 0 / stage 1 controller LUT (`<pipe>.stage[i].u.ctl.u.u`) -/
  L0 : Ret
  L1 : Ret
  /-- boundary-1 request line: wire + SDELAY chain + wire, `O0 → I0` of stage 1 -/
  Rq : Ret
  /-- boundary-1 acknowledge line, fast (tap) path, `O1 → I1` of stage 0 -/
  Ar : Ret
  /-- boundary-1 acknowledge line, slow (ripple) path through the DACK chain -/
  Af : Ret
  /-- `r[0]` at stage 0's I0 makes its `j`-th edge at `ρ j` -/
  ρ : Nat → Nat
  /-- `a[2]` at stage 1's I1 makes its `j`-th edge at `γ j` -/
  γ : Nat → Nat

namespace P2

/-- Edge time at the acknowledge-line output for the node's `j`-th edge at
`τ`: a rise (even `j`) leaves by the earlier path, a fall (odd `j`) by the
later. -/
def ackT (P : P2) (j τ : Nat) : Nat :=
  if j % 2 = 0 then min (P.Ar.fst τ) (P.Af.fst τ) else max (P.Ar.fst τ) (P.Af.fst τ)

def c1of (P : P2) (c0 a1 : Nat) : Nat := max (P.Rq.fst (P.L0.fst c0)) a1

/-- Phase starts of both controllers, by recursion on the phase index. -/
def cc (P : P2) : Nat → Nat × Nat
  | 0 => (max (P.ρ 0) P.R, P.c1of (max (P.ρ 0) P.R) P.R)
  | j + 1 =>
    (max (P.ρ (j + 1)) (P.ackT j (P.L1.fst (cc P j).2)),
     P.c1of (max (P.ρ (j + 1)) (P.ackT j (P.L1.fst (cc P j).2))) (P.γ j))

/-- Phase `j` of stage 0 starts (both its pins at the target). -/
def c0 (P : P2) (j : Nat) : Nat := (P.cc j).1
def c1 (P : P2) (j : Nat) : Nat := (P.cc j).2
/-- Stage 0's node makes its `j`-th edge. -/
def τ0 (P : P2) (j : Nat) : Nat := P.L0.fst (P.c0 j)
def τ1 (P : P2) (j : Nat) : Nat := P.L1.fst (P.c1 j)
/-- Stage 0's I1 (`a[1]`) reaches phase `j`'s level (`!Vph j`). -/
def A0 (P : P2) : Nat → Nat
  | 0 => P.R
  | j + 1 => P.ackT j (P.τ1 j)
/-- Stage 1's I0 (`r[1]`) makes its `j`-th edge. -/
def R1 (P : P2) (j : Nat) : Nat := P.Rq.fst (P.τ0 j)
/-- Stage 1's I1 (`a[2]`) reaches phase `j`'s level. -/
def A1 (P : P2) : Nat → Nat
  | 0 => P.R
  | j + 1 => P.γ j
def alo (P : P2) : Nat := min P.Ar.lo P.Af.lo
def ahi (P : P2) : Nat := max P.Ar.hi P.Af.hi
/-- Minimum round trip seen by stage 0 through stage 1: request line,
stage-1 LUT, acknowledge line. -/
def RT0 (P : P2) : Nat := P.Rq.lo + P.L1.lo + P.alo
/-- Minimum round trip seen by stage 1 through stage 0. -/
def RT1 (P : P2) : Nat := P.alo + P.L0.lo + P.Rq.lo

theorem c0_eq (P : P2) (j : Nat) : P.c0 j = max (P.ρ j) (P.A0 j) := by cases j <;> rfl
theorem c1_eq (P : P2) (j : Nat) : P.c1 j = max (P.R1 j) (P.A1 j) := by cases j <;> rfl

theorem ackT_ge (P : P2) (j τ : Nat) (h : 1 ≤ τ) : τ + P.alo ≤ P.ackT j τ := by
  have h1 := P.Ar.fst_lo h; have h2 := P.Af.fst_lo h
  unfold ackT alo; split <;> omega

theorem ackT_le (P : P2) (j τ : Nat) : P.ackT j τ ≤ τ + P.ahi := by
  have h1 := P.Ar.fst_le τ; have h2 := P.Af.fst_le τ
  unfold ackT ahi; split <;> omega

/-- A fall leaves the acknowledge line by the SLOW path: the DACK credit. -/
theorem ackT_odd (P : P2) (j τ : Nat) (hj : j % 2 = 1) (h : 1 ≤ τ) :
    τ + max P.Ar.lo P.Af.lo ≤ P.ackT j τ := by
  have h1 := P.Ar.fst_lo h; have h2 := P.Af.fst_lo h
  unfold ackT; simp only [show ¬ (j % 2 = 0) by omega, ite_false]; omega

end P2

/-! ## 5. The gate relations, the environment, the control-side obligations -/

/-- **Gate relations of the two-stage pipe** (all nets at the pins they
drive). -/
structure Gates2 (P : P2) (rst r0 a0 O0 q0 r1 a1 O1 q1 : Trace) (w0l w0h w1l w1h : Nat) : Prop where
  /-- **H_RST**: `rst` high on `[0, R)` (from power-up), low after. -/
  H_RST : ∀ t, rst t = decide (t < P.R)
  /-- **H_CTL0/1**: both controllers (real INIT, FIFO LUT, feedback window). -/
  H_CTL0 : Ctl r0 a0 rst O0 q0 P.L0 w0l w0h
  H_CTL1 : Ctl r1 a1 rst O1 q1 P.L1 w1l w1h
  /-- **H_REQ_LINE** (FIFO): the request line `r[1]` (wires + SDELAY chain of
  LUT1 buffers, each FIFO, composed) reads stage 0's node through `P.Rq`.
  Test: SDF of `<pipe>.stage[0].u.rdly` and its nets, >= 4 seeds; GLS shows
  one edge at stage 1's I0 per node edge. -/
  H_REQ_LINE : ∀ t, P.Rq.hi ≤ t → r1 t = O0 (P.Rq.σ t)
  /-- **H_ACK_LINE**: the FASTRISE DACK line `a[1]` as the OR of a fast FIFO
  copy (the side taps: rise in one hop) and a slow FIFO copy (the ripple:
  fall after DACK hops) of stage 1's node. An abstraction of the chain
  `s(i+1) = s i ∨ a` (6c `fastrise_line`): it is exact for edges separated by
  more than the line's spread, which `H_ACK_FLUSH` and the derived phase
  gaps provide. With `DACK ≤ 1` take `Ar = Af`. -/
  H_ACK_LINE : ∀ t, max P.Ar.hi P.Af.hi ≤ t → a0 t = (O1 (P.Ar.σ t) || O1 (P.Af.σ t))

/-- **The environment** (sender at `r[0]`, receiver at `a[2]`): clean
four-phase pins (as 6d), and causality measured from the node edge the
party reacts to (the node is PROVED to make exactly one edge there). -/
structure Env2 (P : P2) (r0 a1 : Trace) (Es Er : Nat) : Prop where
  /-- **H_REQ_SHAPE**: `r[0]` low from reset release to its first rise, then
  `Vph j` between its `j`-th and `(j+1)`-th edges. -/
  H_REQ_LOW0 : ∀ t, P.R ≤ t → t < P.ρ 0 → r0 t = false
  H_REQ : ∀ j t, P.ρ j ≤ t → t < P.ρ (j + 1) → r0 t = Vph j
  /-- **H_ACK_SHAPE**: the same for `a[2]` at stage 1's I1. -/
  H_ACK_LOW0 : ∀ t, P.R ≤ t → t < P.γ 0 → a1 t = false
  H_ACK : ∀ j t, P.γ j ≤ t → t < P.γ (j + 1) → a1 t = Vph j
  /-- **H_SND**: the sender's next request edge comes at least `Es` after
  stage 0's node edge it answers (`Es` = ack_in wire incl. stage 0's DACK
  rise + sender + wire to I0). -/
  H_SND : ∀ j, P.τ0 j + Es ≤ P.ρ (j + 1)
  /-- **H_RCV**: the receiver's acknowledge edge comes at least `Er` after
  stage 1's node edge (req_out DELAY + wires + receiver). -/
  H_RCV : ∀ j, P.τ1 j + Er ≤ P.γ j
  /-- **H_RST_EARLY**: reset released before the first request. -/
  H_RST_EARLY : P.R ≤ P.ρ 0

/-- **Control-side timing obligations.** -/
structure Timing2 (P : P2) (w0h w1h Es Er : Nat) : Prop where
  H_R_POS : 1 ≤ P.R
  /-- **H_RST_LONG**: reset outlasts each controller loop (5b `c2_reset`). -/
  H_RST_LONG : P.L0.hi + w0h ≤ P.R ∧ P.L1.hi + w1h ≤ P.R
  /-- **H_RST_LINES**: and the lines between the stages have flushed the
  power-up values by release. -/
  H_RST_LINES : P.L0.hi + P.Rq.hi ≤ P.R ∧ P.L1.hi + P.ahi ≤ P.R
  /-- **H_LAT0** (5b/6d `H_ENV_LATENCY` at stage 0): both neighbours of
  stage 0 answer slower than its feedback wire plus its LUT spread. -/
  H_LAT0 : P.L0.hi + w0h ≤ P.L0.lo + min Es P.RT0
  /-- **H_LAT1**: the same at stage 1. -/
  H_LAT1 : P.L1.hi + w1h ≤ P.L1.lo + min Er P.RT1
  /-- **H_ACK_FLUSH**: stage 1's high phase outlasts the acknowledge line's
  spread (each path takes the rise before the other takes the fall). -/
  H_ACK_FLUSH : P.ahi ≤ P.L1.lo + max Er P.RT1 + P.alo

section chain
variable {P : P2} {rst r0 a0 O0 q0 r1 a1 O1 q1 : Trace} {w0l w0h w1l w1h Es Er : Nat}

/-- Every phase starts after reset release. -/
theorem ge_R (_E : Env2 P r0 a1 Es Er) (T : Timing2 P w0h w1h Es Er) :
    ∀ j, P.R ≤ P.c0 j ∧ P.R ≤ P.c1 j := by
  have hR := T.H_R_POS
  intro j
  induction j with
  | zero =>
    rw [P.c0_eq, P.c1_eq]; simp only [P2.A0, P2.A1]; omega
  | succ j ih =>
    have h1 : P.R ≤ P.c0 (j + 1) := by
      rw [P.c0_eq]; simp only [P2.A0]
      have := P.ackT_ge j (P.τ1 j) (by have := P.L1.fst_ge (P.c1 j); unfold P2.τ1; omega)
      have := P.L1.fst_ge (P.c1 j); unfold P2.τ1 at *; omega
    refine ⟨h1, ?_⟩
    rw [P.c1_eq]
    have := P.Rq.fst_ge (P.τ0 (j + 1)); have := P.L0.fst_ge (P.c0 (j + 1))
    unfold P2.R1 P2.τ0 at *; omega

variable (E : Env2 P r0 a1 Es Er) (T : Timing2 P w0h w1h Es Er)
include E T

theorem tau0_lo (j : Nat) : P.c0 j + P.L0.lo ≤ P.τ0 j :=
  P.L0.fst_lo (by have := (ge_R E T j).1; have := T.H_R_POS; omega)
theorem tau1_lo (j : Nat) : P.c1 j + P.L1.lo ≤ P.τ1 j :=
  P.L1.fst_lo (by have := (ge_R E T j).2; have := T.H_R_POS; omega)
theorem R1_lo (j : Nat) : P.τ0 j + P.Rq.lo ≤ P.R1 j :=
  P.Rq.fst_lo (by have := tau0_lo E T j; have := (ge_R E T j).1; have := T.H_R_POS; omega)
theorem A0_lo (j : Nat) : P.τ1 j + P.alo ≤ P.A0 (j + 1) :=
  P.ackT_ge j _ (by have := tau1_lo E T j; have := (ge_R E T j).2; have := T.H_R_POS; omega)

/-- Stage 0's request departs `L0.lo + Es` after its phase start. -/
theorem dep0r (j : Nat) : P.c0 j + P.L0.lo + Es ≤ P.ρ (j + 1) := by
  have := E.H_SND j; have := tau0_lo E T j; omega

/-- Stage 0's acknowledge pin departs at least `L0.lo + RT0` after its phase
start: DERIVED (stage 1 cannot answer before it has seen stage 0's edge). -/
theorem dep0a (j : Nat) : P.c0 j + P.L0.lo + P.RT0 ≤ P.A0 (j + 1) := by
  have h1 := A0_lo E T j; have h2 := tau1_lo E T j; have h3 := P.c1_eq j
  have h4 := R1_lo E T j; have h5 := tau0_lo E T j
  unfold P2.RT0; omega

/-- Stage 1's request pin departs at least `L1.lo + RT1` after its phase
start: DERIVED. -/
theorem dep1r (j : Nat) : P.c1 j + P.L1.lo + P.RT1 ≤ P.R1 (j + 1) := by
  have h1 := R1_lo E T (j + 1); have h2 := tau0_lo E T (j + 1); have h3 := P.c0_eq (j + 1)
  have h4 := A0_lo E T j; have h5 := tau1_lo E T j
  unfold P2.RT1; omega

theorem dep1a (j : Nat) : P.c1 j + P.L1.lo + Er ≤ P.A1 (j + 1) := by
  have := E.H_RCV j; have := tau1_lo E T j; simp only [P2.A1]; omega

/-- Node 0's consecutive edges are at least `L0.lo + max Es RT0` apart. -/
theorem gap0 (j : Nat) : P.τ0 j + P.L0.lo + max Es P.RT0 ≤ P.τ0 (j + 1) := by
  have h1 := tau0_lo E T (j + 1); have h2 := P.c0_eq (j + 1); have h3 := E.H_SND j
  have h4 := A0_lo E T j; have h5 := tau1_lo E T j; have h6 := P.c1_eq j
  have h7 := R1_lo E T j
  unfold P2.RT0; omega

theorem gap1 (j : Nat) : P.τ1 j + P.L1.lo + max Er P.RT1 ≤ P.τ1 (j + 1) := by
  have h1 := tau1_lo E T (j + 1); have h2 := P.c1_eq (j + 1); have h3 := E.H_RCV j
  have h4 := R1_lo E T (j + 1); have h5 := tau0_lo E T (j + 1); have h6 := P.c0_eq (j + 1)
  have h7 := A0_lo E T j
  simp only [P2.A1] at h2; unfold P2.RT1; omega

/-- Stage 1's `j`-th edge follows stage 0's through the request line. -/
theorem fwd (j : Nat) : P.τ0 j + P.Rq.lo + P.L1.lo ≤ P.τ1 j := by
  have := R1_lo E T j; have := tau1_lo E T j; have := P.c1_eq j; omega

/-- Stage 0's rise after stage 1's fall comes through the DACK line's SLOW
path. -/
theorem back_odd (j : Nat) (hj : j % 2 = 1) :
    P.τ1 j + max P.Ar.lo P.Af.lo + P.L0.lo ≤ P.τ0 (j + 1) := by
  have h1 := tau0_lo E T (j + 1); have h2 := P.c0_eq (j + 1)
  have h3 := P.ackT_odd j (P.τ1 j) hj
    (by have := tau1_lo E T j; have := (ge_R E T j).2; have := T.H_R_POS; omega)
  simp only [P2.A0] at h2; omega

theorem rho_le (j : Nat) : P.ρ j + P.L0.lo ≤ P.τ0 j := by
  have := tau0_lo E T j; have := P.c0_eq j; omega

theorem gam_le (j : Nat) : P.γ j + P.L1.lo ≤ P.τ1 (j + 1) := by
  have := tau1_lo E T (j + 1); have := P.c1_eq (j + 1); simp only [P2.A1] at this; omega

/-- **Liveness, given the environment's.** Each node's edges strictly
increase, so `nodes_clean` describes infinitely many real transitions (every
phase interval is non-empty). -/
theorem live (j : Nat) (hp0 : 1 ≤ P.L0.lo + w0h) (hp1 : 1 ≤ P.L1.lo + w1h) :
    P.τ0 j < P.τ0 (j + 1) ∧ P.τ1 j < P.τ1 (j + 1) := by
  have g0 := gap0 E T j; have g1 := gap1 E T j
  have l0 := T.H_LAT0; have l1 := T.H_LAT1
  have a0 := P.L0.lo_le_hi; have a1 := P.L1.lo_le_hi
  omega

end chain

/-! ## 6. Every node and internal pin of the pipe is a clean step signal -/

section ctl
variable {P : P2} {rst r0 a0 O0 q0 r1 a1 O1 q1 : Trace} {w0l w0h w1l w1h Es Er : Nat}
variable (G : Gates2 P rst r0 a0 O0 q0 r1 a1 O1 q1 w0l w0h w1l w1h)
  (E : Env2 P r0 a1 Es Er) (T : Timing2 P w0h w1h Es Er)
include G E T

omit E T in
theorem rst_hi : ∀ t, t < P.R → rst t = true := by
  intro t h; rw [G.H_RST]; simp [h]

omit E T in
theorem rst_lo : ∀ t, P.R ≤ t → rst t = false := by
  intro t h; rw [G.H_RST]; simp; omega

theorem pre0 : ∀ s, s < P.c0 0 → ex r0 a0 q0 rst s = false := by
  have hc : P.c0 0 = P.ρ 0 := by rw [P.c0_eq]; simp only [P2.A0]; have := E.H_RST_EARLY; omega
  rw [hc]
  exact exc_pre G.H_CTL0 P.R (P.ρ 0) (rst_hi G) E.H_REQ_LOW0 T.H_RST_LONG.1

theorem node0_pre : ∀ t, P.L0.hi ≤ t → t < P.τ0 0 → O0 t = false := by
  intro t h1 h2
  rw [G.H_CTL0.H_LUT_FIFO t h1]; exact pre0 G E T _ (P.L0.fst_before h2)

theorem pre1 : ∀ s, s < P.c1 0 → ex r1 a1 q1 rst s = false := by
  apply exc_pre G.H_CTL1 P.R (P.c1 0) (rst_hi G) _ T.H_RST_LONG.2
  intro t h1 h2
  have hc := P.c1_eq 0; simp only [P2.A1] at hc
  have hr := T.H_RST_LINES.1; have hl := P.Rq.lo_le_hi
  have g := P.Rq.ge t
  rw [G.H_REQ_LINE t (by omega)]
  exact node0_pre G E T _ (by omega) (P.Rq.fst_before (by unfold P2.R1 at hc; omega))

theorem node1_pre : ∀ t, P.L1.hi ≤ t → t < P.τ1 0 → O1 t = false := by
  intro t h1 h2
  rw [G.H_CTL1.H_LUT_FIFO t h1]; exact pre1 G E T _ (P.L1.fst_before h2)

/-- Stage 0, phase `j`, given its acknowledge pin. -/
theorem phase0_of (j : Nat) (hack : ∀ t, P.A0 j ≤ t → t < P.A0 (j + 1) → a0 t = !Vph j) :
    ∀ s, P.c0 j ≤ s → s < P.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j := by
  have hR := (ge_R E T j).1
  have hlat := T.H_LAT0
  have d1 := dep0r E T j; have d2 := dep0a E T j
  have hc := P.c0_eq j
  have hb := T.H_RST_LONG.1
  have res := exc_phase G.H_CTL0 (Vph j) (P.ρ j) (P.ρ (j + 1)) (P.A0 j) (P.A0 (j + 1))
    (min Es P.RT0) (E.H_REQ j) hack (fun t ht => rst_lo G t (by omega))
    (by omega) (by omega) hlat (by omega)
  intro s h1 h2
  rw [P.c0_eq] at h1 h2; exact res s h1 h2

/-- Stage 1, phase `j`, given stage 0's phase `j`. -/
theorem phase1_of (j : Nat)
    (h0 : ∀ s, P.c0 j ≤ s → s < P.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j) :
    ∀ s, P.c1 j ≤ s → s < P.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j := by
  have hR := ge_R E T j
  have hR' := ge_R E T (j + 1)
  have hlat := T.H_LAT1
  have d1 := dep1r E T j; have d2 := dep1a E T j
  have hc := P.c1_eq j
  have hb := T.H_RST_LONG
  have hl := T.H_RST_LINES
  have hreq : ∀ t, P.R1 j ≤ t → t < P.R1 (j + 1) → r1 t = Vph j := by
    have hO : ∀ s, P.τ0 j ≤ s → s < P.τ0 (j + 1) → O0 s = Vph j := by
      intro s h1 h2
      have := tau0_lo E T j
      exact node_phase G.H_CTL0 h0 s h1 h2 (by omega)
    intro t h1 h2
    have := R1_lo E T j; have := tau0_lo E T j
    exact fifo_hold P.Rq G.H_REQ_LINE hO t h1 h2 (by omega)
  have hack : ∀ t, P.A1 j ≤ t → t < P.A1 (j + 1) → a1 t = !Vph j := by
    cases j with
    | zero =>
      intro t h1 h2; simp only [P2.A1] at h1 h2
      rw [E.H_ACK_LOW0 t h1 h2]; rfl
    | succ j =>
      intro t h1 h2; simp only [P2.A1] at h1 h2
      rw [E.H_ACK j t h1 h2, Vph_succ, Bool.not_not]
  have res := exc_phase G.H_CTL1 (Vph j) (P.R1 j) (P.R1 (j + 1)) (P.A1 j) (P.A1 (j + 1))
    (min Er P.RT1) hreq hack (fun t ht => rst_lo G t (by omega))
    (by omega) (by omega) hlat (by omega)
  intro s h1 h2
  rw [P.c1_eq] at h1 h2; exact res s h1 h2

theorem ack0_zero : ∀ t, P.A0 0 ≤ t → t < P.A0 1 → a0 t = !Vph 0 := by
  intro t h1 h2
  simp only [P2.A0, P2.ackT, show (0 : Nat) % 2 = 0 from rfl, ite_true] at h1 h2
  have hl := T.H_RST_LINES.2
  have f1 := P.Ar.fst_le P.L1.hi; have f2 := P.Af.fst_le P.L1.hi
  have := or_hold_false P.Ar P.Af G.H_ACK_LINE (a := P.L1.hi) (b := P.τ1 0)
    (fun s h1 h2 => node1_pre G E T s h1 h2) t (by unfold P2.ahi at hl; omega) h2
    (by unfold P2.ahi at hl; omega)
  rw [this]; rfl

/-- Stage 0's acknowledge pin for phase `j+1`, from stage 1's phase `j`
through the OR line. -/
theorem ack0_succ (j : Nat)
    (h1 : ∀ s, P.c1 j ≤ s → s < P.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j) :
    ∀ t, P.A0 (j + 1) ≤ t → t < P.A0 (j + 1 + 1) → a0 t = !Vph (j + 1) := by
  have hR := (ge_R E T j).2
  have hl := T.H_RST_LINES.2
  have hO : ∀ s, P.τ1 j ≤ s → s < P.τ1 (j + 1) → O1 s = Vph j := by
    intro s a b
    have := tau1_lo E T j
    exact node_phase G.H_CTL1 h1 s a b (by omega)
  have ha := A0_lo E T j; have ht := tau1_lo E T j; have hRp := T.H_R_POS
  rw [Vph_succ, Bool.not_not]
  intro t t1 t2
  simp only [P2.A0, P2.ackT] at t1 t2
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hv : Vph j = true := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [hj, ite_true] at t1; simp only [show ¬ ((j + 1) % 2 = 0) by omega, ite_false] at t2
    have g := gap1 E T j; have fl := T.H_ACK_FLUSH
    have a1 := P.Ar.fst_le (P.τ1 j); have a2 := P.Af.fst_le (P.τ1 j)
    have hpos : 1 ≤ P.τ1 (j + 1) := by have := T.H_R_POS; omega
    have b1 := P.Ar.fst_lo hpos
    have b2 := P.Af.fst_lo hpos
    have e1 : P.ahi = max P.Ar.hi P.Af.hi := rfl
    have e2 : P.alo = min P.Ar.lo P.Af.lo := rfl
    have ov1 : P.Ar.fst (P.τ1 j) ≤ P.Af.fst (P.τ1 (j + 1)) := by omega
    have ov2 : P.Af.fst (P.τ1 j) ≤ P.Ar.fst (P.τ1 (j + 1)) := by omega
    exact or_hold_true P.Ar P.Af G.H_ACK_LINE hO ov1 ov2 t t1 t2
      (by have := P.Ar.fst_ge (P.τ1 j); have := P.Af.fst_ge (P.τ1 j); omega)
  · have hv : Vph j = false := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [show ¬ (j % 2 = 0) by omega, ite_false] at t1; simp only [show (j + 1) % 2 = 0 by omega, ite_true] at t2
    unfold P2.ahi at hl
    have := P.Ar.fst_ge (P.τ1 j); have := P.Af.fst_ge (P.τ1 j)
    exact or_hold_false P.Ar P.Af G.H_ACK_LINE hO t t1 t2 (by omega)

/-- **(1) The pipe's control is clean, phase by phase.** For every phase `j`,
both controllers' excitations equal `Vph j` from their phase start to the
next. Induction on `j`: stage 0's phase `j+1` uses stage 1's phase `j`
(through the DACK line); stage 1's phase `j` uses stage 0's phase `j`
(through the request line). -/
theorem pipe_ctl : ∀ j,
    (∀ s, P.c0 j ≤ s → s < P.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j) ∧
    (∀ s, P.c1 j ≤ s → s < P.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j) := by
  intro j
  induction j with
  | zero =>
    have h0 := phase0_of G E T 0 (ack0_zero G E T)
    exact ⟨h0, phase1_of G E T 0 h0⟩
  | succ j ih =>
    have h0 := phase0_of G E T (j + 1) (ack0_succ G E T j ih.2)
    exact ⟨h0, phase1_of G E T (j + 1) h0⟩

/-- **(1') Both nodes are clean step signals**: low from `L.hi` to their first
edge, then `Vph j` between their `j`-th and `(j+1)`-th edges `τ`. -/
theorem nodes_clean :
    (∀ t, P.L0.hi ≤ t → t < P.τ0 0 → O0 t = false) ∧
    (∀ j t, P.τ0 j ≤ t → t < P.τ0 (j + 1) → O0 t = Vph j) ∧
    (∀ t, P.L1.hi ≤ t → t < P.τ1 0 → O1 t = false) ∧
    (∀ j t, P.τ1 j ≤ t → t < P.τ1 (j + 1) → O1 t = Vph j) := by
  have hb := T.H_RST_LONG
  refine ⟨node0_pre G E T, fun j t h1 h2 => ?_, node1_pre G E T, fun j t h1 h2 => ?_⟩
  · have := tau0_lo E T j; have := (ge_R E T j).1
    exact node_phase G.H_CTL0 (pipe_ctl G E T j).1 t h1 h2 (by omega)
  · have := tau1_lo E T j; have := (ge_R E T j).2
    exact node_phase G.H_CTL1 (pipe_ctl G E T j).2 t h1 h2 (by omega)

/-- **(1'') The internal pins are clean environments**: stage 1's request pin
makes one edge per phase at `R1 j`, stage 0's acknowledge pin is `!Vph j`
on `[A0 j, A0 (j+1))`. This is the "clean request shape" 6d's `CtlEnv`
asks of its environment. -/
theorem pins_clean :
    (∀ j t, P.R1 j ≤ t → t < P.R1 (j + 1) → r1 t = Vph j) ∧
    (∀ j t, P.A0 j ≤ t → t < P.A0 (j + 1) → a0 t = !Vph j) := by
  have hl := T.H_RST_LINES
  refine ⟨fun j t h1 h2 => ?_, fun j => ?_⟩
  · have := R1_lo E T j; have := tau0_lo E T j; have := (ge_R E T j).1
    exact fifo_hold P.Rq G.H_REQ_LINE ((nodes_clean G E T).2.1 j) t h1 h2 (by omega)
  · cases j with
    | zero => exact ack0_zero G E T
    | succ j => exact ack0_succ G E T j (pipe_ctl G E T j).2

end ctl

/-! ## 7. The data path: every token's value through both stages -/

/-- Per-bit pin windows of one stage's latch LUTs (6c `LatchRel`): data pin
`[dlo, dhi]` (wire from the sender + arc), enable branch `[elo, ehi]` (this
bit's branch of the node's fanout + I1 arc), own loop `[flo, fhi]`. -/
structure Win where
  dlo : Nat → Nat
  dhi : Nat → Nat
  elo : Nat → Nat
  ehi : Nat → Nat
  flo : Nat → Nat
  fhi : Nat → Nat

/-- **Data-path hypotheses and per-boundary obligations** of the two-stage
pipe. `d i`: the environment's data net of bit `i`; `x0 i`, `x1 i`: the
latch outputs of stage 0 and 1 (`dat[W + i]`, `dat[2W + i]`); stage 1's
latch reads `x0 i` as its data. -/
structure Data2 (P : P2) (O0 O1 : Trace) (d x0 x1 : Nat → Bundling.Sig)
    (val : Nat → Nat → Bool) (dS dE : Nat → Nat) (V0 V1 : Win)
    (W Es Er Erel Sdr Lag : Nat) : Prop where
  /-- **H_LATCH0/1**: each latch bit is 6c's Kleene mux over its pin windows
  (`Bundling.odd_latch` / `pair_o5_latch` / `pair_o6_latch` from the real
  INITs under H_KLEENE_LUT); the enable is the stage's node. -/
  H_LATCH0 : ∀ i, i < W → Bundling.LatchRel (d i) O0 (x0 i)
    (V0.dlo i) (V0.dhi i) (V0.elo i) (V0.ehi i) (V0.flo i) (V0.fhi i)
  H_LATCH1 : ∀ i, i < W → Bundling.LatchRel (x0 i) O1 (x1 i)
    (V1.dlo i) (V1.dhi i) (V1.elo i) (V1.ehi i) (V1.flo i) (V1.fhi i)
  H_WIN0 : ∀ i, i < W → V0.dlo i ≤ V0.dhi i ∧ V0.elo i ≤ V0.ehi i ∧ V0.flo i ≤ V0.fhi i ∧ 1 ≤ V0.flo i
  H_WIN1 : ∀ i, i < W → V1.dlo i ≤ V1.dhi i ∧ V1.elo i ≤ V1.ehi i ∧ V1.flo i ≤ V1.fhi i ∧ 1 ≤ V1.flo i
  /-- **H_DATA_VALID**: the sender holds token `k` on `[dS k, dE k)`. -/
  H_DATA_VALID : ∀ k i t, i < W → dS k ≤ t → t < dE k → d i t = val k i
  /-- **H_DATA_LEAD** (rule A at the pipe input): data settled `Sdr` before
  (or `Lag` after) the request edge at stage 0's I0. -/
  H_DATA_LEAD : ∀ k, dS k + Sdr ≤ P.ρ (2 * k) + Lag
  /-- **H_DATA_REL**: the sender releases token `k` at least `Erel` after
  stage 0's node falls (its ack_in, incl. stage 0's DACK fall, + sender). -/
  H_DATA_REL : ∀ k, P.τ0 (2 * k + 1) + Erel ≤ dE k
  /-- **H_PW0**: stage 0's enable high time at bit `i` covers its spread plus
  one latch loop (no rule). -/
  H_PW0 : ∀ i, i < W → V0.ehi i + V0.fhi i ≤ P.L0.lo + max Es P.RT0 + V0.elo i
  /-- **H_SETUP0**: environment data is through stage 0's D arc and latch
  loop before stage 0 closes (rule I at the input boundary; "not audited"
  by tighten.py for data from a pin). -/
  H_SETUP0 : ∀ i, i < W → V0.dhi i + V0.fhi i + Lag ≤ Sdr + 2 * P.L0.lo + max Es P.RT0 + V0.elo i
  /-- **H_HOLD0** (rule H at the input boundary, stage 0's DACK): the
  released data reaches bit `i` no earlier than its enable fall. -/
  H_HOLD0 : ∀ i, i < W → V0.ehi i ≤ Erel + V0.dlo i
  /-- **H_PW1**: stage 1's enable high time (no rule). -/
  H_PW1 : ∀ i, i < W → V1.ehi i + V1.fhi i ≤ P.L1.lo + max Er P.RT1 + V1.elo i
  /-- **H_I1** (rule I at boundary 1, the SDELAY knob): stage 1 closes on
  the path stage-0 rise → ... → stage-0 fall → request line → stage-1 LUT
  → enable branch, no earlier than stage 0's latched value (its enable
  branch + latch, then stage 1's D arc and loop) has arrived. -/
  H_I1 : ∀ i, i < W → V0.ehi i + V1.dhi i + V1.fhi i ≤
    P.L0.lo + max Es P.RT0 + P.Rq.lo + P.L1.lo + V1.elo i
  /-- **H_I1_SRC**: the same for data that came straight through stage 0
  while it was transparent (the environment's own lead/lag). -/
  H_I1_SRC : ∀ i, i < W → V0.dhi i + V1.dhi i + V1.fhi i + Lag ≤
    Sdr + 2 * P.L0.lo + max Es P.RT0 + P.Rq.lo + P.L1.lo + V1.elo i
  /-- **H_H1** (rule H at boundary 1, stage 1's DACK): stage 1's latest
  enable fall at bit `i` is no later than stage 0's next value can reach it
  (DACK slow path + stage-0 LUT + stage-0 enable branch + stage-1 D arc). -/
  H_H1 : ∀ i, i < W → V1.ehi i ≤ max P.Ar.lo P.Af.lo + P.L0.lo + V0.elo i + V1.dlo i

section data
variable {P : P2} {rst r0 a0 O0 q0 r1 a1 O1 q1 : Trace} {w0l w0h w1l w1h Es Er : Nat}
  {d x0 x1 : Nat → Bundling.Sig} {val : Nat → Nat → Bool} {dS dE : Nat → Nat} {V0 V1 : Win}
  {W Erel Sdr Lag : Nat}
variable (G : Gates2 P rst r0 a0 O0 q0 r1 a1 O1 q1 w0l w0h w1l w1h)
  (E : Env2 P r0 a1 Es Er) (T : Timing2 P w0h w1h Es Er)
  (D : Data2 P O0 O1 d x0 x1 val dS dE V0 V1 W Es Er Erel Sdr Lag)
include G E T D

/-- **(2) Stage 0 latches every token.** -/
theorem token0 (k i : Nat) (hi : i < W) :
    ∀ t, max (P.τ0 (2 * k) + V0.ehi i) (dS k + V0.dhi i) ≤ t →
      t < P.τ0 (2 * k + 1 + 1) + V0.elo i → x0 i t = val k i := by
  have hn := nodes_clean G E T
  have hon : ∀ t, P.τ0 (2 * k) ≤ t → t < P.τ0 (2 * k + 1) → O0 t = true := by
    intro t a b; have := hn.2.1 (2 * k) t a b; rwa [Vph_even] at this
  have hoff : ∀ t, P.τ0 (2 * k + 1) ≤ t → t < P.τ0 (2 * k + 1 + 1) → O0 t = false := by
    intro t a b; have := hn.2.1 (2 * k + 1) t a b; rwa [Vph_odd] at this
  have ⟨hdw, hew, hfw, hpos⟩ := D.H_WIN0 i hi
  have g := gap0 E T (2 * k); have r := rho_le E T (2 * k); have l := D.H_DATA_LEAD k
  have pw := D.H_PW0 i hi; have su := D.H_SETUP0 i hi
  have rel := D.H_DATA_REL k; have ho := D.H_HOLD0 i hi
  exact Bundling.capture (d i) O0 (x0 i) _ _ _ _ _ _ (D.H_LATCH0 i hi) hdw hew hfw hpos
    (P.τ0 (2 * k)) (P.τ0 (2 * k + 1)) (P.τ0 (2 * k + 1 + 1)) (dS k) (dE k) (val k i)
    hon hoff (fun t h1 h2 => D.H_DATA_VALID k i t hi h1 h2) (by omega) (by omega)

/-- **(2') Stage 1 latches every token**, from stage 0's latched value. -/
theorem token1 (k i : Nat) (hi : i < W) :
    ∀ t, max (P.τ1 (2 * k) + V1.ehi i)
        (max (P.τ0 (2 * k) + V0.ehi i) (dS k + V0.dhi i) + V1.dhi i) ≤ t →
      t < P.τ1 (2 * k + 1 + 1) + V1.elo i → x1 i t = val k i := by
  have hn := nodes_clean G E T
  have hon : ∀ t, P.τ1 (2 * k) ≤ t → t < P.τ1 (2 * k + 1) → O1 t = true := by
    intro t a b; have := hn.2.2.2 (2 * k) t a b; rwa [Vph_even] at this
  have hoff : ∀ t, P.τ1 (2 * k + 1) ≤ t → t < P.τ1 (2 * k + 1 + 1) → O1 t = false := by
    intro t a b; have := hn.2.2.2 (2 * k + 1) t a b; rwa [Vph_odd] at this
  have ⟨hdw, hew, hfw, hpos⟩ := D.H_WIN1 i hi
  have g0 := gap0 E T (2 * k); have g1 := gap1 E T (2 * k)
  have f := fwd E T (2 * k + 1)
  have r := rho_le E T (2 * k); have l := D.H_DATA_LEAD k
  have b := back_odd E T (2 * k + 1) (by omega)
  have pw := D.H_PW1 i hi; have i1 := D.H_I1 i hi; have i2 := D.H_I1_SRC i hi
  have h1 := D.H_H1 i hi
  exact Bundling.capture (x0 i) O1 (x1 i) _ _ _ _ _ _ (D.H_LATCH1 i hi) hdw hew hfw hpos
    (P.τ1 (2 * k)) (P.τ1 (2 * k + 1)) (P.τ1 (2 * k + 1 + 1))
    (max (P.τ0 (2 * k) + V0.ehi i) (dS k + V0.dhi i)) (P.τ0 (2 * k + 1 + 1) + V0.elo i)
    (val k i) hon hoff (token0 G E T D k i hi) (by omega) (by omega)

/-- **(3) The pipe delivers every token.** The output `x1` carries token
`k`'s value at least until the receiver's acknowledge falls (`γ (2k+1)`),
and, under the output-bundling inequalities (the receiver's own rule:
next consumer's rule I, or B/D/E at an edge-sampling consumer, where the
request's lead over the data -- growing with depth -- appears as
`Rq.lo + L1.lo` against `ehi0 + dhi1`), from the receiver's acknowledge
rise `γ (2k)` on. -/
theorem pipe_forward (k i : Nat) (hi : i < W) :
    (∀ t, max (P.τ1 (2 * k) + V1.ehi i)
        (max (P.τ0 (2 * k) + V0.ehi i) (dS k + V0.dhi i) + V1.dhi i) ≤ t →
      t < P.γ (2 * k + 1) → x1 i t = val k i) ∧
    (V1.ehi i ≤ Er → V0.ehi i + V1.dhi i ≤ P.Rq.lo + P.L1.lo + Er →
      V0.dhi i + V1.dhi i + Lag ≤ Sdr + P.L0.lo + P.Rq.lo + P.L1.lo + Er →
      ∀ t, P.γ (2 * k) ≤ t → t < P.γ (2 * k + 1) → x1 i t = val k i) := by
  have g := gam_le E T (2 * k + 1)
  have rc := E.H_RCV (2 * k); have f := fwd E T (2 * k)
  have r := rho_le E T (2 * k); have l := D.H_DATA_LEAD k
  refine ⟨fun t h1 h2 => token1 G E T D k i hi t h1 (by omega), fun o1 o2 o3 t h1 h2 => ?_⟩
  exact token1 G E T D k i hi t (by omega) (by omega)

end data

/-! ## 8. Non-vacuity: a fixed-delay two-stage run satisfying every control hypothesis

All read-time maps are a fixed delay of 1 tick (LUTs, request line, both
acknowledge paths), feedback wires 1 tick, reset released at 4, sender and
receiver latency 3. Every phase lasts 4 ticks; every net is a square wave
`sq o` (low before `o`, then 4 high, 4 low, ...). The gate relations are
checked for ALL `t`. -/

namespace Wit

/-- Square wave: low before `o`, then high for 4, low for 4, ... -/
def sq (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 8 < 4)

theorem sq_shift (o d t : Nat) : sq (o + d) (t + d) = sq o t := by
  unfold sq
  have e : t + d - (o + d) = t - o := by omega
  rw [e]
  by_cases h : o ≤ t
  · have h' : o + d ≤ t + d := by omega
    simp [h, h']
  · have h' : ¬ (o + d ≤ t + d) := by omega
    simp [h, h']

theorem sq_pre (o t : Nat) (h : t < o) : sq o t = false := by
  unfold sq; simp; omega

theorem sq_phase (o j t : Nat) (h1 : o + 4 * j ≤ t) (h2 : t < o + 4 * (j + 1)) :
    sq o t = Vph j := by
  unfold sq Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 8 < 4 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 8 < 4) := by omega
    simp [hj, this]

def rstW (t : Nat) : Bool := decide (t < 4)

/-- The real `bd_c2n` excitation of square waves offset by 0 (request),
+2 (own feedback) and +4 (acknowledge) is the request wave itself. -/
theorem key (o s : Nat) (ho : 4 ≤ o) :
    ex (sq o) (sq (o + 4)) (sq (o + 2)) rstW s = sq o s := by
  unfold ex rstW
  rw [CElemTiming.c2n_eq]
  by_cases h0 : s < o
  · rw [sq_pre o s h0, sq_pre (o + 4) s (by omega), sq_pre (o + 2) s (by omega)]
    cases decide (s < 4) <;> rfl
  · have hr : decide (s < 4) = false := by simp; omega
    rw [hr]
    have hm : (s - o) % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases hA : (s - o) % 8 < 4
    · have e1 : sq o s = true := by unfold sq; simp; omega
      by_cases hB : s < o + 4
      · have e2 : sq (o + 4) s = false := sq_pre _ _ hB
        rw [e1, e2]; cases sq (o + 2) s <;> rfl
      · have e2 : sq (o + 4) s = false := by unfold sq; simp; omega
        rw [e1, e2]; cases sq (o + 2) s <;> rfl
    · have e1 : sq o s = false := by unfold sq; simp; omega
      have e2 : sq (o + 4) s = true := by unfold sq; simp; omega
      rw [e1, e2]; cases sq (o + 2) s <;> rfl

theorem shift_σ (d t : Nat) : (Ret.shift d).σ t = t - d := rfl

/-- The witness run. -/
def Pw : P2 where
  R := 4
  L0 := Ret.shift 1
  L1 := Ret.shift 1
  Rq := Ret.shift 1
  Ar := Ret.shift 1
  Af := Ret.shift 1
  ρ j := 4 + 4 * j
  γ j := 10 + 4 * j

theorem fst1 (c : Nat) (h : 1 ≤ c) : (Ret.shift 1).fst c = c + 1 := Ret.fst_shift 1 c h

theorem cc_w : ∀ j, Pw.cc j = (4 + 4 * j, 6 + 4 * j) := by
  intro j
  induction j with
  | zero =>
    show (max 4 4, max ((Ret.shift 1).fst ((Ret.shift 1).fst (max 4 4))) 4) = _
    rw [show max 4 4 = 4 from rfl, fst1 4 (by omega), fst1 5 (by omega)]; rfl
  | succ j ih =>
    show (max (4 + 4 * (j + 1)) (Pw.ackT j ((Ret.shift 1).fst (Pw.cc j).2)),
      max ((Ret.shift 1).fst ((Ret.shift 1).fst
        (max (4 + 4 * (j + 1)) (Pw.ackT j ((Ret.shift 1).fst (Pw.cc j).2))))) (10 + 4 * j)) = _
    have ha : Pw.ackT j ((Ret.shift 1).fst (Pw.cc j).2) = 8 + 4 * j := by
      rw [ih]; simp only
      rw [fst1 _ (by omega)]
      show (if j % 2 = 0 then min ((Ret.shift 1).fst _) ((Ret.shift 1).fst _)
        else max ((Ret.shift 1).fst _) ((Ret.shift 1).fst _)) = _
      rw [fst1 _ (by omega)]
      split <;> omega
    rw [ha, show max (4 + 4 * (j + 1)) (8 + 4 * j) = 8 + 4 * j by omega,
      fst1 (8 + 4 * j) (by omega), fst1 (8 + 4 * j + 1) (by omega)]
    simp only [Prod.mk.injEq]; omega

theorem τ0_w (j : Nat) : Pw.τ0 j = 5 + 4 * j := by
  show (Ret.shift 1).fst (Pw.cc j).1 = _
  rw [cc_w, fst1 _ (by omega)]; omega

theorem τ1_w (j : Nat) : Pw.τ1 j = 7 + 4 * j := by
  show (Ret.shift 1).fst (Pw.cc j).2 = _
  rw [cc_w, fst1 _ (by omega)]; omega

theorem gates_w :
    Gates2 Pw rstW (sq 4) (sq 8) (sq 5) (sq 6) (sq 6) (sq 10) (sq 7) (sq 8) 1 1 1 1 where
  H_RST _ := rfl
  H_CTL0 :=
    { H_LUT_FIFO := fun t ht => by
        show sq 5 t = ex (sq 4) (sq 8) (sq 6) rstW (t - 1)
        rw [key 4 (t - 1) (by omega)]
        have := sq_shift 4 1 (t - 1); rw [Nat.sub_add_cancel (by exact ht)] at this; exact this
      H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
        (fun t => sq_shift 5 1 t)
      H_LOOP_POS := by decide }
  H_CTL1 :=
    { H_LUT_FIFO := fun t ht => by
        show sq 7 t = ex (sq 6) (sq 10) (sq 8) rstW (t - 1)
        rw [key 6 (t - 1) (by omega)]
        have := sq_shift 6 1 (t - 1); rw [Nat.sub_add_cancel (by exact ht)] at this; exact this
      H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
        (fun t => sq_shift 7 1 t)
      H_LOOP_POS := by decide }
  H_REQ_LINE t ht := by
    show sq 6 t = sq 5 (t - 1)
    have := sq_shift 5 1 (t - 1); rw [Nat.sub_add_cancel (by exact ht)] at this; exact this
  H_ACK_LINE t ht := by
    show sq 8 t = (sq 7 (t - 1) || sq 7 (t - 1))
    have := sq_shift 7 1 (t - 1)
    rw [Nat.sub_add_cancel (by simp only [Pw, Ret.shift] at ht; omega)] at this
    rw [Bool.or_self]; exact this

theorem env_w : Env2 Pw (sq 4) (sq 10) 3 3 where
  H_REQ_LOW0 t h1 h2 := by simp only [Pw] at h1 h2; omega
  H_REQ j t h1 h2 := sq_phase 4 j t h1 (by simp only [Pw] at h2; omega)
  H_ACK_LOW0 t h1 h2 := sq_pre 10 t h2
  H_ACK j t h1 h2 := sq_phase 10 j t h1 (by simp only [Pw] at h2; omega)
  H_SND j := by rw [τ0_w]; show 5 + 4 * j + 3 ≤ 4 + 4 * (j + 1); omega
  H_RCV j := by rw [τ1_w]; show 7 + 4 * j + 3 ≤ 10 + 4 * j; omega
  H_RST_EARLY := by decide

theorem timing_w : Timing2 Pw 1 1 3 3 where
  H_R_POS := by decide
  H_RST_LONG := by decide
  H_RST_LINES := by decide
  H_LAT0 := by decide
  H_LAT1 := by decide
  H_ACK_FLUSH := by decide

/-- **Non-vacuity of the control contract.** A concrete run satisfies every
field of `Gates2`, `Env2` and `Timing2` at every instant; its nodes are not
constant (they alternate every 4 ticks), so `pipe_ctl` and `nodes_clean`
speak about a real, live two-stage handshake. -/
theorem witness :
    Gates2 Pw rstW (sq 4) (sq 8) (sq 5) (sq 6) (sq 6) (sq 10) (sq 7) (sq 8) 1 1 1 1 ∧
    Env2 Pw (sq 4) (sq 10) 3 3 ∧ Timing2 Pw 1 1 3 3 ∧
    (∀ j, Pw.τ0 j = 5 + 4 * j ∧ Pw.τ1 j = 7 + 4 * j) ∧
    sq 5 5 = true ∧ sq 5 9 = false ∧ sq 7 7 = true ∧ sq 7 11 = false :=
  ⟨gates_w, env_w, timing_w, fun j => ⟨τ0_w j, τ1_w j⟩, rfl, rfl, rfl, rfl⟩

/-! ### The data path of the witness

One bit (`W = 1`), token values alternating (`val k = (k even)`: never the
reset value for every token, so a stuck latch cannot pass). The sender puts
token `k` on its net on `[2 + 8k, 10 + 8k)` (`Sdr = 2` before its request,
released 1 tick after stage 0's node falls). Both latch bits are the real
`ODD` INIT (`B8B8...`) as transport LUTs with every pin delay 1, so 6c's
`odd_latch` gives their `LatchRel`. Their outputs in closed form: stage 0
shows token `m` on `[6 + 8m, 14 + 8m)`, stage 1 on `[8 + 8m, 16 + 8m)`. -/

def dW (t : Nat) : Bool := decide ((t - 2) % 16 < 8)
def x0W (t : Nat) : Bool := decide (6 ≤ t ∧ (t - 6) % 16 < 8)
def x1W (t : Nat) : Bool := decide (8 ≤ t ∧ (t - 8) % 16 < 8)
def valW (k _ : Nat) : Bool := decide (k % 2 = 0)
def dSW (k : Nat) : Nat := 2 + 8 * k
def dEW (k : Nat) : Nat := 10 + 8 * k
def VW : Win := ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1⟩

theorem x0_rel (t : Nat) :
    x0W t = (if sq 5 (t - 1) then dW (t - 1) else x0W (t - 1)) := by
  split
  · next h =>
    unfold sq at h; simp at h
    unfold x0W dW; simp only [decide_eq_decide]; omega
  · next h =>
    unfold sq at h; simp at h
    unfold x0W; simp only [decide_eq_decide]; omega

theorem x1_rel (t : Nat) :
    x1W t = (if sq 7 (t - 1) then x0W (t - 1) else x1W (t - 1)) := by
  split
  · next h =>
    unfold sq at h; simp at h
    unfold x0W x1W; simp only [decide_eq_decide]; omega
  · next h =>
    unfold sq at h; simp at h
    unfold x1W; simp only [decide_eq_decide]; omega

/-- A transport ODD latch with unit pin delays is a 6c `LatchRel`. -/
theorem latch_of (dd en q : Bundling.Sig)
    (h : ∀ t, q t = (if en (t - 1) then dd (t - 1) else q (t - 1))) :
    Bundling.LatchRel dd en q 1 1 1 1 1 1 := by
  apply Bundling.odd_latch
  apply Bundling.transport_gate Bundling.ODD
    [(dd, 1, 1, 1), (en, 1, 1, 1), (q, 1, 1, 1), (Bundling.zero, 0, 0, 0),
     (Bundling.zero, 0, 0, 0), (Bundling.zero, 0, 0, 0)] q (by simp)
  intro t
  show q t = lutB Bundling.ODD [dd (t - 1), en (t - 1), q (t - 1), false, false, false]
  rw [Bundling.odd_bin]; exact h t

set_option linter.unusedSimpArgs false in
theorem data_w : Data2 Pw (sq 5) (sq 7) (fun _ => dW) (fun _ => x0W) (fun _ => x1W)
    valW dSW dEW VW VW 1 3 3 1 2 0 where
  H_LATCH0 _ _ := latch_of dW (sq 5) x0W x0_rel
  H_LATCH1 _ _ := latch_of x0W (sq 7) x1W x1_rel
  H_WIN0 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_WIN1 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_DATA_VALID k i t _ h1 h2 := by
    unfold dSW at h1; unfold dEW at h2; unfold dW valW
    simp only [decide_eq_decide]; omega
  H_DATA_LEAD k := by show 2 + 8 * k + 2 ≤ 4 + 4 * (2 * k) + 0; omega
  H_DATA_REL k := by rw [τ0_w]; show 5 + 4 * (2 * k + 1) + 1 ≤ 10 + 8 * k; omega
  H_PW0 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_SETUP0 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_HOLD0 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_PW1 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_I1 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_I1_SRC _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]
  H_H1 _ _ := by simp [VW, Pw, Ret.shift, P2.RT0, P2.RT1, P2.alo]

/-- **Non-vacuity, data side, and the theorem at work.** The witness run
satisfies `Data2` too, so `pipe_forward` applies to it: the pipe's output
bit carries token `k`'s value from the receiver's acknowledge rise to its
fall, for EVERY token; the values alternate (token 0 high, token 1 low). -/
theorem witness_data :
    Data2 Pw (sq 5) (sq 7) (fun _ => dW) (fun _ => x0W) (fun _ => x1W)
      valW dSW dEW VW VW 1 3 3 1 2 0 ∧
    (∀ k t, Pw.γ (2 * k) ≤ t → t < Pw.γ (2 * k + 1) → x1W t = decide (k % 2 = 0)) ∧
    x1W 10 = true ∧ x1W 18 = false := by
  refine ⟨data_w, fun k t h1 h2 => ?_, rfl, rfl⟩
  exact (pipe_forward gates_w env_w timing_w data_w k 0 (by omega)).2
    (by decide) (by decide) (by decide) t h1 h2

end Wit

end Formal.Cells.PipeTimed
