import Formal.Core.Delay.GLSFid
import Formal.Cells.CElemTiming

/-!
# The trace semantics of research's `FID_RESOLVE` on the bd_c2 feedback loop

Source, read-only: `origin/claude/research` at `6524fa3`, `cells/gls/fid_core.vh` (written
`R:fid_core.vh:<line>`), `cells/gls/gen.py` (`R:gen.py:<line>`). Probe GLSResolve, shard A;
notes in `formal/notes/A-gls-resolve.md`. Core Lean only (no Mathlib).

## What is modelled

`FID_RESOLVE` (`R:fid_core.vh:47-119`) with `en = 1`, `TLOOP = L ≥ 1`, `+META_OFF` unset,
`+META_X` unset (`xmode = 0`), on binary values, as a per-step state machine on end-of-step
values (one step = 1 ps, `timescale 1ps/1ps`):

* the state is the module's registers `o_r`, `busy`, `v_before`, `t_last`, `ign_until` and the
  one pending non-blocking update `o_r <= #(trp) choose; busy <= #(trp) 1'b0` (`:108-109`);
* each step first runs the `always @(f or kick)` body (`:71-118`) once with the step's `f`, then
  applies the pending update if it is due this step (`nba`). This is the Verilog order: `f` is
  written by `FID_SAMPLE` in the active region (`:125-130`), the `<= #trp` updates land in the
  NBA region. The `kick` re-evaluation (`:90,110`) is subsumed: evaluating the body at EVERY
  step is the same as evaluating it on `f` events and kicks, because after every evaluation
  that is not blocked, `o_r = f` (or the node is busy), so a step with no `f` event and no kick
  is a no-op; the kick lands exactly at `ign_until`, where `$time < ign_until` is false
  (`:74,89-90,107,110`). (A modelling argument, cross-checked with iverilog in the notes.)
* the noise `$dist_normal(seed, 0, win/4)` (`:81`) is a free function `nz : Nat → Int` of the
  decision time (at most one decision per step); the resolution time
  `trp = min(40 τ, rtoi(τ ln(win / 2|δ|)))` if `2|δ| < win`, else `0` (`:93-98`), is a free
  function `R : Int → Nat` of `δ`; where its value matters we only use `ResLaw`
  (`trp = 0` when `2|δ| ≥ win`, which is `:98`). Every theorem holds for every `nz` and `R`,
  so for every seed and every `τ`; existence statements ("some draw gives ...") treat the
  Gaussian draw as free (it has full support; the PRNG is not modelled).
* the single-cell loop (gen.py: a LUT output routed back into one of its own pins,
  `R:gen.py:661-682`): `f t = F(pins at t, o (t - L))` with `L = TLOOP` = feedback wire + the
  feedback pin's arc (`R:gen.py:678`). With `FID_LEVEL_PS = 0` the fid LUT's pin delay is the
  arc exactly (`GLSFid.fidO6_default`), so the feedback is `o` delayed by exactly `TLOOP`
  (ICBUF `W` + copy `T - 1` + sampler `1`). The other pins are given as the traces the mux
  sees (already delayed by their arcs).

## What is not modelled
X (the time-0 window, `+META_X=1`), `FID_LEVEL_PS ≠ 0` (then the loop delay differs from
TLOOP), loops through more than one cell (gen.py does not detect them, `R:gen.py:664`), the
Gaussian distribution itself, real time.
-/

namespace Formal.Core.GLSResolve

open Formal.Core.GLSFid (Res resolve lut6)

abbrev Sig := Nat → Bool

/-! ## 0. Causal recursion (existence and uniqueness of runs) -/

/-- The solution of a causal recursion `x t = G t x`. -/
def cr {α : Type} [Inhabited α] (G : Nat → (Nat → α) → α) : Nat → α
  | t => G t (fun u => if u < t then cr G u else default)
termination_by t => t
decreasing_by all_goals (simp_wf; omega)

/-- `G` reads only the strict past. -/
def Causal {α : Type} (G : Nat → (Nat → α) → α) : Prop :=
  ∀ t (h h' : Nat → α), (∀ u, u < t → h u = h' u) → G t h = G t h'

theorem cr_eq {α : Type} [Inhabited α] {G : Nat → (Nat → α) → α} (hG : Causal G) (t : Nat) :
    cr G t = G t (cr G) := by
  rw [cr]; apply hG; intro u hu; simp [hu]

theorem cr_unique {α : Type} {G : Nat → (Nat → α) → α} (hG : Causal G) {x y : Nat → α}
    (hx : ∀ t, x t = G t x) (hy : ∀ t, y t = G t y) : ∀ t, x t = y t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih => rw [hx t, hy t]; exact hG t x y ih

/-! ## 1. The resolver (R:fid_core.vh:47-119) -/

/-- The resolver's registers (binary, `xmode = 0`). `tl = 0` is "no last edge" (`t_last > 0`
test, `:78`); `pt`/`pv` are the pending `o_r <= #(trp) choose` (`:108`), live while `busy`. -/
structure St where
  o : Bool
  busy : Bool
  vb : Bool
  tl : Nat
  ign : Nat
  pt : Nat
  pv : Bool
  deriving DecidableEq

instance : Inhabited St := ⟨⟨false, false, false, 0, 0, 0, false⟩⟩

/-- Power-up state after a quiet reset at value `v` (`busy = 0`, `t_last = 0`, `:56-57`;
`o_r` and `v_before` start at `x` in Verilog, here at the settled value `v`). -/
def St.init (v : Bool) : St := ⟨v, false, v, 0, 0, 0, v⟩

/-- Resolver parameters: `L = TLOOP`, `win = WIN`, noise draws `nz`, resolution-time law `R`. -/
structure Prm where
  L : Nat
  win : Int
  nz : Nat → Int
  R : Int → Nat

/-- `delta` (`:82`). -/
def Prm.delta (p : Prm) (w : Nat) (t : Nat) : Int := (w : Int) - ((p.L : Int) - p.win / 2) + p.nz t

/-- The runt test (`:77-78`), binary. -/
def isRunt (p : Prm) (t : Nat) (f : Bool) (s : St) : Bool :=
  f != s.o && decide (0 < s.tl) && f == s.vb && decide (t - s.tl < p.L)

/-- Blocked: `busy || $time < ign_until` (`:74`). -/
def blocked (t : Nat) (s : St) : Bool := s.busy || decide (t < s.ign)

/-- The body of `always @(f or kick)` (`:71-118`) at time `t` with input `f`. -/
def eval (p : Prm) (t : Nat) (f : Bool) (s : St) : St :=
  if blocked t s then s                                           -- :74-75
  else if f == s.o then s                                         -- :76
  else if isRunt p t f s then
    let w := t - s.tl                                             -- :79
    match resolve (w : Int) (p.L : Int) p.win (p.nz t) with
    | .reject => { s with o := f, tl := 0, ign := t + p.L + 1 }   -- :83-90
    | .commit =>                                                  -- :91-110, choose = runt_val
      { s with o := f, busy := true, tl := 0, ign := t + p.R (p.delta w t) + p.L + 1,
               pt := t + p.R (p.delta w t), pv := s.o }
    | .back =>                                                    -- choose = f
      { s with o := f, busy := true, tl := 0, ign := t + p.R (p.delta w t) + p.L + 1,
               pt := t + p.R (p.delta w t), pv := f }
  else { s with vb := s.o, o := f, tl := t }                      -- :112-115

/-- The pending NBA `o_r <= #(trp) choose; busy <= #(trp) 0` lands (`:108-109`). -/
def nba (t : Nat) (s : St) : St :=
  if s.busy && s.pt == t then { s with o := s.pv, busy := false } else s

/-- One step: the body, then the step's NBA region. -/
def step (p : Prm) (t : Nat) (f : Bool) (s : St) : St := nba t (eval p t f s)

/-- `ResLaw`: `trp = 0` when `2|δ| ≥ win` (`:93-98`, `ad ≥ 1` clamp included). -/
def ResLaw (p : Prm) : Prop := ∀ d : Int, p.win ≤ 2 * d → p.R d = 0

/-! ## 2. The bd_c2 cell and the closed loop -/

/-- `bd_c2`, verbatim from `cells/rtl/bd_ce.v:34` (the same constant as
`Gen/Cells.lean:29`, generated from yosys, and B's `CElemTiming.INIT_c2`). -/
def INIT_c2 : Nat := 0x00E800E800E800E8

/-- Pin map of `bd_c2`: `I0 = a, I1 = b, I2 = q, I3 = rst, I4 = I5 = 0` (`bd_ce.v:34-35`). -/
def pins (a b q r : Bool) : Nat → Bool
  | 0 => a | 1 => b | 2 => q | 3 => r | _ => false

/-- The fid LUT function of bd_c2 (the fid mux tree `GLSFid.lut6` on the real INIT). -/
def fC2 (a b q r : Bool) : Bool := lut6 INIT_c2 (pins a b q r)

theorem fC2_eq (a b q r : Bool) :
    fC2 a b q r = (!r && ((a && b) || (a && q) || (b && q))) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- The fid mux tree and B's `Prelim.lutB` agree on bd_c2. -/
theorem fC2_eq_exc (a b q r : Bool) :
    fC2 a b q r = Formal.Cells.CElemTiming.exc Formal.Cells.CElemTiming.INIT_c2 a b q r := by
  rw [fC2_eq, Formal.Cells.CElemTiming.c2_eq]

/-- The closed loop's step function. `a b rst` are the pin traces the mux sees. -/
def G (p : Prm) (a b rst : Sig) (v0 : Bool) : Nat → (Nat → St) → St
  | 0, _ => St.init v0
  | t + 1, h => step p (t + 1) (fC2 (a (t + 1)) (b (t + 1)) (h (t + 1 - p.L)).o (rst (t + 1))) (h t)

/-- **A resolver run of the bd_c2 loop**: `st 0` is the reset state, and every step is the
resolver fed with the LUT function of the pins and of its own output `TLOOP` ago. -/
def Run (p : Prm) (a b rst : Sig) (v0 : Bool) (st : Nat → St) : Prop :=
  ∀ t, st t = G p a b rst v0 t st

theorem G_causal (p : Prm) (a b rst : Sig) (v0 : Bool) (hL : 1 ≤ p.L) :
    Causal (G p a b rst v0) := by
  intro t h h' e
  cases t with
  | zero => rfl
  | succ t => simp only [G]; rw [e t (by omega), e (t + 1 - p.L) (by omega)]

/-- Runs exist and are unique (deterministic given the noise and the law). -/
theorem run_exists (p : Prm) (a b rst : Sig) (v0 : Bool) (hL : 1 ≤ p.L) :
    Run p a b rst v0 (cr (G p a b rst v0)) := cr_eq (G_causal p a b rst v0 hL)

theorem run_unique {p : Prm} {a b rst : Sig} {v0 : Bool} (hL : 1 ≤ p.L) {x y : Nat → St}
    (hx : Run p a b rst v0 x) (hy : Run p a b rst v0 y) : ∀ t, x t = y t :=
  cr_unique (G_causal p a b rst v0 hL) hx hy

theorem Run.zero {p : Prm} {a b rst : Sig} {v0 : Bool} {st : Nat → St}
    (h : Run p a b rst v0 st) : st 0 = St.init v0 := h 0

theorem Run.succ {p : Prm} {a b rst : Sig} {v0 : Bool} {st : Nat → St}
    (h : Run p a b rst v0 st) (t : Nat) :
    st (t + 1) = step p (t + 1) (fC2 (a (t + 1)) (b (t + 1)) (st (t + 1 - p.L)).o (rst (t + 1)))
      (st t) := h (t + 1)

/-! ## 3. Basic step facts -/

theorem nba_idle {t : Nat} {s : St} (h : s.busy = false) : nba t s = s := by
  simp [nba, h]

theorem eval_blocked {p : Prm} {t : Nat} {f : Bool} {s : St} (h : blocked t s = true) :
    eval p t f s = s := by simp [eval, h]

theorem eval_same {p : Prm} {t : Nat} {f : Bool} {s : St} (h : f = s.o) : eval p t f s = s := by
  simp [eval, h]

/-- An edge that is not a runt is copied to the output in the same step (`:112-115`). -/
theorem eval_edge {p : Prm} {t : Nat} {f : Bool} {s : St} (hb : blocked t s = false)
    (hf : f ≠ s.o) (hr : isRunt p t f s = false) :
    eval p t f s = { s with vb := s.o, o := f, tl := t } := by
  have : (f == s.o) = false := by cases f <;> cases ho : s.o <;> simp_all
  simp [eval, hb, this, hr]

/-- At a runt, `eval` is the decision of `GLSFid.resolve` on `w = t - t_last`. -/
theorem eval_runt {p : Prm} {t : Nat} {f : Bool} {s : St} (hb : blocked t s = false)
    (hf : f ≠ s.o) (hr : isRunt p t f s = true) :
    eval p t f s =
      match resolve ((t - s.tl : Nat) : Int) (p.L : Int) p.win (p.nz t) with
      | .reject => { s with o := f, tl := 0, ign := t + p.L + 1 }
      | .commit =>
        { s with o := f, busy := true, tl := 0, ign := t + p.R (p.delta (t - s.tl) t) + p.L + 1,
                 pt := t + p.R (p.delta (t - s.tl) t), pv := s.o }
      | .back =>
        { s with o := f, busy := true, tl := 0, ign := t + p.R (p.delta (t - s.tl) t) + p.L + 1,
                 pt := t + p.R (p.delta (t - s.tl) t), pv := f } := by
  have : (f == s.o) = false := by cases f <;> cases ho : s.o <;> simp_all
  simp only [eval, hb, this, hr]; rfl

/-! ## 4. (1) What fanout sees: a runt on the bd_c2 loop, every width, every draw

The C-element with `a = 1`, `rst = 0`, empty (`q = 0`), and a pulse on `b` of width `w`
starting at `t0` (as seen by the mux). `C(1, b) = b ∨ q`, so the pulse sets the loop. -/

def aOne : Sig := fun _ => true
def rstZero : Sig := fun _ => false
/-- `b` = 1 exactly on `[t0, t0 + w)`. -/
def bPulse (t0 w : Nat) : Sig := fun t => decide (t0 ≤ t ∧ t < t0 + w)

theorem fC2_or (b q : Bool) : fC2 true b q false = (b || q) := by
  cases b <;> cases q <;> decide

/-- The state after the first edge (`:112-115` at `t0`). -/
def S1 (t0 : Nat) : St := ⟨true, false, false, t0, 0, 0, false⟩

/-- Closed form of the run for a pulse at least as wide as the loop. -/
def Swide (t0 : Nat) (t : Nat) : St := if t < t0 then St.init false else S1 t0

/-- Closed form of the run for a runt (`w < L`): the decision is taken at `tr = t0 + w`
with outcome `resolve w L win (nz tr)`, resolution time `trp = R δ`. -/
def Srunt (p : Prm) (t0 w : Nat) (t : Nat) : St :=
  if t < t0 then St.init false
  else if t < t0 + w then S1 t0
  else match resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) with
    | .reject => ⟨false, false, false, 0, t0 + w + p.L + 1, 0, false⟩
    | .commit => ⟨decide (t0 + w + p.R (p.delta w (t0 + w)) ≤ t),
        decide (t < t0 + w + p.R (p.delta w (t0 + w))), false, 0,
        t0 + w + p.R (p.delta w (t0 + w)) + p.L + 1, t0 + w + p.R (p.delta w (t0 + w)), true⟩
    | .back => ⟨false, decide (t < t0 + w + p.R (p.delta w (t0 + w))), false, 0,
        t0 + w + p.R (p.delta w (t0 + w)) + p.L + 1, t0 + w + p.R (p.delta w (t0 + w)), false⟩

theorem run_wide {p : Prm} {t0 w : Nat} {st : Nat → St} (hL : 1 ≤ p.L) (ht0 : 1 ≤ t0)
    (hw : p.L ≤ w) (h : Run p aOne (bPulse t0 w) rstZero false st) :
    ∀ t, st t = Swide t0 t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    cases t with
    | zero => rw [h.zero]; simp [Swide, show 0 < t0 by omega]
    | succ t =>
      rw [h.succ t, ih t (by omega), ih (t + 1 - p.L) (by omega)]
      simp only [aOne, rstZero, fC2_or, bPulse]
      by_cases h1 : t + 1 < t0
      · have h2 : t < t0 := by omega
        have h3 : t + 1 - p.L < t0 := by omega
        simp [Swide, h1, h2, h3, step, eval, blocked, St.init, nba]
      · by_cases h2 : t + 1 = t0
        · subst h2
          have h3 : t + 1 - p.L < t + 1 := by omega
          simp [Swide, h3, step, eval, blocked, St.init, nba, isRunt, S1,
            show 0 < w by omega]
        · have h3 : ¬ t < t0 := by omega
          have hf : (decide (t0 ≤ t + 1 ∧ t + 1 < t0 + w) || (Swide t0 (t + 1 - p.L)).o) = true := by
            by_cases h4 : t + 1 < t0 + w
            · simp [show t0 ≤ t + 1 by omega, h4]
            · have : ¬ (t + 1 - p.L < t0) := by omega
              simp [Swide, this, S1]
          rw [hf]
          simp [Swide, h1, h3, step, eval, blocked, nba, S1]

theorem nba_c (t T' I : Nat) :
    nba (t + 1) ⟨decide (T' ≤ t), decide (t < T'), false, 0, I, T', true⟩ =
      ⟨decide (T' ≤ t + 1), decide (t + 1 < T'), false, 0, I, T', true⟩ := by
  unfold nba
  by_cases h : t + 1 = T'
  · subst h; simp
  · by_cases h' : t < T'
    · have : t + 1 < T' := by omega
      simp [h', this, show ¬ T' ≤ t by omega, show ¬ T' ≤ t + 1 by omega, show T' ≠ t + 1 by omega]
    · simp [h', show T' ≤ t by omega, show T' ≤ t + 1 by omega, show ¬ t + 1 < T' by omega]

theorem nba_b (t T' I : Nat) :
    nba (t + 1) ⟨false, decide (t < T'), false, 0, I, T', false⟩ =
      ⟨false, decide (t + 1 < T'), false, 0, I, T', false⟩ := by
  unfold nba
  by_cases h : t + 1 = T'
  · subst h; simp
  · by_cases h' : t < T'
    · have : t + 1 < T' := by omega
      simp [h', this, show T' ≠ t + 1 by omega]
    · simp [h', show ¬ t + 1 < T' by omega]

/-- End of the ignore window after the decision at `t0 + w` (`:89,107`): `ign_until`. -/
def Iend (p : Prm) (t0 w : Nat) : Nat :=
  t0 + w + (match resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) with
    | .reject => 0 | _ => p.R (p.delta w (t0 + w))) + p.L + 1

/-- **The runt run, exactly**, for every noise draw and every resolution-time law. `b` is the
pulse `[t0, t0 + w)` up to the decision, ARBITRARY inside the ignore window
`(t0 + w, Iend)`, and `0` from `Iend` on. Every run is `Srunt`: the window's input changes
leave no trace at all. -/
theorem run_runt_gen {p : Prm} {t0 w : Nat} {b : Sig} {st : Nat → St} (hL : 1 ≤ p.L)
    (ht0 : 1 ≤ t0) (hw1 : 1 ≤ w) (hw : w < p.L)
    (hb1 : ∀ t, t ≤ t0 + w → b t = bPulse t0 w t) (hb2 : ∀ t, Iend p t0 w ≤ t → b t = false)
    (h : Run p aOne b rstZero false st) :
    ∀ t, st t = Srunt p t0 w t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    cases t with
    | zero => rw [h.zero]; simp [Srunt, show 0 < t0 by omega]
    | succ t =>
      rw [h.succ t, ih t (by omega), ih (t + 1 - p.L) (by omega)]
      simp only [aOne, rstZero, fC2_or]
      by_cases h1 : t + 1 < t0
      · have h2 : t < t0 := by omega
        have h3 : t + 1 - p.L < t0 := by omega
        rw [hb1 (t + 1) (by omega)]
        simp [bPulse, Srunt, h1, h2, h3, step, eval, blocked, St.init, nba]
      · by_cases h2 : t + 1 = t0
        · subst h2
          have h3 : t + 1 - p.L < t + 1 := by omega
          rw [hb1 (t + 1) (by omega)]
          simp [bPulse, Srunt, h3, step, eval, blocked, St.init, nba, isRunt, S1,
            show 0 < w by omega]
        · by_cases h4 : t + 1 < t0 + w
          · have h3 : t + 1 - p.L < t0 := by omega
            rw [hb1 (t + 1) (by omega)]
            simp [bPulse, Srunt, h1, h3, h4, show ¬ t < t0 by omega, show t < t0 + w by omega,
              step, eval, blocked, nba, S1, show t0 ≤ t + 1 by omega]
          · by_cases h5 : t + 1 = t0 + w
            · -- the decision step
              have h3 : t + 1 - p.L < t0 := by omega
              have hst : Srunt p t0 w t = S1 t0 := by
                simp [Srunt, show ¬ t < t0 by omega, show t < t0 + w by omega]
              have hq : Srunt p t0 w (t + 1 - p.L) = St.init false := by simp [Srunt, h3]
              rw [hb1 (t + 1) (by omega), hst, hq, h5]
              have hf : (bPulse t0 w (t0 + w) || (St.init false).o) = false := by
                simp [bPulse, St.init]
              rw [hf]
              have hr : isRunt p (t0 + w) false (S1 t0) = true := by
                simp [isRunt, S1, show 0 < t0 by omega]; omega
              have hwe : t0 + w - (S1 t0).tl = w := by simp [S1]
              unfold step
              rw [eval_runt (by simp [blocked, S1]) (by simp [S1]) hr, hwe]
              cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) with
              | reject => simp [Srunt, hres, nba, S1, show ¬ t0 + w < t0 by omega]
              | commit =>
                simp only [Srunt, hres, show ¬ t0 + w < t0 by omega,
                  show ¬ t0 + w < t0 + w by omega, ite_false]
                by_cases hz : p.R (p.delta w (t0 + w)) = 0
                · simp [nba, S1, hz]
                · simp [nba, S1, hz]; omega
              | back =>
                simp only [Srunt, hres, show ¬ t0 + w < t0 by omega,
                  show ¬ t0 + w < t0 + w by omega, ite_false]
                by_cases hz : p.R (p.delta w (t0 + w)) = 0
                · simp [nba, S1, hz]
                · simp [nba, S1, hz]; omega
            · -- after the decision
              have h6 : t0 + w < t + 1 := by omega
              cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) with
              | reject =>
                have hIe : Iend p t0 w = t0 + w + p.L + 1 := by simp [Iend, hres]
                have hS : ∀ u, t0 + w ≤ u → Srunt p t0 w u =
                    ⟨false, false, false, 0, t0 + w + p.L + 1, 0, false⟩ := by
                  intro u hu
                  simp [Srunt, hres, show ¬ u < t0 by omega, show ¬ u < t0 + w by omega]
                rw [hS t (by omega), hS (t + 1) (by omega)]
                by_cases hI : t + 1 < t0 + w + p.L + 1
                · simp [step, eval, blocked, hI, nba]
                · rw [hS (t + 1 - p.L) (by omega), hb2 (t + 1) (by omega)]
                  simp [step, eval, blocked, hI, nba]
              | commit =>
                have hIe : Iend p t0 w = t0 + w + p.R (p.delta w (t0 + w)) + p.L + 1 := by
                  simp [Iend, hres]
                generalize hT : p.R (p.delta w (t0 + w)) = T at hIe
                have hS : ∀ u, t0 + w ≤ u → Srunt p t0 w u =
                    ⟨decide (t0 + w + T ≤ u), decide (u < t0 + w + T), false, 0,
                      t0 + w + T + p.L + 1, t0 + w + T, true⟩ := by
                  intro u hu
                  simp [Srunt, hres, hT, show ¬ u < t0 by omega, show ¬ u < t0 + w by omega]
                rw [hS t (by omega), hS (t + 1) (by omega)]
                unfold step
                by_cases hI : t + 1 < t0 + w + T + p.L + 1
                · rw [eval_blocked (by simp [blocked, hI])]; exact nba_c t _ _
                · rw [hS (t + 1 - p.L) (by omega), hb2 (t + 1) (by omega)]
                  rw [eval_same (by simp; omega)]; exact nba_c t _ _
              | back =>
                have hIe : Iend p t0 w = t0 + w + p.R (p.delta w (t0 + w)) + p.L + 1 := by
                  simp [Iend, hres]
                generalize hT : p.R (p.delta w (t0 + w)) = T at hIe
                have hS : ∀ u, t0 + w ≤ u → Srunt p t0 w u =
                    ⟨false, decide (u < t0 + w + T), false, 0,
                      t0 + w + T + p.L + 1, t0 + w + T, false⟩ := by
                  intro u hu
                  simp [Srunt, hres, hT, show ¬ u < t0 by omega, show ¬ u < t0 + w by omega]
                rw [hS t (by omega), hS (t + 1) (by omega)]
                unfold step
                by_cases hI : t + 1 < t0 + w + T + p.L + 1
                · rw [eval_blocked (by simp [blocked, hI])]; exact nba_b t _ _
                · rw [hS (t + 1 - p.L) (by omega), hb2 (t + 1) (by omega)]
                  rw [eval_same (by simp)]; exact nba_b t _ _

/-- The plain runt: `b` is exactly the pulse. -/
theorem run_runt {p : Prm} {t0 w : Nat} {st : Nat → St} (hL : 1 ≤ p.L) (ht0 : 1 ≤ t0)
    (hw1 : 1 ≤ w) (hw : w < p.L) (h : Run p aOne (bPulse t0 w) rstZero false st) :
    ∀ t, st t = Srunt p t0 w t :=
  run_runt_gen hL ht0 hw1 hw (fun _ _ => rfl)
    (fun t ht => by simp [bPulse]; unfold Iend at ht; omega) h

/-! ### What fanout sees (the output wire `o`, i.e. what every fanout pin and the feedback copy) -/

/-- The resolution time used by the run (`0` for a rejection, which schedules nothing). -/
def trpOf (p : Prm) (t0 w : Nat) : Nat :=
  match resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) with
  | .reject => 0 | _ => p.R (p.delta w (t0 + w))

/-- **(1) The output of the bd_c2 node for a pulse of width `w` on `b`, for every width,
every noise draw and every resolution-time law.**
* `w ≥ L`: a clean set at `t0`;
* `w < L`, outcome `reject` or `back`: `o` is the FULL-SWING pulse `[t0, t0 + w)`, then `0`;
* `w < L`, outcome `commit`: `o` is `1` on `[t0, t0 + w)`, `0` on `[t0 + w, t0 + w + trp)`,
  then `1` forever (for `trp = 0` the gap is empty: a clean set).
So every fanout sees the runt in full in every case: "rejected" (`:29`, "the node never
left") is true of the node's final value only. -/
theorem out_wide {p : Prm} {t0 w : Nat} {st : Nat → St} (hL : 1 ≤ p.L) (ht0 : 1 ≤ t0)
    (hw : p.L ≤ w) (h : Run p aOne (bPulse t0 w) rstZero false st) (t : Nat) :
    (st t).o = decide (t0 ≤ t) := by
  rw [run_wide hL ht0 hw h t]; unfold Swide
  by_cases h1 : t < t0
  · simp [h1, St.init]
  · simp [h1, S1]; omega

theorem out_runt {p : Prm} {t0 w : Nat} {st : Nat → St} (hL : 1 ≤ p.L) (ht0 : 1 ≤ t0)
    (hw1 : 1 ≤ w) (hw : w < p.L) (h : Run p aOne (bPulse t0 w) rstZero false st) (t : Nat) :
    (st t).o = decide (t0 ≤ t ∧ (t < t0 + w ∨
      (resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) = .commit ∧
        t0 + w + trpOf p t0 w ≤ t))) := by
  rw [run_runt hL ht0 hw1 hw h t]; unfold Srunt trpOf
  by_cases h1 : t < t0
  · simp [h1, St.init]; omega
  · by_cases h2 : t < t0 + w
    · simp [h1, h2, S1]; omega
    · cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) <;> simp [h1, h2] <;> omega

/-- The rejected (and the "back") runt is a full-swing pulse of width `w` on the output. -/
theorem rejected_runt_emitted {p : Prm} {t0 w : Nat} {st : Nat → St} (hL : 1 ≤ p.L)
    (ht0 : 1 ≤ t0) (hw1 : 1 ≤ w) (hw : w < p.L) (h : Run p aOne (bPulse t0 w) rstZero false st)
    (hr : resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) ≠ .commit) :
    (st (t0 - 1)).o = false ∧ (∀ t, t0 ≤ t → t < t0 + w → (st t).o = true) ∧
      ∀ t, t0 + w ≤ t → (st t).o = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [out_runt hL ht0 hw1 hw h]; simp; omega
  · intro t h1 h2; rw [out_runt hL ht0 hw1 hw h]; simp; omega
  · intro t h1; rw [out_runt hL ht0 hw1 hw h]; simp [hr]; omega

/-- A committed runt with `trp > 0` is seen by fanout as `1`, a `0` gap of width `trp`, then
`1`: two rising edges for one set event. -/
theorem commit_gap {p : Prm} {t0 w : Nat} {st : Nat → St} (hL : 1 ≤ p.L)
    (ht0 : 1 ≤ t0) (hw1 : 1 ≤ w) (hw : w < p.L) (h : Run p aOne (bPulse t0 w) rstZero false st)
    (hr : resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) = .commit) :
    (∀ t, t0 + w ≤ t → t < t0 + w + p.R (p.delta w (t0 + w)) → (st t).o = false) ∧
      ∀ t, t0 + w + p.R (p.delta w (t0 + w)) ≤ t → (st t).o = true := by
  have ht : trpOf p t0 w = p.R (p.delta w (t0 + w)) := by simp [trpOf, hr]
  refine ⟨?_, ?_⟩
  · intro t h1 h2; rw [out_runt hL ht0 hw1 hw h, ht]; simp [hr]; omega
  · intro t h1; rw [out_runt hL ht0 hw1 hw h, ht]; simp [hr]; omega

/-- **Every non-blocked edge reaches the output in the same step**, runt or not, in ANY run of
the resolver (any input, not only bd_c2): the output equals the new `f` unless the edge is a
runt that commits with `trp = 0` (then the 0-width reversal is invisible at end of step). -/
theorem step_emits (p : Prm) (t : Nat) (f : Bool) (s : St) (hb : blocked t s = false)
    (hf : f ≠ s.o) :
    (step p t f s).o = f ∨ (isRunt p t f s = true ∧
      resolve ((t - s.tl : Nat) : Int) (p.L : Int) p.win (p.nz t) = .commit ∧
      p.R (p.delta (t - s.tl) t) = 0) := by
  have hbusy : s.busy = false := by simp [blocked] at hb; exact hb.1
  by_cases hr : isRunt p t f s = true
  · unfold step; rw [eval_runt hb hf hr]
    cases hres : resolve ((t - s.tl : Nat) : Int) (p.L : Int) p.win (p.nz t)
    · left; simp [nba, hbusy]
    · by_cases hz : p.R (p.delta (t - s.tl) t) = 0
      · right; exact ⟨hr, rfl, hz⟩
      · left; simp [nba, hz]
    · left; by_cases hz : p.R (p.delta (t - s.tl) t) = 0 <;> simp [nba, hz]
  · have hr' : isRunt p t f s = false := by simpa using hr
    left; unfold step; rw [eval_edge hb hf hr']; simp [nba, hbusy]

/-! ## 5. (2) What a passing run implies, and what it does not -/

/-- **Seed dependence.** For every runt width `w < L` and every `win ≥ 2` (and every loop
delay, every law), there are noise draws under which the same circuit with the same delays
and inputs ends at `0` (rejected) and at `1` (committed). A run with one `META_SEED` decides
nothing about the others (Gaussian noise: every draw has positive density). -/
theorem seed_dependence (L : Nat) (win : Int) (R : Int → Nat) {t0 w : Nat} (hL : 1 ≤ L)
    (ht0 : 1 ≤ t0) (hw1 : 1 ≤ w) (hw : w < L) (hwin : 2 ≤ win) :
    ∃ n0 n1 : Int,
      (∀ st, Run ⟨L, win, fun _ => n0, R⟩ aOne (bPulse t0 w) rstZero false st →
        ∀ t, t0 + w ≤ t → (st t).o = false) ∧
      (∀ st, Run ⟨L, win, fun _ => n1, R⟩ aOne (bPulse t0 w) rstZero false st →
        ∃ T, ∀ t, T ≤ t → (st t).o = true) := by
  obtain ⟨⟨n0, h0⟩, ⟨n1, h1⟩, _⟩ := Formal.Core.GLSFid.resolve_all_outcomes (w : Int) (L : Int) win hwin
  refine ⟨n0, n1, ?_, ?_⟩
  · intro st h t ht
    exact (rejected_runt_emitted (p := ⟨L, win, fun _ => n0, R⟩) hL ht0 hw1 hw h
      (by simp [h0])).2.2 t ht
  · intro st h
    exact ⟨_, (commit_gap (p := ⟨L, win, fun _ => n1, R⟩) hL ht0 hw1 hw h (by simpa using h1)).2⟩

end Formal.Core.GLSResolve
