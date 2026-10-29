import Formal.Core.Substrate.Chan
import Formal.Core.Prims.SeqNext

/-!
# Formal.Core.Prims.SeqFlop — the slice flops (FDRE/FDSE/FDCE/FDPE) as trace relations

Shard A, probe PrimsSeq. Core Lean only (no Mathlib). Notes: `formal/notes/A-prims-seq.md`.
Numbers (prjxray-db): `Formal.Core.Prims.SeqXray`.

## Substrate

Time is the Core grid (`Substrate.Sig`/`KSig`, 1 step = 1 ps, H_GRID). The clock `ck` is a
binary signal (**H_CK_BINARY**: a clock runt or X is outside this model); `r` (R/S of
FDRE/FDSE, CLR/PRE of FDCE/FDPE), `ce`, `d` and the output `q` are Kleene signals (`KSig`).
A rising edge "at `e`" is `rises ck e` (`ck e = 0`, `ck (e+1) = 1`).

## The model (one corner, `FFTiming`)

* **Aperture sampling.** At an edge `e`, each input is read over its own window
  `[e + lo, e + hi]` (`ap`, integer offsets, so a negative setup is a window after the edge):
  the read value is the input's value if it is constant there, and `X` otherwise
  (`winVal`, the K3 meet over the window). For D the window is setup/hold, for CE its
  setup/hold, for SR its recovery/removal.
* **Next state** = `knext rv r ce d q` (`SeqNext`): R/S/CLR/PRE (value `rv`) beats CE, CE
  selects D or the held state; exact Kleene extension.
* **CK->Q band `[cqLo, cqHi]`.** Until `e + cqLo` the output keeps its old value; in
  `(e + cqLo, e + cqHi]` it is `merge old new` (X if they differ: the edge is somewhere in
  the band); after `e + cqHi` it is the new value.
* **A setup/hold violation** (an input that matters is not constant on its window) makes
  the next state `X`. Then the output is `X` up to `e + cqHi + res`, and from then on a
  **definite but nondeterministic** binary value `b` (∃ b), held until the next edge.
  `res` is **H_FF_RESOLVE**, a named bound on how long a disturbed flop stays undecided.
  It is a hypothesis, not derived: the digital model has no analog state, so it cannot
  say how long resolution takes (no MTBF here), only what holds once it has.
  Why X and then a nondeterministic binary value, and not one of them alone: during the
  window downstream logic can see anything (a runt, a late edge, an oscillation), and K3's
  `X` is exactly "any binary waveform" (`Substrate.Covers`); after it, the flop is a
  storage node again and holds ONE value, but which one is not determined by any digital
  fact, so the model leaves it open (∃ b) and every theorem must hold for both.
* **Power-up (INIT).** Before the first edge the output is `INIT` (H_GSR: time 0 is the
  release of the global set/reset; for FDCE/FDPE also CLR/PRE low since 0).
* **Async CLR/PRE (FDCE/FDPE, `async = true`).** Held high for `sqHi` it forces `rv`
  regardless of the clock (`clr`); after a clean release, `rv` stays until an edge whose
  recovery/removal window lies after the release (`rel`). A clocked rule applies only
  while CLR/PRE is low after the edge's window (`Guard`). Where no rule applies (a runt on
  CLR, CLR inside a window) the output is unconstrained, which is weaker than silicon and
  therefore sound.

The relation is not vacuous: `sim` builds, for EVERY input, an output satisfying it
(`sim_rel`).

## Main theorems

* `capture`: window respected (D = v on its window, CE = 1, R = 0) ⇒ Q = v after `cqHi`.
* `capture_hold`, `capture_reset`: CE = 0 keeps the state, R = 1 gives `rv` (R beats CE).
* `x_contained`: whatever happens in the windows, after `cqHi + res` Q is definite;
  `x_only_in_window`: a definite old state turns X only inside `(cqLo, cqHi + res]`.
* `violation_X`: a D change inside its window (CE = 1, R = 0) does produce X.
* `clr_priority`: CLR/PRE held ⇒ `rv` whatever the clock and D do.
* `power_up`: INIT before the first edge.
* `gls_vs_kleene`: the research GLS's `SLICE_FFX` (X on CE read as 0) has a violation-free
  run with Q = 0 where every Kleene run has Q = X (FOR-RESEARCH §7, notes/A-forres.md).

## What is NOT modelled

Clock minimum pulse width (two edges closer than the band are both trusted); X or runts on
the clock; metastability duration (H_FF_RESOLVE is a parameter); rise/fall split (prjxray-db
has none); the fast-corner setup/hold windows (the shipped SDF has only the slow ones,
`SeqXray`); correlation between the flop's corner and the routing's.
-/

namespace Formal.Core.Prims.Seq

open Formal.Core Formal.Core.K3 Formal.Core.Substrate

/-! ## 1. The value of a K3 signal over a window -/

/-- `winFold x a n`: the K3 meet (`merge`) of `x a, ..., x (a + n)`. -/
def winFold (x : KSig) (a : Nat) : Nat → K3
  | 0 => x a
  | n + 1 => merge (winFold x a n) (x (a + n + 1))

/-- The value of `x` over `[a, b]`: its common value if constant there, else `X`. -/
def winVal (x : KSig) (a b : Nat) : K3 := winFold x a (b - a)

/-- `x` equals `v` at every step of `[a, b]`. -/
def EqOn (x : KSig) (v : K3) (a b : Nat) : Prop := ∀ s, a ≤ s → s ≤ b → x s = v

theorem winFold_const {x : KSig} {a : Nat} {v : K3} :
    ∀ n, (∀ i, i ≤ n → x (a + i) = v) → winFold x a n = v
  | 0, h => by simpa [winFold] using h 0 (Nat.le_refl 0)
  | n + 1, h => by
    simp only [winFold]
    rw [winFold_const n (fun i hi => h i (by omega)), h (n + 1) (Nat.le_refl _)]
    · simp [merge]

theorem winFold_eq_ofBool {x : KSig} {a : Nat} {v : Bool} :
    ∀ n, winFold x a n = ofBool v ↔ ∀ i, i ≤ n → x (a + i) = ofBool v
  | 0 => by
    simp only [winFold]
    exact ⟨fun h i hi => by rw [show i = 0 by omega]; simpa using h,
      fun h => by simpa using h 0 (Nat.le_refl 0)⟩
  | n + 1 => by
    simp only [winFold, merge_eq_ofBool_iff, winFold_eq_ofBool n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hin : i ≤ n
      · exact h1 i hin
      · rw [show i = n + 1 by omega]; simpa [Nat.add_assoc] using h2
    · intro h
      exact ⟨fun i hi => h i (by omega), by simpa [Nat.add_assoc] using h (n + 1) (Nat.le_refl _)⟩

theorem winVal_const {x : KSig} {a b : Nat} {v : K3} (hab : a ≤ b) (h : EqOn x v a b) :
    winVal x a b = v :=
  winFold_const _ (fun i hi => h (a + i) (by omega) (by omega))

theorem winVal_eq_ofBool {x : KSig} {a b : Nat} {v : Bool} (hab : a ≤ b) :
    winVal x a b = ofBool v ↔ EqOn x (ofBool v) a b := by
  unfold winVal EqOn
  rw [winFold_eq_ofBool]
  constructor
  · intro h s h1 h2
    have := h (s - a) (by omega)
    rwa [show a + (s - a) = s by omega] at this
  · intro h i hi
    exact h (a + i) (by omega) (by omega)

/-- Two different values inside the window make the window value `X`. -/
theorem winVal_X_of_ne {x : KSig} {a b s1 s2 : Nat} (h1a : a ≤ s1) (h1b : s1 ≤ b)
    (h2a : a ≤ s2) (h2b : s2 ≤ b) (hne : x s1 ≠ x s2) : winVal x a b = X := by
  cases hw : winVal x a b with
  | X => rfl
  | zero =>
    have := (winVal_eq_ofBool (v := false) (by omega)).1 hw
    exact absurd ((this s1 h1a h1b).trans (this s2 h2a h2b).symm) hne
  | one =>
    have := (winVal_eq_ofBool (v := true) (by omega)).1 hw
    exact absurd ((this s1 h1a h1b).trans (this s2 h2a h2b).symm) hne

/-- An `X` inside the window makes the window value `X`. -/
theorem winVal_X_of_X {x : KSig} {a b s : Nat} (ha : a ≤ s) (hb : s ≤ b) (hx : x s = X) :
    winVal x a b = X := by
  cases hw : winVal x a b with
  | X => rfl
  | zero =>
    have := ((winVal_eq_ofBool (v := false) (by omega)).1 hw) s ha hb
    rw [hx] at this; exact absurd this (by decide)
  | one =>
    have := ((winVal_eq_ofBool (v := true) (by omega)).1 hw) s ha hb
    rw [hx] at this; exact absurd this (by decide)

/-! ## 2. Timing parameters and the aperture read -/

/-- The timing of one slice flop at ONE corner, integer ps. Window offsets are relative
to the clock edge at the flop's bel pins (prjxray's convention, **H_FF_PINREF**). -/
structure FFTiming where
  /-- CK -> Q band. -/
  cqLo : Nat
  cqHi : Nat
  /-- D window `[e + dLo, e + dHi]` (`dLo = -setup`, `dHi = hold`). -/
  dLo : Int
  dHi : Int
  /-- CE window. -/
  ceLo : Int
  ceHi : Int
  /-- SR window (`srLo = -recovery`, `srHi = removal`). -/
  srLo : Int
  srHi : Int
  /-- SR -> Q band (async CLR/PRE only). -/
  sqLo : Nat
  sqHi : Nat
  /-- **H_FF_RESOLVE**: a disturbed flop is X at most `res` ps past `cqHi`. -/
  res : Nat
  deriving Repr, DecidableEq

/-- Well-formed windows: each window nonempty, SR removal ≤ 0 (prjxray: -248 ps). -/
def FFTiming.Ok (T : FFTiming) : Prop :=
  T.dLo ≤ T.dHi ∧ T.ceLo ≤ T.ceHi ∧ T.srLo ≤ T.srHi ∧ T.srHi ≤ 0

/-- Window end point `e + off`, truncated at 0. -/
def wpt (e : Nat) (off : Int) : Nat := ((e : Int) + off).toNat

theorem wpt_le {e : Nat} {lo hi : Int} (h : lo ≤ hi) : wpt e lo ≤ wpt e hi := by
  unfold wpt; omega

/-- The value of `x` read over the window `[e + lo, e + hi]`. -/
def ap (x : KSig) (e : Nat) (lo hi : Int) : K3 := winVal x (wpt e lo) (wpt e hi)

/-- No rising clock edge strictly between `e` and `t`. -/
def NoRise (ck : Sig) (e t : Nat) : Prop := ∀ u, e < u → u < t → ¬ rises ck u

variable (T : FFTiming)

/-- The next state an edge at `e` computes (Kleene, with the old state `q e`). -/
def nextAt (rv : Bool) (r ce d q : KSig) (e : Nat) : K3 :=
  knext rv (ap r e T.srLo T.srHi) (ap ce e T.ceLo T.ceHi) (ap d e T.dLo T.dHi) (q e)

/-- For FDCE/FDPE: CLR/PRE low from the end of the edge's window up to `t`. -/
def Guard (async : Bool) (r : KSig) (e t : Nat) : Prop :=
  async = true → EqOn r zero (wpt e T.srHi + 1) t

/-- A clean release of CLR/PRE at `f`: held high for `sqHi` up to `f`, low on `(f, t]`, and
every edge before `t` has its SR window ending before `f`. -/
def Released (ck : Sig) (r : KSig) (f t : Nat) : Prop :=
  T.sqHi ≤ f ∧ f ≤ t ∧ EqOn r one (f - T.sqHi) f ∧ EqOn r zero (f + 1) t ∧
    ∀ u, u < t → rises ck u → wpt u T.srHi < f

/-- **The flop.** `async = false`: FDRE (`rv = 0`) / FDSE (`rv = 1`), `r` is R/S;
`async = true`: FDCE (`rv = 0`) / FDPE (`rv = 1`), `r` is CLR/PRE. -/
structure FlopRel (async rv init : Bool) (ck : Sig) (r ce d q : KSig) : Prop where
  init : ∀ t, (∀ u, u < t → ¬ rises ck u) → (async = true → EqOn r zero 0 t) →
    q t = ofBool init
  hold : ∀ e t, rises ck e → e < t → NoRise ck e t → Guard T async r e t →
    t ≤ e + T.cqLo → q t = q e
  band : ∀ e t, rises ck e → e < t → NoRise ck e t → Guard T async r e t →
    e + T.cqLo < t → t ≤ e + T.cqHi → q t = merge (q e) (nextAt T rv r ce d q e)
  settle : ∀ e t, rises ck e → e < t → NoRise ck e t → Guard T async r e t →
    e + T.cqHi < t → nextAt T rv r ce d q e ≠ X → q t = nextAt T rv r ce d q e
  xwin : ∀ e t, rises ck e → e < t → NoRise ck e t → Guard T async r e t →
    nextAt T rv r ce d q e = X → e + T.cqHi < t → t ≤ e + T.cqHi + T.res → q t = X
  resolve : ∀ e, rises ck e → nextAt T rv r ce d q e = X → ∃ b : Bool, ∀ t,
    e + T.cqHi + T.res < t → NoRise ck e t → Guard T async r e t → q t = ofBool b
  clr : async = true → ∀ t, T.sqHi ≤ t → EqOn r one (t - T.sqHi) t → q t = ofBool rv
  rel : async = true → ∀ f t, Released T ck r f t → q t = ofBool rv

/-! ## 3. Correct capture when the windows are respected -/

theorem guard_sync (r : KSig) (e t : Nat) : Guard T false r e t := fun h => absurd h (by decide)

/-- **Correct capture.** D = v on its window, CE = 1 on its window, R/CLR = 0 on its window:
after `cqHi`, until the next edge, Q = v. -/
theorem capture {async rv init : Bool} {ck : Sig} {r ce d q : KSig} (hok : T.Ok) (h : FlopRel T async rv init ck r ce d q)
    {e t : Nat} {v : Bool} (he : rises ck e) (het : e < t) (hn : NoRise ck e t) (hg : Guard T async r e t)
    (hd : EqOn d (ofBool v) (wpt e T.dLo) (wpt e T.dHi))
    (hce : EqOn ce one (wpt e T.ceLo) (wpt e T.ceHi))
    (hr : EqOn r zero (wpt e T.srLo) (wpt e T.srHi))
    (ht : e + T.cqHi < t) : q t = ofBool v := by
  have hnx : nextAt T rv r ce d q e = ofBool v := by
    simp only [nextAt, ap, winVal_const (wpt_le hok.1) hd, winVal_const (wpt_le hok.2.1) hce, winVal_const (wpt_le hok.2.2.1) hr, knext, kmux]
  rw [h.settle e t he het hn hg ht (by rw [hnx]; exact ofBool_ne_X v), hnx]

/-- CE = 0 (R = 0): the flop keeps its state. -/
theorem capture_hold {async rv init : Bool} {ck : Sig} {r ce d q : KSig} (hok : T.Ok) (h : FlopRel T async rv init ck r ce d q)
    {e t : Nat} {v : Bool} (he : rises ck e) (het : e < t) (hn : NoRise ck e t) (hg : Guard T async r e t)
    (hq : q e = ofBool v)
    (hce : EqOn ce zero (wpt e T.ceLo) (wpt e T.ceHi))
    (hr : EqOn r zero (wpt e T.srLo) (wpt e T.srHi)) : q t = ofBool v := by
  have hnx : nextAt T rv r ce d q e = ofBool v := by
    simp only [nextAt, ap, winVal_const (wpt_le hok.2.1) hce, winVal_const (wpt_le hok.2.2.1) hr, knext, kmux, hq]
  by_cases h1 : t ≤ e + T.cqLo
  · rw [h.hold e t he het hn hg h1, hq]
  by_cases h2 : t ≤ e + T.cqHi
  · rw [h.band e t he het hn hg (by omega) h2, hnx, hq, merge_self]
  · rw [h.settle e t he het hn hg (by omega) (by rw [hnx]; exact ofBool_ne_X v), hnx]

/-- R (sync) / CLR sampled 1: `rv` after `cqHi`, whatever CE and D do (R beats CE). -/
theorem capture_reset {async rv init : Bool} {ck : Sig} {r ce d q : KSig} (hok : T.Ok) (h : FlopRel T async rv init ck r ce d q)
    {e t : Nat} (he : rises ck e) (het : e < t) (hn : NoRise ck e t) (hg : Guard T async r e t)
    (hr : EqOn r one (wpt e T.srLo) (wpt e T.srHi)) (ht : e + T.cqHi < t) : q t = ofBool rv := by
  have hnx : nextAt T rv r ce d q e = ofBool rv := by
    simp only [nextAt, ap, winVal_const (wpt_le hok.2.2.1) hr, knext, kmux]
  rw [h.settle e t he het hn hg ht (by rw [hnx]; exact ofBool_ne_X rv), hnx]

/-! ## 4. X-containment -/

/-- **X-containment.** Whatever the inputs did in their windows (a violation, X on CE or
R, an X old state), from `e + cqHi + res` until the next edge Q is ONE definite value. -/
theorem x_contained {async rv init : Bool} {ck : Sig} {r ce d q : KSig}
    (h : FlopRel T async rv init ck r ce d q) {e : Nat} (he : rises ck e) :
    ∃ b : Bool, ∀ t, e + T.cqHi + T.res < t → NoRise ck e t → Guard T async r e t →
      q t = ofBool b := by
  by_cases hx : nextAt T rv r ce d q e = X
  · exact h.resolve e he hx
  · obtain ⟨b, hb⟩ := ne_X_iff.1 hx
    exact ⟨b, fun t ht hn hg => by
      rw [h.settle e t he (by omega) hn hg (by omega) hx, hb]⟩

/-- **X only in the window.** If the state was definite at the edge, Q can be `X` only
inside `(e + cqLo, e + cqHi + res]`. -/
theorem x_only_in_window {async rv init : Bool} {ck : Sig} {r ce d q : KSig}
    (h : FlopRel T async rv init ck r ce d q) {e t : Nat} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hg : Guard T async r e t) (hq : q e ≠ X) (hX : q t = X) :
    e + T.cqLo < t ∧ t ≤ e + T.cqHi + T.res := by
  refine ⟨?_, ?_⟩
  · apply Classical.byContradiction; intro hc
    rw [h.hold e t he het hn hg (by omega)] at hX; exact hq hX
  · apply Classical.byContradiction; intro hc
    obtain ⟨b, hb⟩ := x_contained T h he
    rw [hb t (by omega) hn hg] at hX; exact ofBool_ne_X b hX

/-- **A violation produces X** (the model is not optimistic): CE = 1 and R = 0 cleanly, but
D takes two different values inside its window. Then Q is `X` throughout
`(e + cqLo, e + cqHi + res]`. -/
theorem violation_X {async rv init : Bool} {ck : Sig} {r ce d q : KSig}
    (hok : T.Ok) (h : FlopRel T async rv init ck r ce d q) {e t s1 s2 : Nat} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hg : Guard T async r e t)
    (h1a : wpt e T.dLo ≤ s1) (h1b : s1 ≤ wpt e T.dHi) (h2a : wpt e T.dLo ≤ s2) (h2b : s2 ≤ wpt e T.dHi)
    (hne : d s1 ≠ d s2)
    (hce : EqOn ce one (wpt e T.ceLo) (wpt e T.ceHi))
    (hr : EqOn r zero (wpt e T.srLo) (wpt e T.srHi))
    (ht1 : e + T.cqLo < t) (ht2 : t ≤ e + T.cqHi + T.res) : q t = X := by
  have hnx : nextAt T rv r ce d q e = X := by
    simp only [nextAt, ap, winVal_const (wpt_le hok.2.1) hce, winVal_const (wpt_le hok.2.2.1) hr, knext, kmux,
      winVal_X_of_ne h1a h1b h2a h2b hne]
  by_cases h2 : t ≤ e + T.cqHi
  · rw [h.band e t he het hn hg ht1 h2, hnx]; cases q e <;> rfl
  · exact h.xwin e t he het hn hg hnx (by omega) ht2

/-! ## 5. Power-up and the async CLR/PRE -/

/-- **INIT at power-up**: before the first rising edge (and, for FDCE/FDPE, with CLR/PRE low
since 0) Q is INIT. -/
theorem power_up {async rv init : Bool} {ck : Sig} {r ce d q : KSig}
    (h : FlopRel T async rv init ck r ce d q) {t : Nat} (hno : ∀ u, u < t → ¬ rises ck u)
    (hr : async = true → EqOn r zero 0 t) : q t = ofBool init := h.init t hno hr

/-- **Async priority**: FDCE/FDPE with CLR/PRE held high for `sqHi` gives `rv`, whatever
the clock, CE and D do. -/
theorem clr_priority {rv init : Bool} {ck : Sig} {r ce d q : KSig}
    (h : FlopRel T true rv init ck r ce d q) {t : Nat} (ht : T.sqHi ≤ t)
    (hr : EqOn r one (t - T.sqHi) t) : q t = ofBool rv := h.clr rfl t ht hr

/-! ## 6. Non-vacuity: every input has an output satisfying the relation -/

/-- The last rising edge strictly before `t`, with its proof of `< t`. -/
def lastRise (ck : Sig) : (t : Nat) → Option {e : Nat // e < t}
  | 0 => none
  | t + 1 =>
    if ck t = false ∧ ck (t + 1) = true then some ⟨t, Nat.lt_succ_self t⟩
    else (lastRise ck t).map (fun p => ⟨p.1, Nat.lt_succ_of_lt p.2⟩)

theorem rises_iff (ck : Sig) (t : Nat) : rises ck t ↔ (ck t = false ∧ ck (t + 1) = true) := Iff.rfl

theorem lastRise_none {ck : Sig} : ∀ {t}, (∀ u, u < t → ¬ rises ck u) → lastRise ck t = none
  | 0, _ => rfl
  | t + 1, h => by
    have h1 : ¬ (ck t = false ∧ ck (t + 1) = true) := h t (Nat.lt_succ_self t)
    simp only [lastRise, h1, if_false, lastRise_none (t := t) (fun u hu => h u (by omega)),
      Option.map_none]

theorem lastRise_some {ck : Sig} {e : Nat} : ∀ {t}, rises ck e → e < t → NoRise ck e t →
    ∃ h, lastRise ck t = some ⟨e, h⟩
  | 0, _, het, _ => absurd het (Nat.not_lt_zero _)
  | t + 1, he, het, hn => by
    by_cases hte : e = t
    · subst hte
      have : ck e = false ∧ ck (e + 1) = true := he
      exact ⟨het, by simp only [lastRise, this, and_self, if_true]⟩
    · have h1 : ¬ (ck t = false ∧ ck (t + 1) = true) := hn t (by omega) (by omega)
      obtain ⟨h', hl⟩ := lastRise_some (t := t) he (by omega) (fun u h1 h2 => hn u h1 (by omega))
      exact ⟨het, by simp only [lastRise, h1, if_false, hl, Option.map_some]⟩

/-- The canonical behaviour: the rules read as a definition (resolution picks 0; where no
rule applies, X). -/
noncomputable def sim (async rv init : Bool) (ck : Sig) (r ce d : KSig) (t : Nat) : K3 :=
  open Classical in
  if async = true ∧ T.sqHi ≤ t ∧ EqOn r one (t - T.sqHi) t then ofBool rv
  else if async = true ∧ ∃ f, Released T ck r f t then ofBool rv
  else
    match lastRise ck t with
    | none => if async = true → EqOn r zero 0 t then ofBool init else X
    | some ⟨e, _⟩ =>
      if Guard T async r e t then
        let nv := knext rv (ap r e T.srLo T.srHi) (ap ce e T.ceLo T.ceHi) (ap d e T.dLo T.dHi)
          (sim async rv init ck r ce d e)
        if t ≤ e + T.cqLo then sim async rv init ck r ce d e
        else if t ≤ e + T.cqHi then merge (sim async rv init ck r ce d e) nv
        else if nv ≠ X then nv
        else if t ≤ e + T.cqHi + T.res then X
        else zero
      else X
termination_by t

/-- Under a clocked rule's guard the two CLR/PRE rules do not fire (needs `srHi ≤ 0`,
removal ≤ 0, as in prjxray). -/
theorem guard_excl {async : Bool} {ck : Sig} {r : KSig} {e t : Nat} (hsr : T.srHi ≤ 0)
    (he : rises ck e) (het : e < t) (hg : Guard T async r e t) :
    ¬ (async = true ∧ T.sqHi ≤ t ∧ EqOn r one (t - T.sqHi) t) ∧
      ¬ (async = true ∧ ∃ f, Released T ck r f t) := by
  have hw : wpt e T.srHi ≤ e := by unfold wpt; omega
  refine ⟨fun ⟨ha, _, h1⟩ => ?_, fun ⟨ha, f, hf⟩ => ?_⟩
  · have := hg ha t (by omega) (Nat.le_refl _)
    rw [h1 t (by omega) (Nat.le_refl _)] at this; exact absurd this (by decide)
  · obtain ⟨_, hft, h1, _, hu⟩ := hf
    have hlt := hu e het he
    have := hg ha f (by omega) hft
    rw [h1 f (by omega) (Nat.le_refl _)] at this; exact absurd this (by decide)

theorem sim_eq (async rv init : Bool) (ck : Sig) (r ce d : KSig) (t : Nat) :
    sim T async rv init ck r ce d t =
      (open Classical in
      if async = true ∧ T.sqHi ≤ t ∧ EqOn r one (t - T.sqHi) t then ofBool rv
      else if async = true ∧ ∃ f, Released T ck r f t then ofBool rv
      else
        match lastRise ck t with
        | none => if async = true → EqOn r zero 0 t then ofBool init else X
        | some ⟨e, _⟩ =>
          if Guard T async r e t then
            let nv := knext rv (ap r e T.srLo T.srHi) (ap ce e T.ceLo T.ceHi) (ap d e T.dLo T.dHi)
              (sim T async rv init ck r ce d e)
            if t ≤ e + T.cqLo then sim T async rv init ck r ce d e
            else if t ≤ e + T.cqHi then merge (sim T async rv init ck r ce d e) nv
            else if nv ≠ X then nv
            else if t ≤ e + T.cqHi + T.res then X
            else zero
          else X) := by
  rw [sim]

/-- The clocked branch of `sim`, once the guard holds. -/
theorem sim_clocked {async rv init : Bool} {ck : Sig} {r ce d : KSig} {e t : Nat} (hsr : T.srHi ≤ 0)
    (he : rises ck e) (het : e < t) (hn : NoRise ck e t) (hg : Guard T async r e t) :
    sim T async rv init ck r ce d t =
      (let nv := nextAt T rv r ce d (sim T async rv init ck r ce d) e
       if t ≤ e + T.cqLo then sim T async rv init ck r ce d e
       else if t ≤ e + T.cqHi then merge (sim T async rv init ck r ce d e) nv
       else if nv ≠ X then nv
       else if t ≤ e + T.cqHi + T.res then X
       else zero) := by
  obtain ⟨hx1, hx2⟩ := guard_excl T hsr he het hg
  obtain ⟨_, hl⟩ := lastRise_some he het hn
  rw [sim_eq]
  simp only [hx1, hx2, if_false, hl]
  classical
  simp only [hg, if_true, nextAt]

/-- **Non-vacuity**: `sim` satisfies the relation, for every input and every parameter set
with `srHi ≤ 0`. -/
theorem sim_rel (async rv init : Bool) (ck : Sig) (r ce d : KSig) (hok : T.Ok) :
    FlopRel T async rv init ck r ce d (sim T async rv init ck r ce d) := by
  classical
  have hsr : T.srHi ≤ 0 := hok.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hno hr
    have hx1 : ¬ (async = true ∧ T.sqHi ≤ t ∧ EqOn r one (t - T.sqHi) t) := by
      rintro ⟨ha, _, h1⟩
      have := hr ha t (Nat.zero_le _) (Nat.le_refl _)
      rw [h1 t (by omega) (Nat.le_refl _)] at this; exact absurd this (by decide)
    have hx2 : ¬ (async = true ∧ ∃ f, Released T ck r f t) := by
      rintro ⟨ha, f, _, hft, h1, _, _⟩
      have := hr ha f (Nat.zero_le _) hft
      rw [h1 f (by omega) (Nat.le_refl _)] at this; exact absurd this (by decide)
    rw [sim_eq]
    simp only [hx1, hx2, if_false, lastRise_none hno, hr, if_true]
    simp [hr]
  · intro e t he het hn hg h1
    rw [sim_clocked T hsr he het hn hg]; simp only [h1, if_true]
  · intro e t he het hn hg h1 h2
    rw [sim_clocked T hsr he het hn hg]
    simp only [show ¬ t ≤ e + T.cqLo by omega, h2, if_true, if_false]
  · intro e t he het hn hg h1 hx
    rw [sim_clocked T hsr he het hn hg]
    simp only [show ¬ t ≤ e + T.cqLo by omega, show ¬ t ≤ e + T.cqHi by omega, if_false]
    simp [hx]
  · intro e t he het hn hg hx h1 h2
    rw [sim_clocked T hsr he het hn hg]
    simp only [show ¬ t ≤ e + T.cqLo by omega, show ¬ t ≤ e + T.cqHi by omega, if_false, hx,
      h2, if_true]
    simp
  · intro e he hx
    refine ⟨false, fun t ht hn hg => ?_⟩
    rw [sim_clocked T hsr he (by omega) hn hg]
    simp only [show ¬ t ≤ e + T.cqLo by omega, show ¬ t ≤ e + T.cqHi by omega,
      show ¬ t ≤ e + T.cqHi + T.res by omega, if_false, hx]
    simp
  · intro ha t ht hr
    rw [sim_eq]; simp [ha, ht, hr]
  · intro ha f t hf
    rw [sim_eq]
    by_cases h1 : async = true ∧ T.sqHi ≤ t ∧ EqOn r one (t - T.sqHi) t
    · simp only [h1, and_self, if_true]
    · simp only [h1, if_false]; simp [ha]; exact Or.inr ⟨f, hf⟩

/-- So the relation is inhabited for every input (it constrains, it does not exclude). -/
theorem flopRel_inhabited (async rv init : Bool) (ck : Sig) (r ce d : KSig) (hok : T.Ok) :
    ∃ q, FlopRel T async rv init ck r ce d q := ⟨_, sim_rel T async rv init ck r ce d hok⟩

end Formal.Core.Prims.Seq
