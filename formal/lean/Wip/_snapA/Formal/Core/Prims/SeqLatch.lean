import Formal.Core.Prims.SeqFlop

/-!
# Formal.Core.Prims.SeqLatch — the slice latches (LDCE/LDPE) as trace relations

Shard A, probe PrimsSeq. Core Lean only (no Mathlib). Notes: `formal/notes/A-prims-seq.md`.

Signals on the Core grid (1 ps). `g` is the latch's **effective gate** as a K3 signal:
`G ∧ GE` after the slice's CLKINV (for LDCE with `IS_G_INVERTED` the inverted G); combining
the two pins into one signal is **H_LAT_GATE** (their two arcs, CLK->Q and CE->Q, are folded
into one gate band `[gqLo, gqHi]`). `clr` is CLR (LDCE, `rv = 0`) or PRE (LDPE, `rv = 1`).

## Rules (one corner, `LatTiming`)

* **Transparent** (`opn`): gate 1 and CLR 0 for the last `M` ps ⇒ `q t` is D read over
  `[t - dqHi, t - dqLo]` (the K3 form of the substrate's `Win` channel: D's value if D is
  constant there, else X).
* **Hold** (`hold`): a clean closing edge at `c` (gate 1 for `L` ps up to `c`, 0 from `c+1`
  on) ⇒ while closed, Q is D read over the closing window `[c + hLo, c + hHi]`
  (**H_LAT_WINDOW**: `hLo ≤ -dqHi` so the window also covers what the open latch was still
  showing; `hHi` = hold). A D change inside the window (a setup/hold violation) gives X up to
  `c + hHi + gqHi + res` (H_LAT_RESOLVE) and then one definite, nondeterministic value.
* **CLR/PRE** held `sqHi` ⇒ `rv` (beats the gate); released cleanly with the gate closed ⇒
  `rv` stays.
* **INIT**: gate and CLR low since 0 ⇒ INIT.
* Anything else (a runt on the gate, X on the gate, CLR inside a window) is unconstrained:
  e.g. a glitch on a closed latch's gate may store garbage until the gate reopens, and the
  model says exactly that much.

Not modelled: the separate G and GE arcs; gate minimum pulse width beyond "open for `L`";
X on the gate is treated as "no rule" (unconstrained), not propagated through `merge`.
-/

namespace Formal.Core.Prims.Seq

open Formal.Core Formal.Core.K3 Formal.Core.Substrate

/-- Latch timing at ONE corner, integer ps. -/
structure LatTiming where
  /-- gate open -> Q (prjxray `CLK Q`). -/
  gqLo : Nat
  gqHi : Nat
  /-- D -> Q while open. -/
  dqLo : Nat
  dqHi : Nat
  /-- Closing window for D: `[c + hLo, c + hHi]`. -/
  hLo : Int
  hHi : Int
  /-- CLR/PRE -> Q. -/
  sqLo : Nat
  sqHi : Nat
  /-- **H_LAT_RESOLVE**. -/
  res : Nat
  deriving Repr, DecidableEq

variable (T : LatTiming)

/-- How long the gate must have been open for the transparent / closing rules. -/
def LatTiming.L : Nat := T.gqHi + T.dqHi
/-- How long CLR must have been low for them. -/
def LatTiming.M : Nat := T.gqHi + T.dqHi + T.sqHi

/-- Transparent at `t`. -/
def LOpen (g clr : KSig) (t : Nat) : Prop :=
  T.M ≤ t ∧ EqOn g one (t - T.M) t ∧ EqOn clr zero (t - T.M) t

/-- A clean close at `c`, still closed at `t`. -/
def LClosed (g clr : KSig) (c t : Nat) : Prop :=
  c < t ∧ T.L ≤ c ∧ EqOn g one (c - T.L) c ∧ EqOn g zero (c + 1) t ∧ EqOn clr zero (c - T.M) t

/-- The value held after a close at `c`. -/
def held (d : KSig) (c : Nat) : K3 := ap d c T.hLo T.hHi

/-- End of the X window after a disturbed close. -/
def LatTiming.xend (c : Nat) : Nat := wpt c T.hHi + T.gqHi + T.res

/-- CLR/PRE released cleanly at `f` with the gate closed. -/
def LReleased (g clr : KSig) (f t : Nat) : Prop :=
  T.sqHi ≤ f ∧ f ≤ t ∧ EqOn clr one (f - T.sqHi) f ∧ EqOn clr zero (f + 1) t ∧
    EqOn g zero (f - T.sqHi) t

/-- **The latch.** -/
structure LatchRel (rv init : Bool) (g d clr q : KSig) : Prop where
  init : ∀ t, EqOn g zero 0 t → EqOn clr zero 0 t → q t = ofBool init
  opn : ∀ t, LOpen T g clr t → q t = winVal d (t - T.dqHi) (t - T.dqLo)
  hold : ∀ c t, LClosed T g clr c t → held T d c ≠ X → q t = held T d c
  xwin : ∀ c t, LClosed T g clr c t → held T d c = X → t ≤ T.xend c → q t = X
  resolve : ∀ c, held T d c = X → ∃ b : Bool, ∀ t, T.xend c < t → LClosed T g clr c t →
    q t = ofBool b
  clr : ∀ t, T.sqHi ≤ t → EqOn clr one (t - T.sqHi) t → q t = ofBool rv
  rel : ∀ f t, LReleased T g clr f t → q t = ofBool rv

/-! ## Transparency, hold, containment -/

/-- **Transparency.** Open, D = v on `[t - dqHi, t - dqLo]` ⇒ Q = v. -/
theorem latch_transparent {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    {t : Nat} {v : K3} (hle : T.dqLo ≤ T.dqHi) (ho : LOpen T g clr t)
    (hd : EqOn d v (t - T.dqHi) (t - T.dqLo)) : q t = v := by
  rw [h.opn t ho, winVal_const (by omega) hd]

/-- **Transparency is the substrate's window channel, in K3**: while open, Q refines D at
every step of `[t - dqHi, t - dqLo]` (if Q is definite it IS D's value there). -/
theorem latch_transparent_le {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    {t s : Nat} (hle : T.dqLo ≤ T.dqHi) (ho : LOpen T g clr t)
    (h1 : t - T.dqHi ≤ s) (h2 : s ≤ t - T.dqLo) : q t ⊑ d s := by
  rw [h.opn t ho]
  cases hw : winVal d (t - T.dqHi) (t - T.dqLo) with
  | X => exact X_le _
  | zero =>
    have := ((winVal_eq_ofBool (v := false) (by omega)).1 hw) s h1 h2
    rw [this]; exact le_refl _
  | one =>
    have := ((winVal_eq_ofBool (v := true) (by omega)).1 hw) s h1 h2
    rw [this]; exact le_refl _

/-- **Hold.** A clean close at `c` with D = v on the closing window ⇒ Q = v as long as the
latch stays closed. -/
theorem latch_hold {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    {c t : Nat} {v : Bool} (hle : T.hLo ≤ T.hHi) (hc : LClosed T g clr c t)
    (hd : EqOn d (ofBool v) (wpt c T.hLo) (wpt c T.hHi)) : q t = ofBool v := by
  have hv : held T d c = ofBool v := winVal_const (wpt_le hle) hd
  rw [h.hold c t hc (by rw [hv]; exact ofBool_ne_X v), hv]

/-- **X-containment (latch).** After a clean close, whatever D did in the window, Q is one
definite value from `xend c` on while closed. -/
theorem latch_x_contained {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    (c : Nat) : ∃ b : Bool, ∀ t, T.xend c < t → LClosed T g clr c t → q t = ofBool b := by
  by_cases hx : held T d c = X
  · exact h.resolve c hx
  · obtain ⟨b, hb⟩ := ne_X_iff.1 hx
    exact ⟨b, fun t _ hc => by rw [h.hold c t hc hx, hb]⟩

/-- **A closing-window violation produces X** up to `xend c`. -/
theorem latch_violation_X {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    {c t s1 s2 : Nat} (hc : LClosed T g clr c t)
    (h1a : wpt c T.hLo ≤ s1) (h1b : s1 ≤ wpt c T.hHi) (h2a : wpt c T.hLo ≤ s2)
    (h2b : s2 ≤ wpt c T.hHi) (hne : d s1 ≠ d s2) (ht : t ≤ T.xend c) : q t = X :=
  h.xwin c t hc (winVal_X_of_ne h1a h1b h2a h2b hne) ht

/-- **CLR/PRE priority** over the gate. -/
theorem latch_clr_priority {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    {t : Nat} (ht : T.sqHi ≤ t) (hr : EqOn clr one (t - T.sqHi) t) : q t = ofBool rv :=
  h.clr t ht hr

/-- **INIT** while the gate and CLR have been low since power-up. -/
theorem latch_power_up {rv init : Bool} {g d clr q : KSig} (h : LatchRel T rv init g d clr q)
    {t : Nat} (hg : EqOn g zero 0 t) (hr : EqOn clr zero 0 t) : q t = ofBool init :=
  h.init t hg hr

/-! ## Non-vacuity -/

theorem lclosed_unique {g clr : KSig} {c c' t : Nat} (h : LClosed T g clr c t)
    (h' : LClosed T g clr c' t) : c = c' := by
  obtain ⟨_, _, _, hz, _⟩ := h
  obtain ⟨_, _, ho', hz', _⟩ := h'
  obtain ⟨_, _, ho, _, _⟩ := h
  apply Classical.byContradiction; intro hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hz c' (by omega) (by omega); rw [ho' c' (by omega) (Nat.le_refl _)] at this
    exact absurd this (by decide)
  · have := hz' c (by omega) (by omega); rw [ho c (by omega) (Nat.le_refl _)] at this
    exact absurd this (by decide)

/-- The canonical latch behaviour (resolution picks 0, no rule: X). -/
noncomputable def lsim (rv init : Bool) (g d clr : KSig) (t : Nat) : K3 :=
  open Classical in
  if T.sqHi ≤ t ∧ EqOn clr one (t - T.sqHi) t then ofBool rv
  else if ∃ f, LReleased T g clr f t then ofBool rv
  else if LOpen T g clr t then winVal d (t - T.dqHi) (t - T.dqLo)
  else if EqOn g zero 0 t ∧ EqOn clr zero 0 t then ofBool init
  else if hc : ∃ c, LClosed T g clr c t then
    (if held T d (Classical.choose hc) ≠ X then held T d (Classical.choose hc)
     else if t ≤ T.xend (Classical.choose hc) then X else zero)
  else X

private theorem ne_of_eq_zero_one {x : KSig} {s : Nat} (h0 : x s = zero) (h1 : x s = one) : False := by
  rw [h0] at h1; exact absurd h1 (by decide)

/-- **Non-vacuity**: `lsim` satisfies the latch relation for every input. -/
theorem lsim_rel (rv init : Bool) (g d clr : KSig) :
    LatchRel T rv init g d clr (lsim T rv init g d clr) := by
  classical
  -- exclusivity facts
  have nclr_of_zero : ∀ t, clr t = zero → ¬ (T.sqHi ≤ t ∧ EqOn clr one (t - T.sqHi) t) :=
    fun t h0 ⟨_, h1⟩ => ne_of_eq_zero_one h0 (h1 t (by omega) (Nat.le_refl _))
  have nrel_of_g : ∀ t, g t = one → ¬ ∃ f, LReleased T g clr f t :=
    fun t h1 ⟨f, _, hft, _, _, hg⟩ => ne_of_eq_zero_one (hg t (by omega) (Nat.le_refl _)) h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hg hr
    have h2 : ¬ ∃ f, LReleased T g clr f t := fun ⟨f, _, hft, h1, _, _⟩ =>
      ne_of_eq_zero_one (hr f (Nat.zero_le _) hft) (h1 f (by omega) (Nat.le_refl _))
    have h3 : ¬ LOpen T g clr t := fun ⟨_, h1, _⟩ =>
      ne_of_eq_zero_one (hg t (Nat.zero_le _) (Nat.le_refl _)) (h1 t (by omega) (Nat.le_refl _))
    unfold lsim
    rw [if_neg (nclr_of_zero t (hr t (Nat.zero_le _) (Nat.le_refl _))), if_neg h2, if_neg h3,
      if_pos ⟨hg, hr⟩]
  · intro t ho
    obtain ⟨_, hg, hr⟩ := ho
    unfold lsim
    rw [if_neg (nclr_of_zero t (hr t (by omega) (Nat.le_refl _))),
      if_neg (nrel_of_g t (hg t (by omega) (Nat.le_refl _))), if_pos ⟨by assumption, hg, hr⟩]
  · -- closed rules share the case analysis
    intro c t hc hx
    have hcl := hc
    obtain ⟨hct, _, hgo, hgz, hrz⟩ := hc
    have h1 := nclr_of_zero t (hrz t (by omega) (Nat.le_refl _))
    have h2 : ¬ ∃ f, LReleased T g clr f t := fun ⟨f, _, hft, hf1, _, hfg⟩ => by
      by_cases hfc : c - T.M ≤ f
      · exact ne_of_eq_zero_one (hrz f hfc hft) (hf1 f (by omega) (Nat.le_refl _))
      · exact ne_of_eq_zero_one (hfg c (by omega) (by omega)) (hgo c (by omega) (Nat.le_refl _))
    have h3 : ¬ LOpen T g clr t := fun ⟨_, h1, _⟩ =>
      ne_of_eq_zero_one (hgz t (by omega) (Nat.le_refl _)) (h1 t (by omega) (Nat.le_refl _))
    have h4 : ¬ (EqOn g zero 0 t ∧ EqOn clr zero 0 t) := fun ⟨hg0, _⟩ =>
      ne_of_eq_zero_one (hg0 c (Nat.zero_le _) (by omega)) (hgo c (by omega) (Nat.le_refl _))
    have hex : ∃ c, LClosed T g clr c t := ⟨c, hcl⟩
    have hch : Classical.choose hex = c := lclosed_unique T (Classical.choose_spec hex) hcl
    unfold lsim
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, dif_pos hex, hch, if_pos hx]
  · intro c t hc hx ht
    have hcl := hc
    obtain ⟨hct, _, hgo, hgz, hrz⟩ := hc
    have h1 := nclr_of_zero t (hrz t (by omega) (Nat.le_refl _))
    have h2 : ¬ ∃ f, LReleased T g clr f t := fun ⟨f, _, hft, hf1, _, hfg⟩ => by
      by_cases hfc : c - T.M ≤ f
      · exact ne_of_eq_zero_one (hrz f hfc hft) (hf1 f (by omega) (Nat.le_refl _))
      · exact ne_of_eq_zero_one (hfg c (by omega) (by omega)) (hgo c (by omega) (Nat.le_refl _))
    have h3 : ¬ LOpen T g clr t := fun ⟨_, h1, _⟩ =>
      ne_of_eq_zero_one (hgz t (by omega) (Nat.le_refl _)) (h1 t (by omega) (Nat.le_refl _))
    have h4 : ¬ (EqOn g zero 0 t ∧ EqOn clr zero 0 t) := fun ⟨hg0, _⟩ =>
      ne_of_eq_zero_one (hg0 c (Nat.zero_le _) (by omega)) (hgo c (by omega) (Nat.le_refl _))
    have hex : ∃ c, LClosed T g clr c t := ⟨c, hcl⟩
    have hch : Classical.choose hex = c := lclosed_unique T (Classical.choose_spec hex) hcl
    unfold lsim
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, dif_pos hex, hch, if_neg (fun h => h hx),
      if_pos ht]
  · intro c hx
    refine ⟨false, fun t ht hc => ?_⟩
    have hcl := hc
    obtain ⟨hct, _, hgo, hgz, hrz⟩ := hc
    have h1 := nclr_of_zero t (hrz t (by omega) (Nat.le_refl _))
    have h2 : ¬ ∃ f, LReleased T g clr f t := fun ⟨f, _, hft, hf1, _, hfg⟩ => by
      by_cases hfc : c - T.M ≤ f
      · exact ne_of_eq_zero_one (hrz f hfc hft) (hf1 f (by omega) (Nat.le_refl _))
      · exact ne_of_eq_zero_one (hfg c (by omega) (by omega)) (hgo c (by omega) (Nat.le_refl _))
    have h3 : ¬ LOpen T g clr t := fun ⟨_, h1, _⟩ =>
      ne_of_eq_zero_one (hgz t (by omega) (Nat.le_refl _)) (h1 t (by omega) (Nat.le_refl _))
    have h4 : ¬ (EqOn g zero 0 t ∧ EqOn clr zero 0 t) := fun ⟨hg0, _⟩ =>
      ne_of_eq_zero_one (hg0 c (Nat.zero_le _) (by omega)) (hgo c (by omega) (Nat.le_refl _))
    have hex : ∃ c, LClosed T g clr c t := ⟨c, hcl⟩
    have hch : Classical.choose hex = c := lclosed_unique T (Classical.choose_spec hex) hcl
    unfold lsim
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, dif_pos hex, hch, if_neg (fun h => h hx),
      if_neg (show ¬ t ≤ T.xend c by omega)]
    rfl
  · intro t ht hr
    unfold lsim; rw [if_pos ⟨ht, hr⟩]
  · intro f t hf
    unfold lsim
    by_cases h1 : T.sqHi ≤ t ∧ EqOn clr one (t - T.sqHi) t
    · rw [if_pos h1]
    · rw [if_neg h1, if_pos ⟨f, hf⟩]

theorem latchRel_inhabited (rv init : Bool) (g d clr : KSig) :
    ∃ q, LatchRel T rv init g d clr q := ⟨_, lsim_rel T rv init g d clr⟩

end Formal.Core.Prims.Seq
