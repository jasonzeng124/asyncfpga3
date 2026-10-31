import Formal.Cells.FifoFidelity
import Formal.Cells.OpsTimed
import Formal.Core.Substrate.Chan

/-!
# Probe Bw: when does the window channel discharge B's FIFO hypotheses?

Shard A recommends the non-FIFO window channel (`Core.Substrate.Win`, which
is definitionally B's `CElemTiming.WinDelay`; `win_iff` below). Shard B's
timed cell proofs assume FIFO channels instead: every one of `H_LUT_FIFO`,
`H_WIRE_FIFO`, `H_LINE_FIFO`, `H_PIN_FIFO`, `H_TREE_FIFO` has the single
form of `PipeTimed.Ret`:

    ∃ r : Ret (band [lo, hi]),  ∀ t ≥ hi,  y t = x (r.σ t),   r.σ monotone,
                                           t - hi ≤ r.σ t ≤ t - lo.

("FIFO read": the output replays the input through a nondecreasing read
time.) A `Ret` may drop a short pulse (σ may jump over it) but can never
add an output edge that the input did not make, nor reorder edges.

Results (time is ℕ ticks; a clean input has edges `c j`, value `val j` on
`[c j, c (j+1))`, `c 0 = 0`):

1. **No spacing makes `Win` FIFO** once the band is two ticks wide:
   `win_glitch_not_fifo`: for every `lo` and `hi ≥ lo + 2` there is an input
   with ONE edge and a `Win lo hi` output that glitches (1, 0, 1) and that no
   `Ret` with `hi' ≤ hi` reproduces. Conversely `win_fifo_narrow`: if
   `hi ≤ lo + 1`, EVERY `Win lo hi` behaviour is a FIFO read, for every
   input. So `Win ⊆ Ret` holds exactly when `hi - lo ≤ 1` tick.
2. **What spacing does give** (`H_SPREAD_PULSE`: `c j + hi < c (j+1) + lo`,
   i.e. consecutive input edges more than `hi - lo` apart): the output
   settles to `val j` on the nonempty stretch `[c j + hi, c (j+1) + lo)`
   (`win_settled`), and inside edge `j`'s uncertainty zone
   `[c j + lo, c j + hi)` it shows only `val (j-1)` or `val j`
   (`win_zone`): nothing is swallowed, nothing overtakes. Exact:
   `win_swallow` (separation `w ≤ hi - lo`: the constant output is a `Win`
   output that never shows the pulse).
3. **The bridge** (`win_fifo_of_no_revert`): `Win` + `H_SPREAD_PULSE` +
   **H_NO_REVERT** (inside each zone, once the output shows the new value it
   keeps it) give a `Ret` of band `[lo, hi]`, i.e. exactly B's hypothesis
   form. And conversely (`no_revert_of_ret`) under `H_SPREAD_PULSE` every
   such `Ret` satisfies H_NO_REVERT. So, under the spacing, **B's FIFO
   hypothesis is equivalent to `Win` + H_NO_REVERT**: the only part of
   FIFO that is not derived from the window channel is glitch freedom inside
   each edge's own uncertainty zone, which result 1 shows is not derivable.
4. **Instances.** `ctl_of_win`: `PipeTimed.Ctl` (the `bd_link_ctl` LUT,
   `H_LUT_FIFO`) from a `Win` LUT, H_NO_REVERT and the loop form of the
   spacing (`H_LOOP`: the next excitation edge comes at least `D` after the
   node's own output edge; `H_BAND`: `hi < 2 lo + D`).
   `steer_wq_of_win`: the steer's `H_WQ` (`H_WIRE_FIFO`, req → u.I0) from a
   `Win` wire on a request that is clean from time 0. `uenv1_band`: H_BAND
   on the rig's binding C-element (B-gcd-routes.md), with numbers.
5. Non-vacuity (`Wit`): a 100-tick delay of a clean alternating input in the
   band `[45, 124]` satisfies Win, H_SPREAD_PULSE and H_NO_REVERT
   (`Wit.wit`, `Wit.wit_fifo`) and all hypotheses of `steer_wq_of_win`
   (`Wit.steer_wit`). `ctl_of_win` has no separate witness.

Core Lean only.
-/

namespace Formal.Cells.WinFifo
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.FifoFidelity (idx idx_spec idx_mono)

abbrev Win := CElemTiming.WinDelay

/-- Shard A's substrate channel is this channel (A's `Legacy.win_iff_winDelay`). -/
theorem win_iff {lo hi : Nat} {x y : Trace} :
    Formal.Core.Substrate.Win lo hi x y ↔ Win lo hi x y := Iff.rfl

/-- A nonempty window has `lo ≤ hi`. -/
theorem win_le {lo hi : Nat} {x y : Trace} (h : Win lo hi x y) : lo ≤ hi := by
  obtain ⟨s, h1, h2, _⟩ := h hi (Nat.le_refl _); omega

/-! ## 0. Clean inputs -/

/-- **A clean input from time 0**: edges `c j` (strictly increasing,
`c 0 = 0`), value `val j` on `[c j, c (j+1))`. -/
structure Clean (x : Trace) (c : Nat → Nat) (val : Nat → Bool) : Prop where
  c0 : c 0 = 0
  mono : ∀ i j, i < j → c i < c j
  val : ∀ j s, c j ≤ s → s < c (j + 1) → x s = val j

/-- **H_SPREAD_PULSE**: consecutive input edges are more than `hi - lo` apart. -/
def Spread (lo hi : Nat) (c : Nat → Nat) : Prop := ∀ j, 1 ≤ j → c j + hi < c (j + 1) + lo

theorem smono_of_succ (f : Nat → Nat) (h : ∀ j, f j < f (j + 1)) : ∀ i j, i < j → f i < f j := by
  intro i j hij
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h' | h'
    · have := ih h'; have := h j; omega
    · have : i = j := by omega
      subst this; exact h i

theorem dec_eq {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  by_cases hp : p
  · rw [decide_eq_true hp, decide_eq_true (h.1 hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.2 hq))]

/-! ## 1. `Win` is FIFO iff the band is at most one tick wide -/

/-- **Narrow band ⇒ FIFO, for every input.** If `hi ≤ lo + 1`, every window
behaviour is a FIFO read with band `[lo, hi]`. -/
theorem win_fifo_narrow {lo hi : Nat} {x y : Trace} (hn : hi ≤ lo + 1) (h : Win lo hi x y) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  have hlh := win_le h
  refine ⟨{ σ := fun t => if x (t - hi) = y t then t - hi else t - lo, lo := lo, hi := hi,
            mono := ?_, ge := ?_, le := ?_ }, rfl, rfl, ?_⟩
  · intro a b hab
    rcases Nat.lt_or_ge a b with h' | h'
    · show (if x (a - hi) = y a then a - hi else a - lo) ≤ (if x (b - hi) = y b then b - hi else b - lo)
      split <;> split <;> omega
    · have : a = b := by omega
      subst this; exact Nat.le_refl _
  · intro t; show t - hi ≤ (if x (t - hi) = y t then t - hi else t - lo); split <;> omega
  · intro t; show (if x (t - hi) = y t then t - hi else t - lo) ≤ t - lo; split <;> omega
  · intro t ht
    show y t = x (if x (t - hi) = y t then t - hi else t - lo)
    split
    · rename_i e; exact e.symm
    · rename_i e
      obtain ⟨s, h1, h2, h3⟩ := h t ht
      have : s = t - hi ∨ s = t - lo := by omega
      rcases this with hs | hs
      · subst hs; exact absurd h3.symm e
      · rw [← hs]; exact h3

/-- A single rising edge at `c`. -/
def step (c : Nat) : Trace := fun s => decide (c ≤ s)

/-- A `Win` output of `step c` that glitches: 1 at `c + lo`, 0 at
`c + lo + 1`, 1 from `c + lo + 2` on. -/
def glitch (c lo : Nat) : Trace := fun t => decide (c + lo ≤ t ∧ t ≠ c + lo + 1)

theorem glitch_win {c lo hi : Nat} (h2 : lo + 2 ≤ hi) : Win lo hi (step c) (glitch c lo) := by
  intro t ht
  by_cases h1 : t = c + lo + 1
  · refine ⟨t - hi, by omega, by omega, ?_⟩
    simp only [glitch, step]
    apply dec_eq; constructor <;> intro h <;> omega
  · refine ⟨t - lo, by omega, by omega, ?_⟩
    simp only [glitch, step]
    apply dec_eq; constructor <;> intro h <;> omega

/-- **No spacing makes `Win` FIFO.** For every `lo` and every `hi ≥ lo + 2`,
the input `step hi` (ONE edge, so every spacing hypothesis holds) has a
`Win lo hi` output that no FIFO read of band `hi' ≤ hi` reproduces. -/
theorem win_glitch_not_fifo {lo hi : Nat} (h2 : lo + 2 ≤ hi) :
    Win lo hi (step hi) (glitch hi lo) ∧
    ∀ r : Ret, r.hi ≤ hi → ¬ ∀ t, r.hi ≤ t → glitch hi lo t = step hi (r.σ t) := by
  refine ⟨glitch_win h2, fun r hr H => ?_⟩
  have a := H (hi + lo) (by omega)
  have b := H (hi + lo + 1) (by omega)
  have m := r.mono (hi + lo) (hi + lo + 1) (by omega)
  simp [glitch, step] at a b
  omega

/-! ## 2. What spacing gives: settled stretches, adjacent values, no swallow -/

/-- **Settled stretch.** After edge `j` has crossed the whole band and
before edge `j+1` can arrive, the output shows `val j`. (No spacing needed;
`H_SPREAD_PULSE` is exactly what makes the stretch nonempty.) -/
theorem win_settled {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hx : Clean x c val) :
    ∀ j t, hi ≤ t → c j + hi ≤ t → t < c (j + 1) + lo → y t = val j := by
  intro j t h0 h1 h2
  obtain ⟨s, s1, s2, s3⟩ := hW t h0
  rw [s3]; exact hx.val j s (by omega) (by omega)

/-- **Adjacent values only (no overtaking).** Inside edge `j`'s uncertainty
zone the output shows the value before or after edge `j`, nothing older or
newer. -/
theorem win_zone {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hx : Clean x c val) (hsp : Spread lo hi c) :
    ∀ j t, 1 ≤ j → hi ≤ t → c j + lo ≤ t → t < c j + hi → y t = val (j - 1) ∨ y t = val j := by
  intro j t hj h0 h1 h2
  obtain ⟨s, s1, s2, s3⟩ := hW t h0
  have hj1 := hsp j hj
  rw [s3]
  rcases Nat.lt_or_ge s (c j) with h | h
  · left
    have hlow : c (j - 1) ≤ s := by
      rcases Nat.lt_or_ge j 2 with h' | h'
      · have : j - 1 = 0 := by omega
        rw [this, hx.c0]; exact Nat.zero_le _
      · have := hsp (j - 1) (by omega)
        have e : j - 1 + 1 = j := by omega
        rw [e] at this; omega
    exact hx.val (j - 1) s hlow (by have e : j - 1 + 1 = j := by omega
                                    rw [e]; exact h)
  · right; exact hx.val j s h (by omega)

/-- A pulse of width `w` at `c`. -/
def pulse (c w : Nat) : Trace := fun s => decide (c ≤ s ∧ s < c + w)

/-- **Exactness of H_SPREAD_PULSE (swallow).** A pulse whose two edges are
at most `hi - lo` apart can vanish: the constant output is a `Win lo hi`
behaviour of it. So no theorem "every input edge shows on the output" holds
for `Win` at separation `≤ hi - lo`. -/
theorem win_swallow {lo hi c w : Nat} (hw1 : 1 ≤ w) (hw : w ≤ hi - lo) :
    Win lo hi (pulse c w) (fun _ => false) := by
  intro t ht
  by_cases h : t - hi < c
  · exact ⟨t - hi, by omega, by omega, by simp only [pulse]; apply Eq.symm; apply decide_eq_false; omega⟩
  · exact ⟨t - lo, by omega, by omega, by simp only [pulse]; apply Eq.symm; apply decide_eq_false; omega⟩

/-- The swallowed pulse is a clean input with edges `0, c, c + w, c + w + 1, …`. -/
def pc (c w : Nat) : Nat → Nat
  | 0 => 0
  | 1 => c
  | j + 2 => c + w + j

def pv : Nat → Bool
  | 1 => true
  | _ => false

theorem pulse_clean {c w : Nat} (hc : 1 ≤ c) (hw : 1 ≤ w) : Clean (pulse c w) (pc c w) pv where
  c0 := rfl
  mono := smono_of_succ _ (fun j => by
    match j with
    | 0 => simp [pc] <;> omega
    | 1 => simp [pc] <;> omega
    | j + 2 => simp [pc] <;> omega)
  val j s h1 h2 := by
    match j with
    | 0 => simp only [pc] at h1 h2; simp only [pulse, pv]; apply decide_eq_false; omega
    | 1 => simp only [pc] at h1 h2; simp only [pulse, pv]; apply decide_eq_true; omega
    | j + 2 => simp only [pc] at h1 h2; simp only [pulse, pv]; apply decide_eq_false; omega

/-- Non-vacuity of the swallow: with `[lo, hi] = [45, 124]` (prjxray LUT6
O6 box, ps) a 79 ps pulse is a clean input and its constant output is a
`Win` behaviour that never shows the pulse. -/
theorem swallow_witness :
    Clean (pulse 200 79) (pc 200 79) pv ∧ Win 45 124 (pulse 200 79) (fun _ => false) ∧
    pv 1 = true :=
  ⟨pulse_clean (by omega) (by omega), win_swallow (by omega) (by omega), rfl⟩

/-! ## 3. The bridge: `Win` + spacing + H_NO_REVERT ⇔ FIFO -/

/-- **The FIFO read built from the output edges `e`** (`e 0 = 0`, edge `j ≥ 1`
inside zone `j`, strictly increasing). -/
theorem ret_of_zones {lo hi : Nat} {x y : Trace} {c e : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hx : Clean x c val) (he0 : e 0 = 0)
    (hemono : ∀ i j, i < j → e i < e j)
    (hez : ∀ j, 1 ≤ j → c j + lo ≤ e j ∧ e j ≤ c j + hi)
    (h1 : ∀ j t, 1 ≤ j → hi ≤ t → c j + lo ≤ t → t < c j + hi →
      y t = if e j ≤ t then val j else val (j - 1)) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  have hlh := win_le hW
  have cm : ∀ a b, a ≤ b → c a ≤ c b := fun a b h => by
    rcases Nat.lt_or_ge a b with h' | h'
    · exact Nat.le_of_lt (hx.mono _ _ h')
    · have : a = b := by omega
      rw [this]; exact Nat.le_refl _
  have c0 := hx.c0
  refine ⟨{ σ := fun t => max (c (idx e t)) (t - hi), lo := lo, hi := hi,
            mono := ?_, ge := ?_, le := ?_ }, rfl, rfl, ?_⟩
  · intro a b hab
    have := cm _ _ (idx_mono e he0 hemono hab)
    show max (c (idx e a)) (a - hi) ≤ max (c (idx e b)) (b - hi)
    omega
  · intro t; exact Nat.le_max_right _ _
  · intro t
    show max (c (idx e t)) (t - hi) ≤ t - lo
    have s := idx_spec e he0 hemono t
    rcases Nat.eq_zero_or_pos (idx e t) with hk | hk
    · rw [hk, c0]; omega
    · have := hez (idx e t) hk; omega
  · intro t ht
    show y t = x (max (c (idx e t)) (t - hi))
    have s := idx_spec e he0 hemono t
    generalize hk : idx e t = k at s
    have z1 := hez (k + 1) (by omega)
    have cs := hx.mono k (k + 1) (by omega)
    have hxs : x (max (c k) (t - hi)) = val k := hx.val k _ (Nat.le_max_left _ _) (by omega)
    rw [hxs]
    by_cases hA : c (k + 1) + lo ≤ t
    · have := h1 (k + 1) t (by omega) ht hA (by omega)
      rw [this, if_neg (by omega)]; rfl
    · by_cases hB : 1 ≤ k ∧ t < c k + hi
      · have zk := hez k hB.1
        have := h1 k t hB.1 ht (by omega) hB.2
        rw [this, if_pos s.1]
      · obtain ⟨q, q1, q2, q3⟩ := hW t ht
        rw [q3]
        apply hx.val k q _ (by omega)
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, c0]; exact Nat.zero_le _
        · omega

/-- **Bridge, explicit output edges.** `Win` + `H_SPREAD_PULSE` + **H_ONE_EDGE**
(one output edge `e j` inside each zone `j`, the output stepping there from
`val (j-1)` to `val j`) give B's FIFO form with band `[lo, hi]`. The spacing
is what puts the output edges in input order. -/
theorem win_fifo_of_one_edge {lo hi : Nat} {x y : Trace} {c e : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hx : Clean x c val) (hsp : Spread lo hi c) (he0 : e 0 = 0)
    (hez : ∀ j, 1 ≤ j → c j + lo ≤ e j ∧ e j ≤ c j + hi)
    (h1 : ∀ j t, 1 ≤ j → hi ≤ t → c j + lo ≤ t → t < c j + hi →
      y t = if e j ≤ t then val j else val (j - 1)) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  have hemono : ∀ i j, i < j → e i < e j := smono_of_succ e (fun j => by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; have := hez 1 (by omega); have := hx.mono 0 1 (by omega); rw [hx.c0] at this
      show e 0 < e 1; have := he0; omega
    · have := hez j h0; have := hez (j + 1) (by omega); have := hsp j h0; omega)
  exact ret_of_zones hW hx he0 hemono hez h1

/-- A monotone Boolean predicate on `[a, a + n)` has a threshold. -/
theorem threshold (p : Nat → Bool) (a : Nat) : ∀ n,
    (∀ t1 t2, a ≤ t1 → t1 ≤ t2 → t2 < a + n → p t1 = true → p t2 = true) →
    ∃ e, a ≤ e ∧ e ≤ a + n ∧ ∀ t, a ≤ t → t < a + n → (p t = true ↔ e ≤ t) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨a, by omega, by omega, fun t h1 h2 => by omega⟩
  | succ n ih =>
    intro hm
    obtain ⟨e0, e1, e2, e3⟩ := ih (fun t1 t2 h1 h2 h3 => hm t1 t2 h1 h2 (by omega))
    rcases Nat.lt_or_ge e0 (a + n) with hl | hl
    · refine ⟨e0, e1, by omega, fun t h1 h2 => ?_⟩
      by_cases ht : t < a + n
      · exact e3 t h1 ht
      · have pe : p e0 = true := (e3 e0 e1 hl).2 (Nat.le_refl _)
        exact ⟨fun _ => by omega, fun _ => hm e0 t e1 (by omega) h2 pe⟩
    · by_cases hp : p (a + n) = true
      · refine ⟨a + n, by omega, by omega, fun t h1 h2 => ?_⟩
        by_cases ht : t < a + n
        · have := e3 t h1 ht
          constructor
          · intro h; have := this.1 h; omega
          · intro h; omega
        · have : t = a + n := by omega
          subst this; exact ⟨fun _ => Nat.le_refl _, fun _ => hp⟩
      · refine ⟨a + n + 1, by omega, by omega, fun t h1 h2 => ?_⟩
        by_cases ht : t < a + n
        · have := e3 t h1 ht
          constructor
          · intro h; have := this.1 h; omega
          · intro h; omega
        · have : t = a + n := by omega
          subst this
          exact ⟨fun h => absurd h hp, fun h => by omega⟩

/-- **H_NO_REVERT**: inside edge `j`'s uncertainty zone, once the output
shows the new value `val j` it keeps it until the zone ends. This is the
glitch-freedom part of FIFO, the part `win_glitch_not_fifo` shows `Win`
cannot supply. -/
def NoRevert (lo hi : Nat) (y : Trace) (c : Nat → Nat) (val : Nat → Bool) : Prop :=
  ∀ j t1 t2, 1 ≤ j → hi ≤ t1 → c j + lo ≤ t1 → t1 ≤ t2 → t2 < c j + hi →
    y t1 = val j → y t2 = val j

/-- H_NO_REVERT gives the explicit output edges of H_ONE_EDGE. -/
theorem one_edge_of_no_revert {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hx : Clean x c val) (hsp : Spread lo hi c)
    (hnr : NoRevert lo hi y c val) :
    ∃ e : Nat → Nat, e 0 = 0 ∧ (∀ j, 1 ≤ j → c j + lo ≤ e j ∧ e j ≤ c j + hi) ∧
      (∀ j t, 1 ≤ j → hi ≤ t → c j + lo ≤ t → t < c j + hi →
        y t = if e j ≤ t then val j else val (j - 1)) := by
  have hlh := win_le hW
  have mx : ∀ j, c j + lo ≤ max (c j + lo) hi ∧ hi ≤ max (c j + lo) hi ∧
      max (c j + lo) hi ≤ c j + hi := fun j =>
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _, Nat.max_le.mpr ⟨by omega, by omega⟩⟩
  have H : ∀ j, ∃ e, max (c j + lo) hi ≤ e ∧ e ≤ max (c j + lo) hi + (c j + hi - max (c j + lo) hi) ∧
      ∀ t, max (c j + lo) hi ≤ t → t < max (c j + lo) hi + (c j + hi - max (c j + lo) hi) →
        ((y t == val j) = true ↔ e ≤ t) := fun j =>
    threshold (fun t => y t == val j) _ _ (fun t1 t2 h1 h2 h3 hp => by
      have := mx j
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; rw [hx.c0] at h3; omega
      · have := hnr j t1 t2 h0 (by omega) (by omega) h2 (by omega) (by simpa using hp)
        simpa using this)
  refine ⟨fun j => if j = 0 then 0 else Classical.choose (H j), by simp, ?_, ?_⟩
  · intro j hj
    have s := Classical.choose_spec (H j)
    have := mx j
    simp only [if_neg (show j ≠ 0 by omega)]
    omega
  · intro j t hj h0 h1 h2
    have s := Classical.choose_spec (H j)
    have := mx j
    simp only [if_neg (show j ≠ 0 by omega)]
    have st := s.2.2 t (by omega) (by omega)
    split
    · rename_i hle; have := st.2 hle; simpa using this
    · rename_i hle
      have hne : y t ≠ val j := fun h => hle (st.1 (by simp [h]))
      rcases win_zone hW hx hsp j t hj h0 h1 h2 with h | h
      · exact h
      · exact absurd h hne

/-- **THE BRIDGE.** `Win lo hi` + clean input + `H_SPREAD_PULSE` +
H_NO_REVERT ⇒ B's FIFO hypothesis form, band `[lo, hi]`. -/
theorem win_fifo_of_no_revert {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hx : Clean x c val) (hsp : Spread lo hi c)
    (hnr : NoRevert lo hi y c val) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  obtain ⟨e, he0, hez, h1⟩ := one_edge_of_no_revert hW hx hsp hnr
  exact win_fifo_of_one_edge hW hx hsp he0 hez h1

/-- **Converse**: under `H_SPREAD_PULSE`, every FIFO read of band `[lo, hi]`
is a `Win` behaviour satisfying H_NO_REVERT. With the bridge: under the
spacing, B's FIFO hypothesis IS `Win` + H_NO_REVERT. -/
theorem no_revert_of_ret {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hx : Clean x c val) (hsp : Spread lo hi c) (r : Ret) (hl : r.lo = lo) (hh : r.hi = hi)
    (hy : ∀ t, hi ≤ t → y t = x (r.σ t)) :
    Win lo hi x y ∧ NoRevert lo hi y c val := by
  refine ⟨?_, ?_⟩
  · have := PipeTimed.fifo_win r (x := x) (y := y) (fun t ht => hy t (by omega))
    rw [hl, hh] at this; exact this
  · intro j t1 t2 hj h0 h1 h12 h2 hv
    have hs := hsp j hj
    have g1 := r.ge t1; have l1 := r.le t1; have g2 := r.ge t2; have l2 := r.le t2
    have m := r.mono t1 t2 h12
    rw [hl] at l1 l2; rw [hh] at g1 g2
    rw [hy t1 h0] at hv
    rw [hy t2 (by omega)]
    -- `r.σ t1` reads at or after edge `j`, otherwise `val (j-1)` would show
    rcases Nat.lt_or_ge (r.σ t1) (c j) with h | h
    · -- then `r.σ t1` is in segment `j - 1`, and the value there must be `val j`
      have lowj : c (j - 1) ≤ r.σ t1 := by
        rcases Nat.lt_or_ge j 2 with h' | h'
        · have : j - 1 = 0 := by omega
          rw [this, hx.c0]; exact Nat.zero_le _
        · have := hsp (j - 1) (by omega)
          have e : j - 1 + 1 = j := by omega
          rw [e] at this; omega
      have v1 := hx.val (j - 1) (r.σ t1) lowj (by have e : j - 1 + 1 = j := by omega
                                                  rw [e]; exact h)
      rw [v1] at hv
      -- t2's read is in segment j-1 or j; both values equal val j
      rcases Nat.lt_or_ge (r.σ t2) (c j) with h' | h'
      · have v2 := hx.val (j - 1) (r.σ t2) (by omega) (by have e : j - 1 + 1 = j := by omega
                                                          rw [e]; exact h')
        rw [v2]; exact hv
      · exact hx.val j _ h' (by omega)
    · exact hx.val j _ (by omega) (by omega)

/-! ## 4. Instances -/

/-- **H_LOOP + H_BAND ⇒ H_SPREAD_PULSE.** If each next input edge waits at
least `D` after the output edge of the previous one (`H_LOOP`, the cell's
four-phase protocol: the next excitation edge needs the node's edge to go
round the loop), and the output edge comes at least `lo` after its input edge,
then the spacing holds as soon as `hi < 2 lo + D` (`H_BAND`), i.e. the
band's spread `hi - lo` is below the minimum phase `lo + D`. -/
theorem spread_of_loop {lo hi D : Nat} {c e : Nat → Nat}
    (hez : ∀ j, 1 ≤ j → c j + lo ≤ e j)
    (hloop : ∀ j, 1 ≤ j → e j + D ≤ c (j + 1)) (hband : hi < 2 * lo + D) : Spread lo hi c := by
  intro j hj; have := hez j hj; have := hloop j hj; omega

/-- **`H_LUT_FIFO` of the `bd_link_ctl` controller from a window LUT.**
Assumed: the LUT is a `Win lo hi` channel of the pin-level excitation
(shard A's channel); the excitation is clean from time 0 with edges `c`
(H_EX_CLEAN, the run-by-run premise also used by `FifoFidelity.pinlut_fifo_of_edges`);
the node has ONE edge `e j` per excitation edge, inside its zone
(H_ONE_EDGE); `H_LOOP` with loop delay `D` and `H_BAND`; and Ctl's own
`H_FB`, `H_LOOP_POS`. Proved: `PipeTimed.Ctl` with a FIFO LUT of band
`[lo, hi]`, so every `PipeTimed`/`PipeTimedN` theorem applies to this run. -/
theorem ctl_of_win {req ack rst O qp : Trace} {lo hi wl wh D : Nat} {c e : Nat → Nat}
    {val : Nat → Bool}
    (hW : Win lo hi (PipeTimed.ex req ack qp rst) O)
    (hx : Clean (PipeTimed.ex req ack qp rst) c val) (he0 : e 0 = 0)
    (hez : ∀ j, 1 ≤ j → c j + lo ≤ e j ∧ e j ≤ c j + hi)
    (h1 : ∀ j t, 1 ≤ j → hi ≤ t → c j + lo ≤ t → t < c j + hi →
      O t = if e j ≤ t then val j else val (j - 1))
    (hloop : ∀ j, 1 ≤ j → e j + D ≤ c (j + 1)) (hband : hi < 2 * lo + D)
    (hFB : CElemTiming.WinDelay wl wh O qp) (hpos : 1 ≤ lo + wl) :
    ∃ L : Ret, L.lo = lo ∧ L.hi = hi ∧ PipeTimed.Ctl req ack rst O qp L wl wh := by
  have hsp := spread_of_loop (fun j hj => (hez j hj).1) hloop hband
  obtain ⟨L, hl, hh, hr⟩ := win_fifo_of_one_edge hW hx hsp he0 hez h1
  exact ⟨L, hl, hh, ⟨fun t ht => hr t (by omega), hFB, by omega⟩⟩

/-- **H_BAND on the binding routed C-element** (B-gcd-routes.md, `urig.uenv1`,
seed 4, the thinnest H_SELORD instance): earliest response from the node's
own O6 edge to a non-feedback mux select `E = 440 ps` at FAST_MIN. Box
reading of the LUT6 O6 arc (prjxray (45::56)(100::124)): `lo = 45`
(FAST_MIN), `hi = 124` (SLOW_MAX). Taking `D = E - 172` (less the largest
FAST_MIN site-pin delay, A1, so `D` counts from the O6 edge to the pin, as
the lumped excitation needs) gives `124 < 2·45 + 268`; margin 234 ps. With the
SLOW corner alone (`lo = 100`, `hi = 124`) the spread is 24 ps. -/
theorem uenv1_band : 124 < 2 * 45 + (440 - 172) ∧ 124 < 2 * 100 + (440 - 172) := by decide

/-- A token trace clean from time 0 (request low before `ρ 0 ≥ 1`) is a
clean input with edges `0, ρ 0, ρ 1, …`. -/
theorem clean_of_tok {req : Trace} {ρ : Nat → Nat} (h : OpsTimed.Tok 0 req ρ (fun _ => true))
    (hρ0 : 1 ≤ ρ 0) (hρ : ∀ j, ρ j < ρ (j + 1)) :
    Clean req (fun j => match j with | 0 => 0 | j + 1 => ρ j)
      (fun j => match j with | 0 => false | j + 1 => j % 2 == 0) where
  c0 := rfl
  mono := smono_of_succ _ (fun j => by
    match j with
    | 0 => show 0 < ρ 0; omega
    | j + 1 => show ρ j < ρ (j + 1); exact hρ j)
  val j s h1 h2 := by
    match j with
    | 0 => exact h.pre s (Nat.zero_le _) h2
    | j + 1 =>
      simp only at h1 h2 ⊢
      have hd := Nat.div_add_mod j 2
      rcases Nat.mod_two_eq_zero_or_one j with hm | hm
      · have := h.hi (j / 2) s (Nat.zero_le _) (by rw [show 2 * (j / 2) = j by omega]; exact h1)
          (by rw [show 2 * (j / 2) + 1 = j + 1 by omega]; exact h2)
        rw [this, hm]; rfl
      · have := h.lo (j / 2) s (Nat.zero_le _) (by rw [show 2 * (j / 2) + 1 = j by omega]; exact h1)
          (by rw [show 2 * (j / 2) + 2 = j + 1 by omega]; exact h2)
        rw [this, hm]; rfl

/-- **The steer's `H_WQ` (`H_WIRE_FIFO`, req → u.I0) from a window wire.**
Assumed: the sender's request is a clean four-phase trace from time 0
(`H_REQ` with `Tr = 0`, `ρ` strictly increasing, `ρ 0 ≥ 1`); the wire is
`Win lo hi`; H_NO_REVERT at u.I0; `H_SPREAD_PULSE` on the request edges
(from `spread_of_loop` with the steer's loop, see `OpsTimed.steer_gap`).
Proved: a `Ret` of band `[lo, hi]` with exactly the field `SteerGates.H_WQ`. -/
theorem steer_wq_of_win {req rqu : Trace} {ρ : Nat → Nat} {lo hi : Nat}
    (hreq : OpsTimed.Tok 0 req ρ (fun _ => true)) (hρ0 : 1 ≤ ρ 0) (hρ : ∀ j, ρ j < ρ (j + 1))
    (hW : Win lo hi req rqu)
    (hsp : ∀ j, ρ j + hi < ρ (j + 1) + lo)
    (hnr : NoRevert lo hi rqu (fun j => match j with | 0 => 0 | j + 1 => ρ j)
      (fun j => match j with | 0 => false | j + 1 => j % 2 == 0)) :
    ∃ Wq : Ret, Wq.lo = lo ∧ Wq.hi = hi ∧ ∀ t, Wq.hi ≤ t → rqu t = req (Wq.σ t) := by
  have hx := clean_of_tok hreq hρ0 hρ
  have hs : Spread lo hi (fun j => match j with | 0 => 0 | j + 1 => ρ j) := by
    intro j hj
    match j with
    | 0 => omega
    | j + 1 => simpa using hsp j
  obtain ⟨r, hl, hh, hr⟩ := win_fifo_of_no_revert hW hx hs hnr
  exact ⟨r, hl, hh, fun t ht => hr t (by omega)⟩

/-! ## 5. Non-vacuity of the bridge

A fixed delay `d ∈ [lo, hi]` of a clean input satisfies every hypothesis
(Win, H_SPREAD_PULSE, H_NO_REVERT), with a genuinely wide band. -/
namespace Wit

/-- Input: edges at 0, 200, 500, 800, … (value alternates). -/
def c : Nat → Nat
  | 0 => 0
  | j + 1 => 200 + 300 * j

def val (j : Nat) : Bool := j % 2 == 1

def x : Trace := fun s => val (FifoFidelity.idx c s)

theorem c_mono : ∀ i j, i < j → c i < c j :=
  smono_of_succ c (fun j => by match j with
    | 0 => simp [c]
    | j + 1 => simp [c] <;> omega)

theorem x_clean : Clean x c val where
  c0 := rfl
  mono := c_mono
  val j s h1 h2 := by
    have sp := idx_spec c rfl c_mono s
    have a := FifoFidelity.lastLe_max c s s j (by have := FifoFidelity.ge_idx c c_mono j; omega) h1
    have b : FifoFidelity.idx c s ≤ j := by
      apply Classical.byContradiction; intro hn
      have : c (j + 1) ≤ c (FifoFidelity.idx c s) := by
        rcases Nat.lt_or_ge (j + 1) (FifoFidelity.idx c s) with h | h
        · exact Nat.le_of_lt (c_mono _ _ h)
        · have : FifoFidelity.idx c s = j + 1 := by omega
          rw [this]; exact Nat.le_refl _
      omega
    have : FifoFidelity.idx c s = j := by unfold FifoFidelity.idx at b; unfold FifoFidelity.idx; omega
    simp [x, this]

/-- Output: `x` delayed by 100 (inside the band `[45, 124]`). -/
def y : Trace := fun t => x (t - 100)

theorem wit :
    Win 45 124 x y ∧ Spread 45 124 c ∧ NoRevert 45 124 y c val := by
  refine ⟨fun t ht => ⟨t - 100, by omega, by omega, rfl⟩, fun j hj => ?_, ?_⟩
  · match j with
    | 0 => omega
    | j + 1 => simp [c]; omega
  · intro j t1 t2 hj h0 h1 h12 h2 hv
    -- t1 - 100 and t2 - 100 are both in [c j - 55, c j + 24); value val j
    -- holds at t1 only if t1 - 100 ≥ c j, then also at t2.
    have hc := x_clean
    rcases Nat.lt_or_ge (t1 - 100) (c j) with h | h
    · -- t1 reads segment j-1, value val (j-1) ≠ val j: contradiction
      exfalso
      match j, hj with
      | j + 1, _ =>
        have hlo : c j ≤ t1 - 100 := by
          match j with
          | 0 => simp [c]
          | j + 1 => simp [c] at h1 h ⊢; omega
        have v := hc.val j (t1 - 100) hlo h
        simp only [y] at hv
        rw [v] at hv
        simp only [val] at hv
        rcases Nat.mod_two_eq_zero_or_one j with hm | hm
        · have hm' : (j + 1) % 2 = 1 := by omega
          rw [hm, hm'] at hv; exact absurd hv (by decide)
        · have hm' : (j + 1) % 2 = 0 := by omega
          rw [hm, hm'] at hv; exact absurd hv (by decide)
    · simp only [y]
      have hn : t2 - 100 < c (j + 1) := by
        match j, hj with
        | j + 1, _ => simp [c] at h2 ⊢; omega
      exact hc.val j _ (by omega) hn

/-- The bridge fires on the witness. -/
theorem wit_fifo : ∃ r : Ret, r.lo = 45 ∧ r.hi = 124 ∧ ∀ t, 124 ≤ t → y t = x (r.σ t) :=
  win_fifo_of_no_revert wit.1 x_clean wit.2.1 wit.2.2

/-- Non-vacuity of `steer_wq_of_win`: the witness input is a clean token
trace from time 0 (`ρ j = c (j+1)`), and all its hypotheses hold. -/
def ρ (j : Nat) : Nat := c (j + 1)

theorem c_eq : (fun j => match j with | 0 => 0 | j + 1 => ρ j) = c := by
  funext j; match j with
  | 0 => rfl
  | j + 1 => rfl

theorem val_eq : (fun j => match j with | 0 => false | j + 1 => j % 2 == 0) = val := by
  funext j; match j with
  | 0 => rfl
  | j + 1 =>
    show (j % 2 == 0) = ((j + 1) % 2 == 1)
    rcases Nat.mod_two_eq_zero_or_one j with hm | hm
    · have hm' : (j + 1) % 2 = 1 := by omega
      rw [hm, hm']; rfl
    · have hm' : (j + 1) % 2 = 0 := by omega
      rw [hm, hm']; rfl

theorem tok : OpsTimed.Tok 0 x ρ (fun _ => true) where
  pre t _ h := x_clean.val 0 t (Nat.zero_le _) h
  hi k t _ h1 h2 := by
    have := x_clean.val (2 * k + 1) t h1 h2
    rw [this]; simp [val] <;> omega
  lo k t _ h1 h2 := by
    have := x_clean.val (2 * k + 2) t h1 h2
    rw [this]; simp [val] <;> omega

theorem steer_wit : ∃ Wq : Ret, Wq.lo = 45 ∧ Wq.hi = 124 ∧ ∀ t, Wq.hi ≤ t → y t = x (Wq.σ t) := by
  refine steer_wq_of_win (ρ := ρ) tok (by decide) (fun j => c_mono (j + 1) (j + 2) (by omega)) wit.1
    (fun j => by have := wit.2.1 (j + 1) (by omega); exact this) ?_
  rw [c_eq, val_eq]; exact wit.2.2

end Wit

end Formal.Cells.WinFifo
