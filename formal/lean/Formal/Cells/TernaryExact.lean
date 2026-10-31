import Formal.Core.LutList
import Formal.Cells.TernarySound
import Formal.Cells.TernaryPhases
open Formal.Core.LutList

/-!
# Probe 7l: exactness of two-phase ternary simulation (Algorithms A and B)

Probe 7f (`TernarySound.lean`) proved that Algorithms A and B are SOUND for a
general LUT network in the GMW model with per-pin wire delays (`Run`,
`Bounded`). This file proves the converse for the same networks and the same
model. Nothing assumes the network is acyclic: feedback is handled the same
way as everything else.

Setting: `c0` is a stable binary state (`hstab`: every gate equals its LUT
value on `c0`). The inputs go from `c0` to the final vector `a'`. Algorithm A
runs from `s0 c0` with an input vector `u` that admits both `c0` and `a'` on
every input (`hu`). `u = c0 ⊔ a'` is the single-change case. `u = x` on an
input whose final value equals its old one allows a glitch.

* **A is exact** (`A_exact`). If A's iteration is fixed at `mA`, then a gate
  is `x` in A's result IFF some bounded run changes it (start `c0`, inputs
  inside `u`, final from step 2). `A_change_sound` gives the `←` direction for
  every run, bounded or not.
* **A is exact even with FIXED wire delays** (`A_exact_fixed`). One run, in
  which every wire `(j, p)` has a constant transport delay `d j p` and the
  gates are GMW, changes every A-`x` gate. It needs unbounded gate delay: a
  gate holds its new value.
* **B is exact** (`B_exact`). If B's iteration (from A's result, inputs `a'`)
  is fixed at `mB`, then a gate is `x` in the A-then-B result IFF some
  bounded run never settles on it. In the other direction, definite nodes
  settle in every bounded run (7f's `algB_settles`).
* **B is exact with a FIFO witness** (`B_exact_fifo`, `tv_run`). The same
  iff holds with a witness that has unit gate delay and every wire 0 or 1 step
  old (`D = 0`, `W = 1`), with each wire's read times non-decreasing (no
  reordering, no non-FIFO reads). The price: an input that `u` marks `x`
  toggles at every step until `mA`, which is a glitch train inside `u`, not
  one clean edge. `A_witness_fifo` is the same run seen as a witness for A.
* **Non-vacuity** (`cel_runt_never_settles`, `cel_runt_never_settles_fifo`). The theorem is instantiated on
  7i's C-element (`bd_c2`, real INIT) in hold with a runt on b. It produces a
  bounded run in which q never settles.

One run, `wv`, witnesses every `x` at once (`exact_run`, `A_witness`,
`B_witness`):
* It follows the ternary sequence `σ`: A's iterates, then B's iterates. Each
  ternary step is stretched over two time steps.
* At time `t`, a gate whose `σ (t/2)` value is definite shows that value. A
  gate whose value is `x` shows the parity of `t`, so in every pair of steps
  it shows both values.
* A reader with a window of two steps can therefore find any completion of
  its pins (`exists_completion`, the converse of `lutK_sound`, plus
  `reads_exist`).
* Gates are unit delay: the output is the LUT value of the previous step's
  reads, so `H_GATE_BOUND` holds with `D = 0`.
* The inputs follow `inw`: old value at step 0, final value from step 2. At
  step 1 the input is the opposite of its old value if `u` marks it `x`.

## What the witness needs from the model

The witness lives in 7f's `Run` model. Its wire hypotheses are
**H_WIRE_CAUSAL** (a pin sees some past value of its source) and
**H_WIRE_BOUND** `W` (that value is at most `W` steps old).
* In `wv`, the read times vary from step to step. For gate sources they lie
  in `[t-2, t]`. For input sources they are `0`, `1` or `t`: during phase A
  the old input value is read through a wire of delay up to `2·mA + 2`.
* The read times are NOT monotone in `t` (non-FIFO), and an `x` node toggles
  every step (a 1-step pulse train).

So `A_exact` and `B_exact` are exactness for 7f's per-pin-read model. They do
not cover inertial wires, which would swallow the pulses.
`A_exact_fixed` (constant wire delays, clean edge) and `B_exact_fifo` (FIFO
wires of delay 0 or 1, glitching inputs) each remove one of the two
liberties. A single witness with clean input edges, FIFO wires and bounded
gates for B is still open. See
`formal/notes/B-ternary-exact.md` for what is open.
-/

namespace Formal.Cells.TernaryExact
open Formal.Cells Formal.Cells.TernarySound

/-! ## Small K3 facts -/

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem le_ofBool_of_admits {z : K3} {b : Bool} (h : K3.admits z b = true) :
    le (K3.ofBool b) z := by
  cases z <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

/-- Read a K3 value as a Boolean; an `x` shows the supplied bit `p`. -/
def kval : K3 → Bool → Bool
  | .t, _ => true
  | .f, _ => false
  | .x, p => p

theorem kval_admits (z : K3) (p : Bool) : K3.admits z (kval z p) = true := by
  cases z <;> cases p <;> rfl

theorem kval_of_admits {z : K3} {b : Bool} (h : K3.admits z b = true) : kval z b = b := by
  cases z <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem kval_ofBool (b p : Bool) : kval (K3.ofBool b) p = b := by
  cases b <;> rfl

theorem admits_join {x y b : Bool} (h : K3.admits (K3.join (K3.ofBool x) (K3.ofBool y)) b = true) :
    b = x ∨ b = y := by
  revert h; cases x <;> cases y <;> cases b <;> decide

theorem admits_join_left (x y : Bool) : K3.admits (K3.join (K3.ofBool x) (K3.ofBool y)) x = true := by
  cases x <;> cases y <;> decide

theorem admits_join_right (x y : Bool) : K3.admits (K3.join (K3.ofBool x) (K3.ofBool y)) y = true := by
  cases x <;> cases y <;> decide

theorem join_x {x y : Bool} (h : K3.join (K3.ofBool x) (K3.ofBool y) = .x) : x ≠ y := by
  revert h; cases x <;> cases y <;> decide

/-! ## Completions: the converse direction of 7f's `mem_completions_of_forall2` -/

theorem forall2_of_mem_completions : ∀ (zs : List K3) (bs : List Bool),
    bs ∈ completions zs → Pw (fun z b => K3.admits z b = true) zs bs
  | [], bs, h => by
    simp [completions] at h; subst h; exact Pw.nil
  | a :: as, bs, h => by
    simp only [completions, List.mem_append] at h
    rcases h with h | h
    · split at h
      · next ha =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
        exact Pw.cons ha (forall2_of_mem_completions as w hw)
      · simp at h
    · split at h
      · next ha =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
        exact Pw.cons ha (forall2_of_mem_completions as w hw)
      · simp at h

/-- **Exactness of the Kleene LUT** (the converse of `lutK_sound`): every
value admitted by `lutK` is the `lutB` value of some completion. -/
theorem exists_completion (init : Nat) (zs : List K3) (b : Bool)
    (h : K3.admits (lutK init zs) b = true) : ∃ bs ∈ completions zs, lutB init bs = b := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ c ∈ completions zs, lutB init c = !b := by
    intro c hc
    cases hcb : lutB init c <;> cases b <;> first | rfl | exact absurd ⟨c, hc, hcb⟩ hne
  cases b
  · have : lutK init zs = .t := (lutK_eq_t_iff init zs).2 (fun c hc => by simpa using hall c hc)
    rw [this] at h; exact absurd h (by decide)
  · have : lutK init zs = .f := (lutK_eq_f_iff init zs).2 (fun c hc => by simpa using hall c hc)
    rw [this] at h; exact absurd h (by decide)

/-! ## Choosing read times that realise a completion -/

theorem pinsB_congr (rv rv' : Nat → Nat → Bool) : ∀ (pins : List Src) (p0 : Nat),
    (∀ p, p0 ≤ p → ∀ i, rv p i = rv' p i) → pinsB rv pins p0 = pinsB rv' pins p0
  | [], _, _ => rfl
  | s :: ss, p0, h => by
    simp only [pinsB]
    rw [pinsB_congr rv rv' ss (p0 + 1) (fun p hp i => h p (by omega) i)]
    cases s with
    | node i => simp only [srcB]; rw [h p0 (Nat.le_refl _) i]
    | const b => rfl

/-- If every value a pin's source may take (per the ternary state `s`) occurs
in the trace at some allowed time, then any completion of the pins can be
read with per-pin read times that are all allowed. -/
theorem reads_exist (v : Nat → Nat → Bool) (s : Nat → K3) (ok : Nat → Prop) (d : Nat)
    (hd : ok d) (hav : ∀ i b, K3.admits (s i) b = true → ∃ r, ok r ∧ v r i = b) :
    ∀ (pins : List Src) (bs : List Bool) (p0 : Nat),
      Pw (fun z b => K3.admits z b = true) (pins.map (srcK s)) bs →
      ∃ f : Nat → Nat, (∀ p, ok (f p)) ∧ pinsB (fun p i => v (f p) i) pins p0 = bs
  | [], bs, _, h => by
    rw [List.map_nil] at h
    cases h
    exact ⟨fun _ => d, fun _ => hd, rfl⟩
  | src :: ss, bs, p0, h => by
    rw [List.map_cons] at h
    cases h with
    | @cons _ b _ bs' hab hrest =>
      obtain ⟨f', hf'ok, hf'⟩ := reads_exist v s ok d hd hav ss bs' (p0 + 1) hrest
      cases src with
      | node i =>
        obtain ⟨r, hr, hvr⟩ := hav i b hab
        refine ⟨fun p => if p = p0 then r else f' p, ?_, ?_⟩
        · intro p
          by_cases hp : p = p0
          · show ok (if p = p0 then r else f' p)
            rw [ite_pos' hp]; exact hr
          · show ok (if p = p0 then r else f' p)
            rw [ite_neg' hp]; exact hf'ok p
        · show v (if p0 = p0 then r else f' p0) i :: _ = b :: bs'
          rw [ite_pos' rfl, hvr, ← hf']
          congr 1
          apply pinsB_congr
          intro p hp j
          show v (if p = p0 then r else f' p) j = _
          rw [ite_neg' (by omega)]
      | const c =>
        have hbc : b = c := (admits_ofBool_iff c b).1 hab
        subst hbc
        refine ⟨f', hf'ok, ?_⟩
        show b :: pinsB _ ss (p0 + 1) = b :: bs'
        rw [hf']

/-! ## The witness run -/

/-- The old stable state as a ternary state. -/
def s0 (c0 : Nat → Bool) : Nat → K3 := fun n => K3.ofBool (c0 n)

/-- The final input vector as a ternary vector. -/
def fin (a' : Nat → Bool) : Nat → K3 := fun n => K3.ofBool (a' n)

/-- The witness input trace: the old value at step 0, the final value from
step 2 on, and at step 1 the opposite of the old value if `u` marks the input
`x` (so a clean edge at step 1 if the input changes, and a one-step runt if
`u` marks it `x` but it ends where it started), else the final value. -/
def inw (c0 a' : Nat → Bool) (u : Nat → K3) (t i : Nat) : Bool :=
  if t = 0 then c0 i else if t = 1 then (if u i = .x then !c0 i else a' i) else a' i

/-- Inputs of the ternary sequence: `u` for the `mA` A-steps, then `a'`. -/
def uin (a' : Nat → Bool) (u : Nat → K3) (mA k : Nat) : Nat → K3 :=
  if k < mA then u else fin a'

/-- The ternary sequence: Algorithm A for `mA` steps, then Algorithm B. -/
def sig (N : Circ) (c0 a' : Nat → Bool) (u : Nat → K3) (mA : Nat) : Nat → Nat → K3
  | 0 => s0 c0
  | k + 1 => stepK N (uin a' u mA k) (sig N c0 a' u mA k)

def par (t : Nat) : Bool := decide (t % 2 = 1)

/-- The witness trace. Inputs: one clean edge `c0 → a'` at step 1. Gates:
the value of `σ (t/2)`, and the parity of `t` where that is `x`. -/
def wv (N : Circ) (c0 a' : Nat → Bool) (u : Nat → K3) (mA : Nat) (t n : Nat) : Bool :=
  match N.node n with
  | .input => inw c0 a' u t n
  | .gate _ _ => kval (sig N c0 a' u mA (t / 2) n) (par t)

section
variable (N : Circ) (c0 a' : Nat → Bool) (u : Nat → K3) (mA : Nat)

theorem stepK_input {u s : Nat → K3} {n : Nat} (hn : N.node n = .input) :
    stepK N u s n = u n := by
  unfold stepK; rw [hn]

theorem stepK_gate {u s : Nat → K3} {n init : Nat} {pins : List Src}
    (hn : N.node n = .gate init pins) : stepK N u s n = lutK init (pins.map (srcK s)) := by
  unfold stepK; rw [hn]

theorem inw_zero (i : Nat) : inw c0 a' u 0 i = c0 i := ite_pos' rfl _ _

theorem inw_late {t : Nat} (i : Nat) (ht : 2 ≤ t) : inw c0 a' u t i = a' i := by
  unfold inw; rw [ite_neg' (by omega), ite_neg' (by omega)]

theorem inw_admits {i : Nat}
    (hui : K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) (t : Nat) :
    K3.admits (u i) (inw c0 a' u t i) = true := by
  unfold inw
  by_cases h0 : t = 0
  · rw [ite_pos' h0]; exact hui.1
  · rw [ite_neg' h0]
    by_cases h1 : t = 1
    · rw [ite_pos' h1]
      by_cases hx : u i = .x
      · rw [ite_pos' hx, hx]; rfl
      · rw [ite_neg' hx]; exact hui.2
    · rw [ite_neg' h1]; exact hui.2

/-- Every value `u` admits on an input is in the witness input trace at
step 0 or 1. -/
theorem inw_avail {i : Nat}
    (hui : K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) {b : Bool}
    (hb : K3.admits (u i) b = true) : ∃ r, r ≤ 1 ∧ inw c0 a' u r i = b := by
  by_cases hc : b = c0 i
  · exact ⟨0, Nat.zero_le _, by rw [inw_zero, hc]⟩
  · have hx : u i = .x := by
      have h1 := hui.1
      cases hux : u i with
      | X => rfl
      | one =>
        rw [hux] at hb h1; exfalso; apply hc
        revert hb h1; cases b <;> cases c0 i <;> decide
      | zero =>
        rw [hux] at hb h1; exfalso; apply hc
        revert hb h1; cases b <;> cases c0 i <;> decide
    refine ⟨1, Nat.le_refl _, ?_⟩
    unfold inw
    rw [ite_neg' (by decide), ite_pos' rfl, ite_pos' hx]
    revert hc; cases b <;> cases c0 i <;> decide

/-- When `u` is exactly `c0 ⊔ a'` on an input (Algorithm A's input vector
for a single input change), the witness input makes one clean edge. -/
theorem inw_clean {i : Nat} (hui : u i = K3.join (K3.ofBool (c0 i)) (K3.ofBool (a' i)))
    (t : Nat) : inw c0 a' u t i = if t = 0 then c0 i else a' i := by
  unfold inw
  by_cases h0 : t = 0
  · rw [ite_pos' h0, ite_pos' h0]
  · rw [ite_neg' h0, ite_neg' h0]
    by_cases h1 : t = 1
    · rw [ite_pos' h1]
      by_cases hx : u i = .x
      · rw [ite_pos' hx]
        rw [hui] at hx
        have := join_x hx
        revert this; cases c0 i <;> cases a' i <;> decide
      · rw [ite_neg' hx]
    · rw [ite_neg' h1]

theorem wv_input {t n : Nat} (hn : N.node n = .input) :
    wv N c0 a' u mA t n = inw c0 a' u t n := by
  unfold wv; rw [hn]

theorem wv_gate {t n init : Nat} {pins : List Src} (hn : N.node n = .gate init pins) :
    wv N c0 a' u mA t n = kval (sig N c0 a' u mA (t / 2) n) (par t) := by
  unfold wv; rw [hn]

theorem wv_zero (n : Nat) : wv N c0 a' u mA 0 n = c0 n := by
  cases hn : N.node n with
  | input => rw [wv_input N c0 a' u mA hn]; exact inw_zero c0 a' u n
  | gate init pins => rw [wv_gate N c0 a' u mA hn]; exact kval_ofBool _ _

theorem par_two_mul (k : Nat) : par (2 * k) = false := by
  have : (2 * k) % 2 = 0 := by omega
  simp [par, this]

theorem par_two_mul_add_one (k : Nat) : par (2 * k + 1) = true := by
  have : (2 * k + 1) % 2 = 1 := by omega
  simp [par, this]

theorem par_succ (t : Nat) : par (t + 1) = !par t := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : t = 2 * (t / 2) := by omega
    rw [this, par_two_mul, par_two_mul_add_one]; rfl
  · have : t = 2 * (t / 2) + 1 := by omega
    have h2 : 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1) := by omega
    rw [this, h2, par_two_mul, par_two_mul_add_one]; rfl

/-- Every value a source may take under `σ k` is in the witness trace at an
allowed read time for steps `t ∈ [2k+1, 2k+2]`. -/
theorem avail (W : Nat) (hW : 2 * mA + 2 ≤ W)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true)
    (k t : Nat) (ht1 : 2 * k + 1 ≤ t) (ht2 : t ≤ 2 * k + 2) :
    ∀ i b, K3.admits (sig N c0 a' u mA k i) b = true →
      ∃ r, (r ≤ t ∧ t ≤ r + W) ∧ wv N c0 a' u mA r i = b := by
  intro i b hb
  cases hn : N.node i with
  | input =>
    cases k with
    | zero =>
      have : b = c0 i := (admits_ofBool_iff _ _).1 hb
      exact ⟨0, ⟨Nat.zero_le _, by omega⟩, by rw [wv_zero, this]⟩
    | succ k =>
      have hs : sig N c0 a' u mA (k + 1) i = uin a' u mA k i := stepK_input N hn
      rw [hs] at hb
      unfold uin at hb
      split at hb
      · next hk =>
        obtain ⟨r, hr, hrb⟩ := inw_avail c0 a' u (hu i hn) hb
        exact ⟨r, ⟨by omega, by omega⟩, by rw [wv_input N c0 a' u mA hn, hrb]⟩
      · have h : b = a' i := (admits_ofBool_iff _ _).1 hb
        refine ⟨t, ⟨Nat.le_refl _, by omega⟩, ?_⟩
        rw [wv_input N c0 a' u mA hn, inw_late c0 a' u i (by omega), h]
  | gate init pins =>
    cases b
    · refine ⟨2 * k, ⟨by omega, by omega⟩, ?_⟩
      rw [wv_gate N c0 a' u mA hn, Nat.mul_div_cancel_left k (by decide), par_two_mul]
      exact kval_of_admits hb
    · refine ⟨2 * k + 1, ⟨by omega, by omega⟩, ?_⟩
      have : (2 * k + 1) / 2 = k := by omega
      rw [wv_gate N c0 a' u mA hn, this, par_two_mul_add_one]
      exact kval_of_admits hb

/-- One step of the witness: read times exist (within `[t - W, t]`) under
which every gate's next value is its LUT value (unit gate delay). -/
theorem step_reads (W : Nat) (hW : 2 * mA + 2 ≤ W)
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true)
    (t j : Nat) :
    ∃ f : Nat → Nat, (∀ p, f p ≤ t ∧ t ≤ f p + W) ∧
      ∀ init pins, N.node j = .gate init pins →
        wv N c0 a' u mA (t + 1) j = lutB init (pinsB (fun p i => wv N c0 a' u mA (f p) i) pins 0) := by
  cases hn : N.node j with
  | input =>
    exact ⟨fun _ => t, fun _ => ⟨Nat.le_refl t, Nat.le_add_right t W⟩, fun init pins h => by cases h⟩
  | gate init pins =>
    suffices H : ∃ f : Nat → Nat, (∀ p, f p ≤ t ∧ t ≤ f p + W) ∧
        wv N c0 a' u mA (t + 1) j = lutB init (pinsB (fun p i => wv N c0 a' u mA (f p) i) pins 0) by
      obtain ⟨f, hf1, hf2⟩ := H
      refine ⟨f, hf1, fun init' pins' h => ?_⟩
      cases h
      exact hf2
    cases t with
    | zero =>
      refine ⟨fun _ => 0, fun _ => ⟨Nat.le_refl _, Nat.zero_le _⟩, ?_⟩
      have hz : (fun (_ i : Nat) => wv N c0 a' u mA 0 i) = fun _ i => c0 i := by
        funext p i; exact wv_zero N c0 a' u mA i
      rw [hz, hstab j init pins hn, wv_gate N c0 a' u mA hn]
      exact kval_ofBool _ _
    | succ t =>
      have hk : (t + 1 + 1) / 2 = t / 2 + 1 := by omega
      have hsig : sig N c0 a' u mA (t / 2 + 1) j =
          lutK init (pins.map (srcK (sig N c0 a' u mA (t / 2)))) := stepK_gate N hn
      rw [wv_gate N c0 a' u mA hn, hk, hsig]
      obtain ⟨bs, hbs, hval⟩ := exists_completion init _ _
        (kval_admits (lutK init (pins.map (srcK (sig N c0 a' u mA (t / 2))))) (par (t + 1 + 1)))
      have hpw := forall2_of_mem_completions _ _ hbs
      obtain ⟨f, hfok, hf⟩ := reads_exist (wv N c0 a' u mA) (sig N c0 a' u mA (t / 2))
        (fun r => r ≤ t + 1 ∧ t + 1 ≤ r + W) (t + 1) ⟨Nat.le_refl _, by omega⟩
        (avail N c0 a' u mA W hW hu (t / 2) (t + 1) (by omega) (by omega)) pins bs 0 hpw
      exact ⟨f, hfok, by rw [hf, hval]⟩

/-- **The witness is a bounded run** (`D = 0`, `W ≥ 2·mA + 2`): unit gate
delay, per-pin reads at most `W` steps old. -/
theorem exact_run (W : Nat) (hW : 2 * mA + 2 ≤ W)
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) :
    ∃ R : Run N (wv N c0 a' u mA), Bounded N (wv N c0 a' u mA) R 0 W := by
  have G := step_reads N c0 a' u mA W hW hstab hu
  let R : Run N (wv N c0 a' u mA) :=
    { rd := fun t j p => Classical.choose (G t j) p
      rd_le := fun t j p => ((Classical.choose_spec (G t j)).1 p).1
      gate := fun t j init pins h => Or.inr ((Classical.choose_spec (G t j)).2 init pins h) }
  refine ⟨R, ⟨fun t j p => ((Classical.choose_spec (G t j)).1 p).2, ?_⟩⟩
  intro k j init pins b h hb
  refine ⟨k + 1, Nat.le_succ k, Nat.le_refl _, ?_⟩
  have := hb k (Nat.le_refl k) (by omega)
  rw [← this]
  exact (Classical.choose_spec (G k j)).2 init pins h

/-! ## Reading the ternary sequence back as A and B iterates -/

theorem sig_A : ∀ k, k ≤ mA → sig N c0 a' u mA k = iter N u k (s0 c0)
  | 0, _ => rfl
  | k + 1, hk => by
    funext n
    show stepK N (uin a' u mA k) (sig N c0 a' u mA k) n = _
    rw [iter_succ', sig_A k (by omega)]
    unfold uin; rw [ite_pos' (by omega)]

theorem sig_B : ∀ m, sig N c0 a' u mA (mA + m) = iter N (fin a') m (iter N u mA (s0 c0))
  | 0 => sig_A N c0 a' u mA mA (Nat.le_refl _)
  | m + 1 => by
    funext n
    show stepK N (uin a' u mA (mA + m)) (sig N c0 a' u mA (mA + m)) n = _
    rw [iter_succ', ← sig_B m]
    unfold uin; rw [ite_neg' (by omega)]

theorem iter_fix (a s : Nat → K3) (m : Nat) (hfix : ∀ n, iter N a (m + 1) s n = iter N a m s n) :
    ∀ d, iter N a (m + d) s = iter N a m s
  | 0 => rfl
  | d + 1 => by
    funext n
    show iter N a (m + d + 1) s n = _
    rw [iter_succ', iter_fix a s m hfix d, ← iter_succ']
    exact hfix n

/-- **A witness.** A gate that is `x` in the `k`-th A iterate (`k ≤ mA`)
shows 0 at step `2k` and 1 at step `2k+1` of the witness run. -/
theorem A_witness (k : Nat) (hk : k ≤ mA) {n init : Nat} {pins : List Src}
    (hn : N.node n = .gate init pins) (hx : iter N u k (s0 c0) n = .x) :
    wv N c0 a' u mA (2 * k) n = false ∧ wv N c0 a' u mA (2 * k + 1) n = true := by
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [wv_gate N c0 a' u mA hn, wv_gate N c0 a' u mA hn, Nat.mul_div_cancel_left k (by decide),
    h2, sig_A N c0 a' u mA k hk, hx, par_two_mul, par_two_mul_add_one]
  exact ⟨rfl, rfl⟩

/-- **B witness.** Once the B iteration (from the A result `iter u mA s0`,
final inputs `a'`) is fixed at `mB`, every gate of the witness run shows,
from step `2(mA + mB)` on, its B value, and the parity of the step if that
value is `x`: definite nodes hold, `x` nodes oscillate for ever. -/
theorem B_witness (mB : Nat)
    (hfixB : ∀ n, iter N (fin a') (mB + 1) (iter N u mA (s0 c0)) n =
      iter N (fin a') mB (iter N u mA (s0 c0)) n)
    {n init : Nat} {pins : List Src} (hn : N.node n = .gate init pins) :
    ∀ t, 2 * (mA + mB) ≤ t →
      wv N c0 a' u mA t n = kval (iter N (fin a') mB (iter N u mA (s0 c0)) n) (par t) := by
  intro t ht
  have ht2 : t / 2 = mA + (mB + (t / 2 - mA - mB)) := by omega
  rw [wv_gate N c0 a' u mA hn, ht2, sig_B, iter_fix N _ _ mB hfixB]

/-! ## The exactness theorems -/

/-- The old stable state is below its own A step (A's start condition),
derived from stability and `u = c0 ⊔ a'` on the inputs. -/
theorem s0_chain
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) :
    sle (s0 c0) (stepK N u (s0 c0)) := by
  intro n
  cases hn : N.node n with
  | input =>
    rw [stepK_input N hn]
    exact le_ofBool_of_admits (hu n hn).1
  | gate init pins =>
    rw [stepK_gate N hn]
    apply le_ofBool_of_admits
    rw [← hstab n init pins hn]
    exact lutK_sound init (pins_forall2 (s0 c0) (fun _ i => c0 i)
      (fun _ i => admits_ofBool (c0 i)) pins 0)

/-- The witness run's inputs: inside `u` always, old value at 0, final value
from step 2 (a clean edge at step 1 when `u = c0 ⊔ a'`, `inw_clean`). -/
theorem wv_inputs_ok
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) :
    (∀ t i, N.node i = .input → K3.admits (u i) (wv N c0 a' u mA t i) = true) ∧
    (∀ t i, N.node i = .input → 2 ≤ t → wv N c0 a' u mA t i = a' i) :=
  ⟨fun t i hi => by rw [wv_input N c0 a' u mA hi]; exact inw_admits c0 a' u (hu i hi) t,
   fun t i hi ht => by rw [wv_input N c0 a' u mA hi]; exact inw_late c0 a' u i ht⟩

/-- **Exactness of Algorithm A** (B–S Ch. 7, the "A finds exactly the nodes
that can change" half). `c0` is stable for the old inputs (`hstab`); the
inputs go from `c0` to `a'`, and Algorithm A runs with an input vector `u`
admitting both (`u = c0 ⊔ a'` for a single clean change, where the witness
inputs make one clean edge, `inw_clean`; `u = x` on an input that may glitch
without changing). A's iteration is fixed at `mA`. Then a gate is `x` in A's
result IFF some bounded run, starting in `c0`, with inputs inside `u` and
final from step 2, changes it. (The `←` direction holds for every run,
bounded or not: `A_change_sound`.) -/
theorem A_exact
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true)
    (hfixA : ∀ n, iter N u (mA + 1) (s0 c0) n = iter N u mA (s0 c0) n)
    {n init : Nat} {pins : List Src} (hn : N.node n = .gate init pins) :
    iter N u mA (s0 c0) n = .x ↔
      ∃ (v : Nat → Nat → Bool) (R : Run N v) (W : Nat), Bounded N v R 0 W ∧ v 0 = c0 ∧
        (∀ t i, N.node i = .input → K3.admits (u i) (v t i) = true) ∧
        (∀ t i, N.node i = .input → 2 ≤ t → v t i = a' i) ∧
        ∃ t, v t n ≠ c0 n := by
  constructor
  · intro hx
    obtain ⟨R, hB⟩ := exact_run N c0 a' u mA (2 * mA + 2) (Nat.le_refl _) hstab hu
    refine ⟨wv N c0 a' u mA, R, 2 * mA + 2, hB, funext (wv_zero N c0 a' u mA),
      (wv_inputs_ok N c0 a' u mA hu).1, (wv_inputs_ok N c0 a' u mA hu).2, ?_⟩
    obtain ⟨h0, h1⟩ := A_witness N c0 a' u mA mA (Nat.le_refl _) hn hx
    cases hc : c0 n
    · exact ⟨2 * mA + 1, by rw [h1]; decide⟩
    · exact ⟨2 * mA, by rw [h0]; decide⟩
  · rintro ⟨v, R, W, _, hv0, hvin, _, t, ht⟩
    apply Classical.byContradiction
    intro hnx
    have hs0 := s0_chain N c0 a' u hstab hu
    have hcov := algA_sound N u (s0 c0) hs0 mA hfixA R hvin
      (by rw [hv0]; exact fun i => admits_ofBool (c0 i)) t n
    have habove := iter_above N u (s0 c0) hs0 mA n
    rcases habove with heq | hx
    · rw [← heq] at hcov
      exact ht ((admits_ofBool_iff _ _).1 hcov)
    · exact hnx hx

/-- The `←` half of `A_exact` for ANY run (no delay bound, inputs anywhere
inside `u`): a node that is definite in A's result never moves. -/
theorem A_change_sound
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true)
    (hfixA : ∀ n, iter N u (mA + 1) (s0 c0) n = iter N u mA (s0 c0) n)
    {v : Nat → Nat → Bool} (R : Run N v) (hv0 : v 0 = c0)
    (hin : ∀ t i, N.node i = .input → K3.admits (u i) (v t i) = true)
    (n : Nat) (hdef : iter N u mA (s0 c0) n ≠ .x) : ∀ t, v t n = c0 n := by
  intro t
  have hs0 := s0_chain N c0 a' u hstab hu
  have hcov := algA_sound N u (s0 c0) hs0 mA hfixA R hin
    (by rw [hv0]; exact fun i => admits_ofBool (c0 i)) t n
  rcases iter_above N u (s0 c0) hs0 mA n with heq | hx
  · rw [← heq] at hcov
    exact (admits_ofBool_iff _ _).1 hcov
  · exact absurd hx hdef

/-- **Exactness of Algorithm B** (B–S Ch. 7: every `x` of the A-then-B result
is witnessed by a run that does not settle). Same setting as `A_exact`; B is
run from A's result with the final inputs `a'` and is fixed at `mB`. Then a
gate is `x` in the A-then-B result IFF some bounded run (start `c0`, inputs
inside `u` and final from step 2) never settles on it: for every time `T`
and value `b` it differs from `b` at some time `≥ T`. For `←`, 7f's
`algB_settles` gives, for a definite node, a settling time
`2 + mB·(D + W + 1)` valid in EVERY bounded run. -/
theorem B_exact
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true)
    (hfixA : ∀ n, iter N u (mA + 1) (s0 c0) n = iter N u mA (s0 c0) n)
    (mB : Nat)
    (hfixB : ∀ n, iter N (fin a') (mB + 1) (iter N u mA (s0 c0)) n =
      iter N (fin a') mB (iter N u mA (s0 c0)) n)
    {n init : Nat} {pins : List Src} (hn : N.node n = .gate init pins) :
    iter N (fin a') mB (iter N u mA (s0 c0)) n = .x ↔
      ∃ (v : Nat → Nat → Bool) (R : Run N v) (D W : Nat), Bounded N v R D W ∧ v 0 = c0 ∧
        (∀ t i, N.node i = .input → K3.admits (u i) (v t i) = true) ∧
        (∀ t i, N.node i = .input → 2 ≤ t → v t i = a' i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b := by
  constructor
  · intro hx
    obtain ⟨R, hB⟩ := exact_run N c0 a' u mA (2 * mA + 2) (Nat.le_refl _) hstab hu
    refine ⟨wv N c0 a' u mA, R, 0, 2 * mA + 2, hB, funext (wv_zero N c0 a' u mA),
      (wv_inputs_ok N c0 a' u mA hu).1, (wv_inputs_ok N c0 a' u mA hu).2, ?_⟩
    intro T b
    have hw := B_witness N c0 a' u mA mB hfixB hn
    have e1 := hw (T + 2 * (mA + mB)) (by omega)
    have e2 := hw (T + 2 * (mA + mB) + 1) (by omega)
    rw [hx] at e1 e2
    rw [par_succ] at e2
    simp only [kval] at e1 e2
    cases hp : par (T + 2 * (mA + mB)) <;> cases b
    · exact ⟨T + 2 * (mA + mB) + 1, by omega, by rw [e2, hp]; decide⟩
    · exact ⟨T + 2 * (mA + mB), by omega, by rw [e1, hp]; decide⟩
    · exact ⟨T + 2 * (mA + mB), by omega, by rw [e1, hp]; decide⟩
    · exact ⟨T + 2 * (mA + mB) + 1, by omega, by rw [e2, hp]; decide⟩
  · rintro ⟨v, R, D, W, hB, hv0, hvin, hvfin, hns⟩
    apply Classical.byContradiction
    intro hnx
    have hdef : ∃ b, iter N (fin a') mB (iter N u mA (s0 c0)) n = K3.ofBool b := by
      cases h : iter N (fin a') mB (iter N u mA (s0 c0)) n with
      | one => exact ⟨true, rfl⟩
      | zero => exact ⟨false, rfl⟩
      | X => exact absurd h hnx
    obtain ⟨b, hb⟩ := hdef
    have hs0 := s0_chain N c0 a' u hstab hu
    have hpost : sle (stepK N u (iter N u mA (s0 c0))) (iter N u mA (s0 c0)) := by
      intro i; rw [← iter_succ', hfixA i]; exact le_refl _
    have h0 : covers (iter N u mA (s0 c0)) (v 0) := by
      rw [hv0]
      exact covers_of_sle (iter_above N u (s0 c0) hs0 mA) (fun i => admits_ofBool (c0 i))
    have hfin : ∀ k i, 2 ≤ k → N.node i = .input → K3.admits (fin a' i) (v k i) = true := by
      intro k i hk hi
      rw [hvfin k i hi hk]
      exact admits_ofBool (a' i)
    have hset := algB_settles N u (fin a') _ hpost R hB hvin h0 2 hfin mB n b hb
    obtain ⟨t, ht, hne⟩ := hns (2 + mB * (D + W + 1)) b
    exact hne (hset t ht)

/-! ## Algorithm A with FIXED per-wire transport delays

The witness above uses time-varying, non-FIFO reads. For Algorithm A alone a
stronger witness exists: every wire `(j, p)` has ONE constant transport delay
`d j p` (pin reads `k - d j p`, i.e. the source value `d` steps ago, the
initial value before that), gates are GMW (hold, or take the LUT value).
Each gate toggles once, from `c0` to `!c0`, at the A step where it first
becomes `x`, and holds after. This needs unbounded gate delay (a gate holds
its new value against a later excitation), so it is a `Run`, not `Bounded`. -/

/-- The A sequence, frozen after `mA` steps. -/
def sA (t : Nat) : Nat → K3 := iter N u (min t mA) (s0 c0)

/-- Toggle-once trace: a gate is `!c0` from the A step where it is `x` on. -/
def fv (t n : Nat) : Bool :=
  match N.node n with
  | .input => inw c0 a' u t n
  | .gate _ _ => if sA N c0 u mA t n = .x then !c0 n else c0 n

theorem fv_input {t n : Nat} (hn : N.node n = .input) :
    fv N c0 a' u mA t n = inw c0 a' u t n := by
  unfold fv; rw [hn]

theorem fv_gate {t n init : Nat} {pins : List Src} (hn : N.node n = .gate init pins) :
    fv N c0 a' u mA t n = if sA N c0 u mA t n = .x then !c0 n else c0 n := by
  unfold fv; rw [hn]

theorem fv_zero (n : Nat) : fv N c0 a' u mA 0 n = c0 n := by
  cases hn : N.node n with
  | input => rw [fv_input N c0 a' u mA hn]; exact inw_zero c0 a' u n
  | gate init pins =>
    rw [fv_gate N c0 a' u mA hn]
    show (if K3.ofBool (c0 n) = .x then !c0 n else c0 n) = c0 n
    cases c0 n <;> rfl

theorem iter_mono_add (s : Nat → K3) (hs : sle s (stepK N u s)) :
    ∀ k d, sle (iter N u k s) (iter N u (k + d) s)
  | _, 0 => fun _ => le_refl _
  | k, d + 1 => fun n => le_trans (iter_mono_add s hs k d n) (iter_chain N u s hs (k + d) n)

theorem sA_mono (hs : sle (s0 c0) (stepK N u (s0 c0))) {k k' : Nat} (h : k ≤ k') :
    sle (sA N c0 u mA k) (sA N c0 u mA k') := by
  unfold sA
  have : min k' mA = min k mA + (min k' mA - min k mA) := by omega
  rw [this]
  exact iter_mono_add N u _ hs _ _

theorem eq_x_of_le_x {z : K3} (h : le .x z) : z = .x := by
  rcases h with h | h
  · exact h.symm
  · exact h


/-- A value other than `c0 i` admitted by the A state at `k` is shown by the
toggle-once trace at some time `≤ k` (at `k` for a gate, at step 1 for an
input). -/
theorem favail (hs : sle (s0 c0) (stepK N u (s0 c0)))
    (k i : Nat) (b : Bool) (hb : K3.admits (sA N c0 u mA k i) b = true) (hne : b ≠ c0 i) :
    ∃ r, r ≤ k ∧ fv N c0 a' u mA r i = b := by
  have hx : sA N c0 u mA k i = .x := by
    rcases sA_mono N c0 u mA hs (Nat.zero_le k) i with h | h
    · exfalso; rw [← h] at hb
      exact hne ((admits_ofBool_iff _ _).1 hb)
    · exact h
  cases hn : N.node i with
  | input =>
    have hk : min k mA ≠ 0 := by
      intro h0
      unfold sA at hx; rw [h0] at hx
      revert hx; show K3.ofBool (c0 i) = .x → False
      cases c0 i <;> decide
    have hk' : min k mA = (min k mA - 1) + 1 := by omega
    unfold sA at hx
    rw [hk', iter_succ', stepK_input N hn] at hx
    refine ⟨1, by omega, ?_⟩
    rw [fv_input N c0 a' u mA hn]
    unfold inw
    rw [ite_neg' (by decide), ite_pos' rfl, ite_pos' hx]
    revert hne; cases b <;> cases c0 i <;> decide
  | gate init pins =>
    refine ⟨k, Nat.le_refl _, ?_⟩
    rw [fv_gate N c0 a' u mA hn, hx, ite_pos' rfl]
    revert hne; cases b <;> cases c0 i <;> decide

/-- Gate `j` toggles at step `k`. -/
def Tog (k j : Nat) : Prop := sA N c0 u mA k j ≠ .x ∧ sA N c0 u mA (k + 1) j = .x

theorem tog_unique (hs : sle (s0 c0) (stepK N u (s0 c0))) {k k' j : Nat}
    (h : Tog N c0 u mA k j) (h' : Tog N c0 u mA k' j) : k = k' := by
  rcases Nat.lt_trichotomy k k' with hl | he | hl
  · exact absurd (eq_x_of_le_x (h.2 ▸ sA_mono N c0 u mA hs (show k + 1 ≤ k' by omega) j)) h'.1
  · exact he
  · exact absurd (eq_x_of_le_x (h'.2 ▸ sA_mono N c0 u mA hs (show k' + 1 ≤ k by omega) j)) h.1

theorem fv_hold (hs : sle (s0 c0) (stepK N u (s0 c0))) {k j init : Nat} {pins : List Src}
    (hn : N.node j = .gate init pins) (h : ¬ Tog N c0 u mA k j) :
    fv N c0 a' u mA (k + 1) j = fv N c0 a' u mA k j := by
  rw [fv_gate N c0 a' u mA hn, fv_gate N c0 a' u mA hn]
  by_cases h1 : sA N c0 u mA k j = .x
  · have h2 : sA N c0 u mA (k + 1) j = .x :=
      eq_x_of_le_x (h1 ▸ sA_mono N c0 u mA hs (Nat.le_succ k) j)
    rw [h1, h2]
  · have h2 : sA N c0 u mA (k + 1) j ≠ .x := fun h2 => h ⟨h1, h2⟩
    rw [ite_neg' h1, ite_neg' h2]

/-- At its toggle step a gate's new value is its LUT value under constant
per-pin delays `d p` (read time `k - d p`). -/
theorem tog_delays (hs : sle (s0 c0) (stepK N u (s0 c0)))
    {k j init : Nat} {pins : List Src} (hn : N.node j = .gate init pins)
    (ht : Tog N c0 u mA k j) :
    ∃ d : Nat → Nat, fv N c0 a' u mA (k + 1) j =
      lutB init (pinsB (fun p i => fv N c0 a' u mA (k - d p) i) pins 0) := by
  have hmin : min (k + 1) mA = min k mA + 1 := by
    rcases Nat.lt_or_ge k mA with h | h
    · omega
    · exfalso
      have : min (k + 1) mA = min k mA := by omega
      apply ht.1; rw [← ht.2]; unfold sA; rw [this]
  have hstep : sA N c0 u mA (k + 1) j = lutK init (pins.map (srcK (sA N c0 u mA k))) := by
    show iter N u (min (k + 1) mA) (s0 c0) j = _
    rw [hmin, iter_succ', stepK_gate N hn]; rfl
  have hval : fv N c0 a' u mA (k + 1) j = !c0 j := by
    rw [fv_gate N c0 a' u mA hn, ht.2, ite_pos' rfl]
  obtain ⟨bs, hbs, hlut⟩ := exists_completion init (pins.map (srcK (sA N c0 u mA k))) (!c0 j)
    (by rw [← hstep, ht.2]; rfl)
  obtain ⟨f, hfok, hf⟩ := reads_exist (fv N c0 a' u mA) (sA N c0 u mA k) (fun r => r ≤ k) k
    (Nat.le_refl k)
    (by
      intro i b hb
      by_cases hc : b = c0 i
      · exact ⟨0, Nat.zero_le _, by rw [fv_zero, hc]⟩
      · exact favail N c0 a' u mA hs k i b hb hc)
    pins bs 0 (forall2_of_mem_completions _ _ hbs)
  refine ⟨fun p => k - f p, ?_⟩
  have hfun : (fun p i => fv N c0 a' u mA (k - (k - f p)) i) = fun p i => fv N c0 a' u mA (f p) i := by
    funext p i
    have : k - (k - f p) = f p := by have := hfok p; omega
    rw [this]
  show _ = lutB init (pinsB (fun p i => fv N c0 a' u mA (k - (k - f p)) i) pins 0)
  rw [hfun, hf, hlut, hval]

/-- **Algorithm A is exact with fixed per-wire delays.** Same setting as
`A_exact`. There is ONE run, with a constant transport delay `d j p` on every
wire (read time `k - d j p`) and GMW gates, starting in `c0`, with the inputs
following `inw` (a clean edge at step 1 when `u = c0 ⊔ a'`), in which every gate that is `x` in A's
result changes value. With `A_change_sound`, this characterises A's `x` set
exactly under fixed wire delays as well. -/
theorem A_exact_fixed
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) :
    ∃ (R : Run N (fv N c0 a' u mA)) (d : Nat → Nat → Nat),
      (∀ k j p, R.rd k j p = k - d j p) ∧ fv N c0 a' u mA 0 = c0 ∧
      (∀ t i, N.node i = .input → fv N c0 a' u mA t i = inw c0 a' u t i) ∧
      ∀ n init pins, N.node n = .gate init pins → iter N u mA (s0 c0) n = .x →
        fv N c0 a' u mA mA n ≠ c0 n := by
  have hs := s0_chain N c0 a' u hstab hu
  have E : ∀ j, ∃ d : Nat → Nat, ∀ k init pins, N.node j = .gate init pins →
      Tog N c0 u mA k j →
      fv N c0 a' u mA (k + 1) j = lutB init (pinsB (fun p i => fv N c0 a' u mA (k - d p) i) pins 0) := by
    intro j
    by_cases hex : ∃ k init pins, N.node j = .gate init pins ∧ Tog N c0 u mA k j
    · obtain ⟨k, init, pins, hn, ht⟩ := hex
      obtain ⟨d, hd⟩ := tog_delays N c0 a' u mA hs hn ht
      refine ⟨d, fun k' init' pins' hn' ht' => ?_⟩
      have hkk := tog_unique N c0 u mA hs ht ht'
      subst hkk
      rw [hn] at hn'; cases hn'
      exact hd
    · exact ⟨fun _ => 0, fun k init pins hn ht => absurd ⟨k, init, pins, hn, ht⟩ hex⟩
  let d : Nat → Nat → Nat := fun j => Classical.choose (E j)
  let R : Run N (fv N c0 a' u mA) :=
    { rd := fun k j p => k - d j p
      rd_le := fun k j p => Nat.sub_le k _
      gate := fun k j init pins hn => by
        by_cases ht : Tog N c0 u mA k j
        · exact Or.inr (Classical.choose_spec (E j) k init pins hn ht)
        · exact Or.inl (fv_hold N c0 a' u mA hs hn ht) }
  refine ⟨R, d, fun _ _ _ => rfl, funext (fv_zero N c0 a' u mA),
    fun t i hi => fv_input N c0 a' u mA hi, ?_⟩
  intro n init pins hn hx
  have : sA N c0 u mA mA n = .x := by unfold sA; rw [Nat.min_self]; exact hx
  rw [fv_gate N c0 a' u mA hn, this, ite_pos' rfl]
  cases c0 n <;> decide

/-! ## A FIFO witness: unit gate delay, every wire 0 or 1 step, never reordering

A second construction, `tv`, without stretching: the ternary sequence `σ`
advances one step per time step, a node that is definite in `σ t` shows that
value at `t`, and a node that is `x` in `σ t` shows the opposite of its value
at `t - 1` (it toggles). An `x` source then shows both values in `{t-1, t}`,
so every read time is `t - 1` or `t`. Read times of one pin are therefore
monotone (FIFO), and `W = 1`, `D = 0`. The price is on the inputs: an input
that `u` marks `x` toggles at every step up to `mA` (a glitch train inside
`u`), and is final from `mA + 1` on. -/

/-- The toggling witness trace (gates and inputs alike follow `σ`). -/
def tv : Nat → Nat → Bool
  | 0 => c0
  | t + 1 => fun n =>
    match sig N c0 a' u mA (t + 1) n with
    | .x => !tv t n
    | .t => true
    | .f => false

theorem tv_admits : ∀ t n, K3.admits (sig N c0 a' u mA t n) (tv N c0 a' u mA t n) = true
  | 0, n => admits_ofBool (c0 n)
  | t + 1, n => by
    show K3.admits (sig N c0 a' u mA (t + 1) n) (match sig N c0 a' u mA (t + 1) n with
      | .x => !tv N c0 a' u mA t n | .t => true | .f => false) = true
    cases sig N c0 a' u mA (t + 1) n <;> rfl

theorem tv_avail (t i : Nat) (b : Bool) (hb : K3.admits (sig N c0 a' u mA t i) b = true) :
    ∃ r, (r ≤ t ∧ t ≤ r + 1) ∧ tv N c0 a' u mA r i = b := by
  cases t with
  | zero =>
    exact ⟨0, ⟨Nat.le_refl _, Nat.zero_le _⟩, ((admits_ofBool_iff _ _).1 hb).symm⟩
  | succ t =>
    have hdef : tv N c0 a' u mA (t + 1) i = (match sig N c0 a' u mA (t + 1) i with
      | .x => !tv N c0 a' u mA t i | .t => true | .f => false) := rfl
    cases hs : sig N c0 a' u mA (t + 1) i with
    | X =>
      rw [hs] at hdef
      by_cases hc : tv N c0 a' u mA t i = b
      · exact ⟨t, ⟨Nat.le_succ t, by omega⟩, hc⟩
      · refine ⟨t + 1, ⟨Nat.le_refl _, by omega⟩, ?_⟩
        rw [hdef]; revert hc; cases b <;> cases tv N c0 a' u mA t i <;> decide
    | one =>
      rw [hs] at hb hdef
      exact ⟨t + 1, ⟨Nat.le_refl _, by omega⟩,
        by rw [hdef]; exact ((admits_ofBool_iff true b).1 hb).symm⟩
    | zero =>
      rw [hs] at hb hdef
      exact ⟨t + 1, ⟨Nat.le_refl _, by omega⟩,
        by rw [hdef]; exact ((admits_ofBool_iff false b).1 hb).symm⟩

theorem tv_step_reads (t j : Nat) :
    ∃ f : Nat → Nat, (∀ p, f p ≤ t ∧ t ≤ f p + 1) ∧
      ∀ init pins, N.node j = .gate init pins →
        tv N c0 a' u mA (t + 1) j = lutB init (pinsB (fun p i => tv N c0 a' u mA (f p) i) pins 0) := by
  cases hn : N.node j with
  | input =>
    exact ⟨fun _ => t, fun _ => ⟨Nat.le_refl t, Nat.le_succ t⟩, fun init pins h => by cases h⟩
  | gate init pins =>
    have hsig : sig N c0 a' u mA (t + 1) j =
        lutK init (pins.map (srcK (sig N c0 a' u mA t))) := stepK_gate N hn
    have hadm := tv_admits N c0 a' u mA (t + 1) j
    rw [hsig] at hadm
    obtain ⟨bs, hbs, hval⟩ := exists_completion init _ _ hadm
    obtain ⟨f, hfok, hf⟩ := reads_exist (tv N c0 a' u mA) (sig N c0 a' u mA t)
      (fun r => r ≤ t ∧ t ≤ r + 1) t ⟨Nat.le_refl _, Nat.le_succ t⟩
      (tv_avail N c0 a' u mA t) pins bs 0 (forall2_of_mem_completions _ _ hbs)
    refine ⟨f, hfok, fun init' pins' h => ?_⟩
    cases h
    rw [hf, hval]

/-- **The FIFO witness is a run** with `D = 0`, `W = 1`, and every pin's read
times non-decreasing (no reordering on any wire). -/
theorem tv_run :
    ∃ R : Run N (tv N c0 a' u mA), Bounded N (tv N c0 a' u mA) R 0 1 ∧
      ∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p := by
  have G := tv_step_reads N c0 a' u mA
  let R : Run N (tv N c0 a' u mA) :=
    { rd := fun t j p => Classical.choose (G t j) p
      rd_le := fun t j p => ((Classical.choose_spec (G t j)).1 p).1
      gate := fun t j init pins h => Or.inr ((Classical.choose_spec (G t j)).2 init pins h) }
  refine ⟨R, ⟨fun t j p => ((Classical.choose_spec (G t j)).1 p).2, ?_⟩, ?_⟩
  · intro k j init pins b h hb
    refine ⟨k + 1, Nat.le_succ k, Nat.le_refl _, ?_⟩
    have := hb k (Nat.le_refl k) (by omega)
    rw [← this]
    exact (Classical.choose_spec (G k j)).2 init pins h
  · intro k j p
    have h1 := ((Classical.choose_spec (G k j)).1 p).1
    have h2 := ((Classical.choose_spec (G (k + 1) j)).1 p).2
    show Classical.choose (G k j) p ≤ Classical.choose (G (k + 1) j) p
    omega

theorem tv_toggle {t n : Nat} (hx : sig N c0 a' u mA (t + 1) n = .x) :
    tv N c0 a' u mA (t + 1) n = !tv N c0 a' u mA t n := by
  show (match sig N c0 a' u mA (t + 1) n with
    | .x => !tv N c0 a' u mA t n | .t => true | .f => false) = _
  rw [hx]

theorem tv_inputs_ok
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true) :
    (∀ t i, N.node i = .input → K3.admits (u i) (tv N c0 a' u mA t i) = true) ∧
    (∀ t i, N.node i = .input → mA + 1 ≤ t → tv N c0 a' u mA t i = a' i) := by
  have key : ∀ t i, N.node i = .input → 1 ≤ t →
      sig N c0 a' u mA t i = uin a' u mA (t - 1) i := by
    intro t i hi ht
    have : t = (t - 1) + 1 := by omega
    rw [this]; exact stepK_input N hi
  refine ⟨fun t i hi => ?_, fun t i hi ht => ?_⟩
  · cases t with
    | zero => exact (hu i hi).1
    | succ t =>
      have h := tv_admits N c0 a' u mA (t + 1) i
      rw [key (t + 1) i hi (by omega)] at h
      unfold uin at h
      split at h
      · exact h
      · rw [(admits_ofBool_iff _ _).1 h]; exact (hu i hi).2
  · have h := tv_admits N c0 a' u mA t i
    rw [key t i hi (by omega)] at h
    unfold uin at h
    rw [ite_neg' (by omega)] at h
    exact (admits_ofBool_iff _ _).1 h

/-- **Exactness of B with a FIFO witness.** Same setting as `B_exact`. A gate
is `x` in the A-then-B result IFF some run with unit gate delay (`D = 0`),
every wire 0 or 1 step old (`W = 1`) and read times non-decreasing on every
wire, starting in `c0`, with inputs inside `u` and final from some step on,
never settles on it. (The witness's inputs glitch inside `u` up to step `mA`.)
Holds for every node `n` (an input is never `x` in B's result). -/
theorem B_exact_fifo
    (hstab : ∀ j init pins, N.node j = .gate init pins →
      lutB init (pinsB (fun _ i => c0 i) pins 0) = c0 j)
    (hu : ∀ i, N.node i = .input → K3.admits (u i) (c0 i) = true ∧ K3.admits (u i) (a' i) = true)
    (hfixA : ∀ n, iter N u (mA + 1) (s0 c0) n = iter N u mA (s0 c0) n)
    (mB : Nat)
    (hfixB : ∀ n, iter N (fin a') (mB + 1) (iter N u mA (s0 c0)) n =
      iter N (fin a') mB (iter N u mA (s0 c0)) n)
    (n : Nat) :
    iter N (fin a') mB (iter N u mA (s0 c0)) n = .x ↔
      ∃ (v : Nat → Nat → Bool) (R : Run N v) (T0 : Nat), Bounded N v R 0 1 ∧
        (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ v 0 = c0 ∧
        (∀ t i, N.node i = .input → K3.admits (u i) (v t i) = true) ∧
        (∀ t i, N.node i = .input → T0 ≤ t → v t i = a' i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b := by
  constructor
  · intro hx
    obtain ⟨R, hB, hmono⟩ := tv_run N c0 a' u mA
    refine ⟨tv N c0 a' u mA, R, mA + 1, hB, hmono, rfl, (tv_inputs_ok N c0 a' u mA hu).1,
      (tv_inputs_ok N c0 a' u mA hu).2, ?_⟩
    intro T b
    have hsx : sig N c0 a' u mA (mA + mB + T + 1) n = .x := by
      rw [show mA + mB + T + 1 = mA + (mB + (T + 1)) by omega, sig_B, iter_fix N _ _ mB hfixB]
      exact hx
    have ht := tv_toggle N c0 a' u mA hsx
    by_cases hc : tv N c0 a' u mA (mA + mB + T) n = b
    · refine ⟨mA + mB + T + 1, by omega, ?_⟩
      rw [ht, hc]; cases b <;> decide
    · exact ⟨mA + mB + T, by omega, hc⟩
  · rintro ⟨v, R, T0, hB, _, hv0, hvin, hvfin, hns⟩
    apply Classical.byContradiction
    intro hnx
    have hdef : ∃ b, iter N (fin a') mB (iter N u mA (s0 c0)) n = K3.ofBool b := by
      cases h : iter N (fin a') mB (iter N u mA (s0 c0)) n with
      | one => exact ⟨true, rfl⟩
      | zero => exact ⟨false, rfl⟩
      | X => exact absurd h hnx
    obtain ⟨b, hb⟩ := hdef
    have hs0 := s0_chain N c0 a' u hstab hu
    have hpost : sle (stepK N u (iter N u mA (s0 c0))) (iter N u mA (s0 c0)) := by
      intro i; rw [← iter_succ', hfixA i]; exact le_refl _
    have h0 : covers (iter N u mA (s0 c0)) (v 0) := by
      rw [hv0]
      exact covers_of_sle (iter_above N u (s0 c0) hs0 mA) (fun i => admits_ofBool (c0 i))
    have hfin : ∀ k i, T0 ≤ k → N.node i = .input → K3.admits (fin a' i) (v k i) = true := by
      intro k i hk hi
      rw [hvfin k i hi hk]
      exact admits_ofBool (a' i)
    have hset := algB_settles N u (fin a') _ hpost R hB hvin h0 T0 hfin mB n b hb
    obtain ⟨t, ht, hne⟩ := hns (T0 + mB * (0 + 1 + 1)) b
    exact hne (hset t ht)

/-- **A with a FIFO witness**: an A-`x` gate changes in the toggling run. -/
theorem A_witness_fifo (k : Nat) {n : Nat}
    (hx : iter N u (k + 1) (s0 c0) n = .x) (hk1 : k + 1 ≤ mA) :
    tv N c0 a' u mA (k + 1) n = !tv N c0 a' u mA k n := by
  have : sig N c0 a' u mA (k + 1) n = .x := by rw [sig_A N c0 a' u mA (k + 1) hk1]; exact hx
  exact tv_toggle N c0 a' u mA this

end

/-! ## Non-vacuity: the C-element in hold with a runt (7i's `cNet`)

`bd_c2` with its real INIT, inputs 0 a, 1 b, 2 rst, gate 3 q (fed back to its
own I2). Start: a = 1, b = 0, rst = 0, q = 0 (stable). The input b may glitch
(`u` = `x` on b) and ends at 0 again. A is fixed after 2 steps, B after 1, and
q is `x` in the A-then-B result, so `B_exact` produces a bounded run in which
q never settles (7i built such runs by hand; here they come out of the
general theorem). -/

def cc0 (n : Nat) : Bool := decide (n = 0)

def cu (n : Nat) : K3 := if n = 1 then .x else K3.ofBool (cc0 n)

theorem cNet_input_high (n : Nat) : TernaryPhases.cNet.node (n + 4) = .input := rfl

theorem cNet_q : TernaryPhases.cNet.node 3 =
    .gate ArbKleene.C2_INIT [.node 0, .node 1, .node 3, .node 2, .const false, .const false] := rfl

theorem cel_hstab : ∀ j init pins, TernaryPhases.cNet.node j = .gate init pins →
    lutB init (pinsB (fun _ i => cc0 i) pins 0) = cc0 j := by
  intro j init pins h
  match j, h with
  | 3, h => cases h; decide

theorem cel_hu : ∀ i, TernaryPhases.cNet.node i = .input →
    K3.admits (cu i) (cc0 i) = true ∧ K3.admits (cu i) (cc0 i) = true := by
  intro i _
  have : K3.admits (cu i) (cc0 i) = true := by
    unfold cu; split
    · rfl
    · exact admits_ofBool _
  exact ⟨this, this⟩

theorem cel_iter_high (v : Nat → K3) (m n : Nat) (s : Nat → K3) :
    iter TernaryPhases.cNet v (m + 1) s (n + 4) = v (n + 4) := by
  rw [iter_succ', stepK_input TernaryPhases.cNet (cNet_input_high n)]

theorem cel_fixA : ∀ n, iter TernaryPhases.cNet cu (2 + 1) (s0 cc0) n =
    iter TernaryPhases.cNet cu 2 (s0 cc0) n := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | n + 4 => rw [cel_iter_high, cel_iter_high]

theorem cel_fixB : ∀ n, iter TernaryPhases.cNet (fin cc0) (1 + 1)
    (iter TernaryPhases.cNet cu 2 (s0 cc0)) n =
    iter TernaryPhases.cNet (fin cc0) 1 (iter TernaryPhases.cNet cu 2 (s0 cc0)) n := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | n + 4 => rw [cel_iter_high, cel_iter_high]

theorem cel_q_x : iter TernaryPhases.cNet (fin cc0) 1
    (iter TernaryPhases.cNet cu 2 (s0 cc0)) 3 = .x := by decide

/-- **The C-element runt, from the general theorem.** There is a bounded run
of `bd_c2` from the hold state (q = 0, a = 1, b = 0), with a = 1, rst = 0
throughout and b glitching only at step 1 (b = 0 from step 2), in which q
never settles. -/
theorem cel_runt_never_settles :
    ∃ (v : Nat → Nat → Bool) (R : Run TernaryPhases.cNet v) (D W : Nat),
      Bounded TernaryPhases.cNet v R D W ∧ v 0 = cc0 ∧
      (∀ t i, TernaryPhases.cNet.node i = .input → K3.admits (cu i) (v t i) = true) ∧
      (∀ t i, TernaryPhases.cNet.node i = .input → 2 ≤ t → v t i = cc0 i) ∧
      ∀ T b, ∃ t, T ≤ t ∧ v t 3 ≠ b :=
  (B_exact TernaryPhases.cNet cc0 cc0 cu 2 cel_hstab cel_hu cel_fixA 1 cel_fixB cNet_q).1 cel_q_x

/-- The same from the FIFO witness: unit gate delay, every wire 0 or 1 step
and never reordering; b glitches up to step 2 (inside `u`) and is 0 after. -/
theorem cel_runt_never_settles_fifo :
    ∃ (v : Nat → Nat → Bool) (R : Run TernaryPhases.cNet v) (T0 : Nat),
      Bounded TernaryPhases.cNet v R 0 1 ∧ (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ v 0 = cc0 ∧
      (∀ t i, TernaryPhases.cNet.node i = .input → K3.admits (cu i) (v t i) = true) ∧
      (∀ t i, TernaryPhases.cNet.node i = .input → T0 ≤ t → v t i = cc0 i) ∧
      ∀ T b, ∃ t, T ≤ t ∧ v t 3 ≠ b :=
  (B_exact_fifo TernaryPhases.cNet cc0 cc0 cu 2 cel_hstab cel_hu cel_fixA 1 cel_fixB 3).1 cel_q_x

end Formal.Cells.TernaryExact
