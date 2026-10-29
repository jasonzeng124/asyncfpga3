import Formal.Cells.NecessityMerge

/-!
# CTreeExact: the exact per-node own-loop condition of a bd_ctree, any shape

Probe Bct (shard B). Follow-up of Bmg (`NecessityMerge`: the per-node lemma
`cel_box_exact` and the one-node tree `ctree1_box_exact`). Row
`bd_ctree.node_fork` (C7) was proved SUFFICIENT only (`CTreeTimed.StaticOK`,
lumped windows); it charges the delay SPREAD of every leaf->node path. This
file proves the exact condition for a C-element tree of ANY shape and depth
(every node fan-in >= 2: bd_c2 / bd_c3 / bd_c4, whose real INITs are
`cSpec`, `NecessityMerge.c2_cspec/c3_cspec/c4_cspec`) in B's per-pin model.

## Model (Int ps; every delay is a function of the tree position `Path`)

* **H_PIN_READ** (`Sol`): node `p`'s output obeys `CelEq`: for `t ≥ 0` it is
  `cSpec` of its pins, pin `j` reading child `j`'s output at `(rd (j::p)).σ t`
  (wire + site pin + this node's arc from that pin), and its own output at
  `(fb p).σ t` (arc + feedback wire + site pin). **H_RESET**: 0 before 0.
* Box: `rd q ∈ [lo q, hi q]`, `0 ≤ lo q ≤ hi q`; `fb p ∈ [Qlo p, Qhi p]`,
  `1 ≤ Qlo p ≤ Qhi p`.
* **H_PIN_FIFO**: every edge read map `rd q` is monotone (`Mono`); feedback
  maps are arbitrary.
* **H_LEAF** (`LeafOK`): leaf `q` switches once per phase at strictly
  increasing times `σ q k`, the first at `≥ 0` (values 1, 0, 1, ...).
* **H_ACK** (`HAck`): every leaf's phase-(k+1) switch is at least `E ≥ 1`
  after the ROOT's ideal phase-k edge (`Tm .. tr [] k`: the zero-delay tree of
  the pin reads, which equals the real root's edge in a correct run).

**Spec** (`Good`, `TreeOK`): at EVERY node every possible output equals its
zero-delay C-element of its (ideal) children's pin reads, for every map in the box.

## Results (core Lean; axioms: propext, Classical.choice, Quot.sound)

* `tree_box_exact` (headline): `TreeOK ↔ Cond`, i.e. **H_CTREE_LOOP**: for
  every node `n` and every child `c` of `n`
      `Qhi n ≤ dist_min(n -> root) + E + MaxMin(c) + lo(c -> n)`,
  `MaxMin(leaf) = 0`, `MaxMin(m) = max_j (MaxMin(j) + lo(j -> m))`,
  `dist_min` = sum of the read lo's from `n` up to the root.
  Bmg's proposed formula is RIGHT. No hi of any edge and no spread enters.
* `tree_suff` / `tree_needs`: the two halves. Necessity counter-trace in the
  docstring of `tree_needs` (constant maps at lo, `n` made critical in phase 0,
  a sibling delayed in phase 1, `cel_box_exact`'s adversarial feedback map).
* `bridge_phase` / `bridge_hold` / `bridge_needs`: one node with phase-trace
  inputs (any arity, any monotone maps): ideal output is a phase trace, and
  the exact HHold criterion in arrival times (`rho`).
* `arrive_bound`: the tree-level causal bound (Bmg's missing piece).
* `cond_iff` / `CondR`: the condition as a per-node recursion (decidable).
* gcd_hw shapes: `lv k` (N = 2..4), `sh5` = C2(C4, wire) (N = 5), `sh6` =
  C2(C4, C2) (N = 6); `sh6_cond_iff` (uniform delays: `Qh ≤ E + 2 l`),
  `sh6_numbers` (box numbers where the OLD row fails and the tree is
  glitch-free), `sh6_glitch` (1 ps over: not TreeOK), `nonvacuous`.
* `old_imply_new`: the old row (lumped) implies the new one per node.

NOT covered: the protocol (H_ACK is assumed, `bd_ctree.ack_wait` is its row);
Kleene X windows (the JSON's strict +1 stays on top); correlated corners (the
box treats every pin independently); the port-to-leaf environment is one
lower bound `E` (min over leaves).
-/

namespace Audit.P8.CTreeMut
open Formal.Cells
open Formal.Cells.LibCtlMergeMux (cSpec)
open Formal.Cells.LibGapSteer (Rd)
open Formal.Cells.LibGapMux (int_ind)
open Formal.Cells.NecessityMerge

/-! ## 0. Max over `Fin k` -/

/-- Maximum of `f` over `Fin k` (0 for `k = 0`, never used: nodes have fan-in >= 2). -/
def fmx : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | 1, f => f 0
  | k + 2, f => max (f 0) (fmx (k + 1) (fun j => f j.succ))

theorem le_fmx : ∀ (k : Nat) (f : Fin k → Int) (j : Fin k), f j ≤ fmx k f
  | 0, _, j => j.elim0
  | 1, f, ⟨0, _⟩ => by simp only [fmx]; exact Int.le_refl _
  | 1, _, ⟨_ + 1, h⟩ => absurd h (by omega)
  | k + 2, f, ⟨0, _⟩ => by simp only [fmx]; exact Int.le_max_left _ _
  | k + 2, f, ⟨i + 1, h⟩ => by
      have := le_fmx (k + 1) (fun j => f j.succ) ⟨i, by omega⟩
      simp only [fmx]
      exact Int.le_trans this (Int.le_max_right _ _)

theorem fmx_le : ∀ (k : Nat) (f : Fin k → Int) (B : Int), 1 ≤ k → (∀ j, f j ≤ B) → fmx k f ≤ B
  | 0, _, _, h, _ => absurd h (by omega)
  | 1, _, _, _, h => h 0
  | k + 2, f, B, _, h => by
      have := fmx_le (k + 1) (fun j => f j.succ) B (by omega) (fun j => h j.succ)
      have := h 0
      simp only [fmx]; omega

theorem fmx_mem : ∀ (k : Nat) (f : Fin k → Int), 1 ≤ k → ∃ j, fmx k f = f j
  | 0, _, h => absurd h (by omega)
  | 1, _, _ => ⟨0, rfl⟩
  | k + 2, f, _ => by
      obtain ⟨j, hj⟩ := fmx_mem (k + 1) (fun j => f j.succ) (by omega)
      simp only [fmx]
      by_cases h : f 0 ≤ f j.succ
      · exact ⟨j.succ, by rw [hj]; omega⟩
      · exact ⟨0, by rw [hj]; omega⟩

theorem fmx_nonneg : ∀ (k : Nat) (f : Fin k → Int), (∀ j, 0 ≤ f j) → 0 ≤ fmx k f
  | 0, _, _ => Int.le_refl 0
  | _ + 1, f, h => Int.le_trans (h 0) (le_fmx _ f 0)

/-! ## 1. The arrival time of a value through a monotone read map -/

/-- First `t` in `[b, b + n]` with `P t` (else `b + n`). -/
def srch (P : Int → Bool) : Int → Nat → Int
  | b, 0 => b
  | b, n + 1 => if P b then b else srch P (b + 1) n

theorem srch_spec (P : Int → Bool) : ∀ (n : Nat) (b : Int), P (b + n) = true →
    P (srch P b n) = true ∧ b ≤ srch P b n ∧ ∀ t, b ≤ t → t < srch P b n → P t = false := by
  intro n
  induction n with
  | zero =>
    intro b h
    simp only [srch]
    exact ⟨by simpa using h, Int.le_refl _, fun t h1 h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro b h
    simp only [srch]
    by_cases hb : P b = true
    · rw [if_pos hb]
      exact ⟨hb, Int.le_refl _, fun t h1 h2 => absurd h2 (by omega)⟩
    · simp only [hb, Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2, h3⟩ := ih (b + 1)
        (by rw [show b + 1 + (n : Int) = b + ((n + 1 : Nat) : Int) by omega]; exact h)
      refine ⟨h1, by omega, fun t ht1 ht2 => ?_⟩
      by_cases e : t = b
      · subst e; simpa using hb
      · exact h3 t (by omega) ht2

theorem rd_lohi (r : Rd) : r.lo ≤ r.hi := by have := r.ge 0; have := r.le 0; omega

/-- **Arrival time** `rho r x`: the first instant at which a pin with read
map `r` reads a source instant `≥ x` (a source edge at `x` is SEEN from then on). -/
def rho (r : Rd) (x : Int) : Int :=
  srch (fun t => decide (x ≤ r.σ t)) (x + r.lo) (r.hi - r.lo).toNat

theorem rho_spec (r : Rd) (hm : Mono r) (x t : Int) : x ≤ r.σ t ↔ rho r x ≤ t := by
  have hlh := rd_lohi r
  have hP : (fun t => decide (x ≤ r.σ t)) (x + r.lo + ((r.hi - r.lo).toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    have := r.ge (x + r.lo + ((r.hi - r.lo).toNat : Int)); omega
  obtain ⟨h1, _, h3⟩ := srch_spec (fun t => decide (x ≤ r.σ t)) ((r.hi - r.lo).toNat) (x + r.lo) hP
  unfold rho
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    by_cases hb : x + r.lo ≤ t
    · have := h3 t hb (by omega); simp only [decide_eq_false_iff_not] at this; omega
    · have := r.le t; omega
  · intro h
    simp only [decide_eq_true_eq] at h1
    exact Int.le_trans h1 (hm _ _ h)

theorem rho_ge (r : Rd) (hm : Mono r) (x : Int) : x + r.lo ≤ rho r x := by
  have h1 := (rho_spec r hm x (rho r x)).mpr (Int.le_refl _)
  have := r.le (rho r x); omega

theorem rho_le (r : Rd) (hm : Mono r) (x : Int) : rho r x ≤ x + r.hi :=
  (rho_spec r hm x (x + r.hi)).mp (by have := r.ge (x + r.hi); omega)

theorem rho_const (d x : Int) : rho (Rd.const d) x = x + d := by
  have h1 : x + d ≤ rho (Rd.const d) x := rho_ge (Rd.const d) (const_mono d) x
  have h2 : rho (Rd.const d) x ≤ x + d := rho_le (Rd.const d) (const_mono d) x
  omega

/-! ## 2. Phase traces -/

/-- Phase value: phase 0 drives 1, phase 1 drives 0, ... -/
def V (k : Nat) : Bool := k % 2 == 0

theorem V_succ (k : Nat) : V (k + 1) = !V k := by
  unfold V; cases h : k % 2 == 0 <;> simp_all <;> omega

/-- A **phase trace**: 0 before `T 0`, `V k` on `[T k, T (k+1))`, `T` strictly increasing. -/
structure PhaseTr (x : Int → Bool) (T : Nat → Int) : Prop where
  inc : ∀ k, T k < T (k + 1)
  pre : ∀ t, t < T 0 → x t = false
  ph : ∀ k t, T k ≤ t → t < T (k + 1) → x t = V k

theorem ph_add {T : Nat → Int} (hinc : ∀ k, T k < T (k + 1)) :
    ∀ i d : Nat, T i + d ≤ T (i + d) := by
  intro i d
  induction d with
  | zero => simp
  | succ d ih => have := hinc (i + d); rw [show i + (d + 1) = (i + d) + 1 by omega]; omega

theorem ph_le {T : Nat → Int} (hinc : ∀ k, T k < T (k + 1)) {i j : Nat} (h : i ≤ j) :
    T i ≤ T j := by
  have := ph_add hinc i (j - i); rw [show i + (j - i) = j by omega] at this; omega

theorem ph_find {T : Nat → Int} (hinc : ∀ k, T k < T (k + 1)) (t : Int) (h : T 0 ≤ t) :
    ∃ k, T k ≤ t ∧ t < T (k + 1) := by
  have key : ∀ m : Nat, t < T m → ∃ k, T k ≤ t ∧ t < T (k + 1) := by
    intro m
    induction m with
    | zero => intro h'; omega
    | succ m ih =>
      intro h'
      by_cases hm : T m ≤ t
      · exact ⟨m, hm, h'⟩
      · exact ih (by omega)
  apply key ((t - T 0).toNat + 1)
  have := ph_add hinc 0 ((t - T 0).toNat + 1)
  simp only [Nat.zero_add] at this; omega

def cntPh (T : Nat → Int) (t : Int) : Nat → Nat
  | 0 => 0
  | m + 1 => cntPh T t m + (if T m ≤ t then 1 else 0)

theorem cntPh_eq {T : Nat → Int} (hinc : ∀ k, T k < T (k + 1)) {k : Nat} {t : Int}
    (h1 : T k ≤ t) (h2 : t < T (k + 1)) : ∀ m, cntPh T t m = min m (k + 1) := by
  intro m
  induction m with
  | zero => simp [cntPh]
  | succ m ih =>
    simp only [cntPh, ih]
    by_cases hm : m ≤ k
    · have := ph_le hinc hm
      rw [if_pos (by omega)]; omega
    · have := ph_le hinc (show k + 1 ≤ m by omega)
      rw [if_neg (by omega)]; omega

theorem cntPh_zero {T : Nat → Int} (hinc : ∀ k, T k < T (k + 1)) {t : Int} (h : t < T 0) :
    ∀ m, cntPh T t m = 0 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have := ph_le hinc (Nat.zero_le m)
    simp only [cntPh, ih]; rw [if_neg (by omega)]

/-- The phase trace of a strictly increasing switching-time sequence (a leaf). -/
def ofPh (T : Nat → Int) (t : Int) : Bool :=
  if cntPh T t ((t - T 0).toNat + 1) = 0 then false else V (cntPh T t ((t - T 0).toNat + 1) - 1)

theorem ofPh_phase {T : Nat → Int} (hinc : ∀ k, T k < T (k + 1)) : PhaseTr (ofPh T) T := by
  refine ⟨hinc, fun t ht => ?_, fun k t h1 h2 => ?_⟩
  · simp [ofPh, cntPh_zero hinc ht]
  · have e := cntPh_eq hinc h1 h2 ((t - T 0).toNat + 1)
    have := ph_add hinc 0 k
    simp only [Nat.zero_add] at this
    rw [show min ((t - T 0).toNat + 1) (k + 1) = k + 1 by omega] at e
    simp [ofPh, e]

/-- A pin reading a phase trace through a monotone map sees phase `k` on
`[rho (T k), rho (T (k+1)))`. -/
theorem pin_val {x : Int → Bool} {T : Nat → Int} (hP : PhaseTr x T) {r : Rd} (hm : Mono r)
    {k : Nat} {t : Int} (h1 : rho r (T k) ≤ t) (h2 : t < rho r (T (k + 1))) :
    x (r.σ t) = V k := by
  have a := (rho_spec r hm (T k) t).mpr h1
  have b := rho_spec r hm (T (k + 1)) t
  exact hP.ph k _ a (by
    apply Classical.byContradiction; intro hn; exact absurd (b.mp (by omega)) (by omega))

theorem pin_pre {x : Int → Bool} {T : Nat → Int} (hP : PhaseTr x T) {r : Rd} (hm : Mono r)
    {t : Int} (h : t < rho r (T 0)) : x (r.σ t) = false := by
  have b := rho_spec r hm (T 0) t
  exact hP.pre _ (by
    apply Classical.byContradiction; intro hn; exact absurd (b.mp (by omega)) (by omega))

/-! ## 3. One node: phase-trace inputs, exact HHold -/

section bridge
variable {n : Nat}

/-- The pin-read vector of a node: input `j` read through `r j`. -/
def insF (x : Fin n → Int → Bool) (r : Fin n → Rd) : Int → List Bool :=
  fun t => List.ofFn (fun j => x j ((r j).σ t))

/-- The node's ideal edge times: max over its pins of the arrival times. -/
def Tn (T : Fin n → Nat → Int) (r : Fin n → Rd) (k : Nat) : Int :=
  fmx n (fun j => rho (r j) (T j k))

theorem cs_all (hn : 1 ≤ n) (b : Fin n → Bool) (v q : Bool) (h : ∀ j, b j = v) :
    cSpec (List.ofFn b) q = v := by
  have hm : ∀ y, y ∈ List.ofFn b → y = v := by
    intro y hy; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact h j
  have h0 : b ⟨0, hn⟩ ∈ List.ofFn b := List.mem_ofFn.mpr ⟨_, rfl⟩
  cases v
  · have e1 : (List.ofFn b).all id = false := by
      rw [Bool.eq_false_iff]; intro hh
      have := List.all_eq_true.mp hh _ h0; rw [h] at this; exact absurd this (by decide)
    have e2 : (List.ofFn b).all (! ·) = true := by
      rw [List.all_eq_true]; intro y hy; rw [hm y hy]; rfl
    simp [cSpec, e1, e2]
  · have e1 : (List.ofFn b).all id = true := by
      rw [List.all_eq_true]; intro y hy; rw [hm y hy]; rfl
    simp [cSpec, e1]

theorem cs_split (b : Fin n → Bool) (i j : Fin n) (h : b i ≠ b j) : Split (List.ofFn b) := by
  have hi : b i ∈ List.ofFn b := List.mem_ofFn.mpr ⟨_, rfl⟩
  have hj : b j ∈ List.ofFn b := List.mem_ofFn.mpr ⟨_, rfl⟩
  constructor
  · rw [Bool.eq_false_iff]; intro hh
    have a := List.all_eq_true.mp hh _ hi; have c := List.all_eq_true.mp hh _ hj
    simp only [id] at a c; rw [a, c] at h; exact h rfl
  · rw [Bool.eq_false_iff]; intro hh
    have a := List.all_eq_true.mp hh _ hi; have c := List.all_eq_true.mp hh _ hj
    simp only [Bool.not_eq_true'] at a c; rw [a, c] at h; exact h rfl

theorem cs_nsplit (b : Fin n → Bool) (v : Bool) (h : ∀ j, b j = v) : ¬ Split (List.ofFn b) := by
  intro ⟨h1, h2⟩
  cases v
  · apply absurd h2; rw [Bool.not_eq_false, List.all_eq_true]
    intro y hy; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; rw [h j]; rfl
  · apply absurd h1; rw [Bool.not_eq_false, List.all_eq_true]
    intro y hy; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; rw [h j]; rfl

variable {x : Fin n → Int → Bool} {T : Fin n → Nat → Int} {r : Fin n → Rd}

/-- **`bridge_phase`**: a C-element node whose inputs are phase traces, read
through monotone pin maps, is (ideally) a phase trace with edge times `Tn`,
provided no pin skips a phase (**NoSkip**: every pin's next arrival is after
the node's current edge). -/
theorem bridge_phase (hn : 1 ≤ n) (hP : ∀ j, PhaseTr (x j) (T j)) (hm : ∀ j, Mono (r j))
    (h0 : 0 ≤ Tn T r 0) (hNS : ∀ k j, Tn T r k < rho (r j) (T j (k + 1))) :
    PhaseTr (idl (insF x r)) (Tn T r) := by
  have hinc : ∀ k, Tn T r k < Tn T r (k + 1) :=
    fun k => Int.lt_of_lt_of_le (hNS k ⟨0, hn⟩) (le_fmx _ _ _)
  have hRk : ∀ k j, rho (r j) (T j k) ≤ Tn T r k := fun k j => le_fmx _ _ j
  have hmem : ∀ k, ∃ j, Tn T r k = rho (r j) (T j k) := fun k => fmx_mem _ _ hn
  have key : ∀ t, (t < Tn T r 0 → idl (insF x r) t = false) ∧
      (∀ k, Tn T r k ≤ t → t < Tn T r (k + 1) → idl (insF x r) t = V k) := by
    apply int_ind
    · intro t ht
      refine ⟨fun _ => idl_neg _ ht, fun k hk _ => ?_⟩
      have := ph_le hinc (Nat.zero_le k); omega
    · intro t ht ih
      refine ⟨fun hlt => ?_, fun k hk1 hk2 => ?_⟩
      · rw [idl_eq _ ht]
        obtain ⟨j0, hj0⟩ := hmem 0
        have hp0 : x j0 ((r j0).σ t) = false := pin_pre (hP j0) (hm j0) (by omega)
        by_cases hall : ∀ j, x j ((r j).σ t) = false
        · exact cs_all hn (fun j => x j ((r j).σ t)) false _ hall
        · obtain ⟨i, hi⟩ : ∃ i, x i ((r i).σ t) ≠ false :=
            Classical.byContradiction (fun hc =>
              hall (fun j => Classical.byContradiction (fun hj => hc ⟨j, hj⟩)))
          have hs : Split (insF x r t) :=
            cs_split (fun j => x j ((r j).σ t)) i j0 (by rw [hp0]; exact hi)
          rw [cSpec_split hs]
          exact (ih (t - 1) (by omega)).1 (by omega)
      · rw [idl_eq _ ht]
        obtain ⟨j0, hj0⟩ := hmem (k + 1)
        have hpj0 : x j0 ((r j0).σ t) = V k :=
          pin_val (hP j0) (hm j0) (by have := hRk k j0; omega) (by omega)
        by_cases hall : ∀ j, x j ((r j).σ t) = V k
        · exact cs_all hn (fun j => x j ((r j).σ t)) _ _ hall
        · obtain ⟨i, hi⟩ : ∃ i, x i ((r i).σ t) ≠ V k :=
            Classical.byContradiction (fun hc =>
              hall (fun j => Classical.byContradiction (fun hj => hc ⟨j, hj⟩)))
          have hti : rho (r i) (T i (k + 1)) ≤ t := by
            apply Classical.byContradiction; intro hc
            exact hi (pin_val (hP i) (hm i) (by have := hRk k i; omega) (by omega))
          have hs : Split (insF x r t) :=
            cs_split (fun j => x j ((r j).σ t)) i j0 (by rw [hpj0]; exact hi)
          rw [cSpec_split hs]
          have := hNS k i
          exact (ih (t - 1) (by omega)).2 k (by omega) (by omega)
  exact ⟨hinc, fun t ht => (key t).1 ht, fun k t h1 h2 => (key t).2 k h1 h2⟩

/-- **`bridge_hold`** (sufficient): if every pin's next arrival is at least
`Qhi` after the node's edge, HHold holds. -/
theorem bridge_hold (hn : 1 ≤ n) (hP : ∀ j, PhaseTr (x j) (T j)) (hm : ∀ j, Mono (r j))
    (h0 : 0 ≤ Tn T r 0) (hNS : ∀ k j, Tn T r k < rho (r j) (T j (k + 1)))
    {Qlo Qhi : Int} (hQ : 0 ≤ Qlo) (hC : ∀ k j, Tn T r k + Qhi ≤ rho (r j) (T j (k + 1))) :
    HHold (insF x r) Qlo Qhi := by
  intro t ht hs s h1 h2
  have PT := bridge_phase hn hP hm h0 hNS
  by_cases h : t < Tn T r 0
  · rw [PT.pre t h, PT.pre s (by omega)]
  · obtain ⟨k, hk1, hk2⟩ := ph_find PT.inc t (by omega)
    obtain ⟨j, hj⟩ : ∃ j, rho (r j) (T j (k + 1)) ≤ t := by
      apply Classical.byContradiction; intro hc
      apply cs_nsplit (fun j => x j ((r j).σ t)) (V k) _ hs
      intro j
      exact pin_val (hP j) (hm j) (Int.le_trans (le_fmx _ _ j) hk1)
        (by apply Classical.byContradiction; intro hh; exact hc ⟨j, by omega⟩)
    have := hC k j
    rw [PT.ph k t hk1 hk2, PT.ph k s (by omega) (by omega)]

/-- **`bridge_needs`** (necessity, phase 0): if pin `j0` arrives in phase 1
strictly before pin `j1` and less than `Qhi` after the node's phase-0 edge,
HHold fails. -/
theorem bridge_needs (hn : 1 ≤ n) (hP : ∀ j, PhaseTr (x j) (T j)) (hm : ∀ j, Mono (r j))
    (h0 : 0 ≤ Tn T r 0) (hNS : ∀ k j, Tn T r k < rho (r j) (T j (k + 1)))
    {Qlo Qhi : Int} (hQ : Qlo ≤ Qhi) (j0 j1 : Fin n)
    (h01 : rho (r j0) (T j0 1) < rho (r j1) (T j1 1))
    (hv : rho (r j0) (T j0 1) < Tn T r 0 + Qhi) : ¬ HHold (insF x r) Qlo Qhi := by
  intro H
  have PT := bridge_phase hn hP hm h0 hNS
  have a1 : Tn T r 0 < rho (r j0) (T j0 1) := hNS 0 j0
  have a2 : Tn T r 0 < rho (r j1) (T j1 1) := hNS 0 j1
  have a3 : Tn T r 1 < rho (r j0) (T j0 2) := hNS 1 j0
  have a4 : rho (r j0) (T j0 1) ≤ Tn T r 1 := le_fmx _ _ j0
  have a5 : rho (r j1) (T j1 1) ≤ Tn T r 1 := le_fmx _ _ j1
  have a6 : rho (r j1) (T j1 0) ≤ Tn T r 0 := le_fmx _ _ j1
  have p0 : x j0 ((r j0).σ (rho (r j0) (T j0 1))) = V 1 :=
    pin_val (hP j0) (hm j0) (Int.le_refl _) (by show _ < rho (r j0) (T j0 2); omega)
  have p1 : x j1 ((r j1).σ (rho (r j0) (T j0 1))) = V 0 :=
    pin_val (hP j1) (hm j1) (by omega) h01
  have hs : Split (insF x r (rho (r j0) (T j0 1))) :=
    cs_split (fun j => x j ((r j).σ (rho (r j0) (T j0 1)))) j0 j1
      (by rw [p0, p1]; decide)
  have e := H _ (by omega) hs (rho (r j0) (T j0 1) - Qhi) (Int.le_refl _) (by omega)
  rw [PT.pre _ (by omega), PT.ph 0 _ (by omega) (by show _ < Tn T r 1; omega)] at e
  exact absurd e (by decide)

end bridge

/-! ## 4. Trees of any shape -/

/-- Shape of a C-element tree: a leaf (a port) or a node of fan-in `k` (a
`bd_c2/c3/c4`, real INIT = `cSpec`: `NecessityMerge.c2_cspec/c3_cspec/c4_cspec`). -/
inductive Tr where
  | leaf : Tr
  | node : (k : Nat) → (Fin k → Tr) → Tr

/-- Position in the tree: child indices, deepest first (`[]` = root; child `j`
of the node at `p` is at `j :: p`). Every per-node / per-edge delay is a
function of the position. -/
abbrev Path := List Nat

/-- Every node has fan-in >= 2 (bd_ctree: bd_c2/c3/c4; a 1-wide chunk is a wire, i.e. a leaf). -/
def Wf : Tr → Prop
  | .leaf => True
  | .node k cs => 2 ≤ k ∧ ∀ j, Wf (cs j)

/-- `InT s p p0 s0`: the sub-tree `s0` sits at position `p0` inside `s` (at `p`). -/
inductive InT : Tr → Path → Path → Tr → Prop
  | refl (s : Tr) (p : Path) : InT s p p s
  | child {k : Nat} {cs : Fin k → Tr} {p : Path} (j : Fin k) {p0 : Path} {s0 : Tr} :
      InT (cs j) (j.1 :: p) p0 s0 → InT (.node k cs) p p0 s0

/-- Ideal (zero-delay) edge time of a sub-tree in one phase, given the leaf
switching times `τ` of that phase: max over pins of the arrival times. -/
def Tf (rd : Path → Rd) (τ : Path → Int) : Tr → Path → Int
  | .leaf, p => τ p
  | .node k cs, p => fmx k (fun j => rho (rd (j.1 :: p)) (Tf rd τ (cs j) (j.1 :: p)))

/-- Phase-`k` edge time. -/
def Tm (rd : Path → Rd) (σ : Path → Nat → Int) (s : Tr) (p : Path) (k : Nat) : Int :=
  Tf rd (fun q => σ q k) s p

/-- **MaxMin**: the latest of the earliest arrivals, `MaxMin(leaf) = 0`,
`MaxMin(m) = max_j (MaxMin(j) + lo(j -> m))`. -/
def MaxMin (lo : Path → Int) : Tr → Path → Int
  | .leaf, _ => 0
  | .node k cs, p => fmx k (fun j => MaxMin lo (cs j) (j.1 :: p) + lo (j.1 :: p))

/-- **dist_min**(p -> root): sum of the read lo's on the edges from `p` up to the root. -/
def distL (lo : Path → Int) : Path → Int
  | [] => 0
  | j :: p => lo (j :: p) + distL lo p

/-- Ideal trace of every sub-tree: leaves = phase traces of `σ`, nodes = the
zero-delay C-element of their pin reads. -/
def iv (rd : Path → Rd) (σ : Path → Nat → Int) : Tr → Path → Int → Bool
  | .leaf, p => ofPh (σ p)
  | .node _ cs, p => idl (insF (fun j => iv rd σ (cs j) (j.1 :: p)) (fun j => rd (j.1 :: p)))

/-- **Gate-level semantics** (H_PIN_READ + H_RESET per node): `O` is a
possible output of the sub-tree: a node's output obeys `CelEq` (its real INIT
law, own feedback read through `fb p`) on SOME possible outputs of its
children, each read through the edge's map `rd`. -/
def Sol (rd : Path → Rd) (σ : Path → Nat → Int) (fb : Path → Rd) :
    Tr → Path → (Int → Bool) → Prop
  | .leaf, p, O => O = ofPh (σ p)
  | .node k cs, p, O => ∃ X : Fin k → Int → Bool,
      (∀ j, Sol rd σ fb (cs j) (j.1 :: p) (X j)) ∧
      CelEq (insF X (fun j => rd (j.1 :: p))) (fb p) O

/-- **Spec**: at EVERY node, every possible output equals the ideal one. -/
def Good (rd : Path → Rd) (σ : Path → Nat → Int) (fb : Path → Rd) : Tr → Path → Prop
  | .leaf, _ => True
  | .node k cs, p => (∀ O, Sol rd σ fb (.node k cs) p O → O = iv rd σ (.node k cs) p) ∧
      ∀ j, Good rd σ fb (cs j) (j.1 :: p)

/-- The run (one possible output, built bottom-up). -/
def rv (rd : Path → Rd) (σ : Path → Nat → Int) (fb : Path → Rd) : Tr → Path → Int → Bool
  | .leaf, p => ofPh (σ p)
  | .node _ cs, p =>
      run (insF (fun j => rv rd σ fb (cs j) (j.1 :: p)) (fun j => rd (j.1 :: p))) (fb p).σ

theorem sol_rv {rd : Path → Rd} {σ : Path → Nat → Int} {fb : Path → Rd}
    (hσ : ∀ q u, (fb q).σ u ≤ u - 1) : ∀ s p, Sol rd σ fb s p (rv rd σ fb s p) := by
  intro s
  induction s with
  | leaf => intro p; rfl
  | node k cs ih =>
    intro p
    exact ⟨fun j => rv rd σ fb (cs j) (j.1 :: p), fun j => ih j _,
      fun u hu => run_neg _ _ hu, fun u hu => run_eq _ _ (hσ p) hu⟩

theorem sol_iv_of_good {rd : Path → Rd} {σ : Path → Nat → Int} {fb : Path → Rd}
    (hσ : ∀ q u, (fb q).σ u ≤ u - 1) {s : Tr} {p : Path} (hg : Good rd σ fb s p) :
    Sol rd σ fb s p (iv rd σ s p) := by
  cases s with
  | leaf => rfl
  | node k cs =>
    have e := hg.1 _ (sol_rv hσ (.node k cs) p)
    rw [← e]; exact sol_rv hσ _ p

/-! ### Position lemmas -/

/-- `q` lies at or below `p0`. -/
def Und (p0 q : Path) : Prop := ∃ r, q = r ++ p0

theorem und_of_InT {s : Tr} {p q : Path} {s' : Tr} (h : InT s p q s') : Und p q := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @child k cs p j p0 s0 _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r ++ [j.1], by rw [hr]; simp⟩

theorem und_trans {a b c : Path} (h1 : Und a b) (h2 : Und b c) : Und a c := by
  obtain ⟨r1, rfl⟩ := h1; obtain ⟨r2, rfl⟩ := h2
  exact ⟨r2 ++ r1, by simp⟩

theorem und_inj {k : Nat} {i j : Fin k} {p q : Path} (h1 : Und (i.1 :: p) q)
    (h2 : Und (j.1 :: p) q) : i = j := by
  obtain ⟨r1, h1⟩ := h1; obtain ⟨r2, h2⟩ := h2
  have := (List.append_inj' (h1.symm.trans h2) (by simp)).2
  exact Fin.ext (List.cons.inj this).1

theorem InT_trans {s : Tr} {p p1 : Path} {s1 : Tr} (h1 : InT s p p1 s1) :
    ∀ {p2 : Path} {s2 : Tr}, InT s1 p1 p2 s2 → InT s p p2 s2 := by
  induction h1 with
  | refl => exact fun h => h
  | child j _ ih => exact fun h => InT.child j (ih h)

theorem wf_at {s : Tr} {p p0 : Path} {s0 : Tr} (h : InT s p p0 s0) : Wf s → Wf s0 := by
  induction h with
  | refl => exact id
  | child j _ ih => exact fun hw => ih (hw.2 j)

theorem good_at {rd : Path → Rd} {σ : Path → Nat → Int} {fb : Path → Rd} {s : Tr} {p p0 : Path}
    {s0 : Tr} (h : InT s p p0 s0) : Good rd σ fb s p → Good rd σ fb s0 p0 := by
  induction h with
  | refl => exact id
  | child j _ ih => exact fun hg => ih (hg.2 j)

/-! ### Max-plus bounds -/

section bounds
variable {rd : Path → Rd} {lo : Path → Int}

theorem maxmin_nonneg (hlo : ∀ q, 0 ≤ lo q) : ∀ s p, 0 ≤ MaxMin lo s p := by
  intro s
  induction s with
  | leaf => intro p; exact Int.le_refl 0
  | node k cs ih =>
    intro p
    exact fmx_nonneg _ _ (fun j => by have := ih j (j.1 :: p); have := hlo (j.1 :: p); omega)

theorem distL_nonneg (hlo : ∀ q, 0 ≤ lo q) : ∀ p, 0 ≤ distL lo p
  | [] => Int.le_refl 0
  | j :: p => by have := distL_nonneg hlo p; have := hlo (j :: p); simp only [distL]; omega

/-- **Ancestor bound**: an edge of the sub-tree at `p0` reaches the node at
`p` no earlier than `dist_min`. -/
theorem anc_bound (hrl : ∀ q x, x + lo q ≤ rho (rd q) x) (τ : Path → Int) {s : Tr} {p p0 : Path}
    {s0 : Tr} (h : InT s p p0 s0) : Tf rd τ s0 p0 + distL lo p0 ≤ Tf rd τ s p + distL lo p := by
  induction h with
  | refl => exact Int.le_refl _
  | @child k cs p j p0 s0 _ ih =>
    have a := hrl (j.1 :: p) (Tf rd τ (cs j) (j.1 :: p))
    have b := le_fmx k (fun j => rho (rd (j.1 :: p)) (Tf rd τ (cs j) (j.1 :: p))) j
    simp only [distL] at ih
    show _ ≤ fmx k (fun j => rho (rd (j.1 :: p)) (Tf rd τ (cs j) (j.1 :: p))) + _
    omega

/-- **Lower bound**: if every leaf switches at `≥ B`, the sub-tree's edge is
`≥ B + MaxMin`. -/
theorem low_bound (hrl : ∀ q x, x + lo q ≤ rho (rd q) x) (τ : Path → Int) (B : Int) :
    ∀ s p, Wf s → (∀ q, InT s p q .leaf → B ≤ τ q) → B + MaxMin lo s p ≤ Tf rd τ s p := by
  intro s
  induction s with
  | leaf => intro p _ h; have := h p (InT.refl _ _); simp only [MaxMin, Tf]; omega
  | node k cs ih =>
    intro p hw h
    obtain ⟨j, hj⟩ := fmx_mem k (fun j => MaxMin lo (cs j) (j.1 :: p) + lo (j.1 :: p)) (by have := hw.1; omega)
    have a := ih j (j.1 :: p) (hw.2 j) (fun q hq => h q (InT.child j hq))
    have b := hrl (j.1 :: p) (Tf rd τ (cs j) (j.1 :: p))
    have c := le_fmx k (fun j => rho (rd (j.1 :: p)) (Tf rd τ (cs j) (j.1 :: p))) j
    show B + fmx k _ ≤ fmx k _
    rw [hj]; omega

/-- **Upper bound** (maps at their lo): leaves `≤ B` give edge `≤ B + MaxMin`. -/
theorem up_bound (hru : ∀ q x, rho (rd q) x ≤ x + lo q) (τ : Path → Int) (B : Int) :
    ∀ s p, Wf s → (∀ q, InT s p q .leaf → τ q ≤ B) → Tf rd τ s p ≤ B + MaxMin lo s p := by
  intro s
  induction s with
  | leaf => intro p _ h; have := h p (InT.refl _ _); simp only [MaxMin, Tf]; omega
  | node k cs ih =>
    intro p hw h
    show fmx k _ ≤ B + fmx k _
    apply fmx_le _ _ _ (by have := hw.1; omega)
    intro j
    have a := ih j (j.1 :: p) (hw.2 j) (fun q hq => h q (InT.child j hq))
    have b := hru (j.1 :: p) (Tf rd τ (cs j) (j.1 :: p))
    have c := le_fmx k (fun j => MaxMin lo (cs j) (j.1 :: p) + lo (j.1 :: p)) j
    omega

/-- **Critical-path bound** (maps at their lo): if every leaf NOT below `p0`
switches at `≤ B`, the edge at `p` is at most the later of `B + MaxMin` and
the edge at `p0` plus `dist_min(p0 -> p)`. -/
theorem crit_bound (hru : ∀ q x, rho (rd q) x ≤ x + lo q) (τ : Path → Int) (B : Int)
    {s : Tr} {p p0 : Path} {s0 : Tr} (h : InT s p p0 s0) :
    Wf s → (∀ q, InT s p q .leaf → ¬ Und p0 q → τ q ≤ B) →
    Tf rd τ s p ≤ max (B + MaxMin lo s p) (Tf rd τ s0 p0 + distL lo p0 - distL lo p) := by
  induction h with
  | refl => intro _ _; omega
  | @child k cs p j p0 s0 hj ih =>
    intro hw hl
    have ihj := ih (hw.2 j) (fun q hq hn => hl q (InT.child j hq) hn)
    have hu0 : Und (j.1 :: p) p0 := und_of_InT hj
    show fmx k _ ≤ max (B + fmx k _) _
    apply fmx_le _ _ _ (by have := hw.1; omega)
    intro i
    have b := hru (i.1 :: p) (Tf rd τ (cs i) (i.1 :: p))
    have c := le_fmx k (fun j => MaxMin lo (cs j) (j.1 :: p) + lo (j.1 :: p)) i
    by_cases hij : i = j
    · subst hij
      simp only [distL] at ihj; omega
    · have hb := up_bound hru τ B (cs i) (i.1 :: p) (hw.2 i) (fun q hq => by
        apply hl q (InT.child i hq)
        intro hq0
        exact hij (und_inj (und_of_InT hq) (und_trans hu0 hq0)))
      omega

end bounds

/-! ## 5. The tree in its environment: per-node facts -/

/-- **H_LEAF**: leaf `q` switches at strictly increasing times (one clean edge
per phase, values alternating 1, 0, 1, ...), the first at `≥ 0`. -/
def LeafOK (σ : Path → Nat → Int) (q : Path) : Prop := (∀ k, σ q k < σ q (k + 1)) ∧ 0 ≤ σ q 0

/-- **H_ACK** (four-phase ack wait, causal): every leaf's next switch is at
least `E` after the root's (ideal) edge of the current phase. -/
def HAck (rd : Path → Rd) (σ : Path → Nat → Int) (E : Int) (tr : Tr) : Prop :=
  ∀ q, InT tr [] q .leaf → ∀ k, Tm rd σ tr [] k + E ≤ σ q (k + 1)

/-- No pin of the node skips a phase. -/
def NS (rd : Path → Rd) (σ : Path → Nat → Int) : Tr → Path → Prop
  | .leaf, _ => True
  | .node k cs, p => ∀ kk (j : Fin k),
      Tm rd σ (.node k cs) p kk < rho (rd (j.1 :: p)) (Tm rd σ (cs j) (j.1 :: p) (kk + 1))

/-- The node's own loop has settled before any pin's next arrival. -/
def HC (rd : Path → Rd) (σ : Path → Nat → Int) (Qhi : Path → Int) : Tr → Path → Prop
  | .leaf, _ => True
  | .node k cs, p => ∀ kk (j : Fin k),
      Tm rd σ (.node k cs) p kk + Qhi p ≤ rho (rd (j.1 :: p)) (Tm rd σ (cs j) (j.1 :: p) (kk + 1))

section facts
variable {rd : Path → Rd} {σ : Path → Nat → Int}

theorem iv_phase (hm : ∀ q, Mono (rd q)) (hlo : ∀ q, 0 ≤ (rd q).lo) :
    ∀ s p, Wf s → (∀ q, InT s p q .leaf → LeafOK σ q) →
      (∀ p0 s0, InT s p p0 s0 → NS rd σ s0 p0) →
      PhaseTr (iv rd σ s p) (Tm rd σ s p) ∧ 0 ≤ Tm rd σ s p 0 := by
  intro s
  induction s with
  | leaf =>
    intro p _ hl _
    have h := hl p (InT.refl _ _)
    exact ⟨ofPh_phase h.1, h.2⟩
  | node k cs ih =>
    intro p hw hl hns
    have hc : ∀ j : Fin k, PhaseTr (iv rd σ (cs j) (j.1 :: p)) (Tm rd σ (cs j) (j.1 :: p)) ∧
        0 ≤ Tm rd σ (cs j) (j.1 :: p) 0 :=
      fun j => ih j _ (hw.2 j) (fun q hq => hl q (InT.child j hq))
        (fun p0 s0 h => hns p0 s0 (InT.child j h))
    have hk : 1 ≤ k := by have := hw.1; omega
    let j0 : Fin k := ⟨0, hk⟩
    have h0 : 0 ≤ Tn (fun j => Tm rd σ (cs j) (j.1 :: p)) (fun j => rd (j.1 :: p)) 0 := by
      have a := le_fmx k (fun j => rho (rd (j.1 :: p)) (Tm rd σ (cs j) (j.1 :: p) 0)) j0
      have b := rho_ge (rd (j0.1 :: p)) (hm _) (Tm rd σ (cs j0) (j0.1 :: p) 0)
      have := (hc j0).2; have := hlo (j0.1 :: p)
      show 0 ≤ fmx k (fun j => rho (rd (j.1 :: p)) (Tm rd σ (cs j) (j.1 :: p) 0)); omega
    exact ⟨bridge_phase (x := fun j => iv rd σ (cs j) (j.1 :: p))
      (T := fun j => Tm rd σ (cs j) (j.1 :: p)) (r := fun j => rd (j.1 :: p)) hk
      (fun j => (hc j).1) (fun j => hm _) h0 (hns p _ (InT.refl _ _)), h0⟩

/-- **`sol_ideal`**: with NoSkip and the loop condition at every node, every
possible output of every node is its ideal trace. -/
theorem sol_ideal (hm : ∀ q, Mono (rd q)) (hlo : ∀ q, 0 ≤ (rd q).lo) {fb : Path → Rd}
    {Qhi : Path → Int} (hfb : ∀ q, 1 ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q) :
    ∀ s p, Wf s → (∀ q, InT s p q .leaf → LeafOK σ q) →
      (∀ p0 s0, InT s p p0 s0 → NS rd σ s0 p0 ∧ HC rd σ Qhi s0 p0) →
      ∀ O, Sol rd σ fb s p O → O = iv rd σ s p := by
  intro s
  induction s with
  | leaf => intro p _ _ _ O h; exact h
  | node k cs ih =>
    intro p hw hl hh O hO
    obtain ⟨X, hX, hcel⟩ := hO
    have hXe : X = fun j => iv rd σ (cs j) (j.1 :: p) := funext fun j =>
      ih j _ (hw.2 j) (fun q hq => hl q (InT.child j hq))
        (fun p0 s0 h => hh p0 s0 (InT.child j h)) (X j) (hX j)
    subst hXe
    have hk : 1 ≤ k := by have := hw.1; omega
    have hc : ∀ j : Fin k, PhaseTr (iv rd σ (cs j) (j.1 :: p)) (Tm rd σ (cs j) (j.1 :: p)) :=
      fun j => (iv_phase hm hlo (cs j) _ (hw.2 j) (fun q hq => hl q (InT.child j hq))
        (fun p0 s0 h => (hh p0 s0 (InT.child j h)).1)).1
    have h0 := (iv_phase hm hlo (.node k cs) p hw hl (fun p0 s0 h => (hh p0 s0 h).1)).2
    have HH := bridge_hold (x := fun j => iv rd σ (cs j) (j.1 :: p))
      (T := fun j => Tm rd σ (cs j) (j.1 :: p)) (r := fun j => rd (j.1 :: p)) hk hc
      (fun j => hm _) h0 (hh p _ (InT.refl _ _)).1 (Qlo := (fb p).lo) (Qhi := Qhi p)
      (by have := (hfb p).1; omega) (hh p _ (InT.refl _ _)).2
    exact funext (cel_ok (hfb p).1 HH (fb p) (Int.le_refl _) (hfb p).2 O hcel)

theorem good_of (hm : ∀ q, Mono (rd q)) (hlo : ∀ q, 0 ≤ (rd q).lo) {fb : Path → Rd}
    {Qhi : Path → Int} (hfb : ∀ q, 1 ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q) :
    ∀ s p, Wf s → (∀ q, InT s p q .leaf → LeafOK σ q) →
      (∀ p0 s0, InT s p p0 s0 → NS rd σ s0 p0 ∧ HC rd σ Qhi s0 p0) → Good rd σ fb s p := by
  intro s
  induction s with
  | leaf => intro _ _ _ _; trivial
  | node k cs ih =>
    intro p hw hl hh
    exact ⟨fun O h => sol_ideal hm hlo hfb (.node k cs) p hw hl hh O h,
      fun j => ih j _ (hw.2 j) (fun q hq => hl q (InT.child j hq))
        (fun p0 s0 h => hh p0 s0 (InT.child j h))⟩

/-- **`arrive_bound`** (the tree-level causal bound): under H_ACK, pin `j` of
the node at `p0` sees its next edge no earlier than
`edge + dist_min(p0 -> root) + E + MaxMin(child) + lo(child -> node)`. -/
theorem arrive_bound {lo : Path → Int} (hrl : ∀ q x, x + lo q ≤ rho (rd q) x) {E : Int}
    {tr : Tr} (hw : Wf tr) (hack : HAck rd σ E tr) {p0 : Path} {k : Nat} {cs : Fin k → Tr}
    (hin : InT tr [] p0 (.node k cs)) (kk : Nat) (j : Fin k) :
    Tm rd σ (.node k cs) p0 kk + distL lo p0 + E + MaxMin lo (cs j) (j.1 :: p0) + lo (j.1 :: p0)
      ≤ rho (rd (j.1 :: p0)) (Tm rd σ (cs j) (j.1 :: p0) (kk + 1)) := by
  have hwj : Wf (cs j) := (wf_at hin hw).2 j
  have a := low_bound hrl (fun q => σ q (kk + 1)) (Tm rd σ tr [] kk + E) (cs j) (j.1 :: p0) hwj
    (fun q hq => hack q (InT_trans hin (InT.child j hq)) kk)
  have b := hrl (j.1 :: p0) (Tm rd σ (cs j) (j.1 :: p0) (kk + 1))
  have c := anc_bound hrl (fun q => σ q kk) hin
  simp only [distL] at c
  unfold Tm at *
  omega

end facts

/-! ## 6. Headline: the exact per-node condition, any shape -/

/-- **Spec over the box**: for every monotone read map in `[lo, hi]` on every
edge, every leaf schedule obeying H_LEAF and H_ACK, and every feedback map in
`[Qlo, Qhi]` at every node, every node of the tree is glitch-free
(equals its zero-delay C-element). -/
def TreeOK (lo hi Qlo Qhi : Path → Int) (E : Int) (tr : Tr) : Prop :=
  ∀ (rd : Path → Rd) (σ : Path → Nat → Int), (∀ q, Mono (rd q)) →
    (∀ q, lo q ≤ (rd q).lo ∧ (rd q).hi ≤ hi q) →
    (∀ q, InT tr [] q .leaf → LeafOK σ q) → HAck rd σ E tr →
    ∀ fb : Path → Rd, (∀ q, Qlo q ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q) → Good rd σ fb tr []

/-- **H_CTREE_LOOP** (the replacement for `bd_ctree.node_fork`): for every node
`n` and every child `c` of `n`,
`Qhi n ≤ dist_min(n -> root) + E + MaxMin(c) + lo(c -> n)`. -/
def Cond (lo Qhi : Path → Int) (E : Int) (tr : Tr) : Prop :=
  ∀ p0 k (cs : Fin k → Tr), InT tr [] p0 (.node k cs) → ∀ j : Fin k,
    Qhi p0 ≤ distL lo p0 + E + MaxMin lo (cs j) (j.1 :: p0)  -- MUTANT: dropped + lo (j.1 :: p0)

section headline
variable {lo hi Qlo Qhi : Path → Int} {E : Int}

/-- **`tree_suff`** (sufficient, any monotone maps in the box). -/
theorem tree_suff {tr : Tr} (hwf : Wf tr) (hlo : ∀ q, 0 ≤ lo q) (hQ1 : ∀ q, 1 ≤ Qlo q)
    (hE : 1 ≤ E) (hC : Cond lo Qhi E tr) : TreeOK lo hi Qlo Qhi E tr := by
  intro rd σ hm hbox hleaf hack fb hfb
  have hrl : ∀ q x, x + lo q ≤ rho (rd q) x := fun q x => by
    have := rho_ge (rd q) (hm q) x; have := (hbox q).1; omega
  have hlo' : ∀ q, 0 ≤ (rd q).lo := fun q => by have := (hbox q).1; have := hlo q; omega
  apply good_of hm hlo' (Qhi := Qhi)
    (fun q => ⟨by have := hQ1 q; have := (hfb q).1; omega, (hfb q).2⟩) tr [] hwf hleaf
  intro p0 s0 hin
  cases s0 with
  | leaf => exact ⟨trivial, trivial⟩
  | node k cs =>
    refine ⟨?_, ?_⟩
    · simp only [NS]; intro kk j
      have := arrive_bound hrl hwf hack hin kk j
      have := distL_nonneg hlo p0; have := maxmin_nonneg hlo (cs j) (j.1 :: p0)
      have := hlo (j.1 :: p0)
      omega
    · simp only [HC]; intro kk j
      have := arrive_bound hrl hwf hack hin kk j
      have := hC p0 k cs hin j
      omega

/-! ### The necessity witness -/

open Classical in
/-- Phase-0 witness schedule: leaves below `p0` switch late (`M`), the others at 0. -/
noncomputable def wτ (p0 : Path) (M : Int) (q : Path) : Int := if Und p0 q then M else 0

theorem wτ_pos {p0 q : Path} {M : Int} (h : Und p0 q) : wτ p0 M q = M := by simp [wτ, h]
theorem wτ_neg {p0 q : Path} {M : Int} (h : ¬ Und p0 q) : wτ p0 M q = 0 := by simp [wτ, h]
theorem wτ_le {p0 q : Path} {M : Int} (hM : 0 ≤ M) : wτ p0 M q ≤ M := by
  unfold wτ; split <;> omega
theorem wτ_nonneg {p0 q : Path} {M : Int} (hM : 0 ≤ M) : 0 ≤ wτ p0 M q := by
  unfold wτ; split <;> omega

/-- Phases >= 2 of the witness: all leaves together, `G` apart. -/
def gS (G : Int) : Nat → Int
  | 0 => 2 * G
  | k + 1 => gS G k + G

/-- The witness schedule: phase 0 `τ0`, phase 1 `τ1`, then `gS`. -/
def wσ (τ0 τ1 : Path → Int) (G : Int) : Path → Nat → Int
  | q, 0 => τ0 q
  | q, 1 => τ1 q
  | _, k + 2 => gS G k

/-- **`tree_needs`** (necessity): if the spec holds over the box then
H_CTREE_LOOP holds at every node. Counter-trace (when it fails at node `p0`,
child `j0`): every edge read at its lo (constant maps); phase 0: leaves below
`p0` switch at `M = MaxMin(root)`, the others at 0, so `p0` is the critical
input of every ancestor; phase 1: every leaf switches exactly `E` after the
root's edge (H_ACK at equality), except the leaves below a sibling `j1` of
`j0`, which wait `M'` longer; phases >= 2 far apart. Then `p0`'s pin `j0`
reads phase 1 while pin `j1` still reads phase 0, less than `Qhi` after
`p0`'s own edge: the adversarial feedback map of `cel_box_exact` glitches it. -/
theorem tree_needs {tr : Tr} (hwf : Wf tr) (hlo : ∀ q, 0 ≤ lo q) (hlh : ∀ q, lo q ≤ hi q)
    (hQ1 : ∀ q, 1 ≤ Qlo q) (hQ : ∀ q, Qlo q ≤ Qhi q) (hE : 1 ≤ E)
    (H : TreeOK lo hi Qlo Qhi E tr) : Cond lo Qhi E tr := by
  intro p0 k cs hin j0
  apply Classical.byContradiction; intro hlt
  have hwk : Wf (.node k cs) := wf_at hin hwf
  have hk : 2 ≤ k := hwk.1
  obtain ⟨j1, hj1⟩ : ∃ j1 : Fin k, j1 ≠ j0 := by
    by_cases h : j0.1 = 0
    · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
  obtain ⟨rd, hrd⟩ : ∃ rd : Path → Rd, rd = fun q => Rd.const (lo q) := ⟨_, rfl⟩
  have hm : ∀ q, Mono (rd q) := by subst hrd; exact fun q => const_mono _
  have hrc : ∀ q x, rho (rd q) x = x + lo q := by subst hrd; exact fun q x => rho_const _ _
  have hrl : ∀ q x, x + lo q ≤ rho (rd q) x := fun q x => by rw [hrc]; exact Int.le_refl _
  have hru : ∀ q x, rho (rd q) x ≤ x + lo q := fun q x => by rw [hrc]; exact Int.le_refl _
  have hbox : ∀ q, lo q ≤ (rd q).lo ∧ (rd q).hi ≤ hi q := by
    subst hrd; exact fun q => ⟨Int.le_refl _, hlh q⟩
  have hlo' : ∀ q, 0 ≤ (rd q).lo := fun q => by have := (hbox q).1; have := hlo q; omega
  obtain ⟨D, hD⟩ : ∃ D, D = MaxMin lo tr [] := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ maxmin_nonneg hlo _ _
  have hm00 := maxmin_nonneg hlo (cs j0) (j0.1 :: p0)
  have hlo0 := hlo (j0.1 :: p0)
  obtain ⟨M', hM'⟩ : ∃ M', M' = MaxMin lo (cs j0) (j0.1 :: p0) + lo (j0.1 :: p0) + 1 :=
    ⟨_, rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ T0, T0 = Tf rd (wτ p0 D) tr [] := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 3 * D + 2 * E + M' + 1 := ⟨_, rfl⟩
  -- the schedule
  have hT0up : T0 ≤ D + D := by
    have := up_bound hru (wτ p0 D) D tr [] hwf (fun q _ => wτ_le hD0); omega
  have hT0leaf : ∀ q, InT tr [] q .leaf → wτ p0 D q ≤ T0 := fun q hq => by
    have a := anc_bound hrl (wτ p0 D) hq; have := distL_nonneg hlo q
    simp only [Tf, distL] at a; omega
  have h1lo : ∀ q, T0 + E ≤ T0 + E + wτ (j1.1 :: p0) M' q := fun q => by
    have := wτ_nonneg (p0 := j1.1 :: p0) (q := q) (show 0 ≤ M' by omega); omega
  have h1hi : ∀ q, T0 + E + wτ (j1.1 :: p0) M' q ≤ T0 + E + M' := fun q => by
    have := wτ_le (p0 := j1.1 :: p0) (q := q) (show 0 ≤ M' by omega); omega
  have hleaf : ∀ q, InT tr [] q .leaf →
      LeafOK (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G) q := by
    intro q hq
    refine ⟨fun kk => ?_, wτ_nonneg hD0⟩
    rcases kk with _ | _ | kk
    · show wτ p0 D q < T0 + E + wτ (j1.1 :: p0) M' q
      have := hT0leaf q hq; have := h1lo q; omega
    · show T0 + E + wτ (j1.1 :: p0) M' q < gS G 0
      have := h1hi q; simp only [gS]; omega
    · show gS G kk < gS G (kk + 1)
      simp only [gS]; omega
  have hack : HAck rd (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G) E tr := by
    intro q _ kk
    rcases kk with _ | _ | kk
    · show Tf rd (wτ p0 D) tr [] + E ≤ T0 + E + wτ (j1.1 :: p0) M' q
      have := h1lo q; omega
    · show Tf rd (fun q => T0 + E + wτ (j1.1 :: p0) M' q) tr [] + E ≤ gS G 0
      have := up_bound hru (fun q => T0 + E + wτ (j1.1 :: p0) M' q) (T0 + E + M') tr [] hwf
        (fun q _ => h1hi q)
      simp only [gS]; omega
    · show Tf rd (fun _ => gS G kk) tr [] + E ≤ gS G (kk + 1)
      have := up_bound hru (fun _ => gS G kk) (gS G kk) tr [] hwf (fun _ _ => Int.le_refl _)
      simp only [gS]; omega
  -- the spec gives CelOK at p0
  have hcel : CelOK (insF (fun j => iv rd (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G)
      (cs j) (j.1 :: p0)) (fun j => rd (j.1 :: p0))) (Qlo p0) (Qhi p0) := by
    intro pq hpq1 hpq2 q' hq' t
    let fb : Path → Rd := fun q => if q = p0 then pq else Rd.const (Qhi q)
    have hfbp : fb p0 = pq := if_pos rfl
    have hfbbox : ∀ q, Qlo q ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q := by
      intro q
      by_cases h : q = p0
      · subst h; rw [hfbp]; exact ⟨hpq1, hpq2⟩
      · have e : fb q = Rd.const (Qhi q) := if_neg h
        rw [e]; exact ⟨hQ q, Int.le_refl _⟩
    have hfbσ : ∀ q u, (fb q).σ u ≤ u - 1 := fun q u => by
      have := (fb q).le u; have := (hfbbox q).1; have := hQ1 q; omega
    have hg := good_at hin (H rd _ hm hbox hleaf hack fb hfbbox)
    have hsol : Sol rd (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G) fb
        (.node k cs) p0 q' :=
      ⟨_, fun j => sol_iv_of_good hfbσ (hg.2 j), by rw [hfbp]; exact hq'⟩
    rw [hg.1 q' hsol]; rfl
  have HH := cel_needs (hQ1 p0) (hQ p0) hcel
  -- every node of the witness run is a phase trace
  have hns : ∀ p1 s1, InT tr [] p1 s1 →
      NS rd (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G) s1 p1 := by
    intro p1 s1 h1
    cases s1 with
    | leaf => trivial
    | node k1 cs1 =>
      simp only [NS]; intro kk j
      have := arrive_bound hrl hwf hack h1 kk j
      have := distL_nonneg hlo p1; have := maxmin_nonneg hlo (cs1 j) (j.1 :: p1)
      have := hlo (j.1 :: p1)
      omega
  have hc := fun j : Fin k => (iv_phase hm hlo' (cs j) (j.1 :: p0) (hwk.2 j)
    (fun q hq => hleaf q (InT_trans hin (InT.child j hq)))
    (fun a b h => hns a b (InT_trans hin (InT.child j h)))).1
  have hn0 := (iv_phase hm hlo' (.node k cs) p0 hwk (fun q hq => hleaf q (InT_trans hin hq))
    (fun a b h => hns a b (InT_trans hin h))).2
  -- the two pins of p0
  have hA : Tf rd (fun q => T0 + E + wτ (j1.1 :: p0) M' q) (cs j0) (j0.1 :: p0) ≤
      (T0 + E) + MaxMin lo (cs j0) (j0.1 :: p0) :=
    up_bound hru _ (T0 + E) _ _ (hwk.2 j0) (fun q hq => by
      have hu := und_of_InT hq
      have hn : ¬ Und (j1.1 :: p0) q := fun h => hj1 (und_inj h hu)
      show T0 + E + wτ (j1.1 :: p0) M' q ≤ T0 + E
      rw [wτ_neg hn]; omega)
  have hB : (T0 + E + M') + MaxMin lo (cs j1) (j1.1 :: p0) ≤
      Tf rd (fun q => T0 + E + wτ (j1.1 :: p0) M' q) (cs j1) (j1.1 :: p0) :=
    low_bound hrl _ (T0 + E + M') _ _ (hwk.2 j1) (fun q hq => by
      show T0 + E + M' ≤ T0 + E + wτ (j1.1 :: p0) M' q
      rw [wτ_pos (und_of_InT hq)]; exact Int.le_refl _)
  have hX : D + MaxMin lo (.node k cs) p0 ≤ Tf rd (wτ p0 D) (.node k cs) p0 :=
    low_bound hrl _ D _ _ hwk (fun q hq => by
      rw [wτ_pos (und_of_InT hq)]; exact Int.le_refl _)
  have hcr := crit_bound hru (wτ p0 D) 0 hin hwf (fun q _ hn => by rw [wτ_neg hn]; exact Int.le_refl _)
  simp only [distL] at hcr
  have := maxmin_nonneg hlo (.node k cs) p0
  have := maxmin_nonneg hlo (cs j1) (j1.1 :: p0)
  have := distL_nonneg hlo p0
  have := hlo (j1.1 :: p0)
  apply bridge_needs (x := fun j => iv rd (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G)
      (cs j) (j.1 :: p0))
    (T := fun j => Tm rd (wσ (wτ p0 D) (fun q => T0 + E + wτ (j1.1 :: p0) M' q) G)
      (cs j) (j.1 :: p0))
    (r := fun j => rd (j.1 :: p0)) (by omega) hc (fun j => hm _) hn0 (hns p0 _ hin) (hQ p0)
    j0 j1 ?_ ?_ HH
  · show rho (rd (j0.1 :: p0)) (Tf rd (fun q => T0 + E + wτ (j1.1 :: p0) M' q) (cs j0) (j0.1 :: p0))
      < rho (rd (j1.1 :: p0)) (Tf rd (fun q => T0 + E + wτ (j1.1 :: p0) M' q) (cs j1) (j1.1 :: p0))
    rw [hrc, hrc]; omega
  · show rho (rd (j0.1 :: p0)) (Tf rd (fun q => T0 + E + wτ (j1.1 :: p0) M' q) (cs j0) (j0.1 :: p0))
      < Tf rd (wτ p0 D) (.node k cs) p0 + Qhi p0
    rw [hrc]; omega

/-- **`tree_box_exact`** (headline): for a bd_ctree of ANY shape (fan-in >= 2
at every node), the tree is glitch-free for every monotone read map in the
box, every leaf schedule obeying H_LEAF / H_ACK and every feedback map in the
box **iff** H_CTREE_LOOP holds at every node:
`Qhi n ≤ dist_min(n -> root) + E + MaxMin(c) + lo(c -> n)` for every child `c`. -/
theorem tree_box_exact {tr : Tr} (hwf : Wf tr) (hlo : ∀ q, 0 ≤ lo q) (hlh : ∀ q, lo q ≤ hi q)
    (hQ1 : ∀ q, 1 ≤ Qlo q) (hQ : ∀ q, Qlo q ≤ Qhi q) (hE : 1 ≤ E) :
    TreeOK lo hi Qlo Qhi E tr ↔ Cond lo Qhi E tr :=
  ⟨tree_needs hwf hlo hlh hQ1 hQ hE, tree_suff hwf hlo hQ1 hE⟩

end headline

/-! ## 7. Recursive form, gcd_hw shapes, numbers -/

/-- H_CTREE_LOOP, recursively (one conjunct per node, per child). -/
def CondR (lo Qhi : Path → Int) (E : Int) : Tr → Path → Prop
  | .leaf, _ => True
  | .node k cs, p => (∀ j : Fin k,
      Qhi p ≤ distL lo p + E + MaxMin lo (cs j) (j.1 :: p) + lo (j.1 :: p)) ∧
      ∀ j : Fin k, CondR lo Qhi E (cs j) (j.1 :: p)

instance condR_dec (lo Qhi : Path → Int) (E : Int) : ∀ s p, Decidable (CondR lo Qhi E s p)
  | .leaf, _ => isTrue trivial
  | .node k cs, p => by
    have := fun j : Fin k => condR_dec lo Qhi E (cs j) (j.1 :: p)
    unfold CondR; infer_instance

theorem condR_iff (lo Qhi : Path → Int) (E : Int) : ∀ s p,
    CondR lo Qhi E s p ↔ ∀ p0 k (cs : Fin k → Tr), InT s p p0 (.node k cs) → ∀ j : Fin k,
      Qhi p0 ≤ distL lo p0 + E + MaxMin lo (cs j) (j.1 :: p0) + lo (j.1 :: p0) := by
  intro s
  induction s with
  | leaf =>
    intro p
    refine ⟨fun _ p0 k cs h => ?_, fun _ => trivial⟩
    cases h
  | node k cs ih =>
    intro p
    constructor
    · intro ⟨h1, h2⟩ p0 k' cs' h
      cases h with
      | refl => exact h1
      | child j hj => exact (ih j _).mp (h2 j) p0 k' cs' hj
    · intro h
      exact ⟨h p k cs (InT.refl _ _),
        fun j => (ih j _).mpr (fun p0 k' cs' hj => h p0 k' cs' (InT.child j hj))⟩

theorem cond_iff (lo Qhi : Path → Int) (E : Int) (tr : Tr) :
    Cond lo Qhi E tr ↔ CondR lo Qhi E tr [] := (condR_iff lo Qhi E tr []).symm

/-- A node over `k` ports (`bd_ctree` N = 2, 3, 4: one bd_c2 / bd_c3 / bd_c4). -/
def lv (k : Nat) : Tr := .node k (fun _ => .leaf)

/-- `bd_ctree` N = 5 (gcd_hw: 2 bd_forks): `C2(C4(a0..a3), a4)` (the 1-wide chunk is a wire). -/
def sh5 : Tr := .node 2 (fun j => if j.1 = 0 then lv 4 else .leaf)

/-- `bd_ctree` N = 6 (gcd_hw: 1 bd_fork): `C2(C4(a0..a3), C2(a4, a5))`. -/
def sh6 : Tr := .node 2 (fun j => if j.1 = 0 then lv 4 else lv 2)

theorem wf_lv {k : Nat} (h : 2 ≤ k) : Wf (lv k) := ⟨h, fun _ => trivial⟩
theorem wf_sh5 : Wf sh5 := ⟨by decide, fun j => by
  show Wf (if j.1 = 0 then lv 4 else .leaf); split
  · exact wf_lv (by decide)
  · trivial⟩
theorem wf_sh6 : Wf sh6 := ⟨by decide, fun j => by
  show Wf (if j.1 = 0 then lv 4 else lv 2); split
  · exact wf_lv (by decide)
  · exact wf_lv (by decide)⟩

/-- **`sh6_cond_iff`**: for the N = 6 tree with UNIFORM read lo `l` (wire +
site pin + arc, every edge) and uniform loop hi `Qh`, H_CTREE_LOOP is
`Qh ≤ E + 2 l` (root and both inner nodes give the same bound). -/
theorem sh6_cond_iff (l Qh E : Int) :
    Cond (fun _ => l) (fun _ => Qh) E sh6 ↔ Qh ≤ E + 2 * l := by
  rw [cond_iff]
  constructor
  · intro ⟨h1, _⟩
    have : Qh ≤ distL (fun _ => l) [] + E + MaxMin (fun _ => l) (lv 2) [1] + l := h1 ⟨1, by decide⟩
    simp only [lv, MaxMin, fmx, distL] at this
    omega
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · show Qh ≤ 0 + E + MaxMin (fun _ => l) (if j.1 = 0 then lv 4 else lv 2) (j.1 :: []) + l
      split
      · simp only [lv, MaxMin, fmx]; omega
      · simp only [lv, MaxMin, fmx]; omega
    · show CondR (fun _ => l) (fun _ => Qh) E (if j.1 = 0 then lv 4 else lv 2) (j.1 :: [])
      split
      · exact ⟨fun _ => by simp only [MaxMin, distL]; omega, fun _ => trivial⟩
      · exact ⟨fun _ => by simp only [MaxMin, distL]; omega, fun _ => trivial⟩

/-- **`old_imply_new`**: per node, the old `bd_ctree.node_fork` static form
(CTreeTimed.StaticOK, lumped: `Spread n + fmax n ≤ D n + E`, rewritten with
`Qhi = fmax + lmax`, `Spread ≥ lmax - lmin`) implies H_CTREE_LOOP for every
child, since `lo(c -> n) ≥ lmin` and `MaxMin ≥ 0`. Nothing that passed the
old row fails the new one. -/
theorem old_imply_new (fmax lmax lmin Spread D E MM loc : Int) (hS : lmax - lmin ≤ Spread)
    (hMM : 0 ≤ MM) (hloc : lmin ≤ loc) (old : Spread + fmax ≤ D + E) :
    fmax + lmax ≤ D + E + MM + loc := by omega

/-- **`sh6_numbers`**: N = 6, prjxray-shaped box numbers (ps): every read lo
145 (wire 100 + O6 arc FAST_MIN 45), every loop hi 424 (feedback wire 300 +
arc SLOW_MAX 124), `E = 300`. H_CTREE_LOOP holds (424 ≤ 590), so by
`tree_suff` every run in the box is glitch-free. The old row FAILS at the
inner C4 with port wires [100, 400]: Spread = 79 + 300 = 379, `379 + 300 > 145 + 300`. -/
theorem sh6_numbers :
    TreeOK (fun _ => 145) (fun _ => 524) (fun _ => 95) (fun _ => 424) 300 sh6 ∧
    ¬ ((79 + 300 : Int) + 300 ≤ 145 + 300) :=
  ⟨tree_suff wf_sh6 (fun _ => by decide) (fun _ => by decide) (by decide)
    ((sh6_cond_iff 145 424 300).mpr (by decide)), by decide⟩

/-- **`sh6_glitch`**: the same tree with the loop 1 ps over (591 > 300 + 290):
some run in the box glitches (`tree_needs`, its counter-trace). -/
theorem sh6_glitch :
    ¬ TreeOK (fun _ => 145) (fun _ => 524) (fun _ => 95) (fun _ => 591) 300 sh6 := by
  intro h
  have := (sh6_cond_iff 145 591 300).mp
    (tree_needs wf_sh6 (fun _ => by decide) (fun _ => by decide) (fun _ => by decide)
      (fun _ => by decide) (by decide) h)
  omega

/-- **`nonvacuous`**: the hypotheses of `TreeOK` are satisfiable for every
tree: the witness schedule of `tree_needs` (constant maps at lo, any
`Qlo ≥ 1`) meets H_LEAF and H_ACK, so TreeOK is not vacuously true. Shown on
sh6 at the numbers of `sh6_numbers`: an env exists and a run exists. -/
theorem nonvacuous : ∃ (rd : Path → Rd) (σ : Path → Nat → Int),
    (∀ q, Mono (rd q)) ∧ (∀ q, 145 ≤ (rd q).lo ∧ (rd q).hi ≤ 524) ∧
    (∀ q, InT sh6 [] q .leaf → LeafOK σ q) ∧ HAck rd σ 300 sh6 ∧
    ∃ O, Sol rd σ (fun _ => Rd.const 424) sh6 [] O := by
  refine ⟨fun _ => Rd.const 145, fun _ k => 2000 * (k : Int), fun _ => const_mono _,
    fun _ => ⟨Int.le_refl _, show (145 : Int) ≤ 524 by decide⟩,
    fun _ _ => ⟨fun k => show 2000 * ((k : Nat) : Int) < 2000 * ((k + 1 : Nat) : Int) by omega,
      show (0 : Int) ≤ 2000 * ((0 : Nat) : Int) by decide⟩, ?_,
    _, sol_rv (fun _ u => by show u - 424 ≤ u - 1; omega) sh6 []⟩
  intro q _ k
  have := up_bound (lo := fun _ => 145) (fun q x => by rw [rho_const]; exact Int.le_refl _)
    (fun _ => 2000 * (k : Int)) (2000 * (k : Int)) sh6 [] wf_sh6 (fun _ _ => Int.le_refl _)
  have e : MaxMin (fun _ => 145) sh6 [] = 290 := by
    simp only [sh6, lv, MaxMin, fmx]; decide
  show Tf (fun _ => Rd.const 145) (fun _ => 2000 * (k : Int)) sh6 [] + 300 ≤
    2000 * ((k + 1 : Nat) : Int)
  omega

end Audit.P8.CTreeMut
