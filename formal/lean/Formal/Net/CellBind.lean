import Formal.Net.Prelim

/-!
# Probe C-O4 (1/4): generic lemmas for binding the Ops gate models to per-gate SI netlists

The Ops models (`Fork`, `Join`, `Mux`, `Link`, ...) describe each operator by a few LUMPED
SI nodes ("`o` moves only to `F` of the inputs one tick earlier"). The generated netlists
(`Formal/Gen/Cells.lean`) have more nodes: delay chains (`bd_delay`, `bd_delay_gated`,
bd_link's `rdly`/`uack`), C-element trees (`bd_ctree`, N ≥ 5), an OR anchor in front of a
chain. This file proves when a group of per-gate SI nodes behaves like ONE lumped node.

Per-gate model (the "SI model"): every node `x k` (a LUT output or a route) moves only to its
function of the PREVIOUS tick's node values (`NetSI`). Delays are unbounded; pending
excitations are cancelled if the inputs revert (that is what "function of the previous
tick" means).

* `mono_net`: a network of nodes with monotone, constant-preserving functions (buffers, AND /
  OR side taps, C-elements = majority) behind ONE input `x 0`: if the input changes only
  when EVERY node of the network already shows it (**H_CHAIN_SETTLED**, `Settled`), then
  every node moves only to the input's previous value. So the output is the lumped SI node.
* `buf_settled`: for a chain of plain buffers (`bd_delay` FASTFALL = FASTRISE = 0, routes)
  the weaker END-ONLY persistence (`PersistEnd`: the input changes only when the chain's
  end shows it; this is what the four-phase protocol gives) implies H_CHAIN_SETTLED.
* For FASTFALL / FASTRISE chains (side taps) end-only persistence is NOT enough: see
  `CellBindChain.lean` (`fastfall_hazard`), a 3-stage counterexample run.
* `cel_inv`: a C-element node `m` over leaves, read by a downstream node `r` that moves
  only to `m`'s value (**R1**), with leaves that move only while they equal `r`
  (**H_LEAF_PERSIST**): whenever `m` differs from `r`, every leaf equals `m`. This is what
  lets a two-level C-tree (bd_fork N ≥ 5) or a C-element followed by a delay chain (a
  compute unit's join) satisfy the lumped `Fork.cel` / `Join.cel` fields.
* `or_inv`: the same for an OR node (bd_mux's `uor` in front of its request delay).
-/

namespace Formal.Net.CellBind
open Formal.Net

/-! ## 1. Monotone networks with a settled input -/

/-- `G` is monotone in the node values with index `≤ n`. -/
def MonoOn (n : Nat) (G : (Nat → Bool) → Bool) : Prop :=
  ∀ f g : Nat → Bool, (∀ j, j ≤ n → f j = true → g j = true) → G f = true → G g = true

/-- `G` returns `v` when every node `≤ n` shows `v`. -/
def IdemOn (n : Nat) (G : (Nat → Bool) → Bool) : Prop :=
  ∀ (f : Nat → Bool) (v : Bool), (∀ j, j ≤ n → f j = v) → G f = v

/-- Per-gate SI: node `k` (1 ≤ k ≤ n) moves only to `G k` of the previous tick's snapshot. -/
def NetSI (n : Nat) (G : Nat → (Nat → Bool) → Bool) (x : Nat → Trace) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → ∀ t, x k (t + 1) ≠ x k t → x k (t + 1) = G k (fun j => x j t)

/-- **H_CHAIN_SETTLED**: the input `x 0` changes only when every node shows it. -/
def Settled (n : Nat) (x : Nat → Trace) : Prop :=
  ∀ t, x 0 (t + 1) ≠ x 0 t → ∀ j, j ≤ n → x j t = x 0 t

/-- End-only persistence: the input changes only when the last node shows it. -/
def PersistEnd (n : Nat) (x : Nat → Trace) : Prop :=
  ∀ t, x 0 (t + 1) ≠ x 0 t → x n t = x 0 t

theorem bool_ne {a b c : Bool} (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem bool_ne' {a b c : Bool} (h1 : a ≠ b) (h2 : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

section mono
variable {n : Nat} {G : Nat → (Nat → Bool) → Bool} {x : Nat → Trace}

/-- Invariant: a node that already shows the input's value is not excited away from it. -/
def QInv (n : Nat) (G : Nat → (Nat → Bool) → Bool) (x : Nat → Trace) (t : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → x k t = x 0 t → G k (fun j => x j t) = x 0 t

theorem moves_to (hN : NetSI n G x) {t : Nat} (hQ : QInv n G x t) {k : Nat} (h1 : 1 ≤ k) (hn : k ≤ n)
    (hm : x k (t + 1) ≠ x k t) : x k (t + 1) = x 0 t := by
  have e := hN k h1 hn t hm
  by_cases hk : x k t = x 0 t
  · exact absurd ((e.trans (hQ k h1 hn hk)).trans hk.symm) hm
  · exact bool_ne hm (Ne.symm hk)

theorem closer (hN : NetSI n G x) {t : Nat} (hQ : QInv n G x t) (h0 : x 0 (t + 1) = x 0 t) :
    ∀ j, j ≤ n → x j t = x 0 t → x j (t + 1) = x 0 t := by
  intro j hj he
  by_cases hj0 : j = 0
  · subst hj0; exact h0
  · by_cases hm : x j (t + 1) = x j t
    · rw [hm, he]
    · exact moves_to hN hQ (by omega) hj hm

theorem mono_step (hG : ∀ k, 1 ≤ k → k ≤ n → MonoOn n (G k)) {t : Nat} {k : Nat} (h1 : 1 ≤ k) (hn : k ≤ n)
    (hc : ∀ j, j ≤ n → x j t = x 0 t → x j (t + 1) = x 0 t)
    (he : G k (fun j => x j t) = x 0 t) : G k (fun j => x j (t + 1)) = x 0 t := by
  cases hv : x 0 t
  · -- v = false: contrapositive of monotonicity
    rw [hv] at he hc
    cases hg : G k (fun j => x j (t + 1))
    · rfl
    · have := hG k h1 hn (fun j => x j (t + 1)) (fun j => x j t) (by
        intro j hj hjt
        cases hx : x j t
        · rw [hc j hj hx] at hjt; exact absurd hjt (by simp)
        · rfl) hg
      rw [he] at this; exact absurd this (by simp)
  · rw [hv] at he hc
    exact hG k h1 hn (fun j => x j t) (fun j => x j (t + 1)) (fun j hj hjt => hc j hj hjt) he

theorem qinv_all (hG : ∀ k, 1 ≤ k → k ≤ n → MonoOn n (G k) ∧ IdemOn n (G k)) (hN : NetSI n G x)
    (hS : Settled n x) (hI : ∀ j, j ≤ n → x j 0 = x 0 0) : ∀ t, QInv n G x t := by
  intro t
  induction t with
  | zero => intro k h1 hn _; exact (hG k h1 hn).2 _ _ hI
  | succ t ih =>
    intro k h1 hn hk
    by_cases h0 : x 0 (t + 1) = x 0 t
    · -- input steady: the node got to `v` either earlier or by moving now
      have hc := closer hN ih h0
      have he : G k (fun j => x j t) = x 0 t := by
        by_cases hm : x k (t + 1) = x k t
        · exact ih k h1 hn (by rw [← hm, hk, h0])
        · have e := hN k h1 hn t hm; rw [← e, hk, h0]
      rw [h0]; exact mono_step (fun k h1 hn => (hG k h1 hn).1) h1 hn hc he
    · -- input moved: every node showed the old value, so none shows the new one
      exfalso
      have hs := hS t h0
      have hkt : x k (t + 1) = x 0 t := by
        by_cases hm : x k (t + 1) = x k t
        · rw [hm]; exact hs k hn
        · have e := hN k h1 hn t hm
          rw [e]; exact (hG k h1 hn).2 _ _ hs
      exact h0 (hk.symm.trans hkt)

/-- **Monotone network, lumped.** Every node moves only to the input's previous value. -/
theorem mono_net (hG : ∀ k, 1 ≤ k → k ≤ n → MonoOn n (G k) ∧ IdemOn n (G k)) (hN : NetSI n G x)
    (hS : Settled n x) (hI : ∀ j, j ≤ n → x j 0 = x 0 0) :
    ∀ k, 1 ≤ k → k ≤ n → ∀ t, x k (t + 1) ≠ x k t → x k (t + 1) = x 0 t := by
  intro k h1 hn t hm
  have hQ := qinv_all hG hN hS hI t
  by_cases h0 : x 0 (t + 1) = x 0 t
  · exact moves_to hN hQ h1 hn hm
  · have hs := hS t h0
    have e := hN k h1 hn t hm
    rw [e]; exact (hG k h1 hn).2 _ _ hs

end mono

/-! ## 2. Plain buffer chains: end-only persistence suffices -/

/-- A buffer chain: node `k+1` copies node `k`. -/
def bufG (k : Nat) (f : Nat → Bool) : Bool := f (k - 1)

theorem bufG_mono (n k : Nat) (h1 : 1 ≤ k) (hn : k ≤ n) : MonoOn n (bufG k) ∧ IdemOn n (bufG k) :=
  ⟨fun f g h hf => h (k - 1) (by omega) hf, fun f v h => h (k - 1) (by omega)⟩

/-- Front invariant: once a node disagrees with the input, every later node does. -/
def Front (n : Nat) (x : Nat → Trace) (t : Nat) : Prop :=
  ∀ j k, j ≤ k → k ≤ n → x j t ≠ x 0 t → x k t ≠ x 0 t

theorem front_all {n : Nat} {x : Nat → Trace} (hN : NetSI n bufG x) (hP : PersistEnd n x)
    (hI : ∀ j, j ≤ n → x j 0 = x 0 0) : ∀ t, Front n x t := by
  intro t
  induction t with
  | zero => intro j k _ _ h; exact absurd (hI j (by omega)) h
  | succ t ih =>
    intro j k hjk hkn hj
    by_cases h0 : x 0 (t + 1) = x 0 t
    · -- steady input `v`
      rw [h0] at hj ⊢
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · exact absurd h0 hj
        · exact h
      -- some node `j' ≤ j` disagreed at `t`
      have hj' : x (j - 1) t ≠ x 0 t ∨ x j t ≠ x 0 t := by
        by_cases hm : x j (t + 1) = x j t
        · exact Or.inr (hm ▸ hj)
        · have e := hN j hj1 (by omega) t hm
          exact Or.inl (by simp only [bufG] at e; rw [← e]; exact hj)
      by_cases hkj : k = j
      · subst hkj; exact hj
      · have hk1 : x k t ≠ x 0 t := by
          rcases hj' with h | h
          · exact ih (j - 1) k (by omega) hkn h
          · exact ih j k hjk hkn h
        have hk2 : x (k - 1) t ≠ x 0 t := by
          rcases hj' with h | h
          · exact ih (j - 1) (k - 1) (by omega) (by omega) h
          · exact ih j (k - 1) (by omega) (by omega) h
        by_cases hm : x k (t + 1) = x k t
        · rw [hm]; exact hk1
        · have e := hN k (by omega) hkn t hm
          simp only [bufG] at e; rw [e]; exact hk2
    · -- the input moved: the chain was settled at the old value
      have hall : ∀ i, i ≤ n → x i t = x 0 t := by
        intro i hi
        apply Classical.byContradiction; intro hne
        exact ih i n hi (Nat.le_refl n) hne (hP t h0)
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · have : j = 0 := by omega
          subst this; exact absurd rfl hj
        · exact h
      have : x k (t + 1) = x 0 t := by
        by_cases hm : x k (t + 1) = x k t
        · rw [hm]; exact hall k hkn
        · have e := hN k hk1 hkn t hm
          simp only [bufG] at e; rw [e]; exact hall (k - 1) (by omega)
      rw [this]; exact Ne.symm h0

/-- **Buffer chain: end-only persistence gives H_CHAIN_SETTLED.** -/
theorem buf_settled {n : Nat} {x : Nat → Trace} (hN : NetSI n bufG x) (hP : PersistEnd n x)
    (hI : ∀ j, j ≤ n → x j 0 = x 0 0) : Settled n x := by
  intro t h0 j hj
  apply Classical.byContradiction; intro hne
  exact front_all hN hP hI t j n hj (Nat.le_refl n) hne (hP t h0)

/-- **Buffer chain, lumped** (end-only persistence). -/
theorem buf_chain {n : Nat} {x : Nat → Trace} (hN : NetSI n bufG x) (hP : PersistEnd n x)
    (hI : ∀ j, j ≤ n → x j 0 = x 0 0) :
    ∀ t, x n (t + 1) ≠ x n t → 1 ≤ n → x n (t + 1) = x 0 t := fun t hm h1 =>
  mono_net (fun k h1 hn => bufG_mono n k h1 hn) hN (buf_settled hN hP hI) hI n h1 (Nat.le_refl n) t hm

/-! ## 3. A C-element node behind a lumped downstream node -/

/-- **`cel_inv`.** `m` is a C-element over `leaves` (it moves only when every leaf shows
its new value); `r` moves only to `m`'s previous value (R1); every leaf moves only while it
equals `r` (H_LEAF_PERSIST); `m 0 = r 0`. Then whenever `m ≠ r`, every leaf equals `m`. -/
theorem cel_inv {m r : Trace} {leaves : List Trace}
    (hC : ∀ t, m (t + 1) ≠ m t → ∀ l ∈ leaves, l t = m (t + 1))
    (hR : ∀ t, r (t + 1) ≠ r t → r (t + 1) = m t)
    (hL : ∀ l ∈ leaves, ∀ t, l (t + 1) ≠ l t → l t = r t)
    (h0 : m 0 = r 0) :
    ∀ t, m t ≠ r t → ∀ l ∈ leaves, l t = m t := by
  intro t
  induction t with
  | zero => intro h; exact absurd h0 h
  | succ t ih =>
    intro hne l hl
    by_cases hlm : l (t + 1) = l t
    · -- the leaf is steady
      rw [hlm]
      by_cases hmm : m (t + 1) = m t
      · rw [hmm]
        by_cases hmr : m t = r t
        · -- then `r` moved, to `m t`: contradiction
          exfalso
          by_cases hrr : r (t + 1) = r t
          · exact hne (by rw [hmm, hrr, hmr])
          · exact hne (by rw [hmm, hR t hrr])
        · exact ih hmr l hl
      · exact hC t hmm l hl
    · -- the leaf moves, so it equalled `r t`
      exfalso
      have hlr := hL l hl t hlm
      by_cases hmm : m (t + 1) = m t
      · by_cases hmr : m t = r t
        · by_cases hrr : r (t + 1) = r t
          · exact hne (by rw [hmm, hrr, hmr])
          · exact hne (by rw [hmm, hR t hrr])
        · exact hmr ((ih hmr l hl).symm.trans hlr)
      · have hc := hC t hmm l hl
        -- `m` moved to `l t = r t`; then `m t ≠ r t`, so `l t = m t` by `ih`
        have hmr : m t ≠ r t := fun h => hmm (by rw [← hc, hlr, h])
        exact hmm (by rw [← hc, ih hmr l hl])

/-- The lumped C-element field from `cel_inv`: when `r` moves, every leaf already shows
`r`'s new value. -/
theorem cel_lumped {m r : Trace} {leaves : List Trace}
    (hC : ∀ t, m (t + 1) ≠ m t → ∀ l ∈ leaves, l t = m (t + 1))
    (hR : ∀ t, r (t + 1) ≠ r t → r (t + 1) = m t)
    (hL : ∀ l ∈ leaves, ∀ t, l (t + 1) ≠ l t → l t = r t)
    (h0 : m 0 = r 0) :
    ∀ t, r (t + 1) ≠ r t → ∀ l ∈ leaves, l t = r (t + 1) := by
  intro t hr l hl
  have e := hR t hr
  have hmr : m t ≠ r t := fun h => hr (by rw [e, h])
  rw [cel_inv hC hR hL h0 t hmr l hl, e]

/-! ## 4. An OR node behind a lumped downstream node (bd_mux's `uor`) -/

/-- **`or_inv`.** `e` moves only to the OR of the leaves; `r` moves only to `e`'s previous
value; leaves move only while equal to `r`; `e 0 = r 0`. Then whenever `e ≠ r`, the OR of
the leaves equals `e`. -/
theorem or_inv {e r : Trace} {leaves : List Trace}
    (hE : ∀ t, e (t + 1) ≠ e t → e (t + 1) = leaves.any (fun l => l t))
    (hR : ∀ t, r (t + 1) ≠ r t → r (t + 1) = e t)
    (hL : ∀ l ∈ leaves, ∀ t, l (t + 1) ≠ l t → l t = r t)
    (h0 : e 0 = r 0) :
    ∀ t, e t ≠ r t → leaves.any (fun l => l t) = e t := by
  intro t
  induction t with
  | zero => intro h; exact absurd h0 h
  | succ t ih =>
    intro hne
    -- `r` did not move: otherwise it moved to `e t`, and `e` is then steady or contradicts
    have hstep : ∀ l ∈ leaves, l t ≠ r t → l (t + 1) = l t := fun l hl h =>
      Classical.byContradiction fun hm => h (hL l hl t hm)
    have key : e t = r t → e (t + 1) ≠ e t := by
      intro her hee
      apply hne
      by_cases hrr : r (t + 1) = r t
      · rw [hee, hrr, her]
      · rw [hee, hR t hrr]
    by_cases hee : e (t + 1) = e t
    · have her : e t ≠ r t := fun h => key h hee
      have hor := ih her
      rw [hee]
      -- leaves that equal `e t` (≠ r t) are steady; moving leaves go from `r t` to `e t`
      cases hv : e t
      · rw [hv] at hor
        apply List.any_eq_false.mpr
        intro l hl
        have hlt : l t = false := by
          have := List.any_eq_false.mp hor l hl; simpa using this
        have hlr : l t ≠ r t := by rw [hlt]; intro h; apply her; rw [hv, h]
        rw [hstep l hl hlr, hlt]; simp
      · rw [hv] at hor
        obtain ⟨l, hl, hlt⟩ := List.any_eq_true.mp hor
        apply List.any_eq_true.mpr
        refine ⟨l, hl, ?_⟩
        have hlt' : l t = true := by simpa using hlt
        have hlr : l t ≠ r t := by rw [hlt']; intro h; apply her; rw [hv, h]
        rw [hstep l hl hlr]; exact hlt
    · -- `e` moved at `t`, to the OR at `t`
      have e1 := hE t hee
      have her : e t = r t := by
        apply Classical.byContradiction; intro her
        exact hee (by rw [e1, ih her])
      rw [e1]
      -- every leaf that moves equals `r t = e t = ¬ OR`; show the OR is unchanged
      cases hv : leaves.any (fun l => l t)
      · apply List.any_eq_false.mpr
        intro l hl
        have hlt : l t = false := by
          have := List.any_eq_false.mp hv l hl; simpa using this
        have : e t = true := by
          have := hee; rw [e1, hv] at this; cases h : e t <;> simp_all
        have hlr : l t ≠ r t := by rw [hlt, ← her, this]; simp
        rw [hstep l hl hlr, hlt]; simp
      · obtain ⟨l, hl, hlt⟩ := List.any_eq_true.mp hv
        apply List.any_eq_true.mpr
        refine ⟨l, hl, ?_⟩
        have hlt' : l t = true := by simpa using hlt
        have : e t = false := by
          have := hee; rw [e1, hv] at this; cases h : e t <;> simp_all
        have hlr : l t ≠ r t := by rw [hlt', ← her, this]; simp
        rw [hstep l hl hlr]; exact hlt

/-- The lumped OR field: when `r` moves, it moves to the OR of the leaves. -/
theorem or_lumped {e r : Trace} {leaves : List Trace}
    (hE : ∀ t, e (t + 1) ≠ e t → e (t + 1) = leaves.any (fun l => l t))
    (hR : ∀ t, r (t + 1) ≠ r t → r (t + 1) = e t)
    (hL : ∀ l ∈ leaves, ∀ t, l (t + 1) ≠ l t → l t = r t)
    (h0 : e 0 = r 0) :
    ∀ t, r (t + 1) ≠ r t → r (t + 1) = leaves.any (fun l => l t) := by
  intro t hr
  have e1 := hR t hr
  have her : e t ≠ r t := fun h => hr (by rw [e1, h])
  rw [e1, or_inv hE hR hL h0 t her]

/-! ## 5. A zero-delay wire does not satisfy the Ops wire field -/

/-- The Ops wire fields (`Fork.wire`, `Join.wire`, `Sink.wire`, `Mux.ca`, `Link.H_*_DI`)
read "`o` moves only to `i`'s value one tick EARLIER". In the generated netlists many of
these wires are literally the same net (`req_out[k] = req`, `ack_out[k] = ack`, `bd_snk`'s
`ack = req`, bd_link with `DELAY = 0`). The identity wire violates the field as soon as `i`
moves: so every such wire needs a route of at least one tick (**H_WIRE_DI**), it is not a
generalisation that could be dropped. -/
theorem ident_wire_breaks :
    ¬ (∀ (i : Trace) (t : Nat), i (t + 1) ≠ i t → i (t + 1) = i t) := by
  intro h
  have := h (fun t => decide (t = 1)) 0 (by decide)
  exact absurd this (by decide)

end Formal.Net.CellBind
