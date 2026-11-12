import Formal.Net.RingCheck

/-!
# Closed walks vs simple cycles (probe C-9b)

CLAUDE.md states the ring rule per SIMPLE cycle; `RingCheck.check_iff` is
about closed walks.  For `Nat` weights the two agree: every closed walk
contains a simple cycle (a segment between the first repeated vertex pair)
that is no heavier.  `allCyclesGe_iff_simple` proves it, and `check_iff_simple`
restates the checker's correctness against the simple-cycle rule.

Cycles here are explicit edge lists `p = [e₀, …, e_{m-1}]` with
`eᵢ.dst = eᵢ₊₁.src` and `e_{m-1}.dst = e₀.src`; *simple* = the sources
`eᵢ.src` are pairwise distinct (so every vertex is visited once).
-/

namespace Formal.Net.RingCheck

def weight (p : List Edge) : Nat := (p.map Edge.w).sum

def IsChain (p : List Edge) : Prop :=
  ∀ i (h : i + 1 < p.length), (p[i]'(by omega)).dst = (p[i+1]).src

structure IsCycle (g : Graph) (p : List Edge) : Prop where
  ne : 0 < p.length
  mem : ∀ e ∈ p, e ∈ g
  chain : IsChain p
  closed : (p[p.length - 1]'(by omega)).dst = (p[0]'ne).src

def IsSimple (p : List Edge) : Prop :=
  ∀ i j (hi : i < p.length) (hj : j < p.length), i < j → (p[i]).src ≠ (p[j]).src

/-- The rule as CLAUDE.md states it: every simple cycle carries ≥ `k` stages. -/
def AllSimpleCyclesGe (g : Graph) (k : Nat) : Prop :=
  ∀ p, IsCycle g p → IsSimple p → k ≤ weight p

theorem weight_cons (e : Edge) (p : List Edge) : weight (e :: p) = e.w + weight p := by
  simp [weight]

theorem weight_append (p q : List Edge) : weight (p ++ q) = weight p + weight q := by
  simp [weight, List.sum_append]

theorem weight_take_le (m : Nat) (p : List Edge) : weight (p.take m) ≤ weight p := by
  have := weight_append (p.take m) (p.drop m)
  rw [List.take_append_drop] at this; omega

theorem weight_drop_le (m : Nat) (p : List Edge) : weight (p.drop m) ≤ weight p := by
  have := weight_append (p.take m) (p.drop m)
  rw [List.take_append_drop] at this; omega

theorem walk_cons {g : Graph} {s v c : Nat} {e : Edge} (hw : Walk g s v c) (he : e ∈ g)
    (hd : e.dst = s) : Walk g e.src v (e.w + c) := by
  induction hw with
  | @edge e' he' hsrc =>
    have h0 : Walk g e.src e.dst e.w := Walk.edge he rfl
    rw [hd, ← hsrc] at h0
    exact Walk.snoc h0 he'
  | @snoc c e' _ he' ih =>
    rw [← Nat.add_assoc]; exact Walk.snoc ih he'

/-- A chain of edges of `g` is a walk from its first source to its last target. -/
theorem walk_of_chain {g : Graph} : ∀ (p : List Edge) (hne : 0 < p.length),
    (∀ e ∈ p, e ∈ g) → IsChain p →
    Walk g (p[0]'hne).src (p[p.length - 1]'(by omega)).dst (weight p)
  | [], hne, _, _ => absurd hne (Nat.lt_irrefl _)
  | [e], _, hm, _ => by
    simpa [weight] using Walk.edge (g := g) (hm e (by simp)) rfl
  | e :: f :: q, _, hm, hc => by
    have ih := walk_of_chain (f :: q) (by simp) (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      (fun i h => hc (i + 1) (by simp at h ⊢; omega))
    have hd : e.dst = f.src := hc 0 (by simp)
    have := walk_cons ih (hm e (by simp)) (by simpa using hd)
    rw [weight_cons]
    simpa using this

/-- Every walk is a chain of edges of `g`. -/
theorem chain_of_walk {g : Graph} {s v c : Nat} (hw : Walk g s v c) :
    ∃ p : List Edge, ∃ hne : 0 < p.length, (∀ e ∈ p, e ∈ g) ∧ IsChain p ∧
      (p[0]'hne).src = s ∧ (p[p.length - 1]'(by omega)).dst = v ∧ weight p = c := by
  induction hw with
  | @edge e he hsrc =>
    exact ⟨[e], by simp, by simpa using he, fun i h => by simp at h, hsrc, rfl, by simp [weight]⟩
  | @snoc c e _ he ih =>
    obtain ⟨p, hne, hm, hc, h0, hl, hwt⟩ := ih
    refine ⟨p ++ [e], by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; simp at hx; rcases hx with hx | hx
      · exact hm x hx
      · rw [hx]; exact he
    · intro i h
      simp only [List.length_append, List.length_singleton] at h
      by_cases hi : i + 1 < p.length
      · rw [List.getElem_append_left (by omega), List.getElem_append_left hi]
        exact hc i hi
      · have hi' : i = p.length - 1 := by omega
        subst hi'
        rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
        simp only [List.getElem_singleton]
        rw [hl]
    · rw [List.getElem_append_left hne]; exact h0
    · simp
    · rw [weight_append, hwt]; simp [weight]

/-- Every cycle contains a simple cycle that is no heavier. -/
theorem simple_sub {g : Graph} : ∀ (p : List Edge), IsCycle g p →
    ∃ q, IsCycle g q ∧ IsSimple q ∧ weight q ≤ weight p := by
  intro p
  induction h : p.length using Nat.strongRecOn generalizing p with
  | _ n ih =>
  intro hp
  by_cases hs : IsSimple p
  · exact ⟨p, hp, hs, Nat.le_refl _⟩
  · -- a repeated source p[i].src = p[j].src, i < j: cut out p[i..j)
    have : ∃ i j, ∃ (hi : i < p.length) (hj : j < p.length), i < j ∧ (p[i]).src = (p[j]).src := by
      apply Classical.byContradiction; intro hn
      exact hs (fun i j hi hj hij heq => hn ⟨i, j, hi, hj, hij, heq⟩)
    obtain ⟨i, j, hi, hj, hij, heq⟩ := this
    let q := (p.drop i).take (j - i)
    have hql : q.length = j - i := by simp [q]; omega
    have hqget : ∀ t (ht : t < q.length), q[t] = p[i + t]'(by omega) := by
      intro t ht; simp [q]
    have hq : IsCycle g q := by
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro x hx; exact hp.mem x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      · intro t ht
        rw [hqget t (by omega), hqget (t + 1) ht]
        exact hp.chain (i + t) (by omega)
      · rw [hqget _ (by omega), hqget 0 (by omega)]
        have hc := hp.chain (i + (q.length - 1)) (by omega)
        have e1 : i + (q.length - 1) + 1 = j := by omega
        simp only [e1] at hc
        rw [hc]; simp only [Nat.add_zero]; exact heq.symm
    have hlt : q.length < n := by omega
    obtain ⟨r, hr, hrs, hrw⟩ := ih q.length hlt q rfl hq
    exact ⟨r, hr, hrs, Nat.le_trans hrw
      (Nat.le_trans (weight_take_le _ _) (weight_drop_le _ _))⟩

theorem allCyclesGe_iff_simple (g : Graph) (k : Nat) :
    AllCyclesGe g k ↔ AllSimpleCyclesGe g k := by
  constructor
  · intro h p hp _
    have hw := walk_of_chain p hp.ne hp.mem hp.chain
    rw [hp.closed] at hw
    exact h _ _ hw
  · intro h s c hw
    obtain ⟨p, hne, hm, hc, h0, hl, hwt⟩ := chain_of_walk hw
    have hp : IsCycle g p := ⟨hne, hm, hc, by rw [hl, h0]⟩
    obtain ⟨q, hq, hqs, hqw⟩ := simple_sub p hp
    have := h q hq hqs; omega

/-- **The checker decides the CLAUDE.md rule exactly**: `check g k` iff every
simple cycle of `g` carries at least `k` storage stages. -/
theorem check_iff_simple (g : Graph) (k : Nat) :
    check g k = true ↔ AllSimpleCyclesGe g k :=
  (check_iff g k).trans (allCyclesGe_iff_simple g k)

end Formal.Net.RingCheck
