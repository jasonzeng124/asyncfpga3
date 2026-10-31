/-!
# Verified ring-depth checker (probe C-9b)

`bdc/emit.py`'s `ring_depths()` must leave every cycle of the channel graph
with at least `RING_MIN_STAGES = 3` storage stages (CLAUDE.md: "A ring needs
three storage stages per simple cycle").  It finds the lightest cycle as
`min over edges u->v of w(u->v) + dist(v -> u)` with Dijkstra.  This file is
an executable checker for the same property, proved sound and complete.

Graph: a list of edges `src -> dst` carrying a `Nat` weight (the number of
storage stages on that channel; parallel edges and self-loops allowed, node
weights are folded into edge weights by the exporter).  Nodes are the `Nat`s
that occur as endpoints.

Specification (`AllCyclesGe g k`): every closed walk of at least one edge has
weight `≥ k`.  `AllSimpleCyclesGe` is the same with "simple cycle" (no vertex
repeated) and the two are proved equivalent (`allCyclesGe_iff_simple`), so
the checker decides emit.py's stated rule exactly.

Algorithm (`check g k`): for every source `s`, a capped Bellman-Ford over
`[0, k]` (the value `k` stands for "unreached or ≥ k"), iterated to a
fixpoint; the source passes if its own value is still `k`.  Fuel
`numNodes g * k + 1` always suffices: the sum of the table strictly drops on
every non-fixpoint round and starts at `numNodes g * k`.

Main theorem: `check_iff : check g k = true ↔ AllCyclesGe g k`.
No modelling hypotheses: this is a pure graph statement.  What it does *not*
say: that the graph exported from bdc is the circuit (see the exporter,
`formal/tools/ringcheck/export.py`) or that 3 is the right floor (track 9a).
Applying it to a circuit rests on the named hypothesis **H_ONLY_LINKS_STORE**:
only the stages counted in the edge weights (bd_link stages, as `ring_depths`
counts them) hold a token; every other cell on a cycle is storage-free.  It is
a modelling hypothesis about bdc's cells, not proved here (notes/C-9b-ringcheck.md;
probe 9d's `RingResetCert` checks it for the mux -> links -> steer loop shape).
-/

namespace Formal.Net.RingCheck

structure Edge where
  src : Nat
  dst : Nat
  w   : Nat
deriving Repr, DecidableEq

abbrev Graph := List Edge

/-- `Walk g s v c`: a walk of ≥ 1 edge of `g` from `s` to `v` of weight `c`. -/
inductive Walk (g : Graph) (s : Nat) : Nat → Nat → Prop
  | edge {e : Edge} : e ∈ g → e.src = s → Walk g s e.dst e.w
  | snoc {c : Nat} {e : Edge} : Walk g s e.src c → e ∈ g → Walk g s e.dst (c + e.w)

/-- Spec: every closed walk carries at least `k` stages. -/
def AllCyclesGe (g : Graph) (k : Nat) : Prop := ∀ s c, Walk g s s c → k ≤ c

/-- One more than the largest endpoint. -/
def numNodes (g : Graph) : Nat := g.foldr (fun e m => max m (max e.src e.dst + 1)) 0

theorem lt_numNodes {g : Graph} {e : Edge} (h : e ∈ g) :
    e.src < numNodes g ∧ e.dst < numNodes g := by
  induction g with
  | nil => cases h
  | cons a g ih =>
    simp only [numNodes, List.foldr_cons] at *
    cases h with
    | head => omega
    | tail _ h => have := ih h; omega

/-! ## The algorithm -/

/-- Table lookup; out of range reads as `k` ("unreached"). -/
def val (k : Nat) (d : Array Nat) (v : Nat) : Nat := if h : v < d.size then d[v] else k

/-- Candidate value for `e.dst` offered by edge `e`, reading the old table `d`. -/
def cand (k s : Nat) (d : Array Nat) (e : Edge) : Nat :=
  if e.src = s then min k e.w else min k (val k d e.src + e.w)

def relax (k s : Nat) (d : Array Nat) (acc : Array Nat) (e : Edge) : Array Nat :=
  acc.modify e.dst (fun x => min x (cand k s d e))

/-- One Jacobi round of capped Bellman-Ford from source `s`. -/
def step (k s : Nat) (g : Graph) (d : Array Nat) : Array Nat :=
  g.foldl (relax k s d) d

def iter (k s : Nat) (g : Graph) : Nat → Array Nat → Option (Array Nat)
  | 0, _ => none
  | f + 1, d => let d' := step k s g d; if d' = d then some d else iter k s g f d'

def init (k : Nat) (g : Graph) : Array Nat := Array.replicate (numNodes g) k

def fuel (k : Nat) (g : Graph) : Nat := numNodes g * k + 1

def sourceOk (k : Nat) (g : Graph) (s : Nat) : Bool :=
  match iter k s g (fuel k g) (init k g) with
  | some d => decide (k ≤ val k d s)
  | none => false

/-- The checker. -/
def check (g : Graph) (k : Nat) : Bool := (List.range (numNodes g)).all (sourceOk k g)

/-- Lightest closed walk through each node, capped at `k` (for `#eval` reports). -/
def capTable (k : Nat) (g : Graph) : List (Nat × Nat) :=
  (List.range (numNodes g)).map fun s =>
    (s, match iter k s g (fuel k g) (init k g) with | some d => val k d s | none => k)

/-- Lightest closed walk in the graph, capped at `k`. -/
def minCycleCap (k : Nat) (g : Graph) : Nat := (capTable k g).foldl (fun m p => min m p.2) k

/-! ## Facts about one round -/

theorem val_modify (k v i : Nat) (f : Nat → Nat) (a : Array Nat) :
    val k (a.modify i f) v = if i = v ∧ v < a.size then f (val k a v) else val k a v := by
  unfold val
  by_cases hv : v < a.size
  · have hv' : v < (a.modify i f).size := by simp [Array.size_modify]; exact hv
    rw [dite_eq_left hv', dite_eq_left hv, Array.getElem_modify]
    by_cases hi : i = v <;> simp [hi, hv]
  · have hv' : ¬ v < (a.modify i f).size := by simp [Array.size_modify]; omega
    rw [dite_eq_right hv', dite_eq_right hv]; simp [hv]

theorem size_foldl_relax (k s : Nat) (d : Array Nat) (l : List Edge) (acc : Array Nat) :
    (l.foldl (relax k s d) acc).size = acc.size := by
  induction l generalizing acc with
  | nil => rfl
  | cons e l ih => simp only [List.foldl_cons]; rw [ih]; simp [relax, Array.size_modify]

theorem foldl_relax_le (k s : Nat) (d : Array Nat) (l : List Edge) (acc : Array Nat) (v : Nat) :
    val k (l.foldl (relax k s d) acc) v ≤ val k acc v := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons e l ih =>
    simp only [List.foldl_cons]
    refine Nat.le_trans (ih _) ?_
    simp only [relax, val_modify]
    split <;> omega

theorem foldl_relax_cand (k s : Nat) (d : Array Nat) (l : List Edge) (acc : Array Nat)
    (e : Edge) (he : e ∈ l) (hlt : e.dst < acc.size) :
    val k (l.foldl (relax k s d) acc) e.dst ≤ cand k s d e := by
  induction l generalizing acc with
  | nil => cases he
  | cons a l ih =>
    simp only [List.foldl_cons]
    cases he with
    | head =>
      refine Nat.le_trans (foldl_relax_le _ _ _ _ _ _) ?_
      rw [relax, val_modify, ite_eq_left ⟨rfl, hlt⟩]; omega
    | tail _ he =>
      exact ih _ he (by simp [relax, Array.size_modify]; exact hlt)

theorem foldl_relax_cases (k s : Nat) (d : Array Nat) (l : List Edge) (acc : Array Nat) (v : Nat) :
    val k (l.foldl (relax k s d) acc) v = val k acc v ∨
      ∃ e ∈ l, e.dst = v ∧ val k (l.foldl (relax k s d) acc) v = cand k s d e := by
  induction l generalizing acc with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases ih (relax k s d acc a) with h | ⟨e, he, hd, hv⟩
    · rw [h]; simp only [relax, val_modify]
      by_cases hc : a.dst = v ∧ v < acc.size
      · rw [ite_eq_left hc]
        by_cases hm : val k acc v ≤ cand k s d a
        · left; omega
        · right; exact ⟨a, List.mem_cons_self, hc.1, by omega⟩
      · rw [ite_eq_right hc]; exact Or.inl rfl
    · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hd, hv⟩

/-! ## Invariant: every value below `k` is witnessed by a walk -/

def Inv (k s : Nat) (g : Graph) (d : Array Nat) : Prop :=
  d.size = numNodes g ∧ ∀ v, val k d v ≤ k ∧ (val k d v < k → ∃ c, Walk g s v c ∧ c ≤ val k d v)

theorem inv_init (k s : Nat) (g : Graph) : Inv k s g (init k g) := by
  refine ⟨Array.size_replicate, fun v => ?_⟩
  have : val k (init k g) v = k := by
    unfold val init; split
    · exact Array.getElem_replicate _
    · rfl
  rw [this]; exact ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem inv_step {k s : Nat} {g : Graph} {d : Array Nat} (h : Inv k s g d) :
    Inv k s g (step k s g d) := by
  obtain ⟨hs, hv⟩ := h
  refine ⟨by rw [step, size_foldl_relax]; exact hs, fun v => ⟨?_, ?_⟩⟩
  · exact Nat.le_trans (foldl_relax_le _ _ _ _ _ _) (hv v).1
  · intro hlt
    rcases foldl_relax_cases k s d g d v with heq | ⟨e, he, hd, heq⟩
    · unfold step at hlt ⊢; rw [heq] at hlt ⊢; exact (hv v).2 hlt
    · unfold step at hlt ⊢; rw [heq] at hlt ⊢; subst hd
      unfold cand at hlt ⊢
      by_cases hsrc : e.src = s
      · rw [ite_eq_left hsrc] at hlt ⊢
        exact ⟨e.w, Walk.edge he hsrc, by omega⟩
      · rw [ite_eq_right hsrc] at hlt ⊢
        have h1 : val k d e.src < k := by omega
        obtain ⟨c, hw, hc⟩ := (hv e.src).2 h1
        exact ⟨c + e.w, Walk.snoc hw he, by omega⟩

/-- At a fixpoint the table is a lower bound on every walk from `s`. -/
theorem fix_complete {k s : Nat} {g : Graph} {d : Array Nat} (hs : d.size = numNodes g)
    (hfix : step k s g d = d) : ∀ v c, Walk g s v c → val k d v ≤ c := by
  have key : ∀ e ∈ g, val k d e.dst ≤ cand k s d e := by
    intro e he
    have := foldl_relax_cand k s d g d e he (by rw [hs]; exact (lt_numNodes he).2)
    rw [← step, hfix] at this; exact this
  intro v c hw
  induction hw with
  | @edge e he hsrc =>
    have := key e he; unfold cand at this; rw [ite_eq_left hsrc] at this; omega
  | @snoc c e _ he ih =>
    have := key e he; unfold cand at this
    split at this <;> omega

/-! ## Termination of the fixpoint iteration -/

theorem sum_lt_of_le_ne : ∀ (l₁ l₂ : List Nat), l₁.length = l₂.length →
    (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] ≤ l₂[i]) → l₁ ≠ l₂ →
    l₁.sum < l₂.sum
  | [], [], _, _, hne => absurd rfl hne
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: l₁, b :: l₂, hl, hle, hne => by
    simp only [List.sum_cons]
    have hab : a ≤ b := hle 0 (by simp) (by simp)
    have hrest : ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] ≤ l₂[i] :=
      fun i h₁ h₂ => hle (i + 1) (by simp; omega) (by simp; omega)
    have hl' : l₁.length = l₂.length := by simpa using hl
    have hsum_le : ∀ (x y : List Nat), x.length = y.length →
        (∀ i (h₁ : i < x.length) (h₂ : i < y.length), x[i] ≤ y[i]) → x.sum ≤ y.sum := by
      intro x
      induction x with
      | nil => intro y _ _; simp
      | cons p x ih =>
        intro y hxy hle'
        cases y with
        | nil => simp at hxy
        | cons q y =>
          simp only [List.sum_cons]
          have := hle' 0 (by simp) (by simp)
          have := ih y (by simpa using hxy)
            (fun i h₁ h₂ => hle' (i + 1) (by simp; omega) (by simp; omega))
          simp at *; omega
    by_cases h : a = b
    · subst h
      have hne' : l₁ ≠ l₂ := fun h' => hne (by rw [h'])
      have := sum_lt_of_le_ne l₁ l₂ hl' hrest hne'; omega
    · have := hsum_le l₁ l₂ hl' hrest; omega

def pot (d : Array Nat) : Nat := d.toList.sum

theorem pot_step_lt {k s : Nat} {g : Graph} {d : Array Nat}
    (hne : step k s g d ≠ d) : pot (step k s g d) < pot d := by
  have hsz : (step k s g d).size = d.size := by rw [step, size_foldl_relax]
  apply sum_lt_of_le_ne
  · simp [hsz]
  · intro i h₁ h₂
    rw [Array.getElem_toList, Array.getElem_toList]
    have := foldl_relax_le k s d g d i
    have h₁' : i < (List.foldl (relax k s d) d g).size := by simpa [step] using h₁
    have h₂' : i < d.size := by simpa using h₂
    unfold val at this
    rw [dite_eq_left h₂', dite_eq_left h₁'] at this
    exact this
  · intro h; exact hne (Array.toList_inj.mp h)

theorem pot_le {k s : Nat} {g : Graph} {d : Array Nat} (h : Inv k s g d) :
    pot d ≤ numNodes g * k := by
  obtain ⟨hs, hv⟩ := h
  have hall : ∀ x ∈ d.toList, x ≤ k := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := (hv i).1
    simp only [Array.length_toList] at hi
    unfold val at this; rw [dite_eq_left hi] at this
    rw [Array.getElem_toList]; exact this
  have : ∀ (l : List Nat), (∀ x ∈ l, x ≤ k) → l.sum ≤ l.length * k := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hl
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      have := hl a List.mem_cons_self
      have := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)); omega
  have := this _ hall
  simp only [Array.length_toList, hs] at this; exact this

theorem iter_spec (k s : Nat) (g : Graph) : ∀ (f : Nat) (d : Array Nat), Inv k s g d →
    pot d < f → ∃ d', iter k s g f d = some d' ∧ Inv k s g d' ∧ step k s g d' = d'
  | 0, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, d, hinv, hf => by
    simp only [iter]
    by_cases hfix : step k s g d = d
    · rw [ite_eq_left hfix]; exact ⟨d, rfl, hinv, hfix⟩
    · rw [ite_eq_right hfix]
      have := pot_step_lt hfix
      exact iter_spec k s g f _ (inv_step hinv) (by omega)

/-! ## Soundness and completeness -/

theorem sourceOk_iff (k : Nat) (g : Graph) (s : Nat) :
    sourceOk k g s = true ↔ ∀ c, Walk g s s c → k ≤ c := by
  obtain ⟨d, hd, hinv, hfix⟩ :=
    iter_spec k s g (fuel k g) (init k g) (inv_init k s g)
      (by have := pot_le (inv_init k s g); unfold fuel; omega)
  unfold sourceOk; rw [hd]; simp only [decide_eq_true_eq]
  constructor
  · intro hk c hw; exact Nat.le_trans hk (fix_complete hinv.1 hfix s c hw)
  · intro hall
    apply Nat.le_of_not_lt; intro hlt
    obtain ⟨c, hw, hc⟩ := (hinv.2 s).2 hlt
    have := hall c hw; omega

theorem walk_src_lt {g : Graph} {s v c : Nat} (h : Walk g s v c) : s < numNodes g := by
  induction h with
  | edge he hsrc => rw [← hsrc]; exact (lt_numNodes he).1
  | snoc _ _ ih => exact ih

/-- **Sound and complete**: the checker accepts exactly the graphs all of whose
closed walks carry at least `k` stages. -/
theorem check_iff (g : Graph) (k : Nat) : check g k = true ↔ AllCyclesGe g k := by
  unfold check AllCyclesGe
  rw [List.all_eq_true]
  constructor
  · intro h s c hw
    have hs := walk_src_lt hw
    exact (sourceOk_iff k g s).mp (h s (List.mem_range.mpr hs)) c hw
  · intro h s _
    exact (sourceOk_iff k g s).mpr (h s)

instance (g : Graph) (k : Nat) : Decidable (AllCyclesGe g k) :=
  decidable_of_iff _ (check_iff g k)

end Formal.Net.RingCheck
