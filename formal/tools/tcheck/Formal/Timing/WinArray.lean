import Formal.Timing.Checker

/-!
# Single-pass array version of 10a's `win` (probe C-10d)

10a's `win net v` rebuilds a table of all windows `0..v` and, for every node,
scans every arc (`collect`), so one `check` costs O(n² · arcs) reductions in the
kernel.  Here the windows are computed in ONE pass over the arcs, into an
`Array (Option Win)`:

    winTable net = net.arcs.foldl stepA (initA (maxDst net.arcs))
    stepA A a    = A[a.dst] := merge A[a.dst] (A[a.src] + [a.lo, a.hi])   (if A[a.src] is set)

which is correct when the arcs are listed with non-decreasing `src` (then every
arc INTO `a.src` has a smaller source, hence comes earlier, so `A[a.src]` is
final when `a` is processed).  `routed2lean` emits arcs in that order;
`sortedSrc` checks it, and `winArr` falls back to 10a's `win` if it fails, so

* `winArr_eq`   : `net.WF → winArr net v = win net v`  (for EVERY netlist);
* `checkArr_eq` : `net.WF → checkArr net req data setup = check net req data setup`;
* `checkArr_sound` : 10a's `check_sound` for `checkArr`.

Nothing of 10a is changed; this file only imports it.  Core Lean only.
-/

namespace Formal.Timing
open Formal.Net

/-! ## `collect` is a commutative fold, so it is invariant under permutation -/

/-- Merge of two optional windows (union hull). -/
def omerge : Option Win → Option Win → Option Win
  | none, w => w
  | some x, none => some x
  | some (e, l), some (e', l') => some (min e e', max l l')

/-- The window one arc contributes to node `v`. -/
def contrib (L : Nat → Option Win) (v : Nat) (a : Arc) : Option Win :=
  if a.dst = v then
    match L a.src with
    | some (e, l) => some (e + a.lo, l + a.hi)
    | none => none
  else none

theorem collect_cons (L : Nat → Option Win) (v : Nat) (a : Arc) (as : List Arc) :
    collect L v (a :: as) = omerge (collect L v as) (contrib L v a) := by
  simp only [collect, contrib]
  by_cases hd : a.dst = v
  · simp only [hd, if_true]
    cases L a.src with
    | none => cases collect L v as <;> rfl
    | some w =>
      obtain ⟨e, l⟩ := w
      cases h : collect L v as with
      | none => rfl
      | some x => obtain ⟨e', l'⟩ := x; rfl
  · simp only [hd, if_false]
    cases collect L v as <;> rfl

theorem omerge_swap (c x y : Option Win) : omerge (omerge c x) y = omerge (omerge c y) x := by
  rcases c with _ | ⟨c1, c2⟩ <;> rcases x with _ | ⟨x1, x2⟩ <;> rcases y with _ | ⟨y1, y2⟩ <;>
    simp only [omerge, Option.some.injEq, Prod.mk.injEq] <;> omega

theorem collect_perm (L : Nat → Option Win) (v : Nat) {l₁ l₂ : List Arc} (h : l₁.Perm l₂) :
    collect L v l₁ = collect L v l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [collect_cons, collect_cons, ih]
  | swap x y l => rw [collect_cons, collect_cons, collect_cons, collect_cons, omerge_swap]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- Arcs that do not end at `v` do not contribute to it. -/
theorem collect_append_none (L : Nat → Option Win) (v : Nat) :
    ∀ (p q : List Arc), (∀ a ∈ p, a.dst ≠ v) → collect L v (p ++ q) = collect L v q
  | [], _, _ => rfl
  | a :: p, q, h => by
    show collect L v (a :: (p ++ q)) = _
    simp only [collect, h a List.mem_cons_self, if_false]
    exact collect_append_none L v p q (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem omerge_none (c : Option Win) : omerge c none = c := by
  cases c <;> rfl

theorem omerge_mergeW (c : Option Win) (w : Win) : some (mergeW c w) = omerge c (some w) := by
  rcases c with _ | ⟨e, l⟩ <;> rcases w with ⟨e', l'⟩ <;> rfl

/-! ## The array pass -/

/-- Read a window out of the table (`none` out of range). -/
def getW (A : Array (Option Win)) (v : Nat) : Option Win := (A[v]?).getD none

def stepA (A : Array (Option Win)) (a : Arc) : Array (Option Win) :=
  match getW A a.src with
  | some (e, l) => A.setIfInBounds a.dst (some (mergeW (getW A a.dst) (e + a.lo, l + a.hi)))
  | none => A

def maxDst (arcs : List Arc) : Nat := arcs.foldl (fun m a => max m a.dst) 0

def initA (n : Nat) : Array (Option Win) := (Array.replicate (n + 1) none).setIfInBounds 0 (some (0, 0))

/-- All windows in one pass over the arcs. -/
def winTable (net : Netlist) : Array (Option Win) := net.arcs.foldl stepA (initA (maxDst net.arcs))

/-- Arcs listed with non-decreasing source. -/
def sortedSrc : List Arc → Bool
  | a :: b :: l => decide (a.src ≤ b.src) && sortedSrc (b :: l)
  | _ => true

/-- Fast windows (falls back to 10a's `win` when the arcs are not source-sorted). -/
def winArr (net : Netlist) (v : Nat) : Option Win :=
  if sortedSrc net.arcs then getW (winTable net) v else win net v

/-- 10a's `check`, over any window function. -/
def checkWith (W : Nat → Option Win) (req : Nat) (data : List Nat) (setup : Nat) : Bool :=
  match W req with
  | none => false
  | some (er, _) => data.all fun d =>
      match W d with
      | none => true
      | some (_, ld) => decide (ld + setup ≤ er)

def slackWith (W : Nat → Option Win) (req : Nat) (data : List Nat) (setup : Nat) : Option Int :=
  match W req with
  | none => none
  | some (er, _) => some (data.foldl (fun m d =>
      match W d with
      | none => m
      | some (_, ld) => min m ((er : Int) - ld - setup)) (er : Int))

/-- The bundling check on the one-pass table (table computed once). -/
def checkArr (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) : Bool :=
  if sortedSrc net.arcs then
    let T := winTable net
    checkWith (getW T) req data setup
  else check net req data setup

def slackArr (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) : Option Int :=
  if sortedSrc net.arcs then
    let T := winTable net
    slackWith (getW T) req data setup
  else slack net req data setup

theorem check_eq_checkWith (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) :
    check net req data setup = checkWith (win net) req data setup := rfl

theorem slack_eq_slackWith (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) :
    slack net req data setup = slackWith (win net) req data setup := rfl

/-! ## Correctness of the pass -/

theorem sortedSrc_head {a : Arc} : ∀ {l : List Arc}, sortedSrc (a :: l) = true → ∀ b ∈ l, a.src ≤ b.src
  | [], _, b, hb => absurd hb List.not_mem_nil
  | c :: l, h, b, hb => by
    simp only [sortedSrc, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact Nat.le_trans h.1 (sortedSrc_head h.2 b hb)

theorem sortedSrc_tail {a : Arc} : ∀ {l : List Arc}, sortedSrc (a :: l) = true → sortedSrc l = true
  | [], _ => rfl
  | _ :: _, h => by simp only [sortedSrc, Bool.and_eq_true] at h; exact h.2

theorem sortedSrc_append {p q : List Arc} (h : sortedSrc (p ++ q) = true) : sortedSrc q = true := by
  induction p with
  | nil => exact h
  | cons a p ih => exact ih (sortedSrc_tail h)

theorem le_maxDst_aux : ∀ (l : List Arc) (m : Nat),
    m ≤ l.foldl (fun m a => max m a.dst) m ∧ ∀ a ∈ l, a.dst ≤ l.foldl (fun m a => max m a.dst) m
  | [], m => ⟨Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, m => by
    obtain ⟨h1, h2⟩ := le_maxDst_aux l (max m a.dst)
    refine ⟨by simp only [List.foldl_cons]; omega, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · simp only [List.foldl_cons]; omega
    · exact h2 b hb

theorem le_maxDst {l : List Arc} {a : Arc} (h : a ∈ l) : a.dst ≤ maxDst l :=
  (le_maxDst_aux l 0).2 a h

theorem getW_set (A : Array (Option Win)) (i v : Nat) (x : Option Win) (hi : i < A.size) :
    getW (A.setIfInBounds i x) v = if i = v then x else getW A v := by
  simp only [getW, Array.getElem?_setIfInBounds]
  by_cases h : i = v
  · subst h; simp [hi]
  · simp [h]

theorem size_stepA (A : Array (Option Win)) (a : Arc) : (stepA A a).size = A.size := by
  unfold stepA
  split
  · exact Array.size_setIfInBounds
  · rfl

/-- The invariant after processing the prefix `p`: every entry is `collect` over
`p` (with the final windows as sources). -/
def Inv (net : Netlist) (n : Nat) (A : Array (Option Win)) (p : List Arc) : Prop :=
  A.size = n + 1 ∧ getW A 0 = some (0, 0) ∧ ∀ v, v ≠ 0 → getW A v = collect (win net) v p.reverse

theorem inv_step (net : Netlist) (hwf : net.WF) (hs : sortedSrc net.arcs = true)
    (A : Array (Option Win)) (p : List Arc) (a : Arc) (r : List Arc)
    (hsplit : net.arcs = p ++ a :: r) (hI : Inv net (maxDst net.arcs) A p) :
    Inv net (maxDst net.arcs) (stepA A a) (p ++ [a]) := by
  obtain ⟨hsz, h0, hv⟩ := hI
  have ha : a ∈ net.arcs := by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  have hwa := hwf a ha
  have hdst : a.dst < A.size := by have := le_maxDst ha; omega
  -- the source of `a` is final
  have hsrc : getW A a.src = win net a.src := by
    by_cases h : a.src = 0
    · rw [h, h0]; rfl
    · rw [hv a.src h, win_eq net hwf h, hsplit, collect_perm _ _ (List.reverse_perm p)]
      have hrest : ∀ b ∈ a :: r, b.dst ≠ a.src := by
        intro b hb hbd
        have hsr : sortedSrc (a :: r) = true := sortedSrc_append (hsplit ▸ hs)
        have hb2 : b ∈ net.arcs := by rw [hsplit]; exact List.mem_append_right _ hb
        have := (hwf b hb2).1
        rcases List.mem_cons.1 hb with rfl | hb'
        · omega
        · have := sortedSrc_head hsr b hb'; omega
      -- collect over p ++ (a :: r) = collect over p
      have := collect_perm (win net) a.src (List.perm_append_comm (l₁ := p) (l₂ := a :: r))
      rw [this, collect_append_none _ _ _ _ hrest]
  refine ⟨?_, ?_, ?_⟩
  · rw [size_stepA]; exact hsz
  · unfold stepA
    split
    · rw [getW_set _ _ _ _ hdst, if_neg (by omega)]; exact h0
    · exact h0
  · intro v hv0
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, collect_cons,
      ← hv v hv0]
    simp only [contrib, ← hsrc]
    unfold stepA
    cases hw : getW A a.src with
    | none =>
      by_cases hd : a.dst = v
      · rw [if_pos hd, omerge_none]
      · rw [if_neg hd, omerge_none]
    | some w =>
      obtain ⟨e, l⟩ := w
      simp only []
      rw [getW_set _ _ _ _ hdst]
      by_cases hd : a.dst = v
      · subst hd; rw [if_pos rfl, if_pos rfl, omerge_mergeW]
      · rw [if_neg hd, if_neg hd, omerge_none]

theorem inv_fold (net : Netlist) (hwf : net.WF) (hs : sortedSrc net.arcs = true) :
    ∀ (r p : List Arc) (A : Array (Option Win)), net.arcs = p ++ r →
      Inv net (maxDst net.arcs) A p → Inv net (maxDst net.arcs) (r.foldl stepA A) net.arcs
  | [], p, A, h, hI => by
    rw [List.append_nil] at h
    obtain ⟨h1, h2, h3⟩ := hI
    show Inv net (maxDst net.arcs) A net.arcs
    exact ⟨h1, h2, fun v hv => by rw [h3 v hv, h]⟩
  | a :: r, p, A, h, hI => by
    rw [List.foldl_cons]
    exact inv_fold net hwf hs r (p ++ [a]) (stepA A a) (by rw [h, List.append_assoc]; rfl)
      (inv_step net hwf hs A p a r h hI)

theorem inv_init (net : Netlist) : Inv net (maxDst net.arcs) (initA (maxDst net.arcs)) [] := by
  refine ⟨by simp [initA], ?_, ?_⟩
  · simp [initA, getW, Array.getElem?_setIfInBounds, Array.getElem?_replicate]
  · intro v hv
    simp only [initA, getW, Array.getElem?_setIfInBounds, Array.getElem?_replicate, Array.size_replicate]
    rw [if_neg (Ne.symm hv)]
    split <;> rfl

/-- **The one-pass table is 10a's `win`.** -/
theorem winTable_eq (net : Netlist) (hwf : net.WF) (hs : sortedSrc net.arcs = true) (v : Nat) :
    getW (winTable net) v = win net v := by
  obtain ⟨_, h0, hv⟩ := inv_fold net hwf hs net.arcs [] _ rfl (inv_init net)
  by_cases h : v = 0
  · subst h; exact h0
  · rw [winTable, hv v h, collect_perm _ _ (List.reverse_perm _), ← win_eq net hwf h]

theorem winArr_eq (net : Netlist) (hwf : net.WF) (v : Nat) : winArr net v = win net v := by
  unfold winArr
  split
  · next hs => exact winTable_eq net hwf hs v
  · rfl

theorem getW_winTable_fun (net : Netlist) (hwf : net.WF) (hs : sortedSrc net.arcs = true) :
    getW (winTable net) = win net := funext (winTable_eq net hwf hs)

theorem checkArr_eq (net : Netlist) (hwf : net.WF) (req : Nat) (data : List Nat) (setup : Nat) :
    checkArr net req data setup = check net req data setup := by
  unfold checkArr
  split
  · next hs => simp only [getW_winTable_fun net hwf hs]; rfl
  · rfl

theorem slackArr_eq (net : Netlist) (hwf : net.WF) (req : Nat) (data : List Nat) (setup : Nat) :
    slackArr net req data setup = slack net req data setup := by
  unfold slackArr
  split
  · next hs => simp only [getW_winTable_fun net hwf hs]; rfl
  · rfl

/-- 10a's soundness theorem, for the one-pass checker. -/
theorem checkArr_sound {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : checkArr net req data setup = true) {sig : Nat → Trace}
    (r : Run net sig) : ∀ d ∈ data, ∀ s t, changes (sig d) s → changes (sig req) t →
      s + setup ≤ t :=
  check_sound hwf (checkArr_eq net hwf req data setup ▸ hc) r

/-- The one-pass windows are sound (10a's `changes_in_window`). -/
theorem changes_in_winArr {net : Netlist} (hwf : net.WF) {sig : Nat → Trace}
    (r : Run net sig) : ∀ v t, changes (sig v) t →
      ∃ e l, winArr net v = some (e, l) ∧ e ≤ t ∧ t ≤ l := by
  intro v t h
  rw [winArr_eq net hwf]
  exact changes_in_window hwf r v t h

end Formal.Timing
