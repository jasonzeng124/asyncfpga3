import Formal.Net.KahnGcd

/-!
# Bounded channels (probe C-8b)

Core Lean only. Same nodes as `Formal.Net.Kahn`, but every channel `c` holds at
most `cap c` tokens: a node may fire only if, after firing, each channel it
pushes into is within capacity. This is backpressure, the token-level shadow of
a handshake stall. A complete run may now end in an artificial deadlock (a full
channel), but `wfB_diamond` shows the diamond still holds for `WF` graphs, so
determinacy still holds: every schedule reaches the SAME terminal state, deadlock
or result.

`Gcd.G` with capacity 1 on every channel computes the same as the unbounded
graph (`cap1_dataflow_eq_cLoop`): the schedules of `KahnGcd` never hold two
tokens in one channel.

Capacity-1 FIFOs per channel are NOT the bd_link pipeline: a bundled-data
channel without a latch is a rendezvous (capacity 0, fused with its endpoints),
and a latch stage is capacity 1 with a bubble discipline. See the notes.
-/

namespace Formal.Net.Kahn

variable {C V L : Type}

/-- `chans` lists every channel (the graph is finite). -/
def capOK (chans : List C) (cap : C → Nat) (s : Store C V) (r : Fire C V) : Bool :=
  chans.all fun c => (r.2 c).isEmpty || decide ((applyF s r c).length ≤ cap c)

def stepB (G : L → Node C V) (chans : List C) (cap : C → Nat) (s : Store C V) (l : L) :
    Option (Store C V) :=
  match (G l).fire s with
  | none => none
  | some r => if capOK chans cap s r then some (applyF s r) else none

theorem stepB_some {G : L → Node C V} {chans : List C} {cap : C → Nat} {s s' : Store C V} {l : L}
    (h : stepB G chans cap s l = some s') :
    ∃ r, (G l).fire s = some r ∧ capOK chans cap s r = true ∧ s' = applyF s r := by
  unfold stepB at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h; exact ⟨r, hr, by assumption, rfl⟩
    · cases h

theorem capOK_iff {chans : List C} (hall : ∀ c, c ∈ chans) {cap : C → Nat} {s : Store C V}
    {r : Fire C V} :
    capOK chans cap s r = true ↔ ∀ c, r.2 c ≠ [] → (applyF s r c).length ≤ cap c := by
  simp only [capOK, List.all_eq_true, Bool.or_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · intro h c hc; rcases h c (hall c) with h | h
    · exact absurd h hc
    · exact h
  · intro h c _
    by_cases hc : r.2 c = []
    · exact Or.inl hc
    · exact Or.inr (h c hc)

theorem applyF_comm {G : L → Node C V} (hG : WF G) {l₁ l₂ : L} (hne : l₁ ≠ l₂) {s : Store C V}
    {r₁ r₂ : Fire C V} (hr₁ : (G l₁).fire s = some r₁) (hr₂ : (G l₂).fire s = some r₂) :
    applyF (applyF s r₁) r₂ = applyF (applyF s r₂) r₁ := by
  funext c
  have hp : r₁.1 c = 0 ∨ r₂.1 c = 0 := by
    by_cases a : (G l₁).ins c
    · exact Or.inr ((G l₂).pop_ins s r₂ c hr₂ (fun b => hG.ins_disj l₁ l₂ c hne a b))
    · exact Or.inl ((G l₁).pop_ins s r₁ c hr₁ a)
  have hq : r₁.2 c = [] ∨ r₂.2 c = [] := by
    by_cases a : (G l₁).outs c
    · exact Or.inr ((G l₂).push_outs s r₂ c hr₂ (fun b => hG.outs_disj l₁ l₂ c hne a b))
    · exact Or.inl ((G l₁).push_outs s r₁ c hr₁ a)
  have le1 := (G l₁).pop_le s r₁ c hr₁
  have le2 := (G l₂).pop_le s r₂ c hr₂
  simp only [applyF]
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    simp [hp, hq, List.drop_append_of_le_length, le1, le2]

/-- Firing `l₁` cannot overfill a channel `l₂` pushes into (unique producer:
`l₁` only pops from it), so `l₂` stays enabled. -/
theorem capOK_after {G : L → Node C V} (hG : WF G) {chans : List C} (hall : ∀ c, c ∈ chans)
    {cap : C → Nat} {l₁ l₂ : L} (hne : l₁ ≠ l₂) {s : Store C V} {r₁ r₂ : Fire C V}
    (hr₁ : (G l₁).fire s = some r₁) (hr₂ : (G l₂).fire s = some r₂)
    (hc₂ : capOK chans cap s r₂ = true) : capOK chans cap (applyF s r₁) r₂ = true := by
  rw [capOK_iff hall] at hc₂ ⊢
  intro c hc
  have h2 := hc₂ c hc
  have ho : (G l₂).outs c := Classical.byContradiction fun h => hc ((G l₂).push_outs s r₂ c hr₂ h)
  have hq : r₁.2 c = [] :=
    (G l₁).push_outs s r₁ c hr₁ (fun h => hG.outs_disj l₁ l₂ c hne h ho)
  simp only [applyF, hq, List.append_nil, List.length_append, List.length_drop] at h2 ⊢
  omega

theorem wfB_diamond {G : L → Node C V} (hG : WF G) {chans : List C} (hall : ∀ c, c ∈ chans)
    (cap : C → Nat) : DiamondOn (stepB G chans cap) (fun _ => True) := by
  intro s l₁ l₂ s₁ s₂ _ hne h1 h2
  obtain ⟨r₁, hr₁, hc₁, rfl⟩ := stepB_some h1
  obtain ⟨r₂, hr₂, hc₂, rfl⟩ := stepB_some h2
  have f2 : (G l₂).fire (applyF s r₁) = some r₂ :=
    (G l₂).mono s _ r₂ hr₂ (other_extends hG.ins_disj hne hr₁)
  have f1 : (G l₁).fire (applyF s r₂) = some r₁ :=
    (G l₁).mono s _ r₁ hr₁ (other_extends hG.ins_disj (Ne.symm hne) hr₂)
  refine ⟨applyF (applyF s r₁) r₂, ?_, ?_⟩
  · simp [stepB, f2, capOK_after hG hall hne hr₁ hr₂ hc₂]
  · simp [stepB, f1, capOK_after hG hall (Ne.symm hne) hr₂ hr₁ hc₁, applyF_comm hG hne hr₁ hr₂]

theorem wfB_determinate {G : L → Node C V} (hG : WF G) {chans : List C} (hall : ∀ c, c ∈ chans)
    (cap : C → Nat) {s t t' : Store C V} {n m : Nat}
    (h1 : Run (stepB G chans cap) s n t) (ht : Terminal (stepB G chans cap) t)
    (h2 : Run (stepB G chans cap) s m t') (ht' : Terminal (stepB G chans cap) t') :
    t' = t ∧ m = n :=
  terminal_unique closed_true (wfB_diamond hG hall cap) trivial h1 ht h2 ht'

def execB (G : L → Node C V) (chans : List C) (cap : C → Nat) (s : Store C V) :
    List L → Option (Store C V)
  | [] => some s
  | l :: ls => (stepB G chans cap s l).bind (fun s' => execB G chans cap s' ls)

theorem execB_run {G : L → Node C V} {chans : List C} {cap : C → Nat} {s t t' : Store C V}
    {ls : List L} (h : execB G chans cap s ls = some t) (he : ∀ c, t c = t' c) :
    Run (stepB G chans cap) s ls.length t' := by
  induction ls generalizing s with
  | nil => simp only [execB, Option.some.injEq] at h; subst h; exact run_refl_eq (funext he)
  | cons l ls ih =>
    simp only [execB] at h
    cases hs : stepB G chans cap s l with
    | none => rw [hs] at h; cases h
    | some s' => rw [hs] at h; exact Run.cons l hs (ih h)

namespace Gcd

def chans : List Ch :=
  [.inA, .inB, .sA, .sB, .backA, .backB, .hA, .hB, .hA1, .hA2, .cnd, .cA, .cB,
   .aT, .aF, .bT, .out, .a1, .a2, .b1, .b2]

theorem chans_all (c : Ch) : c ∈ chans := by cases c <;> simp [chans]

/-- Every channel holds at most one token. -/
abbrev S1 := stepB G chans (fun _ => 1)

theorem b_init_mid (a b : Nat) : Run S1 (init a b) 2 (mid a b) :=
  execB_run (ls := [.muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem b_top_mid (a b : Nat) : Run S1 (top a b) 2 (mid a b) :=
  execB_run (ls := [.muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem b_mid_top (a b : Nat) :
    Run S1 (mid (a + 1) b) 9 (top (strip2 (absdiff (a + 1) b)) (min (a + 1) b)) :=
  execB_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .forkAT, .forkBT, .sub, .mn]) rfl
    (fun c => by cases c <;> rfl)

theorem b_mid_fin (b : Nat) : Run S1 (mid 0 b) 5 (fin b) :=
  execB_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .snkA]) rfl
    (fun c => by cases c <;> rfl)

theorem b_fin_terminal (r : Nat) : Terminal S1 (fin r) := by
  intro l; cases l <;> rfl

theorem b_run_of_cLoop : ∀ f a b r, cLoop f a b = some r → ∃ n, Run S1 (mid a b) n (fin r) := by
  intro f
  induction f with
  | zero => intro a b r h; simp [cLoop] at h
  | succ f ih =>
    intro a b r h
    simp only [cLoop] at h
    by_cases h0 : a = 0
    · subst h0; simp at h; subst h; exact ⟨6, b_mid_fin b⟩
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨n, hn⟩ := ih _ _ r h
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact ⟨9 + 2 + n, run_trans (run_trans (b_mid_top a' b) (b_top_mid _ _)) hn⟩

/-- With one-token channels the gcd loop graph still never deadlocks on inputs
where the C loop terminates, and every schedule gives the C loop's result. -/
theorem cap1_dataflow_eq_cLoop {f a b r : Nat} (h : cLoop f a b = some r) :
    (∃ n, Run S1 (init a b) n (fin r)) ∧
    (∀ m t, Run S1 (init a b) m t → Terminal S1 t → t = fin r) := by
  obtain ⟨n, hn⟩ := b_run_of_cLoop f a b r h
  have hr := run_trans (b_init_mid a b) hn
  exact ⟨⟨_, hr⟩, fun m t ht hT =>
    (wfB_determinate G_wf chans_all (fun _ => 1) hr (b_fin_terminal r) ht hT).1⟩

end Gcd

end Formal.Net.Kahn
