import Formal.Rewrite.Steps.Basic

/-!
# Formal.Rewrite.Steps.Cong — rewrites that do not change any firing; dropping a dead rule (shard A, 2026-11-19)

**Problem, plainly.** (1) A comp's inputs listed in another order, with its expression re-indexed, or its expression
replaced by one that computes the same value on every input: does anything change? (2) A rule `sink c` on a channel
nothing writes and that starts empty can never fire: may it be deleted?

**Proved.**
* `cong_run` / `cong_terminal`: if two rule lists fire identically at every label on every store, they have the same
  runs and the same terminal stores. `reorder_fire`: a comp with permuted inputs and the re-indexed expression
  (`reindex`) fires identically. `ident_fire`: so does a comp whose expression is replaced by one with the same value
  on every input list of the right length.
* `drop_forward` / `drop_backward`: deleting `sink c` (no rule writes `c`, `c` empty at the start) from a rule list
  keeps every complete run (labels after it shift down by one), same stores.

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## Same firings, same runs -/

theorem cong_run {rs rs' : List Rule} (h : ∀ l σ, step (graph rs') σ l = step (graph rs) σ l) :
    ∀ {σ t n}, Run (step (graph rs)) σ n t → Run (step (graph rs')) σ n t := by
  intro σ t n hr
  induction hr with
  | refl s => exact Run.refl s
  | cons l hl _ ih => exact Run.cons l (by rw [h]; exact hl) ih

theorem cong_terminal {rs rs' : List Rule} (h : ∀ l σ, step (graph rs') σ l = step (graph rs) σ l) {t : Store Nat Nat}
    (ht : Terminal (step (graph rs)) t) : Terminal (step (graph rs')) t := fun l => by rw [h]; exact ht l

/-- Two lists that differ only at `l`, where the two rules fire identically, have the same steps. -/
theorem same_steps {rs rs' : List Rule} {l : Nat} {r r' : Rule} (hr : rs[l]? = some r) (hr' : rs'[l]? = some r')
    (hsame : ∀ k, k ≠ l → rs'[k]? = rs[k]?) (hf : ∀ σ, r'.fire natVI σ = r.fire natVI σ) :
    ∀ k σ, step (graph rs') σ k = step (graph rs) σ k := by
  intro k σ
  by_cases e : k = l
  · subst e; rw [step_graph hr, step_graph hr', hf]
  · simp only [step, graph, graphV, hsame k e]

/-! ## Reordering a comp's inputs -/

/-- Position of `c` in `l` (`l.length` if absent). -/
def pos : List Nat → Nat → Nat
  | [], _ => 0
  | a :: l, c => if a = c then 0 else pos l c + 1

theorem getD_pos (h : Nat → Nat) : ∀ (l : List Nat) {c : Nat}, c ∈ l → (l.map h).getD (pos l c) 0 = h c
  | [], _, hc => by cases hc
  | a :: l, c, hc => by
    simp only [pos]
    by_cases e : a = c
    · subst e; simp
    · simp only [e, ite_false, List.map_cons, List.getD_cons_succ]
      exact getD_pos h l (by rcases List.mem_cons.mp hc with h | h; exact absurd h.symm e; exact h)

/-- The expression of a comp whose inputs `ins` are now read in the order `ins'`. -/
def reindex (ins ins' : List Nat) (F : E) : E := F.subst (ins.map fun c => .var (pos ins' c))

theorem eval_reindex {ins ins' : List Nat} (F : E) (hsub : ∀ c ∈ ins, c ∈ ins') (h : Nat → Nat) :
    (reindex ins ins' F).eval (ins'.map h) = F.eval (ins.map h) := by
  simp only [reindex, eval_subst, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp, E.eval]
  exact getD_pos h ins' (hsub c hc)

theorem popOf_congr {ins ins' : List Nat} (h : ∀ c, c ∈ ins ↔ c ∈ ins') : popOf ins = popOf ins' := by
  funext c; simp only [popOf, h c]

theorem reorder_fire {ins ins' : List Nat} {o : Nat} {F : E} (h : ∀ c, c ∈ ins ↔ c ∈ ins') (σ : Store Nat Nat) :
    (Rule.comp ins' o (reindex ins ins' F)).fire natVI σ = (Rule.comp ins o F).fire natVI σ := by
  by_cases hall : ∀ c ∈ ins, σ c ≠ []
  · have hall' : ∀ c ∈ ins', σ c ≠ [] := fun c hc => hall c ((h c).mpr hc)
    rw [fire_comp hall, fire_comp hall', eval_reindex F (fun c hc => (h c).mp hc), popOf_congr h]
  · obtain ⟨c, hc, he⟩ := exists_empty hall
    rw [fire_comp_none hc he, fire_comp_none ((h c).mp hc) he]

/-! ## Reordering a fork's outputs -/

theorem forder_fire {i : Nat} {os os' : List Nat} (h : ∀ c, c ∈ os ↔ c ∈ os') (σ : Store Nat Nat) :
    (Rule.fork i os').fire natVI σ = (Rule.fork i os).fire natVI σ := by
  cases hσ : σ i with
  | nil => rw [fire_fork_none hσ, fire_fork_none hσ]
  | cons v vs =>
    rw [fire_fork hσ, fire_fork hσ]
    congr 2; funext c; simp only [h c]

/-! ## Replacing an expression by an equal one -/

theorem ident_fire {ins : List Nat} {o : Nat} {F F' : E}
    (h : ∀ vs : List Nat, vs.length = ins.length → F'.eval vs = F.eval vs) (σ : Store Nat Nat) :
    (Rule.comp ins o F').fire natVI σ = (Rule.comp ins o F).fire natVI σ := by
  by_cases hall : ∀ c ∈ ins, σ c ≠ []
  · rw [fire_comp hall, fire_comp hall, h _ (by simp)]
  · obtain ⟨c, hc, he⟩ := exists_empty hall
    rw [fire_comp_none hc he, fire_comp_none hc he]

/-! ## Dropping a dead sink -/

section Drop
variable {rs : List Rule} {l c : Nat}

/-- No rule writes `c`. -/
def NoWrite (rs : List Rule) (c : Nat) : Prop := ∀ (k : Nat) (r : Rule), rs[k]? = some r → c ∉ r.outsL

theorem eraseIdx_lt {k : Nat} (hk : k < l) : (rs.eraseIdx l)[k]? = rs[k]? := by
  exact List.getElem?_eraseIdx_of_lt hk

theorem eraseIdx_ge {k : Nat} (hk : l ≤ k) : (rs.eraseIdx l)[k]? = rs[k + 1]? := by
  exact List.getElem?_eraseIdx_of_ge hk

/-- The label of `rs` that label `k` of the erased list came from. -/
def up (l k : Nat) : Nat := if k < l then k else k + 1

theorem erase_up (k : Nat) : (rs.eraseIdx l)[k]? = rs[up l k]? := by
  unfold up
  by_cases hk : k < l
  · rw [if_pos hk, eraseIdx_lt hk]
  · rw [if_neg hk, eraseIdx_ge (by omega)]

theorem step_c_empty {rs : List Rule} (hw : NoWrite rs c) {σ σ' : Store Nat Nat} {k : Nat} (hc : σ c = [])
    (hs : step (graph rs) σ k = some σ') : σ' c = [] := by
  cases hr : rs[k]? with
  | none => rw [none_none hr] at hs; cases hs
  | some r =>
    rw [step_graph hr] at hs
    cases hf : r.fire natVI σ with
    | none => rw [hf] at hs; cases hs
    | some fr =>
      rw [hf] at hs
      rw [← Option.some.inj hs, applyF_at, hc, fire_push0 hf (hw k r hr)]; simp

theorem run_c_empty {rs : List Rule} (hw : NoWrite rs c) {σ t : Store Nat Nat} {n : Nat}
    (hr : Run (step (graph rs)) σ n t) (hc : σ c = []) : t c = [] := by
  induction hr with
  | refl => exact hc
  | cons k hk _ ih => exact ih (step_c_empty hw hc hk)

theorem noWrite_erase (hw : NoWrite rs c) : NoWrite (rs.eraseIdx l) c := by
  unfold NoWrite at *; intro k r hr; rw [erase_up] at hr; exact hw _ r hr

theorem sink_none (hl : rs[l]? = some (.sink c)) {σ : Store Nat Nat} (hc : σ c = []) : step (graph rs) σ l = none := by
  rw [step_graph hl, fire_sink_none hc]; rfl

theorem drop_forward (hl : rs[l]? = some (.sink c)) (hw : NoWrite rs c) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 c = []) (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    Run (step (graph (rs.eraseIdx l))) σ0 n t ∧ Terminal (step (graph (rs.eraseIdx l))) t := by
  constructor
  · induction hr with
    | refl s => exact Run.refl s
    | @cons σ σ1 u m k hk _ ih =>
      have hk' : k ≠ l := fun e => by subst e; rw [sink_none hl h0] at hk; cases hk
      have hσ1 : σ1 c = [] := step_c_empty hw h0 hk
      refine Run.cons (if k < l then k else k - 1) ?_ (ih hσ1 ht)
      have : step (graph (rs.eraseIdx l)) σ (if k < l then k else k - 1) = step (graph rs) σ k := by
        simp only [step, graph, graphV]
        rw [erase_up]; unfold up
        by_cases hlt : k < l
        · simp [hlt]
        · rw [if_neg hlt, if_neg (by omega), Nat.sub_add_cancel (by omega)]
      rw [this]; exact hk
  · intro k
    have : step (graph (rs.eraseIdx l)) t k = step (graph rs) t (up l k) := by
      simp only [step, graph, graphV]; rw [erase_up]
    rw [this]; exact ht _

theorem drop_backward (hl : rs[l]? = some (.sink c)) (hw : NoWrite rs c) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : σ0 c = []) (hr : Run (step (graph (rs.eraseIdx l))) σ0 n t)
    (ht : Terminal (step (graph (rs.eraseIdx l))) t) :
    Run (step (graph rs)) σ0 n t ∧ Terminal (step (graph rs)) t := by
  have htc : t c = [] := run_c_empty (noWrite_erase hw) hr h0
  constructor
  · induction hr with
    | refl s => exact Run.refl s
    | @cons σ σ1 u m k hk _ ih =>
      refine Run.cons (up l k) ?_ (ih (step_c_empty (noWrite_erase hw) h0 hk) ht htc)
      have : step (graph (rs.eraseIdx l)) σ k = step (graph rs) σ (up l k) := by
        simp only [step, graph, graphV]; rw [erase_up]
      rw [← this]; exact hk
  · intro k
    by_cases e : k = l
    · subst e; exact sink_none hl htc
    · by_cases hlt : k < l
      · have := ht k
        have e2 : step (graph (rs.eraseIdx l)) t k = step (graph rs) t k := by
          simp only [step, graph, graphV]; rw [erase_up]; unfold up; rw [if_pos hlt]
        rw [← e2]; exact this
      · have := ht (k - 1)
        have e2 : step (graph (rs.eraseIdx l)) t (k - 1) = step (graph rs) t k := by
          simp only [step, graph, graphV]; rw [erase_up]; unfold up
          rw [if_neg (by omega), Nat.sub_add_cancel (by omega)]
        rw [← e2]; exact this

end Drop

end Formal.Rewrite.Steps
