import Formal.Rewrite.IncCmpGraph

/-!
# Formal.Rewrite.IncCmp2Lib — pairing two token streams (shard A, 2026-11-18)

Core Lean only. A two-input `comp` pairs the tokens of its two input channels in order. `lft X K` is what is left
of the two lists after pairing (one of the two is empty); `List.zipWith` is what the pairing produced. The lemmas
say how both change when tokens are appended to either side, and the step / drain lemmas for a two-input `comp`.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

/-- What is left of two streams after pairing them in order. -/
def lft : List Nat → List Nat → List Nat × List Nat
  | a :: X, w :: K => lft X K
  | X, K => (X, K)

@[simp] theorem lft_nil_left (K : List Nat) : lft [] K = ([], K) := by cases K <;> rfl
@[simp] theorem lft_nil_right (X : List Nat) : lft X [] = (X, []) := by cases X <;> rfl
@[simp] theorem lft_cons (a w : Nat) (X K : List Nat) : lft (a :: X) (w :: K) = lft X K := rfl

theorem lft_one_empty : ∀ (X K : List Nat), (lft X K).1 = [] ∨ (lft X K).2 = []
  | [], K => by simp
  | a :: X, [] => by simp
  | a :: X, w :: K => by simp only [lft_cons]; exact lft_one_empty X K

theorem lft_len (X K : List Nat) : (lft X K).1.length = (lft X K).1.length := rfl

theorem zw_app_left (f : Nat → Nat → Nat) : ∀ (X ys K : List Nat),
    List.zipWith f (X ++ ys) K = List.zipWith f X K ++ List.zipWith f ys (lft X K).2
  | [], ys, K => by simp
  | a :: X, ys, [] => by simp
  | a :: X, ys, w :: K => by
    simp only [List.cons_append, List.zipWith_cons_cons, lft_cons, zw_app_left f X ys K]

theorem zw_app_right (f : Nat → Nat → Nat) : ∀ (X K ys : List Nat),
    List.zipWith f X (K ++ ys) = List.zipWith f X K ++ List.zipWith f (lft X K).1 ys
  | [], K, ys => by simp
  | a :: X, [], ys => by simp
  | a :: X, w :: K, ys => by
    simp only [List.cons_append, List.zipWith_cons_cons, lft_cons, zw_app_right f X K ys]

theorem lft_app_left : ∀ (X ys K : List Nat),
    lft (X ++ ys) K = if (lft X K).1 = [] then lft ys (lft X K).2 else ((lft X K).1 ++ ys, (lft X K).2)
  | [], ys, K => by simp
  | a :: X, ys, [] => by simp
  | a :: X, ys, w :: K => by simp only [List.cons_append, lft_cons]; exact lft_app_left X ys K

theorem lft_app_right : ∀ (X K ys : List Nat),
    lft X (K ++ ys) = if (lft X K).2 = [] then lft (lft X K).1 ys else ((lft X K).1, (lft X K).2 ++ ys)
  | [], K, ys => by simp
  | a :: X, [], ys => by simp
  | a :: X, w :: K, ys => by simp only [List.cons_append, lft_cons]; exact lft_app_right X K ys

theorem lft_map (g : Nat → Nat) : ∀ (X K : List Nat), lft (X.map g) K = ((lft X K).1.map g, (lft X K).2)
  | [], K => by simp
  | a :: X, [] => by simp
  | a :: X, w :: K => by simp only [List.map_cons, lft_cons]; exact lft_map g X K

theorem zw_map (f : Nat → Nat → Nat) (g : Nat → Nat) : ∀ (X K : List Nat),
    List.zipWith f (X.map g) K = List.zipWith (fun a b => f (g a) b) X K
  | [], K => by simp
  | a :: X, [] => by simp
  | a :: X, w :: K => by simp only [List.map_cons, List.zipWith_cons_cons, zw_map f g X K]

/-! ## A two-input `comp` -/

theorem step_comp2 {rs : List Rule} {l i j o : Nat} {f : E} (hr : rs[l]? = some (.comp [i, j] o f))
    (hij : i ≠ j) (hio : i ≠ o) (hjo : j ≠ o) {σ : Store Nat Nat} {a w : Nat} {as ws : List Nat}
    (hi : σ i = a :: as) (hj : σ j = w :: ws) :
    step (graph rs) σ l = some (upd (upd (upd σ i as) j ws) o (σ o ++ [f.eval [a, w]])) := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hi, hj, Rule.out, natVI, Rule.insL]
  simp only [Option.map_some, Option.bind_some, Option.some.injEq]
  funext c
  simp only [applyF, popOf, upd, List.mem_cons, List.not_mem_nil, or_false]
  by_cases e1 : c = o
  · subst e1; simp [Ne.symm hio, Ne.symm hjo]
  · by_cases e2 : c = j
    · subst e2; simp [hj, e1, Ne.symm hij]
    · by_cases e3 : c = i
      · subst e3; simp [hi, e1, e2]
      · simp [e1, e2, e3]

theorem step_comp2_none {rs : List Rule} {l i j o : Nat} {f : E} (hr : rs[l]? = some (.comp [i, j] o f))
    {σ : Store Nat Nat} (h : σ i = [] ∨ σ j = []) : step (graph rs) σ l = none := by
  rw [step_graph hr]
  rcases h with h | h
  · simp only [Rule.fire, strictF, heads, h, Rule.insL]; rfl
  · simp only [Rule.fire, strictF, heads, Rule.insL]
    cases σ i <;> simp [h]

/-- Fire a two-input `comp` until one input is empty. -/
theorem drain_comp2 {rs : List Rule} {l i j o : Nat} {f : E} (hr : rs[l]? = some (.comp [i, j] o f))
    (hij : i ≠ j) (hio : i ≠ o) (hjo : j ≠ o) : ∀ (X K : List Nat) (σ : Store Nat Nat), σ i = X → σ j = K →
    ∃ n, Run (step (graph rs)) σ n
      (upd (upd (upd σ i (lft X K).1) j (lft X K).2) o (σ o ++ List.zipWith (fun a b => f.eval [a, b]) X K))
  | [], K, σ, hi, hj => by
    refine ⟨0, run_refl_eq ?_⟩
    funext c; simp only [upd, lft_nil_left, List.zipWith_nil_left, List.append_nil]
    by_cases e1 : c = o
    · subst e1; simp
    · by_cases e2 : c = j
      · subst e2; simp [hj, e1]
      · by_cases e3 : c = i
        · subst e3; simp [hi, e1, e2]
        · simp [e1, e2, e3]
  | a :: X, [], σ, hi, hj => by
    refine ⟨0, run_refl_eq ?_⟩
    funext c; simp only [upd, lft_nil_right, List.zipWith_nil_right, List.append_nil]
    by_cases e1 : c = o
    · subst e1; simp
    · by_cases e2 : c = j
      · subst e2; simp [hj, e1]
      · by_cases e3 : c = i
        · subst e3; simp [hi, e1, e2]
        · simp [e1, e2, e3]
  | a :: X, w :: K, σ, hi, hj => by
    have hs := step_comp2 hr hij hio hjo hi hj
    obtain ⟨n, hrun⟩ := drain_comp2 hr hij hio hjo X K (upd (upd (upd σ i X) j K) o (σ o ++ [f.eval [a, w]]))
      (by simp [upd, hio, hij]) (by simp [upd, hjo])
    refine ⟨n + 1, Run.cons l hs ?_⟩
    have e : upd (upd (upd (upd (upd (upd σ i X) j K) o (σ o ++ [f.eval [a, w]])) i (lft X K).1) j (lft X K).2) o
        ((upd (upd (upd σ i X) j K) o (σ o ++ [f.eval [a, w]])) o ++
          List.zipWith (fun a b => f.eval [a, b]) X K) =
        upd (upd (upd σ i (lft (a :: X) (w :: K)).1) j (lft (a :: X) (w :: K)).2) o
          (σ o ++ List.zipWith (fun a b => f.eval [a, b]) (a :: X) (w :: K)) := by
      funext c; simp only [upd, lft_cons, List.zipWith_cons_cons]
      by_cases e1 : c = o
      · subst e1; simp
      · by_cases e2 : c = j
        · subst e2; simp [e1]
        · by_cases e3 : c = i
          · subst e3; simp [e1, e2]
          · simp [e1, e2, e3]
    rw [e] at hrun; exact hrun

end Formal.Rewrite.IncCmp
