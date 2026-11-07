import Formal.Core.XAudit.Untimed

/-!
# Formal.Core.XAudit.SoundChain — the untimed engine's phase chaining (Wip W1), proved

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

`xaudit`'s untimed half runs Eichelberger A/B once per stimulus phase and starts
phase `i` from the B row of phase `i - 1` (power-up: the all-`X` row). The
per-phase theorems `Untimed.untimed_noGlitch`/`untimed_settles` assume the
phase's start STATE is covered by its start row, at time 0 of a `Causal`
behaviour. That hypothesis cannot be discharged for a later phase: a phase does
not start at time 0, and a `Causal` node may sample any earlier time.

Here the chaining is proved under **bounded staleness alone**
(`Ternary.Stale N c σ D`: from time `D` on, every node value is its gate
function of samples taken within the last `D` steps; `Causal` is not needed):

* `stale_cover_window` (the "covered-window" `sound_postfix`): a post-fixed
  point `p` of the ternary net under `u` that covers the state on a window
  `[S - D, S)` of length `D` (with `D ≤ S`), with `u` covering the inputs on
  `[S - D, E)`, covers the state on all of `[S - D, E)`.
* `stale_settle_window`: B-iterates under inputs `b` on `[S, E)` from a row
  covering `[S, E)`: the `k`-th covers `[S + k D, E)`.
* `iterA_X`: A from the all-`X` row stays all `X` (so power-up needs no window).
* **`chain_phases`**: phases `i = 0, 1, ...` with input vector `vs i` on
  `[T i, T (i+1))` and gaps `T i + (n+1) D ≤ T (i+1)` (fundamental mode: each
  phase lasts at least `(n+1) D`). The executable's rows
  `r 0 = rowX`, `r (i+1) = runB N (prevIn vs i) (vs i) (r i)` (with
  `prevIn vs 0 = vs 0`, `prevIn vs (i+1) = vs i`, exactly what `Main.lean`
  passes) satisfy, in every `Stale D` behaviour:
  - the A row of phase `i` covers every state of phase `i`, `[T i, T (i+1))`
    (so an A-binary wire does not glitch during the whole phase);
  - the B row `r (i+1)` covers every state on `[T i + n D, T (i+1))`.
* `chain_noGlitch`, `chain_settles`: the printed binary verdicts as facts.

Remark on `Wip/XAudit.lean`'s `chain_phases`: its recursion
`r (i+1) = runB N (vs i) (vs (i+1)) (r i)` makes `r (i+1)` the B row of the
transition INTO `vs (i+1)`, while its conclusion asks `r (i+1)` to cover phase
`i` (inputs `vs i`); that indexing does not match `Main.lean` and the stated
claim is not what the executable computes. The statement here follows
`Main.lean`.

Not covered: phases shorter than `(n+1) D`; phases with `X` inputs (the
executable skips them); what `D` is for given gate and wire bands (`Stale D`
is a hypothesis; `TernaryChannels.stale_of_transport` gives it for discrete
transport with `hi ≤ D`).
-/

namespace Formal.Core.XAudit.SoundChain

open Formal.Core.Ternary
open Formal.Core.Ternary.K3
open Formal.Core.XAudit.Untimed

local notation "TK" => Formal.Core.Ternary.K3

section Gen
variable {ι ν : Type} (N : Net ι ν)

/-- **Covered-window soundness of a post-fixed point under bounded staleness.** -/
theorem stale_cover_window {u : ι → TK} {p : ν → TK} (hp : VLe p (N.F u p))
    {c : Nat → ι → Bool} {σ : Nat → ν → Bool} {D S E : Nat} (hD : Stale N c σ D) (hS : D ≤ S)
    (hc : ∀ t, S - D ≤ t → t < E → VLe u (vb (c t)))
    (hw : ∀ t, S - D ≤ t → t < S → VLe p (vb (σ t))) :
    ∀ t, S - D ≤ t → t < E → VLe p (vb (σ t)) := by
  suffices H : ∀ M t, t < M → S - D ≤ t → t < E → VLe p (vb (σ t)) from
    fun t => H (t + 1) t (Nat.lt_succ_self t)
  intro M
  induction M with
  | zero => intro t ht; omega
  | succ M IH =>
    intro t htM h1 h2
    by_cases hts : t < S
    · exact hw t h1 hts
    intro i
    obtain ⟨τi, τn, hτi, hτn, h⟩ := hD t i (by omega)
    show p i ⊑ ofBool (σ t i)
    rw [h]
    refine le_trans (hp i) (N.cover ?_ ?_ i)
    · intro x
      exact hc (τi x) (by have := hτi x; omega) (by have := hτi x; omega) x
    · intro j
      exact IH (τn j) (by have := hτn j; omega) (by have := hτn j; omega)
        (by have := hτn j; omega) j

/-- **B-iterates settle within a window.** -/
theorem stale_settle_window {b : ι → Bool} {q0 : ν → TK}
    {c : Nat → ι → Bool} {σ : Nat → ν → Bool} {D S E : Nat} (hD : Stale N c σ D)
    (hb : ∀ t, S ≤ t → t < E → c t = b)
    (h0 : ∀ t, S ≤ t → t < E → VLe q0 (vb (σ t))) :
    ∀ k t, S + k * D ≤ t → t < E → VLe (iterB N b q0 k) (vb (σ t)) := by
  intro k
  induction k with
  | zero => intro t h1 h2; exact h0 t (by omega) h2
  | succ k IH =>
    intro t h1 h2 i
    rw [Nat.succ_mul] at h1
    obtain ⟨τi, τn, hτi, hτn, h⟩ := hD t i (by omega)
    show N.F (vb b) (iterB N b q0 k) i ⊑ ofBool (σ t i)
    rw [h]
    apply N.cover
    · intro x
      have : c (τi x) = b := hb _ (by have := hτi x; omega) (by have := hτi x; omega)
      show vb b x ⊑ ofBool (c (τi x) x)
      rw [this]; exact le_refl _
    · intro j
      exact IH (τn j) (by have := hτn j; omega) (by have := hτn j; omega) j

/-- Algorithm A from the all-`X` row stays all `X`. -/
theorem iterA_X (u : ι → TK) : ∀ k, iterA N u (fun _ => X) k = fun _ => X
  | 0 => rfl
  | k + 1 => by
      funext i
      show meet (iterA N u (fun _ => X) k i) _ = X
      rw [iterA_X u k]
      simp only [meet]
      split <;> rfl

end Gen

/-! ## The executable's chain -/

/-- The "previous" input vector the executable passes for phase `i`: phase 0
(power-up) is the null transition `vs 0 → vs 0`. -/
def prevIn {n : Nat} (vs : Nat → Fin n → Bool) : Nat → Fin n → Bool
  | 0 => vs 0
  | i + 1 => vs i

theorem rget_rowX {n : Nat} : rget (n := n) (rowX n) = fun _ => (X : TK) := by
  funext i; rw [rowX, rget_rowOf]

variable {n : Nat} (N : Net (Fin n) (Fin n)) (D : Nat) (vs : Nat → Fin n → Bool)
  (T : Nat → Nat) (r : Nat → Array TK)

/-- **Phase chaining** (Wip W1). -/
theorem chain_phases
    (hr0 : r 0 = rowX n) (hr : ∀ i, r (i + 1) = runB N (prevIn vs i) (vs i) (r i))
    (hT : ∀ i, T i + (n + 1) * D ≤ T (i + 1))
    (c : Nat → Fin n → Bool) (σ : Nat → Fin n → Bool)
    (hc : ∀ i t, T i ≤ t → t < T (i + 1) → c t = vs i) (hD : Stale N c σ D) :
    ∀ i, (∀ t, T i ≤ t → t < T (i + 1) →
        VLe (rget (runA N (prevIn vs i) (vs i) (r i))) (vb (σ t))) ∧
      (∀ t, T i + n * D ≤ t → t < T (i + 1) → VLe (rget (r (i + 1))) (vb (σ t))) := by
  -- B covers from the A cover
  have hB : ∀ i, (∀ t, T i ≤ t → t < T (i + 1) →
        VLe (rget (runA N (prevIn vs i) (vs i) (r i))) (vb (σ t))) →
      ∀ t, T i + n * D ≤ t → t < T (i + 1) → VLe (rget (r (i + 1))) (vb (σ t)) := by
    intro i hA t h1 h2
    rw [hr i, runB_eq, ← runA_eq, List.length_finRange]
    exact stale_settle_window N hD (hc i) hA n t h1 h2
  intro i
  induction i with
  | zero =>
      have hA : ∀ t, T 0 ≤ t → t < T 1 →
          VLe (rget (runA N (prevIn vs 0) (vs 0) (r 0))) (vb (σ t)) := by
        intro t _ _ w
        rw [runA_eq, hr0, rget_rowX, iterA_X]
        exact X_le _
      exact ⟨hA, hB 0 hA⟩
  | succ i IH =>
      obtain ⟨_, hBi⟩ := IH
      have hTi := hT i
      have hTi1 := hT (i + 1)
      have hmul : (n + 1) * D = n * D + D := Nat.succ_mul n D
      have hA : ∀ t, T (i + 1) ≤ t → t < T (i + 1 + 1) →
          VLe (rget (runA N (prevIn vs (i + 1)) (vs (i + 1)) (r (i + 1)))) (vb (σ t)) := by
        have hpost := iterA_postfix N (List.finRange n) List.mem_finRange
          (uA (prevIn vs (i + 1)) (vs (i + 1))) (rget (r (i + 1)))
        have hle := iterA_le_start N (uA (prevIn vs (i + 1)) (vs (i + 1))) (rget (r (i + 1)))
          (List.finRange n).length
        have hcov := stale_cover_window N hpost (S := T (i + 1)) (E := T (i + 1 + 1)) hD
          (by omega)
          (fun t h1 h2 => hull_le (fun x => by
            by_cases ht : t < T (i + 1)
            · left; rw [hc i t (by omega) ht]; rfl
            · right; rw [hc (i + 1) t (by omega) h2]))
          (fun t h1 h2 => vle_trans hle (hBi t (by omega) h2))
        intro t h1 h2
        rw [runA_eq]
        exact hcov t (by omega) h2
      exact ⟨hA, hB (i + 1) hA⟩

/-- **No glitch in a chained phase**: a wire binary `v` in phase `i`'s A row is
`v` throughout phase `i`. -/
theorem chain_noGlitch
    (hr0 : r 0 = rowX n) (hr : ∀ i, r (i + 1) = runB N (prevIn vs i) (vs i) (r i))
    (hT : ∀ i, T i + (n + 1) * D ≤ T (i + 1))
    (c : Nat → Fin n → Bool) (σ : Nat → Fin n → Bool)
    (hc : ∀ i t, T i ≤ t → t < T (i + 1) → c t = vs i) (hD : Stale N c σ D)
    (i : Nat) (w : Fin n) (v : Bool) (hv : rget (runA N (prevIn vs i) (vs i) (r i)) w = ofBool v) :
    ∀ t, T i ≤ t → t < T (i + 1) → σ t w = v := by
  intro t h1 h2
  have h := (chain_phases N D vs T r hr0 hr hT c σ hc hD i).1 t h1 h2 w
  rw [hv] at h
  exact ofBool_inj.mp (ofBool_le_iff.mp h)

/-- **Settles in a chained phase**: a wire binary `v` in the B row `r (i+1)` is
`v` from `T i + n D` to the end of phase `i`. -/
theorem chain_settles
    (hr0 : r 0 = rowX n) (hr : ∀ i, r (i + 1) = runB N (prevIn vs i) (vs i) (r i))
    (hT : ∀ i, T i + (n + 1) * D ≤ T (i + 1))
    (c : Nat → Fin n → Bool) (σ : Nat → Fin n → Bool)
    (hc : ∀ i t, T i ≤ t → t < T (i + 1) → c t = vs i) (hD : Stale N c σ D)
    (i : Nat) (w : Fin n) (v : Bool) (hv : rget (r (i + 1)) w = ofBool v) :
    ∀ t, T i + n * D ≤ t → t < T (i + 1) → σ t w = v := by
  intro t h1 h2
  have h := (chain_phases N D vs T r hr0 hr hT c σ hc hD i).2 t h1 h2 w
  rw [hv] at h
  exact ofBool_inj.mp (ofBool_le_iff.mp h)

end Formal.Core.XAudit.SoundChain
