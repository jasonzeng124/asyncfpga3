import Formal.Cells.ZeroDelayNet

/-!
# ZeroDelayNetTok: k tokens (partial): pulse trains, C's protocol, one retiming across tokens

Probe Bzd2 (shard B); note `formal/notes/B-zero-delay-net.md`. Goal 3 of the probe (the link
chain with `k` tokens) is only PARTLY done here; what checks:

* `train`: a wire carrying `k` four-phase tokens (rises `ru j`, falls `rf j`), the `k`-token
  generalisation of Bzd's `tokA`. `train_move` (it moves only at its own edges) and `train_at`
  (inside token `j`'s zone it IS `tokA (ru j) (rf j)`), under the wire order `WOrd`.
* `proto_train`: C's `Protocol` for a `k`-token channel whose edges interleave
  (`req↑ < ack↑ < req↓ < ack↓ < next req↑`).
* `key_mono_family`: the key retiming of `ZeroDelayNet` applied to ANY family of event windows,
  tokens included (index = token × event), is monotone across tokens as well as within one:
  the only requirement is `T ≤ lo ≤ hi` and depth `< D`.

NOT done (open, see the note): C's `Link` for the `k`-token chain run, and the physical
`k`-token stage (LinkExact's `Spec` is one token; a second token needs the node to read the
previous acknowledge fall before the next request rise, a cross-token race that is not one of
the six `bd_link.stage` rows, and a multi-token latch capture, which `LibGapLatch.EnTok` does
not express). Core Lean only.
-/

namespace Formal.Cells.ZeroDelayNet
open Formal.Cells
open Formal.Cells.ZeroDelayRefine
open Formal.Net (Trace)
open Formal.Net.Handshake (Chan Protocol SendStep RecvStep)

/-- A wire carrying `k` tokens: high on `(ru j, rf j]` for each `j < k`. -/
def train (ru rf : Nat → Nat) (k : Nat) (n : Nat) : Bool :=
  decide (∃ j, j < k ∧ tokA (ru j) (rf j) n = true)

/-- **Wire order**: each token's pulse is nonempty and every token's fall precedes every later
token's rise. -/
def WOrd (ru rf : Nat → Nat) (k : Nat) : Prop :=
  (∀ a < k, ru a < rf a) ∧ (∀ a b, a < b → b < k → rf a < ru b)

theorem train_move {ru rf : Nat → Nat} {k t : Nat} (h : train ru rf k (t + 1) ≠ train ru rf k t) :
    ∃ j < k, t = ru j ∨ t = rf j := by
  refine Classical.byContradiction fun hc => h ?_
  have e : ∀ j, j < k → tokA (ru j) (rf j) (t + 1) = tokA (ru j) (rf j) t := by
    intro j hj
    refine Classical.byContradiction fun hm => hc ⟨j, hj, tA_move hm⟩
  unfold train
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (e j hj) ▸ hv⟩
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (e j hj).symm ▸ hv⟩

/-- **Inside token `j`'s zone the train is token `j`'s pulse.** -/
theorem train_at {ru rf : Nat → Nat} {k j n : Nat} (W : WOrd ru rf k) (hj : j < k)
    (lo : j = 0 ∨ rf (j - 1) < n) (hi : j + 1 = k ∨ n ≤ ru (j + 1)) :
    train ru rf k n = tokA (ru j) (rf j) n := by
  have h1 := W.1; have h2 := W.2
  unfold train
  cases hv : tokA (ru j) (rf j) n
  · apply decide_eq_false
    rintro ⟨j', hj', hv'⟩
    simp only [tokA, decide_eq_true_eq] at hv'
    rcases Nat.lt_trichotomy j' j with hl | rfl | hl
    · rcases lo with lo | lo
      · omega
      · have : rf j' ≤ rf (j - 1) := by
          rcases Nat.lt_or_ge j' (j - 1) with h | h
          · have := h2 j' (j - 1) h (by omega); have := h1 (j - 1) (by omega); omega
          · have : j' = j - 1 := by omega
            subst this; omega
        omega
    · simp only [tokA, decide_eq_false_iff_not] at hv; exact hv hv'
    · rcases hi with hi | hi
      · omega
      · have : ru (j + 1) ≤ ru j' := by
          rcases Nat.lt_or_ge (j + 1) j' with h | h
          · have := h2 (j + 1) j' h hj'; have := h1 (j + 1) (by omega); omega
          · have : j' = j + 1 := by omega
            subst this; omega
        omega
  · exact decide_eq_true ⟨j, hj, hv⟩

/-- **C's protocol for a `k`-token channel** whose edges interleave: for each token
`req↑ < ack↑ < req↓ < ack↓`, and each token's `ack↓` precedes the next token's `req↑`. -/
theorem proto_train {a b c d : Nat → Nat} {k : Nat}
    (h1 : ∀ j < k, a j < b j) (h2 : ∀ j < k, b j < c j) (h3 : ∀ j < k, c j < d j)
    (h4 : ∀ j, j + 1 < k → d j < a (j + 1)) (dat : Nat → Nat) :
    Protocol ⟨train a c k, train b d k, dat⟩ := by
  -- every edge of token j precedes every edge of token j' > j
  have mono : ∀ j j', j < j' → j' < k → d j < a j' := by
    intro j j' hjj' hk
    induction j' with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge j m with h | h
      · have := ih h (by omega); have := h1 m (by omega); have := h2 m (by omega)
        have := h3 m (by omega); have := h4 m hk; omega
      · have : j = m := by omega
        subst this; exact h4 j hk
  have Wr : WOrd a c k := ⟨fun j hj => by have := h1 j hj; have := h2 j hj; omega,
    fun x y hxy hy => by have := mono x y hxy hy; have := h3 x (by omega); omega⟩
  have Wa : WOrd b d k := ⟨fun j hj => by have := h2 j hj; have := h3 j hj; omega,
    fun x y hxy hy => by have := mono x y hxy hy; have := h1 y hy; omega⟩
  have z : ∀ (ru rf : Nat → Nat), train ru rf k 0 = false := fun ru rf => by
    unfold train; apply decide_eq_false; rintro ⟨j, -, hv⟩; simp [tokA] at hv
  refine ⟨⟨z _ _, z _ _⟩, fun t => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · obtain ⟨j, hj, e | e⟩ := train_move hm <;> subst e <;>
      have := h1 j hj <;> have := h2 j hj <;> have := h3 j hj
    · -- req rises at a j: both low there
      have lo : j = 0 ∨ c (j - 1) < a j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; have := h3 m (by omega); simp; omega
      have lo' : j = 0 ∨ d (j - 1) < a j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; simp; omega
      have hi : j + 1 = k ∨ a j ≤ a (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := mono j (j + 1) (by omega) h; omega
        · left; omega
      have hi' : j + 1 = k ∨ a j ≤ b (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := mono j (j + 1) (by omega) h; have := h1 (j + 1) h; omega
        · left; omega
      show train a c k (a j) = train b d k (a j)
      rw [train_at Wr hj lo hi, train_at Wa hj lo' hi', tA_f1 (Nat.le_refl _), tA_f1 (by omega)]
    · -- req falls at c j: both high there
      have lo : j = 0 ∨ c (j - 1) < c j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; have := h3 m (by omega); simp; omega
      have lo' : j = 0 ∨ d (j - 1) < c j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; simp; omega
      have hi : j + 1 = k ∨ c j ≤ a (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := mono j (j + 1) (by omega) h; omega
        · left; omega
      have hi' : j + 1 = k ∨ c j ≤ b (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := mono j (j + 1) (by omega) h; have := h1 (j + 1) h; omega
        · left; omega
      show train a c k (c j) = train b d k (c j)
      rw [train_at Wr hj lo hi, train_at Wa hj lo' hi', tA_t (by omega) (Nat.le_refl _),
        tA_t (by omega) (by omega)]
  · obtain ⟨j, hj, e | e⟩ := train_move hm <;> subst e <;>
      have := h1 j hj <;> have := h2 j hj <;> have := h3 j hj
    · -- ack rises at b j: req high there
      have lo : j = 0 ∨ c (j - 1) < b j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; have := h3 m (by omega); simp; omega
      have lo' : j = 0 ∨ d (j - 1) < b j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; simp; omega
      have hi : j + 1 = k ∨ b j ≤ a (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := mono j (j + 1) (by omega) h; omega
        · left; omega
      have hi' : j + 1 = k ∨ b j ≤ b (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := mono j (j + 1) (by omega) h; have := h1 (j + 1) h; omega
        · left; omega
      show train b d k (b j) ≠ train a c k (b j)
      rw [train_at Wr hj lo hi, train_at Wa hj lo' hi', tA_f1 (Nat.le_refl _),
        tA_t (by omega) (by omega)]
      decide
    · -- ack falls at d j: req low there
      have lo : j = 0 ∨ c (j - 1) < d j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; have := h3 m (by omega); simp; omega
      have lo' : j = 0 ∨ d (j - 1) < d j := by
        rcases j with _ | m
        · exact Or.inl rfl
        · right; have := h4 m hj; simp; omega
      have hi : j + 1 = k ∨ d j ≤ a (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := h4 j h; omega
        · left; omega
      have hi' : j + 1 = k ∨ d j ≤ b (j + 1) := by
        rcases Nat.lt_or_ge (j + 1) k with h | h
        · right; have := h4 j h; have := h1 (j + 1) h; omega
        · left; omega
      show train b d k (d j) ≠ train a c k (d j)
      rw [train_at Wr hj lo hi, train_at Wa hj lo' hi', tA_t (by omega) (Nat.le_refl _),
        tA_f2 (by omega)]
      decide

/-- **One retiming across tokens.** For ANY family of physical event windows (e.g. indexed by
token × event) whose steps are key steps `key T D lo d` with `T ≤ lo ≤ hi` and `d < D`, the
retiming is monotone over the whole family: an event of token `j` that surely precedes an event
of token `j'` gets the earlier step, whatever `j, j'`. -/
theorem key_mono_family {ι : Type} (ok : ι → Prop) (T : Int) (D : Nat) (w : ι → Ev)
    (dep : ι → Nat) (hT : ∀ p, ok p → T ≤ (w p).lo) (hw : ∀ p, ok p → (w p).lo ≤ (w p).hi)
    (hd : ∀ p, ok p → dep p < D) :
    MonoF ok (fun p => (w p, key T D (w p).lo (dep p))) := by
  intro p q hp hq hlt
  have := hw p hp
  exact key_mono (hT p hp) (by simp only at hlt; omega) (hd p hp)

end Formal.Cells.ZeroDelayNet
