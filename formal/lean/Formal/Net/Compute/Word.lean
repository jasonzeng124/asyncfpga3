import Formal.Net.Compute.Basic

/-!
# H_COMPUTE_FN, part 2: words, and bit-local units

* `inEnv xs`: input port `p` carries the number `xs[p]` (bit `k` on leaf `.inp p k`).
* `unitVal cells outs xs`: the number the unit's output bits form (`outs[0]` the LSB).
* `testBit_unitVal`: bit `i` of it is the evaluation of output wire `i`.
* `BitLocal`: a decidable per-bit certificate (for every output bit, a local check over a leaf
  list covering its support). `bitLocal_sound` turns it into a per-bit statement for every
  environment.
-/

namespace Formal.Net.Compute

/-- Port `p` carries `xs[p]`; cut leaves are unused (false). -/
def inEnv (xs : List Nat) : Leaf → Bool
  | .inp p k => (xs.getD p 0).testBit k
  | .cut _ => false

/-- The number whose bit `i` is `f i`, for `i < n`. -/
def word (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => word f n ||| (if f n then 2 ^ n else 0)

theorem testBit_word (f : Nat → Bool) : ∀ n i, (word f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [word]
  | n + 1, i => by
    simp only [word, Nat.testBit_or, testBit_word f n i]
    by_cases hf : f n
    · simp only [hf, if_true, Nat.testBit_two_pow]
      by_cases hi : i = n
      · subst hi; simp [hf]
      · have : (n = i) = False := propext ⟨fun h => hi h.symm, False.elim⟩
        simp only [this, decide_false, Bool.or_false]
        by_cases h2 : i < n
        · simp [h2, show i < n + 1 by omega]
        · simp [h2, show ¬ i < n + 1 by omega]
    · simp only [hf, Bool.false_eq_true, if_false, Nat.zero_testBit, Bool.or_false]
      by_cases hi : i = n
      · subst hi; simp [hf]
      · by_cases h2 : i < n
        · simp [h2, show i < n + 1 by omega]
        · simp [h2, show ¬ i < n + 1 by omega]

/-- The net of output wire `i` (0 if it is not a net). -/
def outNet (outs : List W) (i : Nat) : Nat :=
  match outs.getD i .c0 with
  | .net n => n
  | _ => 0

/-- The unit's output as a number. -/
def unitVal (cells : List Cell) (outs : List W) (xs : List Nat) : Nat :=
  word (fun i => eval (inEnv xs) [] cells (outs.getD i .c0)) outs.length

theorem testBit_unitVal (cells : List Cell) (outs : List W) (xs : List Nat) (i : Nat) :
    (unitVal cells outs xs).testBit i =
      (decide (i < outs.length) && eval (inEnv xs) [] cells (outs.getD i .c0)) :=
  testBit_word _ _ _

/-- A per-output-bit certificate: output bit `i`, with leaf list `S i` and spec `spec i`,
passes the exhaustive check and `S i` covers its support. -/
def BitLocal (cells : List Cell) (outs : List W) (S : Nat → List Leaf)
    (spec : Nat → List Bool → Bool) : Prop :=
  ∀ i, i < outs.length → LocalOK [] cells (outs.getD i .c0) (S i) (spec i) ∧
    (S i).Nodup ∧ (swOf [] cells (outs.getD i .c0)).all (fun l => decide (l ∈ S i)) = true

instance (cells : List Cell) (outs : List W) (S : Nat → List Leaf)
    (spec : Nat → List Bool → Bool) : Decidable (BitLocal cells outs S spec) := by
  unfold BitLocal; exact Nat.decidableBallLT _ _

theorem bitLocal_sound {cells : List Cell} {outs : List W} {S : Nat → List Leaf}
    {spec : Nat → List Bool → Bool} (h : BitLocal cells outs S spec) {i : Nat}
    (hi : i < outs.length) (env : Leaf → Bool) :
    eval env [] cells (outs.getD i .c0) = spec i ((S i).map env) := by
  obtain ⟨hok, hnd, hsup⟩ := h i hi
  exact local_sound hok hnd (fun l hl => by
    have := List.all_eq_true.mp hsup l hl
    simpa using this) env

/-- A net checked exhaustively on its cone (cut set `C`, leaves `S` covering the support). -/
def NetOK (cells : List Cell) (C : List Nat) (n : Nat) (S : List Leaf) (spec : List Bool → Bool) :
    Prop :=
  LocalOK C (filt cells [n]).1 (.net n) S spec ∧ S.Nodup ∧
    (swOf C (filt cells [n]).1 (.net n)).all (fun l => decide (l ∈ S)) = true

instance (cells : List Cell) (C : List Nat) (n : Nat) (S : List Leaf) (spec : List Bool → Bool) :
    Decidable (NetOK cells C n S spec) := by unfold NetOK; exact inferInstance

/-- The cut environment: input bits from `env`, cut leaves carry the REAL net values. -/
def cutEnv (env : Leaf → Bool) (cells : List Cell) : Leaf → Bool := fun l => match l with
  | .inp p k => env (.inp p k)
  | .cut m => run env [] cells (fun _ => false) m

/-- **A checked net's real value.** A passing local check of net `n` on its cone, with any cut
set `C`, over a duplicate-free leaf list covering the cone's support, gives the real value of
`n` as `spec` of the leaf values, where cut leaves carry the real values of their nets. -/
theorem cert_val {cells : List Cell} {C : List Nat} {n : Nat} {S : List Leaf}
    {spec : List Bool → Bool} (hnd : (cells.flatMap Cell.outs).Nodup)
    (hok : LocalOK C (filt cells [n]).1 (.net n) S spec) (hS : S.Nodup)
    (hsup : (swOf C (filt cells [n]).1 (.net n)).all (fun l => decide (l ∈ S)) = true)
    (env : Leaf → Bool) :
    run env [] cells (fun _ => false) n = spec (S.map (cutEnv env cells)) := by
  have hcut := cut_sound env (cutEnv env cells) C (fun _ _ => rfl) cells (fun _ => false) hnd
    (fun _ _ => rfl) n
  have h1 : eval (cutEnv env cells) C cells (.net n) = run env [] cells (fun _ => false) n := hcut
  rw [← h1, eval_filt]
  exact local_sound hok hS (fun l hl => by simpa using List.all_eq_true.mp hsup l hl) _

end Formal.Net.Compute

/-! ## Splitting a large exhaustive check (kernel memory) -/

namespace Formal.Net.Compute

/-- The local check restricted to the assignments `lo, lo+1, …, lo+n-1`. -/
def LocalOKR (C : List Nat) (cells : List Cell) (w : W) (S : List Leaf)
    (spec : List Bool → Bool) (lo n : Nat) : Prop :=
  ∀ m, m < n → eval (envOf S (lo + m)) C cells w = spec (S.map (envOf S (lo + m)))

instance (C : List Nat) (cells : List Cell) (w : W) (S : List Leaf) (spec : List Bool → Bool)
    (lo n : Nat) : Decidable (LocalOKR C cells w S spec lo n) := by
  unfold LocalOKR; exact Nat.decidableBallLT _ _

theorem localOK_of_ranges {C : List Nat} {cells : List Cell} {w : W} {S : List Leaf}
    {spec : List Bool → Bool} (K B : Nat) (hKB : K * B = 2 ^ S.length)
    (h : ∀ c, c < K → LocalOKR C cells w S spec (c * B) B) : LocalOK C cells w S spec := by
  intro m hm
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hKB; exact absurd hKB (Nat.ne_of_lt (Nat.two_pow_pos _))
    · exact h0
  have hc : m / B < K := by
    apply (Nat.div_lt_iff_lt_mul hB).mpr; rw [hKB]; exact hm
  have := h (m / B) hc (m % B) (Nat.mod_lt _ hB)
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

end Formal.Net.Compute
