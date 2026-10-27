import Formal.Net.Kahn

/-!
# The gcd kernel's main loop as a Kahn dataflow graph (probe C-8b)

Core Lean only.

## The C source
Dynamatic's `integration-test/gcd/gcd.c` (its CF lowering is in
`cloud/fixtures/frontend/gcd/comp/cf_transformed.mlir`; a Python transcription
is `cells/hw/uniform_oracle.py:k_gcd`). It is BINARY gcd (Stein):
```
if (a == 0) return b;  if (b == 0) return a;
k = 0; while (((a | b) & 1) == 0) { a >>= 1; b >>= 1; k++; }   // bb3
while (a > 0 && (a & 1) == 0) a >>= 1;                          // bb5
while (b > 0 && (b & 1) == 0) b >>= 1;                          // bb7
while (a != 0) {                                                // bb8..bb11
  diff = a - b; if (a < b) b = a; a = diff >= 0 ? diff : -diff;
  while (a > 0 && (a & 1) == 0) a >>= 1;
}
return b << k;
```
`gcdC` transcribes all of it (fuelled loops are not needed except the main
loop, whose termination is the interesting part); `gcdC_eq` proves it is
`Nat.gcd` for ALL natural inputs. `cLoop` is the main loop alone.

## The graph
`G` is the main loop (bb10 header, bb11 strip, bb9 min/test) as a Kahn graph:
mux loop header with an initial select token, a test, two `cond_br`s, forks,
and two operator nodes (`|a-b|` then strip, and `min`). The inner strip loop
(bb11) is ONE operator node here (`strip2`), not a nested loop: see the notes.

`G` is well-formed (`G_wf`), so every schedule that completes ends in the same
store; `run_of_cLoop` exhibits one such schedule from the initial store, for
every input on which the C loop terminates, ending with `[cLoop result]` on
`out`. Hence (`dataflow_eq_cLoop`) EVERY complete run's output is the C loop's
result, and (`dataflow_gcd`) on the loop's entry condition that is `Nat.gcd`.

## Values
Values are `Nat`. The C uses `int32`; for inputs in `[0, 2^31)` every
intermediate value lies in `[0, max a b]`, so no operation wraps and the signed
comparisons agree with `Nat` ones. That is the hypothesis H_NONNEG31 of the
notes; it is not proved here (no BitVec model).
-/

namespace Formal.Net.Kahn.Gcd

open Formal.Net.Kahn

/-! ## The C kernel as Lean functions -/

/-- `while (a > 0 && (a & 1) == 0) a >>= 1;` -/
def strip2 (n : Nat) : Nat :=
  if 0 < n ∧ n % 2 = 0 then strip2 (n / 2) else n
termination_by n
decreasing_by omega

/-- `diff = a - b; a = diff >= 0 ? diff : -diff` on non-negative values. -/
def absdiff (a b : Nat) : Nat := if b ≤ a then a - b else b - a

/-- The main loop (bb8-bb11), fuelled: `none` means the fuel ran out. -/
def cLoop : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, a, b => if a = 0 then some b else cLoop f (strip2 (absdiff a b)) (min a b)

/-- `k = 0; while (((a | b) & 1) == 0) { a >>= 1; b >>= 1; k++; }` for `a > 0`
(the C reaches it only with `a, b ≠ 0`; the `0 < a` conjunct is what makes the
Lean definition total and is always true there). -/
def shared (a b k : Nat) : Nat × Nat × Nat :=
  if 0 < a ∧ a % 2 = 0 ∧ b % 2 = 0 then shared (a / 2) (b / 2) (k + 1) else (a, b, k)
termination_by a
decreasing_by omega

/-- The whole C function. -/
def gcdC (a b : Nat) : Option Nat :=
  if a = 0 then some b else if b = 0 then some a else
    let p := shared a b 0
    let a2 := strip2 p.1
    let b2 := strip2 p.2.1
    (cLoop (a2 + b2 + 1) a2 b2).map (fun r => r <<< p.2.2)

/-! ## Arithmetic: the C function is `Nat.gcd` -/

theorem coprime_two {m : Nat} (hm : m % 2 = 1) : Nat.gcd 2 m = 1 := by
  rw [Nat.gcd_rec, hm]; rfl

theorem gcd_strip2 (n m : Nat) (hm : m % 2 = 1) : Nat.gcd (strip2 n) m = Nat.gcd n m := by
  rw [strip2]
  split
  · rename_i h
    rw [gcd_strip2 (n / 2) m hm]
    have e : n = 2 * (n / 2) := by omega
    conv => rhs; rw [e]
    exact (Nat.Coprime.gcd_mul_left_cancel (n / 2) (coprime_two hm)).symm
  · rfl
termination_by n
decreasing_by omega

theorem strip2_le (n : Nat) : strip2 n ≤ n := by
  rw [strip2]; split
  · have := strip2_le (n / 2); omega
  · exact Nat.le_refl _
termination_by n
decreasing_by omega

theorem strip2_odd (n : Nat) : strip2 n = 0 ∨ strip2 n % 2 = 1 := by
  rw [strip2]; split
  · exact strip2_odd (n / 2)
  · omega
termination_by n
decreasing_by omega

theorem strip2_pos {n : Nat} (h : 0 < n) : 0 < strip2 n := by
  rw [strip2]; split
  · exact strip2_pos (n := n / 2) (by omega)
  · exact h
termination_by n
decreasing_by omega

theorem strip2_of_odd {n : Nat} (h : n % 2 = 1) : strip2 n = n := by
  rw [strip2]; split
  · omega
  · rfl

theorem absdiff_min {a b : Nat} (ha : 0 < a) (hb : 0 < b) : absdiff a b + min a b < a + b := by
  unfold absdiff; split <;> omega

/-- The C main loop computes `gcd` on its entry condition (`b` odd, `a` odd or
zero), given fuel `a + b + 1`. -/
theorem cLoop_gcd : ∀ f a b, a + b < f → b % 2 = 1 → (a = 0 ∨ a % 2 = 1) →
    cLoop f a b = some (Nat.gcd a b) := by
  intro f
  induction f with
  | zero => intro a b h; omega
  | succ f ih =>
    intro a b hf hb ha
    simp only [cLoop]
    by_cases h0 : a = 0
    · subst h0; simp
    · have hao : a % 2 = 1 := by omega
      simp only [h0, ↓reduceIte]
      have hmin : min a b % 2 = 1 := by
        rcases Nat.le_total a b with h | h
        · rw [Nat.min_eq_left h]; exact hao
        · rw [Nat.min_eq_right h]; exact hb
      have hle := strip2_le (absdiff a b)
      rw [ih (strip2 (absdiff a b)) (min a b) ?_ hmin (strip2_odd _)]
      · rw [gcd_strip2 _ _ hmin]
        unfold absdiff
        split
        · rename_i h; rw [Nat.min_eq_right h, Nat.gcd_sub_self_left h]
        · rename_i h
          rw [Nat.min_eq_left (by omega), Nat.gcd_sub_self_left (by omega), Nat.gcd_comm]
      · have := absdiff_min (Nat.pos_of_ne_zero h0) (show 0 < b by omega)
        omega

theorem shared_spec (a b k : Nat) (ha : 0 < a) (hb : 0 < b) :
    0 < (shared a b k).1 ∧ 0 < (shared a b k).2.1 ∧
    ((shared a b k).1 % 2 = 1 ∨ (shared a b k).2.1 % 2 = 1) ∧
    Nat.gcd a b * 2 ^ k = Nat.gcd (shared a b k).1 (shared a b k).2.1 * 2 ^ (shared a b k).2.2 := by
  rw [shared]
  split
  · rename_i h
    have := shared_spec (a / 2) (b / 2) (k + 1) (by omega) (by omega)
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    rw [← this.2.2.2]
    have ea : a = 2 * (a / 2) := by omega
    have eb : b = 2 * (b / 2) := by omega
    conv => lhs; rw [ea, eb]
    rw [Nat.gcd_mul_left, Nat.pow_succ]
    ac_rfl
  · rename_i h
    refine ⟨ha, hb, ?_, rfl⟩
    simp only; omega
termination_by a
decreasing_by omega

theorem gcd_strip2_both {x y : Nat} (_hx : 0 < x) (hy : 0 < y) (h : x % 2 = 1 ∨ y % 2 = 1) :
    Nat.gcd (strip2 x) (strip2 y) = Nat.gcd x y := by
  rcases strip2_odd y with h0 | hyo
  · have := strip2_pos hy; omega
  rw [gcd_strip2 _ _ hyo, Nat.gcd_comm]
  rcases h with hxo | hyo'
  · rw [gcd_strip2 _ _ hxo, Nat.gcd_comm]
  · rw [strip2_of_odd hyo', Nat.gcd_comm]

/-- The C gcd kernel (as transcribed) returns `Nat.gcd a b` for ALL inputs. -/
theorem gcdC_eq (a b : Nat) : gcdC a b = some (Nat.gcd a b) := by
  unfold gcdC
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp [ha]
  simp only [ha, hb, ↓reduceIte]
  obtain ⟨h1, h2, h3, h4⟩ := shared_spec a b 0 (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
  generalize shared a b 0 = p at h1 h2 h3 h4
  obtain ⟨x, y, k⟩ := p
  simp only at h1 h2 h3 h4
  dsimp only
  have hyo : strip2 y % 2 = 1 := by
    rcases strip2_odd y with h | h
    · have := strip2_pos h2; omega
    · exact h
  rw [cLoop_gcd _ _ _ (by omega) hyo (strip2_odd x)]
  simp only [Option.map_some, Option.some.injEq]
  rw [gcd_strip2_both h1 h2 h3, Nat.shiftLeft_eq, ← h4]
  simp

/-! ## The dataflow graph of the main loop -/

inductive Ch
  | inA | inB | sA | sB | backA | backB | hA | hB | hA1 | hA2 | cnd | cA | cB
  | aT | aF | bT | out | a1 | a2 | b1 | b2
  deriving DecidableEq

inductive Nd
  | muxA | muxB | forkA | isnz | forkC | brA | brB | snkA | forkAT | forkBT | sub | mn
  deriving DecidableEq

/-- Condition encoding: a token `v` means true iff `v ≠ 0`. -/
def tst (v : Nat) : Bool := v != 0

def G : Nd → Node Ch Nat
  | .muxA   => mux .sA .inA .backA .hA tst (by decide) (by decide)
  | .muxB   => mux .sB .inB .backB .hB tst (by decide) (by decide)
  | .forkA  => fork .hA [.hA1, .hA2]
  | .isnz   => op1 .hA1 .cnd (fun x => if x == 0 then 0 else 1)
  | .forkC  => fork .cnd [.cA, .cB, .sA, .sB]
  | .brA    => branch .cA .hA2 .aT .aF tst
  | .brB    => branch .cB .hB .bT .out tst
  | .snkA   => sink .aF
  | .forkAT => fork .aT [.a1, .a2]
  | .forkBT => fork .bT [.b1, .b2]
  | .sub    => op2 .a1 .b1 .backA (fun x y => strip2 (absdiff x y))
  | .mn     => op2 .a2 .b2 .backB min

/-- The unique consumer of each channel (`out` has none: it is the result). -/
def consumer : Ch → Option Nd
  | .inA | .sA | .backA => some .muxA
  | .inB | .sB | .backB => some .muxB
  | .hA => some .forkA | .hA1 => some .isnz | .cnd => some .forkC
  | .cA | .hA2 => some .brA | .cB | .hB => some .brB | .aF => some .snkA
  | .aT => some .forkAT | .bT => some .forkBT
  | .a1 | .b1 => some .sub | .a2 | .b2 => some .mn
  | .out => none

/-- The unique producer of each channel (`inA`, `inB` have none: they are the inputs). -/
def producer : Ch → Option Nd
  | .hA => some .muxA | .hB => some .muxB
  | .hA1 | .hA2 => some .forkA | .cnd => some .isnz
  | .cA | .cB | .sA | .sB => some .forkC
  | .aT | .aF => some .brA | .bT | .out => some .brB
  | .a1 | .a2 => some .forkAT | .b1 | .b2 => some .forkBT
  | .backA => some .sub | .backB => some .mn
  | .inA | .inB => none

theorem ins_consumer (l : Nd) (c : Ch) (h : (G l).ins c) : consumer c = some l := by
  cases l <;> cases c <;>
    simp_all [G, mux, fork, op1, op2, branch, sink, strict, consumer]

theorem outs_producer (l : Nd) (c : Ch) (h : (G l).outs c) : producer c = some l := by
  cases l <;> cases c <;>
    simp_all [G, mux, fork, op1, op2, branch, sink, strict, producer]

theorem G_wf : WF G where
  ins_disj l₁ l₂ c hne h1 h2 := by
    have := (ins_consumer l₁ c h1).symm.trans (ins_consumer l₂ c h2)
    exact hne (Option.some.inj this)
  outs_disj l₁ l₂ c hne h1 h2 := by
    have := (outs_producer l₁ c h1).symm.trans (outs_producer l₂ c h2)
    exact hne (Option.some.inj this)

/-! ## Stores and one loop iteration -/

/-- Initial store: the two arguments, and the loop selects primed to "entry". -/
def init (a b : Nat) : Store Ch Nat := fun
  | .inA => [a] | .inB => [b] | .sA => [0] | .sB => [0] | _ => []

/-- Loop header has fired: `a`, `b` are on the header outputs. -/
def mid (a b : Nat) : Store Ch Nat := fun
  | .hA => [a] | .hB => [b] | _ => []

/-- After the body: next values on the back edges, selects primed to "loop". -/
def top (a b : Nat) : Store Ch Nat := fun
  | .sA => [1] | .sB => [1] | .backA => [a] | .backB => [b] | _ => []

/-- Final store: result on `out`, selects re-primed to "entry" for the next call. -/
def fin (r : Nat) : Store Ch Nat := fun
  | .sA => [0] | .sB => [0] | .out => [r] | _ => []

theorem init_mid (a b : Nat) : Run (step G) (init a b) 2 (mid a b) :=
  exec_run (ls := [.muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem top_mid (a b : Nat) : Run (step G) (top a b) 2 (mid a b) :=
  exec_run (ls := [.muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem mid_top (a b : Nat) :
    Run (step G) (mid (a + 1) b) 9 (top (strip2 (absdiff (a + 1) b)) (min (a + 1) b)) :=
  exec_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .forkAT, .forkBT, .sub, .mn]) rfl
    (fun c => by cases c <;> rfl)

theorem mid_fin (b : Nat) : Run (step G) (mid 0 b) 6 (fin b) :=
  exec_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .snkA]) rfl
    (fun c => by cases c <;> rfl)

theorem fin_terminal (r : Nat) : Terminal (step G) (fin r) := by
  intro l; cases l <;> rfl

/-- For every input on which the C loop terminates, the graph has a complete run
from `init` ending with exactly the C loop's result on `out`. -/
theorem run_of_cLoop : ∀ f a b r, cLoop f a b = some r → ∃ n, Run (step G) (mid a b) n (fin r) := by
  intro f
  induction f with
  | zero => intro a b r h; simp [cLoop] at h
  | succ f ih =>
    intro a b r h
    simp only [cLoop] at h
    by_cases h0 : a = 0
    · subst h0; simp at h; subst h; exact ⟨6, mid_fin b⟩
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨n, hn⟩ := ih _ _ r h
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact ⟨9 + 2 + n, run_trans (run_trans (mid_top a' b) (top_mid _ _)) hn⟩

/-- Kahn for the gcd loop: wherever the C loop terminates with `r`, EVERY complete
firing sequence of the graph (any schedule) ends in `fin r`, i.e. with exactly
`[r]` on `out`; and no schedule can fire more often than that one. -/
theorem dataflow_eq_cLoop {f a b r : Nat} (h : cLoop f a b = some r) :
    (∃ n, Run (step G) (init a b) n (fin r)) ∧
    (∀ m t, Run (step G) (init a b) m t → Terminal (step G) t → t = fin r) ∧
    (∃ N, ∀ m u, Run (step G) (init a b) m u → m ≤ N) := by
  obtain ⟨n, hn⟩ := run_of_cLoop f a b r h
  have hr := run_trans (init_mid a b) hn
  refine ⟨⟨_, hr⟩, fun m t ht hT => (wf_determinate G_wf hr (fin_terminal r) ht hT).1,
    ⟨_, fun m u hu => wf_no_divergence G_wf hr (fin_terminal r) hu⟩⟩

/-- The gcd loop graph computes `Nat.gcd` under the loop's entry condition
(which the C prologue establishes: `b` odd, `a` odd or zero), for any schedule. -/
theorem dataflow_gcd {a b : Nat} (hb : b % 2 = 1) (ha : a = 0 ∨ a % 2 = 1) :
    (∃ n, Run (step G) (init a b) n (fin (Nat.gcd a b))) ∧
    (∀ m t, Run (step G) (init a b) m t → Terminal (step G) t → t .out = [Nat.gcd a b]) ∧
    (∃ N, ∀ m u, Run (step G) (init a b) m u → m ≤ N) := by
  obtain ⟨h1, h2, h3⟩ := dataflow_eq_cLoop (cLoop_gcd (a + b + 1) a b (by omega) hb ha)
  exact ⟨h1, fun m t ht hT => by rw [h2 m t ht hT]; rfl, h3⟩

end Formal.Net.Kahn.Gcd
