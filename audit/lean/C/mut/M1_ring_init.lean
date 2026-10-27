import Formal.Cells.CElemFn

/-!
# Track 9, probe 9a: a ring of `bd_link` controllers needs three stages

The project's rule (CLAUDE.md, `bdc/emit.py` `RING_MIN_STAGES = 3`,
`cells/tb/tb_ring.v`): a closed ring of simple Muller controllers

    c_i = C(c_{i-1}, ~c_{i+1})          (`bd_link_ctl` = one `bd_c2n`)

is dead for `N ≤ 2` and live for `N ≥ 3` when it holds one loop token.

## Model
* Each stage is the real LUT6 of `cells/rtl/bd_ce.v`: `bd_c2n` (comes up 0) or
  `bd_c2n_set` (comes up 1), evaluated through shard B's `lutB` with the
  verbatim INITs (`Formal.Cells.CElemFn`). Wiring is `tb_ring.v`'s:
  `.a(c[i-1]) .b(c[i+1])`; stages `i < K` are `_set`.
* **H_RESET_CLEAN**: `rst` is held until every node has settled to its forced
  value, then released; the state at release is `resetState K`
  (we prove it is the unique value every gate drives while `rst = 1`).
  Testable: tb_ring's HOLD comment documents exactly the failure when it is
  violated (power-up X latched into the feedback).
* **H_SI** (speed independence): after reset, the ring evolves by firing one
  *excited* gate at a time (output flips to its LUT value), in any order.
  Every bounded-delay inertial execution in which no two outputs change at
  the same instant is such an interleaving, so: a deadlock here (no excited
  gate) is a deadlock under every delay assignment (nothing can ever move),
  and the safety/liveness facts hold under every delay assignment for which
  an excited gate eventually fires. We also prove the ring is *persistent*
  (an excited gate is never disabled by another firing), which is the
  condition for an inertial-delay implementation to be hazard-free.
  H_SI is faithful to the fabric only to the extent that the LUT is a
  glitch-free single-output gate on a single-input change (shard A/B's
  Kleene results) and its feedback net is settled (`H_FB_SETTLED`, probe 5a).

## Tokens
`tok s i := c_{i-1} ≠ c_i` is a *wavefront* at stage `i`. Firing `i` needs a
wavefront at `i` and none at `i+1` and moves it from `i` to `i+1`. A four-phase
data token is two wavefronts (its `req↑` and its `req↓`): the reset state with
`0 < K < N` stages set has exactly `D = 2` wavefronts, i.e. one loop token
("half a token per stage"). Results:
* `dead_of_le_two`: `N ≤ 2` → no gate is ever excited, from ANY state.
* `D_reach`: wavefront count is invariant (safety: tokens neither lost nor
  duplicated).
* `live_iff`: for `N ≥ 3`, a state has an excited gate iff `0 < D < N`.
* `ring_three`: from reset with `0 < K < N`, every reachable state has an
  excited gate iff `N ≥ 3`.
* `k_tokens`: with `D = 2k`, `k ≥ 1`, reachable states are live iff
  `N ≥ 2k+1`. So the "3" is `2·1+1`; `k` loop tokens need `2k+1` stages.
* `fair_window`: (bounded progress) in any execution where stage `i` never
  fires, at most `N(N-1)/2` transitions happen; so every window of
  `N(N-1)/2 + 1` transitions fires every stage.
-/

namespace Formal.Net.Ring
open Formal.Cells Formal.Cells.CElemFn

abbrev State := Nat → Bool
-- MUTANT M1: bd_c2n INIT bit 0 flipped (0x00B2.. -> 0x00B3..)
def c2nBm (a b q rst : Bool) : Bool := lutB 0x00B300B300B300B3 [a, b, q, rst, false, false]

def prv (n i : Nat) : Nat := (i + n - 1) % n
def nxt (n i : Nat) : Nat := (i + 1) % n

/-- Stage `i` of `tb_ring.v`'s `ring #(N, K)`: the real LUT. -/
def gate (n K : Nat) (rst : Bool) (s : State) (i : Nat) : Bool :=
  if i < K then c2nsetB (s (prv n i)) (s (nxt n i)) (s i) rst
  else c2nBm (s (prv n i)) (s (nxt n i)) (s i) rst

/-- The controller's run-mode function, read as an SR latch: set on a·~b,
reset on ~a·b, hold on a tie. -/
def ctl (a b q : Bool) : Bool :=
  if a && !b then true else if !a && b then false else q

theorem c2n_run : ∀ a b q : Bool, c2nBm a b q false = ctl a b q := by decide
theorem c2nset_run : ∀ a b q : Bool, c2nsetB a b q false = ctl a b q := by decide
theorem c2n_rst : ∀ a b q : Bool, c2nBm a b q true = false := by decide
theorem c2nset_rst : ∀ a b q : Bool, c2nsetB a b q true = true := by decide

theorem gate_run (n K : Nat) (s : State) (i : Nat) :
    gate n K false s i = ctl (s (prv n i)) (s (nxt n i)) (s i) := by
  unfold gate; split <;> simp [c2n_run, c2nset_run]

/-- First `K` stages come up holding (`bd_c2n_set`), the rest empty. -/
def resetState (K : Nat) : State := fun j => decide (j < K)

/-- While `rst = 1` every gate drives its reset value whatever the ring holds,
so `resetState K` is the unique state the ring can be in at release
(H_RESET_CLEAN). -/
theorem gate_rst (n K : Nat) (s : State) (i : Nat) :
    gate n K true s i = resetState K i := by
  unfold gate resetState; split <;> simp_all [c2n_rst, c2nset_rst]

theorem ctl_ne_iff : ∀ a b q : Bool, ctl a b q ≠ q ↔ (a ≠ q ∧ b = q) := by decide

/-! ## The transition system (H_SI) -/

def excited (n : Nat) (s : State) (i : Nat) : Prop :=
  i < n ∧ ctl (s (prv n i)) (s (nxt n i)) (s i) ≠ s i

/-- The run-mode excitation is that of the real LUT, for either reset polarity. -/
theorem excited_gate (n K : Nat) (s : State) (i : Nat) :
    excited n s i ↔ i < n ∧ gate n K false s i ≠ s i := by
  rw [gate_run]; rfl

def fire (s : State) (i : Nat) : State := fun j => if j = i then !s i else s j

inductive Reach (n : Nat) (s0 : State) : State → Prop
  | refl : Reach n s0 s0
  | step {s : State} (i : Nat) : Reach n s0 s → excited n s i → Reach n s0 (fire s i)

theorem excited_iff (n : Nat) (s : State) (i : Nat) :
    excited n s i ↔ i < n ∧ s (prv n i) ≠ s i ∧ s (nxt n i) = s i := by
  unfold excited; rw [ctl_ne_iff]

/-! ## N ≤ 2: dead from every state -/

theorem prv_eq_nxt_of_le_two {n i : Nat} (hn : n ≤ 2) (hi : i < n) :
    prv n i = nxt n i := by
  unfold prv nxt
  have : n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl
  · have : i = 0 := by omega
    subst this; rfl
  · have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> rfl

theorem dead_of_le_two {n : Nat} (hn : n ≤ 2) (s : State) (i : Nat) :
    ¬ excited n s i := by
  rw [excited_iff]
  rintro ⟨hi, h1, h2⟩
  rw [prv_eq_nxt_of_le_two hn hi] at h1
  exact h1 h2

/-- Hence the only state reachable from anything is itself. -/
theorem reach_le_two {n : Nat} (hn : n ≤ 2) {s0 s : State} (h : Reach n s0 s) :
    s = s0 := by
  induction h with
  | refl => rfl
  | step i _ he _ => exact absurd he (dead_of_le_two hn _ i)

/-! ## Index arithmetic on the ring -/

theorem nxt_eq {n i : Nat} (hi : i < n) : nxt n i = if i + 1 < n then i + 1 else 0 := by
  unfold nxt
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · have : i + 1 = n := by omega
    rw [this, Nat.mod_self]

theorem prv_eq {n i : Nat} (hi : i < n) : prv n i = if i = 0 then n - 1 else i - 1 := by
  unfold prv
  split
  · subst ‹i = 0›; rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · have : i + n - 1 = (i - 1) + n := by omega
    rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)

theorem nxt_lt {n i : Nat} (hi : i < n) : nxt n i < n := by
  rw [nxt_eq hi]; split <;> omega
theorem prv_lt {n i : Nat} (hi : i < n) : prv n i < n := by
  rw [prv_eq hi]; split <;> omega
theorem nxt_prv {n i : Nat} (hi : i < n) : nxt n (prv n i) = i := by
  rw [nxt_eq (prv_lt hi), prv_eq hi]; split <;> split <;> omega
theorem prv_nxt {n i : Nat} (hi : i < n) : prv n (nxt n i) = i := by
  rw [prv_eq (nxt_lt hi), nxt_eq hi]; split <;> split <;> omega
theorem nxt_ne {n i : Nat} (hn : 2 ≤ n) (hi : i < n) : nxt n i ≠ i := by
  rw [nxt_eq hi]; split <;> omega
theorem prv_ne {n i : Nat} (hn : 2 ≤ n) (hi : i < n) : prv n i ≠ i := by
  rw [prv_eq hi]; split <;> omega

/-! ## Wavefronts -/

def tok (n : Nat) (s : State) (i : Nat) : Bool := s (prv n i) != s i

theorem tok_iff (n : Nat) (s : State) (i : Nat) : tok n s i = true ↔ s (prv n i) ≠ s i := by
  unfold tok; simp

theorem excited_tok {n : Nat} (hn : 3 ≤ n) (s : State) {i : Nat} (hi : i < n) :
    excited n s i ↔ tok n s i = true ∧ tok n s (nxt n i) = false := by
  rw [excited_iff]
  unfold tok
  rw [prv_nxt hi]
  cases s (prv n i) <;> cases s i <;> cases s (nxt n i) <;> simp [hi]

/-- Firing `i` moves the wavefront from `i` to `i+1` and touches nothing else. -/
theorem tok_fire {n : Nat} (hn : 3 ≤ n) {s : State} {i : Nat} (he : excited n s i)
    {j : Nat} (hj : j < n) :
    tok n (fire s i) j = if j = i then false else if j = nxt n i then true else tok n s j := by
  have hi := he.1
  rw [excited_iff] at he
  obtain ⟨_, h1, h2⟩ := he
  unfold tok
  by_cases hji : j = i
  · subst hji
    have := prv_ne (by omega) hi
    simp [fire, this]
    revert h1; cases s (prv n j) <;> cases s j <;> simp
  · by_cases hjn : j = nxt n i
    · subst hjn
      rw [prv_nxt hi]
      have := nxt_ne (n := n) (by omega) hi
      simp [fire, this, h2]
    · have hp : prv n j ≠ i := by
        intro h; apply hjn; rw [← h, nxt_prv hj]
      simp [fire, hp, hji, hjn]

/-! ## Counting -/

def cnt (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => cnt f m + (if f m then 1 else 0)

theorem cnt_le (f : Nat → Bool) (m : Nat) : cnt f m ≤ m := by
  induction m with
  | zero => simp [cnt]
  | succ m ih => simp only [cnt]; split <;> omega

theorem cnt_ext {f g : Nat → Bool} {m : Nat} (h : ∀ j, j < m → f j = g j) :
    cnt f m = cnt g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [cnt]; rw [ih (fun j hj => h j (by omega)), h m (by omega)]

theorem cnt_pos {f : Nat → Bool} {m : Nat} (h : 0 < cnt f m) : ∃ j, j < m ∧ f j = true := by
  induction m with
  | zero => simp [cnt] at h
  | succ m ih =>
    simp only [cnt] at h
    by_cases hm : f m = true
    · exact ⟨m, by omega, hm⟩
    · simp [hm] at h; obtain ⟨j, hj, hf⟩ := ih h; exact ⟨j, by omega, hf⟩

theorem cnt_lt {f : Nat → Bool} {m : Nat} (h : cnt f m < m) : ∃ j, j < m ∧ f j = false := by
  induction m with
  | zero => simp at h
  | succ m ih =>
    simp only [cnt] at h
    by_cases hm : f m = true
    · simp [hm] at h; obtain ⟨j, hj, hf⟩ := ih h; exact ⟨j, by omega, hf⟩
    · exact ⟨m, by omega, by simpa using hm⟩

theorem cnt_ge_of_true {f : Nat → Bool} {m j : Nat} (hj : j < m) (h : f j = true) :
    0 < cnt f m := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [cnt]
    by_cases hjm : j = m
    · subst hjm; simp [h]
    · have := ih (by omega); omega

theorem cnt_lt_of_false {f : Nat → Bool} {m j : Nat} (hj : j < m) (h : f j = false) :
    cnt f m < m := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [cnt]
    by_cases hjm : j = m
    · subst hjm; simp [h]; have := cnt_le f j; omega
    · have := ih (by omega); split <;> omega

/-- Moving one `true` from `a` to `b` preserves the count. -/
theorem cnt_move {f g : Nat → Bool} {a b : Nat} (hab : a ≠ b)
    (ha : f a = true) (ha' : g a = false) (hb : f b = false) (hb' : g b = true)
    (hrest : ∀ j, j ≠ a → j ≠ b → g j = f j) (m : Nat) :
    cnt g m + (if a < m then 1 else 0) = cnt f m + (if b < m then 1 else 0) := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    simp only [cnt]
    by_cases hma : m = a
    · subst hma
      have : ¬ b = m := fun h => hab h.symm
      simp [ha, ha'] at *
      by_cases hbm : b < m
      · simp [hbm] at ih; have : b < m + 1 := by omega
        simp [hbm, this]; omega
      · have : ¬ b < m + 1 := by omega
        simp [hbm] at ih; simp [this]; omega
    · by_cases hmb : m = b
      · subst hmb
        simp [hb, hb'] at *
        by_cases ham : a < m
        · simp [ham] at ih; have : a < m + 1 := by omega
          simp [this]; omega
        · have : ¬ a < m + 1 := by omega
          simp [ham] at ih; simp [this]; omega
      · rw [hrest m hma hmb]
        have e1 : (a < m + 1) = (a < m) := by
          apply propext; constructor <;> intro <;> omega
        have e2 : (b < m + 1) = (b < m) := by
          apply propext; constructor <;> intro <;> omega
        simp only [e1, e2]
        by_cases ha2 : a < m <;> by_cases hb2 : b < m <;> simp [ha2, hb2] at ih ⊢ <;> omega

/-- Number of wavefronts on the ring. -/
def D (n : Nat) (s : State) : Nat := cnt (tok n s) n

theorem D_fire {n : Nat} (hn : 3 ≤ n) {s : State} {i : Nat} (he : excited n s i) :
    D n (fire s i) = D n s := by
  have hi := he.1
  have hne := nxt_ne (n := n) (by omega) hi
  have hx := (excited_tok hn s hi).1 he
  unfold D
  -- restrict both functions to indices < n
  let g : Nat → Bool := fun j => if j < n then tok n (fire s i) j else false
  let f : Nat → Bool := fun j => if j < n then tok n s j else false
  have hg : cnt (tok n (fire s i)) n = cnt g n := cnt_ext (fun j hj => by simp [g, hj])
  have hf : cnt (tok n s) n = cnt f n := cnt_ext (fun j hj => by simp [f, hj])
  have hnl := nxt_lt hi
  have key := cnt_move (f := f) (g := g) (a := i) (b := nxt n i) (Ne.symm hne)
    (by simp [f, hi, hx.1]) (by simp [g, hi, tok_fire hn he hi])
    (by simp [f, hnl, hx.2]) (by simp [g, hnl, tok_fire hn he hnl, hne])
    (by
      intro j h1 h2
      by_cases hj : j < n
      · simp [g, f, hj, tok_fire hn he hj, h1, h2]
      · simp [g, f, hj]) n
  simp [hi, hnl] at key
  rw [hg, hf]; omega

/-- **Safety**: the wavefront count (twice the loop-token count) is invariant. -/
theorem D_reach {n : Nat} (hn : 3 ≤ n) {s0 s : State} (h : Reach n s0 s) : D n s = D n s0 := by
  induction h with
  | refl => rfl
  | step i _ he ih => rw [D_fire hn he, ih]

/-! ## Liveness: excited ⇔ 0 < D < N -/

theorem mod_succ_nxt (n x : Nat) : (x + 1) % n = nxt n (x % n) := by
  unfold nxt; rw [Nat.mod_add_mod]

theorem live_of_D {n : Nat} (hn : 3 ≤ n) {s : State} (h0 : 0 < D n s) (h1 : D n s < n) :
    ∃ i, excited n s i := by
  obtain ⟨j, hj, htj⟩ := cnt_pos h0
  obtain ⟨k, hk, htk⟩ := cnt_lt h1
  apply Classical.byContradiction
  intro hno
  have prop : ∀ x, x < n → tok n s x = true → tok n s (nxt n x) = true := by
    intro x hx htx
    cases hq : tok n s (nxt n x)
    · exact absurd ⟨x, (excited_tok hn s hx).2 ⟨htx, hq⟩⟩ hno
    · rfl
  have all : ∀ m, tok n s ((j + m) % n) = true := by
    intro m
    induction m with
    | zero => rw [Nat.add_zero, Nat.mod_eq_of_lt hj]; exact htj
    | succ m ih =>
      rw [← Nat.add_assoc, mod_succ_nxt]
      exact prop _ (Nat.mod_lt _ (by omega)) ih
  have := all (k + n - j)
  have e : (j + (k + n - j)) % n = k := by
    have : j + (k + n - j) = k + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  rw [e, htk] at this
  exact Bool.false_ne_true this

theorem D_of_live {n : Nat} (hn : 3 ≤ n) {s : State} {i : Nat} (he : excited n s i) :
    0 < D n s ∧ D n s < n := by
  have hi := he.1
  have hx := (excited_tok hn s hi).1 he
  exact ⟨cnt_ge_of_true hi hx.1, cnt_lt_of_false (nxt_lt hi) hx.2⟩

theorem live_iff {n : Nat} (hn : 3 ≤ n) (s : State) :
    (∃ i, excited n s i) ↔ (0 < D n s ∧ D n s < n) :=
  ⟨fun ⟨_, he⟩ => D_of_live hn he, fun ⟨a, b⟩ => live_of_D hn a b⟩

/-! ## Persistence (no excited gate is ever disabled) -/

theorem persistent {n : Nat} (hn : 3 ≤ n) {s : State} {i j : Nat}
    (hi : excited n s i) (hj : excited n s j) (hij : i ≠ j) : excited n (fire s j) i := by
  have hil := hi.1
  rw [excited_tok hn _ hil]
  have x := (excited_tok hn s hil).1 hi
  have y := (excited_tok hn s hj.1).1 hj
  have hni := nxt_lt hil
  rw [tok_fire hn hj hil, tok_fire hn hj hni]
  -- i ≠ nxt j, else tok i would be both false (from j) and true
  have h1 : i ≠ nxt n j := by intro h; rw [h] at x; rw [x.1] at y; exact Bool.noConfusion y.2
  have h2 : nxt n i ≠ j := by intro h; rw [h] at x; rw [x.2] at y; exact Bool.noConfusion y.1
  have h3 : nxt n i ≠ nxt n j := by
    intro h; apply hij; rw [← prv_nxt hil, h, prv_nxt hj.1]
  simp [hij, h1, h2, h3, x.1, x.2]

/-! ## The reset state holds exactly one loop token -/

theorem tok_reset {n K : Nat} (hK0 : 0 < K) (hKn : K < n) {j : Nat} (hj : j < n) :
    tok n (resetState K) j = (j == 0 || j == K) := by
  unfold tok resetState
  rw [prv_eq hj]
  by_cases h0 : j = 0
  · subst h0; simp; omega
  · by_cases hk : j = K
    · subst hk; simp [h0]; omega
    · have e : (j - 1 < K) = (j < K) := propext (by omega)
      have e0 : (j == 0) = false := by simp [h0]
      have eK : (j == K) = false := by simp [hk]
      rw [if_neg h0, e0, eK]; simp [e]

theorem cnt_two (a b : Nat) (hab : a ≠ b) (m : Nat) :
    cnt (fun j => j == a || j == b) m = (if a < m then 1 else 0) + (if b < m then 1 else 0) := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    simp only [cnt, ih]
    by_cases ha : m = a
    · subst ha
      have : ¬ m = b := hab
      simp [this]
      by_cases hb : b < m
      · have : b < m + 1 := by omega
        simp [hb, this]
      · have : ¬ b < m + 1 := by omega
        simp [hb, this]
    · by_cases hb : m = b
      · subst hb; simp [ha]
        by_cases h : a < m
        · have : a < m + 1 := by omega
          simp [h, this]
        · have : ¬ a < m + 1 := by omega
          simp [h, this]
      · simp [ha, hb]
        have e1 : (a < m + 1) = (a < m) := by
          apply propext; constructor <;> intro <;> omega
        have e2 : (b < m + 1) = (b < m) := by
          apply propext; constructor <;> intro <;> omega
        simp only [e1, e2]

theorem D_reset {n K : Nat} (hK0 : 0 < K) (hKn : K < n) : D n (resetState K) = 2 := by
  unfold D
  rw [cnt_ext (g := fun j => j == 0 || j == K) (fun j hj => tok_reset hK0 hKn hj)]
  rw [cnt_two 0 K (by omega)]; simp [hKn]; omega

/-- K = 0 (all empty) or K ≥ N (all holding): no wavefront, dead (tb_ring's
occupancy sweep ends). -/
theorem D_reset_degenerate {n K : Nat} (h : K = 0 ∨ n ≤ K) : D n (resetState K) = 0 := by
  unfold D
  rw [cnt_ext (g := fun _ => false) (fun j hj => by
    unfold tok resetState; rw [prv_eq hj]
    rcases h with rfl | h
    · simp
    · split <;> simp <;> omega)]
  clear h; induction n with
  | zero => rfl
  | succ n ih => simp [cnt, ih]

/-! ## The rule -/

/-- **The decided rule, proved.** A ring of `N` `bd_link` controllers released
from reset with `K` stages holding (`0 < K < N`, i.e. one loop token) is live
in every reachable state iff `N ≥ 3`; for `N ≤ 2` it is frozen at reset. -/
theorem ring_three (n K : Nat) (hK0 : 0 < K) (hKn : K < n) :
    (∀ s, Reach n (resetState K) s → ∃ i, excited n s i) ↔ 3 ≤ n := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hlt
    obtain ⟨i, hi⟩ := h _ .refl
    exact dead_of_le_two (by omega) _ i hi
  · intro hn s hs
    apply live_of_D hn <;> rw [D_reach hn hs, D_reset hK0 hKn] <;> omega

/-- Safety from reset: one loop token, forever (two wavefronts). -/
theorem ring_safe {n K : Nat} (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n) {s : State}
    (hs : Reach n (resetState K) s) : D n s = 2 := by
  rw [D_reach hn hs, D_reset hK0 hKn]

/-- Empty or full rings never move (tb_ring K=0 and K=N cases). -/
theorem ring_degenerate_dead {n K : Nat} (h : K = 0 ∨ n ≤ K) (i : Nat) :
    ¬ excited n (resetState K) i := by
  intro he
  by_cases hn : 3 ≤ n
  · have := (D_of_live hn he); rw [D_reset_degenerate h] at this; omega
  · exact dead_of_le_two (by omega) _ i he

/-- **k loop tokens need 2k+1 stages.** From any initial state carrying `k ≥ 1`
four-phase tokens (`2k` wavefronts), every reachable state is live iff
`N ≥ 2k+1`. -/
theorem k_tokens (n k : Nat) (hk : 1 ≤ k) (s0 : State) (h0 : D n s0 = 2 * k) :
    (∀ s, Reach n s0 s → ∃ i, excited n s i) ↔ 2 * k + 1 ≤ n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h _ .refl
    by_cases hn : 3 ≤ n
    · have := D_of_live hn hi; omega
    · exact absurd hi (dead_of_le_two (by omega) _ i)
  · intro hn s hs
    have hn3 : 3 ≤ n := by omega
    apply live_of_D hn3 <;> rw [D_reach hn3 hs, h0] <;> omega

/-- A reset pattern carrying `k` tokens: stages `0, 2, …, 2k-2` holding. -/
def kState (k : Nat) : State := fun j => decide (j < 2 * k) && j % 2 == 0

theorem D_kState {n k : Nat} (hk : 1 ≤ k) (hn : 2 * k ≤ n) : D n (kState k) = 2 * k := by
  unfold D
  rw [cnt_ext (g := fun j => decide (j < 2 * k)) (fun j hj => by
    unfold tok kState; rw [prv_eq hj]
    by_cases h0 : j = 0
    · subst h0
      have hk' : 0 < k := by omega
      by_cases hlt : n - 1 < 2 * k
      · have : (n - 1) % 2 = 1 := by omega
        simp [hk', hlt, this]
      · simp [hk', hlt]
    · simp only [h0, if_false]
      by_cases hj2 : j < 2 * k
      · have : j - 1 < 2 * k := by omega
        rcases Nat.mod_two_eq_zero_or_one j with h | h
        · have h' : (j - 1) % 2 = 1 := by omega
          simp [hj2, this, h, h']
        · have h' : (j - 1) % 2 = 0 := by omega
          simp [hj2, this, h, h']
      · by_cases he : j = 2 * k
        · subst he
          have : (2 * k - 1) % 2 = 1 := by omega
          simp [this]
        · have : ¬ j - 1 < 2 * k := by omega
          simp [hj2, this])]
  have : ∀ m, m ≤ 2 * k → cnt (fun j => decide (j < 2 * k)) m = m := by
    intro m; induction m with
    | zero => intro; rfl
    | succ m ih => intro h; simp [cnt, ih (by omega)]; omega
  have h2 : ∀ m, 2 * k ≤ m → cnt (fun j => decide (j < 2 * k)) m = 2 * k := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases e : 2 * k = m + 1
      · rw [← e]; exact this _ (Nat.le_refl _)
      · simp [cnt, ih (by omega)]; omega
  exact h2 n hn

/-- Instance of `k_tokens` that is not vacuous. -/
theorem kState_live_iff (n k : Nat) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (∀ s, Reach n (kState k) s → ∃ i, excited n s i) ↔ 2 * k + 1 ≤ n :=
  k_tokens n k hk _ (D_kState hk hn)

/-! ## Small cases, as tb_ring sweeps them (N = 1..6, K = 1) -/

example : ¬ ∀ s, Reach 1 (resetState 1) s → ∃ i, excited 1 s i := by
  intro h; obtain ⟨i, hi⟩ := h _ .refl; exact dead_of_le_two (by omega) _ i hi
example : ¬ ∀ s, Reach 2 (resetState 1) s → ∃ i, excited 2 s i :=
  fun h => by have := (ring_three 2 1 (by omega) (by omega)).1 h; omega
example : ∀ s, Reach 3 (resetState 1) s → ∃ i, excited 3 s i :=
  (ring_three 3 1 (by omega) (by omega)).2 (by omega)
example : ∀ s, Reach 4 (resetState 1) s → ∃ i, excited 4 s i :=
  (ring_three 4 1 (by omega) (by omega)).2 (by omega)
example : ∀ s, Reach 5 (resetState 1) s → ∃ i, excited 5 s i :=
  (ring_three 5 1 (by omega) (by omega)).2 (by omega)
example : ∀ s, Reach 6 (resetState 1) s → ∃ i, excited 6 s i :=
  (ring_three 6 1 (by omega) (by omega)).2 (by omega)

/-! ## Bounded progress: no stage starves

An execution is the list of stages fired, in order. `nf x is` counts the
firings of stage `x`. -/

def Run (n : Nat) : State → List Nat → Prop
  | _, [] => True
  | s, i :: is => excited n s i ∧ Run n (fire s i) is

def final : State → List Nat → State
  | s, [] => s
  | s, i :: is => final (fire s i) is

def nf (x : Nat) : List Nat → Nat
  | [] => 0
  | i :: is => (if i = x then 1 else 0) + nf x is

def b2n (b : Bool) : Nat := if b then 1 else 0

theorem run_reach {n : Nat} {s0 s : State} (h0 : Reach n s0 s) :
    ∀ {is : List Nat}, Run n s is → Reach n s0 (final s is) := by
  intro is
  induction is generalizing s with
  | nil => intro _; exact h0
  | cons i is ih => intro ⟨he, hr⟩; exact ih (Reach.step i h0 he) hr

/-- Exact firing balance: a wavefront enters `x` only when `prv x` fires and
leaves only when `x` fires. -/
theorem balance {n : Nat} (hn : 3 ≤ n) {x : Nat} (hx : x < n) :
    ∀ (is : List Nat) (s : State), Run n s is →
      nf x is + b2n (tok n (final s is) x) = nf (prv n x) is + b2n (tok n s x) := by
  intro is
  induction is with
  | nil => intro s _; simp [nf, final]
  | cons i is ih =>
    intro s ⟨he, hr⟩
    have := ih (fire s i) hr
    simp only [nf, final]
    have hi := he.1
    have ex := (excited_tok hn s hi).1 he
    rw [tok_fire hn he hx] at this
    by_cases hxi : x = i
    · subst hxi
      have : ¬ x = prv n x := fun h => prv_ne (by omega) hx h.symm
      simp [b2n, ex.1, this] at *; omega
    · by_cases hxn : x = nxt n i
      · subst hxn
        simp only [prv_nxt hi] at *
        have : ¬ i = nxt n i := fun h => nxt_ne (by omega) hi h.symm
        simp [b2n, ex.2, this, hxi] at *; omega
      · have hp : ¬ i = prv n x := by
          intro h; apply hxn; rw [h, nxt_prv hx]
        simp [b2n, hxi, hxn, hp, Ne.symm hxi] at *; omega

theorem nf_step {n : Nat} (hn : 3 ≤ n) {y : Nat} (hy : y < n) {is : List Nat} {s : State}
    (hr : Run n s is) : nf (nxt n y) is ≤ nf y is + 1 := by
  have := balance hn (nxt_lt hy) is s hr
  rw [prv_nxt hy] at this
  have : b2n (tok n s (nxt n y)) ≤ 1 := by unfold b2n; split <;> omega
  omega

theorem nf_dist {n : Nat} (hn : 3 ≤ n) {i : Nat} (hi : i < n) {is : List Nat} {s : State}
    (hr : Run n s is) (h0 : nf i is = 0) : ∀ j, nf ((i + j) % n) is ≤ j := by
  intro j
  induction j with
  | zero => rw [Nat.add_zero, Nat.mod_eq_of_lt hi]; omega
  | succ j ih =>
    rw [← Nat.add_assoc, mod_succ_nxt]
    have := nf_step hn (Nat.mod_lt (i + j) (by omega)) hr
    omega

theorem nf_le {n : Nat} (hn : 3 ≤ n) {i x : Nat} (hi : i < n) (hx : x < n) {is : List Nat}
    {s : State} (hr : Run n s is) (h0 : nf i is = 0) : nf x is ≤ n - 1 := by
  have key := nf_dist hn hi hr h0 (if i ≤ x then x - i else x + n - i)
  have e : (i + (if i ≤ x then x - i else x + n - i)) % n = x := by
    split
    · have : i + (x - i) = x := by omega
      rw [this, Nat.mod_eq_of_lt hx]
    · have : i + (x + n - i) = x + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  rw [e] at key
  split at key <;> omega

def sumTo (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumTo g m + g m

theorem sumTo_le {g : Nat → Nat} {c m : Nat} (h : ∀ x, x < m → g x ≤ c) : sumTo g m ≤ m * c := by
  induction m with
  | zero => simp [sumTo]
  | succ m ih =>
    simp only [sumTo]; have := ih (fun x hx => h x (by omega)); have := h m (by omega)
    rw [Nat.succ_mul]; omega

theorem sumTo_ind (i m : Nat) : sumTo (fun x => if i = x then 1 else 0) m = if i < m then 1 else 0 := by
  induction m with
  | zero => simp [sumTo]
  | succ m ih =>
    simp only [sumTo, ih]
    by_cases h : i = m
    · subst h; simp
    · have e : (i < m + 1) = (i < m) := propext (by omega)
      simp [h, e]

theorem run_lt {n : Nat} : ∀ {is : List Nat} {s : State}, Run n s is → ∀ i, i ∈ is → i < n := by
  intro is
  induction is with
  | nil => intro _ _ _ h; simp at h
  | cons j is ih =>
    intro s ⟨he, hr⟩ i hm
    simp at hm
    rcases hm with rfl | hm
    · exact he.1
    · exact ih hr i hm

theorem length_eq_sum {n : Nat} : ∀ {is : List Nat}, (∀ i, i ∈ is → i < n) →
    is.length = sumTo (fun x => nf x is) n := by
  intro is
  induction is with
  | nil =>
    intro _
    have z : ∀ m, sumTo (fun x => nf x []) m = 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m ihm => show sumTo _ m + nf m [] = 0; rw [ihm]; rfl
    rw [z]; rfl
  | cons i is ih =>
    intro h
    have hi := h i (by simp)
    have ih' := ih (fun j hj => h j (by simp [hj]))
    simp only [List.length_cons, nf]
    have split_sum : ∀ m, sumTo (fun x => (if i = x then 1 else 0) + nf x is) m
        = sumTo (fun x => if i = x then 1 else 0) m + sumTo (fun x => nf x is) m := by
      intro m; induction m with
      | zero => rfl
      | succ m ihm => simp only [sumTo, ihm]; omega
    rw [split_sum, sumTo_ind, ← ih']; simp [hi]; omega

/-- **No stage starves.** On a ring of `N ≥ 3` stages, any execution in which
stage `i` never fires has at most `N(N-1)` transitions. So every window of
`N(N-1) + 1` consecutive transitions fires every stage, under any interleaving
(any delay assignment). With `ring_three`, a ring released from reset with
`N ≥ 3` circulates forever and every stage toggles infinitely often. -/
theorem fair_window {n : Nat} (hn : 3 ≤ n) {i : Nat} (hi : i < n) {s : State} {is : List Nat}
    (hr : Run n s is) (h0 : nf i is = 0) : is.length ≤ n * (n - 1) := by
  rw [length_eq_sum (run_lt hr)]
  exact sumTo_le (fun x hx => nf_le hn hi hx hr h0)

theorem every_stage_fires {n : Nat} (hn : 3 ≤ n) {s : State} {is : List Nat}
    (hr : Run n s is) (hlen : n * (n - 1) < is.length) : ∀ i, i < n → 0 < nf i is := by
  intro i hi
  apply Classical.byContradiction; intro h
  have := fair_window hn hi hr (by omega); omega

/-- From reset, an execution can always be extended (with `ring_three`), and
every reachable state is the end of an execution. -/
theorem extend {n K : Nat} (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n) {is : List Nat}
    (hr : Run n (resetState K) is) : ∃ i, excited n (final (resetState K) is) i :=
  (ring_three n K hK0 hKn).2 hn _ (run_reach .refl hr)

end Formal.Net.Ring
