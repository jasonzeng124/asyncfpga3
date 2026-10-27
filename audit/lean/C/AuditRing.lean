import Formal.Net.Ring

/-! Audit of shard C ring claims (Formal/Net/Ring.lean @ 71ee3e86). -/

namespace Audit.C.Ring
open Formal.Net.Ring Formal.Cells Formal.Cells.CElemFn

/-! ## 1. INITs: the ring's gates are the bd_ce.v LUTs (INIT copied from RTL). -/
example : INIT_c2n = 0x00B200B200B200B2 := rfl
example : INIT_c2n_set = 0xFFB2FFB2FFB2FFB2 := rfl

/-! ## 2. Non-vacuity of ring_three: N=3, K=1 satisfies 0<K<N, and
    the conclusion is the nontrivial (live) direction. -/
theorem nv_ring3 : ∀ s, Reach 3 (resetState 1) s → ∃ i, excited 3 s i :=
  (ring_three 3 1 (by decide) (by decide)).2 (by decide)

/-- The reset state itself really has an excited gate (checked directly, not
    via the theorem): stage 1 at N=3, K=1. -/
theorem direct_excited_3_1 : excited 3 (resetState 1) 1 := by
  unfold excited; decide

/-- Direct: N=2, K=1: no gate excited (independent of ring_three). -/
theorem direct_dead_2_1 : ∀ i, i < 2 → ¬ excited 2 (resetState 1) i := by
  unfold excited prv nxt ctl resetState; decide

/-- Dropping 0 < K breaks ring_three's conclusion: N=3, K=0 has 3 ≤ N but is dead. -/
theorem drop_K0 : ¬ (∀ s, Reach 3 (resetState 0) s → ∃ i, excited 3 s i) := by
  intro h
  obtain ⟨i, hi⟩ := h _ .refl
  exact ring_degenerate_dead (Or.inl rfl) i hi

/-- Dropping K < N breaks it too: N=3, K=3 dead. -/
theorem drop_KN : ¬ (∀ s, Reach 3 (resetState 3) s → ∃ i, excited 3 s i) := by
  intro h
  obtain ⟨i, hi⟩ := h _ .refl
  exact ring_degenerate_dead (Or.inr (Nat.le_refl _)) i hi

/-! ## 3. k_tokens non-vacuity and the tb_ring finding -/

/-- kState 2 at N=4 has 4 wavefronts (two four-phase tokens). -/
theorem D_k2_n4 : D 4 (kState 2) = 4 := D_kState (by decide) (by decide)

/-- Direct, independent of k_tokens: N=4 with two tokens (1010) is dead. -/
theorem direct_dead_4_two_tokens : ∀ i, i < 4 → ¬ excited 4 (kState 2) i := by
  unfold excited prv nxt ctl kState; decide

/-- Direct: N=5 with two tokens has an excited gate. -/
theorem direct_live_5_two_tokens : excited 5 (kState 2) 3 := by
  unfold excited prv nxt ctl kState; decide

/-- k_tokens instance: N=5, k=2 live in every reachable state. -/
theorem nv_k2_n5 : ∀ s, Reach 5 (kState 2) s → ∃ i, excited 5 s i :=
  (kState_live_iff 5 2 (by decide) (by decide)).2 (by decide)

/-- k_tokens instance: N=4, k=2 is not live. -/
theorem nv_k2_n4 : ¬ ∀ s, Reach 4 (kState 2) s → ∃ i, excited 4 s i := by
  intro h; have := (kState_live_iff 4 2 (by decide) (by decide)).1 h; omega

/-- Every non-degenerate tb_ring case (N,K) in {(3..6,1),(4,2),(4,3),(6,3),(6,5)}
    carries exactly 2 wavefronts = one loop token: the bench never varies the token count. -/
theorem tb_cases_one_token :
    D 3 (resetState 1) = 2 ∧ D 4 (resetState 1) = 2 ∧ D 5 (resetState 1) = 2 ∧
    D 6 (resetState 1) = 2 ∧ D 4 (resetState 2) = 2 ∧ D 4 (resetState 3) = 2 ∧
    D 6 (resetState 3) = 2 ∧ D 6 (resetState 5) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact D_reset (by decide) (by decide)

/-- And by direct evaluation (no theorem used). -/
example : (D 4 (resetState 2), D 6 (resetState 3), D 6 (resetState 5), D 4 (kState 2)) = (2, 2, 2, 4) := by
  decide

/-! ## 4. Independent brute-force cross-check: explicit BFS over all 2^n states. -/

def toSt (n m : Nat) : State := fun j => j < n && m.testBit j
def enc (n : Nat) (s : State) : Nat := (List.range n).foldl (fun acc j => if s j then acc + 2^j else acc) 0
def exB (n : Nat) (s : State) (i : Nat) : Bool := decide (i < n) && (ctl (s (prv n i)) (s (nxt n i)) (s i) != s i)
def succs (n m : Nat) : List Nat :=
  (List.range n).filter (fun i => exB n (toSt n m) i) |>.map (fun i => enc n (fire (toSt n m) i))
partial def bfs (n : Nat) (front seen : List Nat) : List Nat :=
  match front with
  | [] => seen
  | x :: xs => let nw := (succs n x).filter (fun y => !seen.contains y)
               bfs n (xs ++ nw) (seen ++ nw)
def reachAllLive (n m : Nat) : Bool :=
  (bfs n [m] [m]).all (fun y => (List.range n).any (fun i => exB n (toSt n y) i))
def DB (n m : Nat) : Nat := (List.range n).countP (fun i => toSt n m (prv n i) != toSt n m i)
/-- For every n ≤ 8 and every initial state with D = 2k ≥ 2: (all reachable live) == (n ≥ 2k+1). -/
def crossCheck : Bool :=
  (List.range 9).all fun n => (List.range (2^n)).all fun m =>
    let d := DB n m
    d == 0 || (reachAllLive n m == decide (d + 1 ≤ n))
#eval crossCheck
-- also count mismatches of D parity (D always even)
#eval (List.range 9).all fun n => (List.range (2^n)).all fun m => DB n m % 2 == 0

/-! ## 5. Axioms -/
#print axioms ring_three
#print axioms k_tokens
#print axioms dead_of_le_two
#print axioms D_reach
#print axioms fair_window
#print axioms kState_live_iff
#print axioms direct_dead_4_two_tokens
#print axioms tb_cases_one_token

end Audit.C.Ring
