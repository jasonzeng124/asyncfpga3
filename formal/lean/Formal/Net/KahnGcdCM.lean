import Formal.Net.KahnGcd

/-!
# The gcd loop with a Dynamatic-style `control_merge` header (probe C-8b)

Core Lean only. `Formal.Net.Kahn.Gcd.G` used the textbook Kahn loop header: a
`mux` whose select FIFO is primed with an initial "entry" token. Dynamatic does
not emit that. Its loop header (`handshake_transformed.mlir` of gcd, bb10:
`mux12..14` + `control_merge9`) is a `control_merge` of the control tokens
(entry, back edge) whose INDEX output drives the data muxes. A `control_merge`
is a nondeterministic merge (bdc lowers it to `bd_arbiter` + `bd_mux`), so the
graph is not `WF`: `cmL` and `cmR` both produce `hC` and `idx`.

This file shows the graph is still determinate, but only under the invariant
H_ONE_INVOCATION: at most one control token is on the loop's control ring
(`start`, `hC`, `backC`). `Inv` is closed under every firing (`G2_closed`), and
under it the two merge labels are never enabled together (`G2_wfOn`), which is
exactly what `WFOn` needs. Result (`cm_dataflow_eq_cLoop`, `cm_dataflow_gcd`):
same output as the C loop for every schedule, from the one-invocation initial
store. `two_invocations_not_inv` records that two start tokens break `Inv`.
-/

namespace Formal.Net.Kahn.GcdCM

open Formal.Net.Kahn Formal.Net.Kahn.Gcd

inductive Ch
  | start | inA | inB | backA | backB | backC | hA | hB | hC | idx | sA | sB
  | hA1 | hA2 | cnd | cA | cB | cC | aT | aF | bT | out | exitC | a1 | a2 | b1 | b2
  deriving DecidableEq

inductive Nd
  | cmL | cmR | forkI | muxA | muxB | forkA | isnz | forkC | brA | brB | brC
  | snkA | forkAT | forkBT | sub | mn
  deriving DecidableEq

/-- One input of the `control_merge`: forward the control token to `hC` and
emit the index `i` on `idx`. -/
def cmIn (i0 : Ch) (i : Nat) : Node Ch Nat :=
  strict [i0] (fun c => c = .hC ∨ c = .idx)
    (fun vs c => if c = .hC then vs.take 1 else if c = .idx then [i] else [])
    (fun vs c h => by
      have h1 : c ≠ .hC := fun e => h (Or.inl e)
      have h2 : c ≠ .idx := fun e => h (Or.inr e)
      simp [h1, h2])

def G2 : Nd → Node Ch Nat
  | .cmL    => cmIn .start 0
  | .cmR    => cmIn .backC 1
  | .forkI  => fork .idx [.sA, .sB]
  | .muxA   => mux .sA .inA .backA .hA tst (by decide) (by decide)
  | .muxB   => mux .sB .inB .backB .hB tst (by decide) (by decide)
  | .forkA  => fork .hA [.hA1, .hA2]
  | .isnz   => op1 .hA1 .cnd (fun x => if x == 0 then 0 else 1)
  | .forkC  => fork .cnd [.cA, .cB, .cC]
  | .brA    => branch .cA .hA2 .aT .aF tst
  | .brB    => branch .cB .hB .bT .out tst
  | .brC    => branch .cC .hC .backC .exitC tst
  | .snkA   => sink .aF
  | .forkAT => fork .aT [.a1, .a2]
  | .forkBT => fork .bT [.b1, .b2]
  | .sub    => op2 .a1 .b1 .backA (fun x y => strip2 (absdiff x y))
  | .mn     => op2 .a2 .b2 .backB min

def consumer : Ch → Option Nd
  | .start => some .cmL | .backC => some .cmR | .idx => some .forkI
  | .inA | .sA | .backA => some .muxA
  | .inB | .sB | .backB => some .muxB
  | .hA => some .forkA | .hA1 => some .isnz | .cnd => some .forkC
  | .cA | .hA2 => some .brA | .cB | .hB => some .brB | .cC | .hC => some .brC
  | .aF => some .snkA | .aT => some .forkAT | .bT => some .forkBT
  | .a1 | .b1 => some .sub | .a2 | .b2 => some .mn
  | .out | .exitC => none

/-- Producer up to the merge: `hC` and `idx` are produced by `cmL` OR `cmR`,
both recorded as `cmL` here (`canon` identifies them). -/
def producer : Ch → Option Nd
  | .hC | .idx => some .cmL
  | .sA | .sB => some .forkI
  | .hA => some .muxA | .hB => some .muxB
  | .hA1 | .hA2 => some .forkA | .cnd => some .isnz
  | .cA | .cB | .cC => some .forkC
  | .aT | .aF => some .brA | .bT | .out => some .brB | .backC | .exitC => some .brC
  | .a1 | .a2 => some .forkAT | .b1 | .b2 => some .forkBT
  | .backA => some .sub | .backB => some .mn
  | .start | .inA | .inB => none

def canon : Nd → Nd
  | .cmR => .cmL
  | l => l

theorem ins_consumer (l : Nd) (c : Ch) (h : (G2 l).ins c) : consumer c = some l := by
  cases l <;> cases c <;>
    simp_all [G2, cmIn, mux, fork, op1, op2, branch, sink, strict, consumer]

theorem outs_producer (l : Nd) (c : Ch) (h : (G2 l).outs c) : producer c = some (canon l) := by
  cases l <;> cases c <;>
    simp_all [G2, cmIn, mux, fork, op1, op2, branch, sink, strict, producer, canon]

theorem canon_eq {l₁ l₂ : Nd} (hne : l₁ ≠ l₂) (h : canon l₁ = canon l₂) :
    (l₁ = .cmL ∧ l₂ = .cmR) ∨ (l₁ = .cmR ∧ l₂ = .cmL) := by
  cases l₁ <;> cases l₂ <;> simp_all [canon]

/-- H_ONE_INVOCATION: at most one control token on the loop's control ring. -/
def Inv (s : Store Ch Nat) : Prop :=
  (s .start).length + (s .backC).length + (s .hC).length ≤ 1

theorem strict_fire {ins : List Ch} {f : List Nat → Ch → List Nat}
    {s : Store Ch Nat} {r : Fire Ch Nat}
    (h : (heads s ins).map (fun vs => ((fun c => if c ∈ ins then 1 else 0), f vs)) = some r) :
    ∃ vs, heads s ins = some vs ∧ r = (fun c => if c ∈ ins then 1 else 0, f vs) := by
  cases hh : heads s ins with
  | none => rw [hh] at h; cases h
  | some vs => rw [hh] at h; cases h; exact ⟨vs, rfl, rfl⟩

theorem enabled_cm {i0 : Ch} {i : Nat} {s : Store Ch Nat} (h : (cmIn i0 i).fire s ≠ none) :
    s i0 ≠ [] := by
  intro he
  apply h
  simp [cmIn, strict, heads, he]

theorem untouched {l : Nd} {s : Store Ch Nat} {r : Fire Ch Nat} {c : Ch}
    (hr : (G2 l).fire s = some r) (hi : ¬ (G2 l).ins c) (ho : ¬ (G2 l).outs c) :
    applyF s r c = s c := by
  simp [applyF, (G2 l).pop_ins s r c hr hi, (G2 l).push_outs s r c hr ho]

theorem G2_wfOn : WFOn G2 Inv where
  ins_disj l₁ l₂ c hne h1 h2 := by
    have := (ins_consumer l₁ c h1).symm.trans (ins_consumer l₂ c h2)
    exact hne (Option.some.inj this)
  outs_disj s l₁ l₂ c hI hne e1 e2 h1 h2 := by
    have := (outs_producer l₁ c h1).symm.trans (outs_producer l₂ c h2)
    rcases canon_eq hne (Option.some.inj this) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have a := enabled_cm e1; have b := enabled_cm e2
      unfold Inv at hI
      cases hs : s .start <;> cases hb : s .backC <;> simp_all <;> omega
    · have a := enabled_cm e1; have b := enabled_cm e2
      unfold Inv at hI
      cases hs : s .start <;> cases hb : s .backC <;> simp_all <;> omega

theorem len_take1 (vs : List Nat) : (vs.take 1).length ≤ 1 := by
  cases vs <;> simp

theorem G2_closed : Closed (step G2) Inv := by
  intro s l s' hI hs
  obtain ⟨r, hr, rfl⟩ := step_some hs
  unfold Inv at hI ⊢
  cases l
  case cmL =>
    obtain ⟨vs, hv, rfl⟩ := strict_fire hr
    have hne := heads_nonempty hv .start (by simp)
    simp only [applyF, List.length_append, List.length_drop]
    have := len_take1 vs
    cases hst : s .start with
    | nil => exact absurd hst hne
    | cons _ _ => simp_all; omega
  case cmR =>
    obtain ⟨vs, hv, rfl⟩ := strict_fire hr
    have hne := heads_nonempty hv .backC (by simp)
    simp only [applyF, List.length_append, List.length_drop]
    have := len_take1 vs
    cases hst : s .backC with
    | nil => exact absurd hst hne
    | cons _ _ => simp_all; omega
  case brC =>
    obtain ⟨vs, hv, rfl⟩ := strict_fire hr
    have hne := heads_nonempty hv .hC (by simp)
    simp only [applyF, List.length_append, List.length_drop]
    cases hst : s .hC with
    | nil => exact absurd hst hne
    | cons _ _ =>
      match vs with
      | [v, y] =>
        simp only [hst] at hI ⊢
        simp
        split <;> simp_all <;> omega
      | [] => simp_all; omega
      | [_] => simp_all; omega
      | _ :: _ :: _ :: _ => simp_all; omega
  all_goals
    rw [untouched hr (by simp [G2, mux, fork, op1, op2, branch, sink, strict])
          (by simp [G2, mux, fork, op1, op2, branch, sink, strict]),
        untouched hr (by simp [G2, mux, fork, op1, op2, branch, sink, strict])
          (by simp [G2, mux, fork, op1, op2, branch, sink, strict]),
        untouched hr (by simp [G2, mux, fork, op1, op2, branch, sink, strict])
          (by simp [G2, mux, fork, op1, op2, branch, sink, strict])]
    exact hI

/-! ## Stores and schedules -/

def init (a b : Nat) : Store Ch Nat := fun
  | .start => [0] | .inA => [a] | .inB => [b] | _ => []

def mid (a b : Nat) : Store Ch Nat := fun
  | .hA => [a] | .hB => [b] | .hC => [0] | _ => []

def top (a b : Nat) : Store Ch Nat := fun
  | .backA => [a] | .backB => [b] | .backC => [0] | _ => []

def fin (r : Nat) : Store Ch Nat := fun
  | .out => [r] | .exitC => [0] | _ => []

theorem init_inv (a b : Nat) : Inv (init a b) := by simp [Inv, init]

theorem init_mid (a b : Nat) : Run (step G2) (init a b) 4 (mid a b) :=
  exec_run (ls := [.cmL, .forkI, .muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem top_mid (a b : Nat) : Run (step G2) (top a b) 4 (mid a b) :=
  exec_run (ls := [.cmR, .forkI, .muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem mid_top (a b : Nat) :
    Run (step G2) (mid (a + 1) b) 10 (top (strip2 (absdiff (a + 1) b)) (min (a + 1) b)) :=
  exec_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .brC, .forkAT, .forkBT, .sub, .mn]) rfl
    (fun c => by cases c <;> rfl)

theorem mid_fin (b : Nat) : Run (step G2) (mid 0 b) 7 (fin b) :=
  exec_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .brC, .snkA]) rfl
    (fun c => by cases c <;> rfl)

theorem fin_terminal (r : Nat) : Terminal (step G2) (fin r) := by
  intro l; cases l <;> rfl

theorem run_of_cLoop : ∀ f a b r, cLoop f a b = some r → ∃ n, Run (step G2) (mid a b) n (fin r) := by
  intro f
  induction f with
  | zero => intro a b r h; simp [cLoop] at h
  | succ f ih =>
    intro a b r h
    simp only [cLoop] at h
    by_cases h0 : a = 0
    · subst h0; simp at h; subst h; exact ⟨7, mid_fin b⟩
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨n, hn⟩ := ih _ _ r h
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact ⟨10 + 4 + n, run_trans (run_trans (mid_top a' b) (top_mid _ _)) hn⟩

/-- With a `control_merge` header and one invocation in flight, every complete
run (any schedule, any arbitration outcome) ends with the C loop's result. -/
theorem cm_dataflow_eq_cLoop {f a b r : Nat} (h : cLoop f a b = some r) :
    (∃ n, Run (step G2) (init a b) n (fin r)) ∧
    (∀ m t, Run (step G2) (init a b) m t → Terminal (step G2) t → t = fin r) ∧
    (∃ N, ∀ m u, Run (step G2) (init a b) m u → m ≤ N) := by
  obtain ⟨n, hn⟩ := run_of_cLoop f a b r h
  have hr := run_trans (init_mid a b) hn
  refine ⟨⟨_, hr⟩, fun m t ht hT =>
      (terminal_unique G2_closed (wfOn_diamond G2_wfOn) (init_inv a b) hr (fin_terminal r) ht hT).1,
    ⟨_, fun m u hu => no_divergence G2_closed (wfOn_diamond G2_wfOn) (init_inv a b) hr
      (fin_terminal r) hu⟩⟩

theorem cm_dataflow_gcd {a b : Nat} (hb : b % 2 = 1) (ha : a = 0 ∨ a % 2 = 1) :
    ∀ m t, Run (step G2) (init a b) m t → Terminal (step G2) t → t .out = [Nat.gcd a b] := by
  have := (cm_dataflow_eq_cLoop (cLoop_gcd (a + b + 1) a b (by omega) hb ha)).2.1
  intro m t ht hT; rw [this m t ht hT]; rfl

/-- Two invocations in flight (two start tokens) violate H_ONE_INVOCATION. -/
theorem two_invocations_not_inv (a b : Nat) :
    ¬ Inv (fun c => if c = .start then [0, 0] else init a b c) := by simp [Inv, init]

end Formal.Net.Kahn.GcdCM
