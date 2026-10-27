import Formal.Net.KahnGcd

/-!
# The gcd main loop with its inner strip loop as a real nested dataflow loop

Probe C-8b, core Lean only. `Formal.Net.Kahn.Gcd.G` folded the C kernel's inner
loop `while (a > 0 && (a & 1) == 0) a >>= 1;` (bb11) into one operator node.
Here it is a loop of its own, nested in the outer one, built the same way: a
`mux` primed with an "entry" select token (`sD = [0]`), a condition token
(`ev`), a `cond_br` whose exit edge feeds the outer back edge `backA`, and the
shift on the inner back edge. The inner select is re-primed by the inner exit
(the `0` it pushes to `sD`), so each outer iteration re-enters it correctly.

`G3_wf`: the graph is well-formed, so determinacy is again `wf_determinate`.
`nested_dataflow_eq_cLoop`, `nested_dataflow_gcd`: every complete run, under any
schedule, ends with the C loop's result (`Nat.gcd` on the loop's entry condition).

Symbolic schedule evaluation: steps whose control decision depends on a symbolic
value (`ev x`) are evaluated with `simp` and the hypothesis on `ev x`; the rest by
`rfl` (definitional unfolding), as in `KahnGcd`.
-/

namespace Formal.Net.Kahn.GcdN
open Formal.Net.Kahn Formal.Net.Kahn.Gcd

inductive Ch
  | inA | inB | sA | sB | backA | backB | hA | hB | hA1 | hA2 | cnd | cA | cB
  | aT | aF | bT | out | a1 | a2 | b1 | b2
  | d | sD | dBack | hD | hD1 | hD2 | ce | cE | dT
  deriving DecidableEq

inductive Nd
  | muxA | muxB | forkA | isnz | forkC | brA | brB | snkA | forkAT | forkBT | sub | mn
  | muxD | forkD | evn | forkE | brD | shr
  deriving DecidableEq

/-- inner-loop condition `a > 0 && (a & 1) == 0` as a token -/
def ev (x : Nat) : Nat := if 0 < x ∧ x % 2 = 0 then 1 else 0

def G3 : Nd → Node Ch Nat
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
  | .sub    => op2 .a1 .b1 .d absdiff
  | .mn     => op2 .a2 .b2 .backB min
  | .muxD   => mux .sD .d .dBack .hD tst (by decide) (by decide)
  | .forkD  => fork .hD [.hD1, .hD2]
  | .evn    => op1 .hD1 .ce ev
  | .forkE  => fork .ce [.cE, .sD]
  | .brD    => branch .cE .hD2 .dT .backA tst
  | .shr    => op1 .dT .dBack (· / 2)

def consumer : Ch → Option Nd
  | .inA | .sA | .backA => some .muxA
  | .inB | .sB | .backB => some .muxB
  | .hA => some .forkA | .hA1 => some .isnz | .cnd => some .forkC
  | .cA | .hA2 => some .brA | .cB | .hB => some .brB | .aF => some .snkA
  | .aT => some .forkAT | .bT => some .forkBT
  | .a1 | .b1 => some .sub | .a2 | .b2 => some .mn
  | .sD | .d | .dBack => some .muxD | .hD => some .forkD | .hD1 => some .evn
  | .ce => some .forkE | .cE | .hD2 => some .brD | .dT => some .shr
  | .out => none

def producer : Ch → Option Nd
  | .hA => some .muxA | .hB => some .muxB
  | .hA1 | .hA2 => some .forkA | .cnd => some .isnz
  | .cA | .cB | .sA | .sB => some .forkC
  | .aT | .aF => some .brA | .bT | .out => some .brB
  | .a1 | .a2 => some .forkAT | .b1 | .b2 => some .forkBT
  | .d => some .sub | .backB => some .mn
  | .hD => some .muxD | .hD1 | .hD2 => some .forkD | .ce => some .evn
  | .cE | .sD => some .forkE | .dT | .backA => some .brD | .dBack => some .shr
  | .inA | .inB => none

theorem ins_consumer (l : Nd) (c : Ch) (h : (G3 l).ins c) : consumer c = some l := by
  cases l <;> cases c <;>
    simp_all [G3, mux, fork, op1, op2, branch, sink, strict, consumer]

theorem outs_producer (l : Nd) (c : Ch) (h : (G3 l).outs c) : producer c = some l := by
  cases l <;> cases c <;>
    simp_all [G3, mux, fork, op1, op2, branch, sink, strict, producer]

theorem G3_wf : WF G3 where
  ins_disj l₁ l₂ c hne h1 h2 := by
    have := (ins_consumer l₁ c h1).symm.trans (ins_consumer l₂ c h2)
    exact hne (Option.some.inj this)
  outs_disj l₁ l₂ c hne h1 h2 := by
    have := (outs_producer l₁ c h1).symm.trans (outs_producer l₂ c h2)
    exact hne (Option.some.inj this)

def init (a b : Nat) : Store Ch Nat := fun
  | .inA => [a] | .inB => [b] | .sA => [0] | .sB => [0] | .sD => [0] | _ => []

def mid (a b : Nat) : Store Ch Nat := fun
  | .hA => [a] | .hB => [b] | .sD => [0] | _ => []

def top (a b : Nat) : Store Ch Nat := fun
  | .sA => [1] | .sB => [1] | .sD => [0] | .backA => [a] | .backB => [b] | _ => []

def fin (r : Nat) : Store Ch Nat := fun
  | .sA => [0] | .sB => [0] | .sD => [0] | .out => [r] | _ => []

/-- inner loop header has fired on `x`; `m` waits on backB -/
def imid (x m : Nat) : Store Ch Nat := fun
  | .hD => [x] | .sA => [1] | .sB => [1] | .backB => [m] | _ => []

def itop (x m : Nat) : Store Ch Nat := fun
  | .dBack => [x] | .sD => [1] | .sA => [1] | .sB => [1] | .backB => [m] | _ => []

theorem inner_iter (x m : Nat) (h : ev x = 1) : Run (step G3) (imid x m) 5 (itop (x / 2) m) := by
  apply exec_run (ls := [.forkD, .evn, .forkE, .brD, .shr]) (t := itop (x / 2) m) _ (fun _ => rfl)
  simp [exec, step, G3, fork, op1, branch, strict, heads, applyF, imid, h, tst]
  funext c; cases c <;> rfl


theorem itop_imid (x m : Nat) : Run (step G3) (itop x m) 1 (imid x m) :=
  exec_run (ls := [.muxD]) rfl (fun c => by cases c <;> rfl)

theorem inner_exit (x m : Nat) (h : ev x = 0) : Run (step G3) (imid x m) 4 (top x m) := by
  apply exec_run (ls := [.forkD, .evn, .forkE, .brD]) (t := top x m) _ (fun _ => rfl)
  simp [exec, step, G3, fork, op1, branch, strict, heads, applyF, imid, h, tst]
  funext c; cases c <;> rfl

theorem ev_spec (x : Nat) : (0 < x ∧ x % 2 = 0 → ev x = 1) ∧ (¬ (0 < x ∧ x % 2 = 0) → ev x = 0) := by
  unfold ev; constructor <;> intro h <;> simp [h]

/-- The inner loop computes `strip2`, from any entry value. -/
theorem inner_loop (x m : Nat) : ∃ n, Run (step G3) (imid x m) n (top (strip2 x) m) := by
  by_cases h : 0 < x ∧ x % 2 = 0
  · obtain ⟨n, hn⟩ := inner_loop (x / 2) m
    have e : strip2 x = strip2 (x / 2) := by rw [strip2]; simp [h]
    rw [e]
    exact ⟨_, run_trans (run_trans (inner_iter x m ((ev_spec x).1 h)) (itop_imid _ _)) hn⟩
  · have e : strip2 x = x := by rw [strip2]; simp [h]
    rw [e]
    exact ⟨_, inner_exit x m ((ev_spec x).2 h)⟩
termination_by x
decreasing_by omega

theorem init_mid (a b : Nat) : Run (step G3) (init a b) 2 (mid a b) :=
  exec_run (ls := [.muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem top_mid (a b : Nat) : Run (step G3) (top a b) 2 (mid a b) :=
  exec_run (ls := [.muxA, .muxB]) rfl (fun c => by cases c <;> rfl)

theorem mid_imid (a b : Nat) :
    Run (step G3) (mid (a + 1) b) 10 (imid (absdiff (a + 1) b) (min (a + 1) b)) :=
  exec_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .forkAT, .forkBT, .sub, .mn, .muxD]) rfl
    (fun c => by cases c <;> rfl)

theorem mid_fin (b : Nat) : Run (step G3) (mid 0 b) 7 (fin b) :=
  exec_run (ls := [.forkA, .isnz, .forkC, .brA, .brB, .snkA]) rfl
    (fun c => by cases c <;> rfl)

theorem fin_terminal (r : Nat) : Terminal (step G3) (fin r) := by
  intro l; cases l <;> rfl

theorem run_of_cLoop : ∀ f a b r, cLoop f a b = some r → ∃ n, Run (step G3) (mid a b) n (fin r) := by
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
      obtain ⟨k, hk⟩ := inner_loop (absdiff (a' + 1) b) (min (a' + 1) b)
      exact ⟨_, run_trans (run_trans (run_trans (mid_imid a' b) hk) (top_mid _ _)) hn⟩

theorem nested_dataflow_eq_cLoop {f a b r : Nat} (h : cLoop f a b = some r) :
    (∃ n, Run (step G3) (init a b) n (fin r)) ∧
    (∀ m t, Run (step G3) (init a b) m t → Terminal (step G3) t → t = fin r) ∧
    (∃ N, ∀ m u, Run (step G3) (init a b) m u → m ≤ N) := by
  obtain ⟨n, hn⟩ := run_of_cLoop f a b r h
  have hr := run_trans (init_mid a b) hn
  exact ⟨⟨_, hr⟩, fun m t ht hT => (wf_determinate G3_wf hr (fin_terminal r) ht hT).1,
    ⟨_, fun m u hu => wf_no_divergence G3_wf hr (fin_terminal r) hu⟩⟩

theorem nested_dataflow_gcd {a b : Nat} (hb : b % 2 = 1) (ha : a = 0 ∨ a % 2 = 1) :
    ∀ m t, Run (step G3) (init a b) m t → Terminal (step G3) t → t .out = [Nat.gcd a b] := by
  have := (nested_dataflow_eq_cLoop (cLoop_gcd (a + b + 1) a b (by omega) hb ha)).2.1
  intro m t ht hT; rw [this m t ht hT]; rfl

end Formal.Net.Kahn.GcdN
