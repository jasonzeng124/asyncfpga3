import Formal.Net.AO.UnrollClaimU
import Formal.Net.AO.SymClaim

/-!
# Template kinds: the claim check of every sub-word, once for every pair (shard C, 2026-11-15; piece 3, step 2.2)

**Problem, plainly.** `UnrollClaimU.gc_unrollU_gen` proves every non-external claim of the long certificate of a
word from the sub-word checks `GcWinU` on concrete kinds. With register bits in the claims, the concrete kind of
window `j` depends on the pair (its register words). Can the sub-word checks be done once, on *template* kinds whose
claims carry window-relative symbols `(rel, v)` (bit `v` of the register words of window `j + rel`), for every pair?

**The model.** `TKind`: a kind plus template claims over symbols `Nat × V0`. A pair gives a global assignment
`ρ : Nat × V0 → Bool` (`ρ (j, v)`: bit `v` in window `j`); `instW ρ n ts` instantiates window `t` of `ts` with the
symbols renamed to `(n + t + rel, v)`. `uclTT` is the template form of the long claim list (shifted timing,
renamed symbols).

**Proved.**
* `uclT_instW`: the long claim list of the instantiated word is the instantiation of `uclTT`.
* `wt_instW`, `usep_instW`, `uup_instW`, `WSep_instW`, `WUp_instW`: the event structures and the separation /
  upper-bound tables of a word do not depend on the claims, so not on `ρ`.
* `GateProofWS`, `gateProofW_inst`: the template form of `GateProofW` (`SymClaim.valSB`) gives `GateProofW` under
  every assignment.
* `GcWinS` (the template sub-word check, external claims given by a node predicate) and `gcWinU_inst`: it gives
  `GcWinU` of the instantiated sub-word, for every `ρ` and every start window `n`.
* `instW_drop_take`: the sub-word of an instantiated word is the instantiated template sub-word.
* `gc_unrollU_sym`: hence `hGC` of the long certificate of the instantiated word, for EVERY assignment, from the
  template sub-word checks (one finite set of checks for all pairs).

**Not shown.** Chains (`ChainUOK`) in template checks (only the GateProof alternative is lifted); that the
assignment of a pair is its token run's register bits (the window invariant: UnitProof value premises); the instance.
-/

namespace Formal.Net.AO.Sym
open Formal.Net.OccNet (st)
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX
  Formal.Net.OccNet.TimedU Formal.Net.AO

variable {α V0 : Type} [DecidableEq α] [DecidableEq V0]

/-! ## Renaming and shifting templates -/

/-- Window-relative symbols of window `n`: `(rel, v)` becomes `(n + rel, v)`. -/
def SVal.rn (n : Nat) : SVal (Nat × V0) → SVal (Nat × V0)
  | .lit b => .lit b
  | .sym q neg => .sym (n + q.1, q.2) neg

omit [DecidableEq V0] in
theorem SVal.eval_rn (ρ : Nat × V0 → Bool) (n : Nat) (s : SVal (Nat × V0)) :
    (s.rn n).eval ρ = s.eval (fun q => ρ (n + q.1, q.2)) := by
  cases s <;> rfl

def TClaim.rn (n : Nat) (c : TClaim α (Nat × V0)) : TClaim α (Nat × V0) := { c with sv := c.sv.rn n }

def TClaim.sh {V : Type} (o : α → Nat) (c : TClaim α V) : TClaim α V :=
  { c with A := c.A.map (shE o), B := c.B.map (shE o) }

omit [DecidableEq α] [DecidableEq V0] in
theorem inst_sh_rn (ρ : Nat × V0 → Bool) (o : α → Nat) (n : Nat) (c : TClaim α (Nat × V0)) :
    ((c.rn n).sh o).inst ρ = shC o (c.inst (fun q => ρ (n + q.1, q.2))) := by
  simp only [TClaim.inst, TClaim.sh, TClaim.rn, shC, SVal.eval_rn]

/-! ## Template kinds and words -/

/-- A template kind: a kind (its own `cl` is ignored) and template claims. -/
structure TKind (α V0 : Type) where
  k : WKindT α
  tcl : List (TClaim α (Nat × V0))

/-- Window `n`'s instance of a template kind. -/
def TKind.inst (ρ : Nat × V0 → Bool) (n : Nat) (t : TKind α V0) : WKindT α :=
  { t.k with cl := instL (fun q => ρ (n + q.1, q.2)) t.tcl }

/-- The instantiated word, windows numbered from `n`. -/
def instW (ρ : Nat × V0 → Bool) : Nat → List (TKind α V0) → List (WKindT α)
  | _, [] => []
  | n, t :: ts => t.inst ρ n :: instW ρ (n + 1) ts

/-- The template long claim list, windows numbered from `n`. -/
def uclTT : Nat → List (TKind α V0) → (α → Nat) → List (TClaim α (Nat × V0))
  | _, [], _ => []
  | n, t :: ts, b => t.tcl.map (fun c => (c.rn n).sh b) ++ uclTT (n + 1) ts (fun p => b p + t.k.len p)

omit [DecidableEq α] [DecidableEq V0] in
theorem instW_length (ρ : Nat × V0 → Bool) : ∀ (n : Nat) (ts : List (TKind α V0)), (instW ρ n ts).length = ts.length
  | _, [] => rfl
  | n, _ :: ts => by simp [instW, instW_length ρ (n + 1) ts]

omit [DecidableEq α] [DecidableEq V0] in
theorem uclT_instW (ρ : Nat × V0 → Bool) :
    ∀ (n : Nat) (ts : List (TKind α V0)) (b : α → Nat), uclT (wk (instW ρ n ts)) b = instL ρ (uclTT n ts b)
  | _, [], _ => rfl
  | n, t :: ts, b => by
    simp only [instW, wk, List.map_cons, uclT, uclTT, instL, List.map_append, List.map_map]
    have ih := uclT_instW ρ (n + 1) ts (fun p => b p + t.k.len p)
    simp only [wk, instL] at ih
    have hl : (t.inst ρ n).toWKind.len = t.k.len := rfl
    rw [hl, ih]
    congr 1
    simp only [TKind.inst, instL, List.map_map]
    apply List.map_congr_left
    intro c _
    simp only [Function.comp, inst_sh_rn]

omit [DecidableEq V0] in
/-- Event structures ignore claims. -/
theorem wt_instW (ρ : Nat × V0 → Bool) :
    ∀ (n : Nat) (ts : List (TKind α V0)), wt (instW ρ n ts) = wt (ts.map TKind.k)
  | _, [] => rfl
  | n, t :: ts => by
    rw [instW, List.map_cons, wt_cons, wt_cons, wt_instW ρ (n + 1) ts]
    rfl

omit [DecidableEq V0] in
theorem usep_instW (ρ : Nat × V0 → Bool) :
    ∀ (n : Nat) (ts : List (TKind α V0)), usep (instW ρ n ts) = usep (ts.map TKind.k)
  | _, [] => rfl
  | n, t :: ts => by
    funext b m a k
    simp only [instW, List.map_cons, usep]
    rw [usep_instW ρ (n + 1) ts]
    rfl

omit [DecidableEq V0] in
theorem uup_instW (ρ : Nat × V0 → Bool) :
    ∀ (n : Nat) (ts : List (TKind α V0)), uup (instW ρ n ts) = uup (ts.map TKind.k)
  | _, [] => rfl
  | n, t :: ts => by
    funext e0 e
    simp only [instW, List.map_cons, uup]
    rw [uup_instW ρ (n + 1) ts]
    rfl

omit [DecidableEq V0] in
theorem WSep_instW (ρ : Nat × V0 → Bool) (n : Nat) (ts : List (TKind α V0)) :
    WSep (instW ρ n ts) = WSep (ts.map TKind.k) := by
  funext b m a k
  simp only [WSep, wt_instW, usep_instW]

omit [DecidableEq V0] in
theorem WUp_instW (ρ : Nat × V0 → Bool) (n : Nat) (ts : List (TKind α V0)) :
    WUp (instW ρ n ts) = WUp (ts.map TKind.k) := by
  funext e0 e
  simp only [WUp, wt_instW, uup_instW]

omit [DecidableEq α] [DecidableEq V0] in
theorem instW_shift (ρ : Nat × V0 → Bool) :
    ∀ (n m : Nat) (ts : List (TKind α V0)), instW ρ (n + m) ts = instW (fun q => ρ (n + q.1, q.2)) m ts
  | _, _, [] => rfl
  | n, m, t :: ts => by
    simp only [instW]
    rw [show n + m + 1 = n + (m + 1) by omega, instW_shift ρ n (m + 1) ts]
    congr 1
    simp only [TKind.inst]
    congr 3
    funext q
    rw [Nat.add_assoc]

omit [DecidableEq α] [DecidableEq V0] in
theorem instW_drop (ρ : Nat × V0 → Bool) :
    ∀ (n j : Nat) (ts : List (TKind α V0)), (instW ρ n ts).drop j = instW ρ (n + j) (ts.drop j)
  | n, 0, ts => by simp
  | _, _ + 1, [] => rfl
  | n, j + 1, t :: ts => by
    simp only [instW, List.drop_succ_cons]
    rw [instW_drop ρ (n + 1) j ts, show n + 1 + j = n + (j + 1) by omega]

omit [DecidableEq α] [DecidableEq V0] in
theorem instW_take (ρ : Nat × V0 → Bool) :
    ∀ (n j : Nat) (ts : List (TKind α V0)), (instW ρ n ts).take j = instW ρ n (ts.take j)
  | _, 0, ts => by simp [instW]
  | _, _ + 1, [] => rfl
  | n, j + 1, t :: ts => by
    simp only [instW, List.take_succ_cons]
    rw [instW_take ρ (n + 1) j ts]

omit [DecidableEq α] [DecidableEq V0] in
/-- **The sub-word of an instantiated word is the instantiated template sub-word.** -/
theorem instW_drop_take (ρ : Nat × V0 → Bool) (ts : List (TKind α V0)) (i r : Nat) :
    ((instW ρ 0 ts).drop i).take r = instW ρ i ((ts.drop i).take r) := by
  rw [instW_drop, instW_take, Nat.zero_add]

/-! ## The template sub-word check -/

/-- `GateProofW` on templates: the symbolic value check and the value-free facts. -/
def GateProofWS (N : TNet α) (dat : α → Bool) (Sep : α → Nat → α → Nat → Option Nat) (s0 : α → Bool)
    (tcl : List (TClaim α (Nat × V0))) (t : Nat) (c : TClaim α (Nat × V0)) : Prop :=
  N.gate c.z = true ∧ 0 ≤ c.a ∧ ∃ cov : α → Cov, valSB N s0 tcl c cov = true ∧
    (∀ u ∈ N.pins c.z, ∀ w, covWin s0 (instL (fun _ => false) tcl) u (cov u) = some w →
      CovTime Sep (c.inst (fun _ => false)) w (N.hi c.z u) (N.lo c.z u)) ∧
    (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false ∧ (k = 0 → t = 0)) ∧
      (∀ i w, cov u = .cl i → tcl[i]? = some w → w.z = u))

theorem gateProofW_inst {N : TNet α} {dat : α → Bool} {Sep : α → Nat → α → Nat → Option Nat} {s0 : α → Bool}
    {tcl : List (TClaim α (Nat × V0))} {t : Nat} {c : TClaim α (Nat × V0)} (h : GateProofWS N dat Sep s0 tcl t c)
    (ρ : Nat × V0 → Bool) : GateProofW N dat Sep s0 (instL ρ tcl) t (c.inst ρ) := by
  obtain ⟨hg, ha, cov, hv, hct, hcf⟩ := h
  refine ⟨hg, ha, cov, valOK_inst N s0 tcl c cov hv ρ, ?_, ?_⟩
  · intro u hu w hw
    obtain ⟨w', hw', e1, e2, e3, e4⟩ := covWin_timing s0 tcl ρ (fun _ => false) u (cov u) w hw
    exact covTime_congr ⟨rfl, rfl, rfl, rfl⟩ ⟨e1, e2, e3, e4⟩ (hct u hu w' hw')
  · intro u hu
    refine ⟨(hcf u hu).1, fun i w hci hw => ?_⟩
    rw [instL_get] at hw
    cases ht : tcl[i]? with
    | none => rw [ht] at hw; simp at hw
    | some c' =>
      rw [ht] at hw
      simp only [Option.map_some, Option.some.injEq] at hw
      subst hw
      exact (hcf u hu).2 i c' hci ht

/-- **The template sub-word check**: every claim of window `t` whose node is not external (`P`) is proved by its
gate, for every assignment of the sub-word's symbols (symbols renamed by window index). -/
def GcWinS (N : TNet α) (dat : α → Bool) (P : α → Prop) (s0 : α → Bool) (ts : List (TKind α V0)) (t : Nat) :
    Prop :=
  ∀ (h : t < ts.length), ∀ c0 ∈ ts[t].tcl, ¬ P c0.z → N.gate c0.z = true →
    GateProofWS N dat (WSep (ts.map TKind.k)) s0 (uclTT 0 ts (fun _ => 0)) t
      ((c0.rn t).sh (off (wt (ts.map TKind.k)) t))

omit [DecidableEq α] [DecidableEq V0] in
theorem instW_get (ρ : Nat × V0 → Bool) :
    ∀ (n : Nat) (ts : List (TKind α V0)) (t : Nat) (h : t < (instW ρ n ts).length) (h' : t < ts.length),
      (instW ρ n ts)[t] = ts[t].inst ρ (n + t)
  | _, [], _, _, h' => absurd h' (Nat.not_lt_zero _)
  | n, t0 :: ts, 0, _, _ => by simp [instW]
  | n, t0 :: ts, t + 1, h, h' => by
    simp only [instW, List.getElem_cons_succ]
    rw [instW_get ρ (n + 1) ts t (by simpa [instW] using h) (by simpa using h')]
    rw [show n + 1 + t = n + (t + 1) by omega]

/-- **Template checks give the concrete sub-word checks under every assignment.** -/
theorem gcWinU_inst {N : TNet α} {dat : α → Bool} {P : α → Prop} {s0 : α → Bool} {ts : List (TKind α V0)}
    {t : Nat} (h : GcWinS N dat P s0 ts t) (ρ : Nat × V0 → Bool) (n : Nat) :
    GcWinU N dat (fun c => P c.z) s0 (instW ρ n ts) t := by
  intro ht c0 hc0 hx hg
  have ht' : t < ts.length := by rw [instW_length] at ht; exact ht
  rw [instW_get ρ n ts t ht ht'] at hc0
  simp only [TKind.inst, instL, List.mem_map] at hc0
  obtain ⟨c, hc, rfl⟩ := hc0
  left
  have hP : ¬ P c.z := hx
  have hG := h ht' c hc hP hg
  have e1 : uclT (wk (instW ρ n ts)) (fun _ => 0) = instL (fun q => ρ (n + q.1, q.2)) (uclTT 0 ts (fun _ => 0)) := by
    have hs := instW_shift ρ n 0 ts
    rw [Nat.add_zero] at hs
    rw [hs, uclT_instW]
  have e2 : shC (off (wt (instW ρ n ts)) t) (c.inst (fun q => ρ (n + t + q.1, q.2))) =
      ((c.rn t).sh (off (wt (ts.map TKind.k)) t)).inst (fun q => ρ (n + q.1, q.2)) := by
    rw [inst_sh_rn, wt_instW]
    congr 2
    funext q
    rw [Nat.add_assoc]
  rw [e1, WSep_instW, e2]
  exact gateProofW_inst hG _

/-- **`hGC` of the long certificate of every instantiated word from the template sub-word checks** (the
GateProof alternative): one finite set of checks on template sub-words serves every assignment, so every pair. -/
theorem gc_unrollU_sym (N : TNet α) (dat : α → Bool) (P : α → Prop) (r : Nat) (hr : 2 ≤ r)
    (tks : List (TKind α V0)) (ρ : Nat × V0 → Bool) (s0 : α → Bool) (sw : Nat → α → Bool)
    (hsw : ∀ i, i < tks.length → ∀ w ∈ ((instW ρ 0 tks).drop (i - 1)).take r, ∀ c0 ∈ w.cl, ∀ u ∈ N.pins c0.z,
      sw i u = st s0 (off (wt (instW ρ 0 tks)) (i - 1)) u)
    (hW : ∀ i, i < tks.length → GcWinS N dat P (sw i) ((tks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk (instW ρ 0 tks)) (fun _ => 0), ¬ P c.z → N.gate c.z = true →
      GateProof N dat (LSep (instW ρ 0 tks)) s0 (uclT (wk (instW ρ 0 tks)) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk (instW ρ 0 tks)) (fun _ => 0) ∧
        GateProof N dat (LSep (instW ρ 0 tks)) s0 (uclT (wk (instW ρ 0 tks)) (fun _ => 0)) c') ∧
        ChainUOK (LSep (instW ρ 0 tks)) (LUp (instW ρ 0 tks)) c cs := by
  have hX : ExtShift (fun c : Claim α => P c.z) := extShift_node (fun z _ => P z)
  have := gc_unrollU_gen N dat (fun c => P c.z) hX r hr (instW ρ 0 tks) s0 sw
    (fun i hi => hsw i (by rw [instW_length] at hi; exact hi))
    (fun i hi => by
      rw [instW_drop_take]
      exact gcWinU_inst (hW i (by rw [instW_length] at hi; exact hi)) ρ (i - 1))
  exact this

end Formal.Net.AO.Sym
