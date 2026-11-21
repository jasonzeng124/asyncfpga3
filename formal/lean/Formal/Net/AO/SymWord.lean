import Formal.Net.AO.SymChain
import Formal.Net.AO.UnrollUnit

/-!
# Every pair from template kinds: the composed safety theorem (shard C, 2026-11-15)

**Problem.** Do the pieces compose? For a pair, the word of concrete kinds is the instantiation of template kinds by
the pair's assignment `ρ` (register bits per window). `UnrollUnit.timedA_follows_unrollUnitC` needs the sub-word
claim checks `GcWinU` on the concrete kinds; `SymChain` gives them from template checks.

**Proved.** `TKindF` (template kinds with full causes), `instWF`, `wP_instWF`; `timedA_follows_sym`: safety for
the certificate of the instantiated word, with the claim checks given ONCE on template sub-words (`GcWinS2`, for
every ρ) and the external claims (a node predicate `P`) by `UnitProof`. The other hypotheses are those of
`timedA_follows_unrollUnitC`, stated on the instantiated word.

**Not shown.** That the other per-kind hypotheses (`hloc`, `hIk`, ...) are value-independent (they read claim values
only through guards on condition claims, which are literals per kind in the intended use; not proved here); the
`UnitProof`s (value premises = token run); the instance.
-/

namespace Formal.Net.AO.Sym
open Formal.Net.OccNet (st)
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX
  Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU Formal.Net.AO

variable {α V0 : Type} [DecidableEq α] [DecidableEq V0]

/-- A template kind with full causes. -/
structure TKindF (α V0 : Type) where
  k : WKindF α
  tcl : List (TClaim α (Nat × V0))

def TKindF.toT (t : TKindF α V0) : TKind α V0 := ⟨t.k.toWKindT, t.tcl⟩

def TKindF.inst (ρ : Nat × V0 → Bool) (n : Nat) (t : TKindF α V0) : WKindF α :=
  { t.k with cl := instL (fun q => ρ (n + q.1, q.2)) t.tcl }

def instWF (ρ : Nat × V0 → Bool) : Nat → List (TKindF α V0) → List (WKindF α)
  | _, [] => []
  | n, t :: ts => t.inst ρ n :: instWF ρ (n + 1) ts

omit [DecidableEq α] [DecidableEq V0] in
theorem wP_instWF (ρ : Nat × V0 → Bool) :
    ∀ (n : Nat) (ts : List (TKindF α V0)), wP (instWF ρ n ts) = instW ρ n (ts.map TKindF.toT)
  | _, [] => rfl
  | n, t :: ts => by
    simp only [instWF, wP, List.map_cons, instW] at *
    rw [← wP_instWF ρ (n + 1) ts]
    rfl

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {D : α → List α}

/-- **Safety for every pair's word from template kinds** (module docstring). -/
theorem timedA_follows_sym (P : α → Prop) [DecidablePred P] (ρ : Nat × V0 → Bool)
    (BIG r' : Nat) (hr : 2 ≤ r') (tks : List (TKindF α V0)) (ks : List (WKindF α)) (hks : ks = instWF ρ 0 tks)
    (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hWS : ∀ i, i < tks.length → GcWinS2 N dat P (st (fun w => x w t0) (off (wt (wP ks)) (i - 1)))
      (((tks.map TKindF.toT).drop (i - 1)).take r') (i - (i - 1)))
    (hUn : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), P c.z →
      UnitProof x (LSep (wP ks)) (fun c => P c.z) (uclT (wk (wP ks)) (fun _ => 0)) c)
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hIk : ∀ i (hi : i < (wP ks).length), ∀ c0 ∈ (wP ks)[i].cl,
      (c0.A ≠ none ∧ 0 ≤ c0.a) ∨ (i = 0 ∧ ∀ s, s ≤ t0 → Holds x t0 H c0 s)) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N (CPu BIG ks) x t0 r v s) ∧
      (∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 (LSep (wP ks)) t :=
  timedA_follows_unrollUnitC (fun c => P c.z) (extShift_node (fun z _ => P z)) BIG r' hr ks Dc hKP hKF hcD hBC
    hS hU hT hG hL hRTk hSEk hDLk hb hDE hloc hEnvE hgdF
    (fun i hi => by
      have hi' : i < tks.length := by rw [hks, wP_instWF, instW_length] at hi; simpa using hi
      rw [hks, wP_instWF, instW_drop_take]
      exact gcWinU_inst2 (by have := hWS i hi'; rw [hks, wP_instWF] at this; exact this) ρ (i - 1))
    hUn hEnvC hIk
end main

end Formal.Net.AO.Sym
