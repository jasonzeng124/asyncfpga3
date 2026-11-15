import Formal.Net.AO.SymWord

/-!
# The local check is value-independent when guards read only literal claims (shard C, 2026-11-15)

**Problem.** `SymWord.timedA_follows_sym` still states the long local check `hloc` on the instantiated word, i.e.
per pair. The local check reads claims only through guards (`dv`: the value of the guarded claim). In the intended
use the control's guards read condition claims, whose values are literals of the kind. Then is `hloc` the same for
every assignment?

**Proved.** `dv_congr_cl`, `lcheckXA_congr_cl`: the local check depends on the claim list only through the values of
the guarded claims. `lcheckXA_inst`: if every claim a guard of `v` points to is a literal template (`GuardLit`), the
local check of the instantiation under `ρ` holds iff it holds under `ρ'`; so it is checked once (e.g. at
`ρ = fun _ => false`) for every pair.

**Not shown.** That THE target's guards read only literal claims (a decidable per-kind fact of the instance).
-/

namespace Formal.Net.AO.Sym
open Formal.Net.OccNet (st)
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.AO

variable {α V : Type} [DecidableEq α]

theorem dv_congr_cl {cl cl' : List (Claim α)} {gs : List (Guard α)}
    (h : ∀ g ∈ gs, (cl[g.ci]?).map Claim.val = (cl'[g.ci]?).map Claim.val) (n : α → Nat) :
    dv cl gs n = dv cl' gs n := by
  unfold dv
  cases hf : gs.find? (guardOn n) with
  | none => rfl
  | some g => exact h g (List.mem_of_find?_eq_some hf)

theorem lcheckXA_congr_cl {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α} {cl cl' : List (Claim α)} {gd : α → α → List (Guard α)}
    {v : α} (h : ∀ z, ∀ g ∈ gd v z, (cl[g.ci]?).map Claim.val = (cl'[g.ci]?).map Claim.val) :
    LCheckXA N dat envEn s0 C L D cl gd v ↔ LCheckXA N dat envEn s0 C L D cl' gd v := by
  have e : ∀ z n, dv cl (gd v z) n = dv cl' (gd v z) n := fun z n => dv_congr_cl (h z) n
  simp only [LCheckXA, e]

/-- Every claim a guard of `v` points to is a literal template. -/
def GuardLit (tcl : List (TClaim α V)) (gd : α → α → List (Guard α)) (v : α) : Prop :=
  ∀ z, ∀ g ∈ gd v z, ∀ c, tcl[g.ci]? = some c → ∃ b, c.sv = .lit b

omit [DecidableEq α] in
theorem guard_val_inst {tcl : List (TClaim α V)} {i : Nat} (hl : ∀ c, tcl[i]? = some c → ∃ b, c.sv = .lit b)
    (ρ ρ' : V → Bool) : ((instL ρ tcl)[i]?).map Claim.val = ((instL ρ' tcl)[i]?).map Claim.val := by
  rw [instL_get, instL_get]
  cases ht : tcl[i]? with
  | none => rfl
  | some c =>
    obtain ⟨b, hb⟩ := hl c ht
    simp [TClaim.inst, hb, SVal.eval]

/-- **With literal guarded claims, the local check is the same under every assignment.** -/
theorem lcheckXA_inst {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α} {tcl : List (TClaim α V)} {gd : α → α → List (Guard α)}
    {v : α} (hg : GuardLit tcl gd v) (ρ ρ' : V → Bool) :
    LCheckXA N dat envEn s0 C L D (instL ρ tcl) gd v ↔ LCheckXA N dat envEn s0 C L D (instL ρ' tcl) gd v :=
  lcheckXA_congr_cl (fun z g hgz => guard_val_inst (hg z g hgz) ρ ρ')

end Formal.Net.AO.Sym
