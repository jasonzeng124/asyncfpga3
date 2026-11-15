import Formal.Net.AO.SymUnroll

/-!
# Template claims joined in chains (shard C, 2026-11-15; piece 3, step 2.2b)

**Problem.** `SymUnroll.gc_unrollU_sym` lifts only the GateProof alternative of `GcWinU` to templates. THE target's
data layer proves latch claims as chains of phase claims joined by separations or upper bounds (`ChainUOK`; the c = 0
residue needed the upper-bound joins). The chain rule compares claim values. Does it lift to templates?

**Proved.** `TChainUOK` (the chain rule on templates, comparing symbolic values `sv`) and `chainUOK_inst`: it gives
`ChainUOK` of the instantiated claims under every assignment. `GcWinS2` (template sub-word check with both
alternatives), `gcWinU_inst2`, and `gc_unrollU_sym2`: `hGC` of the long certificate of every instantiated word.

**Not shown.** The instance.
-/

namespace Formal.Net.AO.Sym
open Formal.Net.OccNet (st)
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX
  Formal.Net.OccNet.TimedU Formal.Net.AO

variable {α V0 : Type} [DecidableEq α] [DecidableEq V0]

/-- `ChainUOK` on templates: equal symbolic values instead of equal values. -/
def TChainUOK {V : Type} (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat)
    (c : TClaim α V) : List (TClaim α V) → Prop
  | [] => False
  | [c1] => c1.z = c.z ∧ c1.sv = c.sv ∧ c1.A = c.A ∧ c1.a = c.a ∧ c1.B = c.B ∧ c1.b = c.b
  | c1 :: c2 :: cs => c1.z = c.z ∧ c1.sv = c.sv ∧ c1.A = c.A ∧ c1.a = c.a ∧
      (match c1.B, c2.A with
        | some e1, some e2 => (∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d) ∨
            (∃ u, Up e1 e2 = some u ∧ 1 ≤ c2.a ∧ c2.a + (u : Int) ≤ c1.b)
        | none, _ => True
        | some _, none => True) ∧
      TChainUOK Sep Up ⟨c.z, c.sv, c2.A, c2.a, c.B, c.b⟩ (c2 :: cs)

omit [DecidableEq α] in
theorem chainUOK_inst {V : Type} {Sep : α → Nat → α → Nat → Option Nat} {Up : α × Nat → α × Nat → Option Nat}
    (ρ : V → Bool) : ∀ (cs : List (TClaim α V)) (c : TClaim α V), TChainUOK Sep Up c cs →
      ChainUOK Sep Up (c.inst ρ) (cs.map (TClaim.inst ρ))
  | [], _, h => h.elim
  | [c1], c, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, by simp [TClaim.inst, h2], h3, h4, h5, h6⟩
  | c1 :: c2 :: cs, c, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h1, by simp [TClaim.inst, h2], h3, h4, h5, ?_⟩
    exact chainUOK_inst ρ (c2 :: cs) ⟨c.z, c.sv, c2.A, c2.a, c.B, c.b⟩ h6

/-- **The template sub-word check with both alternatives** (GateProof, or a chain of GateProof-proved claims). -/
def GcWinS2 (N : TNet α) (dat : α → Bool) (P : α → Prop) (s0 : α → Bool) (ts : List (TKind α V0)) (t : Nat) :
    Prop :=
  ∀ (h : t < ts.length), ∀ c0 ∈ ts[t].tcl, ¬ P c0.z → N.gate c0.z = true →
    GateProofWS N dat (WSep (ts.map TKind.k)) s0 (uclTT 0 ts (fun _ => 0)) t
      ((c0.rn t).sh (off (wt (ts.map TKind.k)) t)) ∨
    ∃ cs : List (TClaim α (Nat × V0)), (∀ c' ∈ cs, c' ∈ uclTT 0 ts (fun _ => 0) ∧
      GateProofWS N dat (WSep (ts.map TKind.k)) s0 (uclTT 0 ts (fun _ => 0)) t c') ∧
      TChainUOK (WSep (ts.map TKind.k)) (WUp (ts.map TKind.k)) ((c0.rn t).sh (off (wt (ts.map TKind.k)) t)) cs

theorem gcWinU_inst2 {N : TNet α} {dat : α → Bool} {P : α → Prop} {s0 : α → Bool} {ts : List (TKind α V0)}
    {t : Nat} (h : GcWinS2 N dat P s0 ts t) (ρ : Nat × V0 → Bool) (n : Nat) :
    GcWinU N dat (fun c => P c.z) s0 (instW ρ n ts) t := by
  intro ht c0 hc0 hx hg
  have ht' : t < ts.length := by rw [instW_length] at ht; exact ht
  rw [instW_get ρ n ts t ht ht'] at hc0
  simp only [TKind.inst, instL, List.mem_map] at hc0
  obtain ⟨c, hc, rfl⟩ := hc0
  have hP : ¬ P c.z := hx
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
  rw [e1, WSep_instW, WUp_instW, e2]
  rcases h ht' c hc hP hg with hG | ⟨cs, hcs, hch⟩
  · left; exact gateProofW_inst hG _
  · right
    refine ⟨cs.map (TClaim.inst (fun q => ρ (n + q.1, q.2))), ?_, chainUOK_inst _ cs _ hch⟩
    intro c' hc'
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hm, hp⟩ := hcs c'' hc''
    exact ⟨List.mem_map.mpr ⟨c'', hm, rfl⟩, gateProofW_inst hp _⟩

/-- **`hGC` of the long certificate of every instantiated word from the template sub-word checks**, both
alternatives. -/
theorem gc_unrollU_sym2 (N : TNet α) (dat : α → Bool) (P : α → Prop) (r : Nat) (hr : 2 ≤ r)
    (tks : List (TKind α V0)) (ρ : Nat × V0 → Bool) (s0 : α → Bool) (sw : Nat → α → Bool)
    (hsw : ∀ i, i < tks.length → ∀ w ∈ ((instW ρ 0 tks).drop (i - 1)).take r, ∀ c0 ∈ w.cl, ∀ u ∈ N.pins c0.z,
      sw i u = st s0 (off (wt (instW ρ 0 tks)) (i - 1)) u)
    (hW : ∀ i, i < tks.length → GcWinS2 N dat P (sw i) ((tks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk (instW ρ 0 tks)) (fun _ => 0), ¬ P c.z → N.gate c.z = true →
      GateProof N dat (LSep (instW ρ 0 tks)) s0 (uclT (wk (instW ρ 0 tks)) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk (instW ρ 0 tks)) (fun _ => 0) ∧
        GateProof N dat (LSep (instW ρ 0 tks)) s0 (uclT (wk (instW ρ 0 tks)) (fun _ => 0)) c') ∧
        ChainUOK (LSep (instW ρ 0 tks)) (LUp (instW ρ 0 tks)) c cs :=
  gc_unrollU_gen N dat (fun c => P c.z) (extShift_node (fun z _ => P z)) r hr (instW ρ 0 tks) s0 sw
    (fun i hi => hsw i (by rw [instW_length] at hi; exact hi))
    (fun i hi => by
      rw [instW_drop_take]
      exact gcWinU_inst2 (hW i (by rw [instW_length] at hi; exact hi)) ρ (i - 1))

end Formal.Net.AO.Sym
