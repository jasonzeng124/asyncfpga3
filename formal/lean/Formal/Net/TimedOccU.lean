import Formal.Net.TimedOccRT

/-!
# Union claims: a data value held across phases (shard C, data layer)

**Problem, plainly.** A data latch `Q = en ? D : Q` holds one value from the moment its transparent input settles
until it next opens, but the proof of that value differs by phase: while `en` is read high, `Q` follows `D` (its own
feedback is irrelevant); while `en` is read low, `Q` follows its feedback. Each phase is a claim with its own pin
coverage (`TimedOccX.CovTime`, one covering window per pin), and the hold phase's feedback read reaches back into the
transparent phase, so it must be covered by ONE claim spanning both: the union.

**Proved:** `union_holds` (a claim whose window is the union of two claims' windows with the same value holds, when
the first claim's end comes no earlier than the second's start: one `Sep` inequality, `UnionOK`), `chain_holds` (the
same for a chain of claims, `ChainOK`; a latch needs three: transparent, enable read uncertain (both branches agree),
hold), and `timedU_follows`: `TimedR.timedR_follows` where each data-gate claim is either gate-proved or the union of
a chain of gate-proved claims; gate-proved claims may cover their pins (e.g. a latch's feedback) by union claims.

**Not shown here:** any instance.
-/

namespace Formal.Net.OccNet.TimedU
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR

variable {α : Type} [DecidableEq α]

/-- A data-gate claim proved by its gate's function (the `hGC` shape of `TimedOccX`). -/
def GateProof (N : TNet α) (dat : α → Bool) (Sep : α → Nat → α → Nat → Option Nat) (s0 : α → Bool)
    (cl : List (Claim α)) (c : Claim α) : Prop :=
  N.gate c.z = true ∧ 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N s0 cl c cov ∧
    (∀ u ∈ N.pins c.z, ∀ w, covWin s0 cl u (cov u) = some w → CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
    (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u))

/-- `c` is the union of `c1` (same start) and `c2` (same end), same node and value, and `c1` lasts until `c2` starts. -/
def UnionOK (Sep : α → Nat → α → Nat → Option Nat) (c c1 c2 : Claim α) : Prop :=
  c1.z = c.z ∧ c2.z = c.z ∧ c1.val = c.val ∧ c2.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c2.B = c.B ∧ c2.b = c.b ∧
  (match c1.B, c2.A with
    | some e1, some e2 => ∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d
    | none, _ => True
    | some _, none => True)

theorem union_holds {x : α → Nat → Bool} {t0 H T : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (c c1 c2 : Claim α) (hu : UnionOK Sep c c1 c2) (t : Nat) (ht : t ≤ T)
    (h1 : Holds x t0 H c1 t) (h2 : Holds x t0 H c2 t) : Holds x t0 H c t := by
  obtain ⟨hz1, hz2, hv1, hv2, hA1, ha1, hB2, hb2, hj⟩ := hu
  intro hH hA hBn
  by_cases hend : ∃ e1, c1.B = some e1 ∧ hbI x t0 e1 ((t : Int) - c1.b)
  · obtain ⟨e1, he1, hhb⟩ := hend
    rw [← hz2, ← hv2]
    apply h2 hH
    · cases hA2 : c2.A with
      | none => trivial
      | some e2 =>
        rw [he1, hA2] at hj
        obtain ⟨d, hd, hle⟩ := hj
        have := hSS e1.1 e2.1 e1.2 e2.2 d hd _ (by omega) hhb
        exact hbI_mono this (by omega)
    · rw [hB2, hb2]; exact hBn
  · rw [← hz1, ← hv1]
    apply h1 hH
    · rw [hA1, ha1]; exact hA
    · cases hB1 : c1.B with
      | none => trivial
      | some e1 => exact fun hh => hend ⟨e1, hB1, hh⟩

/-- `c` is the union of the consecutive claims `cs` (same node and value; `c` starts with the first, ends with the last;
each lasts until the next starts). -/
def ChainOK (Sep : α → Nat → α → Nat → Option Nat) (c : Claim α) : List (Claim α) → Prop
  | [] => False
  | [c1] => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c1.B = c.B ∧ c1.b = c.b
  | c1 :: c2 :: cs => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧
      (match c1.B, c2.A with
        | some e1, some e2 => ∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d
        | none, _ => True
        | some _, none => True) ∧
      ChainOK Sep ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ (c2 :: cs)

theorem chain_holds {x : α → Nat → Bool} {t0 H T : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (t : Nat) (ht : t ≤ T) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainOK Sep c cs → (∀ c' ∈ cs, Holds x t0 H c' t) → Holds x t0 H c t
  | [], c, h, _ => h.elim
  | [c1], c, h, hh => by
    obtain ⟨hz, hv, hA, ha, hB, hb⟩ := h
    have h1 := hh c1 (by simp)
    intro hH hA' hB'
    rw [← hz, ← hv]
    exact h1 hH (by rw [hA, ha]; exact hA') (by rw [hB, hb]; exact hB')
  | c1 :: c2 :: cs, c, h, hh => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    let c' : Claim α := ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩
    have hc' := chain_holds hSS t ht (c2 :: cs) c' hrest (fun d hd => hh d (by simp [hd]))
    have h1 := hh c1 (by simp)
    exact union_holds hSS c c1 c' ⟨hz, rfl, hv, rfl, hA, ha, rfl, rfl, hj⟩ t ht h1 hc'

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Cert α} {L : α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

/-- **`timedR_follows` with union claims.** -/
theorem timedU_follows (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : LSound CF L)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N CF L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) CP L D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOK N dat CP Up) (hS : SepOKR N CP Sep Up)
    (hTF : TmOK CF)
    (hRT : ∀ u k p, k < CF.len u → p ∈ CF.causes u k → p ∉ CP.causes u k →
      ∃ d, Sep p.1 p.2 u k = some d ∧ 1 ≤ d)
    (hGC : ∀ c ∈ cl, N.gate c.z = true → GateProof N dat Sep (fun w => x w t0) cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainOK Sep c cs)
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, Holds x t0 H c s)
    (hInit : ∀ c ∈ cl, ∀ s, s ≤ t0 → Holds x t0 H c s)
    (hDataLen : ∀ u, dat u = true → CF.len u = 0) :
    ∀ t, (∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N CP x t0 r v s) ∧
      (∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 Sep t := by
  have h0 : Ideal CF (fun _ => 0) := fun u => ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  have hz : ∀ τ, τ ≤ t0 → (fun u => cntE dat x t0 u τ) = fun _ => 0 := by
    intro τ hτ; funext u; unfold cntE; split
    · rfl
    · exact cnt_le_t0 u τ hτ
  have hss0 : ∀ t, t ≤ t0 → SepSound x t0 Sep t := by
    intro t ht a b k m d hd σ hσ hh
    exfalso
    have := cnt_pos hh.2
    omega
  intro t
  induction t with
  | zero =>
    refine ⟨fun τ hτ => ?_, fun v s _ h1 h2 => by omega, fun c hc s hs => hInit c hc s (by omega), hss0 0 (by omega)⟩
    rw [hz τ (by omega)]; exact h0
  | succ t ih =>
    obtain ⟨hI, hB, hC, hSS⟩ := ih
    by_cases ht : t0 ≤ t
    · have hC1 : ∀ v, dat v = false → x v (t + 1) ≠ x v t → ChangeOK N CP x t0 r v (t + 1) :=
        fun v hve hch => change_okR hb hLs hTO hDE hloc hlenEq hgdF hGd t ht hI hB hC hSS v hve hch
      have hB' : ∀ v s, dat v = false → t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOK N CP x t0 r v s := by
        intro v s hve h1 h2 h3
        rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · have : s = t + 1 := by omega
          subst this; exact hC1 v hve (by simpa using h3)
      have hSS' := sepSound_step hb hTP hLs hSE hTO hDE hloc hlenEq hgdF hGd hUp hS t ht hI hB' hC hSS
      refine ⟨fun τ hτ => ?_, hB', fun c hc s hs => ?_, hSS'⟩
      · rcases Nat.lt_or_ge τ (t + 1) with h | h
        · exact hI τ (by omega)
        · have : τ = t + 1 := by omega
          subst this
          apply ideal_step CF (hI t (Nat.le_refl _))
          · intro u
            unfold cntE
            cases hdu : dat u with
            | true => left; rfl
            | false =>
              simp only [Bool.false_eq_true, if_false]
              rw [cnt_succ u t ht]
              by_cases hx : x u (t + 1) = x u t
              · left; simp [hx]
              · right
                refine ⟨by simp [hx], ?_⟩
                obtain ⟨hfb, hen⟩ := hC1 u hdu hx
                have e : nT N x t0 r u (t + 1) u = cnt x t0 u t := by
                  unfold nT ρ
                  by_cases h : reads N u u = true
                  · simp only [h, if_true]; rw [hfb h]; rfl
                  · simp only [h, if_false, Bool.false_eq_true]; rfl
                have hlt : cnt x t0 u t < CF.len u := by rw [← hlenEq, ← e]; exact hen.1
                refine ⟨by simp only [cntE, hdu, Bool.false_eq_true, if_false]; exact hlt, fun p hp => ?_⟩
                simp only [cntE, hdu, Bool.false_eq_true, if_false] at hp
                obtain ⟨hpl, _⟩ := hTF.2 u _ hlt p hp
                have hpe : dat p.1 = false := by
                  cases hd : dat p.1 with
                  | false => rfl
                  | true => have := hDataLen p.1 hd; omega
                simp only [cntE, hpe, Bool.false_eq_true, if_false]
                by_cases hph : p ∈ CP.causes u (cnt x t0 u t)
                · have h1 := hen.2 p (by rw [e]; exact hph)
                  obtain ⟨_, _, h3, _⟩ := rho_boundsX hb u p.1 (t + 1) (by omega)
                  simp only [nT] at h1
                  exact Nat.lt_of_lt_of_le h1 (cnt_mono _ _ _ (by omega))
                · obtain ⟨d, hd, hd1⟩ := hRT u _ p hlt hp hph
                  have hcs := cnt_succ (x := x) (t0 := t0) u t ht
                  have hux : (x u (t + 1) != x u t) = true := by simpa using hx
                  rw [hux] at hcs
                  have := hSS' u p.1 (cnt x t0 u t) p.2 d hd ((t + 1 : Nat) : Int) (Int.le_refl _)
                    ⟨by omega, by simp only [Int.toNat_natCast]; rw [hcs]; simp⟩
                  obtain ⟨h1', h2⟩ := this
                  simp only at h2
                  have := cnt_mono (x := x) (t0 := t0) p.1 (((t + 1 : Nat) : Int) - d).toNat t (by omega)
                  omega
          · intro u; unfold cntE; split
            · exact Nat.le_refl _
            · exact cnt_mono u _ _ (by omega)
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hC c hc s (by omega)
        · have : s = t + 1 := by omega
          subst this
          cases hgz : N.gate c.z with
          | false => exact hEnvC c hc hgz _
          | true =>
            have gp : ∀ c', c' ∈ cl → GateProof N dat Sep (fun w => x w t0) cl c' → Holds x t0 H c' (t + 1) := by
              intro c' _ hp
              obtain ⟨hg', ha, cov, hval, hcov, hkind⟩ := hp
              exact claim_stepR hb t ht hSS' hC c' hg' ha cov hval hcov hkind
            rcases hGC c hc hgz with hp | ⟨cs, hcs, hch⟩
            · exact gp c hc hp
            · exact chain_holds hSS' (t + 1) (Nat.le_refl _) cs c hch (fun c' hc' => gp c' (hcs c' hc').1 (hcs c' hc').2)
    · refine ⟨fun τ hτ => ?_, fun v s hve h1 h2 h3 => ?_, fun c hc s hs => hInit c hc s (by omega), hss0 _ (by omega)⟩
      · rw [hz τ (by omega)]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · omega

end main

end Formal.Net.OccNet.TimedU
