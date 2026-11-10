import Formal.Net.AO.Timed
import Formal.Net.TimedOccUp

/-!
# `timedA_follows` with upper-bound joins of claims (shard C, 2026-11-10)

**Problem.** The one-pair data layer at corner c = 0 needs claims joined by an upper bound (`TimedOccUp.ChainUOK`),
which `timedA_follows`'s claim hypothesis `hGC` (with `ChainOK`) does not admit.

**Proved** (`timedA_followsU`): `timedA_follows` with `ChainOK` replaced by `ChainUOK` in `hGC`, same conclusion. The
proof is `timedA_follows`'s, except at the claim step: an upper-bound join at time `t + 1` (which asks `1 ≤ c2.a`)
needs the Up table sound only up to `t`, which `up_sound` gives from the induction hypothesis.

**Not shown:** the liveness version (`timedA_live` takes `timedA_follows`'s hypotheses; a `ChainUOK` variant would
follow the same way but is not written); that the c = 0 data layer passes with the new rule.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Cert α} {L : α → α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

/-- **Every bounded-delay behaviour follows the full certificate**, with claims joined by separations or upper bounds. -/
theorem timedA_followsU (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → LCheckXA N dat envEn (fun w => x w t0) CP (L v) D cl gd v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal CF (fun u => cntE dat x t0 u (s - 1)) → Enabled CP (fun w => cnt x t0 w (s - 1)) v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOKA N dat CP Sep Up) (hS : SepOKA N CP Sep Up)
    (hTF : TmOK CF)
    (hRT : ∀ u k, k < CF.len u → ∀ altP ∈ CP.causes u k, ∃ altF ∈ CF.causes u k, ∀ p ∈ altF,
      p ∈ altP ∨ ∃ d, Sep p.1 p.2 u k = some d ∧ 1 ≤ d)
    (hGC : ∀ c ∈ cl, N.gate c.z = true → GateProof N dat Sep (fun w => x w t0) cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUOK Sep Up c cs)
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, (∀ τ, τ ≤ s → Ideal CF (fun u => cntE dat x t0 u τ)) →
      Holds x t0 H c s)
    (hInit : ∀ c ∈ cl, ∀ s, s ≤ t0 → Holds x t0 H c s)
    (hDataLen : ∀ u, dat u = true → CF.len u = 0) :
    ∀ t, (∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s) ∧
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
    · have hC1 : ∀ v, dat v = false → x v (t + 1) ≠ x v t → ChangeOKA N CP x t0 r v (t + 1) :=
        fun v hve hch => change_okA hb hLs hTO hDE hloc hEnvE hlenEq hgdF hGd t ht hI hB hC hSS v hve hch
      have hB' : ∀ v s, dat v = false → t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s := by
        intro v s hve h1 h2 h3
        rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · have : s = t + 1 := by omega
          subst this; exact hC1 v hve (by simpa using h3)
      have hSS' := sepSound_step hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS t ht hI hB' hC hSS
      have hI' : ∀ τ, τ ≤ t + 1 → Ideal CF (fun u => cntE dat x t0 u τ) := by
        intro τ hτ
        rcases Nat.lt_or_ge τ (t + 1) with h | h
        · exact hI τ (by omega)
        · have : τ = t + 1 := by omega
          subst this
          apply ideal_stepA CF (hI t (Nat.le_refl _))
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
                obtain ⟨_, altP, haltP, hinP⟩ := hen
                rw [e] at haltP
                obtain ⟨altF, haltF, hF⟩ := hRT u _ hlt altP haltP
                refine ⟨by simp only [cntE, hdu, Bool.false_eq_true, if_false]; exact hlt, altF,
                  by simp only [cntE, hdu, Bool.false_eq_true, if_false]; exact haltF, fun p hp => ?_⟩
                obtain ⟨hpl, _⟩ := hTF.2 u _ hlt altF haltF p hp
                have hpe : dat p.1 = false := by
                  cases hd : dat p.1 with
                  | false => rfl
                  | true => have := hDataLen p.1 hd; omega
                simp only [cntE, hpe, Bool.false_eq_true, if_false]
                rcases hF p hp with hph | ⟨d, hd, hd1⟩
                · have h1 := hinP p hph
                  obtain ⟨_, _, h3, _⟩ := rho_boundsX hb u p.1 (t + 1) (by omega)
                  simp only [nT] at h1
                  exact Nat.lt_of_lt_of_le h1 (cnt_mono _ _ _ (by omega))
                · have hcs := cnt_succ (x := x) (t0 := t0) u t ht
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
      refine ⟨hI', hB', fun c hc s hs => ?_, hSS'⟩
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · exact hC c hc s (by omega)
      · have : s = t + 1 := by omega
        subst this
        cases hgz : N.gate c.z with
        | false => exact hEnvC c hc hgz _ hI'
        | true =>
          have gp : ∀ c', c' ∈ cl → GateProof N dat Sep (fun w => x w t0) cl c' → Holds x t0 H c' (t + 1) := by
            intro c' _ hp
            obtain ⟨hg', ha, cov, hval, hcov, hkind⟩ := hp
            exact claim_stepR hb t ht hSS' hC c' hg' ha cov hval hcov hkind
          rcases hGC c hc hgz with hp | ⟨cs, hcs, hch⟩
          · exact gp c hc hp
          · have hUS : UpSoundI x t0 Up t := by
              intro e1 e2 u hU σ hσ h1
              obtain ⟨hσ0, h1'⟩ := h1
              have := up_sound hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS t hI
                (fun v s h1 h2 h3 h4 => hB v s h1 h2 (by omega) h4) hC hSS e1 σ.toNat h1' _ e2 u (Nat.le_refl _) hU
                (by omega)
              refine ⟨by omega, ?_⟩
              have e : (σ + (u : Int)).toNat = σ.toNat + u := by omega
              rw [e]; exact this
            exact chainU_holds hSS' hUS (t + 1) (Nat.le_refl _) (Nat.le_refl _) cs c hch
              (fun c' hc' => gp c' (hcs c' hc').1 (hcs c' hc').2)
    · refine ⟨fun τ hτ => ?_, fun v s hve h1 h2 h3 => ?_, fun c hc s hs => hInit c hc s (by omega), hss0 _ (by omega)⟩
      · rw [hz τ (by omega)]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · omega

/-! ## Liveness -/


end main

end Formal.Net.AO
