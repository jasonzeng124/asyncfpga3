import Formal.Net.AO.Timed
import Formal.Net.TimedOccUp

/-!
# `timedA_follows` with upper-bound joins of claims (shard C, 2026-11-10)

**Problem.** The one-pair data layer at corner c = 0 needs claims joined by an upper bound (`TimedOccUp.ChainUOK`),
which `timedA_follows`'s claim hypothesis `hGC` (with `ChainOK`) does not admit.

**Proved** (`timedA_followsU`): `timedA_follows` with `ChainOK` replaced by `ChainUOK` in `hGC`, same conclusion. The
proof is `timedA_follows`'s, except at the claim step: an upper-bound join at time `t + 1` (which asks `1 ≤ c2.a`)
needs the Up table sound only up to `t`, which `up_sound` gives from the induction hypothesis.

Also `gate_firesAU`, `timedA_liveU`: the liveness theorem with the same change (proofs copied, calls redirected).

**Not shown:** that the c = 0 data layer passes with the new rule.
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


/-- **An enabled exact gate event happens within `K`.** -/
theorem gate_firesAU (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
    (hDataLen : ∀ u, dat u = true → CF.len u = 0)
    (hCPsub : ∀ u k, ∀ altF ∈ CF.causes u k, ∃ altP ∈ CP.causes u k, ∀ p ∈ altP, p ∈ altF)
    (v : α) (hve : dat v = false) (hg : N.gate v = true) (K : Nat) (hK : ∀ w ∈ N.pins v, N.hi v w < K) (hK1 : 1 ≤ K)
    (t : Nat) (ht : t0 ≤ t) (hen : Enabled CF (fun u => cntE dat x t0 u t) v) :
    cnt x t0 v t < cnt x t0 v (t + K) := by
  rcases Nat.lt_or_ge (cnt x t0 v t) (cnt x t0 v (t + K - 1)) with hlt | hge
  · exact Nat.lt_of_lt_of_le hlt (cnt_mono v _ _ (by omega))
  · have hconst : ∀ τ, t ≤ τ → τ ≤ t + K - 1 → cnt x t0 v τ = cnt x t0 v t := by
      intro τ h1 h2
      have := cnt_mono (x := x) (t0 := t0) v t τ h1
      have := cnt_mono (x := x) (t0 := t0) v τ (t + K - 1) h2
      omega
    let t' := t + K - 1
    obtain ⟨hI, hB, hC, hSS⟩ := timedA_followsU hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hEnvC hInit hDataLen t'
    have hcons := read_consistentA hb hLs hTO hDE t' (by omega) hI hB hSS v
    have hlen : ∀ u ∈ D v, nT N x t0 r v (t' + 1) u ≤ CP.len u := by
      intro u hu
      obtain ⟨_, _, h3, _⟩ := rho_boundsX hb v u (t' + 1) (by omega)
      have := (hI (ρ N r v u (t' + 1)) (by omega) u).1
      simp only [cntE, hDE v u hu, Bool.false_eq_true, if_false] at this
      rw [hlenEq]; exact this
    have hbb : ∀ z, dat z = true → z ∈ N.pins v → ∀ val,
        dv cl (gd v z) (nT N x t0 r v (t' + 1)) = some val → x z (r v z (t' + 1)) = val :=
      fun z _ hz val hdv => guard_readR hb t' (by omega) hSS hC v z hg hz (hGd v z hg hz) val hdv
    have hL := hloc v hg hve (nT N x t0 r v (t' + 1)) hlen hcons (own_readA hb t' (by omega) hB v hve) (fun w => x w (r v w (t' + 1))) hbb
    have hρ : ∀ w, t ≤ ρ N r v w (t' + 1) := by
      intro w
      unfold ρ
      by_cases h : reads N v w = true
      · simp only [h, if_true]
        simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨_, h2, h3, _⟩ := hb.rd v w (t' + 1) h.1 h.2 (by omega)
        have := hK w h.2
        omega
      · simp only [h, if_false, Bool.false_eq_true]; omega
    have hnv : nT N x t0 r v (t' + 1) v = cnt x t0 v t := by
      have h1 := hρ v
      obtain ⟨_, _, h3, _⟩ := rho_boundsX hb v v (t' + 1) (by omega)
      exact hconst _ h1 (by omega)
    have hEn : Enabled CP (nT N x t0 r v (t' + 1)) v := by
      have hlt : cnt x t0 v t < CP.len v := by rw [hlenEq]; have := hen.1; simpa [cntE, hve] using this
      obtain ⟨_, altF, haltF, hinF⟩ := hen
      have haltF' : altF ∈ CF.causes v (cnt x t0 v t) := by simpa [cntE, hve] using haltF
      obtain ⟨altP, haltP, hsub⟩ := hCPsub v _ altF haltF'
      refine ⟨by rw [hnv]; exact hlt, altP, by rw [hnv]; exact haltP, fun p hp => ?_⟩
      have hpF := hsub p hp
      obtain ⟨hpl, _⟩ := hTP.2 v _ hlt altP haltP p hp
      have hen2 := hinF p hpF
      have hpe : dat p.1 = false := by
        cases hd : dat p.1 with
        | false => rfl
        | true => have := hDataLen p.1 hd; rw [← hlenEq] at this; omega
      simp only [cntE, hpe, Bool.false_eq_true, if_false] at hen2
      simp only [nT]
      exact Nat.lt_of_lt_of_le hen2 (cnt_mono p.1 _ _ (hρ p.1))
    have he := hL.2 hEn
    unfold tEn at he; rw [hg] at he; simp only [if_true] at he
    have hgeq := hb.geq v (t' + 1) hg (by omega)
    rw [pins_readX hb v hg (t' + 1) (by omega)] at hgeq
    have hmixv : mix dat (st (fun w => x w t0) (nT N x t0 r v (t' + 1))) (fun w => x w (r v w (t' + 1))) v =
        st (fun w => x w t0) (nT N x t0 r v (t' + 1)) v := by simp [mix, hve]
    rw [hmixv, ← hgeq] at he
    have hst : st (fun w => x w t0) (nT N x t0 r v (t' + 1)) v = x v t' := by
      rw [x_eq_st v H (fun s' h1 h2 => hb.quiet v s' hve h1 h2) t' (by omega)]
      simp only [st]; rw [hnv, hconst t' (by omega) (Nat.le_refl _)]
    rw [hst] at he
    have hc := cnt_succ (x := x) (t0 := t0) v t' (by omega)
    have hx : (x v (t' + 1) != x v t') = true := he
    rw [hx] at hc
    have e : t' + 1 = t + K := by omega
    rw [← e, hc, hconst t' (by omega) (Nat.le_refl _)]
    simp

/-- **Liveness with the data layer.** If every enabled environment move eventually happens, every event of the
certificate happens: from some `T` on every exact node has had exactly its `len` changes and never changes again. -/
theorem timedA_liveU (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
    (hDataLen : ∀ u, dat u = true → CF.len u = 0)
    (hCPsub : ∀ u k, ∀ altF ∈ CF.causes u k, ∃ altP ∈ CP.causes u k, ∀ p ∈ altP, p ∈ altF)
    (U : List α) (hcov : ∀ u, 0 < CF.len u → u ∈ U)
    (K : α → Nat) (hK : ∀ v, N.gate v = true → 1 ≤ K v ∧ ∀ w ∈ N.pins v, N.hi v w < K v)
    (hne : ∀ u k, CF.causes u k ≠ [])
    (henv : ∀ u t, N.gate u = false → dat u = false → t0 ≤ t → Enabled CF (fun w => cntE dat x t0 w t) u →
      ∃ t', t < t' ∧ cnt x t0 u t < cnt x t0 u t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cntE dat x t0 u T = CF.len u) ∧ ∀ u s, dat u = false → T ≤ s → x u s = x u T := by
  have hfol := timedA_followsU hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hEnvC hInit hDataLen
  have hI : ∀ t, Ideal CF (fun u => cntE dat x t0 u t) := fun t => (hfol t).1 t (Nat.le_refl _)
  have prog : ∀ t, t0 ≤ t → (∃ u, cntE dat x t0 u t < CF.len u) →
      ∃ t', t < t' ∧ ∃ v, v ∈ U ∧ cntE dat x t0 v t < cntE dat x t0 v t' := by
    intro t ht ⟨u, hu⟩
    obtain ⟨v, hv⟩ := enabled_of_not_full hTF (hI t) hne _ u hu (Nat.le_refl _)
    have hvl : 0 < CF.len v := by have := hv.1; omega
    have hvU : v ∈ U := hcov v hvl
    have hve : dat v = false := by
      cases hd : dat v with
      | false => rfl
      | true => have := hDataLen v hd; omega
    cases hg : N.gate v with
    | true =>
      obtain ⟨hK1, hK2⟩ := hK v hg
      have := gate_firesAU hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hEnvC hInit hDataLen hCPsub v hve hg (K v) hK2 hK1 t ht hv
      exact ⟨t + K v, by omega, v, hvU, by simp only [cntE, hve, Bool.false_eq_true, if_false]; exact this⟩
    | false =>
      obtain ⟨t', h1, h2⟩ := henv v t hg hve ht hv
      exact ⟨t', h1, v, hvU, by simp only [cntE, hve, Bool.false_eq_true, if_false]; exact h2⟩
  have hmonoE : ∀ u a b, a ≤ b → cntE dat x t0 u a ≤ cntE dat x t0 u b := by
    intro u a b hab; unfold cntE; split
    · exact Nat.le_refl _
    · exact cnt_mono u _ _ hab
  let M : Nat → Nat := fun t => sumOver U fun u => CF.len u - cntE dat x t0 u t
  have hMdec : ∀ t t', t ≤ t' → ∀ v ∈ U, cntE dat x t0 v t < cntE dat x t0 v t' → M t' < M t := by
    intro t t' htt v hv hlt
    have hle : ∀ u ∈ U, CF.len u - cntE dat x t0 u t' ≤ CF.len u - cntE dat x t0 u t := fun u _ => by
      have := hmonoE u t t' htt; omega
    have hlt' : CF.len v - cntE dat x t0 v t' < CF.len v - cntE dat x t0 v t := by
      have := (hI t' v).1; simp only at this; omega
    exact sumOver_lt hle v hv hlt'
  have full : ∀ n t, t0 ≤ t → M t ≤ n → ∃ T, t ≤ T ∧ ∀ u, cntE dat x t0 u T = CF.len u := by
    intro n
    induction n with
    | zero =>
      intro t ht hM
      refine ⟨t, Nat.le_refl _, fun u => ?_⟩
      rcases Nat.lt_or_ge (cntE dat x t0 u t) (CF.len u) with hlt | hge
      · exfalso
        have hpos := hcov u (by omega)
        have := sumOver_lt (U := U) (f := fun _ => 0) (g := fun u => CF.len u - cntE dat x t0 u t)
          (fun _ _ => Nat.zero_le _) u hpos (by omega)
        rw [sumOver_zero] at this
        simp only [M] at hM; omega
      · have := (hI t u).1; simp only at this; omega
    | succ n ih =>
      intro t ht hM
      by_cases hall : ∀ u, cntE dat x t0 u t = CF.len u
      · exact ⟨t, Nat.le_refl _, hall⟩
      · simp only [Classical.not_forall] at hall
        obtain ⟨u, hu⟩ := hall
        obtain ⟨t', h1, v, hv, h2⟩ := prog t ht ⟨u, Nat.lt_of_le_of_ne (by have := (hI t u).1; simpa using this) hu⟩
        have := hMdec t t' (by omega) v hv h2
        obtain ⟨T, hT1, hT2⟩ := ih t' (by omega) (by omega)
        exact ⟨T, by omega, hT2⟩
  obtain ⟨T, hT1, hT2⟩ := full (M t0) t0 (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨T, hT1, hT2, fun u s hue hs => ?_⟩
  have hc : ∀ s, T ≤ s → cnt x t0 u s = cnt x t0 u T := by
    intro s hs
    have h1 := hmonoE u T s hs
    have h2 := (hI s u).1
    simp only at h2
    have h3 := hT2 u
    simp only [cntE, hue, Bool.false_eq_true, if_false] at h1 h2 h3 ⊢
    omega
  rw [x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hue h1 h2) s (by omega),
    x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hue h1 h2) T (by omega)]
  simp only [st]; rw [hc s hs]


end main

end Formal.Net.AO
