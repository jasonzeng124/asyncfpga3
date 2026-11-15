import Formal.Net.AO.TimedUp

/-!
# External (datapath condition) claims discharged by unit theorems (shard C, 2026-11-15; piece 3, step 1)

**Problem, plainly.** In the timed certificate theorems (`TimedUp.timedA_followsUX`), the 1-bit datapath
conditions the control reads (a `cmpi` result, the shift loop's parity bit) are *external* claims: no window of the
certificate fixes them, because their value depends on the operand words. `timedA_followsUX` takes their truth as
a hypothesis `hExt`. This file proves that hypothesis from a *unit theorem* (the shape of
`Net/Compute/PS/<Unit>T.<unit>_timed_circ`: inputs held on `[T0, T1]` ⇒ output = op of the inputs on
`[T0 + D, T1]`) and the certificate's own (non-external) claims on the unit's inputs.

**The rule (`UnitProof`).** An external claim `c` on node `z` (value `c.val`, window `[τ(A)+a, τ(B)+b)`) is proved
by a unit `(ins, Dc, F)` if
* `UnitFact`: holding every input in `ins` on `[T0, T1]` makes `z = F(inputs)` on `[T0 + Dc, T1]`;
* every input `u` is covered by a non-external claim `w` of the certificate, whose window contains c's window
  widened by `Dc` on the left: `Sep(A_w → A) = d` with `Dc + w.a ≤ c.a + d`, and `Sep(B → B_w) = d'` with
  `c.b ≤ w.b + d'` (or `w` never ends); `0 ≤ w.a`, `0 ≤ c.a`;
* `F` of the covering claims' values is `c.val` (and `F` reads only `ins`).

**Proved.**
* `unit_holds`: under Sep soundness up to `s` and the non-external claims holding up to `s`, a `UnitProof` claim
  holds at `s`.
* `timedA_followsUY`: `timedA_followsUX` with the weaker external-claim hypothesis that may use Sep soundness and the
  non-external claims up to the same time (the induction proves non-external claims at `t + 1` first).
* `unitFact_comp`: chained units compose (delays add); `UnitFact.mono`: extra held inputs are harmless.
* `timedA_followsUnit`, `timedA_liveUnit`: the safety and liveness theorems with `hExt` replaced by a `UnitProof` for
  every external claim.

**Not shown.** That THE target's units and claims meet `UnitProof` (an instance needs each unit's `UnitFact` from its
`_timed_circ` theorem, the corresponding `x`, and certificate claims on the register latch outputs with the
register values: the register-word invariant, piece 3 step 2); external claims whose inputs are themselves external
(chained units: compose the unit theorems first).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]

/-! ## The unit rule -/

/-- A combinational unit from `ins` to `z` with settle delay `Dc`, as the timed unit theorems state it. -/
def UnitFact (x : α → Nat → Bool) (z : α) (ins : List α) (Dc : Nat) (F : (α → Bool) → Bool) : Prop :=
  ∀ T0 T1, (∀ u ∈ ins, ∀ t, T0 ≤ t → t ≤ T1 → x u t = x u T0) →
    ∀ t, T0 + Dc ≤ t → t ≤ T1 → x z t = F (fun u => x u t)

omit [DecidableEq α] in
/-- A unit fact for a sub-list of inputs still holds when more inputs are held. -/
theorem UnitFact.mono {x : α → Nat → Bool} {z : α} {ins ins' : List α} {Dc : Nat} {F : (α → Bool) → Bool}
    (h : UnitFact x z ins Dc F) (hs : ∀ u ∈ ins, u ∈ ins') : UnitFact x z ins' Dc F :=
  fun T0 T1 hh t h1 h2 => h T0 T1 (fun u hu => hh u (hs u hu)) t h1 h2

/-- **Chained units compose:** if `z1 = F1(ins1)` after `D1` and `z = F2(z1, ins2)` after `D2`, and each `F` reads
only its inputs, then `z = F2(F1(ins1), ins2)` after `D1 + D2`, holding `ins1 ++ ins2`. -/
theorem unitFact_comp {x : α → Nat → Bool} {z1 z : α} {ins1 ins2 : List α} {D1 D2 : Nat}
    {F1 F2 : (α → Bool) → Bool} (hu1 : UnitFact x z1 ins1 D1 F1) (hu2 : UnitFact x z (z1 :: ins2) D2 F2)
    (hF1 : ∀ σ σ' : α → Bool, (∀ u ∈ ins1, σ u = σ' u) → F1 σ = F1 σ')
    (hF2 : ∀ σ σ' : α → Bool, (∀ u ∈ z1 :: ins2, σ u = σ' u) → F2 σ = F2 σ') :
    UnitFact x z (ins1 ++ ins2) (D1 + D2) (fun σ => F2 (fun u => if u = z1 then F1 σ else σ u)) := by
  intro T0 T1 hh t ht1 ht2
  have hin1 : ∀ u ∈ ins1, ∀ τ, T0 ≤ τ → τ ≤ T1 → x u τ = x u T0 :=
    fun u hu => hh u (List.mem_append_left _ hu)
  have hF1c : ∀ τ, T0 ≤ τ → τ ≤ T1 → F1 (fun u => x u τ) = F1 (fun u => x u T0) :=
    fun τ h1 h2 => hF1 _ _ (fun u hu => hin1 u hu τ h1 h2)
  have hz1 : ∀ τ, T0 + D1 ≤ τ → τ ≤ T1 → x z1 τ = F1 (fun u => x u T0) := by
    intro τ h1 h2
    rw [hu1 T0 T1 hin1 τ h1 h2, hF1c τ (by omega) h2]
  have hz := hu2 (T0 + D1) T1 (by
      intro u hu τ h1 h2
      rcases List.mem_cons.mp hu with rfl | hu
      · rw [hz1 τ h1 h2, hz1 (T0 + D1) (Nat.le_refl _) (by omega)]
      · rw [hh u (List.mem_append_right _ hu) τ (by omega) h2,
          hh u (List.mem_append_right _ hu) (T0 + D1) (by omega) (by omega)])
    t (by omega) ht2
  rw [hz]
  apply hF2
  intro u hu
  by_cases hu1 : u = z1
  · subst hu1
    simp only [if_true]
    rw [hz1 t (by omega) ht2, hF1c t (by omega) ht2]
  · simp only [hu1, if_false]

/-- The input claim `w` covers the external claim `c`'s window widened by `Dc` on the left. -/
def UnitCovTime (Sep : α → Nat → α → Nat → Option Nat) (Dc : Nat) (c w : Claim α) : Prop :=
  0 ≤ w.a ∧ 0 ≤ c.a ∧
  (∃ e e', c.A = some e ∧ w.A = some e' ∧ ∃ d, Sep e'.1 e'.2 e.1 e.2 = some d ∧ (Dc : Int) + w.a ≤ c.a + d) ∧
  (match w.B with
    | none => True
    | some e' => ∃ e, c.B = some e ∧ ∃ d, Sep e.1 e.2 e'.1 e'.2 = some d ∧ c.b ≤ w.b + d)

/-- The value a claim index stands for (`false` when out of range; never used then). -/
def clVal (cl : List (Claim α)) (i : Nat) : Bool := ((cl[i]?).map Claim.val).getD false

/-- An external claim proved by a unit whose inputs are covered by non-external claims (`cv u`: the index of
the claim covering input `u`). -/
def UnitProof (x : α → Nat → Bool) (Sep : α → Nat → α → Nat → Option Nat) (ext : Claim α → Prop)
    (cl : List (Claim α)) (c : Claim α) : Prop :=
  ∃ (ins : List α) (Dc : Nat) (F : (α → Bool) → Bool) (cv : α → Nat),
    ins ≠ [] ∧ UnitFact x c.z ins Dc F ∧
    (∀ σ σ' : α → Bool, (∀ u ∈ ins, σ u = σ' u) → F σ = F σ') ∧
    (∀ u ∈ ins, ∃ w, cl[cv u]? = some w ∧ w.z = u ∧ ¬ ext w ∧ UnitCovTime Sep Dc c w) ∧
    F (fun u => clVal cl (cv u)) = c.val

/-- A covering input claim holds on the whole widened window `[s - Dc, s]`. -/
theorem unit_input_holds {x : α → Nat → Bool} {t0 H : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Dc : Nat} {c w : Claim α} {e : α × Nat} (s : Nat) (hSS : SepSound x t0 Sep s)
    (hcA : c.A = some e) (hA : hbI x t0 e ((s : Int) - c.a))
    (hB : match c.B with | none => True | some e => ¬ hbI x t0 e ((s : Int) - c.b))
    (hct : UnitCovTime Sep Dc c w) (hw : ∀ τ, τ ≤ s → Holds x t0 H w τ) :
    Dc ≤ s ∧ ∀ τ, s - Dc ≤ τ → τ ≤ s → x w.z τ = w.val := by
  obtain ⟨hwa, hca, ⟨e1, e1', hcA1, hwA1, d1, hd1, hin1⟩, hBw⟩ := hct
  rw [hcA] at hcA1
  cases hcA1
  have hA' := hSS e.1 e1'.1 e.2 e1'.2 d1 hd1 ((s : Int) - c.a) (by omega) hA
  have hs : Dc ≤ s := by have := hA'.1; omega
  refine ⟨hs, fun τ h1 h2 => ?_⟩
  have hwA : hbI x t0 e1' ((τ : Int) - w.a) := hbI_mono hA' (by omega)
  apply hw τ h2
  · obtain ⟨h0, hk⟩ := hwA
    rcases Nat.lt_or_ge (((τ : Int) - w.a).toNat) (t0 + 1) with hlt | hge
    · have := cnt_le_t0 (x := x) (t0 := t0) e1'.1 (((τ : Int) - w.a).toNat) (by omega)
      omega
    · omega
  · rw [hwA1]; exact hwA
  · revert hBw
    cases hwB : w.B with
    | none => intro _; trivial
    | some e' =>
      intro hBw hh
      obtain ⟨eB, hcB, d2, hd2, hin2⟩ := hBw
      rw [hcB] at hB
      have := hSS e'.1 eB.1 e'.2 eB.2 d2 hd2 ((τ : Int) - w.b) (by omega) hh
      exact hB (hbI_mono this (by omega))

/-- **A `UnitProof` claim holds at `s`**, given Sep soundness and the non-external claims up to `s`. -/
theorem unit_holds {x : α → Nat → Bool} {t0 H : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {ext : Claim α → Prop} {cl : List (Claim α)} {c : Claim α} (hU : UnitProof x Sep ext cl c) (s : Nat)
    (hSS : SepSound x t0 Sep s) (hNE : ∀ c' ∈ cl, ¬ ext c' → ∀ τ, τ ≤ s → Holds x t0 H c' τ) :
    Holds x t0 H c s := by
  obtain ⟨ins, Dc, F, cv, hne, hUF, hFd, hcov, hval⟩ := hU
  intro _ hA hB
  obtain ⟨u0, hu0⟩ := List.exists_mem_of_ne_nil ins hne
  obtain ⟨w0, _, _, _, _, _, ⟨e, _, hcA, _⟩, _⟩ := hcov u0 hu0
  rw [hcA] at hA
  have key : ∀ u ∈ ins, Dc ≤ s ∧ ∀ τ, s - Dc ≤ τ → τ ≤ s → x u τ = clVal cl (cv u) := by
    intro u hu
    obtain ⟨w, hw, hwz, hwx, hct⟩ := hcov u hu
    have hmem : w ∈ cl := List.mem_of_getElem? hw
    obtain ⟨hs, hh⟩ := unit_input_holds s hSS hcA hA hB hct (hNE w hmem hwx)
    refine ⟨hs, fun τ h1 h2 => ?_⟩
    have e1 := hh τ h1 h2
    rw [hwz] at e1
    rw [e1]
    simp [clVal, hw]
  have hs : Dc ≤ s := (key u0 hu0).1
  have hz := hUF (s - Dc) s (fun u hu τ h1 h2 => by
      rw [(key u hu).2 τ h1 h2, (key u hu).2 (s - Dc) (Nat.le_refl _) (by omega)])
    s (by omega) (Nat.le_refl _)
  rw [hz, ← hval]
  exact hFd _ _ (fun u hu => (key u hu).2 s (by omega) (Nat.le_refl _))

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Cert α} {L : α → α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

/-- **Every bounded-delay behaviour follows the full certificate**, with external claims whose proof may use Sep
soundness and the non-external claims up to the same time. -/
theorem timedA_followsUY (ext : Claim α → Prop) [DecidablePred ext] (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
    (hGC : ∀ c ∈ cl, ¬ ext c → N.gate c.z = true → GateProof N dat Sep (fun w => x w t0) cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUOK Sep Up c cs)
    (hExt : ∀ c ∈ cl, ext c → ∀ s, t0 < s → (∀ τ, τ ≤ s → Ideal CF (fun u => cntE dat x t0 u τ)) →
      SepSound x t0 Sep s → (∀ c' ∈ cl, ¬ ext c' → ∀ τ, τ ≤ s → Holds x t0 H c' τ) → Holds x t0 H c s)
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
      have hNE : ∀ c ∈ cl, ¬ ext c → Holds x t0 H c (t + 1) := by
        intro c hc hx
        cases hgz : N.gate c.z with
        | false => exact hEnvC c hc hgz _ hI'
        | true =>
          have gp : ∀ c', c' ∈ cl → GateProof N dat Sep (fun w => x w t0) cl c' → Holds x t0 H c' (t + 1) := by
            intro c' _ hp
            obtain ⟨hg', ha, cov, hval, hcov, hkind⟩ := hp
            exact claim_stepR hb t ht hSS' hC c' hg' ha cov hval hcov hkind
          rcases hGC c hc hx hgz with hp | ⟨cs, hcs, hch⟩
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
      have hNE' : ∀ c ∈ cl, ¬ ext c → ∀ τ, τ ≤ t + 1 → Holds x t0 H c τ := by
        intro c hc hx τ hτ
        rcases Nat.lt_or_ge τ (t + 1) with h | h
        · exact hC c hc τ (by omega)
        · have : τ = t + 1 := by omega
          subst this; exact hNE c hc hx
      refine ⟨hI', hB', fun c hc s hs => ?_, hSS'⟩
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · exact hC c hc s (by omega)
      · have : s = t + 1 := by omega
        subst this
        by_cases hx : ext c
        · exact hExt c hc hx (t + 1) (by omega) hI' hSS' hNE'
        · exact hNE c hc hx
    · refine ⟨fun τ hτ => ?_, fun v s hve h1 h2 h3 => ?_, fun c hc s hs => hInit c hc s (by omega), hss0 _ (by omega)⟩
      · rw [hz τ (by omega)]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · omega

/-! ## Liveness -/


/-- **Safety with unit-proved external claims.** -/
theorem timedA_followsUnit (ext : Claim α → Prop) [DecidablePred ext] (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
    (hGC : ∀ c ∈ cl, ¬ ext c → N.gate c.z = true → GateProof N dat Sep (fun w => x w t0) cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUOK Sep Up c cs)
    (hU : ∀ c ∈ cl, ext c → UnitProof x Sep ext cl c)
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, (∀ τ, τ ≤ s → Ideal CF (fun u => cntE dat x t0 u τ)) →
      Holds x t0 H c s)
    (hInit : ∀ c ∈ cl, ∀ s, s ≤ t0 → Holds x t0 H c s)
    (hDataLen : ∀ u, dat u = true → CF.len u = 0) :
    ∀ t, (∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s) ∧
      (∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 Sep t :=
  timedA_followsUY ext hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC
    (fun c hc hx s _ _ hSS hNE => unit_holds (hU c hc hx) s hSS hNE) hEnvC hInit hDataLen

/-- **Liveness with unit-proved external claims.** -/
theorem timedA_liveUnit (ext : Claim α → Prop) [DecidablePred ext] (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
    (hGC : ∀ c ∈ cl, ¬ ext c → N.gate c.z = true → GateProof N dat Sep (fun w => x w t0) cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUOK Sep Up c cs)
    (hU : ∀ c ∈ cl, ext c → UnitProof x Sep ext cl c)
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
  have hfol := timedA_followsUnit ext hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hU
    hEnvC hInit hDataLen
  exact timedA_liveUX ext hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC
    (fun c hc _ s _ => (hfol s).2.2.1 c hc s (Nat.le_refl _)) hEnvC hInit hDataLen hCPsub U hcov K hK hne henv

end main

end Formal.Net.AO
