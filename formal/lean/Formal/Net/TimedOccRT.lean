import Formal.Net.TimedOccX

/-!
# Timed occurrence nets with relative-timing edges (shard C, S4)

**Problem, plainly.** THE target's control is not persistent by itself: in 18 C-elements a falling excitation
can be withdrawn by another node's move (JOURNAL-C 2026-11-06). In a certificate this shows up as a pair of events
that must happen in one order although neither causes the other (the C-element must fall before the other
node moves): a **relative-timing (RT) edge**. `TimedOccX` can only order events through physical causes, so it
cannot use such an edge. Which timing conditions justify RT edges?

**The extension.** The certificate has two cause relations with the same events: the physical causes `CP`
(what a node reads; they decide when it may move: `LCheckX` against `Enabled CP`) and the full order `CF`
(physical plus RT edges; ideals and the bounds `L` are taken in `CF`). Each RT edge `p → (u, k)` needs a
certified separation `Sep p (u, k) ≥ hi'(u, p)`. Separations may now also be justified through a common
ancestor `e0`: `Sep b (a, k) ≥ Sep e0 (a, k) - Up e0 b` (`SepOKR`, fourth form), where `Up e0 e` bounds how LATE
`e` can happen after `e0`: every physical cause of `e` (and `e`'s previous event) is read within its `hi`, and
then `e` happens at once (`UpOK`; only gate events, the environment has no upper bound).

**Proved:** `timedR_follows`: every bounded-delay behaviour follows the full certificate (ideals of `CF`, every
exact change certified, every claim holds), with the soundness of `Sep` and `Up` proved inside the induction
on time (`up_sound`, `sepSound_step`).

**Not shown here:** liveness for this version, any instance.
-/

namespace Formal.Net.OccNet.TimedR
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

/-- Soundness of separations up to time `t`: if `(a, k)` happened by `σ ≤ t`, then `(b, m)` happened by `σ - d`. -/
def SepSound (x : α → Nat → Bool) (t0 : Nat) (Sep : α → Nat → α → Nat → Option Nat) (t : Nat) : Prop :=
  ∀ (a b : α) (k m d : Nat), Sep b m a k = some d → ∀ σ : Int, σ ≤ t → hbI x t0 (a, k) σ → hbI x t0 (b, m) (σ - d)

theorem ss_nat {x : α → Nat → Bool} {t0 : Nat} {Sep : α → Nat → α → Nat → Option Nat} {t : Nat}
    (hSS : SepSound x t0 Sep t) {a b : α} {k m d τ : Nat} (hd : Sep b m a k = some d) (hτ : τ ≤ t)
    (hk : k < cnt x t0 a τ) : m < cnt x t0 b (τ - d) := by
  have h := hSS a b k m d hd τ (by omega) ⟨by omega, by simpa using hk⟩
  obtain ⟨h0, h1⟩ := h
  have e : ((τ : Int) - d).toNat = τ - d := by omega
  rw [e] at h1; exact h1

theorem ss_mono {x : α → Nat → Bool} {t0 : Nat} {Sep : α → Nat → α → Nat → Option Nat} {t t' : Nat}
    (h : SepSound x t0 Sep t) (ht : t' ≤ t) : SepSound x t0 Sep t' :=
  fun a b k m d hd σ hσ hh => h a b k m d hd σ (by omega) hh

section lem
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Cert α} {L : α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}

/-- The read tuple respects the bounds on `D v` (exact nodes only). -/
theorem read_consistentR (hb : TBehX N dat envEn x r t0 H) (hLs : LSound CF L)
    (hTO : TO N CF L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false) (t : Nat) (ht : t0 ≤ t)
    (hI : ∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ)) (hSS : SepSound x t0 Sep t) (v : α) :
    ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < nT N x t0 r v (t + 1) a → L a k b ≤ nT N x t0 r v (t + 1) b := by
  intro a ha b hbD k hk
  have hae := hDE v a ha
  have hbe := hDE v b hbD
  obtain ⟨ra1, ra2, ra3, _⟩ := rho_boundsX hb v a (t + 1) (by omega)
  obtain ⟨rb1, rb2, rb3, _⟩ := rho_boundsX hb v b (t + 1) (by omega)
  let τa := ρ N r v a (t + 1)
  have hIa := hI τa (by omega)
  have hk' : k < cntE dat x t0 a τa := by simp only [cntE, hae]; exact hk
  have hL1 : L a k b ≤ cntE dat x t0 b τa := hLs _ hIa a k b hk'
  simp only [cntE, hbe] at hL1
  unfold nT
  by_cases hle : τa ≤ ρ N r v b (t + 1)
  · exact Nat.le_trans hL1 (cnt_mono b _ _ hle)
  · by_cases hL0 : L a k b = 0
    · rw [hL0]; exact Nat.zero_le _
    · have hkl : k < CF.len a := by
        have := (hIa a).1; simp only [cntE, hae] at this; exact Nat.lt_of_lt_of_le hk this
      obtain ⟨d, hd, hdle⟩ := hTO v a b k ha hbD hkl (by omega) (by omega)
      have := ss_nat (τ := τa) hSS hd (by omega) hk
      have h2 := cnt_mono (x := x) (t0 := t0) b (τa - d) (ρ N r v b (t + 1)) (by omega)
      omega


/-- **A guarded data read is the claimed value.** -/
theorem guard_readR (hb : TBehX N dat envEn x r t0 H) (t : Nat) (ht : t0 ≤ t) (hSS : SepSound x t0 Sep t)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s)
    (v z : α) (hg : N.gate v = true) (hz : z ∈ N.pins v)
    (hGd : ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧ GuardTime N Sep v z c g)
    (val : Bool) (hdv : dv cl (gd v z) (nT N x t0 r v (t + 1)) = some val) :
    x z (r v z (t + 1)) = val := by
  unfold dv at hdv
  split at hdv
  · cases hdv
  · rename_i g hf
    obtain ⟨hgm, hon⟩ := find_some hf
    obtain ⟨c, hc, hcz, hgt⟩ := hGd g hgm
    rw [hc] at hdv; simp only [Option.map_some, Option.some.injEq] at hdv
    have hcm : c ∈ cl := List.mem_of_getElem? hc
    subst hcz hdv
    have hrz : reads N v c.z = true := by simp [reads, hg, hz]
    have hρz : ρ N r v c.z (t + 1) = r v c.z (t + 1) := by simp [ρ, hrz]
    obtain ⟨z1, z2, z3, z4⟩ := rho_boundsX hb v c.z (t + 1) (by omega)
    rw [hρz] at z1 z2 z3 z4
    have hHolds := hC c hcm (r v c.z (t + 1)) (by omega)
    apply hHolds z4
    · -- start
      obtain ⟨hgA, _⟩ := hgt
      cases hA : c.A with
      | none => trivial
      | some e =>
        rw [hA] at hgA
        obtain ⟨w, hw, d, hd, hle⟩ := hgA
        simp only [guardOn, hw, Bool.and_eq_true, decide_eq_true_eq] at hon
        have hw1 := hon.1
        obtain ⟨w1, w2, w3, _⟩ := rho_boundsX hb v w.1 (t + 1) (by omega)
        have hw1' : w.2 < cnt x t0 w.1 (ρ N r v w.1 (t + 1)) := by simpa [nT] using hw1
        have := cnt_pos hw1'
        have hhb : hbI x t0 (w.1, w.2) (ρ N r v w.1 (t + 1) : Int) := ⟨by omega, by simpa using hw1'⟩
        have := hSS w.1 e.1 w.2 e.2 d hd _ (by omega) hhb
        refine hbI_mono this ?_
        have : (hi' N v c.z : Int) = N.hi v c.z := by simp [hi', hrz]
        omega
    · -- end
      obtain ⟨_, hgB⟩ := hgt
      cases hB' : c.B with
      | none => trivial
      | some e =>
        rw [hB'] at hgB
        obtain ⟨w, hw, d, hd, hle⟩ := hgB
        simp only [guardOn, hw, Bool.and_eq_true, decide_eq_true_eq] at hon
        have hw2 := hon.2
        intro hE
        obtain ⟨w1, w2, w3, _⟩ := rho_boundsX hb v w.1 (t + 1) (by omega)
        have hlz : (lo' N v c.z : Int) = N.lo v c.z := by simp [lo', hrz]
        have := hSS e.1 w.1 e.2 w.2 d hd _ (by omega) hE
        have h2 := hbI_mono this (s' := (ρ N r v w.1 (t + 1) : Int)) (by omega)
        have h3 := h2.2
        simp only [Int.toNat_natCast] at h3
        simp only [nT] at hw2
        omega


/-- **Window transfer**: if a claim's window contains `s` and a covering window's separations hold for a pin read
at `ρ ∈ [s - hi, s - lo]`, then the covering window contains `ρ`. -/
theorem win_transferR (s : Nat) (hSS : SepSound x t0 Sep s)
    (c w : Claim α) (hi lo ρ' : Nat) (ha : 0 ≤ c.a) (hρ1 : s ≤ ρ' + hi) (hρ2 : ρ' + lo ≤ s)
    (hct : CovTime Sep c w hi lo)
    (hA : match c.A with | none => True | some e => hbI x t0 e ((s : Int) - c.a))
    (hBn : match c.B with | none => True | some e => ¬ hbI x t0 e ((s : Int) - c.b)) :
    (match w.A with | none => True | some e => hbI x t0 e ((ρ' : Int) - w.a)) ∧
    (match w.B with | none => True | some e => ¬ hbI x t0 e ((ρ' : Int) - w.b)) := by
  obtain ⟨hcA, hcB⟩ := hct
  refine ⟨?_, ?_⟩
  · cases hwA : w.A with
    | none => trivial
    | some e' =>
      rw [hwA] at hcA
      obtain ⟨e, he, d, hd, hle⟩ := hcA
      rw [he] at hA
      have := hSS e.1 e'.1 e.2 e'.2 d hd _ (by omega) hA
      exact hbI_mono this (by omega)
  · cases hwB : w.B with
    | none => trivial
    | some e' =>
      rw [hwB] at hcB
      obtain ⟨e, he, d, hd, hle⟩ := hcB
      rw [he] at hBn
      intro hE
      have hpos := hE.1
      have := hSS e'.1 e.1 e'.2 e.2 d hd _ (by omega) hE
      exact hBn (hbI_mono this (by omega))


/-- **One step for a data-gate claim.** -/
theorem claim_stepR (hb : TBehX N dat envEn x r t0 H) (t : Nat) (ht : t0 ≤ t) (hSS : SepSound x t0 Sep (t + 1))
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s)
    (c : Claim α) (hgz : N.gate c.z = true) (ha : 0 ≤ c.a) (cov : α → Cov)
    (hval : ValOK N (fun w => x w t0) cl c cov)
    (hcov : ∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
      CovTime Sep c w (N.hi c.z u) (N.lo c.z u))
    (hkind : ∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧
      (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)) :
    Holds x t0 H c (t + 1) := by
  intro _ hA hBn
  rw [hb.geq c.z (t + 1) hgz (by omega)]
  apply hval
  intro u hu w hw
  obtain ⟨r1, r2, r3, r4⟩ := hb.rd c.z u (t + 1) hgz hu (by omega)
  have hlo := hb.lo1 c.z u hgz hu
  obtain ⟨wA, wB⟩ := win_transferR (t + 1) hSS c w (N.hi c.z u) (N.lo c.z u) (r c.z u (t + 1))
    ha (by omega) (by omega) (hcov u hu w hw) hA hBn
  obtain ⟨hk1, hk2⟩ := hkind u hu
  cases hc : cov u with
  | X => rw [hc] at hw; simp [covWin] at hw
  | cl i =>
    rw [hc] at hw
    simp only [covWin] at hw
    have hwz := hk2 i w hc hw
    have hwm : w ∈ cl := List.mem_of_getElem? hw
    have := hC w hwm (r c.z u (t + 1)) (by omega) (by omega) wA wB
    rw [hwz] at this; exact this
  | ex k =>
    rw [hc] at hw
    simp only [covWin, Option.some.injEq] at hw
    subst hw
    have hdu := hk1 k hc
    simp only at wA wB
    have hcnt : cnt x t0 u (r c.z u (t + 1)) = k := by
      have hle : cnt x t0 u (r c.z u (t + 1)) ≤ k := by
        rcases Nat.lt_or_ge k (cnt x t0 u (r c.z u (t + 1))) with h | h
        · exact absurd ⟨by omega, by simpa using h⟩ wB
        · exact h
      by_cases hk0 : k = 0
      · omega
      · simp only [hk0, if_false] at wA
        have := wA.2; simp at this; omega
    rw [x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hdu h1 h2) _ r4]
    simp only [st, hcnt]

theorem change_okR (hb : TBehX N dat envEn x r t0 H) (hLs : LSound CF L)
    (hTO : TO N CF L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) CP L D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (t : Nat) (ht : t0 ≤ t) (hI : ∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N CP x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s) (hSS : SepSound x t0 Sep t)
    (v : α) (hve : dat v = false) (hch : x v (t + 1) ≠ x v t) : ChangeOK N CP x t0 r v (t + 1) := by
  have hcons := read_consistentR hb hLs hTO hDE t ht hI hSS v
  have hlen : ∀ u ∈ D v, nT N x t0 r v (t + 1) u ≤ CP.len u := by
    intro u hu
    obtain ⟨_, _, h3, _⟩ := rho_boundsX hb v u (t + 1) (by omega)
    have := (hI (ρ N r v u (t + 1)) (by omega) u).1
    simp only [cntE, hDE v u hu, Bool.false_eq_true, if_false] at this
    rw [hlenEq]; exact this
  have hq : ∀ u, dat u = false → ∀ s, t0 ≤ s + H → x u s = st (fun w => x w t0) (fun w => cnt x t0 w s) u :=
    fun u hu => x_eq_st (x := x) (t0 := t0) u H (fun s' h1 h2 => hb.quiet u s' hu h1 h2)
  have hsub : t + 1 - 1 = t := by omega
  show (reads N v v = true → cnt x t0 v (r v v (t + 1)) = cnt x t0 v (t + 1 - 1)) ∧
    Enabled CP (nT N x t0 r v (t + 1)) v
  rw [hsub]
  cases hg : N.gate v with
  | false =>
    -- a free node
    have he := hb.env v (t + 1) hg hve (by omega) (by simpa [hsub] using hch)
    have hrd : reads N v v = false := by simp [reads, hg]
    refine ⟨fun h => absurd h (by simp [hrd]), ?_⟩
    have hL := hloc v hve (nT N x t0 r v (t + 1)) hlen hcons (fun w => x w t)
      (fun z _ _ val hdv => by rw [hgdF v z hg] at hdv; simp [dv] at hdv)
    apply hL.1
    unfold tEn; rw [hg]; simp only [Bool.false_eq_true, if_false]
    rw [hsub] at he
    have : (fun w => x w t) = mix dat (st (fun w => x w t0) (nT N x t0 r v (t + 1))) (fun w => x w t) := by
      funext w
      unfold mix
      cases hdw : dat w with
      | true => rfl
      | false =>
        have hrw : reads N v w = false := by simp [reads, hg]
        simp only [Bool.false_eq_true, if_false]
        rw [hq w hdw t (by omega)]; simp [st, nT, ρ, hrw]
    rw [← this]; exact he
  | true =>
    have hbb : ∀ z, dat z = true → z ∈ N.pins v → ∀ val,
        dv cl (gd v z) (nT N x t0 r v (t + 1)) = some val → x z (r v z (t + 1)) = val :=
      fun z _ hz val hdv => guard_readR hb t ht hSS hC v z hg hz (hGd v z hg hz) val hdv
    have hL := hloc v hve (nT N x t0 r v (t + 1)) hlen hcons (fun w => x w (r v w (t + 1))) hbb
    have hgeq := hb.geq v (t + 1) hg (by omega)
    rw [pins_readX hb v hg (t + 1) (by omega)] at hgeq
    have hmixv : ∀ n : α → Nat, ∀ bb : α → Bool, mix dat (st (fun w => x w t0) n) bb v = st (fun w => x w t0) n v := by
      intro n bb; simp [mix, hve]
    by_cases hfb : reads N v v = true
    · -- a gate with a feedback pin
      let nv := nT N x t0 r v (t + 1) v
      have hnv : nv = cnt x t0 v (r v v (t + 1)) := by simp [nv, nT, ρ, hfb]
      obtain ⟨rv1, _, rv3, rv4⟩ := rho_boundsX hb v v (t + 1) (by omega)
      have hrle : r v v (t + 1) ≤ t := by
        have : ρ N r v v (t + 1) = r v v (t + 1) := by simp [ρ, hfb]
        omega
      have hnvle : nv ≤ cnt x t0 v t := by rw [hnv]; exact cnt_mono v _ _ hrle
      rcases Nat.lt_or_ge nv (cnt x t0 v t) with hlt | hge
      · -- stale feedback: no change can happen (contradiction)
        exfalso
        obtain ⟨s1, h1a, h1b, h1c, h1d, h1e⟩ := event_time (x := x) (t0 := t0) v nv t hlt
        obtain ⟨fb1, en1⟩ := hB v s1 hve h1a h1b h1e
        have hr_s1 : r v v (t + 1) < s1 := by
          rcases Nat.lt_or_ge (r v v (t + 1)) s1 with h | h
          · exact h
          · have := cnt_mono (x := x) (t0 := t0) v s1 (r v v (t + 1)) h
            rw [← hnv] at this; omega
        have hn1v : nT N x t0 r v s1 v = nv := by
          simp only [nT, ρ, hfb, if_true]; rw [fb1 hfb, h1c]
        have hEn : Enabled CP (nT N x t0 r v (t + 1)) v := by
          refine enabled_mono en1 (by rw [hn1v]) (fun w => ?_)
          exact cnt_mono w _ _ (rho_monoX hb v w s1 (t + 1) h1a (by omega))
        have hen := hL.2 hEn
        unfold tEn at hen; rw [hg] at hen; simp only [if_true] at hen
        rw [hmixv, ← hgeq] at hen
        -- the state of `v` in the tuple is its value before event `nv`
        have hstv : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v (s1 - 1) := by
          rw [hq v hve (s1 - 1) (by omega)]; simp only [st, nT, ρ, hfb, if_true]; rw [← hnv, h1c]
        rw [hstv] at hen
        -- at most one event of `v` after the stale read
        have hcnt : cnt x t0 v t = nv + 1 := by
          rcases Nat.lt_or_ge (nv + 1) (cnt x t0 v t) with h2 | h2
          · exfalso
            obtain ⟨s2, h2a, h2b, h2c, _, h2e⟩ := event_time (x := x) (t0 := t0) v (nv + 1) t h2
            obtain ⟨fb2, _⟩ := hB v s2 hve h2a h2b h2e
            have := fb2 hfb
            have hs12 : s1 < s2 := by
              rcases Nat.lt_or_ge s1 s2 with h | h
              · exact h
              · have := cnt_mono (x := x) (t0 := t0) v s2 s1 h; omega
            have hm := hb.mono v v s2 (t + 1) hg (by simp [reads] at hfb; exact hfb.2) h2a (by omega)
            have := cnt_mono (x := x) (t0 := t0) v _ _ hm
            rw [← hnv] at this; omega
          · have := cnt_mono (x := x) (t0 := t0) v s1 t h1b
            omega
        have hxt : x v t = x v s1 := by
          rw [hq v hve t (by omega), hq v hve s1 (by omega)]; simp only [st]; rw [hcnt, h1d]
        apply hch
        rw [hxt]; exact bool3 hen h1e
      · -- current feedback
        have hnveq : nv = cnt x t0 v t := Nat.le_antisymm hnvle hge
        refine ⟨fun _ => by rw [← hnv, hnveq], ?_⟩
        apply hL.1
        unfold tEn; rw [hg]; simp only [if_true]
        rw [hmixv, ← hgeq]
        have : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v t := by
          rw [hq v hve t (by omega)]; simp only [st]; rw [show nT N x t0 r v (t + 1) v = nv from rfl, hnveq]
        rw [this]; simpa using hch
    · -- a gate without a feedback pin
      have hfb' : reads N v v = false := by simpa using hfb
      refine ⟨fun h => absurd h hfb, ?_⟩
      apply hL.1
      unfold tEn; rw [hg]; simp only [if_true]
      rw [hmixv, ← hgeq, st_nT_selfX hb v hve hfb' t ht]
      simpa using hch


end lem

/-! ## Upper bounds and the extended separations -/

/-- `Up e0 e = some d`: if `e0` happened by `τ`, then `e` happened by `τ + d`. Justified by `e`'s physical causes
and previous event (each read within its pin's `hi`); only exact gate events. -/
def UpOK (N : TNet α) (dat : α → Bool) (CP : Cert α) (Up : α × Nat → α × Nat → Option Nat) : Prop :=
  ∀ e0 e d, Up e0 e = some d →
    e = e0 ∨
    (N.gate e.1 = true ∧ dat e.1 = false ∧ e.2 < CP.len e.1 ∧
      (∀ p ∈ CP.causes e.1 e.2, ∃ dp, Up e0 p = some dp ∧ dp + hi' N e.1 p.1 ≤ d) ∧
      (0 < e.2 → ∃ dp, Up e0 (e.1, e.2 - 1) = some dp ∧ dp + hi' N e.1 e.1 ≤ d))

/-- Separations: one step back along a physical cause or the previous event, or through a common ancestor `e0`
with an upper bound on how late `(b, m)` follows it. -/
def SepOKR (N : TNet α) (CP : Cert α) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) : Prop :=
  ∀ b m a k d, k < CP.len a → Sep b m a k = some d →
    (b = a ∧ m = k ∧ d = 0) ∨
    (∃ p ∈ CP.causes a k, ∃ d', Sep b m p.1 p.2 = some d' ∧ d ≤ d' + lo' N a p.1) ∨
    (0 < k ∧ ∃ d', Sep b m a (k - 1) = some d' ∧ d ≤ d' + lo' N a a) ∨
    (1 ≤ d ∧ ∃ e0 : α × Nat, ∃ dl du, Sep e0.1 e0.2 a k = some dl ∧ Up e0 (b, m) = some du ∧ d + du ≤ dl ∧
      CP.tm e0.1 e0.2 < CP.tm b m)

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Cert α} {L : α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

theorem tm_prev {C : Cert α} (hT : TmOK C) (w : α) (j : Nat) (hj : 0 < j) (hl : j < C.len w) :
    C.tm w (j - 1) < C.tm w j := by
  have := hT.1 w (j - 1) (by omega)
  rwa [show j - 1 + 1 = j by omega] at this

theorem hi'_pos (hb : TBehX N dat envEn x r t0 H) (v w : α) : 1 ≤ hi' N v w := by
  unfold hi'
  by_cases h : reads N v w = true
  · simp only [h, if_true]
    simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := hb.lo1 v w h.1 h.2
    obtain ⟨a1, a2, _, _⟩ := hb.rd v w (t0 + 1) h.1 h.2 (by omega)
    omega
  · simp only [h, if_false, Bool.false_eq_true]; exact Nat.le_refl _

/-- **Upper bounds are sound** up to a horizon where the invariants hold. -/
theorem up_sound (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : LSound CF L)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N CF L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) CP L D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOK N dat CP Up) (hS : SepOKR N CP Sep Up)
    (T : Nat) (hI : ∀ τ, τ ≤ T → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ T → x v s ≠ x v (s - 1) → ChangeOK N CP x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ T → Holds x t0 H c s) (hSS : SepSound x t0 Sep T)
    (e0 : α × Nat) (τ : Nat) (h0 : e0.2 < cnt x t0 e0.1 τ) :
    ∀ M (e : α × Nat) du, CP.tm e.1 e.2 ≤ M → Up e0 e = some du → τ + du ≤ T → e.2 < cnt x t0 e.1 (τ + du) := by
  intro M
  refine Nat.strongRecOn M ?_
  intro M ih e du hM hU hT
  have hτ0 := cnt_pos h0
  rcases hUp e0 e du hU with he | ⟨hg, hde, hlen, hca, hpr⟩
  · subst he; exact Nat.lt_of_lt_of_le h0 (cnt_mono _ _ _ (by omega))
  · obtain ⟨w, j⟩ := e
    simp only at hg hde hlen hca hpr hM ⊢
    -- by contradiction: `(w, j)` has not happened by `T' = τ + du`
    rcases Nat.lt_or_ge j (cnt x t0 w (τ + du)) with hdone | hnot
    · exact hdone
    exfalso
    obtain ⟨T', hTd⟩ : ∃ T', T' = τ + du := ⟨_, rfl⟩
    have hnot' : cnt x t0 w T' ≤ j := by rw [hTd]; exact hnot
    -- the previous event happened by `T' - 1`
    have hprev : j ≤ cnt x t0 w (T' - 1) := by
      by_cases hj : j = 0
      · omega
      · obtain ⟨dp, hdp, hle⟩ := hpr (by omega)
        have h1 := tm_prev hTP w j (by omega) hlen
        have hip := ih (CP.tm w (j - 1)) (by omega) (w, j - 1) dp (Nat.le_refl _) hdp (by omega)
        have := hi'_pos hb w w
        have := cnt_mono (x := x) (t0 := t0) w (τ + dp) (T' - 1) (by omega)
        simp only at hip; omega
    have hcT : cnt x t0 w T' = j := by
      have := cnt_mono (x := x) (t0 := t0) w (T' - 1) T' (by omega); omega
    have hcT1 : cnt x t0 w (T' - 1) = j := by
      have := cnt_mono (x := x) (t0 := t0) w (T' - 1) T' (by omega); omega
    have hTe : T' - 1 + 1 = T' := by omega
    -- the read tuple at `T'` enables `(w, j)`
    have hnw : nT N x t0 r w T' w = j := by
      unfold nT ρ
      by_cases hr : reads N w w = true
      · simp only [hr, if_true]
        obtain ⟨_, r2, r3, _⟩ := rho_boundsX hb w w T' (by omega)
        have hrr : ρ N r w w T' = r w w T' := by simp [ρ, hr]
        rw [hrr] at r2 r3
        have hle := cnt_mono (x := x) (t0 := t0) w (r w w T') (T' - 1) (by omega)
        by_cases hj : j = 0
        · omega
        · obtain ⟨dp, hdp, hle2⟩ := hpr (by omega)
          have hip := ih (CP.tm w (j - 1)) (by have := tm_prev hTP w j (by omega) hlen; omega) (w, j - 1) dp
            (Nat.le_refl _) hdp (by omega)
          simp only at hip
          have := cnt_mono (x := x) (t0 := t0) w (τ + dp) (r w w T') (by omega)
          omega
      · simp only [hr, if_false, Bool.false_eq_true]; exact hcT1
    have hEn : Enabled CP (nT N x t0 r w T') w := by
      refine ⟨by rw [hnw]; exact hlen, fun p hp => ?_⟩
      rw [hnw] at hp
      obtain ⟨dp, hdp, hle⟩ := hca p hp
      have htm := (hTP.2 w j hlen p hp).2
      have hip := ih (CP.tm p.1 p.2) (by omega) p dp (Nat.le_refl _) hdp (by omega)
      obtain ⟨_, r2, _, _⟩ := rho_boundsX hb w p.1 T' (by omega)
      simp only [nT]
      exact Nat.lt_of_lt_of_le hip (cnt_mono _ _ _ (by omega))
    -- the local check makes the gate move at `T'`
    have hT1 : t0 ≤ T' - 1 := by omega
    have hcons := read_consistentR hb hLs hTO hDE (T' - 1) hT1 (fun τ' h => hI τ' (by omega))
      (ss_mono hSS (by omega)) w
    rw [hTe] at hcons
    have hlen' : ∀ u ∈ D w, nT N x t0 r w T' u ≤ CP.len u := by
      intro u hu
      obtain ⟨_, _, h3, _⟩ := rho_boundsX hb w u T' (by omega)
      have := (hI (ρ N r w u T') (by omega) u).1
      simp only [cntE, hDE w u hu, Bool.false_eq_true, if_false] at this
      rw [hlenEq]; exact this
    have hbb : ∀ z, dat z = true → z ∈ N.pins w → ∀ val,
        dv cl (gd w z) (nT N x t0 r w T') = some val → x z (r w z T') = val := by
      intro z _ hz val hdv
      have := guard_readR hb (T' - 1) hT1 (ss_mono hSS (by omega)) (fun c hc s hs => hC c hc s (by omega))
        w z hg hz (hGd w z hg hz) val (by rw [hTe]; exact hdv)
      rw [hTe] at this; exact this
    have hL := hloc w hde (nT N x t0 r w T') hlen' hcons (fun u => x u (r w u T')) hbb
    have he := hL.2 hEn
    unfold tEn at he; rw [hg] at he; simp only [if_true] at he
    have hgeq := hb.geq w T' hg (by omega)
    rw [pins_readX hb w hg T' (by omega)] at hgeq
    have hmixv : mix dat (st (fun u => x u t0) (nT N x t0 r w T')) (fun u => x u (r w u T')) w =
        st (fun u => x u t0) (nT N x t0 r w T') w := by simp [mix, hde]
    rw [hmixv, ← hgeq] at he
    have hst : st (fun u => x u t0) (nT N x t0 r w T') w = x w (T' - 1) := by
      rw [x_eq_st w H (fun s' h1 h2 => hb.quiet w s' hde h1 h2) (T' - 1) (by omega)]
      simp only [st]; rw [hnw, hcT1]
    rw [hst] at he
    have hc := cnt_succ (x := x) (t0 := t0) w (T' - 1) hT1
    rw [hTe] at hc
    have hx : (x w T' != x w (T' - 1)) = true := he
    rw [hx] at hc
    simp only [if_true] at hc
    rw [hcT, hcT1] at hc
    omega

/-- **Separations stay sound one more step.** -/
theorem sepSound_step (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : LSound CF L)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N CF L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) CP L D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOK N dat CP Up) (hS : SepOKR N CP Sep Up)
    (t : Nat) (ht : t0 ≤ t) (hI : ∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOK N CP x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s) (hSS : SepSound x t0 Sep t) :
    SepSound x t0 Sep (t + 1) := by
  intro a b k m d hd σ hσ hh
  by_cases hσt : σ ≤ t
  · exact hSS a b k m d hd σ hσt hh
  obtain ⟨hh0, hh1⟩ := hh
  simp only at hh1
  have hσe : σ.toNat = t + 1 := by omega
  rw [hσe] at hh1
  have hσ' : σ = ((t + 1 : Nat) : Int) := by omega
  subst hσ'
  by_cases hkt : k < cnt x t0 a t
  · have := hSS a b k m d hd t (by omega) ⟨by omega, by simpa using hkt⟩
    exact hbI_mono this (by omega)
  -- `(a, k)` happens exactly at `t + 1`
  have hstep := cnt_step_le (x := x) (t0 := t0) a t
  have hck : cnt x t0 a t = k := by omega
  have hch : x a (t + 1) ≠ x a t := by
    intro he
    have := cnt_succ (x := x) (t0 := t0) a t ht
    rw [he] at this; simp at this; omega
  have hae := hSE b m a k d hd
  obtain ⟨hfb, hen⟩ := hB a (t + 1) hae (by omega) (Nat.le_refl _) (by simpa using hch)
  have hna : nT N x t0 r a (t + 1) a = k := by
    unfold nT ρ
    by_cases h : reads N a a = true
    · simp only [h, if_true]; rw [hfb h]; simpa using hck
    · simp only [h, if_false, Bool.false_eq_true]; simpa using hck
  have hkl : k < CP.len a := hna ▸ hen.1
  suffices Q : ∀ M b m d, CP.tm b m ≤ M → Sep b m a k = some d → hbI x t0 (b, m) (((t + 1 : Nat) : Int) - d) from
    Q _ b m d (Nat.le_refl _) hd
  intro M
  refine Nat.strongRecOn M ?_
  intro M ih b m d hM hd
  rcases hS b m a k d hkl hd with ⟨hb', hm, hd0⟩ | ⟨p, hp, d', hd', hle⟩ | ⟨hk0, d', hd', hle⟩ |
      ⟨hd1, e0, dl, du, hdl, hdu, hle, htm⟩
  · subst hb' hm hd0; exact ⟨by omega, by simpa using hh1⟩
  · have hpc : p.2 < nT N x t0 r a (t + 1) p.1 := hen.2 p (hna ▸ hp)
    obtain ⟨r1, _, r3, _⟩ := rho_boundsX hb a p.1 (t + 1) (by omega)
    have hpc' : p.2 < cnt x t0 p.1 (ρ N r a p.1 (t + 1)) := by simpa [nT] using hpc
    have hpos := cnt_pos hpc'
    have := hSS p.1 b p.2 m d' hd' (ρ N r a p.1 (t + 1)) (by omega) ⟨by omega, by simpa using hpc'⟩
    exact hbI_mono this (by omega)
  · have hprev : k - 1 < cnt x t0 a (ρ N r a a (t + 1)) := by
      have : cnt x t0 a (ρ N r a a (t + 1)) = k := hna
      omega
    obtain ⟨r1, _, r3, _⟩ := rho_boundsX hb a a (t + 1) (by omega)
    have hpos := cnt_pos hprev
    have := hSS a b (k - 1) m d' hd' (ρ N r a a (t + 1)) (by omega) ⟨by omega, by simpa using hprev⟩
    exact hbI_mono this (by omega)
  · have h0 := ih (CP.tm e0.1 e0.2) (by omega) e0.1 e0.2 dl (Nat.le_refl _) hdl
    obtain ⟨h00, h01⟩ := h0
    let τ := (((t + 1 : Nat) : Int) - dl).toNat
    have hτ : (τ : Int) = ((t + 1 : Nat) : Int) - dl := by simp only [τ]; omega
    have hup := up_sound hb hTP hLs hSE hTO hDE hloc hlenEq hgdF hGd hUp hS t hI (fun v s h1 h2 h3 h4 => hB v s h1 h2 (by omega) h4) hC hSS
      e0 τ h01 _ (b, m) du (Nat.le_refl _) hdu (by omega)
    refine ⟨by omega, ?_⟩
    simp only at hup
    exact Nat.lt_of_lt_of_le hup (cnt_mono _ _ _ (by omega))

/-- **Every bounded-delay behaviour follows the full certificate, RT edges included.** -/
theorem timedR_follows (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : LSound CF L)
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
    (hGC : ∀ c ∈ cl, N.gate c.z = true → 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N (fun w => x w t0) cl c cov ∧
      (∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
        CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
      (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)))
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
            obtain ⟨ha, cov, hval, hcov, hkind⟩ := hGC c hc hgz
            exact claim_stepR hb t ht hSS' hC c hgz ha cov hval hcov hkind
    · refine ⟨fun τ hτ => ?_, fun v s hve h1 h2 h3 => ?_, fun c hc s hs => hInit c hc s (by omega), hss0 _ (by omega)⟩
      · rw [hz τ (by omega)]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · omega

end main

end Formal.Net.OccNet.TimedR
