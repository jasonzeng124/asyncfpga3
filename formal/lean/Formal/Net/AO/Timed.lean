import Formal.Net.AO.Occ
import Formal.Net.TimedOccU

/-!
# The timed theorem with AND-OR causes, reader-specific bounds and relaxed skew rows (shard C, S4)

**Problem, plainly.** A first certificate for THE target (pair (12,18), Python, JOURNAL-C 2026-11-08) failed against
`TimedOccRT`/`TimedOccU` for four reasons: (1) ~1,400 control gates fire on the first of two concurrent inputs
(OR-causality), which AND-only causes cannot express; (2) the skew rows `TO` were demanded for a = b, where they are
impossible and never used; (3) rows where the first source is the reader itself are implied by the reader's own
earlier reads, but were demanded as separations; (4) one bound function `L` for all readers. This file is the
timed theorem with all four repaired, on `AO.Cert` (alternative cause sets):
* `Enabled`/`Ideal` take ANY alternative; separations (`SepOKA` form ii) go back through a cause found in EVERY
  alternative; upper bounds (`UpOKA`) through ANY one alternative;
* `TOA`: rows only for a ≠ b, and a row with a = v may instead name, for an earlier event of v, a cause on b in
  every alternative (`read_consistentA` then uses the reader's own enabling read, by monotone reads);
* bounds `L v` per reader v, each sound for the full order;
* RT edges, data claims, chains of claims as in `TimedOccU`.

**Proved:** `timedA_follows` (every bounded-delay behaviour follows the certificate: ideals of the full order,
every exact change a certified event, every claim holds, separations sound).

**Not shown here:** liveness for this version (next), any instance.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]

def ChangeOKA (N : TNet α) (CP : Cert α) (x : α → Nat → Bool) (t0 : Nat) (r : α → α → Nat → Nat)
    (v : α) (s : Nat) : Prop :=
  (reads N v v = true → cnt x t0 v (r v v s) = cnt x t0 v (s - 1)) ∧ Enabled CP (nT N x t0 r v s) v

/-- The local check with data inputs, AND-OR version. -/
def LCheckXA (N : TNet α) (dat : α → Bool) (envEn : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α)
    (L : α → Nat → α → Nat) (D : α → List α) (cl : List (Claim α)) (gd : α → α → List (Guard α)) (v : α) : Prop :=
  ∀ n : α → Nat, (∀ u ∈ D v, n u ≤ C.len u) → (∀ u ∈ D v, ∀ w ∈ D v, ∀ k, k < n u → L u k w ≤ n w) →
    ∀ bb : α → Bool, (∀ z, dat z = true → z ∈ N.pins v → ∀ val, dv cl (gd v z) n = some val → bb z = val) →
      (tEn N envEn v (mix dat (st s0 n) bb) = true ↔ Enabled C n v)

/-- **The skew rows**, relaxed: only for distinct sources; a row whose first source is the reader may instead name,
for an earlier event of the reader, a cause on the second source in every alternative. -/
def TOA (N : TNet α) (CF CP : Cert α) (L : α → α → Nat → α → Nat) (D : α → List α)
    (Sep : α → Nat → α → Nat → Option Nat) : Prop :=
  ∀ v a b k, a ∈ D v → b ∈ D v → a ≠ b → k < CF.len a → 0 < L v a k b → lo' N v a < hi' N v b →
    (∃ d, Sep b (L v a k b - 1) a k = some d ∧ hi' N v b ≤ lo' N v a + d) ∨
    (a = v ∧ ∃ k', k' ≤ k ∧ ∀ alt ∈ CP.causes v k', ∃ p ∈ alt, p.1 = b ∧ L v v k b ≤ p.2 + 1)

theorem ideal_stepA {c c' : α → Nat} (C : Cert α) (hc : Ideal C c)
    (h : ∀ u, c' u = c u ∨ (c' u = c u + 1 ∧ Enabled C c u)) (hle : ∀ u, c u ≤ c' u) : Ideal C c' := by
  intro u
  rcases h u with h1 | ⟨h1, he⟩
  · rw [h1]
    refine ⟨(hc u).1, fun k hk => ?_⟩
    obtain ⟨alt, ha, hin⟩ := (hc u).2 k hk
    exact ⟨alt, ha, altIn_mono hle hin⟩
  · rw [h1]
    refine ⟨he.1, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (c u) with hk' | hk'
    · obtain ⟨alt, ha, hin⟩ := (hc u).2 k hk'
      exact ⟨alt, ha, altIn_mono hle hin⟩
    · have : k = c u := by omega
      subst this
      obtain ⟨_, alt, ha, hin⟩ := he
      exact ⟨alt, ha, altIn_mono hle hin⟩

theorem enabled_monoA {C : Cert α} {n n' : α → Nat} {v : α} (h : Enabled C n v) (hv : n v = n' v)
    (hle : ∀ w, n w ≤ n' w) : Enabled C n' v := by
  obtain ⟨h1, alt, ha, hin⟩ := h
  exact ⟨hv ▸ h1, alt, hv ▸ ha, altIn_mono hle hin⟩

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Cert α} {L : α → α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

/-- The read tuple respects the reader's bounds. -/
theorem read_consistentA (hb : TBehX N dat envEn x r t0 H) (hLs : ∀ v, LSound CF (L v))
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false) (t : Nat) (ht : t0 ≤ t)
    (hI : ∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s)
    (hSS : SepSound x t0 Sep t) (v : α) :
    ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < nT N x t0 r v (t + 1) a → L v a k b ≤ nT N x t0 r v (t + 1) b := by
  intro a ha b hbD k hk
  have hae := hDE v a ha
  have hbe := hDE v b hbD
  obtain ⟨ra1, ra2, ra3, _⟩ := rho_boundsX hb v a (t + 1) (by omega)
  obtain ⟨rb1, rb2, rb3, _⟩ := rho_boundsX hb v b (t + 1) (by omega)
  let τa := ρ N r v a (t + 1)
  have hIa := hI τa (by omega)
  have hk' : k < cntE dat x t0 a τa := by simp only [cntE, hae]; exact hk
  have hL1 : L v a k b ≤ cntE dat x t0 b τa := hLs v _ hIa a k b hk'
  simp only [cntE, hbe] at hL1
  unfold nT
  by_cases hle : τa ≤ ρ N r v b (t + 1)
  · exact Nat.le_trans hL1 (cnt_mono b _ _ hle)
  · have hab : a ≠ b := by intro e; subst e; exact hle (Nat.le_refl _)
    by_cases hL0 : L v a k b = 0
    · rw [hL0]; exact Nat.zero_le _
    · have hkl : k < CF.len a := by
        have := (hIa a).1; simp only [cntE, hae] at this; exact Nat.lt_of_lt_of_le hk this
      rcases hTO v a b k ha hbD hab hkl (by omega) (by omega) with ⟨d, hd, hdle⟩ | ⟨hav, k', hkk', hcs⟩
      · have := ss_nat (τ := τa) hSS hd (by omega) hk
        have h2 := cnt_mono (x := x) (t0 := t0) b (τa - d) (ρ N r v b (t + 1)) (by omega)
        omega
      · subst hav
        -- the reader's own event `(a, k')` happened by `τa`; it read a cause on `b`
        have hk'c : k' < cnt x t0 a τa := Nat.lt_of_le_of_lt hkk' hk
        obtain ⟨s', hs1, hs2, hs3, hs4, hs5⟩ := event_time (x := x) (t0 := t0) a k' τa hk'c
        obtain ⟨hfb, hen⟩ := hB a s' hae hs1 (by omega) hs5
        have hna : nT N x t0 r a s' a = k' := by
          unfold nT ρ
          by_cases h : reads N a a = true
          · simp only [h, if_true]; rw [hfb h, hs3]
          · simp only [h, if_false, Bool.false_eq_true]; exact hs3
        obtain ⟨_, alt, halt, hin⟩ := hen
        rw [hna] at halt
        obtain ⟨p, hp, hpb, hpl⟩ := hcs alt halt
        have h1 := hin p hp
        rw [hpb] at h1
        have h2 := cnt_mono (x := x) (t0 := t0) b (ρ N r a b s') (ρ N r a b (t + 1))
          (rho_monoX hb a b s' (t + 1) hs1 (by omega))
        simp only [nT] at h1
        omega

theorem change_okA (hb : TBehX N dat envEn x r t0 H) (hLs : ∀ v, LSound CF (L v))
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckXA N dat envEn (fun w => x w t0) CP (L v) D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (t : Nat) (ht : t0 ≤ t) (hI : ∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s) (hSS : SepSound x t0 Sep t)
    (v : α) (hve : dat v = false) (hch : x v (t + 1) ≠ x v t) : ChangeOKA N CP x t0 r v (t + 1) := by
  have hcons := read_consistentA hb hLs hTO hDE t ht hI hB hSS v
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
          refine enabled_monoA en1 (by rw [hn1v]) (fun w => ?_)
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


/-! ## Upper bounds and the extended separations -/

/-- `Up e0 e = some d`: if `e0` happened by `τ`, then `e` happened by `τ + d`. Justified by `e`'s physical causes
and previous event (each read within its pin's `hi`); only exact gate events. -/
def UpOKA (N : TNet α) (dat : α → Bool) (CP : Cert α) (Up : α × Nat → α × Nat → Option Nat) : Prop :=
  ∀ e0 e d, Up e0 e = some d →
    e = e0 ∨
    (N.gate e.1 = true ∧ dat e.1 = false ∧ e.2 < CP.len e.1 ∧
      (∃ alt ∈ CP.causes e.1 e.2, ∀ p ∈ alt, ∃ dp, Up e0 p = some dp ∧ dp + hi' N e.1 p.1 ≤ d) ∧
      (0 < e.2 → ∃ dp, Up e0 (e.1, e.2 - 1) = some dp ∧ dp + hi' N e.1 e.1 ≤ d))

/-- Separations: one step back along a physical cause or the previous event, or through a common ancestor `e0`
with an upper bound on how late `(b, m)` follows it. -/
def SepOKA (N : TNet α) (CP : Cert α) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) : Prop :=
  ∀ b m a k d, k < CP.len a → Sep b m a k = some d →
    (b = a ∧ m = k ∧ d = 0) ∨
    (∀ alt ∈ CP.causes a k, ∃ p ∈ alt, ∃ d', Sep b m p.1 p.2 = some d' ∧ d ≤ d' + lo' N a p.1) ∨
    (0 < k ∧ ∃ d', Sep b m a (k - 1) = some d' ∧ d ≤ d' + lo' N a a) ∨
    (1 ≤ d ∧ ∃ e0 : α × Nat, ∃ dl du, Sep e0.1 e0.2 a k = some dl ∧ Up e0 (b, m) = some du ∧ d + du ≤ dl ∧
      CP.tm e0.1 e0.2 < CP.tm b m)



theorem hi'_posA (hb : TBehX N dat envEn x r t0 H) (v w : α) : 1 ≤ hi' N v w := by
  unfold hi'
  by_cases h : reads N v w = true
  · simp only [h, if_true]
    simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := hb.lo1 v w h.1 h.2
    obtain ⟨a1, a2, _, _⟩ := hb.rd v w (t0 + 1) h.1 h.2 (by omega)
    omega
  · simp only [h, if_false, Bool.false_eq_true]; exact Nat.le_refl _

/-- **Upper bounds are sound** up to a horizon where the invariants hold. -/
theorem up_sound (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckXA N dat envEn (fun w => x w t0) CP (L v) D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOKA N dat CP Up) (hS : SepOKA N CP Sep Up)
    (T : Nat) (hI : ∀ τ, τ ≤ T → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ T → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s)
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
        have h1 := Formal.Net.AO.tm_prev hTP w j (by omega) hlen
        have hip := ih (CP.tm w (j - 1)) (by omega) (w, j - 1) dp (Nat.le_refl _) hdp (by omega)
        have := hi'_posA hb w w
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
          have hip := ih (CP.tm w (j - 1)) (by have := Formal.Net.AO.tm_prev hTP w j (by omega) hlen; omega) (w, j - 1) dp
            (Nat.le_refl _) hdp (by omega)
          simp only at hip
          have := cnt_mono (x := x) (t0 := t0) w (τ + dp) (r w w T') (by omega)
          omega
      · simp only [hr, if_false, Bool.false_eq_true]; exact hcT1
    have hEn : Enabled CP (nT N x t0 r w T') w := by
      obtain ⟨alt, halt, hall⟩ := hca
      refine ⟨by rw [hnw]; exact hlen, alt, by rw [hnw]; exact halt, fun p hp => ?_⟩
      obtain ⟨dp, hdp, hle⟩ := hall p hp
      have htm := (hTP.2 w j hlen alt halt p hp).2
      have hip := ih (CP.tm p.1 p.2) (by omega) p dp (Nat.le_refl _) hdp (by omega)
      obtain ⟨_, r2, _, _⟩ := rho_boundsX hb w p.1 T' (by omega)
      simp only [nT]
      exact Nat.lt_of_lt_of_le hip (cnt_mono _ _ _ (by omega))
    -- the local check makes the gate move at `T'`
    have hT1 : t0 ≤ T' - 1 := by omega
    have hcons := read_consistentA hb hLs hTO hDE (T' - 1) hT1 (fun τ' h => hI τ' (by omega))
      (fun v s h1 h2 h3 h4 => hB v s h1 h2 (by omega) h4) (ss_mono hSS (by omega)) w
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
theorem sepSound_step (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckXA N dat envEn (fun w => x w t0) CP (L v) D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOKA N dat CP Up) (hS : SepOKA N CP Sep Up)
    (t : Nat) (ht : t0 ≤ t) (hI : ∀ τ, τ ≤ t → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s)
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
  rcases hS b m a k d hkl hd with ⟨hb', hm, hd0⟩ | hall | ⟨hk0, d', hd', hle⟩ |
      ⟨hd1, e0, dl, du, hdl, hdu, hle, htm⟩
  · subst hb' hm hd0; exact ⟨by omega, by simpa using hh1⟩
  · obtain ⟨_, alt, halt, hin⟩ := hen
    rw [hna] at halt
    obtain ⟨p, hp, d', hd', hle⟩ := hall alt halt
    have hpc : p.2 < nT N x t0 r a (t + 1) p.1 := hin p hp
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
theorem timedA_follows (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckXA N dat envEn (fun w => x w t0) CP (L v) D cl gd v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOKA N dat CP Up) (hS : SepOKA N CP Sep Up)
    (hTF : TmOK CF)
    (hRT : ∀ u k, k < CF.len u → ∀ altP ∈ CP.causes u k, ∃ altF ∈ CF.causes u k, ∀ p ∈ altF,
      p ∈ altP ∨ ∃ d, Sep p.1 p.2 u k = some d ∧ 1 ≤ d)
    (hGC : ∀ c ∈ cl, N.gate c.z = true → GateProof N dat Sep (fun w => x w t0) cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainOK Sep c cs)
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, Holds x t0 H c s)
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
        fun v hve hch => change_okA hb hLs hTO hDE hloc hlenEq hgdF hGd t ht hI hB hC hSS v hve hch
      have hB' : ∀ v s, dat v = false → t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s := by
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

end Formal.Net.AO
