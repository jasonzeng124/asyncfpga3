import Formal.Net.AO.Timed

/-!
# Formal.Cells.UnionUp — joining claim phases by an UPPER bound (shard B, 2026-11-09)

## Problem, plainly
Shard C's data layer proves a latch's value across its phases (transparent, enable uncertain, hold, ...) as a chain
of claims (`TimedU.ChainOK`). Two consecutive claims `c1`, `c2` are joined when `c1` lasts until `c2` starts, and the
only way `ChainOK` can say so is a LOWER bound: a separation `Sep(c2.A → c1.B) = d` ("`c1`'s end event comes at
least `d` after `c2`'s start event"). On THE target, pair (12,18), this fails for the bulk of the truncated latch
holds (B's tracing, JOURNAL-B 2026-11-09, class A): the claim on the latch's data input ends at an event `c1.B` that
comes causally BEFORE the latch's close `c2.A` (often the latch's own opening), with a large offset `c1.b`. Then
`Sep(c2.A → c1.B)` cannot exist (it is a natural number), and the right statement is an UPPER bound: the close
happens at most `u` after `c1.B`, and `c2.a + u ≤ c1.b`.

## Proved (core Lean, no Mathlib)
* `UpSoundT x t0 Up T`: "every `Up e0 e = some d` entry is a true upper bound up to horizon `T`" (the conclusion
  shape of C's `AO.up_sound`); `upSoundT_of_up_sound`: C's `up_sound` gives it, under exactly `up_sound`'s
  hypotheses.
* `UnionUpOK`, `union_holds_up`: if `c1.B = e1`, `c2.A = e2`, `Up e1 e2 = some u`, `c2.a + u ≤ c1.b` and `1 ≤ c2.a`,
  then at every `t ≤ T + 1` (upper bounds sound up to `T`) where both claims hold, their union holds (same value, `c1`'s start, `c2`'s end).
* `ChainUpOK`, `chain_holds_up`: chains whose links are joined by either rule (`Sep` as in `ChainOK`, `Up`, or `JoinAnc`: a `Sep` from a common ancestor `e0` to `c1`'s
  end and an `Up` from `e0` to `c2`'s start, `c2.a + u ≤ c1.b + s`; `union_holds_anc`);
  `chainOK_up_of_chainOK`: every `ChainOK` chain is a `ChainUpOK` chain, so this is a strict generalisation.
* `timedA_follows_up`: C's main AO theorem (`AO.timedA_follows`, proof copied) with data-claim chains in
  `ChainUpOK` form; it implies C's theorem (weaker `hGC`).

* `gate_firesA_up`, `timedA_live_up`: C's liveness theorems (proofs copied) with `ChainUpOK` chains.

## Measured use (JOURNAL-B 2026-11-09 10:2x, untrusted Python)
On pairs (12,18) and (17,5), once C's relative Up clause is in, neither the `Up` join nor `JoinAnc` joins any link
that the `Sep` join does not: they are sound generalisations with no measured use yet.

## Not shown
Class B (claim end and
close causally unordered) is the shape `JoinAnc` covers when C's Up/Sep tables reach a common ancestor; whether they
do is measured, not shown. Class C (re-open setup; a claim-builder artefact) is not addressed. No instance.
-/

namespace Formal.Cells.UnionUp
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR
  Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]

/-- Upper bounds are sound up to horizon `T`: if `e0` has happened by `τ` and `τ + d ≤ T`, `e` has happened by
`τ + d`. -/
def UpSoundT (x : α → Nat → Bool) (t0 : Nat) (Up : α × Nat → α × Nat → Option Nat) (T : Nat) : Prop :=
  ∀ (e0 e : α × Nat) (d τ : Nat), Up e0 e = some d → e0.2 < cnt x t0 e0.1 τ → τ + d ≤ T →
    e.2 < cnt x t0 e.1 (τ + d)

/-- Two consecutive claims joined by an upper bound: `c2` starts at most `u` after `c1`'s end event, early enough. -/
def UnionUpOK (Up : α × Nat → α × Nat → Option Nat) (c c1 c2 : Claim α) : Prop :=
  c1.z = c.z ∧ c2.z = c.z ∧ c1.val = c.val ∧ c2.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c2.B = c.B ∧ c2.b = c.b ∧
  (match c1.B, c2.A with
    | some e1, some e2 => ∃ u, Up e1 e2 = some u ∧ 1 ≤ c2.a ∧ c2.a + u ≤ (c1.b : Int)
    | none, _ => True
    | some _, none => True)

theorem union_holds_up {x : α → Nat → Bool} {t0 H T : Nat} {Up : α × Nat → α × Nat → Option Nat}
    (hUS : UpSoundT x t0 Up T) (c c1 c2 : Claim α) (hu : UnionUpOK Up c c1 c2) (t : Nat) (ht : t ≤ T + 1)
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
        obtain ⟨u, hU, ha0, hle⟩ := hj
        obtain ⟨h0, hc⟩ := hhb
        have hτ := hUS e1 e2 u ((t : Int) - c1.b).toNat hU hc (by omega)
        refine ⟨by omega, ?_⟩
        have : ((t : Int) - c2.a).toNat ≥ ((t : Int) - c1.b).toNat + u := by omega
        exact Nat.lt_of_lt_of_le hτ (cnt_mono e2.1 _ _ this)
    · rw [hB2, hb2]; exact hBn
  · rw [← hz1, ← hv1]
    apply h1 hH
    · rw [hA1, ha1]; exact hA
    · cases hB1 : c1.B with
      | none => trivial
      | some e1 => exact fun hh => hend ⟨e1, hB1, hh⟩

/-- The join through a common ancestor `e0`: `c1`'s end event comes at least `s` after `e0` (a `Sep` entry) and
`c2`'s start event at most `u` after it (an `Up` entry), with `c2.a + u ≤ c1.b + s`. -/
def JoinAnc (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c1 c2 : Claim α) : Prop :=
  match c1.B, c2.A with
  | some e1, some e2 => ∃ e0 s u, Sep e0.1 e0.2 e1.1 e1.2 = some s ∧ Up e0 e2 = some u ∧ 1 ≤ c2.a ∧
      c2.a + u ≤ (c1.b : Int) + s
  | none, _ => True
  | some _, none => True

theorem union_holds_anc {x : α → Nat → Bool} {t0 H T T' : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (hUS : UpSoundT x t0 Up T') (c c1 c2 : Claim α)
    (hz1 : c1.z = c.z) (hz2 : c2.z = c.z) (hv1 : c1.val = c.val) (hv2 : c2.val = c.val) (hA1 : c1.A = c.A)
    (ha1 : c1.a = c.a) (hB2 : c2.B = c.B) (hb2 : c2.b = c.b) (hj : JoinAnc Sep Up c1 c2)
    (t : Nat) (ht : t ≤ T) (ht' : t ≤ T' + 1)
    (h1 : Holds x t0 H c1 t) (h2 : Holds x t0 H c2 t) : Holds x t0 H c t := by
  intro hH hA hBn
  by_cases hend : ∃ e1, c1.B = some e1 ∧ hbI x t0 e1 ((t : Int) - c1.b)
  · obtain ⟨e1, he1, hhb⟩ := hend
    rw [← hz2, ← hv2]
    apply h2 hH
    · cases hA2 : c2.A with
      | none => trivial
      | some e2 =>
        unfold JoinAnc at hj
        rw [he1, hA2] at hj
        obtain ⟨e0, s, u, hS, hU, ha0, hle⟩ := hj
        have h0 := hSS e1.1 e0.1 e1.2 e0.2 s hS ((t : Int) - c1.b) (by omega) hhb
        obtain ⟨h00, hc0⟩ := h0
        have hτ := hUS e0 e2 u (((t : Int) - c1.b) - s).toNat hU hc0 (by omega)
        refine ⟨by omega, ?_⟩
        have : ((t : Int) - c2.a).toNat ≥ (((t : Int) - c1.b) - s).toNat + u := by omega
        exact Nat.lt_of_lt_of_le hτ (cnt_mono e2.1 _ _ this)
    · rw [hB2, hb2]; exact hBn
  · rw [← hz1, ← hv1]
    apply h1 hH
    · rw [hA1, ha1]; exact hA
    · cases hB1 : c1.B with
      | none => trivial
      | some e1 => exact fun hh => hend ⟨e1, hB1, hh⟩

/-- Chains whose consecutive claims are joined by a separation (as `ChainOK`) or by an upper bound. -/
def ChainUpOK (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c : Claim α) :
    List (Claim α) → Prop
  | [] => False
  | [c1] => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c1.B = c.B ∧ c1.b = c.b
  | c1 :: c2 :: cs => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧
      ((match c1.B, c2.A with
        | some e1, some e2 => ∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d
        | none, _ => True
        | some _, none => True) ∨
       (match c1.B, c2.A with
        | some e1, some e2 => ∃ u, Up e1 e2 = some u ∧ 1 ≤ c2.a ∧ c2.a + u ≤ (c1.b : Int)
        | none, _ => True
        | some _, none => True) ∨
       JoinAnc Sep Up c1 c2) ∧
      ChainUpOK Sep Up ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ (c2 :: cs)

theorem chain_holds_up {x : α → Nat → Bool} {t0 H T T' : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (hUS : UpSoundT x t0 Up T') (t : Nat) (ht : t ≤ T) (ht' : t ≤ T' + 1) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainUpOK Sep Up c cs → (∀ c' ∈ cs, Holds x t0 H c' t) →
      Holds x t0 H c t
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
    have hc' := chain_holds_up hSS hUS t ht ht' (c2 :: cs) c' hrest (fun d hd => hh d (by simp [hd]))
    have h1 := hh c1 (by simp)
    rcases hj with hj | hj | hj
    · exact union_holds hSS c c1 c' ⟨hz, rfl, hv, rfl, hA, ha, rfl, rfl, hj⟩ t ht h1 hc'
    · exact union_holds_up hUS c c1 c' ⟨hz, rfl, hv, rfl, hA, ha, rfl, rfl, hj⟩ t ht' h1 hc'
    · exact union_holds_anc hSS hUS c c1 c' hz rfl hv rfl hA ha rfl rfl hj t ht ht' h1 hc'

omit [DecidableEq α] in
/-- Every `ChainOK` chain is a `ChainUpOK` chain (the new rule only adds the upper-bound join). -/
theorem chainOK_up_of_chainOK {Sep : α → Nat → α → Nat → Option Nat} {Up : α × Nat → α × Nat → Option Nat} :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainOK Sep c cs → ChainUpOK Sep Up c cs
  | [], _, h => h
  | [_], _, h => h
  | _ :: c2 :: cs, _, h => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    exact ⟨hz, hv, hA, ha, Or.inl hj, chainOK_up_of_chainOK (c2 :: cs) _ hrest⟩

section bridge
open Formal.Net.AO
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Formal.Net.AO.Cert α} {L : α → α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

/-- C's `AO.up_sound`, under its own hypotheses at horizon `T`, gives `UpSoundT` at `T`: the upper-bound join of
`union_holds_up` can be used wherever C's induction already has `up_sound`. -/
theorem upSoundT_of_up_sound (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
    (T : Nat) (hI : ∀ τ, τ ≤ T → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ T → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ T → Holds x t0 H c s) (hSS : SepSound x t0 Sep T) :
    UpSoundT x t0 Up T := by
  intro e0 e d τ hU h0 hT
  exact up_sound hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS T hI hB hC hSS e0 τ h0
    (CP.tm e.1 e.2) e d (Nat.le_refl _) hU hT

open Formal.Net.OccNet (st)

/-- **C's `AO.timedA_follows` with `ChainUpOK` chains** (the proof is C's, copied verbatim from
`Formal/Net/AO/Timed.lean` at the commit of 2026-11-09 08:2x, except the chain step, which uses `chain_holds_up` with
`SepSound` at `t + 1` and `UpSoundT` at `t` from `upSoundT_of_up_sound`). Every hypothesis is C's except `hGC`, which
is weaker (every `ChainOK` chain is a `ChainUpOK` chain), so this theorem implies C's. -/
theorem timedA_follows_up (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUpOK Sep Up c cs)
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
          · have hUS := upSoundT_of_up_sound hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS t hI hB hC hSS
            exact chain_holds_up hSS' hUS (t + 1) (Nat.le_refl _) (Nat.le_refl _) cs c hch
              (fun c' hc' => gp c' (hcs c' hc').1 (hcs c' hc').2)
    · refine ⟨fun τ hτ => ?_, fun v s hve h1 h2 h3 => ?_, fun c hc s hs => hInit c hc s (by omega), hss0 _ (by omega)⟩
      · rw [hz τ (by omega)]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · omega

/-- **An enabled exact gate event happens within `K`** (C's `gate_firesA`, with `ChainUpOK` chains). -/
theorem gate_firesA_up (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUpOK Sep Up c cs)
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
    obtain ⟨hI, hB, hC, hSS⟩ := timedA_follows_up hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hEnvC hInit hDataLen t'
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
theorem timedA_live_up (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
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
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProof N dat Sep (fun w => x w t0) cl c') ∧ ChainUpOK Sep Up c cs)
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
  have hfol := timedA_follows_up hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hEnvC hInit hDataLen
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
      have := gate_firesA_up hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS hTF hRT hGC hEnvC hInit hDataLen hCPsub v hve hg (K v) hK2 hK1 t ht hv
      exact ⟨t + K v, by omega, v, hvU, by simp only [cntE, hve, Bool.false_eq_true, if_false]; exact this⟩
    | false =>
      obtain ⟨t', h1, h2⟩ := henv v t hg hve ht hv
      exact ⟨t', h1, v, hvU, by simp only [cntE, hve, Bool.false_eq_true, if_false]; exact h2⟩
  have hmonoE : ∀ u a b, a ≤ b → cntE dat x t0 u a ≤ cntE dat x t0 u b := by
    intro u a b hab; unfold cntE; split
    · exact Nat.le_refl _
    · exact cnt_mono u _ _ hab
  let M : Nat → Nat := fun t => Formal.Net.AO.sumOver U fun u => CF.len u - cntE dat x t0 u t
  have hMdec : ∀ t t', t ≤ t' → ∀ v ∈ U, cntE dat x t0 v t < cntE dat x t0 v t' → M t' < M t := by
    intro t t' htt v hv hlt
    have hle : ∀ u ∈ U, CF.len u - cntE dat x t0 u t' ≤ CF.len u - cntE dat x t0 u t := fun u _ => by
      have := hmonoE u t t' htt; omega
    have hlt' : CF.len v - cntE dat x t0 v t' < CF.len v - cntE dat x t0 v t := by
      have := (hI t' v).1; simp only at this; omega
    exact Formal.Net.AO.sumOver_lt hle v hv hlt'
  have full : ∀ n t, t0 ≤ t → M t ≤ n → ∃ T, t ≤ T ∧ ∀ u, cntE dat x t0 u T = CF.len u := by
    intro n
    induction n with
    | zero =>
      intro t ht hM
      refine ⟨t, Nat.le_refl _, fun u => ?_⟩
      rcases Nat.lt_or_ge (cntE dat x t0 u t) (CF.len u) with hlt | hge
      · exfalso
        have hpos := hcov u (by omega)
        have := Formal.Net.AO.sumOver_lt (U := U) (f := fun _ => 0) (g := fun u => CF.len u - cntE dat x t0 u t)
          (fun _ _ => Nat.zero_le _) u hpos (by omega)
        rw [Formal.Net.AO.sumOver_zero] at this
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

end bridge

end Formal.Cells.UnionUp
