import Formal.Core.XAudit.Events8Beh

/-!
# Formal.Core.XAudit.Events9Cert — HDsub discharged: the first-reach SUB rule (`dsub9`)

Probe HDsub. See `formal/notes/A-events9.md`.

`Events8.design_verdict8` assumes **HDsub**: every `dsub` hypothesis judgement (a
LABELLED walk that starts at a guarded source `D`, reaches a merge `xm` by an
unlabelled walk `w1`, enters arm `ab` of `xm` by SUB and continues by `w2`) holds:

    filt (sel g) β (M u D) ≤ M (u − (d1 + loF xm + loP xm ab + d2)) bb + (t1 + t2).

The Events7 SUB rule is sound only for a walk that starts at the label's source `S`.
Here a new rule, **`dsub9`**, derives the same conclusion from `D` with ONE more
premise: a log line `wS` that is an unlabelled walk `S → D` with at most one token
(`M u S ≤ M (u − dS) D + tS`, `tS ≤ 1`). Soundness (`dsub9_sound`) is the
"first time S reaches m + 1" argument (`m = M u D`):

* if at `xm`'s sample every other arm's `S`-count is `≤ m`, the other arms are at
  most `filt_i m` and conservation (`fsum_filt_le`) leaves `filt_ab m` for arm `ab`
  (`stepA`);
* otherwise some other arm saw `S ≥ m + 1`. Take the FIRST time `τ` at which
  `S ≥ m + 1` (`Nat.find`). By `wS`, `D ≥ m` at `τ − dS`; by `w1`, `xm ≥ m − t1`
  at `v1 = τ − dS − d1`; at `xm`'s sample of `v1` (strictly before `τ`) every
  arm's `S`-count is still `≤ m` (minimality), so `stepA` applies at `v1 ≤ u − d1`,
  and arm `ab` is monotone.

The checker side: a hypothesis line `HLn9` is Events8's `HLn` with the extra field
`wS`; `HLn9.toH J` turns it into an Events8 `HLn`, mapping a `dsub` whose `wS` does
NOT check (`wsOK`) to a line that `hconcl` rejects (so its guard is uncertified).
**`hdsub9`**: for an accepted log, `Events8.HDsub` holds for `hl.map (HLn9.toH J)`,
for EVERY behaviour. **`verdict9`** is `verdict8` without the HDsub hypothesis.
-/

namespace Formal.Core.XAudit.Events9

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events3 (filt filt_mono)
open Formal.Core.XAudit.Events4 (filt_le)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8

/-- A hypothesis line: Events8's `HLn` with, for `dsub`, the log line `wS` of an
unlabelled walk from the label source `S` to the walk's start `a` (≤ 1 token). -/
inductive HLn9 where
  | copy (i : Nat)
  | dsub (a xm S ab : Nat) (arms : List Arm) (w1 w2 wS : Nat)
  deriving Repr, Inhabited

/-- The side condition of `dsub9`: log line `wS` is an unlabelled walk `S → a`
with at most one token. -/
def WSOK (J : Array Jd) (a S wS : Nat) : Prop :=
  ∃ h : wS < J.size, J[wS].u = false ∧ J[wS].c = none ∧ J[wS].a = S ∧ J[wS].bb = a ∧ J[wS].t ≤ 1

instance (J : Array Jd) (a S wS : Nat) : Decidable (WSOK J a S wS) := by
  unfold WSOK; exact inferInstance

def wsOK (J : Array Jd) (a S wS : Nat) : Bool := decide (WSOK J a S wS)

/-- The Events8 hypothesis line checked by `dsub9`: a `dsub` whose `wS` does not
check becomes `copy J.size`, which `hconcl` rejects. -/
def HLn9.toH (J : Array Jd) : HLn9 → HLn
  | .copy i => .copy i
  | .dsub a xm S ab arms w1 w2 wS =>
    if wsOK J a S wS then .dsub a xm S ab arms w1 w2 else .copy J.size

/-- The FIRST time a decidable predicate holds (a minimum-time witness). -/
theorem exists_first (P : Nat → Prop) [DecidablePred P] :
    ∀ n, P n → ∃ τ, τ ≤ n ∧ P τ ∧ ∀ τ', τ' < τ → ¬ P τ' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hex : ∃ τ', τ' < n ∧ P τ'
    · obtain ⟨τ', hlt, hP⟩ := hex
      obtain ⟨τ, hle, hPτ, hmin⟩ := ih τ' hlt hP
      exact ⟨τ, by omega, hPτ, hmin⟩
    · exact ⟨n, Nat.le_refl n, hn, fun τ' hlt hP => hex ⟨τ', hlt, hP⟩⟩

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)
  (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts)

include hOK hp

/-- **The core of `dsub9`** (the first-reach argument): from `D` (`a`), with a walk
`a → xm` (`W1`) and a walk `S → a` with at most one token (`WS`), arm `ab` of `xm`
at the sample of `u − d1` carries the label's share of `M u a`, up to `t1`. -/
theorem dsub_core {J : Array Jd} (hJ : AllH x J) (xm : Fin N) (hm : net.mg xm = true)
    (ab : Fin (net.ar xm)) (S a : Nat) (arms : List Arm)
    (hA : ArmsOK net b parts J xm S arms (some ab.val))
    (d1 t1 dS tS : Nat) (htS : tS ≤ 1)
    (W1 : ∀ u, Mn x u a ≤ x.M (u - d1) xm + t1)
    (WS : ∀ u, Mn x u S ≤ Mn x (u - dS) a + tS) (u : Nat) :
    filt (sel (labA arms ab.val).1) (labA arms ab.val).2 (Mn x u a) ≤ x.P xm ab (x.F xm (u - d1)) + t1 := by
  obtain ⟨hB, hX⟩ := armsOK_sound x hOK hp hJ xm hm S arms (some ab.val) hA
  generalize hL : labA arms ab.val = L
  generalize hmd : Mn x u a = m
  have hflt := filt_le (sel L.1) L.2 m
  -- (A) at a sample where every other arm's S-count is ≤ m
  have stepA : ∀ v, 1 ≤ v → (∀ i : Fin (net.ar xm), i ≠ ab →
      Mn x (x.F xm v - armDl net b J xm S arms i) S ≤ m) → m ≤ x.M v xm + t1 →
      filt (sel L.1) L.2 m ≤ x.P xm ab (x.F xm v) + t1 := by
    intro v hv hall hmv
    rw [x.M_merge xm hm v hv] at hmv
    generalize x.F xm v = s at hall hmv ⊢
    have hrest : fsum (net.ar xm) (fun i => if i = ab then 0 else x.P xm i s) ≤
        fsum (net.ar xm) (fun i => if i = ab then 0 else filt (sel (labA arms i.val).1) (labA arms i.val).2 m) := by
      apply fsum_mono; intro i
      by_cases hi : i = ab
      · simp [hi]
      · simp only [hi, ite_false]
        have hne : some ab.val ≠ some i.val := by
          intro e; apply hi; apply Fin.ext; exact (Option.some.inj e).symm
        obtain ⟨hb, _⟩ := hB i hne s
        exact Nat.le_trans hb (filt_mono _ _ (hall i hi))
    have hsp := fsum_split _ (fun i => x.P xm i s) ab
    have hspl := fsum_split _ (fun i => filt (sel (labA arms i.val).1) (labA arms i.val).2 m) ab
    have hcons := fsum_filt_le (net.ar xm) (fun i => labA arms i.val) hX m
    simp only [hL] at hspl
    try dsimp only at hsp hspl hcons
    omega
  -- trivial case: nothing to carry
  have triv : ∀ v, m ≤ x.M v xm + t1 → v = 0 → filt (sel L.1) L.2 m ≤ x.P xm ab (x.F xm (u - d1)) + t1 := by
    intro v hmv hv0
    rw [hv0, x.M_zero] at hmv; omega
  have hW0 : m ≤ x.M (u - d1) xm + t1 := by rw [← hmd]; exact W1 u
  by_cases hc : ∃ i : Fin (net.ar xm), i ≠ ab ∧ m + 1 ≤ Mn x (x.F xm (u - d1) - armDl net b J xm S arms i) S
  · -- some other arm already saw S ≥ m + 1: go back to the FIRST time S reached m + 1
    obtain ⟨i, _, hi⟩ := hc
    obtain ⟨τ, hτle, hτ, hmin⟩ := exists_first (fun τ => m + 1 ≤ Mn x τ S) _ hi
    have hlate := (x.wF xm).le_late (u - d1)
    -- by WS, D ≥ m at τ − dS; by W1, xm ≥ m − t1 at v1
    have h1 := WS τ
    have h2 := W1 (τ - dS)
    have hDm : m ≤ x.M (τ - dS - d1) xm + t1 := by omega
    rcases Nat.eq_zero_or_pos (τ - dS - d1) with hv0 | hv1
    · exact triv _ hDm hv0
    · have hall : ∀ i' : Fin (net.ar xm), i' ≠ ab →
          Mn x (x.F xm (τ - dS - d1) - armDl net b J xm S arms i') S ≤ m := by
        intro i' _
        have hF := x.F_lt xm (τ - dS - d1) hv1
        have := hmin (x.F xm (τ - dS - d1) - armDl net b J xm S arms i') (by omega)
        omega
      have hA1 := stepA _ hv1 hall hDm
      have hmo := x.P_mono xm ab ((x.wF xm).mono (τ - dS - d1) (u - d1) (by omega))
      omega
  · -- every other arm's S-count is ≤ m already at xm's sample of u − d1
    have hall : ∀ i : Fin (net.ar xm), i ≠ ab →
        Mn x (x.F xm (u - d1) - armDl net b J xm S arms i) S ≤ m := by
      intro i hi
      apply Nat.le_of_not_lt
      intro hlt
      exact hc ⟨i, hi, hlt⟩
    rcases Nat.eq_zero_or_pos (u - d1) with hv0 | hv1
    · exact triv _ hW0 hv0
    · exact stepA _ hv1 hall hW0

/-- **Soundness of the `dsub9` rule**: the `dsub` judgement (Events8's `hconcl`) of a
line whose `wS` checks holds for every behaviour. -/
theorem dsub9_sound {J : Array Jd} (hJ : AllH x J) {a xm S ab : Nat} {arms : List Arm} {w1 w2 wS : Nat}
    (hw : wsOK J a S wS = true) {jj : Jd}
    (h : hconcl net b parts J (HLn.dsub a xm S ab arms w1 w2) = some jj) : Holds x jj := by
  obtain ⟨hwS, wu, wc, wa, wbb, wt⟩ := of_decide_eq_true hw
  obtain ⟨_, _, WS⟩ := holds_w x (hJ wS hwS) wu wc
  rw [wa, wbb] at WS
  simp only [hconcl] at h
  split at h
  · rename_i hxm
    split at h
    · rename_i hab
      split at h
      · rename_i h1
        split at h
        · rename_i h2
          split at h
          · rename_i hcd
            obtain ⟨ha, hm, hA, hu1, hc1, ha1, hb1, hu2, hc2, ha2⟩ := hcd
            cases h
            obtain ⟨_, _, hw1⟩ := holds_w x (hJ w1 h1) hu1 hc1
            obtain ⟨_, hbb, hw2⟩ := holds_w x (hJ w2 h2) hu2 hc2
            rw [ha1, hb1] at hw1
            rw [ha2] at hw2
            refine ⟨ha, hbb, fun u => ?_⟩
            have W1 : ∀ u, Mn x u a ≤ x.M (u - J[w1].d) ⟨xm, hxm⟩ + J[w1].t := by
              intro u; have := hw1 u; rw [Mn_fin x _ ⟨xm, hxm⟩] at this; exact this
            have hcore := dsub_core x hOK hp hJ ⟨xm, hxm⟩ hm ⟨ab, hab⟩ S a arms hA
              J[w1].d J[w1].t J[wS].d J[wS].t wt W1 WS u
            dsimp only at hcore
            show filt (sel (labA arms ab).1) (labA arms ab).2 (Mn x u a) ≤ Mn x (u - (J[w1].d + b.loF ⟨xm, hxm⟩ +
              b.loP ⟨xm, hxm⟩ ⟨ab, hab⟩ + J[w2].d)) J[w2].bb + (J[w1].t + J[w2].t)
            have hpA := x.P_merge_le hOK ⟨xm, hxm⟩ hm ⟨ab, hab⟩ (x.F ⟨xm, hxm⟩ (u - J[w1].d))
            have a1 := (x.wF ⟨xm, hxm⟩).le_late (u - J[w1].d)
            have h3 := x.M_mono (u - J[w1].d - b.loF ⟨xm, hxm⟩ - b.loP ⟨xm, hxm⟩ ⟨ab, hab⟩)
              (net.src ⟨xm, hxm⟩ ⟨ab, hab⟩)
              (x.F ⟨xm, hxm⟩ (u - J[w1].d) - b.loP ⟨xm, hxm⟩ ⟨ab, hab⟩) (by omega)
            have h4 := hw2 (u - J[w1].d - b.loF ⟨xm, hxm⟩ - b.loP ⟨xm, hxm⟩ ⟨ab, hab⟩)
            rw [Mn_fin] at h4
            have e2 : u - (J[w1].d + b.loF ⟨xm, hxm⟩ + b.loP ⟨xm, hxm⟩ ⟨ab, hab⟩ + J[w2].d) =
                u - J[w1].d - b.loF ⟨xm, hxm⟩ - b.loP ⟨xm, hxm⟩ ⟨ab, hab⟩ - J[w2].d := by omega
            rw [e2]
            omega
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- **HDsub discharged.** For an accepted log (`AllH`), Events8's hypothesis `HDsub`
holds for the hypothesis lines `hl.map (HLn9.toH J)`, for every behaviour. -/
theorem hdsub9 {J : Array Jd} (hJ : AllH x J) (hl : List HLn9) :
    HDsub x parts J (hl.map (HLn9.toH J)) := by
  intro l hmem hD jj hjj
  obtain ⟨l9, _, rfl⟩ := List.mem_map.mp hmem
  cases l9 with
  | copy i => simp [HLn9.toH, HLn.isD] at hD
  | dsub a xm S ab arms w1 w2 wS =>
    simp only [HLn9.toH] at hD hjj
    by_cases hw : wsOK J a S wS = true
    · simp only [hw, ite_true] at hjj
      exact dsub9_sound x hOK hp hJ hw hjj
    · simp [hw, HLn.isD] at hD

end

/-! ## The verdict without HDsub -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **`verdict9`**: `verdict8` with the guard certificates checked against the
hypothesis lines `hl.map (HLn9.toH J)` — and NO `HDsub` hypothesis (`hdsub9`). -/
theorem verdict9 (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {log : List Ln} {J : Array Jd}
    (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (HLn9.toH J)) j p (gd j p) = true)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (rB : ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => x.P m p s) ≤ 1)
    (rL : ∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (rG : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin x j p)
    (hsel : x.SelOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) :=
  verdict8 x hOK hp hJ back line xS xw xa (hl.map (HLn9.toH J)) gd cp cxm cl cg hcp hcx hcl hcg hgc rB rX rL rG
    hsel (hdsub9 x hOK hp (runLog_sound x hOK hp hJ) hl)

end

/-! ## Negative control -/

/-- NEGATIVE CONTROL (why `dsub9` needs the first-reach argument, not the counts at
one time): `sel` with transaction 0 on `true`, transaction 1 on `false`. Source count
`m = M u D = 2` (transaction 0 complete), `S = 3` (transaction 1 started), the other
arm (`false`) at `filt false 3 = 1`, the merge at `1 + 1 = 2 = m`: every one-time fact
the Events7 SUB proof uses holds, yet the target arm (`true`) at `1` is one short of
its share `filt true 2 = 2`. -/
theorem dsub_onetime_neg :
    let s : Nat → Bool := fun k => decide (k = 0)
    filt s true 2 = 2 ∧ filt s false 3 = 1 ∧ 1 + filt s false 3 = 2 ∧ ¬ (filt s true 2 ≤ 1 + 0) := by
  decide

end Formal.Core.XAudit.Events9
