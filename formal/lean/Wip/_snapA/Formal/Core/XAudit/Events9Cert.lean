import Formal.Core.XAudit.Events8Cert

/-!
# Formal.Core.XAudit.Events9Cert — the first-reach SUB rule `dsub9`: HDsub discharged

Probe HDsub (shard A). See `formal/notes/A-events9.md`.

`Events8.verdict8` assumes `HDsub`: every `dsub` hypothesis judgement holds. A `dsub`
judgement is the conclusion of the Events7 SUB rule for a walk that starts at a node `a`
(the guarded source `D`) instead of the label's source `S`:

* `w1`: `M u a ≤ M (u − d1) xm + t1` (unlabelled walk `a → xm`, `xm` a merge);
* the arms `i ≠ ab` of `xm` are U-bounded by labels of `S`: `P xm i s ≤ filt_i (M (s − δi) S)`,
  pairwise exclusive with the label `ℓ = labA arms ab` of arm `ab`;
* `w2`: `M v (src xm ab) ≤ M (v − d2) bb + t2`;
* conclusion: `filt_ℓ (M u a) ≤ M (u − (d1 + loF xm + loP xm ab + d2)) bb + (t1 + t2)`.

From `S` it is the Events7 rule (conservation). From `a ≠ S` the counts at ONE time
do not imply it (`dsub_counts_neg`): the other arm may already count a transaction of
`S` that `a` has not reached.

**The rule `dsub9`** adds ONE premise, a log line `wS`: an unlabelled walk `S → a` with
at most one token, `M v S ≤ M (v − dW) a + tW`, `tW ≤ 1` (any delay `dW`, also 0).

**Soundness (`first_reach`, `dsub9_sound`)**, by strong induction on the time `u`
(the "first time `S` passes `M u a`" argument, as a well-founded descent). Let
`m = M u a` and `s = F xm (u − d1)` the merge's sample.
* If `M s S ≤ m`: the other arms are below `Σ_{i≠ab} filt_i m`, and conservation
  (`filt_ℓ m + Σ_{i≠ab} filt_i m ≤ m`) with `w1` gives `filt_ℓ m ≤ P xm ab s + t1`.
* If `M s S ≥ m + 1`: by `wS`, `a` had already reached `m` at the EARLIER time
  `u' = s − dW < u` (`F xm v < v`), and `M` is monotone, so `M u' a = m`. The induction
  hypothesis at `u'` and monotonicity of `P xm ab ∘ F xm` give the bound at `u`.
Then `w2` finishes as in the Events7 SUB rule. The minimum-time witness is the walk
`wS`; the descent ends because each step goes strictly back in time.

**Discharge.** `san` turns a hypothesis line `HLn9` into an Events8 `HLn`: a `dsub` line
whose `wS` is valid (`wsOK`) stays a `dsub`, one without a valid `wS` becomes `copy J.size`
(no judgement, so a guard certificate that cites it is rejected). `hdsub_san`: HDsub holds
for the sanitized list, for EVERY behaviour. `verdict9` = `verdict8` with that list and
no HDsub hypothesis.
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

/-! ## 1. The first-reach lemma (abstract) -/

/-- **`first_reach`** (abstract form of the `dsub9` argument).
`Dc` = the start's count (`M · a`), `Sc` = the label source's count (`M · S`),
`σ u` = the merge's sample for time `u`, `A` = the target arm's count at a sample,
`O` = the other arms' total, `R n` = the other labels' branch counts of `n`, `fb` = the
target label's branch count. -/
theorem first_reach (Dc Sc A O R fb σ : Nat → Nat) (t1 dW : Nat)
    (hD0 : Dc 0 = 0) (hDm : ∀ a c, a ≤ c → Dc a ≤ Dc c)
    (hσ : ∀ u, 1 ≤ u → σ u < u) (hσm : ∀ a c, a ≤ c → σ a ≤ σ c)
    (hAm : ∀ a c, a ≤ c → A a ≤ A c) (hRm : ∀ a c, a ≤ c → R a ≤ R c)
    (hcons : ∀ n, fb n + R n ≤ n)
    (h1 : ∀ u, Dc u ≤ A (σ u) + O (σ u) + t1)
    (hO : ∀ s, O s ≤ R (Sc s))
    (hW : ∀ v, Sc v ≤ Dc (v - dW) + 1) :
    ∀ u, fb (Dc u) ≤ A (σ u) + t1 := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    rcases Nat.eq_zero_or_pos u with hu0 | hu1
    · subst hu0; rw [hD0]; have := hcons 0; omega
    · by_cases hn : Sc (σ u) ≤ Dc u
      · have := hRm _ _ hn; have := hcons (Dc u); have := hO (σ u); have := h1 u; omega
      · have hw := hW (σ u)
        have hlt := hσ u hu1
        have hle := hDm (σ u - dW) u (by omega)
        have heq : Dc (σ u - dW) = Dc u := by omega
        have ih' := ih (σ u - dW) (by omega)
        rw [heq] at ih'
        have := hAm _ _ (hσm (σ u - dW) u (by omega))
        omega

/-- Branch counts of one count split it exactly (two branches). -/
theorem filt_tf (s : Nat → Bool) : ∀ n, filt s true n + filt s false n = n
  | 0 => rfl
  | n + 1 => by
    have ih := filt_tf s n
    simp only [filt]
    cases s (n / 2) <;> simp <;> omega

/-- NEGATIVE CONTROL (why the first-reach walk `wS` may carry at most ONE token): with
`Sc v ≤ Dc (v − dW) + 2` instead of `+ 1`, every other premise of `first_reach` can hold
and the conclusion fail. Selections `true, false` (target label `true`); `Dc = 0, 1, 2, 2, …`;
`Sc = 2, 3, 3, …` (`S` has started transaction 1 when `a` is still at 1); `σ u = u − 1`;
the target arm stuck at 1 (`A ≡ 1`), the other arm at `filt false (Sc s)`; `t1 = dW = 0`.
At `u = 2`: `filt true 2 = 2 > 1`. -/
theorem first_reach_two_tok_neg :
    let s : Nat → Bool := fun k => k == 0
    let Dc : Nat → Nat := fun u => if u = 0 then 0 else if u = 1 then 1 else 2
    let Sc : Nat → Nat := fun v => if v = 0 then 2 else 3
    let A : Nat → Nat := fun _ => 1
    let O : Nat → Nat := fun s' => filt s false (Sc s')
    let R : Nat → Nat := fun n => filt s false n
    let fb : Nat → Nat := fun n => filt s true n
    let σ : Nat → Nat := fun u => u - 1
    (Dc 0 = 0) ∧ (∀ a c, a ≤ c → Dc a ≤ Dc c) ∧ (∀ u, 1 ≤ u → σ u < u) ∧ (∀ a c, a ≤ c → σ a ≤ σ c) ∧
    (∀ a c, a ≤ c → A a ≤ A c) ∧ (∀ a c, a ≤ c → R a ≤ R c) ∧ (∀ n, fb n + R n ≤ n) ∧
    (∀ u, Dc u ≤ A (σ u) + O (σ u) + 0) ∧ (∀ s', O s' ≤ R (Sc s')) ∧
    (∀ v, Sc v ≤ Dc (v - 0) + 2) ∧ ¬ (∀ v, Sc v ≤ Dc (v - 0) + 1) ∧
    ¬ (fb (Dc 2) ≤ A (σ 2) + 0) := by
  intro s Dc Sc A O R fb σ
  have f2 : filt s false 2 = 0 := by decide
  have f3 : filt s false 3 = 1 := by decide
  have t2 : filt s true 2 = 2 := by decide
  refine ⟨rfl, ?_, ?_, ?_, fun _ _ _ => Nat.le_refl 1, fun _ _ h => filt_mono _ _ h,
    fun n => Nat.le_of_eq (filt_tf s n), ?_, fun _ => Nat.le_refl _, ?_, ?_, ?_⟩
  · intro a c h; simp only [Dc]; split <;> split <;> (try split) <;> (try split) <;> omega
  · intro u hu; simp only [σ]; omega
  · intro a c h; simp only [σ]; omega
  · intro u; simp only [Dc, A, O, σ, Sc]
    rcases (show u = 0 ∨ u = 1 ∨ 2 ≤ u by omega) with h | h | h
    · subst h; simp
    · subst h; simp [f2]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), f3]; omega
  · intro v; simp only [Dc, Sc]; split <;> split <;> (try split) <;> omega
  · intro h; have := h 1; simp [Dc, Sc] at this
  · simp only [fb, Dc, A, σ]; decide

/-- NEGATIVE CONTROL (why HDsub is not a count fact at one time; A-events8's finding):
counts at ONE time that satisfy `w1` (`t1 = 0`), the other arm's U-bound and even the
one-token walk `S → a` AT THAT TIME (`M S = 3 ≤ M a + 1`), but violate the `dsub`
conclusion: selections `true, false` (target label `true`); `a` has finished
transaction 0 (`M a = 2`); `S` has started transaction 1 (`M S = 3`, branch `false`);
the other arm counts its first event of transaction 1; the target arm is still at 1.
`first_reach` excludes this only through the descent in time (at the earlier time
`u'` the target arm must already have counted 2). -/
theorem dsub_counts_neg :
    let s : Nat → Bool := fun k => k == 0
    -- w1: M a ≤ A + O + t1;  O ≤ filt false (M S);  M S ≤ M a + 1
    (2 ≤ 1 + 1 + 0) ∧ (1 ≤ filt s false 3) ∧ (3 ≤ 2 + 1) ∧
    -- conclusion filt true (M a) ≤ A + t1 FAILS
    ¬ (filt s true 2 ≤ 1 + 0) := by
  decide

/-! ## 2. The rule `dsub9` and its soundness -/

/-- A hypothesis line with the first-reach witness: `copy`, or a `dsub` line with `wS`, the
log line of an unlabelled walk from the label source `S` to the start `a` (≤ 1 token). -/
inductive HLn9 where
  | copy (i : Nat)
  | dsub (a xm S ab : Nat) (arms : List Arm) (w1 w2 wS : Nat)
  deriving Repr, Inhabited

/-- The first-reach witness check: log line `w` is an unlabelled walk `S → a` with at most
one token. -/
def WSOK (J : Array Jd) (S a w : Nat) : Prop :=
  ∃ h : w < J.size, J[w].u = false ∧ J[w].c = none ∧ J[w].a = S ∧ J[w].bb = a ∧ J[w].t ≤ 1

instance (J : Array Jd) (S a w : Nat) : Decidable (WSOK J S a w) := by unfold WSOK; exact inferInstance

def wsOK (J : Array Jd) (S a w : Nat) : Bool := decide (WSOK J S a w)

/-- **Sanitize** a hypothesis line: a `dsub` line keeps its judgement only with a valid `wS`
(otherwise it becomes `copy J.size`, which has no judgement). -/
def san (J : Array Jd) : HLn9 → HLn
  | .copy i => .copy i
  | .dsub a xm S ab arms w1 w2 wS => if wsOK J S a wS then .dsub a xm S ab arms w1 w2 else .copy J.size

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)
  (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts)

include hOK hp in
/-- **Soundness of `dsub9`**: a `dsub` judgement whose start `a` is reached from the label
source `S` by a valid first-reach walk (`wsOK`) holds for every behaviour. -/
theorem dsub9_sound {J : Array Jd} (hJ : AllH x J) (a xm S ab : Nat) (arms : List Arm) (w1 w2 wS : Nat)
    (hws : wsOK J S a wS = true) {jj : Jd}
    (hc : hconcl net b parts J (.dsub a xm S ab arms w1 w2) = some jj) : Holds x jj := by
  obtain ⟨hwi, wu, wc, wa, wbb, wt⟩ := of_decide_eq_true hws
  simp only [hconcl] at hc
  split at hc
  · rename_i h
    split at hc
    · rename_i hab
      split at hc
      · rename_i h1
        split at hc
        · rename_i h2
          split at hc
          · rename_i hcd
            obtain ⟨haN, hm, hA, hu1, hc1, ha1, hb1, hu2, hc2, ha2⟩ := hcd
            cases hc
            obtain ⟨_, _, hw1⟩ := holds_w x (hJ w1 h1) hu1 hc1
            obtain ⟨_, hbb, hw2⟩ := holds_w x (hJ w2 h2) hu2 hc2
            obtain ⟨_, _, hW⟩ := holds_w x (hJ wS hwi) wu wc
            rw [ha1, hb1] at hw1
            rw [ha2] at hw2
            rw [wa, wbb] at hW
            obtain ⟨hB, hX⟩ := armsOK_sound x hOK hp hJ ⟨xm, h⟩ hm S arms (some ab) hA
            let XM : Fin N := ⟨xm, h⟩
            let AB : Fin (net.ar XM) := ⟨ab, hab⟩
            let lab : Fin (net.ar XM) → Lab := fun i => labA arms i.val
            let σ : Nat → Nat := fun u => x.F XM (u - J[w1].d)
            let A : Nat → Nat := fun s => x.P XM AB s
            let O : Nat → Nat := fun s => fsum (net.ar XM) (fun i => if i = AB then 0 else x.P XM i s)
            let R : Nat → Nat := fun n => fsum (net.ar XM) (fun i => if i = AB then 0 else
              filt (sel (lab i).1) (lab i).2 n)
            let fb : Nat → Nat := fun n => filt (sel (lab AB).1) (lab AB).2 n
            have key := first_reach (fun u => Mn x u a) (fun v => Mn x v S) A O R fb σ J[w1].t J[wS].d
              (Mn_zero x a) (fun _ _ hac => Mn_mono x a hac)
              (fun u hu => by
                simp only [σ]
                rcases Nat.eq_zero_or_pos (u - J[w1].d) with h0 | h0
                · rw [h0, x.F_zero]; omega
                · have := x.F_lt XM (u - J[w1].d) h0; omega)
              (fun a c hac => (x.wF XM).mono _ _ (by omega))
              (fun a c hac => x.P_mono XM AB hac)
              (fun a c hac => fsum_mono _ _ _ (fun i => by
                by_cases hi : i = AB
                · simp [hi]
                · simp only [hi, ite_false]; exact filt_mono _ _ hac))
              (fun n => by
                have hs := fsum_split (net.ar XM) (fun i => filt (sel (lab i).1) (lab i).2 n) AB
                have hcn := fsum_filt_le (net.ar XM) lab hX n
                simp only [fb, R]; omega)
              (fun u => by
                have hw := hw1 u
                rcases Nat.eq_zero_or_pos (u - J[w1].d) with hv0 | hv1
                · rw [hv0, Mn_zero] at hw; omega
                · have hMn : Mn x (u - J[w1].d) xm = x.M (u - J[w1].d) XM := Mn_fin x _ XM
                  rw [hMn, x.M_merge XM hm _ hv1] at hw
                  have hsp := fsum_split _ (fun i => x.P XM i (x.F XM (u - J[w1].d))) AB
                  simp only [A, O, σ]; omega)
              (fun s => fsum_mono _ _ _ (fun i => by
                by_cases hi : i = AB
                · simp [hi]
                · simp only [hi, ite_false]
                  have hne : some ab ≠ some i.val := by
                    intro e; apply hi; apply Fin.ext; exact (Option.some.inj e).symm
                  obtain ⟨hb', _⟩ := hB i hne s
                  exact Nat.le_trans hb' (filt_mono _ _ (Mn_mono x S (by omega)))))
              (fun v => by have := hW v; omega)
            refine ⟨haN, hbb, fun u => ?_⟩
            show filt (sel (labA arms ab).1) (labA arms ab).2 (Mn x u a) ≤
              Mn x (u - (J[w1].d + b.loF XM + b.loP XM AB + J[w2].d)) J[w2].bb + (J[w1].t + J[w2].t)
            have k1 : filt (sel (labA arms ab).1) (labA arms ab).2 (Mn x u a) ≤
                x.P XM AB (x.F XM (u - J[w1].d)) + J[w1].t := key u
            have hpa := x.P_merge_le hOK XM hm AB (x.F XM (u - J[w1].d))
            have a1 : x.F XM (u - J[w1].d) ≤ u - J[w1].d - b.loF XM := (x.wF XM).le_late (u - J[w1].d)
            have h3 := x.M_mono (u - J[w1].d - b.loF XM - b.loP XM AB) (net.src XM AB)
              (x.F XM (u - J[w1].d) - b.loP XM AB) (Nat.sub_le_sub_right a1 _)
            have h4 : x.M (u - J[w1].d - b.loF XM - b.loP XM AB) (net.src XM AB) ≤
                Mn x (u - J[w1].d - b.loF XM - b.loP XM AB - J[w2].d) J[w2].bb + J[w2].t := by
              have := hw2 (u - J[w1].d - b.loF XM - b.loP XM AB); rw [Mn_fin] at this; exact this
            have e : u - J[w1].d - b.loF XM - b.loP XM AB - J[w2].d =
                u - (J[w1].d + b.loF XM + b.loP XM AB + J[w2].d) := by omega
            rw [e] at h4
            omega
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc
  · simp at hc

include hOK hp in
/-- **HDsub discharged**: for EVERY behaviour, every `dsub` judgement of the sanitized
hypothesis list holds (`Events8.HDsub`). -/
theorem hdsub_san {J : Array Jd} (hJ : AllH x J) (hl : List HLn9) :
    HDsub x parts J (hl.map (san J)) := by
  intro l hl' hd jj hc
  obtain ⟨l9, _, rfl⟩ := List.mem_map.mp hl'
  cases l9 with
  | copy i => simp [san, HLn.isD] at hd
  | dsub a xm S ab arms w1 w2 wS =>
    by_cases hw : wsOK J S a wS = true
    · simp only [san, hw, ite_true] at hc
      exact dsub9_sound x hOK hp hJ a xm S ab arms w1 w2 wS hw hc
    · simp only [san, hw, Bool.false_eq_true, ite_false, HLn.isD] at hd

end

/-! ## 3. The verdict without HDsub -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **`verdict9`**: `verdict8` with the hypothesis lines sanitized (`san`) and HDsub
PROVED (`hdsub_san`). A guarded pin is certified by `guardOK8` against the sanitized
list: its two labelled walks from the guarded source must carry a valid first-reach
walk `wS`. -/
theorem verdict9 (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {log : List Ln} {J : Array Jd}
    (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (rB : ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => x.P m p s) ≤ 1)
    (rL : ∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (rG : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin x j p)
    (hsel : x.SelOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) :=
  verdict8 x hOK hp hJ back line xS xw xa (hl.map (san J)) gd cp cxm cl cg hcp hcx hcl hcg hgc rB rX rL rG hsel
    (hdsub_san x hOK hp (runLog_sound x hOK hp hJ) hl)

end

end Formal.Core.XAudit.Events9
