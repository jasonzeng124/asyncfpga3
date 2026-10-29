import Formal.Core.XAudit.Events9Cert

/-!
# Formal.Core.XAudit.Events9Par — a log rule for PARALLEL C-elements (probe E9Par, shard A)

See `formal/notes/A-e9par.md`.

With the corrected arbiter core (probe E8ArbFix, `Events9Arb`) each grant `g_b` has a SHADOW
`s_b`: two virtual two-pin C-elements reading the SAME request and the SAME `ctl` through
DIFFERENT pin bands, and `R0` is the merge of the shadows. Every Events7/8/9 log rule bounds a
node's count from ABOVE by what it reads; none bounds a node's count from BELOW, so no walk can
pass from a shadow to its grant (or back): 54 items per gcd_hw row lost their certificates.

The count of a non-merge stage is the MINIMUM of its pin counts at its sample (`Beh7.M_eq`), so
a lower bound needs no induction: if every pin of `y` reads (through an UPPER band end) a source
that the matching pin of `z` reads (through a LOWER band end), then `y` at time `v + e` has seen
everything `z` saw at `v`, provided `y`'s reset is not still holding it low.

* `ParOK` (decidable, per ordered pair `z → y`, from the certificate's bands): `z`, `y` non-merge
  stages in the reset-synchronous set `rs`; a pin map `pm` sending each pin `q` of `y` to a pin
  `p` of `z` with the same source, compatible kinds (plain / line on both, or filtered with the
  same label on both), `off z p ≤ off y q + tp`, and for every copy `i`
  `hiF y + hiC y q i ≤ e + loF z + loP z p` (and `hiF y ≤ e + loF z`).
* **`par_fact`**: under `ParOK` and `RstSync` (the nodes of `rs` have one common reset signal),
  `M v z ≤ M (v + e) y + tp` for every `v` — a NEGATIVE-delay walk `z → y`.
* the log `LnP`: the Events7 lines (`base`), a first-reach `dsub` line in the LOG (sound by
  `Events9.dsub9_sound` when its `wS` is valid), and **`par w1 w2 z y e tp pm`**: from a walk
  `w1` ending at `z` (any label context) and an unlabelled walk `w2` from `y`, with
  `e ≤ d1 + d2`, the walk `w1 · (z ⇝ y) · w2` with delay `d1 + d2 − e` and `t1 + tp + t2`
  tokens. A `par` / `dsub` line whose check FAILS is not a rejection of the log: it gets the
  trivial judgement `refl y` (resp. `refl a`), so only the items citing it lose their
  certificate (the controls rely on this).
* **`runLogP_sound`**: every judgement of an accepted log holds for every `Beh7` with
  `RstSync` (under `Net4.OK7`, SelPart).
* **`verdict9par`**: `Events9.verdict9` with the log `LnP`; the Back / line / exclusivity /
  guard checks (`backOK7`, `lineOK7`, `exclOK7`, `guardOK8` on the sanitized hypothesis lines)
  are the unchanged Events7/8 checks, evaluated on this log's judgements.

What it does NOT give: `RstSync` is a hypothesis on the realising behaviour (discharged at the
netlist level from the named hypothesis `HRst`, `Events9ParBeh`); nothing here says the
corrected core is right (that is `HARB7'`).
-/

namespace Formal.Core.XAudit.Events9Par

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (fmin fmin_le le_fmin fmin_mem)
open Formal.Core.XAudit.Events3 (filt filt_mono)
open Formal.Core.XAudit.Events4 (andCnt orCnt)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9

/-! ## 1. The parallel-pair check and the log -/

section
variable {N : Nat} (net : Net4 N) (b : Bands4 net)

/-- Pin `p` of `z` and pin `q` of `y` are PARALLEL: same source, same kind (not guarded), the
same label if filtered, the same operator if a line, and the same number of copies. -/
def PinPar (z : Fin N) (p : Fin (net.ar z)) (y : Fin N) (q : Fin (net.ar y)) : Prop :=
  net.src z p = net.src y q ∧ net.pk z p = net.pk y q ∧ net.pk y q ≠ PK.guard ∧
  (net.pk y q = PK.filt → net.grp z p = net.grp y q ∧ net.br z p = net.br y q) ∧
  (net.pk y q = PK.multi → net.op z p = net.op y q) ∧ net.nc z p = net.nc y q

instance (z : Fin N) (p : Fin (net.ar z)) (y : Fin N) (q : Fin (net.ar y)) :
    Decidable (PinPar net z p y q) := by
  unfold PinPar; exact inferInstance

/-- **The parallel-pair check** `z ⇝ y` with lag `e` and `tp` tokens (decidable; every band
inequality is checked on the certificate's own bands): `z`, `y` are non-merge stages of `rs`;
pin `q` of `y` is parallel to pin `pm q` of `z`, with `off z ≤ off y + tp`, and copy `i` of `y`'s
pin reads no earlier than copy `i` of `z`'s: `hiF y + hiC y q i ≤ e + loF z + loC z (pm q) i`. -/
def ParOK (rs : Nat → Bool) (z y : Fin N) (e tp : Nat) (pm : List Nat) : Prop :=
  rs z.val = true ∧ rs y.val = true ∧ net.mg z = false ∧ net.mg y = false ∧ b.hiF y ≤ e + b.loF z ∧
  ∀ q : Fin (net.ar y), ∃ hp : pm.getD q.val 0 < net.ar z,
    PinPar net z ⟨pm.getD q.val 0, hp⟩ y q ∧ net.off z ⟨pm.getD q.val 0, hp⟩ ≤ net.off y q + tp ∧
    ∀ i : Fin (net.nc y q), ∃ hi : i.val < net.nc z ⟨pm.getD q.val 0, hp⟩,
      b.hiF y + b.hiC y q i ≤ e + b.loF z + b.loC z ⟨pm.getD q.val 0, hp⟩ ⟨i.val, hi⟩

instance (rs : Nat → Bool) (z y : Fin N) (e tp : Nat) (pm : List Nat) :
    Decidable (ParOK net b rs z y e tp pm) := by
  unfold ParOK; exact inferInstance

/-- A log line: an Events7 line, a first-reach `dsub` line (its walk `wS : S → a` is checked by
`wsOK`), or a walk through a parallel pair. -/
inductive LnP where
  | base (l : Ln)
  | dsub (a xm S ab : Nat) (arms : List Arm) (w1 w2 wS : Nat)
  | par (w1 w2 z y e tp : Nat) (pm : List Nat)
  deriving Repr, Inhabited

/-- The trivial judgement `M u k ≤ M u k` (what a failing `par` / `dsub` line degrades to). -/
def degr (k : Nat) : Option Jd := if k < N then some ⟨false, k, none, k, 0, 0⟩ else none

/-- The conclusion of a `par` line (or `none` if a check fails). -/
def parJ (rs : Nat → Bool) (J : Array Jd) (w1 w2 z y e tp : Nat) (pm : List Nat) : Option Jd :=
  if hz : z < N then if hy : y < N then if h1 : w1 < J.size then if h2 : w2 < J.size then
    if ParOK net b rs ⟨z, hz⟩ ⟨y, hy⟩ e tp pm ∧ J[w1].u = false ∧ J[w1].bb = z ∧
        J[w2].u = false ∧ J[w2].c = none ∧ J[w2].a = y ∧ e ≤ J[w1].d + J[w2].d
    then some ⟨false, J[w1].a, J[w1].c, J[w2].bb, J[w1].d + J[w2].d - e, J[w1].t + tp + J[w2].t⟩
    else none else none else none else none else none

/-- **The conclusion of a log line.** -/
def conclP (rs : Nat → Bool) (parts : List (List Nat)) (J : Array Jd) : LnP → Option Jd
  | .base l => concl net b parts J l
  | .dsub a xm S ab arms w1 w2 wS =>
    if wsOK J S a wS then
      match hconcl net b parts J (.dsub a xm S ab arms w1 w2) with
      | some j => some j
      | none => degr (N := N) a
    else degr (N := N) a
  | .par w1 w2 z y e tp pm =>
    match parJ net b rs J w1 w2 z y e tp pm with
    | some j => some j
    | none => degr (N := N) y

def runFromP (rs : Nat → Bool) (parts : List (List Nat)) (J : Array Jd) : List LnP → Option (Array Jd)
  | [] => some J
  | ln :: l => match conclP net b rs parts J ln with
    | some j => runFromP rs parts (J.push j) l
    | none => none

def runLogP (rs : Nat → Bool) (parts : List (List Nat)) (log : List LnP) : Option (Array Jd) :=
  runFromP net b rs parts #[] log

end

/-! ## 2. Semantics: the parallel-pair lower bound -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **`RstSync`**: the nodes of `rs` share one reset signal. -/
def RstSync (rs : Nat → Bool) : Prop :=
  ∀ z y : Fin N, rs z.val = true → rs y.val = true → ∀ s, x.r z s = x.r y s

/-- **Parallel pins**: if every copy of `z`'s pin samples its source no later than the same
copy of `y`'s pin, `z`'s pin count is at most `y`'s (same kind, label, operator: the count of a
pin is monotone in its copies' counts). -/
theorem pin_par (z : Fin N) (p : Fin (net.ar z)) (y : Fin N) (q : Fin (net.ar y)) (h : PinPar net z p y q)
    (s1 s2 : Nat) (hcw : ∀ (i : Fin (net.nc y q)) (hi : i.val < net.nc z p),
      x.G z p ⟨i.val, hi⟩ s1 ≤ x.G y q i s2) :
    x.pc z p s1 (x.cm z p s1) ≤ x.pc y q s2 (x.cm y q s2) := by
  obtain ⟨hsrc, hk, hg, hl, hop, hnc⟩ := h
  have hc : ∀ (i : Fin (net.nc y q)) (hi : i.val < net.nc z p), x.cm z p s1 ⟨i.val, hi⟩ ≤ x.cm y q s2 i := by
    intro i hi; unfold Beh7.cm; rw [hsrc]; exact x.M_mono _ _ _ (hcw i hi)
  have hmin : fmin _ (x.cm z p s1) ≤ fmin _ (x.cm y q s2) := by
    obtain ⟨iy, hiy⟩ := fmin_mem _ (x.cm y q s2) (net.nc_pos y q)
    rw [hiy]
    have hi : iy.val < net.nc z p := by have := iy.isLt; omega
    exact Nat.le_trans (fmin_le _ _ ⟨iy.val, hi⟩) (hc iy hi)
  have hmax : fmax _ (x.cm z p s1) ≤ fmax _ (x.cm y q s2) := by
    apply fmax_le _ _ (net.nc_pos z p)
    intro i
    have hi : i.val < net.nc y q := by have := i.isLt; omega
    exact Nat.le_trans (hc ⟨i.val, hi⟩ i.isLt) (le_fmax _ _ _)
  unfold Beh7.pc
  cases hky : net.pk y q with
  | guard => exact absurd hky hg
  | plain =>
    have hkz : net.pk z p = PK.plain := hk.trans hky
    simp only [hkz]; exact hmax
  | filt =>
    have hkz : net.pk z p = PK.filt := hk.trans hky
    obtain ⟨hgr, hbr⟩ := hl hky
    simp only [hkz]; rw [hgr, hbr]; exact filt_mono _ _ hmax
  | multi =>
    have hkz : net.pk z p = PK.multi := hk.trans hky
    simp only [hkz]
    rw [hop hky]
    cases net.op y q
    · simp only [Bool.false_eq_true, ite_false]; unfold orCnt; omega
    · simp only [ite_true]; unfold andCnt; omega

/-- **`par_fact`** (the parallel C-element rule, semantic form): if `z ⇝ y` passes `ParOK` and
the nodes of `rs` share their reset, then `y`'s count at `v + e` is at least `z`'s at `v`, up to
`tp` tokens. No induction: a stage's count is the minimum of its pins' counts (`M_eq`); every copy
of every pin of `y` reads its source no earlier than the matching copy of `z` (the band
inequality), and `y`'s reset has ended when `z`'s has (`RstSync`, `hiF y ≤ e + loF z`). -/
theorem par_fact (hOK : net.OK7) {rs : Nat → Bool} (hrs : RstSync x rs) {z y : Fin N} {e tp : Nat}
    {pm : List Nat} (h : ParOK net b rs z y e tp pm) : ∀ v, x.M v z ≤ x.M (v + e) y + tp := by
  obtain ⟨hrz, hry, hmz, hmy, hF, hpins⟩ := h
  intro v
  rcases Nat.eq_zero_or_pos v with h0 | hv
  · subst h0; rw [x.M_zero]; exact Nat.zero_le _
  rw [x.M_eq v z hv, x.M_eq (v + e) y (by omega)]
  have aF1 := (x.wF z).le_late v
  have aF2 := (x.wF y).early_le (v + e)
  generalize x.F z v = s1 at aF1 ⊢
  generalize x.F y (v + e) = s2 at aF2 ⊢
  unfold Beh7.E
  simp only [hmz, hmy, Bool.false_eq_true, ite_false]
  cases hr1 : x.r z s1
  · have hr2 : x.r y s2 = false := by
      cases hh : x.r y s2
      · rfl
      · rw [← hrs z y hrz hry s2] at hh
        have := x.ranti z s1 s2 (by omega) hh
        rw [hr1] at this; exact absurd this (by decide)
    simp only [hr2, Bool.false_eq_true, ite_false]
    obtain ⟨q0, hq0⟩ := fmin_mem (net.ar y) (fun q => x.P y q s2) (net.ar_pos y)
    rw [hq0]
    obtain ⟨hp, hpp, hoff, hti⟩ := hpins q0
    have h1 := fmin_le (net.ar z) (fun p => x.P z p s1) ⟨_, hp⟩
    refine Nat.le_trans h1 ?_
    have hcw : ∀ (i : Fin (net.nc y q0)) (hi : i.val < net.nc z ⟨_, hp⟩),
        x.G z ⟨_, hp⟩ ⟨i.val, hi⟩ s1 ≤ x.G y q0 i s2 := by
      intro i hi
      obtain ⟨_, ht⟩ := hti i
      have g1 := (x.wG z ⟨_, hp⟩ ⟨i.val, hi⟩).le_late s1
      have g2 := (x.wG y q0 i).early_le s2
      omega
    have := pin_par x z ⟨_, hp⟩ y q0 hpp s1 s2 hcw
    show x.pc z _ s1 (x.cm z _ s1) + net.off z _ ≤ x.pc y q0 s2 (x.cm y q0 s2) + net.off y q0 + tp
    omega
  · simp

/-! ## 3. Soundness of the log -/

theorem degr_sound {k : Nat} {j : Jd} (h : degr (N := N) k = some j) : Holds x j := by
  unfold degr at h
  split at h
  · rename_i hk; cases h; exact ⟨hk, hk, fun u => by simp⟩
  · simp at h

variable (hOK : net.OK7)
include hOK

theorem parJ_sound {rs : Nat → Bool} (hrs : RstSync x rs) {J : Array Jd} (hJ : AllH x J)
    {w1 w2 z y e tp : Nat} {pm : List Nat} {j : Jd} (hc : parJ net b rs J w1 w2 z y e tp pm = some j) :
    Holds x j := by
  unfold parJ at hc
  split at hc
  · rename_i hz
    split at hc
    · rename_i hy
      split at hc
      · rename_i h1
        split at hc
        · rename_i h2
          split at hc
          · rename_i hcd
            obtain ⟨hpar, hu1, hb1, hu2, hc2, ha2, he⟩ := hcd
            cases hc
            have hf := par_fact x hOK hrs hpar
            have hf' : ∀ v, Mn x v z ≤ Mn x (v + e) y + tp := fun v => by
              unfold Mn; rw [dif_pos hz, dif_pos hy]; exact hf v
            obtain ⟨_, hbb, hw2⟩ := holds_w x (hJ w2 h2) hu2 hc2
            rw [ha2] at hw2
            have key : ∀ u, Mn x (u - J[w1].d) z ≤
                Mn x (u - (J[w1].d + J[w2].d - e)) J[w2].bb + (tp + J[w2].t) := by
              intro u
              by_cases hu : J[w1].d ≤ u
              · have k1 := hf' (u - J[w1].d)
                have k2 := hw2 (u - J[w1].d + e)
                have eq : u - J[w1].d + e - J[w2].d = u - (J[w1].d + J[w2].d - e) := by omega
                rw [eq] at k2
                omega
              · have : u - J[w1].d = 0 := by omega
                rw [this, Mn_zero]; exact Nat.zero_le _
            refine ⟨(hJ w1 h1).1, hbb, ?_⟩
            show HoldsC x false J[w1].c J[w1].a J[w2].bb (J[w1].d + J[w2].d - e) (J[w1].t + tp + J[w2].t)
            rcases hcc : J[w1].c with _ | ⟨g, β⟩
            · obtain ⟨_, _, hw1⟩ := holds_w x (hJ w1 h1) hu1 hcc
              rw [hb1] at hw1
              intro u; have := hw1 u; have := key u; omega
            · obtain ⟨_, _, hw1⟩ := holds_wc x (hJ w1 h1) hu1 hcc
              rw [hb1] at hw1
              intro u; have := hw1 u; have := key u; omega
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc
  · simp at hc

variable {parts : List (List Nat)} (hp : SelPart sel parts)
include hp

/-- **Soundness of one line.** -/
theorem conclP_sound {rs : Nat → Bool} (hrs : RstSync x rs) {J : Array Jd} (hJ : AllH x J) (ln : LnP)
    {j : Jd} (hc : conclP net b rs parts J ln = some j) : Holds x j := by
  cases ln with
  | base l => exact concl_sound x hOK hp hJ l hc
  | dsub a xm S ab arms w1 w2 wS =>
    simp only [conclP] at hc
    split at hc
    · rename_i hws
      split at hc
      · rename_i j' hj'
        cases hc; exact dsub9_sound x hOK hp hJ a xm S ab arms w1 w2 wS hws hj'
      · exact degr_sound x hc
    · exact degr_sound x hc
  | par w1 w2 z y e tp pm =>
    simp only [conclP] at hc
    split at hc
    · rename_i j' hj'
      cases hc; exact parJ_sound x hOK hrs hJ hj'
    · exact degr_sound x hc

theorem runFromP_sound {rs : Nat → Bool} (hrs : RstSync x rs) :
    ∀ (l : List LnP) {J J' : Array Jd}, AllH x J → runFromP net b rs parts J l = some J' → AllH x J'
  | [], J, J', hJ, h => by simp only [runFromP, Option.some.injEq] at h; subst h; exact hJ
  | ln :: l, J, J', hJ, h => by
      simp only [runFromP] at h
      split at h
      · rename_i j hj
        exact runFromP_sound hrs l (allH_push x hJ (conclP_sound x hOK hp hrs hJ ln hj)) h
      · simp at h

/-- **`runLogP_sound`**: every judgement of an accepted log holds, for every behaviour whose
`rs` nodes share their reset (under `Net4.OK7` and SelPart). -/
theorem runLogP_sound {rs : Nat → Bool} (hrs : RstSync x rs) {log : List LnP} {J : Array Jd}
    (h : runLogP net b rs parts log = some J) : AllH x J :=
  runFromP_sound x hOK hp hrs log (J := #[]) (fun i hi => absurd hi (by simp)) h

end

/-! ## 4. The verdict -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **`verdict9par`**: `Events9.verdict9` for the log `LnP` (parallel-pair and first-reach lines
in the log). Same item checks and residual obligations, plus `RstSync x rs`. -/
theorem verdict9par (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {rs : Nat → Bool}
    (hrs : RstSync x rs) {log : List LnP} {J : Array Jd} (hJ : runLogP net b rs parts log = some J)
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
    (hsel : x.SelOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  have hA := runLogP_sound x hOK hp hrs hJ
  refine safe8 x hOK hsel ?_ ?_ ?_ cg hgc ?_ rG
  · intro j p s hk
    cases hc : cl j p
    · exact rL j p s hk hc
    · exact lineOK7_sound x hA j p _ (hcl j p hc) s
  · intro j p s hm hk
    cases hc : cp j p
    · exact rB j p s hm hk hc
    · exact backOK7_sound x hOK hA j p hk _ (hcp j p hc) s
  · intro m s hm
    cases hc : cxm m
    · exact rX m s hm hc
    · exact exclOK7_sound x hOK hp hA m hm _ _ _ (hcx m hc) s
  · intro j p hk hc
    exact guardOK8_sound x hOK hA (hdsub_san x hOK hp hA hl) j p (gd j p) (fun s => hgc j p s hk) (hcg j p hc)

end

end Formal.Core.XAudit.Events9Par
