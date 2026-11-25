import Formal.Core.XAudit.Events9Beh

/-!
# Formal.Core.XAudit.Events9Prefix — the routed-timing verdict, prefix by prefix

Probe E8Causal (shard A). Notes: `formal/notes/A-e8causal.md`.

`Events9.design_verdict9` (via `Events8.safe8`) proves the count/wire link of every node at
EVERY time from SelOK (and the residual obligations) at EVERY sample. Two open obligations
need the link at earlier times to establish SelOK itself (E8SelC's H_ACK_LAG, E8Arb's Unc),
which is circular in that all-times form. This file proves the time-inductive form.

* `SelAt x s`: SelOK at ONE sample `s` (all filtered pins, all copies).
* `Link x t`: the count/wire link `c j u = ph (v j) (M u j)` of every node at every `u ≤ t`.
* **`safe8_upto`**: `safe8` with SelOK, LineOK, PinOK, ExclOK and the guard facts assumed
  only at the samples `s < t0`; conclusion `Link x t0`. The lag is `L = 0` (a node's value at
  `t` is computed from its sample `F t < t`, so samples before `t0` decide `[0, t0]`).
* `safe8_of_upto`: `safe8`'s conclusion as a corollary (statement of `safe8` re-derived).
* **`verdict9_upto`**: `verdict9` in prefix form (the certified items are count facts at all
  times; SelOK and the residual obligations only before `t0`).
* **`design_verdict9_upto`**: `design_verdict9` in prefix form. The realisation `bh` is chosen
  ONCE (it does not depend on `t0`); for every `t0`, SelPart, SelOK at the samples `< t0` and
  the residual obligations at the samples `< t0` give the link of every real LUT wire on
  `[0, t0]` (and `Link bh t0` for every node, virtual ones included).
* **`design_verdict9'`**: `design_verdict9`'s exact statement, proved from the prefix form.
* **`causal_close`**: the induction that removes the circularity. If SelOK at each sample `s`
  follows from the link at all times `< s` (a CAUSAL derivation of SelOK, e.g. through
  H_BUNDLE and a lag argument), then the link holds at all times and SelOK holds.

NOT covered: H_ARB is still assumed at all times (the realisation `bh` is built from it); a
prefix form of H_ARB needs an ND7 prefix-extension lemma (notes §4).
-/

namespace Formal.Core.XAudit.Events9Prefix

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_off offB)
open Formal.Core.XAudit.Events2 (cel fmin fmin_le le_fmin fmin_mono fmin_mem ph_xor)
open Formal.Core.XAudit.Events3 (filt filt_mono steer_val)
open Formal.Core.XAudit.Events4 (andCnt orCnt)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9

/-! ## 1. Prefix predicates -/

section P
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- SelOK at ONE sample `s`. -/
def SelAt (s : Nat) : Prop :=
  ∀ j p (i : Fin (net.nc j p)), net.pk j p = PK.filt → x.M (x.G j p i s) (net.src j p) % 2 = 1 →
    x.sv j p s = sel (net.grp j p) (x.M (x.G j p i s) (net.src j p) / 2)

/-- The count/wire link of every node at every time `u ≤ t`. -/
def Link (t : Nat) : Prop := ∀ u, u ≤ t → ∀ j : Fin N, x.c j u = ph (net.v j) (x.M u j)

theorem selOK_iff : x.SelOK ↔ ∀ s, SelAt x s :=
  ⟨fun h s j p i hk hodd => h j p s i hk hodd, fun h j p s i hk hodd => h s j p i hk hodd⟩

/-- GuardCnt (Events8) at the samples before `t0`. -/
def GuardCntB (t0 : Nat) (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  ∀ s, s < t0 → net.mg j = false → x.r j s = false →
    x.P j p s ≤ x.M (x.Q j s) j + 1 ∧ ContigF (net.nc j p) (x.cm j p s) ∧
    (x.P j (net.gp j p) s = x.M (x.Q j s) j + 1 →
      lineCnt (net.op j p) (net.nc j p) (x.cm j p s) % 2 = 1 →
      sel (net.grp j p) (lineCnt (net.op j p) (net.nc j p) (x.cm j p s) / 2) = net.br j p)

/-- GuardPin (Events8; GuardOK for one uncertified guarded pin) at the samples before `t0`. -/
def GuardPinB (t0 : Nat) (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  ∀ s, s < t0 → net.mg j = false → x.r j s = false →
    x.P j p s ≤ x.M (x.Q j s) j + 1 ∧
    (x.P j (net.gp j p) s = x.M (x.Q j s) j + 1 → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s))

theorem guardCntB_of {j : Fin N} {p : Fin (net.ar j)} (h : GuardCnt x j p) (t0 : Nat) : GuardCntB x t0 j p :=
  fun s _ hm hr => h s hm hr

theorem guardPinB_of {j : Fin N} {p : Fin (net.ar j)} (h : GuardPin x j p) (t0 : Nat) : GuardPinB x t0 j p :=
  fun s _ hm hr => h s hm hr

/-- `Beh7.pin_val` with SelOK and LineOK at the ONE sample used. -/
theorem pin_val_at (hOK : net.OK7) (j : Fin N) (p : Fin (net.ar j)) (s : Nat)
    (hsel : ∀ i : Fin (net.nc j p), net.pk j p = PK.filt → x.M (x.G j p i s) (net.src j p) % 2 = 1 →
      x.sv j p s = sel (net.grp j p) (x.M (x.G j p i s) (net.src j p) / 2))
    (hline : net.pk j p = PK.multi → ContigF (net.nc j p) (x.cm j p s)) (hk : net.pk j p ≠ PK.guard)
    (ih : ∀ i, x.c (net.src j p) (x.G j p i s) = ph (net.v (net.src j p)) (x.cm j p s i)) :
    (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) := by
  obtain ⟨hnc, hv, hinv, _, _⟩ := hOK j p
  rw [x.hpin j p s]
  unfold Beh7.P Beh7.pc Net4.off
  cases hpk : net.pk j p with
  | guard => exact absurd hpk hk
  | plain =>
    have h1 := hnc (by rw [hpk]; decide)
    simp only [hpk]
    rw [Beh4.fany_one h1, Beh4.fmax_one h1, ih, ph_xor]
    exact ph_off _ _ _
  | filt =>
    have h1 := hnc (by rw [hpk]; decide)
    have hvs := hv (Or.inr hpk)
    have hi := hinv hpk
    simp only [hpk]
    rw [Beh4.fany_one h1, Beh4.fmax_one h1, ih, hvs, hi]
    have st := steer_val (sel (net.grp j p)) (net.br j p) (x.cm j p s ⟨0, by omega⟩) (x.sv j p s)
      (fun h => hsel ⟨0, by omega⟩ hpk h)
    rw [st, ph_xor]
    exact ph_off _ _ _
  | multi =>
    have hvs := hv (Or.inl hpk)
    have hc := hline hpk
    simp only [hpk]
    have e : (fun i => x.c (net.src j p) (x.G j p i s)) = (fun i => ph false (x.cm j p s i)) := by
      funext i; rw [ih, hvs]
    rw [e]
    cases net.op j p
    · simp only [Bool.false_eq_true, ite_false]
      rw [orF_val _ (net.nc_pos j p) _ hc, ph_xor, hvs]; exact ph_off _ _ _
    · simp only [ite_true]
      rw [andF_val _ (net.nc_pos j p) _ hc, ph_xor, hvs]; exact ph_off _ _ _

/-! ## 2. `safe8` prefix by prefix -/

/-- **`safe8_upto`** (the prefix form of `Events8.safe8`). If SelOK, LineOK, PinOK, ExclOK
and the guard facts (certified: `GStruct` + `GuardCnt`; uncertified: `GuardPin`) hold at
every sample `s < t0`, then every node's value equals its reset value flipped `M u j` times
at every `u ≤ t0`. Lag `L = 0`. -/
theorem safe8_upto (hOK : net.OK7) (t0 : Nat)
    (hsel : ∀ s, s < t0 → SelAt x s)
    (hline : ∀ j p s, s < t0 → net.pk j p = PK.multi → ContigF (net.nc j p) (x.cm j p s))
    (hpinok : ∀ j p s, s < t0 → net.mg j = false → net.pk j p ≠ PK.guard → x.P j p s ≤ x.M (x.Q j s) j + 1)
    (hexcl : ∀ j s, s < t0 → net.mg j = true → fodd (net.ar j) (fun p => x.P j p s) ≤ 1)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (hcert : ∀ j p, net.pk j p = PK.guard → cg j p = true → GStruct net j p ∧ GuardCntB x t0 j p)
    (hres : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPinB x t0 j p) :
    Link x t0 := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro htt j
    rcases Nat.eq_zero_or_pos t with ht0 | ht1
    · subst ht0
      rw [x.M_zero, ph_zero]
      by_cases hm : net.mg j = true
      · rw [x.mg0 j hm]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1.symm
      · rw [x.hc j 0, x.F_zero, x.r0]; simp [hm]
    · have hst : x.F j t < t := x.F_lt j t ht1
      have hs0 : x.F j t < t0 := by omega
      rw [x.hc j t, x.M_eq t j ht1]
      generalize x.F j t = s at hst hs0 ⊢
      have hcopy : ∀ p i, x.c (net.src j p) (x.G j p i s) = ph (net.v (net.src j p)) (x.cm j p s i) := by
        intro p i
        unfold Beh7.cm
        rcases Nat.eq_zero_or_pos s with hs0 | hs1
        · have : x.G j p i s = 0 := by have := (x.wG j p i).le_late s; omega
          rw [this]; exact ih 0 (by omega) (by omega) _
        · have := x.G_lt j p i s hs1
          exact ih _ (by omega) (by omega) _
      have hpv : ∀ p, net.pk j p ≠ PK.guard → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) :=
        fun p hk => pin_val_at x hOK j p s (fun i => hsel s hs0 j p i) (hline j p s hs0) hk (hcopy p)
      unfold Beh7.E
      by_cases hm : net.mg j = true
      · simp only [hm, ite_true]
        have hv0 := ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
        have e : (fun p => x.pin j p s) = (fun p => ph false (x.P j p s)) := by
          funext p
          obtain ⟨hvj, hng, hkg, _⟩ := (hOK j p).2.2.2.1 hm
          have := hpv p hkg
          rw [hng, Bool.xor_false, hvj] at this; exact this
        rw [e, fany_sum _ _ (hexcl j s hs0 hm), hv0]
      · have hm' : net.mg j = false := by simpa using hm
        simp only [hm, Bool.false_eq_true, ite_false]
        by_cases hr : x.r j s = true
        · simp [hr, ph_zero]
        · have hr' : x.r j s = false := by simpa using hr
          simp only [hr, ite_false, Bool.false_eq_true]
          have hs1 : 1 ≤ s := by
            rcases Nat.eq_zero_or_pos s with h | h
            · rw [h, x.r0] at hr'; exact absurd hr' (by decide)
            · exact h
          have hq : x.q j s = ph (net.v j) (x.M (x.Q j s) j) := by
            rw [x.hq j s]
            have := x.Q_lt j s hs1
            exact ih _ (by omega) (by omega) _
          rw [hq]
          refine cel_guards (net.v j) (net.ar j) (net.ar_pos j) (fun p => x.P j p s) _ _
            (fun p => decide (net.pk j p = PK.guard)) (net.gp j) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            have := ((hOK j p).2.2.2.2 (of_decide_eq_true hp)).2
            simpa using this
          · intro p hp
            exact hpv p (by simpa using hp)
          · intro p; exact x.q_le_P j hm' s hr' p
          · intro p
            by_cases hk : net.pk j p = PK.guard
            · cases hcg : cg j p
              · exact (hres j p hk hcg s hs0 hm' hr').1
              · exact ((hcert j p hk hcg).2 s hs0 hm' hr').1
            · exact hpinok j p s hs0 hm' hk
          · intro p hp hadv
            have hk : net.pk j p = PK.guard := of_decide_eq_true hp
            cases hcg : cg j p
            · exact (hres j p hk hcg s hs0 hm' hr').2 hadv
            · obtain ⟨hstr, hG⟩ := hcert j p hk hcg
              obtain ⟨_, hcont, hlab⟩ := hG s hs0 hm' hr'
              exact guard_val x j p s hstr (hgc j p s hk) hcont (hlab hadv) (hcopy p)

/-- **`safe8` is a corollary** of `safe8_upto` (its exact conclusion, from its exact
hypotheses). -/
theorem safe8_of_upto (hOK : net.OK7) (hsel : x.SelOK) (hline : x.LineOK) (hpinok : x.PinOK) (hexcl : x.ExclOK)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (hcert : ∀ j p, net.pk j p = PK.guard → cg j p = true → GStruct net j p ∧ GuardCnt x j p)
    (hres : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin x j p) :
    ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  intro t j
  exact safe8_upto x hOK t (fun s _ => (selOK_iff x).mp hsel s) (fun j p s _ => hline j p s)
    (fun j p s _ => hpinok j p s) (fun j s _ => hexcl j s) cg hgc
    (fun j p hk hc => ⟨(hcert j p hk hc).1, guardCntB_of x (hcert j p hk hc).2 t⟩)
    (fun j p hk hc => guardPinB_of x (hres j p hk hc) t) t (Nat.le_refl t) j

/-! ## 3. The certified verdict, prefix by prefix -/

/-- **`verdict9_upto`**: `Events9.verdict9` in prefix form. The certified items (Back, Excl,
Line, guard certificates against the sanitized hypothesis lines) are count facts at every
sample (they hold for every `Beh7`); SelOK and the residual obligations of the uncertified
items are assumed only at the samples `s < t0`; the conclusion is `Link x t0`. -/
theorem verdict9_upto (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {log : List Ln}
    {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (t0 : Nat)
    (rB : ∀ j p s, s < t0 → net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false →
      x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ m s, s < t0 → net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => x.P m p s) ≤ 1)
    (rL : ∀ j p s, s < t0 → net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (rG : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPinB x t0 j p)
    (hsel : ∀ s, s < t0 → SelAt x s) : Link x t0 := by
  have hA := runLog_sound x hOK hp hJ
  have hH := hdsub_san x hOK hp hA hl
  refine safe8_upto x hOK t0 hsel ?_ ?_ ?_ cg hgc ?_ rG
  · intro j p s hs hk
    cases hc : cl j p
    · exact rL j p s hs hk hc
    · exact lineOK7_sound x hA j p _ (hcl j p hc) s
  · intro j p s hs hm hk
    cases hc : cp j p
    · exact rB j p s hs hm hk hc
    · exact backOK7_sound x hOK hA j p hk _ (hcp j p hc) s
  · intro m s hs hm
    cases hc : cxm m
    · exact rX m s hs hm hc
    · exact exclOK7_sound x hOK hp hA m hm _ _ _ (hcx m hc) s
  · intro j p hk hc
    have h := guardOK8_sound x hOK hA hH j p (gd j p) (fun s => hgc j p s hk) (hcg j p hc)
    exact ⟨h.1, guardCntB_of x h.2 t0⟩

/-! ## 4. Causal closure -/

/-- **`causal_close`**: the induction that breaks the circularity. If the link holds on
`[0, t0]` whenever SelOK holds at the samples `< t0` (the prefix verdict), and SelOK at each
sample `s` follows from the link at all times `< s` (a causal derivation of SelOK), then the
link holds at all times, and so does SelOK. -/
theorem causal_close
    (hpre : ∀ t0, (∀ s, s < t0 → SelAt x s) → Link x t0)
    (hstep : ∀ s, (∀ u, u < s → ∀ j : Fin N, x.c j u = ph (net.v j) (x.M u j)) → SelAt x s) :
    x.SelOK ∧ ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  have key : ∀ s, SelAt x s := by
    intro s
    induction s using Nat.strongRecOn with
    | ind s ih =>
      apply hstep s
      intro u hu j
      exact hpre s ih u (by omega) j
  exact ⟨(selOK_iff x).mpr key, fun t j => hpre t (fun s _ => key s) t (Nat.le_refl t) j⟩

end P

/-! ## 5. The design verdict, prefix by prefix -/

section D
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9_upto`** (`design_verdict9` in prefix form). Same checks and trace
hypotheses as `design_verdict9` (SatPin, constants, reset, H_ARB). There is ONE realisation
`bh` (independent of `t0`), with the same three properties as before plus: for every `t0`,
if `sel` satisfies SelPart and `bh` satisfies SelOK at every sample `s < t0` and the residual
obligations of the uncertified items at every sample `s < t0`, then every node's count/wire
link holds on `[0, t0]` (`Link bh t0`) and in particular every real LUT wire is its reset
value flipped `M t j` times at every `t ≤ t0`. Lag `L = 0`. -/
theorem design_verdict9_upto (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hsat : SatPinW d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) ∧
      ∀ t0, SelPart sel parts → (∀ s, s < t0 → SelAt bh s) →
        (∀ j p s, s < t0 → net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false →
          bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, s < t0 → net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, s < t0 → net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPinB bh t0 j p) →
        Link bh t0 ∧ ∀ t, t ≤ t0 → ∀ j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j) := by
  obtain ⟨bh, hc, hgc, hreal⟩ := design_beh8 hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, hreal, fun t0 hp hsel rB rX rL rG => ?_⟩
  have hL := verdict9_upto bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) t0 rB rX rL rG hsel
  refine ⟨hL, fun t ht j hv => ?_⟩
  rw [← hreal j hv t]; exact hL t ht j

/-- **`design_verdict9` as a corollary of the prefix form** (statement identical to
`Events9.design_verdict9`). -/
theorem design_verdict9' (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hsat : SatPinW d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, _, H⟩ := design_verdict9_upto hr hOK hJ back line xS xw xa hl gd cp cxm cl cg
    hcp hcx hcl hcg hsat h0 h1 hT hrst harb sel
  refine ⟨bh, hc, hgc, fun hp hsel rB rX rL rG t j hv => ?_⟩
  exact (H t hp (fun s _ => (selOK_iff bh).mp hsel s) (fun j p s _ => rB j p s) (fun m s _ => rX m s)
    (fun j p s _ => rL j p s) (fun j p hk hc => guardPinB_of bh (rG j p hk hc) t)).2 t (Nat.le_refl t) j hv

end D

end Formal.Core.XAudit.Events9Prefix
