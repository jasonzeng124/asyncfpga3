import Formal.Core.XAudit.Events8Core

/-!
# Formal.Core.XAudit.Events8Cert — the guard checks (BACK-G, ENTRY, EXIT) and their soundness

Probe WE4g. See `formal/notes/A-events8.md`.

A guarded pin `p` of stage `j` (source `D`, guard pin `g = gp j p` with source `Gs`,
label `(grp, br)` of `p`, the guard's label source `S`) is certified by six log lines
of the Events7 derivation log (`GD`) and STRICT timing inequalities (`GuardOK8`):

* **BACK-G** `iB`: `filt (M u D) ≤ M (u − dB) j + tB`, `tB ≤ 1`, `hiQ j < loP j p + dB`;
* **LINE** `iX`: `LineOK7` for the copies (a closed walk of `D`, one token, `W = dX`);
* **ENTRY** `iU`, `iW`: `M u Gs ≤ filt (M (u − dU) S)` and `M u S ≤ M (u − dW) D + 1`,
  every copy `hiC j p i < loP j g + dU + dW`;
* **EXIT** `iX`, `iG`: `M u D ≤ M (u − W) D + 1` and `filt (M u D) ≤ M (u − dG) Gs`
  (no token), every pair of copies `hiC j p i' + hiF j + hiQ j < loC j p i + W` and
  `hiC j g + hiF j + hiQ j < loC j p i + W + dG`;
* structure: `GStruct`, `j` a stage with exactly the two pins `p` and `g`, `g` plain
  with offset 0.

**`guardOK8_sound`**: for a behaviour whose guarded count is `gcnt` (as `beh8`'s is),
an accepted log and `GuardOK8` give `GuardCnt` (bound, contiguity, label) for the pin.
**`verdict8`**: `verdict7` with GuardOK replaced by these checks; an uncertified
guarded pin carries its own GuardOK conjuncts (`GuardPin`).
-/

namespace Formal.Core.XAudit.Events8

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (fmin fmin_le le_fmin fmin_mem)
open Formal.Core.XAudit.Events3 (filt filt_mono filt_even)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7

/-- The log lines certifying one guarded pin, and the guard's label source `S`. -/
structure GD where
  S : Nat
  iB : Nat
  iU : Nat
  iW : Nat
  iX : Nat
  iG : Nat
  deriving Repr, Inhabited

/-- Line `i` of `J` (the default judgement out of range). -/
def jd (J : Array Jd) (i : Nat) : Jd := if h : i < J.size then J[i] else default

theorem jd_eq {J : Array Jd} {i : Nat} (h : i < J.size) : jd J i = J[i] := by unfold jd; rw [dif_pos h]

section
variable {N : Nat} (net : Net4 N) (b : Bands4 net)

/-- **The guard certificate** of guarded pin `p` of stage `j` (decidable; STRICT margins). -/
def GuardOK8 (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (g : GD) : Prop :=
  GStruct net j p ∧ net.mg j = false ∧ net.ar j = 2 ∧
  net.pk j (net.gp j p) = PK.plain ∧ net.off j (net.gp j p) = 0 ∧
  g.iB < J.size ∧ g.iU < J.size ∧ g.iW < J.size ∧ g.iG < J.size ∧
  -- BACK-G
  (jd J g.iB).u = false ∧ (jd J g.iB).a = (net.src j p).val ∧ (jd J g.iB).bb = j.val ∧
  (jd J g.iB).c = some (net.grp j p, net.br j p) ∧ (jd J g.iB).t ≤ 1 ∧ b.hiQ j < b.loP j p + (jd J g.iB).d ∧
  -- ENTRY
  (jd J g.iU).u = true ∧ (jd J g.iU).a = (net.src j (net.gp j p)).val ∧
  (jd J g.iU).c = some (net.grp j p, net.br j p) ∧ (jd J g.iU).bb = g.S ∧
  (jd J g.iW).u = false ∧ (jd J g.iW).c = none ∧ (jd J g.iW).a = g.S ∧ (jd J g.iW).bb = (net.src j p).val ∧
  (jd J g.iW).t ≤ 1 ∧
  (∀ i : Fin (net.nc j p), b.hiC j p i < b.loP j (net.gp j p) + (jd J g.iU).d + (jd J g.iW).d) ∧
  -- LINE and EXIT
  LineOK7 net b J j p g.iX ∧
  (jd J g.iG).u = false ∧ (jd J g.iG).c = some (net.grp j p, net.br j p) ∧ (jd J g.iG).a = (net.src j p).val ∧
  (jd J g.iG).bb = (net.src j (net.gp j p)).val ∧ (jd J g.iG).t = 0 ∧
  (∀ i i' : Fin (net.nc j p), b.hiC j p i' + b.hiF j + b.hiQ j < b.loC j p i + (jd J g.iX).d) ∧
  (∀ i : Fin (net.nc j p), ∀ i0 : Fin (net.nc j (net.gp j p)),
    b.hiC j (net.gp j p) i0 + b.hiF j + b.hiQ j < b.loC j p i + (jd J g.iX).d + (jd J g.iG).d)

set_option synthInstance.maxSize 2048 in
instance (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (g : GD) : Decidable (GuardOK8 net b J j p g) := by
  unfold GuardOK8; exact inferInstance

def guardOK8 (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (g : GD) : Bool := decide (GuardOK8 net b J j p g)

end

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

theorem allH_jd {J : Array Jd} (hJ : AllH x J) {i : Nat} (h : i < J.size) : Holds x (jd J i) := by
  rw [jd_eq h]; exact hJ i h

/-- **Soundness of the guard certificate.** -/
theorem guardOK8_sound (hOK : net.OK7) {J : Array Jd} (hJ : AllH x J) (j : Fin N) (p : Fin (net.ar j)) (g : GD)
    (hgc : ∀ s, x.gc j p s = gcnt net sel j p (x.cm j p s)) (h : guardOK8 net b J j p g = true) :
    GStruct net j p ∧ GuardCnt x j p := by
  obtain ⟨hst, hm, har, hgk, hgoff, hB, hU, hW, hG, bu, ba, bbb, bc, bt, bq, uu, ua, uc, ubb,
    wu, wc, wa, wbb, wt, hent, hline, gu, gcn, ga, gbb, gt, hex1, hex2⟩ := of_decide_eq_true h
  refine ⟨hst, ?_⟩
  obtain ⟨hpk, _, _, hoff⟩ := hst
  have hgg : net.pk j (net.gp j p) ≠ PK.guard := by rw [hgk]; decide
  -- the count of the guarded pin
  have hP : ∀ s, x.P j p s = gcnt net sel j p (x.cm j p s) := by
    intro s; unfold Beh7.P Beh7.pc; simp only [hpk]; rw [hoff, hgc]; rfl
  have hcmle : ∀ s i, x.cm j p s i ≤ x.M (s - b.loP j p) (net.src j p) := by
    intro s i; unfold Beh7.cm
    have := (x.wG j p i).le_late s
    have := fmin_le (net.nc j p) (b.loC j p) i
    exact x.M_mono _ _ _ (by unfold Bands4.loP; omega)
  -- the log facts
  obtain ⟨_, _, HB⟩ := holds_wc x (allH_jd x hJ hB) bu bc
  rw [ba, bbb] at HB
  obtain ⟨_, hSN, HU⟩ := holds_U x (allH_jd x hJ hU) uu uc
  rw [ua, ubb] at HU
  obtain ⟨_, _, HW⟩ := holds_w x (allH_jd x hJ hW) wu wc
  rw [wa, wbb] at HW
  obtain ⟨_, _, HG⟩ := holds_wc x (allH_jd x hJ hG) gu gcn
  rw [ga, gbb, gt] at HG
  have hline' : lineOK7 net b J j p g.iX = true := decide_eq_true hline
  obtain ⟨hXi, xu, xc, xa, xbb, xt, _⟩ := hline
  obtain ⟨_, _, HX⟩ := holds_w x (hJ g.iX hXi) xu xc
  rw [xa, xbb] at HX
  rw [jd_eq hXi] at hex1 hex2
  intro s hm' hr
  -- (1) BOUND
  have hbound : ∀ s, x.P j p s ≤ x.M (x.Q j s) j + 1 := by
    intro s
    have h0 := fmax_le _ _ (net.nc_pos j p) _ (hcmle s)
    have h1 := lineCnt_le (net.op j p) _ (x.cm j p s) (net.nc_pos j p)
    have h2 := filt_mono (sel (net.grp j p)) (net.br j p) (Nat.le_trans h1 h0)
    have h3 := HB (s - b.loP j p)
    rw [Mn_fin, Mn_fin] at h3
    have a4 := (x.wQ j).early_le s
    have hmq := x.M_mono (x.Q j s) j (s - b.loP j p - (jd J g.iB).d) (by omega)
    rw [hP s]; unfold gcnt; omega
  refine ⟨hbound s, lineOK7_sound x hJ j p g.iX hline' s, ?_⟩
  -- (3) LABEL
  intro hadv hodd
  generalize hL : lineCnt (net.op j p) (net.nc j p) (x.cm j p s) = L at hodd ⊢
  apply Classical.byContradiction
  intro hne
  obtain ⟨k, rfl⟩ : ∃ k, L = 2 * k + 1 := ⟨L / 2, by omega⟩
  rw [show (2 * k + 1) / 2 = k by omega] at hne
  have hsk := filt_skip (sel (net.grp j p)) (net.br j p) k hne
  have he := filt_even (sel (net.grp j p)) (net.br j p) k
  have hPs : x.P j p s = filt (sel (net.grp j p)) (net.br j p) (2 * k) := by
    rw [hP s]; unfold gcnt; rw [hL, hsk.1]
  have hlow := x.q_le_P j hm' s hr p
  have hup := hbound s
  rcases (show filt (sel (net.grp j p)) (net.br j p) (2 * k) = x.M (x.Q j s) j ∨
      filt (sel (net.grp j p)) (net.br j p) (2 * k) = x.M (x.Q j s) j + 1 by omega) with hA | hBc
  · -- ENTRY: the guard advanced into a later transaction of `S`, which needs `D` past `2k + 1`
    have hPg := x.P_le hOK j (net.gp j p) hgg s
    rw [hgoff] at hPg
    have h1 := HU (s - b.loP j (net.gp j p))
    rw [Mn_fin] at h1
    have hgap := filt_gap (sel (net.grp j p)) (net.br j p) k
      (Mn x (s - b.loP j (net.gp j p) - (jd J g.iU).d) g.S) hne (by omega)
    have h2 := HW (s - b.loP j (net.gp j p) - (jd J g.iU).d)
    rw [Mn_fin] at h2
    obtain ⟨i0, hi0⟩ := fmin_mem _ (x.cm j p s) (net.nc_pos j p)
    have hmin := lineCnt_ge (net.op j p) _ (x.cm j p s) (net.nc_pos j p)
    rw [hL] at hmin
    have hG0 := (x.wG j p i0).early_le s
    have hent0 := hent i0
    have hmono := x.M_mono (x.G j p i0 s) (net.src j p)
      (s - b.loP j (net.gp j p) - (jd J g.iU).d - (jd J g.iW).d) (by omega)
    have hc0 : x.cm j p s i0 = x.M (x.G j p i0 s) (net.src j p) := rfl
    omega
  · -- EXIT: the stage has already fired past the transaction the copies still see
    have hMq1 : 1 ≤ x.M (x.Q j s) j := by omega
    have hQ1 : 1 ≤ x.Q j s := by
      rcases Nat.eq_zero_or_pos (x.Q j s) with h0 | h0
      · rw [h0, x.M_zero] at hMq1; omega
      · exact h0
    have hEq := x.M_eq (x.Q j s) j hQ1
    have hs'Q := (x.wF j).early_le (x.Q j s)
    have hQs := (x.wQ j).early_le s
    generalize hs' : x.F j (x.Q j s) = s' at hEq hs'Q
    have hr' : x.r j s' = false := by
      cases hrr : x.r j s'
      · rfl
      · exfalso; unfold Beh7.E at hEq; simp only [hm', hrr] at hEq; simp at hEq; omega
    have hE : x.E j s' = fmin (net.ar j) (fun q => x.P j q s') := by
      unfold Beh7.E; simp [hm', hr']
    rw [hE] at hEq
    -- `D` had completed transaction k-1 at least W before copy i1 saw 2k+1
    obtain ⟨i1, hi1⟩ := fmax_mem _ (x.cm j p s) (net.nc_pos j p)
    have hmax := lineCnt_le (net.op j p) _ (x.cm j p s) (net.nc_pos j p)
    rw [hL] at hmax
    have hX1 := HX (x.G j p i1 s)
    rw [Mn_fin, Mn_fin] at hX1
    have hc1 : x.cm j p s i1 = x.M (x.G j p i1 s) (net.src j p) := rfl
    have hlate1 := (x.wG j p i1).le_late s
    have hD2k : 2 * k ≤ x.M (x.G j p i1 s - (J[g.iX]).d) (net.src j p) := by omega
    -- the guarded pin at s'
    have hp' : filt (sel (net.grp j p)) (net.br j p) (2 * k) ≤ x.P j p s' := by
      rw [hP s']; unfold gcnt
      apply filt_mono
      refine Nat.le_trans ?_ (lineCnt_ge _ _ _ (net.nc_pos j p))
      apply le_fmin _ _ (net.nc_pos j p)
      intro i'
      have he' := (x.wG j p i').early_le s'
      have ht := hex1 i1 i'
      exact Nat.le_trans hD2k (x.M_mono _ _ _ (by omega))
    -- the guard at s'
    have hnc1 : net.nc j (net.gp j p) = 1 := (hOK j (net.gp j p)).1 ⟨by rw [hgk]; decide, by rw [hgk]; decide⟩
    have hg' : filt (sel (net.grp j p)) (net.br j p) (2 * k) ≤ x.P j (net.gp j p) s' := by
      let i0 : Fin (net.nc j (net.gp j p)) := ⟨0, by omega⟩
      have hPg' : x.P j (net.gp j p) s' = x.M (x.G j (net.gp j p) i0 s') (net.src j (net.gp j p)) := by
        unfold Beh7.P Beh7.pc; simp only [hgk]; rw [hgoff, Beh4.fmax_one hnc1]; rfl
      rw [hPg']
      have h3 := HG (x.G j (net.gp j p) i0 s' + (jd J g.iG).d)
      rw [Nat.add_sub_cancel, Mn_fin, Mn_fin] at h3
      have he' := (x.wG j (net.gp j p) i0).early_le s'
      have ht := hex2 i1 i0
      have := filt_mono (sel (net.grp j p)) (net.br j p)
        (Nat.le_trans hD2k (x.M_mono (x.G j (net.gp j p) i0 s' + (jd J g.iG).d) (net.src j p) _ (by omega)))
      omega
    -- every pin of `j` (there are two) is past the feedback: contradiction
    have hpg : p ≠ net.gp j p := by intro he; rw [← he, hpk] at hgk; exact absurd hgk (by decide)
    have hall : ∀ q : Fin (net.ar j), filt (sel (net.grp j p)) (net.br j p) (2 * k) ≤ x.P j q s' := by
      intro q
      have hq := q.isLt
      have hpl := p.isLt
      have hgl := (net.gp j p).isLt
      have hpv : p.val ≠ (net.gp j p).val := fun h => hpg (Fin.ext h)
      rcases (show q.val = p.val ∨ q.val = (net.gp j p).val by omega) with h | h
      · rw [show q = p from Fin.ext h]; exact hp'
      · rw [show q = net.gp j p from Fin.ext h]; exact hg'
    have := le_fmin (net.ar j) (fun q => x.P j q s') (net.ar_pos j) _ hall
    omega

/-- **`verdict8`**: `verdict7` with GuardOK replaced by the guard certificates. The
stage pins, merges, line pins and guarded pins the checker certified (`cp`, `cxm`,
`cl`, `cg`) need nothing more; every other item carries its count-level obligation
(`rB`, `rX`, `rL`, and `rG`: GuardOK for that one guarded pin). Needs the guarded
count to be `gcnt` (`hgc`; `beh8` has it). -/
theorem verdict8 (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {log : List Ln} {J : Array Jd}
    (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b J j p (gd j p) = true)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (rB : ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => x.P m p s) ≤ 1)
    (rL : ∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (rG : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin x j p)
    (hsel : x.SelOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  have hA := runLog_sound x hOK hp hJ
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
    exact guardOK8_sound x hOK hA j p (gd j p) (fun s => hgc j p s hk) (hcg j p hc)

end

end Formal.Core.XAudit.Events8
