import Formal.Net.AO.UnrollTime

/-!
# The unrolled certificate, part 5: the remaining certificate-wide hypotheses for every word (shard C, all-pairs route)

**Problem, plainly.** `UnrollAsm` and `UnrollTime` reduce the local check and the timing tables of the long
certificate of a word of window kinds to checks on short sub-words. `Timed.timedA_follows` and `Timed.timedA_live`
also take hypotheses that quantify over the WHOLE certificate: the bounds are sound in every ideal of the full order
(`hLs : ∀ v, LSound CF (L v)`), every physical alternative has a full alternative up to separated causes (`hRT`),
`TmOK CF`, separation targets are exact (`hSE`), data nodes have no events (`hDataLen`), equal event counts
(`hlenEq`), and for liveness `hCPsub`, no empty cause list (`hne`) and a finite cover `U` (`hcov`). There are
infinitely many words, so each must follow from checks on single kinds or on two consecutive kinds.

**Design.** A kind `WKindF` is a `UnrollTime.WKindT` with a second cause list `fc` (the full order `CF`, e.g. with
real-time edges) beside its physical causes (`CP`), in the same window-relative coordinates. The certificates of a
word are `CPu` and `CFu`: the long certificates `UnrollTime.LC` of the physical and of the full causes, PADDED
(`padC`) with the cause list `[[]]` at every index at or beyond a node's event count. Padding is forced:
`timedA_live` asks `hne : ∀ u k, CF.causes u k ≠ []` and `hCPsub` at EVERY index `k`, and an unpadded `unroll` has
no causes beyond the last event, so it fails `hne` for every word. Below the event counts padding changes nothing:
`ideal_padC`, `enabled_padC`, `tmOK_padC`, `lsound_padC`, `sepOKA_padC`, `upOKA_padC`, `toa_padC`, and
`lcheckXA_padC` (for a reader on its own dependency set). Time stamps, separation and upper-bound tables, and the
bounds `L v = uL (wk (wP ks)) 0` (`UnrollAsm.uL`, one for all readers) are those of `UnrollTime`.

**Proved.**
* `uc_loc`, `uL_loc`, `usep_loc`: the long causes, bound and separation entry of an event of window `i` are its
  kind's, made absolute with base `off i`.
* `lstep_unroll`, `lsound_unroll`: `LStep` (hence, with `KindTm`, `LSound` by `Occ.lsound_of_step`) of the long
  certificate of every word, from `KindLStep pv w`, a check on the first kind (`pv = none`) and on each pair of
  consecutive kinds (`pv = some` predecessor): each relative bound is justified one step back by the node itself,
  by being at most 0 in the first window, by the previous event (in this window, or the last one of the node in the
  previous kind), or, in every alternative, by a cause in this window or at most one window back.
* `lsound_PF` (`hLs`), `rt_unroll` (`hRT`, with `Sep = UnrollTime.LSep`), `se_unroll` (`hSE`), `dataLen_unroll`
  (`hDataLen`), `lenEq_unroll` (`hlenEq`, by construction), `sub_unroll` (`hCPsub`), `ne_unroll` (`hne`),
  `cov_unroll` (`hcov`), `tmOK_PF` (`TmOK` of both), from per-kind checks `KindRT`, `KindSub`, `KindNe` and
  one-line per-kind facts; all collected in `side_unroll`.
* `timing_unroll_pad`: `UnrollTime.timing_unroll` for the padded certificates.
* `timedA_follows_unroll`, `timedA_live_unroll`: `timedA_follows` and `timedA_live` instantiated for the certificate
  of every word, with every certificate-wide hypothesis listed above replaced by these per-kind and sub-word checks.

**Not shown here.** That any instance (THE target's kinds) passes these checks. The remaining hypotheses of
`timedA_follows_unroll` / `timedA_live_unroll` stay as hypotheses: the behaviour `hb`, `hDE`, the local check
`hloc` (on the unpadded `LC`; reduced to window checks by `UnrollAsm.lcheckXA_unroll` with `UnrollTime.lcheckXA_uclT`,
not composed here), the environment and claim hypotheses `hEnvE`, `hgdF`, `hGC` (claim proofs, `ChainOK`), `hEnvC`,
`hInit`, `henv`, and the delay bounds `K`. `KindLStep` is only a sufficient condition: it justifies a bound across a
window boundary only through the previous kind (one window back). Moreover `uL` reads a relative bound with base
`off i` (a limitation of `UnrollAsm.uL`, not of this reduction): with finitely many kinds and a node `c` with events
in every kind, the bound of `u` on `c` grows without limit along long words, so it is sound only if `c`'s events
really precede `u`'s by a causal chain; this file does not check that THE target's bounds have this form. Bounds are one
function for all readers (as in `UnrollAsm`). That THE target's runs are unrolled certificates of a word (piece 3).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## Locating an event in its window -/

/-- Window `i + 1` starts `ks[i].len` events after window `i`. -/
theorem off_get (ks : List (WKindT α)) (i : Nat) (hi : i < ks.length) (u : α) :
    off (wt ks) (i + 1) u = off (wt ks) i u + ks[i].len u := by
  rw [off_wt_split ks i 1 u, List.drop_eq_getElem_cons hi, off_wt_succ, off_zero]; omega

/-- **The long causes of an event of window `i`** are its kind's causes made absolute with base `off i`. -/
theorem uc_loc (ks : List (WKindT α)) (i : Nat) (hi : i < ks.length) (u : α) (K : Nat)
    (h1 : off (wt ks) i u ≤ K) (h2 : K < off (wt ks) (i + 1) u) :
    uc (wt ks) (fun _ => 0) u K = (ks[i].causes u (K - off (wt ks) i u)).map (absAlt (off (wt ks) i)) := by
  have hs := uc_shift (wt ks) i (fun _ => 0) u (K - off (wt ks) i u)
  rw [Nat.sub_add_cancel h1, ← wt_drop, List.drop_eq_getElem_cons hi, wt_cons] at hs
  rw [hs]
  have hlt : K - off (wt ks) i u < ks[i].len u := by have := off_get ks i hi u; omega
  simp only [uc, hlt, ite_true, Nat.zero_add]

/-- **The long bound of an event of window `i`** is its kind's relative bound made absolute with base `off i`. -/
theorem uL_loc (ks : List (WKindT α)) (i : Nat) (hi : i < ks.length) (a : α) (K : Nat) (c : α)
    (h1 : off (wt ks) i a ≤ K) (h2 : K < off (wt ks) (i + 1) a) :
    uL (wk ks) (fun _ => 0) a K c = ((off (wt ks) i c : Int) + ks[i].Lr a (K - off (wt ks) i a) c).toNat := by
  have hs : uL (wk ks) (fun _ => 0) a (K - off (wt ks) i a + off (wt ks) i a) c =
      uL ((wk ks).drop i) (fun p => 0 + off (wt ks) i p) a (K - off (wt ks) i a) c :=
    uL_shift (wk ks) i (fun _ => 0) a (K - off (wt ks) i a) c
  rw [Nat.sub_add_cancel h1, ← wk_drop, List.drop_eq_getElem_cons hi] at hs
  rw [hs]
  have hlt : K - off (wt ks) i a < ks[i].len a := by have := off_get ks i hi a; omega
  simp only [wk, List.map_cons, uL, hlt, ite_true, Nat.zero_add]

/-- **The long separation table at an event of window `i`** is its kind's table, the source made relative. -/
theorem usep_loc (ks : List (WKindT α)) (i : Nat) (hi : i < ks.length) (b : α) (m : Int) (a : α) (K : Nat)
    (h1 : off (wt ks) i a ≤ K) (h2 : K < off (wt ks) (i + 1) a) :
    usep ks b m a K = ks[i].sep b (m - off (wt ks) i b) a (K - off (wt ks) i a) := by
  have hs := usep_shift ks i b (m - off (wt ks) i b) a (K - off (wt ks) i a)
  rw [Nat.sub_add_cancel h1, Int.sub_add_cancel, List.drop_eq_getElem_cons hi] at hs
  rw [hs]
  have hlt : K - off (wt ks) i a < ks[i].len a := by have := off_get ks i hi a; omega
  simp only [usep, hlt, ite_true]

/-- The previous kind, as the per-kind checks see it: `none` for the first window. -/
theorem prev_none {β : Type} {ks : List β} {i : Nat} (hi : i < ks.length)
    (h : (if i = 0 then none else ks[i - 1]?) = none) : i = 0 := by
  by_cases h0 : i = 0
  · exact h0
  · rw [ite_eq_right h0, List.getElem?_eq_getElem (by omega)] at h
    cases h

/-- A previous kind exists only after the first window, and it is the kind before. -/
theorem prev_some {β : Type} {ks : List β} {i : Nat} {p : β} (hi : i < ks.length)
    (h : (if i = 0 then none else ks[i - 1]?) = some p) : 0 < i ∧ ks[i - 1]'(by omega) = p := by
  by_cases h0 : i = 0
  · rw [ite_eq_left h0] at h; cases h
  · rw [ite_eq_right h0, List.getElem?_eq_getElem (by omega)] at h
    exact ⟨by omega, Option.some.inj h⟩

/-! ## `LSound` of the bounds -/

/-- Every cause of an alternative bounds `altBound` from below (its bound, and its own index plus one on its node). -/
theorem le_altBound {L : α → Nat → α → Nat} {w : α} : ∀ (alt : List (α × Nat)) (p : α × Nat), p ∈ alt →
    L p.1 p.2 w ≤ altBound L alt w ∧ (p.1 = w → p.2 + 1 ≤ altBound L alt w)
  | [], p, h => by simp at h
  | a :: t, p, h => by
    simp only [altBound, List.foldr]
    rcases List.mem_cons.mp h with rfl | h'
    · refine ⟨by omega, fun he => ?_⟩
      have : (if p.1 = w then p.2 + 1 else 0) = p.2 + 1 := ite_eq_left he
      omega
    · obtain ⟨i1, i2⟩ := le_altBound (L := L) (w := w) t p h'
      simp only [altBound] at i1 i2
      exact ⟨by omega, fun he => by have := i2 he; omega⟩

/-- **The per-kind bound check** for kind `w`, its previous kind `pv` (`none` in the first window): the relative
bound `Lr u k c` of each event is justified one step back, in relative coordinates, by one of: the node itself
(`u = c`); being at most 0 in the first window; the previous event in this window; the last event of `u` in the
previous kind (when this is `u`'s first event here and `u` has events there); or, in EVERY alternative of the
causes, some cause `q` that is on `c` itself, or in this window with a bound at least as large, or in the previous
window (relative index in `[-pv.len, 0)`) with a bound at least as large after the shift by `pv.len`. -/
def KindLStep (pv : Option (WKindT α)) (w : WKindT α) : Prop :=
  ∀ u k c, k < w.len u →
    (u = c ∧ w.Lr u k c ≤ k + 1) ∨
    (pv = none ∧ w.Lr u k c ≤ 0) ∨
    (0 < k ∧ w.Lr u k c ≤ w.Lr u (k - 1) c) ∨
    (k = 0 ∧ ∃ p, pv = some p ∧ 0 < p.len u ∧ w.Lr u 0 c + p.len c ≤ p.Lr u (p.len u - 1) c) ∨
    (∀ alt ∈ w.causes u k, ∃ q ∈ alt,
      (q.1 = c ∧ w.Lr u k c ≤ q.2 + 1) ∨
      (0 ≤ q.2 ∧ q.2 < w.len q.1 ∧ w.Lr u k c ≤ w.Lr q.1 q.2.toNat c) ∨
      (∃ p, pv = some p ∧ q.2 < 0 ∧ -(p.len q.1 : Int) ≤ q.2 ∧
        w.Lr u k c + p.len c ≤ p.Lr q.1 (q.2 + p.len q.1).toNat c))

/-- **`LStep` of the long certificate, for every word, from the per-kind bound checks** (each a check on the first
kind or on two consecutive kinds). -/
theorem lstep_unroll (BIG : Nat) (ks : List (WKindT α))
    (hL : ∀ i (hi : i < ks.length), KindLStep (if i = 0 then none else ks[i - 1]?) ks[i]) :
    LStep (LC BIG ks) (uL (wk ks) (fun _ => 0)) := by
  intro u K c hK
  have hK' : K < tot (wt ks) u := hK
  obtain ⟨i, hi, h1, h2⟩ := locate ks u K hK'
  have hLe := uL_loc ks i hi u K c h1 h2
  have hoi := off_get ks i hi u
  have hkl : K - off (wt ks) i u < ks[i].len u := by omega
  rcases hL i hi u _ c hkl with ⟨huc, hl⟩ | ⟨hpv, hl⟩ | ⟨hk0, hl⟩ | ⟨hk0, p, hp, hpl, hl⟩ | hc
  · left
    subst huc
    rw [ite_eq_left rfl, hLe]
    omega
  · left
    have := prev_none hi hpv
    subst this
    refine Nat.le_trans ?_ (Nat.zero_le _)
    rw [hLe, off_zero]
    omega
  · right; left
    refine ⟨by omega, ?_⟩
    rw [hLe, uL_loc ks i hi u (K - 1) c (by omega) (by omega)]
    have e : K - 1 - off (wt ks) i u = K - off (wt ks) i u - 1 := by omega
    rw [e]
    omega
  · right; left
    obtain ⟨hi0, hpe⟩ := prev_some hi hp
    subst hpe
    have hop := off_get ks (i - 1) (by omega) u
    have hoc := off_get ks (i - 1) (by omega) c
    rw [Nat.sub_add_cancel hi0] at hop hoc
    refine ⟨by omega, ?_⟩
    rw [hLe, uL_loc ks (i - 1) (by omega) u (K - 1) c (by omega) (by rw [Nat.sub_add_cancel hi0]; omega)]
    have e : K - 1 - off (wt ks) (i - 1) u = ks[i - 1].len u - 1 := by omega
    rw [e]
    have e2 : K - off (wt ks) i u = 0 := hk0
    rw [e2]
    omega
  · right; right
    intro alt halt
    have hc' : (LC BIG ks).causes u K = (ks[i].causes u (K - off (wt ks) i u)).map (absAlt (off (wt ks) i)) :=
      uc_loc ks i hi u K h1 h2
    rw [hc'] at halt
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp halt
    obtain ⟨q, hq, hcl⟩ := hc a0 ha0
    by_cases hkeep : 0 ≤ (off (wt ks) i q.1 : Int) + q.2
    · have hpm : (q.1, ((off (wt ks) i q.1 : Int) + q.2).toNat) ∈ absAlt (off (wt ks) i) a0 :=
        mem_absAlt.mpr ⟨q, hq, hkeep, rfl⟩
      have hab := le_altBound (L := uL (wk ks) (fun _ => 0)) (w := c) _ _ hpm
      simp only at hab
      rw [hLe]
      rcases hcl with ⟨hqc, hl⟩ | ⟨hq0, hql, hl⟩ | ⟨p, hp, hq0, hqp, hl⟩
      · have := hab.2 hqc
        rw [hqc] at this
        omega
      · have hoq := off_get ks i hi q.1
        have := uL_loc ks i hi q.1 (((off (wt ks) i q.1 : Int) + q.2).toNat) c (by omega) (by omega)
        have e : ((off (wt ks) i q.1 : Int) + q.2).toNat - off (wt ks) i q.1 = q.2.toNat := by omega
        rw [e] at this
        have := hab.1
        omega
      · obtain ⟨hi0, hpe⟩ := prev_some hi hp
        subst hpe
        have hoq := off_get ks (i - 1) (by omega) q.1
        have hoc := off_get ks (i - 1) (by omega) c
        rw [Nat.sub_add_cancel hi0] at hoq hoc
        have := uL_loc ks (i - 1) (by omega) q.1 (((off (wt ks) i q.1 : Int) + q.2).toNat) c (by omega)
          (by rw [Nat.sub_add_cancel hi0]; omega)
        have e : ((off (wt ks) i q.1 : Int) + q.2).toNat - off (wt ks) (i - 1) q.1 =
            (q.2 + (ks[i - 1].len q.1 : Int)).toNat := by omega
        rw [e] at this
        have := hab.1
        omega
    · -- the cause is dropped (before the word): then the bound is 0
      refine Nat.le_trans ?_ (Nat.zero_le _)
      rw [hLe]
      rcases hcl with ⟨hqc, hl⟩ | ⟨hq0, hql, hl⟩ | ⟨p, hp, hq0, hqp, hl⟩
      · rw [hqc] at hkeep
        omega
      · omega
      · obtain ⟨hi0, hpe⟩ := prev_some hi hp
        subst hpe
        have hoq := off_get ks (i - 1) (by omega) q.1
        rw [Nat.sub_add_cancel hi0] at hoq
        omega

/-- **`LSound` of the long bounds `uL`, for every word**, from the per-kind time-stamp checks (`KindTm`) and the
per-kind bound checks (`KindLStep`). -/
theorem lsound_unroll (BIG : Nat) (ks : List (WKindT α)) (hK : ∀ w ∈ ks, KindTm BIG w)
    (hL : ∀ i (hi : i < ks.length), KindLStep (if i = 0 then none else ks[i - 1]?) ks[i]) :
    LSound (LC BIG ks) (uL (wk ks) (fun _ => 0)) :=
  lsound_of_step (tmOK_unroll BIG ks hK) (lstep_unroll BIG ks hL)

/-! ## Padding: a cause list beyond each node's last event -/

/-- The certificate `C` with the cause list `[[]]` (one empty alternative) at every index at or beyond a node's
event count. Below the counts nothing changes, so ideals, enabledness and every timing table are unaffected
(`ideal_padC`, `enabled_padC`, ...); `Timed.timedA_live` demands `hne` and `hCPsub` at EVERY index, which an
unpadded `unroll` (no causes beyond the last event) cannot meet. -/
def padC (C : Cert α) : Cert α :=
  { len := C.len, causes := fun u k => if k < C.len u then C.causes u k else [[]], tm := C.tm }

/-- Below the event count, padding keeps the causes. -/
theorem padC_causes {C : Cert α} {u : α} {k : Nat} (hk : k < C.len u) : (padC C).causes u k = C.causes u k :=
  ite_eq_left hk

/-- At or beyond the event count, the padded cause list is `[[]]`. -/
theorem padC_causes_ge {C : Cert α} {u : α} {k : Nat} (hk : ¬ k < C.len u) : (padC C).causes u k = [[]] :=
  ite_eq_right hk

/-- Padding does not change ideals. -/
theorem ideal_padC {C : Cert α} {c : α → Nat} : Ideal (padC C) c ↔ Ideal C c := by
  constructor
  · intro h u
    refine ⟨(h u).1, fun k hk => ?_⟩
    obtain ⟨alt, ha, hin⟩ := (h u).2 k hk
    rw [padC_causes (C := C) (Nat.lt_of_lt_of_le hk (h u).1)] at ha
    exact ⟨alt, ha, hin⟩
  · intro h u
    refine ⟨(h u).1, fun k hk => ?_⟩
    obtain ⟨alt, ha, hin⟩ := (h u).2 k hk
    refine ⟨alt, ?_, hin⟩
    rw [padC_causes (C := C) (Nat.lt_of_lt_of_le hk (h u).1)]
    exact ha

/-- Padding does not change enabledness. -/
theorem enabled_padC {C : Cert α} {c : α → Nat} {v : α} : Enabled (padC C) c v ↔ Enabled C c v := by
  constructor
  · rintro ⟨h1, alt, ha, hin⟩
    rw [padC_causes (C := C) h1] at ha
    exact ⟨h1, alt, ha, hin⟩
  · rintro ⟨h1, alt, ha, hin⟩
    refine ⟨h1, alt, ?_, hin⟩
    rw [padC_causes (C := C) h1]
    exact ha

/-- Padding keeps valid time stamps. -/
theorem tmOK_padC {C : Cert α} (h : TmOK C) : TmOK (padC C) :=
  ⟨h.1, fun u k hk alt ha p hp => h.2 u k hk alt (by rw [padC_causes (C := C) hk] at ha; exact ha) p hp⟩

/-- Padding keeps sound bounds. -/
theorem lsound_padC {C : Cert α} {L : α → Nat → α → Nat} (h : LSound C L) : LSound (padC C) L :=
  fun c hc => h c (ideal_padC.1 hc)

section pad
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α}
  {L : α → Nat → α → Nat} {D : α → List α} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Sep : α → Nat → α → Nat → Option Nat} {Up : α × Nat → α × Nat → Option Nat}

/-- Padding keeps a justified separation table. -/
theorem sepOKA_padC (h : SepOKA N C Sep Up) : SepOKA N (padC C) Sep Up := by
  intro b m a k d hk hd
  rw [padC_causes (C := C) hk]
  exact h b m a k d hk hd

/-- Padding keeps a justified upper-bound table. -/
theorem upOKA_padC (h : UpOKA N dat C Sep Up) : UpOKA N dat (padC C) Sep Up := by
  intro e0 e d hd
  rcases h e0 e d hd with h1 | ⟨hg, hdat, hl, halt, hprev⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hg, hdat, hl, ?_, hprev⟩
    rw [padC_causes (C := C) hl]
    exact halt

/-- Padding the physical certificate keeps the skew rows, when the event counts agree. -/
theorem toa_padC {CF : Cert α} {LL : α → α → Nat → α → Nat} (h : TOA N CF C LL D Sep)
    (hl : ∀ u, CF.len u = C.len u) : TOA N CF (padC C) LL D Sep := by
  intro v a b k ha hb hab hk hL hlh
  rcases h v a b k ha hb hab hk hL hlh with h1 | ⟨hav, k', hk', hc⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hav, k', hk', ?_⟩
    subst hav
    rw [padC_causes (C := C) (by rw [← hl]; omega)]
    exact hc

/-- The local check carries over to the padded certificate when the reader is on its own dependency set (as
`UnrollAsm.lcheckXA_unroll` assumes). -/
theorem lcheckXA_padC {v : α} (hv : v ∈ D v) (h : LCheckXA N dat envEn s0 C L D cl gd v) :
    LCheckXA N dat envEn s0 (padC C) L D cl gd v := by
  intro n hn hL hown bb hbb
  have hown' : ∀ k, k < n v → ∃ alt ∈ C.causes v k, AltIn n alt := by
    intro k hk
    obtain ⟨alt, ha, hin⟩ := hown k hk
    rw [padC_causes (C := C) (Nat.lt_of_lt_of_le hk (hn v hv))] at ha
    exact ⟨alt, ha, hin⟩
  rw [h n hn hL hown' bb hbb]
  exact enabled_padC.symm

end pad

/-! ## Kinds with a full (RT) cause list -/

/-- A window kind with, besides its physical causes `causes` (those of `CP`), the causes `fc` of the FULL order
(those of `CF`, e.g. with real-time edges), in the same window-relative coordinates. -/
structure WKindF (α : Type) extends WKindT α where
  fc : α → Nat → List (List (α × Int))

/-- The kind with its full causes as its causes. -/
def WKindF.full (w : WKindF α) : WKindT α := { w.toWKindT with causes := w.fc }

/-- The word with physical causes. -/
def wP (ks : List (WKindF α)) : List (WKindT α) := ks.map WKindF.toWKindT

/-- The word with full causes. -/
def wF (ks : List (WKindF α)) : List (WKindT α) := ks.map WKindF.full

/-- **The certificate `CP`** of a word: the long certificate of its physical causes, padded. -/
def CPu (BIG : Nat) (ks : List (WKindF α)) : Cert α := padC (LC BIG (wP ks))

/-- **The certificate `CF`** of a word: the long certificate of its full causes, padded. -/
def CFu (BIG : Nat) (ks : List (WKindF α)) : Cert α := padC (LC BIG (wF ks))

/-- The full and the physical word have the same event counts. -/
theorem tot_FP : ∀ (ks : List (WKindF α)) (u : α), tot (wt (wF ks)) u = tot (wt (wP ks)) u
  | [], _ => rfl
  | w :: ks, u => by
    show w.full.len u + tot (wt (wF ks)) u = w.len u + tot (wt (wP ks)) u
    rw [tot_FP ks u]; rfl

/-- The full and the physical word have the same window offsets. -/
theorem off_FP (ks : List (WKindF α)) (j : Nat) : off (wt (wF ks)) j = off (wt (wP ks)) j := by
  funext u
  rw [off_eq_tot_take, off_eq_tot_take, ← wt_take, ← wt_take]
  have e1 : (wF ks).take j = wF (ks.take j) := by simp [wF, List.map_take]
  have e2 : (wP ks).take j = wP (ks.take j) := by simp [wP, List.map_take]
  rw [e1, e2, tot_FP]

/-- The full and the physical word have the same bounds `uL`. -/
theorem uL_FP : ∀ (ks : List (WKindF α)) (B : α → Nat) (a : α) (k : Nat) (c : α),
    uL (wk (wF ks)) B a k c = uL (wk (wP ks)) B a k c
  | [], _, _, _, _ => rfl
  | w :: ks, B, a, k, c => by
    show (if k < w.len a then ((B c : Int) + w.Lr a k c).toNat
        else uL (wk (wF ks)) (fun p => B p + w.len p) a (k - w.len a) c) =
      (if k < w.len a then ((B c : Int) + w.Lr a k c).toNat
        else uL (wk (wP ks)) (fun p => B p + w.len p) a (k - w.len a) c)
    rw [uL_FP ks]

/-- One physical kind per kind. -/
theorem len_wP (ks : List (WKindF α)) : (wP ks).length = ks.length := by simp [wP]

/-- One full kind per kind. -/
theorem len_wF (ks : List (WKindF α)) : (wF ks).length = ks.length := by simp [wF]

/-- The `i`-th physical kind. -/
theorem get_wP (ks : List (WKindF α)) (i : Nat) (hi : i < (wP ks).length) :
    (wP ks)[i] = (ks[i]'(by rw [len_wP] at hi; exact hi)).toWKindT := by simp [wP]

/-- The `i`-th full kind. -/
theorem get_wF (ks : List (WKindF α)) (i : Nat) (hi : i < (wF ks).length) :
    (wF ks)[i] = (ks[i]'(by rw [len_wF] at hi; exact hi)).full := by simp [wF]

/-- `CP`'s causes of an event of window `i`. -/
theorem CP_loc (BIG : Nat) (ks : List (WKindF α)) (i : Nat) (hi : i < ks.length) (u : α) (K : Nat)
    (h1 : off (wt (wP ks)) i u ≤ K) (h2 : K < off (wt (wP ks)) (i + 1) u) :
    (CPu BIG ks).causes u K = (ks[i].causes u (K - off (wt (wP ks)) i u)).map (absAlt (off (wt (wP ks)) i)) := by
  have hi' : i < (wP ks).length := by rw [len_wP]; exact hi
  have hK : K < (LC BIG (wP ks)).len u := by
    have := off_le_tot (wt (wP ks)) (i + 1) u
    show K < tot (wt (wP ks)) u
    omega
  rw [CPu, padC_causes hK]
  have := uc_loc (wP ks) i hi' u K h1 h2
  rw [get_wP ks i hi'] at this
  exact this

/-- `CF`'s causes of an event of window `i`. -/
theorem CF_loc (BIG : Nat) (ks : List (WKindF α)) (i : Nat) (hi : i < ks.length) (u : α) (K : Nat)
    (h1 : off (wt (wP ks)) i u ≤ K) (h2 : K < off (wt (wP ks)) (i + 1) u) :
    (CFu BIG ks).causes u K = (ks[i].fc u (K - off (wt (wP ks)) i u)).map (absAlt (off (wt (wP ks)) i)) := by
  have hi' : i < (wF ks).length := by rw [len_wF]; exact hi
  have hK : K < (LC BIG (wF ks)).len u := by
    have := off_le_tot (wt (wP ks)) (i + 1) u
    show K < tot (wt (wF ks)) u
    rw [tot_FP]
    omega
  rw [CFu, padC_causes hK]
  have := uc_loc (wF ks) i hi' u K (by rw [off_FP]; exact h1) (by rw [off_FP]; exact h2)
  rw [get_wF ks i hi', off_FP] at this
  exact this

/-! ## The per-kind side conditions -/

/-- **Per-kind `hRT`**: for every physical alternative of an event, some full alternative whose every cause is
in the physical one or separated from the event by at least 1 in this kind's separation table. -/
def KindRT (w : WKindF α) : Prop :=
  ∀ u k, k < w.len u → ∀ aP ∈ w.causes u k, ∃ aF ∈ w.fc u k, ∀ q ∈ aF,
    q ∈ aP ∨ ∃ d, w.sep q.1 q.2 u k = some d ∧ 1 ≤ d

/-- **Per-kind `hCPsub`**: every full alternative contains some physical alternative. -/
def KindSub (w : WKindF α) : Prop :=
  ∀ u k, k < w.len u → ∀ aF ∈ w.fc u k, ∃ aP ∈ w.causes u k, ∀ q ∈ aP, q ∈ aF

/-- **Per-kind `hne`**: no event of the kind has an empty full cause list. -/
def KindNe (w : WKindF α) : Prop := ∀ u k, k < w.len u → w.fc u k ≠ []

/-- Making alternatives absolute preserves inclusion. -/
theorem absAlt_mono {o : α → Nat} {a b : List (α × Int)} (h : ∀ q ∈ a, q ∈ b) :
    ∀ p ∈ absAlt o a, p ∈ absAlt o b := by
  intro p hp
  obtain ⟨q, hq, h0, rfl⟩ := mem_absAlt.mp hp
  exact mem_absAlt.mpr ⟨q, h q hq, h0, rfl⟩

/-- **`hRT` of `timedA_follows` for every word**, from `KindRT` of each kind, with `Sep = LSep (wP ks)` (the
separation table of `UnrollTime`). -/
theorem rt_unroll (BIG : Nat) (ks : List (WKindF α)) (h : ∀ w ∈ ks, KindRT w) :
    ∀ u k, k < (CFu BIG ks).len u → ∀ altP ∈ (CPu BIG ks).causes u k, ∃ altF ∈ (CFu BIG ks).causes u k,
      ∀ p ∈ altF, p ∈ altP ∨ ∃ d, LSep (wP ks) p.1 p.2 u k = some d ∧ 1 ≤ d := by
  intro u K hK altP haP
  have hK' : K < tot (wt (wP ks)) u := by rw [← tot_FP]; exact hK
  obtain ⟨i, hi, h1, h2⟩ := locate (wP ks) u K hK'
  rw [len_wP] at hi
  rw [CP_loc BIG ks i hi u K h1 h2] at haP
  rw [CF_loc BIG ks i hi u K h1 h2]
  obtain ⟨aP, haP0, rfl⟩ := List.mem_map.mp haP
  have hoi := off_get (wP ks) i (by rw [len_wP]; exact hi) u
  rw [get_wP] at hoi
  obtain ⟨aF, haF, hcl⟩ := h ks[i] (List.getElem_mem hi) u _ (by omega) aP haP0
  refine ⟨absAlt (off (wt (wP ks)) i) aF, List.mem_map.mpr ⟨aF, haF, rfl⟩, fun p hp => ?_⟩
  obtain ⟨q, hq, h0, rfl⟩ := mem_absAlt.mp hp
  rcases hcl q hq with hm | ⟨d, hd, hd1⟩
  · exact Or.inl (mem_absAlt.mpr ⟨q, hm, h0, rfl⟩)
  · refine Or.inr ⟨d, ?_, hd1⟩
    show usep (wP ks) q.1 (((off (wt (wP ks)) i q.1 : Int) + q.2).toNat : Int) u K = some d
    rw [usep_loc (wP ks) i (by rw [len_wP]; exact hi) _ _ u K h1 h2, get_wP]
    have e : ((((off (wt (wP ks)) i q.1 : Int) + q.2).toNat : Nat) : Int) - (off (wt (wP ks)) i q.1 : Int) = q.2 := by
      omega
    rw [e]
    exact hd

/-- **`hCPsub` of `timedA_live` for every word**, from `KindSub` of each kind (beyond the last event both padded
lists are `[[]]`). -/
theorem sub_unroll (BIG : Nat) (ks : List (WKindF α)) (h : ∀ w ∈ ks, KindSub w) :
    ∀ u k, ∀ altF ∈ (CFu BIG ks).causes u k, ∃ altP ∈ (CPu BIG ks).causes u k, ∀ p ∈ altP, p ∈ altF := by
  intro u K altF haF
  by_cases hK : K < tot (wt (wP ks)) u
  · obtain ⟨i, hi, h1, h2⟩ := locate (wP ks) u K hK
    rw [len_wP] at hi
    rw [CF_loc BIG ks i hi u K h1 h2] at haF
    rw [CP_loc BIG ks i hi u K h1 h2]
    obtain ⟨aF, haF0, rfl⟩ := List.mem_map.mp haF
    have hoi := off_get (wP ks) i (by rw [len_wP]; exact hi) u
    rw [get_wP] at hoi
    obtain ⟨aP, haP, hsub⟩ := h ks[i] (List.getElem_mem hi) u _ (by omega) aF haF0
    exact ⟨_, List.mem_map.mpr ⟨aP, haP, rfl⟩, absAlt_mono hsub⟩
  · have hKF : ¬ K < (LC BIG (wF ks)).len u := by
      show ¬ K < tot (wt (wF ks)) u
      rw [tot_FP]; exact hK
    have hKP : ¬ K < (LC BIG (wP ks)).len u := hK
    rw [CFu, padC_causes_ge hKF] at haF
    rw [CPu, padC_causes_ge hKP]
    simp only [List.mem_singleton] at haF
    subst haF
    exact ⟨[], List.mem_singleton.mpr rfl, fun p hp => by simp at hp⟩

/-- **`hne` of `timedA_live` for every word**, from `KindNe` of each kind. -/
theorem ne_unroll (BIG : Nat) (ks : List (WKindF α)) (h : ∀ w ∈ ks, KindNe w) :
    ∀ u k, (CFu BIG ks).causes u k ≠ [] := by
  intro u K
  by_cases hK : K < tot (wt (wP ks)) u
  · obtain ⟨i, hi, h1, h2⟩ := locate (wP ks) u K hK
    rw [len_wP] at hi
    rw [CF_loc BIG ks i hi u K h1 h2]
    have hoi := off_get (wP ks) i (by rw [len_wP]; exact hi) u
    rw [get_wP] at hoi
    intro he
    exact h ks[i] (List.getElem_mem hi) u _ (by omega) (List.map_eq_nil_iff.mp he)
  · have hKF : ¬ K < (LC BIG (wF ks)).len u := by
      show ¬ K < tot (wt (wF ks)) u
      rw [tot_FP]; exact hK
    rw [CFu, padC_causes_ge hKF]
    simp

/-- A node with an event in the word has one in some kind. -/
theorem tot_pos_mem : ∀ (ks : List (WKindT α)) (u : α), 0 < tot (wt ks) u → ∃ w ∈ ks, 0 < w.len u
  | [], _, h => by simp [wt, wcs, wk, tot] at h
  | w :: ks, u, h => by
    rw [tot_wt_cons] at h
    by_cases hw : 0 < w.len u
    · exact ⟨w, by simp, hw⟩
    · obtain ⟨w', hw', h'⟩ := tot_pos_mem ks u (by omega)
      exact ⟨w', by simp [hw'], h'⟩

/-- **`hcov` of `timedA_live` for every word**: every node with an event in some kind is in `U`. -/
theorem cov_unroll (BIG : Nat) (ks : List (WKindF α)) (U : List α) (h : ∀ w ∈ ks, ∀ u, 0 < w.len u → u ∈ U) :
    ∀ u, 0 < (CFu BIG ks).len u → u ∈ U := by
  intro u hu
  have hu' : 0 < tot (wt (wP ks)) u := by rw [← tot_FP]; exact hu
  obtain ⟨w, hw, hpos⟩ := tot_pos_mem (wP ks) u hu'
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
  exact h w0 hw0 u hpos

/-- **`hlenEq`** holds by construction: both certificates have the word's event counts. -/
theorem lenEq_unroll (BIG : Nat) (ks : List (WKindF α)) : ∀ u, (CPu BIG ks).len u = (CFu BIG ks).len u :=
  fun u => (tot_FP ks u).symm

/-- Every entry of the long separation table is an entry of some kind's table. -/
theorem usep_mem : ∀ (ks : List (WKindT α)) (b : α) (m : Int) (a : α) (k d : Nat), usep ks b m a k = some d →
    ∃ w ∈ ks, ∃ m' k', w.sep b m' a k' = some d
  | [], _, _, _, _, _, h => by simp [usep] at h
  | w :: ks, b, m, a, k, d, h => by
    simp only [usep] at h
    split at h
    · exact ⟨w, by simp, _, _, h⟩
    · obtain ⟨w', hw', m', k', h'⟩ := usep_mem ks _ _ _ _ _ h
      exact ⟨w', by simp [hw'], m', k', h'⟩

/-- **`hSE` of `timedA_follows` for every word**: every separation entry of every kind targets an exact node. -/
theorem se_unroll (ks : List (WKindF α)) (dat : α → Bool)
    (h : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false) :
    ∀ b m a k d, LSep (wP ks) b m a k = some d → dat a = false := by
  intro b m a k d hd
  obtain ⟨w, hw, m', k', h'⟩ := usep_mem (wP ks) b m a k d hd
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
  exact h w0 hw0 b m' a k' d h'

/-- A node with no event in any kind has no event in the word. -/
theorem tot_zero : ∀ (ks : List (WKindT α)) (u : α), (∀ w ∈ ks, w.len u = 0) → tot (wt ks) u = 0
  | [], _, _ => rfl
  | w :: ks, u, h => by
    rw [tot_wt_cons, h w (by simp), tot_zero ks u (fun w' hw' => h w' (by simp [hw']))]

/-- **`hDataLen` of `timedA_follows` for every word**: no kind has an event of a data node. -/
theorem dataLen_unroll (BIG : Nat) (ks : List (WKindF α)) (dat : α → Bool)
    (h : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0) : ∀ u, dat u = true → (CFu BIG ks).len u = 0 := by
  intro u hu
  show tot (wt (wF ks)) u = 0
  rw [tot_FP]
  exact tot_zero (wP ks) u (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact h w0 hw0 u hu)

/-- **`TmOK` of both certificates**, from the per-kind time-stamp checks of the physical and the full causes. -/
theorem tmOK_PF (BIG : Nat) (ks : List (WKindF α)) (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT)
    (hKF : ∀ w ∈ ks, KindTm BIG w.full) : TmOK (CPu BIG ks) ∧ TmOK (CFu BIG ks) :=
  ⟨tmOK_padC (tmOK_unroll BIG (wP ks) (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKP w0 hw0)),
    tmOK_padC (tmOK_unroll BIG (wF ks) (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKF w0 hw0))⟩

/-- **`hLs` of `timedA_follows` for every word**: the bounds `uL` (the same for every reader) are sound for the full
order `CF`, from the per-kind time-stamp checks of the full causes and the per-kind bound checks `KindLStep` on the
full causes (first kind against `none`, every other against its predecessor). -/
theorem lsound_PF (BIG : Nat) (ks : List (WKindF α)) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i]) :
    ∀ _v : α, LSound (CFu BIG ks) (uL (wk (wP ks)) (fun _ => 0)) := by
  intro _
  have h := lsound_unroll BIG (wF ks)
    (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKF w0 hw0) hL
  have e : uL (wk (wF ks)) (fun _ => 0) = uL (wk (wP ks)) (fun _ => 0) := by
    funext a k c; exact uL_FP ks _ a k c
  rw [e] at h
  exact lsound_padC h

/-! ## Everything together -/

/-- **The timing hypotheses of `timing_unroll`, for the padded certificates** `CPu`, `CFu`. -/
theorem timing_unroll_pad (N : TNet α) (dat : α → Bool) (D : α → List α) (BIG r : Nat) (hr : 2 ≤ r)
    (ks : List (WKindF α)) (hK : ∀ w ∈ wP ks, KindTm BIG w) (Dc : α → List α)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r) (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r) (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r) (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r) (i - (i - 1))) :
    TmOK (CPu BIG ks) ∧ SepOKA N (CPu BIG ks) (LSep (wP ks)) (LUp (wP ks)) ∧
      UpOKA N dat (CPu BIG ks) (LSep (wP ks)) (LUp (wP ks)) ∧
      TOA N (CFu BIG ks) (CPu BIG ks) (fun _ => uL (wk (wP ks)) (fun _ => 0)) D (LSep (wP ks)) ∧
      (∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ ugd v z (wk (wP ks)) (fun _ => 0) 0,
        ∃ c, (uclT (wk (wP ks)) (fun _ => 0))[g.ci]? = some c ∧ c.z = z ∧ GuardTime N (LSep (wP ks)) v z c g) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := timing_unroll N dat D BIG r hr (wP ks) (CFu BIG ks) (fun u => tot_FP ks u) hK Dc hcD
    hBC hS hU hT hG
  exact ⟨tmOK_padC h1, sepOKA_padC h2, upOKA_padC h3, toa_padC h4 (fun u => tot_FP ks u), h5⟩

/-- **The whole-certificate side conditions of `timedA_follows` / `timedA_live`, for every word, from per-kind
checks**: `TmOK` of both certificates, `hLs` (bounds `uL`, one for all readers), `hRT`, `hSE`, `hDataLen`,
`hlenEq`, `hCPsub`, `hne`, `hcov`. -/
theorem side_unroll (BIG : Nat) (ks : List (WKindF α)) (dat : α → Bool) (U : List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRT : ∀ w ∈ ks, KindRT w) (hSub : ∀ w ∈ ks, KindSub w) (hNe : ∀ w ∈ ks, KindNe w)
    (hSE : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDL : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0) (hCov : ∀ w ∈ ks, ∀ u, 0 < w.len u → u ∈ U) :
    TmOK (CPu BIG ks) ∧ TmOK (CFu BIG ks) ∧
    (∀ _v : α, LSound (CFu BIG ks) (uL (wk (wP ks)) (fun _ => 0))) ∧
    (∀ u k, k < (CFu BIG ks).len u → ∀ altP ∈ (CPu BIG ks).causes u k, ∃ altF ∈ (CFu BIG ks).causes u k,
      ∀ p ∈ altF, p ∈ altP ∨ ∃ d, LSep (wP ks) p.1 p.2 u k = some d ∧ 1 ≤ d) ∧
    (∀ b m a k d, LSep (wP ks) b m a k = some d → dat a = false) ∧
    (∀ u, dat u = true → (CFu BIG ks).len u = 0) ∧
    (∀ u, (CPu BIG ks).len u = (CFu BIG ks).len u) ∧
    (∀ u k, ∀ altF ∈ (CFu BIG ks).causes u k, ∃ altP ∈ (CPu BIG ks).causes u k, ∀ p ∈ altP, p ∈ altF) ∧
    (∀ u k, (CFu BIG ks).causes u k ≠ []) ∧
    (∀ u, 0 < (CFu BIG ks).len u → u ∈ U) :=
  ⟨(tmOK_PF BIG ks hKP hKF).1, (tmOK_PF BIG ks hKP hKF).2, lsound_PF BIG ks hKF hL, rt_unroll BIG ks hRT,
    se_unroll ks dat hSE, dataLen_unroll BIG ks dat hDL, lenEq_unroll BIG ks, sub_unroll BIG ks hSub,
    ne_unroll BIG ks hNe, cov_unroll BIG ks U hCov⟩

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {D : α → List α}

/-- **`timedA_follows` for the certificate of every word**, its certificate-wide hypotheses replaced by per-kind
checks (`side_unroll`, `timing_unroll_pad`) and window local checks on the unpadded certificate. What remains
are the behaviour `hb`, the dependency sets `hDE`, the local checks `hloc` (reduced to window checks by
`UnrollAsm.lcheckXA_unroll` and `UnrollTime.lcheckXA_uclT`), and the environment and claim hypotheses `hEnvE`,
`hgdF`, `hGC`, `hEnvC`, `hInit`, stated here on the padded certificates (`ideal_padC`, `enabled_padC` move them
to the unpadded ones). -/
theorem timedA_follows_unroll (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = true →
      GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk (wP ks)) (fun _ => 0) ∧
        GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c') ∧
        ChainOK (LSep (wP ks)) c cs)
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hInit : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t0 → Holds x t0 H c s) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N (CPu BIG ks) x t0 r v s) ∧
      (∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 (LSep (wP ks)) t := by
  obtain ⟨hTP, hSep, hUp, hTO, hGd⟩ := timing_unroll_pad N dat D BIG r' hr ks
    (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKP w0 hw0) Dc hcD hBC hS hU hT hG
  exact timedA_follows hb hTP (lsound_PF BIG ks hKF hL) (se_unroll ks dat hSEk) hTO hDE
    (fun v hg hd => lcheckXA_padC (hloc v hg hd).1 (hloc v hg hd).2) hEnvE (lenEq_unroll BIG ks) hgdF hGd hUp hSep
    (tmOK_PF BIG ks hKP hKF).2 (rt_unroll BIG ks hRTk) hGC hEnvC hInit (dataLen_unroll BIG ks dat hDLk)

/-- **`timedA_live` for the certificate of every word**: with the hypotheses of `timedA_follows_unroll`, the
per-kind liveness checks (`KindSub`, `KindNe`, every node with an event in some kind is in `U`), the gate delay
bounds `K` and the environment's progress `henv` (on the padded `CFu`), every event of the word's certificate
happens and the exact nodes then stay quiet. -/
theorem timedA_live_unroll (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hSubk : ∀ w ∈ ks, KindSub w) (hNek : ∀ w ∈ ks, KindNe w)
    (U : List α) (hCovk : ∀ w ∈ ks, ∀ u, 0 < w.len u → u ∈ U)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = true →
      GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk (wP ks)) (fun _ => 0) ∧
        GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c') ∧
        ChainOK (LSep (wP ks)) c cs)
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hInit : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t0 → Holds x t0 H c s)
    (K : α → Nat) (hK : ∀ v, N.gate v = true → 1 ≤ K v ∧ ∀ w ∈ N.pins v, N.hi v w < K v)
    (henv : ∀ u t, N.gate u = false → dat u = false → t0 ≤ t → Enabled (CFu BIG ks) (fun w => cntE dat x t0 w t) u →
      ∃ t', t < t' ∧ cnt x t0 u t < cnt x t0 u t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cntE dat x t0 u T = (CFu BIG ks).len u) ∧ ∀ u s, dat u = false → T ≤ s → x u s = x u T := by
  obtain ⟨hTP, hSep, hUp, hTO, hGd⟩ := timing_unroll_pad N dat D BIG r' hr ks
    (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKP w0 hw0) Dc hcD hBC hS hU hT hG
  exact timedA_live hb hTP (lsound_PF BIG ks hKF hL) (se_unroll ks dat hSEk) hTO hDE
    (fun v hg hd => lcheckXA_padC (hloc v hg hd).1 (hloc v hg hd).2) hEnvE (lenEq_unroll BIG ks) hgdF hGd hUp hSep
    (tmOK_PF BIG ks hKP hKF).2 (rt_unroll BIG ks hRTk) hGC hEnvC hInit (dataLen_unroll BIG ks dat hDLk)
    (sub_unroll BIG ks hSubk) U (cov_unroll BIG ks U hCovk) K hK (ne_unroll BIG ks hNek) henv

end main

end Formal.Net.AO
