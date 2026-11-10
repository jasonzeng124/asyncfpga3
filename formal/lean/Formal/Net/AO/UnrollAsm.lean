import Formal.Net.AO.UnrollData

/-!
# The unrolled certificate, part 3: bounds, spread, and the local check for every word (shard C, all-pairs route)

**Problem, plainly.** For a word of window kinds `ks` (one per loop iteration of a run), the long certificate is
`unroll`; its local check at a reader `v` quantifies over every count vector of `v`'s dependency set, so it cannot be
checked once per word (there are infinitely many words). Does it follow from the local checks of the `r`-window
certificates `win ks j r`, each of which depends only on `r` consecutive kinds?

**Proved.**
* `uL`: the long bounds from per-kind relative bounds `Lr`; `uL_rel` gives `WinAt.hL` by construction.
* `spread_unroll`: the long bounds spread the windows (`Cover.Spread`) when, for every two consecutive kinds
  `w, w'`, the first event of a dependency node in `w'` needs every dependency node to have entered `w`
  (`PairChain`, a check on consecutive kinds).
* `lcheckXA_unroll`: **the long local check at `v` holds for the word `ks`** if every window certificate
  `win ks j r` (`j ≤ length`, `r ≥ 2`) passes its local check, given `PairChain`, the per-kind facts of
  `guardsCorr_win` for `v`'s data pins, every cause of `v` on its dependency set, and that each window holds `v`'s
  next event after the window's second window (`hWv`; e.g. `r = 3` when every kind has an event of `v`,
  `lcheckXA_unroll3`).

So the local check of every unrolled certificate is reduced to finitely many checks on kind tuples, plus the
reader facts `hv`, `hT` that the existing per-pair theorem already takes.

**Not shown here:** the timing tables (`TOA`, `SepOKA`, `UpOKA`, `GuardTime`) for every word (`WindowT` lifts single
entries); claim checks; that THE target's runs ARE unrolled certificates of words given by the token run
(refinement, piece 3); the instance.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## Bounds -/

/-- The long bound for event `k` of `a` on `c`: the per-kind relative bound made absolute (at least 0). -/
def uL : List (WKind α) → (α → Nat) → α → Nat → α → Nat
  | [], _, _, _, _ => 0
  | w :: ks, b, a, k, c =>
    if k < w.len a then ((b c : Int) + w.Lr a k c).toNat else uL ks (fun p => b p + w.len p) a (k - w.len a) c

theorem uL_shift : ∀ (ks : List (WKind α)) (j : Nat) (b : α → Nat) (a : α) (k : Nat) (c : α),
    uL ks b a (k + off (wcs ks) j a) c = uL (ks.drop j) (fun p => b p + off (wcs ks) j p) a k c
  | [], j, b, a, k, c => by cases j <;> rfl
  | w :: ks, 0, b, a, k, c => by simp [off_zero]
  | w :: ks, j + 1, b, a, k, c => by
    have hnl : ¬ (k + off (wcs (w :: ks)) (j + 1) a < w.len a) := by rw [off_wcs_succ]; omega
    have e : k + off (wcs (w :: ks)) (j + 1) a - w.len a = k + off (wcs ks) j a := by rw [off_wcs_succ]; omega
    simp only [uL, hnl, if_false, e, List.drop_succ_cons]
    rw [uL_shift ks j _ a k c]
    congr 1
    funext p
    rw [off_wcs_succ]; omega

theorem uL_take : ∀ (ks : List (WKind α)) (r : Nat) (b : α → Nat) (a : α) (k : Nat) (c : α),
    k < tot (wcs (ks.take r)) a → uL (ks.take r) b a k c = uL ks b a k c
  | [], _, _, _, _, _, _ => by simp
  | w :: ks, 0, _, _, _, _, h => by simp [wcs, tot] at h
  | w :: ks, r + 1, b, a, k, c, h => by
    simp only [List.take_succ_cons, uL]
    split
    · rfl
    · simp only [List.take_succ_cons, wcs, List.map_cons, tot] at h
      exact uL_take ks r _ a _ c (by simp only [wcs]; omega)

/-- A bound read with base `b` is 0 or, shifted by `o`, at most the bound read with base `b + o`. -/
theorem uL_rel : ∀ (ks : List (WKind α)) (b o : α → Nat) (a : α) (k : Nat) (c : α),
    uL ks b a k c = 0 ∨ uL ks b a k c + o c ≤ uL ks (fun p => b p + o p) a k c
  | [], _, _, _, _, _ => Or.inl rfl
  | w :: ks, b, o, a, k, c => by
    simp only [uL]
    split
    · omega
    · have := uL_rel ks (fun p => b p + w.len p) o a (k - w.len a) c
      have e : (fun p => (b p + o p) + w.len p) = (fun p => (b p + w.len p) + o p) := by funext p; omega
      rw [e]; exact this

/-- **`WinAt.hL` by construction.** -/
theorem hL_win (ks : List (WKind α)) (tm' : α → Nat → Nat) (j r : Nat) (a c : α) (k : Nat)
    (hk : k < (win (wcs ks) j r tm').len a) :
    uL ((ks.drop j).take r) (fun _ => 0) a k c = 0 ∨
      uL ((ks.drop j).take r) (fun _ => 0) a k c + off (wcs ks) j c ≤
        uL ks (fun _ => 0) a (k + off (wcs ks) j a) c := by
  rw [uL_shift ks j _ a k c]
  have hk' : k < tot (wcs ((ks.drop j).take r)) a := by
    simp only [win, unroll] at hk; rw [wcs_take, wcs_drop]; exact hk
  rw [← uL_take (ks.drop j) r _ a k c hk']
  exact uL_rel _ (fun _ => 0) (off (wcs ks) j) a k c

/-! ## Spread -/

/-- Consecutive kinds: the first event of a dependency node in the second needs every dependency node to have
entered the first. -/
def PairChain (Dv : List α) : List (WKind α) → Prop
  | [] => True
  | [_] => True
  | w :: w' :: ks => (∀ a ∈ Dv, ∀ c ∈ Dv, 0 < w'.len a → -(w.len c : Int) ≤ w'.Lr a 0 c) ∧ PairChain Dv (w' :: ks)

theorem pairChain_tail {Dv : List α} : ∀ {w : WKind α} {ks : List (WKind α)}, PairChain Dv (w :: ks) → PairChain Dv ks
  | _, [], _ => trivial
  | _, _ :: _, h => h.2

theorem pairChain_drop {Dv : List α} : ∀ (ks : List (WKind α)) (i : Nat), PairChain Dv ks → PairChain Dv (ks.drop i)
  | [], i, _ => by simp [PairChain]
  | w :: ks, 0, h => h
  | w :: ks, i + 1, h => pairChain_drop ks i (pairChain_tail h)

/-- The first event of `a` from a window on, read with base `B`, needs `B c - pl c` events of `c`, where `pl` is the
previous window's event count (the pair condition with the previous kind). -/
theorem uL_first (Dv : List α) (a c : α) (ha : a ∈ Dv) (hc : c ∈ Dv) :
    ∀ (ks : List (WKind α)) (B pl : α → Nat), PairChain Dv ks →
      (∀ w, ks.head? = some w → 0 < w.len a → -(pl c : Int) ≤ w.Lr a 0 c) →
      0 < tot (wcs ks) a → B c ≤ uL ks B a 0 c + pl c
  | [], _, _, _, _, h => by simp [wcs, tot] at h
  | w :: ks, B, pl, hP, hh, ht => by
    simp only [uL]
    split
    · have := hh w rfl (by assumption)
      omega
    · rename_i hnl
      have hw0 : w.len a = 0 := by omega
      simp only [Nat.zero_sub]
      have ht' : 0 < tot (wcs ks) a := by
        simp only [wcs, List.map_cons, tot] at ht; simp only [wcs]; omega
      have := uL_first Dv a c ha hc ks (fun p => B p + w.len p) (fun p => w.len p) (pairChain_tail hP)
        (fun w' hw' hpos => by
          cases ks with
          | nil => simp at hw'
          | cons w1 ks =>
            simp only [List.head?_cons, Option.some.injEq] at hw'
            subst hw'
            exact hP.1 a ha c hc hpos)
        ht'
      omega

theorem off_split (ks : List (WKind α)) (i t : Nat) (p : α) :
    off (wcs ks) (i + t) p = off (wcs ks) i p + off (wcs (ks.drop i)) t p := by
  rw [off_eq_tot_take, off_eq_tot_take, off_eq_tot_take, List.take_add, tot_append, wcs_drop]

/-- **The long bounds spread the windows** (`Cover.Spread`), from the pair condition on consecutive kinds. -/
theorem spread_unroll (ks : List (WKind α)) (tm : α → Nat → Nat) (Dv : List α) (hP : PairChain Dv ks) :
    Spread (unroll (wcs ks) tm) (uL ks (fun _ => 0)) Dv (off (wcs ks)) := by
  intro a ha c hc j hlt
  simp only [unroll] at hlt
  -- window j+1 exists
  have hlen : j + 1 < ks.length := by
    apply Classical.byContradiction
    intro hn
    have e := off_top (wcs ks) (j + 2) a (by simp [wcs]; omega)
    omega
  obtain ⟨w, hw⟩ : ∃ w, ks[j + 1]? = some w := ⟨ks[j + 1], List.getElem?_eq_getElem hlen⟩
  have hdrop : ks.drop (j + 1) = w :: ks.drop (j + 2) := by
    rw [List.drop_eq_getElem_cons hlen]
    congr 1
    exact (Option.some.inj (hw.symm.trans (List.getElem?_eq_getElem hlen))).symm
  -- read the bound of the first event of `a` from window j+2
  have e0 : uL ks (fun _ => 0) a (off (wcs ks) (j + 2) a) c =
      uL (ks.drop (j + 2)) (fun p => 0 + off (wcs ks) (j + 2) p) a 0 c := by
    have := uL_shift ks (j + 2) (fun _ => 0) a 0 c
    simpa using this
  rw [e0]
  have hoff : ∀ p, off (wcs ks) (j + 2) p = off (wcs ks) (j + 1) p + w.len p := by
    intro p
    rw [off_split ks (j + 1) 1 p, hdrop, off_wcs_succ, off_zero]; omega
  have hP' : PairChain Dv (w :: ks.drop (j + 2)) := by rw [← hdrop]; exact pairChain_drop ks (j + 1) hP
  have ht : 0 < tot (wcs (ks.drop (j + 2))) a := by
    have h1 := off_add_tot_drop (wcs ks) (j + 2) a
    rw [← wcs_drop] at h1
    simp only [wcs] at h1 hlt ⊢
    omega
  have := uL_first Dv a c ha hc (ks.drop (j + 2)) (fun p => 0 + off (wcs ks) (j + 2) p) (fun p => w.len p)
    (pairChain_tail hP')
    (fun w' hw' hpos => by
      cases hd : ks.drop (j + 2) with
      | nil => rw [hd] at hw'; simp at hw'
      | cons w1 l =>
        rw [hd] at hw' hP'
        simp only [List.head?_cons, Option.some.injEq] at hw'
        subst hw'
        exact hP'.1 a ha c hc hpos)
    ht
  rw [hoff c] at this
  omega

/-! ## Assembly -/

/-- **The long local check of an unrolled certificate, from its window checks.** -/
theorem lcheckXA_unroll {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {D : α → List α} {v : α} (hv : v ∈ D v)
    (hT : ∀ s s' : α → Bool, (∀ u ∈ D v, s u = s' u) → (∀ u, dat u = true → s u = s' u) →
      tEn N envEn v s = tEn N envEn v s')
    (ks : List (WKind α)) (tm tm' : α → Nat → Nat) (r : Nat) (hr : 2 ≤ r)
    (hcD : ∀ w ∈ ks, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ D v)
    (hen : ∀ z, dat z = true → z ∈ N.pins v →
      ∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.en = some w ∧ w.1 ∈ D v ∧ w.2 < k.len w.1)
    (hst : ∀ z, dat z = true → z ∈ N.pins v → ∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.st = some w ∧ w.1 ∈ D v)
    (hci : ∀ z, dat z = true → z ∈ N.pins v → ∀ k ∈ ks, ∀ g ∈ k.gd v z, g.ci < k.cl.length)
    (hP : PairChain (D v) ks)
    (hWv : ∀ j, j ≤ ks.length → off (wcs ks) (j + 2) v < tot (wcs ks) v →
      off (wcs ks) (j + 2) v < off (wcs ks) (j + r) v)
    (hW : ∀ j, j ≤ ks.length →
      LCheckXA N dat envEn (st s0 (off (wcs ks) j)) (win (wcs ks) j r tm') (uL ((ks.drop j).take r) (fun _ => 0)) D
        (ucl ((ks.drop j).take r)) (fun v z => ugd v z ((ks.drop j).take r) (fun _ => 0) 0) v) :
    LCheckXA N dat envEn s0 (unroll (wcs ks) tm) (uL ks (fun _ => 0)) D (ucl ks)
      (fun v z => ugd v z ks (fun _ => 0) 0) v := by
  have hB := bounds_unroll (wcs ks) tm
  have hlen' : (wcs ks).length = ks.length := by simp [wcs]
  rw [hlen'] at hB
  let W : Nat → WinAt N dat envEn s0 (unroll (wcs ks) tm) (uL ks (fun _ => 0)) D (ucl ks)
      (fun v z => ugd v z ks (fun _ => 0) 0) v := fun j0 =>
    let j := min j0 ks.length
    { C' := win (wcs ks) j r tm'
      L' := uL ((ks.drop j).take r) (fun _ => 0)
      s0' := st s0 (off (wcs ks) j)
      cl' := ucl ((ks.drop j).take r)
      gd' := fun v z => ugd v z ((ks.drop j).take r) (fun _ => 0) 0
      o := off (wcs ks) j
      co := coff ks j
      hc := hW j (Nat.min_le_right _ _)
      hs0 := fun _ _ => rfl
      hcs := causesCorr_win (wcs ks) tm tm' j r (D v) v (fun w hw => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw; exact hcD k hk)
      hcD := causes_dep_win (wcs ks) tm' j r (D v) v (fun w hw => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw; exact hcD k hk)
      hgd := fun z hz hzp => guardsCorr_win ks tm' j r (D v) v z (hen z hz hzp) (hst z hz hzp) (hci z hz hzp)
      hL := fun a _ c _ k hk => hL_win ks tm' j r a c k hk }
  have hWj : ∀ j, j ≤ ks.length → (W j).o = off (wcs ks) j ∧ (W j).C' = win (wcs ks) j r tm' := by
    intro j hj
    refine ⟨?_, ?_⟩ <;> simp [W, Nat.min_eq_left hj]
  apply lcheckXA_of_twoWindows hv hT hB (spread_unroll ks tm (D v) hP) W
  · intro j hj; exact (hWj j hj).1
  · intro j hj u _
    rw [(hWj j hj).2]
    rw [win_len]
    refine ⟨Bounds.mono_le hB u (j + 2) (j + r) (by omega), ?_⟩
    simp only [unroll]
    rw [off_eq_tot_take]
    exact tot_take_le _ _ _
  · intro j hj hlt
    rw [(hWj j hj).2, win_len]
    exact hWv j hj hlt

/-- With an event of the reader in every kind, three-window certificates hold the reader's next event (`hWv`). -/
theorem hWv_three (ks : List (WKind α)) (v : α) (hk : ∀ w ∈ ks, 0 < w.len v) :
    ∀ j, j ≤ ks.length → off (wcs ks) (j + 2) v < tot (wcs ks) v →
      off (wcs ks) (j + 2) v < off (wcs ks) (j + 3) v := by
  intro j _ hlt
  have hlen : j + 2 < ks.length := by
    apply Classical.byContradiction
    intro hn
    have e := off_top (wcs ks) (j + 2) v (by simp [wcs]; omega)
    omega
  have hdrop : ks.drop (j + 2) = ks[j + 2] :: ks.drop (j + 3) := List.drop_eq_getElem_cons hlen
  have e : off (wcs ks) (j + 3) v = off (wcs ks) (j + 2) v + ks[j + 2].len v := by
    rw [off_split ks (j + 2) 1 v, hdrop, off_wcs_succ, off_zero]; omega
  have := hk _ (List.getElem_mem hlen)
  omega

/-- **`lcheckXA_unroll` with three-window certificates**, when every kind has an event of the reader. -/
theorem lcheckXA_unroll3 {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {D : α → List α} {v : α} (hv : v ∈ D v)
    (hT : ∀ s s' : α → Bool, (∀ u ∈ D v, s u = s' u) → (∀ u, dat u = true → s u = s' u) →
      tEn N envEn v s = tEn N envEn v s')
    (ks : List (WKind α)) (tm tm' : α → Nat → Nat)
    (hcD : ∀ w ∈ ks, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ D v)
    (hen : ∀ z, dat z = true → z ∈ N.pins v →
      ∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.en = some w ∧ w.1 ∈ D v ∧ w.2 < k.len w.1)
    (hst : ∀ z, dat z = true → z ∈ N.pins v → ∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.st = some w ∧ w.1 ∈ D v)
    (hci : ∀ z, dat z = true → z ∈ N.pins v → ∀ k ∈ ks, ∀ g ∈ k.gd v z, g.ci < k.cl.length)
    (hP : PairChain (D v) ks) (hk : ∀ w ∈ ks, 0 < w.len v)
    (hW : ∀ j, j ≤ ks.length →
      LCheckXA N dat envEn (st s0 (off (wcs ks) j)) (win (wcs ks) j 3 tm') (uL ((ks.drop j).take 3) (fun _ => 0)) D
        (ucl ((ks.drop j).take 3)) (fun v z => ugd v z ((ks.drop j).take 3) (fun _ => 0) 0) v) :
    LCheckXA N dat envEn s0 (unroll (wcs ks) tm) (uL ks (fun _ => 0)) D (ucl ks)
      (fun v z => ugd v z ks (fun _ => 0) 0) v :=
  lcheckXA_unroll hv hT ks tm tm' 3 (by omega) hcD hen hst hci hP (hWv_three ks v hk) hW

end Formal.Net.AO
