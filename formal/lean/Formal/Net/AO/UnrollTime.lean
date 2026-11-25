import Formal.Net.AO.UnrollAsm
import Formal.Net.AO.WindowT

/-!
# The unrolled certificate, part 4: the timing tables for every word (shard C, all-pairs route)

**Problem, plainly.** For a word of window kinds `ks` (one per loop iteration), `UnrollAsm` reduces the long local
check to finitely many window checks. The timed theorem (`Timed.timedA_follows`) also needs the long certificate's
timing tables to be justified: time stamps (`TmOK`), separations (`SepOKA`), upper bounds (`UpOKA`), skew rows
(`TOA`) and guard timing (`hGd`, `GuardTime`). There are infinitely many words, so these must also follow from checks
on boundedly many consecutive kinds.

**Design.** A kind `WKindT` carries tables in coordinates relative to its window: `sep b m a k` (target `(a, k)` in the
window, source index `m : Int` counted from `b`'s first event in the window, negative = earlier windows), `up e0 e`
(target `e` in the window, `e0` relative), and a rank `rk`. The long tables `usep`, `uup` locate the target in its
window and read that kind's table (as `Unroll.uc` and `UnrollAsm.uL` do); the long time stamp of an event of window
`i` is `i * BIG + rk` (`utm`). In `Timed`, time stamps enter only through `TmOK`, the comparison `tm e0 < tm (b, m)`
in `SepOKA`'s fourth clause, and as the measure of the strong inductions in `up_sound`, `sepSound_step`, `lsound_of_step` and
`enabled_of_not_full`; any stamps with these properties serve, so synthetic ranks are enough. The certificate of a
sub-word `s` is `WC BIG s` (= `win` of the word, `win_wt`) with the sub-word's own tables restricted to its events
(`WSep`, `WUp`). The entries of window `i` are checked in the sub-word `(ks.drop (i - 1)).take r` (`r ≥ 2`; window 0
in the sub-word from window 0), whose window `i - (i - 1)` (1, or 0 for `i = 0`) holds them.

**Proved.**
* `tmOK_unroll`: `TmOK` of the long certificate for every word, from per-kind checks `KindTm` (ranks increase along a
  node, stay below `BIG`, causes are earlier in the window or in earlier windows).
* `sep_win`, `up_win`, `tm_win`, `wsep_dom`, `wup_dom`, `causes_win`: the correspondence hypotheses of `WindowT`
  (`hSep`, `hUp`, `hTm` with `B = j * BIG`, `hSepDom`, `hUpDom`, `hcs`) hold by construction for every word and `j`.
* `sepOKA_unroll`, `upOKA_unroll`, `toa_unroll`, `guardTime_unroll`: `SepOKA`, `UpOKA`, `TOA`, and `GuardTime` of
  every long guard, for every word, from the window checks `SepWin`, `UpWin`, `TOWin`, `GdWin` (each a property of
  one sub-word of at most `r` consecutive kinds and `t ∈ {0, 1}`, hence finitely many for finitely many kinds).
  `UpOKA` also needs `BackChain` (a check on consecutive kinds: every cause looks back at most one window).
* `upClause_window_np`: a variant of `WindowT.upClause_window` (whose `hExtra` asks for a justification of EVERY
  event before the window, which no window with positive offsets can give) that instead takes the fact that no long
  cause lies before the window (`noPre`, from `BackChain`).
* `uclT`, `lcheckXA_uclT`: `UnrollData.ucl` keeps window claims unshifted, which the local check does not notice but
  timing does; `uclT` shifts claim events to absolute indices and gives the same local check.
* `timing_unroll`: all five together, in the forms `timedA_follows` takes.

The window checks demand more than the long clauses strictly need, in ways an instance must meet: every table
entry's other event lies inside the checking sub-word (at most one window back for `r = 2`); in `UpWin`, a non-trivial
upper bound whose target is in window 1 of the sub-word must not be its node's first event there; in `TOWin`, every
skew row of window 1 must have a positive bound relative to the sub-word; guard and claim events are window-relative
`Nat` indices (as in `UnrollData`), so never in earlier windows.

**Not shown here:** that any instance passes these checks; the other hypotheses of `timedA_follows` (`LSound` of the
bounds, `hSE`, `hRT`, `TmOK CF`, claim proofs `hGC`/`ChainOK`, `hEnvE`, `hEnvC`, `hInit`, `hDataLen`); the same bound
`uL` is used for every reader (as in `UnrollAsm`); liveness bounds across words; that THE target's runs are unrolled
certificates of the token run's word (piece 3).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## Kinds with timing tables -/

/-- A window kind with timing tables, in coordinates RELATIVE to the window: `sep b m a k` (`k` an event of `a` in
this window, `m` counted from `b`'s first event in this window, negative = earlier windows), `up e0 e` (`e` in this
window, `e0` relative), and a within-window rank `rk` from which the long time stamps are built. -/
structure WKindT (α : Type) extends WKind α where
  sep : α → Int → α → Nat → Option Nat
  up : α × Int → α × Nat → Option Nat
  rk : α → Nat → Nat

/-- The plain kinds of a word. -/
def wk (ks : List (WKindT α)) : List (WKind α) := ks.map WKindT.toWKind

/-- The event structures of a word. -/
def wt (ks : List (WKindT α)) : List (WCert α) := wcs (wk ks)

/-- The event structures of a word, one kind at a time. -/
theorem wt_cons (w : WKindT α) (ks : List (WKindT α)) : wt (w :: ks) = w.toWCert :: wt ks := rfl

/-- Event counts of a word, one kind at a time. -/
theorem tot_wt_cons (w : WKindT α) (ks : List (WKindT α)) (u : α) :
    tot (wt (w :: ks)) u = w.len u + tot (wt ks) u := rfl

/-- Window offsets of a word, one kind at a time. -/
theorem off_wt_succ (w : WKindT α) (ks : List (WKindT α)) (j : Nat) (u : α) :
    off (wt (w :: ks)) (j + 1) u = w.len u + off (wt ks) j u := off_wcs_succ w.toWKind (wk ks) j u

/-- Dropping kinds commutes with forgetting the tables. -/
theorem wk_drop (ks : List (WKindT α)) (j : Nat) : wk (ks.drop j) = (wk ks).drop j := by
  simp [wk, List.map_drop]

/-- Taking kinds commutes with forgetting the tables. -/
theorem wk_take (ks : List (WKindT α)) (j : Nat) : wk (ks.take j) = (wk ks).take j := by
  simp [wk, List.map_take]

/-- Dropping kinds commutes with taking event structures. -/
theorem wt_drop (ks : List (WKindT α)) (j : Nat) : wt (ks.drop j) = (wt ks).drop j := by
  simp only [wt]; rw [wk_drop, wcs_drop]

/-- Taking kinds commutes with taking event structures. -/
theorem wt_take (ks : List (WKindT α)) (j : Nat) : wt (ks.take j) = (wt ks).take j := by
  simp only [wt]; rw [wk_take, wcs_take]

/-- One event structure per kind. -/
theorem wt_length (ks : List (WKindT α)) : (wt ks).length = ks.length := by
  simp [wt, wcs, wk]

/-- Offsets split at window `j`. -/
theorem off_wt_split (ks : List (WKindT α)) (j t : Nat) (u : α) :
    off (wt ks) (j + t) u = off (wt ks) j u + off (wt (ks.drop j)) t u := by
  have := off_split (wk ks) j t u
  simp only [wt]; rw [wk_drop]; exact this

/-- Offsets inside the first `r` windows do not see the rest. -/
theorem off_wt_take (l : List (WKindT α)) (r t : Nat) (u : α) (h : t ≤ r) :
    off (wt (l.take r)) t u = off (wt l) t u := by
  rw [off_eq_tot_take, off_eq_tot_take, wt_take, List.take_take, Nat.min_eq_left h]

/-- An offset is at most the total count. -/
theorem off_le_tot (ws : List (WCert α)) (j : Nat) (u : α) : off ws j u ≤ tot ws u := by
  have := off_add_tot_drop ws j u; omega

/-- Offsets grow with the window index. -/
theorem off_mono (ks : List (WKindT α)) (j t : Nat) (u : α) : off (wt ks) j u ≤ off (wt ks) (j + t) u := by
  rw [off_wt_split]; omega

/-- **Every event lies in a window.** -/
theorem locate : ∀ (ks : List (WKindT α)) (a : α) (K : Nat), K < tot (wt ks) a →
    ∃ i, i < ks.length ∧ off (wt ks) i a ≤ K ∧ K < off (wt ks) (i + 1) a
  | [], _, _, h => by simp [wt, wcs, wk, tot] at h
  | w :: ks, a, K, h => by
    by_cases hk : K < w.len a
    · refine ⟨0, by simp, by rw [off_zero]; omega, ?_⟩
      rw [off_wt_succ, off_zero]; omega
    · rw [tot_wt_cons] at h
      obtain ⟨i, hi, h1, h2⟩ := locate ks a (K - w.len a) (by omega)
      refine ⟨i + 1, by simp; omega, ?_, ?_⟩
      · rw [off_wt_succ]; omega
      · rw [off_wt_succ]; omega

/-! ## The long tables -/

/-- The long separation table: locate the event `(a, k)` in its window and read that kind's table, with `m`
(relative to `b`'s first event in the first window of the list) made relative to that window. -/
def usep : List (WKindT α) → α → Int → α → Nat → Option Nat
  | [], _, _, _, _ => none
  | w :: ks, b, m, a, k => if k < w.len a then w.sep b m a k else usep ks b (m - w.len b) a (k - w.len a)

/-- The long upper-bound table, likewise located by the target event `e`. -/
def uup : List (WKindT α) → α × Int → α × Nat → Option Nat
  | [], _, _ => none
  | w :: ks, e0, e => if e.2 < w.len e.1 then w.up e0 e else uup ks (e0.1, e0.2 - w.len e0.1) (e.1, e.2 - w.len e.1)

/-- The long time stamps: `i * BIG + rk` for an event of window `i` (rank `rk` in its kind). -/
def utm (BIG : Nat) : List (WKindT α) → α → Nat → Nat
  | [], _, _ => 0
  | w :: ks, u, k => if k < w.len u then w.rk u k else BIG + utm BIG ks u (k - w.len u)

/-- **The long certificate** of a word. -/
def LC (BIG : Nat) (ks : List (WKindT α)) : Cert α := unroll (wt ks) (utm BIG ks)

/-- The long separation table (`Nat` indices). -/
def LSep (ks : List (WKindT α)) : α → Nat → α → Nat → Option Nat := fun b m a k => usep ks b m a k

/-- The long upper-bound table (`Nat` indices). -/
def LUp (ks : List (WKindT α)) : α × Nat → α × Nat → Option Nat := fun e0 e => uup ks (e0.1, e0.2) e

/-- The certificate of a sub-word `s` (a window certificate when `s = (ks.drop j).take r`). -/
def WC (BIG : Nat) (s : List (WKindT α)) : Cert α := unroll (wt s) (utm BIG s)

/-- The sub-word's separation table, restricted to its own events. -/
def WSep (s : List (WKindT α)) : α → Nat → α → Nat → Option Nat := fun b m a k =>
  if m < tot (wt s) b ∧ k < tot (wt s) a then usep s b m a k else none

/-- The sub-word's upper-bound table, restricted to its own events. -/
def WUp (s : List (WKindT α)) : α × Nat → α × Nat → Option Nat := fun e0 e =>
  if e0.2 < tot (wt s) e0.1 ∧ e.2 < tot (wt s) e.1 then uup s (e0.1, e0.2) e else none

/-- The window certificate `win` of a word is the certificate of the sub-word. -/
theorem win_wt (ks : List (WKindT α)) (j r : Nat) (tm : α → Nat → Nat) :
    win (wt ks) j r tm = unroll (wt ((ks.drop j).take r)) tm := by
  simp only [win]; rw [wt_take, wt_drop]

/-! ## Shift and take identities -/

/-- **The long separation table, read from window `j`, is the table of the word from window `j`.** -/
theorem usep_shift : ∀ (ks : List (WKindT α)) (j : Nat) (b : α) (m : Int) (a : α) (k : Nat),
    usep ks b (m + (off (wt ks) j b : Int)) a (k + off (wt ks) j a) = usep (ks.drop j) b m a k
  | [], j, b, m, a, k => by cases j <;> rfl
  | w :: ks, 0, b, m, a, k => by simp [off_zero]
  | w :: ks, j + 1, b, m, a, k => by
    have hnl : ¬ (k + off (wt (w :: ks)) (j + 1) a < w.len a) := by rw [off_wt_succ]; omega
    have e : k + off (wt (w :: ks)) (j + 1) a - w.len a = k + off (wt ks) j a := by rw [off_wt_succ]; omega
    have e2 : m + (off (wt (w :: ks)) (j + 1) b : Int) - (w.len b : Int) = m + (off (wt ks) j b : Int) := by
      rw [off_wt_succ]; push_cast; omega
    simp only [usep, hnl, ite_false, e, e2, List.drop_succ_cons]
    exact usep_shift ks j b m a k

/-- The separation table of the first `r` kinds agrees on their events. -/
theorem usep_take : ∀ (ks : List (WKindT α)) (r : Nat) (b : α) (m : Int) (a : α) (k : Nat),
    k < tot (wt (ks.take r)) a → usep (ks.take r) b m a k = usep ks b m a k
  | [], _, _, _, _, _, _ => by simp
  | w :: ks, 0, _, _, _, _, h => by simp [wt, wcs, wk, tot] at h
  | w :: ks, r + 1, b, m, a, k, h => by
    simp only [List.take_succ_cons, usep]
    split
    · rfl
    · simp only [List.take_succ_cons, tot_wt_cons] at h
      exact usep_take ks r _ _ a _ (by omega)

/-- **The long upper-bound table, read from window `j`, is the table of the word from window `j`.** -/
theorem uup_shift : ∀ (ks : List (WKindT α)) (j : Nat) (e0 : α × Int) (e : α × Nat),
    uup ks (e0.1, e0.2 + (off (wt ks) j e0.1 : Int)) (e.1, e.2 + off (wt ks) j e.1) = uup (ks.drop j) e0 e
  | [], j, e0, e => by cases j <;> rfl
  | w :: ks, 0, e0, e => by simp [off_zero]
  | w :: ks, j + 1, e0, e => by
    have hnl : ¬ (e.2 + off (wt (w :: ks)) (j + 1) e.1 < w.len e.1) := by rw [off_wt_succ]; omega
    have e1 : e.2 + off (wt (w :: ks)) (j + 1) e.1 - w.len e.1 = e.2 + off (wt ks) j e.1 := by
      rw [off_wt_succ]; omega
    have e2 : e0.2 + (off (wt (w :: ks)) (j + 1) e0.1 : Int) - (w.len e0.1 : Int) =
        e0.2 + (off (wt ks) j e0.1 : Int) := by
      rw [off_wt_succ]; push_cast; omega
    simp only [uup, hnl, ite_false, e1, e2, List.drop_succ_cons]
    exact uup_shift ks j e0 e

/-- The upper-bound table of the first `r` kinds agrees on their events. -/
theorem uup_take : ∀ (ks : List (WKindT α)) (r : Nat) (e0 : α × Int) (e : α × Nat),
    e.2 < tot (wt (ks.take r)) e.1 → uup (ks.take r) e0 e = uup ks e0 e
  | [], _, _, _, _ => by simp
  | w :: ks, 0, _, _, h => by simp [wt, wcs, wk, tot] at h
  | w :: ks, r + 1, e0, e, h => by
    simp only [List.take_succ_cons, uup]
    split
    · rfl
    · simp only [List.take_succ_cons, tot_wt_cons] at h
      exact uup_take ks r _ (e.1, e.2 - w.len e.1) (by simp only; omega)

/-- Upper-bound entries have their target among the word's events. -/
theorem uup_dom : ∀ (ks : List (WKindT α)) (e0 : α × Int) (e : α × Nat) (d : Nat),
    uup ks e0 e = some d → e.2 < tot (wt ks) e.1
  | [], _, _, _, h => by simp [uup] at h
  | w :: ks, e0, e, d, h => by
    simp only [uup] at h
    rw [tot_wt_cons]
    split at h
    · omega
    · have := uup_dom ks _ _ d h; simp only at this; omega

/-- **Time stamps from window `j` on are the stamps of the word from window `j`, plus `j * BIG`.** -/
theorem utm_shift (BIG : Nat) : ∀ (ks : List (WKindT α)) (j : Nat) (u : α) (k : Nat), j ≤ ks.length →
    utm BIG ks u (k + off (wt ks) j u) = j * BIG + utm BIG (ks.drop j) u k
  | [], j, u, k, h => by
    have : j = 0 := by simpa using h
    subst this; simp [off_zero]
  | w :: ks, 0, u, k, _ => by simp [off_zero]
  | w :: ks, j + 1, u, k, h => by
    have hnl : ¬ (k + off (wt (w :: ks)) (j + 1) u < w.len u) := by rw [off_wt_succ]; omega
    have e : k + off (wt (w :: ks)) (j + 1) u - w.len u = k + off (wt ks) j u := by rw [off_wt_succ]; omega
    simp only [utm, hnl, ite_false, e, List.drop_succ_cons]
    rw [utm_shift BIG ks j u k (by simp at h; omega), Nat.add_mul, Nat.one_mul]
    generalize j * BIG = c
    omega

/-- The time stamps of the first `r` kinds agree on their events. -/
theorem utm_take (BIG : Nat) : ∀ (ks : List (WKindT α)) (r : Nat) (u : α) (k : Nat),
    k < tot (wt (ks.take r)) u → utm BIG (ks.take r) u k = utm BIG ks u k
  | [], _, _, _, _ => by simp
  | w :: ks, 0, _, _, h => by simp [wt, wcs, wk, tot] at h
  | w :: ks, r + 1, u, k, h => by
    simp only [List.take_succ_cons, utm]
    split
    · rfl
    · simp only [List.take_succ_cons, tot_wt_cons] at h
      rw [utm_take BIG ks r u _ (by omega)]

/-! ## Time stamps -/

/-- The per-kind time-stamp checks: ranks increase along each node's events and stay below `BIG`; every cause of a
window event is an earlier event of the window (smaller rank) or lies in an earlier window (negative index). -/
def KindTm (BIG : Nat) (w : WKindT α) : Prop :=
  (∀ u k, k + 1 < w.len u → w.rk u k < w.rk u (k + 1)) ∧
  (∀ u k, k < w.len u → w.rk u k < BIG) ∧
  (∀ u k, k < w.len u → ∀ alt ∈ w.causes u k, ∀ q ∈ alt,
    q.2 < (w.len q.1 : Int) ∧ (0 ≤ q.2 → w.rk q.1 q.2.toNat < w.rk u k))

/-- Time stamps increase along each node's events. -/
theorem utm_succ (BIG : Nat) : ∀ (ks : List (WKindT α)), (∀ w ∈ ks, KindTm BIG w) →
    ∀ u k, k + 1 < tot (wt ks) u → utm BIG ks u k < utm BIG ks u (k + 1)
  | [], _, u, k, h => by simp [wt, wcs, wk, tot] at h
  | w :: ks, hK, u, k, h => by
    have hw := hK w (by simp)
    rw [tot_wt_cons] at h
    by_cases h1 : k + 1 < w.len u
    · simp only [utm, h1, show k < w.len u by omega, ite_true]
      exact hw.1 u k h1
    · by_cases h2 : k < w.len u
      · have e : k + 1 - w.len u = 0 := by omega
        simp only [utm, h1, h2, ite_true, ite_false, e]
        have := hw.2.1 u k h2
        omega
      · have e : k + 1 - w.len u = (k - w.len u) + 1 := by omega
        simp only [utm, h1, h2, ite_false, e]
        have := utm_succ BIG ks (fun w' hw' => hK w' (by simp [hw'])) u (k - w.len u) (by omega)
        omega

/-- Every cause at or after the base `B` is an event of the word with a smaller time stamp. -/
theorem utm_cause (BIG : Nat) : ∀ (ks : List (WKindT α)) (B : α → Nat), (∀ w ∈ ks, KindTm BIG w) →
    ∀ u k, k < tot (wt ks) u → ∀ alt ∈ uc (wt ks) B u k, ∀ p ∈ alt, B p.1 ≤ p.2 →
      p.2 - B p.1 < tot (wt ks) p.1 ∧ utm BIG ks p.1 (p.2 - B p.1) < utm BIG ks u k
  | [], _, _, u, k, h, _, _, _, _, _ => by simp [wt, wcs, wk, tot] at h
  | w :: ks, B, hK, u, k, h, alt, halt, p, hp, hBp => by
    have hw := hK w (by simp)
    rw [tot_wt_cons] at h ⊢
    rw [wt_cons] at halt
    simp only [uc] at halt
    by_cases hk : k < w.len u
    · rw [ite_eq_left hk] at halt
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp halt
      obtain ⟨q, hq, h0, rfl⟩ := mem_absAlt.mp hp
      simp only at hBp ⊢
      obtain ⟨hq1, hq2⟩ := hw.2.2 u k hk a0 ha0 q hq
      have hq0 : 0 ≤ q.2 := by omega
      have e : ((B q.1 : Int) + q.2).toNat - B q.1 = q.2.toNat := by omega
      rw [e]
      have hlt : q.2.toNat < w.len q.1 := by omega
      simp only [utm, hk, hlt, ite_true]
      exact ⟨by omega, hq2 hq0⟩
    · rw [ite_eq_right hk] at halt
      have hK' : ∀ w' ∈ ks, KindTm BIG w' := fun w' hw' => hK w' (by simp [hw'])
      simp only [utm, hk, ite_false]
      by_cases hp2 : B p.1 + w.len p.1 ≤ p.2
      · obtain ⟨h1, h2⟩ := utm_cause BIG ks (fun p => B p + w.len p) hK' u (k - w.len u) (by omega) alt halt p hp hp2
        have hnl : ¬ (p.2 - B p.1 < w.len p.1) := by omega
        have e : p.2 - B p.1 - w.len p.1 = p.2 - (B p.1 + w.len p.1) := by omega
        simp only [hnl, ite_false, e]
        exact ⟨by omega, by omega⟩
      · have hlt : p.2 - B p.1 < w.len p.1 := by omega
        simp only [hlt, ite_true]
        have := hw.2.1 p.1 _ hlt
        exact ⟨by omega, by omega⟩

/-- **The long certificate's time stamps are valid** (`TmOK`), from the per-kind checks. -/
theorem tmOK_unroll (BIG : Nat) (ks : List (WKindT α)) (hK : ∀ w ∈ ks, KindTm BIG w) : TmOK (LC BIG ks) := by
  refine ⟨fun u k h => utm_succ BIG ks hK u k h, fun u k hk alt halt p hp => ?_⟩
  have := utm_cause BIG ks (fun _ => 0) hK u k hk alt halt p hp (Nat.zero_le _)
  simp only [LC, unroll]
  simpa using this

/-- A sub-word's certificate has valid time stamps too. -/
theorem tmOK_WC (BIG : Nat) (s : List (WKindT α)) (hK : ∀ w ∈ s, KindTm BIG w) : TmOK (WC BIG s) :=
  tmOK_unroll BIG s hK

/-! ## Window transfer: the identities `WindowT` needs, by construction -/

section transfer
variable (BIG : Nat) (ks : List (WKindT α)) (j r : Nat)

/-- **`WindowT`'s `hSep` by construction**: the long table at shifted indices is the sub-word's table. -/
theorem sep_win : ∀ b m a k, m < (WC BIG ((ks.drop j).take r)).len b → k < (WC BIG ((ks.drop j).take r)).len a →
    LSep ks b (m + off (wt ks) j b) a (k + off (wt ks) j a) = WSep ((ks.drop j).take r) b m a k := by
  intro b m a k hm hk
  simp only [WC, unroll] at hm hk
  simp only [LSep, WSep, hm, hk, and_self, ite_true]
  push_cast
  rw [usep_shift, usep_take _ _ _ _ _ _ hk]

/-- **`WindowT`'s `hUp` by construction.** -/
theorem up_win : ∀ e0 e : α × Nat, e0.2 < (WC BIG ((ks.drop j).take r)).len e0.1 →
    e.2 < (WC BIG ((ks.drop j).take r)).len e.1 →
    LUp ks (shE (off (wt ks) j) e0) (shE (off (wt ks) j) e) = WUp ((ks.drop j).take r) e0 e := by
  intro e0 e h0 he
  simp only [WC, unroll] at h0 he
  simp only [LUp, WUp, shE, h0, he, and_self, ite_true]
  push_cast
  have := uup_shift ks j (e0.1, (e0.2 : Int)) e
  simp only at this
  rw [this, uup_take _ _ _ _ he]

/-- **`WindowT`'s `hTm` by construction**, with the constant `B = j * BIG`. -/
theorem tm_win (hj : j ≤ ks.length) : ∀ u k, k < (WC BIG ((ks.drop j).take r)).len u →
    (LC BIG ks).tm u (k + off (wt ks) j u) = j * BIG + (WC BIG ((ks.drop j).take r)).tm u k := by
  intro u k hk
  simp only [WC, LC, unroll] at hk ⊢
  rw [utm_shift BIG ks j u k hj, utm_take BIG _ _ _ _ hk]

/-- **`WindowT`'s `hSepDom` by construction.** -/
theorem wsep_dom : ∀ b m a k d, WSep ((ks.drop j).take r) b m a k = some d →
    m < (WC BIG ((ks.drop j).take r)).len b ∧ k < (WC BIG ((ks.drop j).take r)).len a := by
  intro b m a k d h
  simp only [WSep] at h
  split at h
  · rename_i hc; exact hc
  · cases h

/-- **`WindowT`'s `hUpDom` by construction.** -/
theorem wup_dom : ∀ e0 e d, WUp ((ks.drop j).take r) e0 e = some d →
    e0.2 < (WC BIG ((ks.drop j).take r)).len e0.1 ∧ e.2 < (WC BIG ((ks.drop j).take r)).len e.1 := by
  intro e0 e d h
  simp only [WUp] at h
  split at h
  · rename_i hc; exact hc
  · cases h

/-- **`WindowT`'s `hcs` by construction** (from `Unroll.causesCorr_win`), given that every cause of `u` in every kind lies on `Dc u`. -/
theorem causes_win (Dc : α → List α) (hcD : ∀ w ∈ ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (v : α) :
    ∀ k, k < (WC BIG ((ks.drop j).take r)).len v → k + off (wt ks) j v < (LC BIG ks).len v ∧
      Pw (AltCorr (Dc v) (off (wt ks) j)) ((LC BIG ks).causes v (k + off (wt ks) j v))
        ((WC BIG ((ks.drop j).take r)).causes v k) := by
  have h := causesCorr_win (wt ks) (utm BIG ks) (utm BIG ((ks.drop j).take r)) j r (Dc v) v (by
    intro w hw k alt halt q hq
    simp only [wt, wcs, wk, List.map_map, List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact hcD w0 hw0 v k alt halt q hq)
  rw [win_wt] at h
  exact h

end transfer

/-! ## Locating a long event in a window certificate -/

/-- Event `k` of `a` lies in window `t` of the word `s`. -/
def InW (s : List (WKindT α)) (t : Nat) (a : α) (k : Nat) : Prop :=
  off (wt s) t a ≤ k ∧ k < off (wt s) (t + 1) a

/-- An event of window `i` of the word, seen from the sub-word that starts one window earlier (at window 0 for
`i = 0`): it lies in window `i - (i - 1)` (0 or 1) of the sub-word. -/
theorem local_win (ks : List (WKindT α)) (r : Nat) (hr : 2 ≤ r) (i : Nat) (a : α) (K : Nat)
    (hK1 : off (wt ks) i a ≤ K) (hK2 : K < off (wt ks) (i + 1) a) :
    off (wt ks) (i - 1) a ≤ K ∧ InW ((ks.drop (i - 1)).take r) (i - (i - 1)) a (K - off (wt ks) (i - 1) a) ∧
      K - off (wt ks) (i - 1) a < tot (wt ((ks.drop (i - 1)).take r)) a := by
  have hji : i - 1 + (i - (i - 1)) = i := by omega
  have e1 := off_wt_split ks (i - 1) (i - (i - 1)) a
  have e2 := off_wt_split ks (i - 1) (i - (i - 1) + 1) a
  rw [hji] at e1
  rw [show i - 1 + (i - (i - 1) + 1) = i + 1 by omega] at e2
  have f1 := off_wt_take (ks.drop (i - 1)) r (i - (i - 1)) a (by omega)
  have f2 := off_wt_take (ks.drop (i - 1)) r (i - (i - 1) + 1) a (by omega)
  have g := off_le_tot (wt ((ks.drop (i - 1)).take r)) (i - (i - 1) + 1) a
  exact ⟨by omega, ⟨by omega, by omega⟩, by omega⟩

/-- Kinds of a sub-word are kinds of the word. -/
theorem mem_sub {ks : List (WKindT α)} {j r : Nat} {w : WKindT α} (h : w ∈ (ks.drop j).take r) : w ∈ ks :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-! ## Separations -/

/-- **The window check for separations** of the sub-word `s` (target window `t` of `s`): every entry whose target
event lies in window `t` names a source inside `s` (index `m` relative to `s`, `0 ≤ m < tot`), and satisfies its
`SepOKA` clause in `s`'s certificate with `s`'s restricted tables. A property of `s` and `t` only. -/
def SepWin (N : TNet α) (BIG : Nat) (s : List (WKindT α)) (t : Nat) : Prop :=
  ∀ b (m : Int) a k d, InW s t a k → usep s b m a k = some d →
    0 ≤ m ∧ m < tot (wt s) b ∧ SepClause N (WC BIG s) (WSep s) (WUp s) b m.toNat a k d

/-- **`SepOKA` of the long certificate, for every word, from the window checks**: the entries of window `i` are
checked in the sub-word of `r ≥ 2` kinds from window `i - 1` (from window 0 when `i = 0`). -/
theorem sepOKA_unroll (N : TNet α) (BIG r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α))
    (hK : ∀ w ∈ ks, KindTm BIG w) (Dc : α → List α)
    (hcD : ∀ w ∈ ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u)
    (hW : ∀ i, i < ks.length → SepWin N BIG ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    SepOKA N (LC BIG ks) (LSep ks) (LUp ks) := by
  intro b M a K d hKl hd
  have hKl' : K < tot (wt ks) a := hKl
  obtain ⟨i, hi, hK1, hK2⟩ := locate ks a K hKl'
  obtain ⟨hle, hin, htot⟩ := local_win ks r hr i a K hK1 hK2
  have hd1 : usep ks b (M : Int) a K = some d := hd
  have hd' : usep ((ks.drop (i - 1)).take r) b ((M : Int) - off (wt ks) (i - 1) b) a
      (K - off (wt ks) (i - 1) a) = some d := by
    rw [usep_take _ _ _ _ _ _ htot, ← usep_shift ks (i - 1), Int.sub_add_cancel, Nat.sub_add_cancel hle]
    exact hd1
  obtain ⟨hm0, hm1, hcl⟩ := hW i hi b _ a _ d hin hd'
  obtain ⟨mN, hmN⟩ : ∃ mN : Nat, (mN : Int) = (M : Int) - off (wt ks) (i - 1) b := ⟨_, Int.toNat_of_nonneg hm0⟩
  have e1 : ((M : Int) - off (wt ks) (i - 1) b).toNat = mN := by omega
  rw [e1] at hcl
  have hKs : ∀ w ∈ (ks.drop (i - 1)).take r, KindTm BIG w := fun w hw => hK w (mem_sub hw)
  have := sepClause_window (N := N) (C := LC BIG ks) (C' := WC BIG ((ks.drop (i - 1)).take r)) (Sep := LSep ks)
    (Sep' := WSep ((ks.drop (i - 1)).take r)) (Up := LUp ks) (Up' := WUp ((ks.drop (i - 1)).take r))
    (o := off (wt ks) (i - 1)) (B := (i - 1) * BIG) (tmOK_WC BIG _ hKs) (sep_win BIG ks (i - 1) r)
    (up_win BIG ks (i - 1) r) (tm_win BIG ks (i - 1) r (by omega)) (wsep_dom BIG ks (i - 1) r) (Dc a) a
    (causes_win BIG ks (i - 1) r Dc hcD a) b mN (K - off (wt ks) (i - 1) a) d htot (by show mN < tot _ b; omega) hcl
  rw [show mN + off (wt ks) (i - 1) b = M by omega, Nat.sub_add_cancel hle] at this
  exact this

/-! ## Upper bounds -/

/-- Consecutive kinds: every cause of an event of the second kind lies at most one window back (its relative index is
at least minus the first kind's event count of the cause node). -/
def BackChain : List (WKindT α) → Prop
  | [] => True
  | [_] => True
  | w :: w' :: ks => (∀ u k, k < w'.len u → ∀ alt ∈ w'.causes u k, ∀ q ∈ alt, -(w.len q.1 : Int) ≤ q.2) ∧
      BackChain (w' :: ks)

/-- `BackChain` of a tail. -/
theorem backChain_tail : ∀ {w : WKindT α} {ks : List (WKindT α)}, BackChain (w :: ks) → BackChain ks
  | _, [], _ => trivial
  | _, _ :: _, h => h.2

/-- `BackChain` of a suffix. -/
theorem backChain_drop : ∀ (ks : List (WKindT α)) (i : Nat), BackChain ks → BackChain (ks.drop i)
  | [], i, _ => by simp [BackChain]
  | w :: ks, 0, h => h
  | w :: ks, i + 1, h => backChain_drop ks i (backChain_tail h)

/-- **No long cause lies before the sub-word**: a cause of an event of window `i` is at or after window `i - 1`. -/
theorem noPre (ks : List (WKindT α)) (hBC : BackChain ks) (i : Nat) (hi : i < ks.length) (u : α) (K : Nat)
    (hK1 : off (wt ks) i u ≤ K) (hK2 : K < off (wt ks) (i + 1) u) :
    ∀ alt ∈ uc (wt ks) (fun _ => 0) u K, ∀ p ∈ alt, off (wt ks) (i - 1) p.1 ≤ p.2 := by
  intro alt halt p hp
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; simp [off_zero]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨w, w', rest, hdrop⟩ : ∃ w w' rest, ks.drop j = w :: w' :: rest :=
    ⟨ks[j], ks[j + 1], ks.drop (j + 2), by
      rw [List.drop_eq_getElem_cons (by omega : j < ks.length),
        List.drop_eq_getElem_cons (by omega : j + 1 < ks.length)]⟩
  have o1 : off (wt ks) (j + 1) u = off (wt ks) j u + w.len u := by
    rw [off_wt_split ks j 1 u, hdrop, off_wt_succ, off_zero]; omega
  have o2 : off (wt ks) (j + 1 + 1) u = off (wt ks) j u + w.len u + w'.len u := by
    rw [show j + 1 + 1 = j + 2 by omega, off_wt_split ks j 2 u, hdrop, off_wt_succ, off_wt_succ, off_zero]; omega
  have huc := uc_shift (wt ks) j (fun _ => 0) u (K - off (wt ks) j u)
  rw [Nat.sub_add_cancel (by omega)] at huc
  rw [huc, ← wt_drop, hdrop, wt_cons, wt_cons] at halt
  have hn1 : ¬ (K - off (wt ks) j u < w.len u) := by omega
  have hn2 : K - off (wt ks) j u - w.len u < w'.len u := by omega
  simp only [uc, hn1, hn2, ite_false, ite_true] at halt
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp halt
  obtain ⟨q, hq, h0, rfl⟩ := mem_absAlt.mp hp
  have hBC' := backChain_drop ks j hBC
  rw [hdrop] at hBC'
  have := hBC'.1 u _ hn2 a0 ha0 q hq
  simp only at h0 ⊢
  omega

/-- `Window.upClause_window` with the pre-window clause replaced by the fact that no long cause lies before the
window (`hNoPre`); `upClause_window`'s `hExtra` quantifies over every event before the window, which a window with
positive offsets cannot supply. -/
theorem upClause_window_np {N : TNet α} {dat : α → Bool} {C C' : Cert α} {Sep Sep' : α → Nat → α → Nat → Option Nat}
    {Up Up' : α × Nat → α × Nat → Option Nat} {o : α → Nat} (hT' : TmOK C')
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hUp : ∀ e0 e : α × Nat, e0.2 < C'.len e0.1 → e.2 < C'.len e.1 → Up (shE o e0) (shE o e) = Up' e0 e)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (hUpDom : ∀ e0 e d, Up' e0 e = some d → e0.2 < C'.len e0.1 ∧ e.2 < C'.len e.1)
    (Dv : List α) (e0 e : α × Nat) (d : Nat)
    (hcs : ∀ k, k < C'.len e.1 → k + o e.1 < C.len e.1 ∧
      Pw (AltCorr Dv o) (C.causes e.1 (k + o e.1)) (C'.causes e.1 k))
    (hNoPre : ∀ alt ∈ C.causes e.1 (e.2 + o e.1), ∀ p ∈ alt, o p.1 ≤ p.2)
    (hprevW : 0 < e.2 + o e.1 → e.2 = 0 → UpCause N Sep Up (shE o e0) e.1 (e.1, e.2 + o e.1 - 1) d)
    (hd : Up' e0 e = some d) (hW : UpClause N dat C' Sep' Up' e0 e d) :
    UpClause N dat C Sep Up (shE o e0) (shE o e) d := by
  obtain ⟨he0, he⟩ := hUpDom e0 e d hd
  rcases hW with rfl | ⟨hg, hdat, hlen, ⟨alt', halt', hall⟩, hprev⟩
  · exact Or.inl rfl
  · right
    refine ⟨hg, hdat, (hcs e.2 he).1, ?_, ?_⟩
    · obtain ⟨alt, halt, hcor⟩ := forall₂_mem_right (hcs e.2 he).2 alt' halt'
      refine ⟨alt, halt, fun p hp => ?_⟩
      rcases hcor.2 p hp with ⟨q, hq, rfl⟩ | ⟨_, hpo⟩
      · have hql : q.2 < C'.len q.1 := (hT'.2 e.1 e.2 hlen alt' halt' q hq).1
        exact upCause_window hSep hUp hSepDom hUpDom e0 he0 e.1 q hql d (hall q hq)
      · exact absurd (hNoPre alt halt p hp) (by omega)
    · intro hpos
      by_cases h0 : e.2 = 0
      · exact hprevW hpos h0
      · have := upCause_window (N := N) hSep hUp hSepDom hUpDom e0 he0 e.1 (e.1, e.2 - 1) (by simp only; omega) d
          (hprev (by omega))
        simp only [shE] at this ⊢
        rw [show e.2 + o e.1 - 1 = e.2 - 1 + o e.1 by omega]; exact this

/-- **The window check for upper bounds** of the sub-word `s` (target window `t`): every entry whose target event
lies in window `t` has its reference event inside `s`, the target is not the first event of its node in `s` unless
`t = 0` or the entry is the trivial one (`e = e0`), and the entry satisfies its `UpOKA` clause in `s`'s
certificate. A property of `s` and `t` only. -/
def UpWin (N : TNet α) (dat : α → Bool) (BIG : Nat) (s : List (WKindT α)) (t : Nat) : Prop :=
  ∀ (e0 : α × Int) (e : α × Nat) d, InW s t e.1 e.2 → uup s e0 e = some d →
    0 ≤ e0.2 ∧ e0.2 < tot (wt s) e0.1 ∧ (e.2 = 0 → t = 0 ∨ e = (e0.1, e0.2.toNat)) ∧
    UpClause N dat (WC BIG s) (WSep s) (WUp s) (e0.1, e0.2.toNat) e d

/-- **`UpOKA` of the long certificate, for every word, from the window checks**, when every cause looks back at
most one window (`BackChain`). -/
theorem upOKA_unroll (N : TNet α) (dat : α → Bool) (BIG r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α))
    (hK : ∀ w ∈ ks, KindTm BIG w) (Dc : α → List α)
    (hcD : ∀ w ∈ ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain ks)
    (hW : ∀ i, i < ks.length → UpWin N dat BIG ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    UpOKA N dat (LC BIG ks) (LSep ks) (LUp ks) := by
  intro e0 e d hd
  obtain ⟨a0, M⟩ := e0
  obtain ⟨u, K⟩ := e
  have hd1 : uup ks (a0, (M : Int)) (u, K) = some d := hd
  have hKl : K < tot (wt ks) u := uup_dom ks _ _ d hd1
  obtain ⟨i, hi, hK1, hK2⟩ := locate ks u K hKl
  obtain ⟨hle, hin, htot⟩ := local_win ks r hr i u K hK1 hK2
  have hd' : uup ((ks.drop (i - 1)).take r) (a0, (M : Int) - off (wt ks) (i - 1) a0)
      (u, K - off (wt ks) (i - 1) u) = some d := by
    rw [uup_take _ _ _ _ htot]
    have := uup_shift ks (i - 1) (a0, (M : Int) - off (wt ks) (i - 1) a0) (u, K - off (wt ks) (i - 1) u)
    simp only at this
    rw [← this, Int.sub_add_cancel, Nat.sub_add_cancel hle]; exact hd1
  obtain ⟨hm0, hm1, hgap, hcl⟩ := hW i hi _ (u, K - off (wt ks) (i - 1) u) d hin hd'
  simp only at hm0 hm1 hgap hcl
  obtain ⟨mN, hmN⟩ : ∃ mN : Nat, (mN : Int) = (M : Int) - off (wt ks) (i - 1) a0 := ⟨_, Int.toNat_of_nonneg hm0⟩
  have e1 : ((M : Int) - off (wt ks) (i - 1) a0).toNat = mN := by omega
  rw [e1] at hcl hgap
  by_cases heq : (u, K - off (wt ks) (i - 1) u) = (a0, mN)
  · left
    simp only [Prod.mk.injEq] at heq ⊢
    obtain ⟨rfl, h2⟩ := heq
    exact ⟨rfl, by omega⟩
  have hKs : ∀ w ∈ (ks.drop (i - 1)).take r, KindTm BIG w := fun w hw => hK w (mem_sub hw)
  have hdW : WUp ((ks.drop (i - 1)).take r) (a0, mN) (u, K - off (wt ks) (i - 1) u) = some d := by
    simp only [WUp]
    rw [ite_eq_left ⟨by omega, htot⟩, hmN]; exact hd'
  have := upClause_window_np (N := N) (dat := dat) (C := LC BIG ks) (C' := WC BIG ((ks.drop (i - 1)).take r))
    (Sep := LSep ks) (Sep' := WSep ((ks.drop (i - 1)).take r)) (Up := LUp ks) (Up' := WUp ((ks.drop (i - 1)).take r))
    (o := off (wt ks) (i - 1)) (tmOK_WC BIG _ hKs) (sep_win BIG ks (i - 1) r) (up_win BIG ks (i - 1) r)
    (wsep_dom BIG ks (i - 1) r) (wup_dom BIG ks (i - 1) r) (Dc u) (a0, mN) (u, K - off (wt ks) (i - 1) u) d
    (causes_win BIG ks (i - 1) r Dc hcD u)
    (by
      simp only [Nat.sub_add_cancel hle]
      exact noPre ks hBC i hi u K hK1 hK2)
    (by
      intro h1 h2
      rcases hgap h2 with ht | he
      · have hi0 : i = 0 := by omega
        subst hi0
        have hz : off (wt ks) (0 - 1) u = 0 := off_zero _ _
        simp only at h1 h2
        omega
      · exact absurd he heq)
    hdW hcl
  simp only [shE] at this
  rw [show mN + off (wt ks) (i - 1) a0 = M by omega, Nat.sub_add_cancel hle] at this
  exact this

/-! ## Skew rows -/

/-- A positive bound read with base `B + o` is the bound read with base `B`, shifted by `o`. -/
theorem uL_add : ∀ (ks : List (WKind α)) (B o : α → Nat) (a : α) (k : Nat) (c : α),
    0 < uL ks B a k c → uL ks (fun p => B p + o p) a k c = uL ks B a k c + o c
  | [], _, _, _, _, _, h => by simp [uL] at h
  | w :: ks, B, o, a, k, c, h => by
    by_cases hk : k < w.len a
    · simp only [uL, hk, ite_true] at h ⊢
      push_cast; omega
    · simp only [uL, hk, ite_false] at h ⊢
      have := uL_add ks (fun p => B p + w.len p) o a (k - w.len a) c h
      have e : (fun p => (B p + o p) + w.len p) = (fun p => (B p + w.len p) + o p) := by funext p; omega
      rw [e]; exact this

/-- **The window check for skew rows** of the sub-word `s` (target window `t`): for every reader `v` and distinct
dependency nodes `a, b` with `lo' < hi'`, an event of `a` in window `t` whose bound on `b` is positive, or any such
event when `t > 0`, has a positive bound pointing inside `s` and its `TOA` row holds in `s`'s certificate with
`s`'s bounds `uL` and restricted separation table. A property of `s` and `t` only. -/
def TOWin (N : TNet α) (BIG : Nat) (D : α → List α) (s : List (WKindT α)) (t : Nat) : Prop :=
  ∀ v a b k, a ∈ D v → b ∈ D v → a ≠ b → InW s t a k → lo' N v a < hi' N v b →
    (0 < t ∨ 0 < uL (wk s) (fun _ => 0) a k b) →
    0 < uL (wk s) (fun _ => 0) a k b ∧ uL (wk s) (fun _ => 0) a k b - 1 < tot (wt s) b ∧
    TORow N (WC BIG s) (fun _ => uL (wk s) (fun _ => 0)) (WSep s) v a b k

/-- **`TOA` of the long certificate, for every word, from the window checks** (bounds `uL` of `UnrollAsm`, the
same for every reader; `CF` any certificate with the long event counts). -/
theorem toa_unroll (N : TNet α) (BIG r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α)) (D : α → List α)
    (CF : Cert α) (hCF : ∀ u, CF.len u = tot (wt ks) u) (Dc : α → List α)
    (hcD : ∀ w ∈ ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u)
    (hW : ∀ i, i < ks.length → TOWin N BIG D ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    TOA N CF (LC BIG ks) (fun _ => uL (wk ks) (fun _ => 0)) D (LSep ks) := by
  intro v a b K ha hb hab hKl hL0 hlh
  rw [hCF] at hKl
  obtain ⟨i, hi, hK1, hK2⟩ := locate ks a K hKl
  obtain ⟨hle, hin, htot⟩ := local_win ks r hr i a K hK1 hK2
  have hws : wk ((ks.drop (i - 1)).take r) = ((wk ks).drop (i - 1)).take r := by rw [wk_take, wk_drop]
  -- the long bound is the sub-word's bound read with base `off (i - 1)`
  have hLeq : uL (wk ks) (fun _ => 0) a K b =
      uL (wk ((ks.drop (i - 1)).take r)) (fun p => 0 + off (wt ks) (i - 1) p) a (K - off (wt ks) (i - 1) a) b := by
    have h1 : uL (wk ks) (fun _ => 0) a (K - off (wt ks) (i - 1) a + off (wt ks) (i - 1) a) b =
        uL ((wk ks).drop (i - 1)) (fun p => 0 + off (wt ks) (i - 1) p) a (K - off (wt ks) (i - 1) a) b :=
      uL_shift (wk ks) (i - 1) (fun _ => 0) a _ b
    have h2 : uL (((wk ks).drop (i - 1)).take r) (fun p => 0 + off (wt ks) (i - 1) p) a (K - off (wt ks) (i - 1) a) b =
        uL ((wk ks).drop (i - 1)) (fun p => 0 + off (wt ks) (i - 1) p) a (K - off (wt ks) (i - 1) a) b :=
      uL_take ((wk ks).drop (i - 1)) r _ a _ b (by rw [← hws]; exact htot)
    rw [hws, h2, ← h1, Nat.sub_add_cancel hle]
  have hpos : 0 < i - (i - 1) ∨ 0 < uL (wk ((ks.drop (i - 1)).take r)) (fun _ => 0) a (K - off (wt ks) (i - 1) a) b := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · right
      subst h0
      have hf : (fun p => 0 + off (wt ks) (0 - 1) p) = (fun _ => 0) := by funext p; rw [off_zero]
      have : 0 < uL (wk ks) (fun _ => 0) a K b := hL0
      rw [hLeq, hf] at this; exact this
    · left; omega
  obtain ⟨hL'0, hLb, hrow⟩ := hW i hi v a b _ ha hb hab hin hlh hpos
  have hLa : uL (wk ks) (fun _ => 0) a (K - off (wt ks) (i - 1) a + off (wt ks) (i - 1) a) b =
      uL (wk ((ks.drop (i - 1)).take r)) (fun _ => 0) a (K - off (wt ks) (i - 1) a) b + off (wt ks) (i - 1) b := by
    rw [Nat.sub_add_cancel hle, hLeq]
    have := uL_add (wk ((ks.drop (i - 1)).take r)) (fun _ => 0) (off (wt ks) (i - 1)) a _ b hL'0
    simpa using this
  have := toRow_window (N := N) (C := LC BIG ks) (C' := WC BIG ((ks.drop (i - 1)).take r)) (Sep := LSep ks)
    (Sep' := WSep ((ks.drop (i - 1)).take r)) (L := fun _ => uL (wk ks) (fun _ => 0))
    (L' := fun _ => uL (wk ((ks.drop (i - 1)).take r)) (fun _ => 0)) (o := off (wt ks) (i - 1))
    (sep_win BIG ks (i - 1) r) (Dc v) v a b _ htot (causes_win BIG ks (i - 1) r Dc hcD v) hL'0 hLb hLa hrow
  rw [Nat.sub_add_cancel hle] at this
  exact this

/-! ## Guards and claims -/

/-- The long claim list with each window's claim events made absolute (`UnrollData.ucl` keeps the windows' claims
unshifted, which is all the local check reads; timing needs absolute events). -/
def uclT : List (WKind α) → (α → Nat) → List (Claim α)
  | [], _ => []
  | w :: ks, b => w.cl.map (shC b) ++ uclT ks (fun p => b p + w.len p)

/-- `uclT` and `ucl` carry the same values. -/
theorem uclT_val : ∀ (ks : List (WKind α)) (b : α → Nat), (uclT ks b).map Claim.val = (ucl ks).map Claim.val
  | [], _ => rfl
  | w :: ks, b => by
    simp only [uclT, ucl, List.map_append, List.map_map]
    rw [uclT_val ks]
    rfl

/-- The data values the local check reads are the same with `uclT` as with `ucl`. -/
theorem dv_uclT (ks : List (WKind α)) (b : α → Nat) : dv (uclT ks b) = dv (ucl ks) := by
  funext gs n
  unfold dv
  split
  · rfl
  · rw [← List.getElem?_map, ← List.getElem?_map, uclT_val]

/-- **The local check is unchanged** when the claim list `ucl` is replaced by `uclT`. -/
theorem lcheckXA_uclT {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α}
    {L : α → Nat → α → Nat} {D : α → List α} {gd : α → α → List (Guard α)} {v : α}
    (ks : List (WKind α)) (b : α → Nat) :
    LCheckXA N dat envEn s0 C L D (uclT ks b) gd v ↔ LCheckXA N dat envEn s0 C L D (ucl ks) gd v := by
  simp only [LCheckXA, dv_uclT]

/-- Every long guard is a guard of some window's kind, shifted by that window's offsets. -/
theorem mem_ugd (v z : α) : ∀ (ks : List (WKind α)) (b : α → Nat) (c : Nat) (g : Guard α),
    g ∈ ugd v z ks b c → ∃ i, ∃ h : i < ks.length, ∃ g0 ∈ ks[i].gd v z,
      g = shiftG (fun p => b p + off (wcs ks) i p) (c + ncl (ks.take i)) g0
  | [], _, _, _, h => by simp [ugd] at h
  | w :: ks, b, c, g, h => by
    simp only [ugd, List.mem_append, List.mem_map] at h
    rcases h with ⟨g0, hg0, rfl⟩ | h
    · refine ⟨0, by simp, g0, by simpa using hg0, ?_⟩
      simp [off_zero, ncl]
    · obtain ⟨i, hi, g0, hg0, rfl⟩ := mem_ugd v z ks _ _ g h
      refine ⟨i + 1, by simp; omega, g0, by simpa using hg0, ?_⟩
      have e1 : (fun p => b p + w.len p + off (wcs ks) i p) = (fun p => b p + off (wcs (w :: ks)) (i + 1) p) := by
        funext p; rw [off_wcs_succ]; omega
      have e2 : c + w.cl.length + ncl (ks.take i) = c + ncl ((w :: ks).take (i + 1)) := by
        simp only [List.take_succ_cons, ncl]; omega
      rw [e1, e2]

/-- The claim a window guard names, in the long list `uclT`, is the window's claim shifted by that window's offsets. -/
theorem uclT_get : ∀ (ks : List (WKind α)) (b : α → Nat) (i : Nat) (h : i < ks.length) (n : Nat) (c : Claim α),
    ks[i].cl[n]? = some c → (uclT ks b)[ncl (ks.take i) + n]? = some (shC (fun p => b p + off (wcs ks) i p) c)
  | [], _, _, h, _, _, _ => by simp at h
  | w :: ks, b, 0, _, n, c, hc => by
    simp only [List.getElem_cons_zero] at hc
    have hn : n < w.cl.length := by
      rcases Nat.lt_or_ge n w.cl.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hc; cases hc
    simp only [List.take_zero, ncl, Nat.zero_add, uclT]
    rw [List.getElem?_append_left (by simpa using hn), List.getElem?_map, hc]
    simp [off_zero]
  | w :: ks, b, i + 1, h, n, c, hc => by
    simp only [List.getElem_cons_succ] at hc
    have := uclT_get ks (fun p => b p + w.len p) i (by simp at h; omega) n c hc
    simp only [List.take_succ_cons, ncl, uclT]
    rw [List.getElem?_append_right (by simp; omega), List.length_map,
      show w.cl.length + ncl (ks.take i) + n - w.cl.length = ncl (ks.take i) + n by omega, this]
    congr 2
    funext p; rw [off_wcs_succ]; omega

/-- Shifting a claim twice. -/
theorem shC_shC (o b : α → Nat) (c : Claim α) : shC o (shC b c) = shC (fun p => b p + o p) c := by
  cases c with
  | mk z val A a B b' =>
    cases A <;> cases B <;> simp [shC, shE, Nat.add_assoc]

/-- **The window check for guard timing** of the sub-word `s`: every guard of a data pin of a gate in window `t`'s
kind names a claim of that kind with the pin as its node, and the guard and claim, shifted to `s`'s coordinates,
satisfy `GuardTime` with `s`'s restricted separation table. A property of `s` and `t` only. -/
def GdWin (N : TNet α) (s : List (WKindT α)) (t : Nat) : Prop :=
  ∀ (h : t < s.length) (v z : α), N.gate v = true → z ∈ N.pins v → ∀ g ∈ s[t].gd v z, ∃ c, s[t].cl[g.ci]? = some c ∧
    c.z = z ∧ GuardTime N (WSep s) v z (shC (off (wt s) t) c) (shiftG (off (wt s) t) 0 g)

/-- **Guard timing of the long certificate (`Timed`'s `hGd`), for every word, from the window checks**, with the
long guards `ugd` of `UnrollData` and the absolute claim list `uclT`. -/
theorem guardTime_unroll (N : TNet α) (BIG r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α))
    (hW : ∀ i, i < ks.length → GdWin N ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ ugd v z (wk ks) (fun _ => 0) 0,
      ∃ c, (uclT (wk ks) (fun _ => 0))[g.ci]? = some c ∧ c.z = z ∧ GuardTime N (LSep ks) v z c g := by
  intro v z hg hz g hgm
  obtain ⟨i, hi, g0, hg0, rfl⟩ := mem_ugd v z (wk ks) _ _ g hgm
  have hi' : i < ks.length := by simpa [wk] using hi
  have hwi : (wk ks)[i] = ks[i].toWKind := by simp [wk]
  have ht : i - (i - 1) < ((ks.drop (i - 1)).take r).length := by simp; omega
  have hst : ((ks.drop (i - 1)).take r)[i - (i - 1)] = ks[i] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1; omega
  have hW' := hW i hi' ht v z hg hz g0 (by rw [hst]; rw [hwi] at hg0; exact hg0)
  rw [hst] at hW'
  obtain ⟨c0, hc0, hcz, hgt⟩ := hW'
  have hgt' := guardTime_window (N := N) (C' := WC BIG ((ks.drop (i - 1)).take r)) (Sep := LSep ks)
    (Sep' := WSep ((ks.drop (i - 1)).take r)) (o := off (wt ks) (i - 1)) (sep_win BIG ks (i - 1) r)
    (wsep_dom BIG ks (i - 1) r) v z _ _ (ncl ((wk ks).take i)) hgt
  rw [shC_shC, shiftG_shiftG] at hgt'
  have hf : (fun p => off (wt ((ks.drop (i - 1)).take r)) (i - (i - 1)) p + off (wt ks) (i - 1) p) =
      (fun p => (fun _ => 0) p + off (wcs (wk ks)) i p) := by
    funext p
    have e1 := off_wt_split ks (i - 1) (i - (i - 1)) p
    rw [show i - 1 + (i - (i - 1)) = i by omega] at e1
    have e2 := off_wt_take (ks.drop (i - 1)) r (i - (i - 1)) p (by omega)
    show _ = 0 + off (wt ks) i p
    omega
  rw [hf] at hgt'
  refine ⟨shC (fun p => (fun _ => 0) p + off (wcs (wk ks)) i p) c0, ?_, hcz, ?_⟩
  · have := uclT_get (wk ks) (fun _ => 0) i hi g0.ci c0 (by rw [hwi]; exact hc0)
    simp only [shiftG]
    rw [show g0.ci + (0 + ncl ((wk ks).take i)) = ncl ((wk ks).take i) + g0.ci by omega]
    exact this
  · rw [show (0 + ncl ((wk ks).take i)) = 0 + ncl ((wk ks).take i) from rfl] at hgt'
    simpa using hgt'

/-! ## Everything together -/

/-- **The timing hypotheses of `Timed.timedA_follows` for the long certificate of every word**, in the forms
`timedA_follows` takes them (`TmOK`, `SepOKA`, `UpOKA`, `TOA`, and `hGd` with guards `ugd` and claims `uclT`),
from per-kind checks (`KindTm`), the one-window lookback of causes (`BackChain`), and the window checks of the
sub-words of `r ≥ 2` kinds starting one window before each window. -/
theorem timing_unroll (N : TNet α) (dat : α → Bool) (D : α → List α) (BIG r : Nat) (hr : 2 ≤ r)
    (ks : List (WKindT α)) (CF : Cert α) (hCF : ∀ u, CF.len u = tot (wt ks) u)
    (hK : ∀ w ∈ ks, KindTm BIG w) (Dc : α → List α)
    (hcD : ∀ w ∈ ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain ks)
    (hS : ∀ i, i < ks.length → SepWin N BIG ((ks.drop (i - 1)).take r) (i - (i - 1)))
    (hU : ∀ i, i < ks.length → UpWin N dat BIG ((ks.drop (i - 1)).take r) (i - (i - 1)))
    (hT : ∀ i, i < ks.length → TOWin N BIG D ((ks.drop (i - 1)).take r) (i - (i - 1)))
    (hG : ∀ i, i < ks.length → GdWin N ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    TmOK (LC BIG ks) ∧ SepOKA N (LC BIG ks) (LSep ks) (LUp ks) ∧ UpOKA N dat (LC BIG ks) (LSep ks) (LUp ks) ∧
      TOA N CF (LC BIG ks) (fun _ => uL (wk ks) (fun _ => 0)) D (LSep ks) ∧
      (∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ ugd v z (wk ks) (fun _ => 0) 0,
        ∃ c, (uclT (wk ks) (fun _ => 0))[g.ci]? = some c ∧ c.z = z ∧ GuardTime N (LSep ks) v z c g) :=
  ⟨tmOK_unroll BIG ks hK, sepOKA_unroll N BIG r hr ks hK Dc hcD hS,
    upOKA_unroll N dat BIG r hr ks hK Dc hcD hBC hU, toa_unroll N BIG r hr ks D CF hCF Dc hcD hT,
    guardTime_unroll N BIG r hr ks hG⟩

end Formal.Net.AO
