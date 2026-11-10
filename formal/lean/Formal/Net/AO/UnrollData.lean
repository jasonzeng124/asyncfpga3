import Formal.Net.AO.Unroll

/-!
# The unrolled certificate, part 2: start states, claims and guards (shard C, all-pairs route)

**Problem, plainly.** `Unroll` builds the long certificate's events and causes from window certificates and shows
the cause half of `Window.WinAt` holds by construction. The local check also reads the start state of each window,
the data claims and the guards of each data pin. If each window kind carries its own start state, claim list and
guard lists (relative indices), are the long certificate's state, claims and guards the shifted window ones, as
`WinAt.hs0` and `WinAt.hgd` require?

**Proved:**
* `st_off`: if the first window's start state is the certificate's start state and each window's start state is the
  previous one's flipped by the parity of its event count (`StChain`, a check on consecutive kinds), the long state
  after `off ws j` events is window `j`'s start state; with `Formal.Net.OccNet.st` this is `WinAt.hs0`;
* `ugd_split`, `ugd_shift`: the long guard list of a data pin is the guards of the windows before `j`, then the
  window-`j..j+r` guard list shifted by `off ws j` (claim indices by `coff ws j`), then the later windows' guards;
* `guardsCorr_win`: hence `GuardsCorr` (`WinAt.hgd`), given per-kind facts: every guard names a start and an end
  event on the dependency set, its end lies inside its window (strictly before the window's length) and its claim
  index inside its window's claim list.

**Not shown here:** the bounds `L` (`hL`), the timing tables, the assembly for every word.

Per-kind hypotheses of `guardsCorr_win` are finite checks on the kinds; the strict end (`w.2 < len`) means a guard
of one window never extends to the next window's first event.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-- A window kind's data: its events and causes, its start state, its claims and, per reader and data pin, its
guards (event indices relative to the window, claim indices relative to its claim list). -/
structure WKind (α : Type) extends WCert α where
  s0 : α → Bool
  cl : List (Claim α)
  gd : α → α → List (Guard α)

/-- The windows' event structure. -/
def wcs (ks : List (WKind α)) : List (WCert α) := ks.map WKind.toWCert

/-! ## Start states -/

/-- Each window's start state is the previous window's flipped by the parity of its event count. -/
def StChain (Dv : List α) : List (WKind α) → Prop
  | [] => True
  | [_] => True
  | w :: w' :: ks => (∀ u ∈ Dv, w'.s0 u = xor (w.s0 u) (w.len u % 2 == 1)) ∧ StChain Dv (w' :: ks)

theorem xor_par (b : Bool) (x y : Nat) :
    xor b ((x + y) % 2 == 1) = xor (xor b (x % 2 == 1)) (y % 2 == 1) := by
  cases b <;> rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [Nat.add_mod, hx, hy]

theorem off_wcs_succ (w : WKind α) (ks : List (WKind α)) (j : Nat) (u : α) :
    off (wcs (w :: ks)) (j + 1) u = w.len u + off (wcs ks) j u := by
  simp only [wcs, List.map_cons]
  cases h : ks.map WKind.toWCert with
  | nil => simp [off]
  | cons a l => simp [off]

/-- **The long state at window `j`'s start is window `j`'s start state.** -/
theorem st_off (Dv : List α) : ∀ (ks : List (WKind α)) (s0 : α → Bool), StChain Dv ks →
    (∀ w, ks.head? = some w → ∀ u ∈ Dv, w.s0 u = s0 u) →
    ∀ j w, ks[j]? = some w → ∀ u ∈ Dv, st s0 (off (wcs ks) j) u = w.s0 u
  | [], _, _, _, _, w, h, _, _ => by simp at h
  | w0 :: ks, s0, hc, hh, 0, w, h, u, hu => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [st, off_zero, hh w0 rfl u hu]
    simp
  | [w0], _, _, _, j + 1, w, h, _, _ => by simp at h
  | w0 :: w1 :: ks, s0, hc, hh, j + 1, w, h, u, hu => by
    simp only [List.getElem?_cons_succ] at h
    have ih := st_off Dv (w1 :: ks) (fun u => xor (s0 u) (w0.len u % 2 == 1)) hc.2
      (fun w' hw' u' hu' => by
        simp only [List.head?_cons, Option.some.injEq] at hw'
        subst hw'
        rw [hc.1 u' hu', hh w0 rfl u' hu'])
      j w h u hu
    rw [← ih]
    simp only [st]
    rw [off_wcs_succ, xor_par]

/-! ## Claims and guards -/

/-- Number of claims of the windows. -/
def ncl : List (WKind α) → Nat
  | [] => 0
  | w :: ks => w.cl.length + ncl ks

/-- The long claim list: the windows' claims in order. -/
def ucl : List (WKind α) → List (Claim α)
  | [] => []
  | w :: ks => w.cl ++ ucl ks

/-- The long guard list of reader `v`'s data pin `z`, the first window's event indices of node `p` shifted by
`b p` and its claim indices by `c`. -/
def ugd (v z : α) : List (WKind α) → (α → Nat) → Nat → List (Guard α)
  | [], _, _ => []
  | w :: ks, b, c => (w.gd v z).map (shiftG b c) ++ ugd v z ks (fun p => b p + w.len p) (c + w.cl.length)

theorem ncl_eq : ∀ ks : List (WKind α), ncl ks = (ucl ks).length
  | [] => rfl
  | w :: ks => by simp [ncl, ucl, ncl_eq ks]

theorem ucl_append : ∀ a b : List (WKind α), ucl (a ++ b) = ucl a ++ ucl b
  | [], b => rfl
  | w :: a, b => by simp [ucl, ucl_append a b]

theorem shiftG_shiftG (o b : α → Nat) (co c : Nat) (g : Guard α) :
    shiftG o co (shiftG b c g) = shiftG (fun p => b p + o p) (c + co) g := by
  cases g with
  | mk ci st en =>
    cases st <;> cases en <;> simp [shiftG, Nat.add_assoc]

theorem ugd_shift (v z : α) (o : α → Nat) (co : Nat) : ∀ (ks : List (WKind α)) (b : α → Nat) (c : Nat),
    ugd v z ks (fun p => b p + o p) (c + co) = (ugd v z ks b c).map (shiftG o co)
  | [], _, _ => rfl
  | w :: ks, b, c => by
    simp only [ugd, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro g _
      simp only [Function.comp, shiftG_shiftG]
    · have e1 : (fun p => (b p + o p) + w.len p) = (fun p => (b p + w.len p) + o p) := by funext p; omega
      have e2 : c + co + w.cl.length = (c + w.cl.length) + co := by omega
      rw [e1, e2]
      exact ugd_shift v z o co ks _ _

theorem ugd_append (v z : α) : ∀ (a a' : List (WKind α)) (b : α → Nat) (c : Nat),
    ugd v z (a ++ a') b c = ugd v z a b c ++ ugd v z a' (fun p => b p + tot (wcs a) p) (c + ncl a)
  | [], a', b, c => by simp [ugd, tot, wcs, ncl]
  | w :: a, a', b, c => by
    simp only [List.cons_append, ugd, List.append_assoc]
    rw [ugd_append v z a a']
    have e1 : (fun p => b p + w.len p + tot (wcs a) p) = (fun p => b p + tot (wcs (w :: a)) p) := by
      funext p; simp only [wcs, List.map_cons, tot]; omega
    have e2 : c + w.cl.length + ncl a = c + ncl (w :: a) := by simp only [ncl]; omega
    rw [e1, e2]

theorem wcs_take (ks : List (WKind α)) (j : Nat) : wcs (ks.take j) = (wcs ks).take j := by
  simp [wcs, List.map_take]

theorem wcs_drop (ks : List (WKind α)) (j : Nat) : wcs (ks.drop j) = (wcs ks).drop j := by
  simp [wcs, List.map_drop]

/-- The claim offset of window `j`. -/
def coff (ks : List (WKind α)) (j : Nat) : Nat := ncl (ks.take j)

theorem ugd_en (v z : α) (Dv : List α) : ∀ (ks : List (WKind α)) (b : α → Nat) (c : Nat),
    (∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.en = some w ∧ w.1 ∈ Dv ∧ w.2 < k.len w.1) →
    ∀ g ∈ ugd v z ks b c, ∃ w, g.en = some w ∧ w.1 ∈ Dv ∧ w.2 < b w.1 + tot (wcs ks) w.1
  | [], _, _, _, g, h => by simp [ugd] at h
  | w :: ks, b, c, hk, g, h => by
    simp only [ugd, List.mem_append, List.mem_map] at h
    rcases h with ⟨g0, hg0, rfl⟩ | h
    · obtain ⟨e, he, heD, hlt⟩ := hk w (by simp) g0 hg0
      refine ⟨(e.1, e.2 + b e.1), by simp [shiftG, he], heD, ?_⟩
      simp only [wcs, List.map_cons, tot]; omega
    · obtain ⟨e, he, heD, hlt⟩ := ugd_en v z Dv ks _ _ (fun k hk' => hk k (by simp [hk'])) g h
      refine ⟨e, he, heD, ?_⟩
      simp only [wcs, List.map_cons, tot] at hlt ⊢; omega

theorem ugd_st (v z : α) (Dv : List α) : ∀ (ks : List (WKind α)) (b : α → Nat) (c : Nat),
    (∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.st = some w ∧ w.1 ∈ Dv) →
    ∀ g ∈ ugd v z ks b c, ∃ w, g.st = some w ∧ w.1 ∈ Dv ∧ b w.1 ≤ w.2
  | [], _, _, _, g, h => by simp [ugd] at h
  | w :: ks, b, c, hk, g, h => by
    simp only [ugd, List.mem_append, List.mem_map] at h
    rcases h with ⟨g0, hg0, rfl⟩ | h
    · obtain ⟨e, he, heD⟩ := hk w (by simp) g0 hg0
      exact ⟨(e.1, e.2 + b e.1), by simp [shiftG, he], heD, by simp only; omega⟩
    · obtain ⟨e, he, heD, hle⟩ := ugd_st v z Dv ks _ _ (fun k hk' => hk k (by simp [hk'])) g h
      exact ⟨e, he, heD, by omega⟩

theorem ugd_dep (v z : α) (Dv : List α) : ∀ (ks : List (WKind α)) (c : Nat),
    (∀ k ∈ ks, ∀ g ∈ k.gd v z, (∀ w, g.st = some w → w.1 ∈ Dv) ∧ (∀ w, g.en = some w → w.1 ∈ Dv)) →
    ∀ (b : α → Nat), ∀ g ∈ ugd v z ks b c, (∀ w, g.st = some w → w.1 ∈ Dv) ∧ (∀ w, g.en = some w → w.1 ∈ Dv)
  | [], _, _, _, g, h => by simp [ugd] at h
  | w :: ks, c, hk, b, g, h => by
    simp only [ugd, List.mem_append, List.mem_map] at h
    rcases h with ⟨g0, hg0, rfl⟩ | h
    · have := hk w (by simp) g0 hg0
      constructor
      · intro e he
        simp only [shiftG, Option.map_eq_some_iff] at he
        obtain ⟨e0, he0, rfl⟩ := he
        exact this.1 e0 he0
      · intro e he
        simp only [shiftG, Option.map_eq_some_iff] at he
        obtain ⟨e0, he0, rfl⟩ := he
        exact this.2 e0 he0
    · exact ugd_dep v z Dv ks _ (fun k hk' => hk k (by simp [hk'])) _ g h

theorem ugd_ci (v z : α) : ∀ (ks : List (WKind α)) (c : Nat),
    (∀ k ∈ ks, ∀ g ∈ k.gd v z, g.ci < k.cl.length) →
    ∀ (b : α → Nat), ∀ g ∈ ugd v z ks b c, c ≤ g.ci ∧ g.ci < c + ncl ks
  | [], _, _, _, g, h => by simp [ugd] at h
  | w :: ks, c, hk, b, g, h => by
    simp only [ugd, List.mem_append, List.mem_map] at h
    rcases h with ⟨g0, hg0, rfl⟩ | h
    · have := hk w (by simp) g0 hg0
      simp only [shiftG, ncl]; omega
    · have := ugd_ci v z ks _ (fun k hk' => hk k (by simp [hk'])) _ g h
      simp only [ncl]; omega

/-- **The long guards of a data pin correspond to the window's** (`Window.GuardsCorr`, i.e. `WinAt.hgd`), for every
word, given per-kind facts: every guard has a start and an end event on the dependency set, the end strictly
inside its window, and its claim inside its window's claim list. -/
theorem guardsCorr_win (ks : List (WKind α)) (tm' : α → Nat → Nat) (j r : Nat) (Dv : List α) (v z : α)
    (hen : ∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.en = some w ∧ w.1 ∈ Dv ∧ w.2 < k.len w.1)
    (hst : ∀ k ∈ ks, ∀ g ∈ k.gd v z, ∃ w, g.st = some w ∧ w.1 ∈ Dv)
    (hci : ∀ k ∈ ks, ∀ g ∈ k.gd v z, g.ci < k.cl.length) :
    GuardsCorr (win (wcs ks) j r tm') Dv (off (wcs ks) j) (coff ks j) (ucl ks) (ucl ((ks.drop j).take r))
      (ugd v z ks (fun _ => 0) 0) (ugd v z ((ks.drop j).take r) (fun _ => 0) 0) := by
  have hdep : ∀ k ∈ ks, ∀ g ∈ k.gd v z, (∀ w, g.st = some w → w.1 ∈ Dv) ∧ (∀ w, g.en = some w → w.1 ∈ Dv) := by
    intro k hk g hg
    obtain ⟨e, he, heD, -⟩ := hen k hk g hg
    obtain ⟨e', he', heD'⟩ := hst k hk g hg
    exact ⟨fun w hw => by rw [he'] at hw; cases hw; exact heD', fun w hw => by rw [he] at hw; cases hw; exact heD⟩
  have hsubD : ∀ k ∈ ks.drop j, k ∈ ks := fun k hk => List.mem_of_mem_drop hk
  have hsubT : ∀ k ∈ (ks.drop j).take r, k ∈ ks := fun k hk => hsubD k (List.mem_of_mem_take hk)
  have hsubP : ∀ k ∈ ks.take j, k ∈ ks := fun k hk => List.mem_of_mem_take hk
  have hsubR : ∀ k ∈ (ks.drop j).drop r, k ∈ ks := fun k hk => hsubD k (List.mem_of_mem_drop hk)
  -- the split of the long guard list
  have hsplit : ugd v z ks (fun _ => 0) 0 =
      ugd v z (ks.take j) (fun _ => 0) 0 ++
        ((ugd v z ((ks.drop j).take r) (fun _ => 0) 0).map (shiftG (off (wcs ks) j) (coff ks j)) ++
          (ugd v z ((ks.drop j).drop r) (fun p => tot (wcs ((ks.drop j).take r)) p) (ncl ((ks.drop j).take r))).map
            (shiftG (off (wcs ks) j) (coff ks j))) := by
    conv => lhs; rw [← List.take_append_drop j ks]
    rw [ugd_append]
    congr 1
    conv => lhs; rw [← List.take_append_drop r (ks.drop j)]
    rw [ugd_append]
    congr 1
    · have e1 : (fun p => (0 : Nat) + tot (wcs (ks.take j)) p) =
          (fun p => (fun _ => (0 : Nat)) p + off (wcs ks) j p) := by
        funext p; simp only; rw [off_eq_tot_take, wcs_take]
      rw [e1, show (0 : Nat) + ncl (ks.take j) = 0 + coff ks j from rfl, ugd_shift]
    · have e3 : (fun p => (0 : Nat) + tot (wcs (ks.take j)) p + tot (wcs ((ks.drop j).take r)) p) =
          (fun p => (fun p => tot (wcs ((ks.drop j).take r)) p) p + off (wcs ks) j p) := by
        funext p; simp only; rw [off_eq_tot_take, wcs_take]; omega
      rw [e3, show (0 : Nat) + ncl (ks.take j) + ncl ((ks.drop j).take r) =
          ncl ((ks.drop j).take r) + coff ks j by unfold coff; omega, ugd_shift]
  refine ⟨ugd v z (ks.take j) (fun _ => 0) 0,
    (ugd v z ((ks.drop j).drop r) (fun p => tot (wcs ((ks.drop j).take r)) p) (ncl ((ks.drop j).take r))).map
      (shiftG (off (wcs ks) j) (coff ks j)), by rw [hsplit, List.append_assoc], ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨e, he, heD, hlt⟩ := ugd_en v z Dv (ks.take j) _ 0 (fun k hk => hen k (hsubP k hk)) g hg
    refine ⟨e, he, heD, ?_⟩
    rw [off_eq_tot_take, ← wcs_take]; simpa using hlt
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨e, he, heD, hle⟩ := ugd_st v z Dv ((ks.drop j).drop r) _ _ (fun k hk => hst k (hsubR k hk)) g0 hg0
    refine ⟨(e.1, e.2 + off (wcs ks) j e.1), by simp [shiftG, he], heD, ?_⟩
    have hl : (win (wcs ks) j r tm').len e.1 = tot (wcs ((ks.drop j).take r)) e.1 := by
      rw [wcs_take, wcs_drop]; rfl
    rw [hl]
    simp only at hle ⊢; omega
  · exact fun g hg => ugd_dep v z Dv _ 0 (fun k hk => hdep k (hsubT k hk)) _ g hg
  · intro g hg
    have hc := ugd_ci v z ((ks.drop j).take r) 0 (fun k hk => hci k (hsubT k hk)) _ g hg
    have e : ucl ks = ucl (ks.take j) ++ (ucl ((ks.drop j).take r) ++ ucl ((ks.drop j).drop r)) := by
      conv => lhs; rw [← List.take_append_drop j ks, ← List.take_append_drop r (ks.drop j)]
      rw [ucl_append, ucl_append]
    have hco : coff ks j = (ucl (ks.take j)).length := ncl_eq _
    have hlen : g.ci < (ucl ((ks.drop j).take r)).length := by rw [← ncl_eq]; omega
    rw [e, hco, List.getElem?_append_right (by omega), Nat.add_sub_cancel,
      List.getElem?_append_left hlen]

end Formal.Net.AO
