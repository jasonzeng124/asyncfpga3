import Formal.Net.AO.Cover

/-!
# The unrolled certificate: a long certificate assembled from window certificates (shard C, all-pairs route)

**Problem, plainly.** For every operand pair, THE target's run is a sequence of windows (loop iterations), each of
one of finitely many *kinds*; its certificate should be the concatenation of per-kind window certificates. A window
certificate numbers each node's events from 0 at the window's start, and a cause may point back into earlier
windows (a negative relative index). This file defines the concatenation (`unroll`), the sub-certificate seen
from window `j` (`win`: `r` consecutive windows from `j`, causes before window `j` dropped), and proves that the
correspondence `Window.lcheckXA_window` / `Cover.lcheckXA_of_twoWindows` need holds **by construction**:
* `bounds_unroll`: the window boundaries `off ws j` are `Bounds` of the long certificate with top `ws.length`;
* `causesCorr_win`: the causes of the reader's events in `win ws j r`, shifted by `off ws j`, are the long
  certificate's, up to causes before window `j` (`AltCorr`), when every cause of the reader lies on its
  dependency set;
* `causes_dep_win`: the window's causes of the reader lie on the dependency set.

So for every word of kinds, the long local check at a reader reduces to the local checks of the `r`-window
certificates `win ws j r`, which depend only on `r` consecutive kinds (finitely many), plus `Spread`, the initial
states, guards and bounds (still hypotheses here; see `Cover`).

**Not shown here:** the initial state of each window (`hs0`), guards (`GuardsCorr`), bounds (`hL`), the timing
tables, time stamps; the instance.
-/

namespace Formal.Net.AO

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-- A window certificate: per node, its number of events in the window and, for each, the AND-OR causes, each
cause naming a node and an event index RELATIVE to that node's first event in this window (negative: earlier
windows). -/
structure WCert (α : Type) where
  len : α → Nat
  causes : α → Nat → List (List (α × Int))

/-- Events of `u` in the first `j` windows. -/
def off : List (WCert α) → Nat → α → Nat
  | [], _, _ => 0
  | _ :: _, 0, _ => 0
  | w :: ws, j + 1, u => w.len u + off ws j u

/-- Events of `u` in all windows. -/
def tot : List (WCert α) → α → Nat
  | [], _ => 0
  | w :: ws, u => w.len u + tot ws u

/-- An alternative with relative indices, made absolute with base `b`; causes before index 0 are dropped. -/
def absAlt (b : α → Nat) (alt : List (α × Int)) : List (α × Nat) :=
  alt.filterMap fun q => if 0 ≤ (b q.1 : Int) + q.2 then some (q.1, ((b q.1 : Int) + q.2).toNat) else none

/-- The causes of `u`'s `k`-th event in the concatenation of `ws`, the first window's events of each node `p`
numbered from `b p`. -/
def uc : List (WCert α) → (α → Nat) → α → Nat → List (List (α × Nat))
  | [], _, _, _ => []
  | w :: ws, b, u, k =>
    if k < w.len u then (w.causes u k).map (absAlt b) else uc ws (fun p => b p + w.len p) u (k - w.len u)

/-- **The unrolled certificate** of the windows `ws` (time stamps `tm` supplied separately). -/
def unroll (ws : List (WCert α)) (tm : α → Nat → Nat) : Cert α :=
  { len := tot ws, causes := uc ws (fun _ => 0), tm := tm }

/-- **The certificate seen from window `j`**: `r` windows from `j`, causes before window `j` dropped. -/
def win (ws : List (WCert α)) (j r : Nat) (tm : α → Nat → Nat) : Cert α :=
  unroll ((ws.drop j).take r) tm

/-! ## Offsets -/

theorem off_zero (ws : List (WCert α)) (u : α) : off ws 0 u = 0 := by
  cases ws <;> rfl

theorem off_succ_le : ∀ (ws : List (WCert α)) (j : Nat) (u : α), off ws j u ≤ off ws (j + 1) u
  | [], _, _ => Nat.le_refl _
  | w :: ws, 0, u => by simp [off]
  | w :: ws, j + 1, u => by
    have := off_succ_le ws j u
    simp only [off]; omega

theorem off_top : ∀ (ws : List (WCert α)) (j : Nat) (u : α), ws.length ≤ j → off ws j u = tot ws u
  | [], _, _, _ => rfl
  | w :: ws, 0, _, h => by simp at h
  | w :: ws, j + 1, u, h => by
    simp only [off, tot]
    rw [off_top ws j u (by simp at h; omega)]

theorem bounds_unroll (ws : List (WCert α)) (tm : α → Nat → Nat) :
    Bounds (unroll ws tm) (off ws) ws.length :=
  ⟨off_zero ws, off_succ_le ws, fun j u h => off_top ws j u h⟩

theorem tot_take_le : ∀ (ws : List (WCert α)) (r : Nat) (u : α), tot (ws.take r) u ≤ tot ws u
  | [], _, _ => by simp [tot]
  | w :: ws, 0, u => by simp [tot]
  | w :: ws, r + 1, u => by
    have := tot_take_le ws r u
    simp only [List.take_succ_cons, tot]; omega

theorem off_add_tot_drop : ∀ (ws : List (WCert α)) (j : Nat) (u : α), off ws j u + tot (ws.drop j) u = tot ws u
  | [], _, _ => by simp [off, tot]
  | w :: ws, 0, u => by simp [off, tot]
  | w :: ws, j + 1, u => by
    have := off_add_tot_drop ws j u
    simp only [off, List.drop_succ_cons, tot]; omega

/-! ## Causes -/

theorem uc_shift : ∀ (ws : List (WCert α)) (j : Nat) (b : α → Nat) (u : α) (k : Nat),
    uc ws b u (k + off ws j u) = uc (ws.drop j) (fun p => b p + off ws j p) u k
  | [], j, b, u, k => by cases j <;> rfl
  | w :: ws, 0, b, u, k => by simp [off]
  | w :: ws, j + 1, b, u, k => by
    have hnl : ¬ (k + off (w :: ws) (j + 1) u < w.len u) := by simp only [off]; omega
    have e : k + off (w :: ws) (j + 1) u - w.len u = k + off ws j u := by simp only [off]; omega
    simp only [uc, hnl, if_false, e, List.drop_succ_cons]
    rw [uc_shift ws j _ u k]
    congr 1
    funext p
    simp only [off]; omega

theorem uc_take : ∀ (ws : List (WCert α)) (r : Nat) (b : α → Nat) (u : α) (k : Nat),
    k < tot (ws.take r) u → uc (ws.take r) b u k = uc ws b u k
  | [], _, _, _, _, _ => by simp
  | w :: ws, 0, _, _, _, h => by simp [tot] at h
  | w :: ws, r + 1, b, u, k, h => by
    simp only [List.take_succ_cons, uc]
    split
    · rfl
    · simp only [List.take_succ_cons, tot] at h
      exact uc_take ws r _ u _ (by omega)

/-- Two lists that are maps of one list are related elementwise when the images are. -/
theorem pw_map {β γ δ : Type} {R : γ → δ → Prop} {f : β → γ} {g : β → δ} :
    ∀ (l : List β), (∀ a ∈ l, R (f a) (g a)) → Pw R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (pw_map l (fun b hb => h b (by simp [hb])))

theorem mem_absAlt {b : α → Nat} {alt : List (α × Int)} {p : α × Nat} :
    p ∈ absAlt b alt ↔ ∃ q ∈ alt, 0 ≤ (b q.1 : Int) + q.2 ∧ p = (q.1, ((b q.1 : Int) + q.2).toNat) := by
  unfold absAlt
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, h⟩
    split at h
    · exact ⟨q, hq, by assumption, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨q, hq, h0, rfl⟩
    exact ⟨q, hq, by simp [h0]⟩

/-- A relative alternative, made absolute at base `b + o` (long) and at base `b` (window), corresponds. -/
theorem altCorr_abs (Dv : List α) (o b : α → Nat) (alt : List (α × Int)) (hD : ∀ q ∈ alt, q.1 ∈ Dv) :
    AltCorr Dv o (absAlt (fun p => b p + o p) alt) (absAlt b alt) := by
  constructor
  · intro q hq
    obtain ⟨q0, hq0, h0, rfl⟩ := mem_absAlt.mp hq
    refine mem_absAlt.mpr ⟨q0, hq0, by push_cast; omega, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    push_cast; omega
  · intro p hp
    obtain ⟨q0, hq0, h0, rfl⟩ := mem_absAlt.mp hp
    by_cases hw : 0 ≤ (b q0.1 : Int) + q0.2
    · left
      refine ⟨(q0.1, ((b q0.1 : Int) + q0.2).toNat), mem_absAlt.mpr ⟨q0, hq0, hw, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      push_cast at h0 ⊢; omega
    · right
      refine ⟨hD q0 hq0, ?_⟩
      simp only
      push_cast at h0 ⊢; omega

theorem pw_uc (Dv : List α) (o : α → Nat) (v : α) :
    ∀ (ws : List (WCert α)) (b : α → Nat), (∀ w ∈ ws, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ Dv) →
      ∀ k, Pw (AltCorr Dv o) (uc ws (fun p => b p + o p) v k) (uc ws b v k)
  | [], _, _, _ => .nil
  | w :: ws, b, hD, k => by
    simp only [uc]
    split
    · exact pw_map _ (fun alt halt => altCorr_abs Dv o b alt (hD w (by simp) k alt halt))
    · have := pw_uc Dv o v ws (fun p => b p + w.len p) (fun w' hw' => hD w' (by simp [hw'])) (k - w.len v)
      have e : (fun p => (b p + w.len p) + o p) = (fun p => (b p + o p) + w.len p) := by
        funext p; omega
      rw [e] at this
      exact this

/-- **The window's causes of the reader correspond to the long certificate's** (`Window.CausesCorr`'s form). -/
theorem causesCorr_win (ws : List (WCert α)) (tm tm' : α → Nat → Nat) (j r : Nat) (Dv : List α) (v : α)
    (hD : ∀ w ∈ ws, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ Dv) :
    ∀ k, k < (win ws j r tm').len v → k + off ws j v < (unroll ws tm).len v ∧
      Pw (AltCorr Dv (off ws j)) ((unroll ws tm).causes v (k + off ws j v)) ((win ws j r tm').causes v k) := by
  intro k hk
  simp only [win, unroll] at hk ⊢
  have h1 := tot_take_le (ws.drop j) r v
  have h2 := off_add_tot_drop ws j v
  refine ⟨by omega, ?_⟩
  rw [uc_shift ws j _ v k, uc_take (ws.drop j) r _ v k hk]
  have hD' : ∀ w ∈ ws.drop j, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ Dv :=
    fun w hw => hD w (List.mem_of_mem_drop hw)
  have := pw_uc Dv (off ws j) v (ws.drop j) (fun _ => 0) hD' k
  simpa using this

theorem mem_uc {v : α} {Dv : List α} :
    ∀ (ws : List (WCert α)) (b : α → Nat), (∀ w ∈ ws, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ Dv) →
      ∀ k, ∀ alt ∈ uc ws b v k, ∀ q ∈ alt, q.1 ∈ Dv
  | [], _, _, _, alt, h => by simp [uc] at h
  | w :: ws, b, hD, k, alt, halt => by
    simp only [uc] at halt
    split at halt
    · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp halt
      intro q hq
      obtain ⟨q0, hq0, -, rfl⟩ := mem_absAlt.mp hq
      exact hD w (by simp) k a0 ha0 q0 hq0
    · exact mem_uc ws _ (fun w' hw' => hD w' (by simp [hw'])) _ alt halt

/-- **The window's causes of the reader lie on the dependency set** (`WinAt.hcD`). -/
theorem causes_dep_win (ws : List (WCert α)) (tm' : α → Nat → Nat) (j r : Nat) (Dv : List α) (v : α)
    (hD : ∀ w ∈ ws, ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ Dv) :
    ∀ k, k < (win ws j r tm').len v → ∀ alt ∈ (win ws j r tm').causes v k, ∀ q ∈ alt, q.1 ∈ Dv := by
  intro k _ alt halt
  simp only [win, unroll] at halt
  exact mem_uc _ _ (fun w hw => hD w (List.mem_of_mem_drop (List.mem_of_mem_take hw))) k alt halt

theorem off_eq_tot_take : ∀ (ws : List (WCert α)) (j : Nat) (u : α), off ws j u = tot (ws.take j) u
  | [], _, _ => by simp [off, tot]
  | w :: ws, 0, u => by simp [off, tot]
  | w :: ws, j + 1, u => by
    simp only [off, List.take_succ_cons, tot]
    rw [off_eq_tot_take ws j u]

theorem tot_append : ∀ (a b : List (WCert α)) (u : α), tot (a ++ b) u = tot a u + tot b u
  | [], b, u => by simp [tot]
  | w :: a, b, u => by
    simp only [List.cons_append, tot]
    rw [tot_append a b u]; omega

/-- **The window's end**: `r` windows from `j` end at boundary `j + r` (clipped at the end of the word). -/
theorem win_len (ws : List (WCert α)) (tm' : α → Nat → Nat) (j r : Nat) (u : α) :
    off ws j u + (win ws j r tm').len u = off ws (j + r) u := by
  simp only [win, unroll]
  rw [off_eq_tot_take, off_eq_tot_take, List.take_add, tot_append]

end Formal.Net.AO
