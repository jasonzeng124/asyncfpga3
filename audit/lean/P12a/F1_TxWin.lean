import Formal.Net.CapstoneRefine4Fn
import Formal.Net.CapstoneRefine4Wit

/-!
# Audit P12a / F1: `TxWin` (hence `Row`, `RowG`, `BCert.dag`, `BCert.cert`) needs INFINITELY
many offers on the channel.

`TxWin.count : ∀ k, cnt (riseB P.req) (τ k) = k` for EVERY `k : Nat`. On a channel that is
offered only finitely often this is impossible. Consequences proved here:

* `txwin_inf`: a `TxWin` forces an offer after every time `M`.
* `bcert_fin_held`: on a finitely-offered channel a `BCert` is necessarily `exempt`
  (it yields `Held` with NO reset / receiver premise: the tcheck constructors are dead).
* `row_inf`: same for `Row`.
* `cls_sampled_inf`: phys5_cls's per-operator hypothesis forces EVERY sampled channel (incl.
  out0) to be offered infinitely often.
* `chW_not_cls`: on C-8t's run `chW` (the only gcd_hw witness; finite event lists) the
  hypothesis of `gcd_hw_circuit_safe_phys5_cls` (and so of `phys5_gen`) is FALSE.
-/

namespace P12a
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine
open Formal.Net.CapNet Formal.Net.CapNet.Gcd Formal.Net.OpsBusy Formal.Net.OpsBusy3

theorem cnt_stable {f : Nat → Bool} {M : Nat} (h : ∀ t, M ≤ t → f t = false) :
    ∀ n, cnt f (M + n) = cnt f M
  | 0 => rfl
  | n + 1 => by
    have e : cnt f (M + (n + 1)) = cnt f (M + n) + (if f (M + n) then 1 else 0) := rfl
    rw [e, h (M + n) (by omega), cnt_stable h n]
    simp

theorem cnt_bound {f : Nat → Bool} {M : Nat} (h : ∀ t, M ≤ t → f t = false) (t : Nat) :
    cnt f t ≤ cnt f M := by
  rcases Nat.le_total t M with ht | ht
  · exact cnt_mono f ht
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [cnt_stable h n]
    exact Nat.le_refl _

/-- **A `TxWin` forces an offer after every time `M`.** -/
theorem txwin_inf {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat}
    {R : Nat → Nat → Prop} (X : TxWin P sig data R) (M : Nat) :
    ∃ t, M ≤ t ∧ riseB P.req t = true := by
  apply Classical.byContradiction
  intro hne
  have h : ∀ t, M ≤ t → riseB P.req t = false := by
    intro t ht
    cases e : riseB P.req t with
    | false => rfl
    | true => exact absurd ⟨t, ht, e⟩ hne
  have h1 := X.count (cnt (riseB P.req) M + 1)
  have h2 := cnt_bound h (X.τ (cnt (riseB P.req) M + 1))
  omega

theorem txwin_false_of_fin {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat}
    {R : Nat → Nat → Prop} {M : Nat} (h : ∀ t, M ≤ t → riseB P.req t = false)
    (X : TxWin P sig data R) : False := by
  obtain ⟨t, ht, e⟩ := txwin_inf X M
  rw [h t ht] at e
  exact Bool.noConfusion e

/-- **On a finitely-offered channel a certificate is `exempt`**: it gives `Held` with no reset
and no receiver rule. -/
theorem bcert_fin_held {P : Chan} {M : Nat} (h : ∀ t, M ≤ t → riseB P.req t = false)
    (B : BCert P) : Held P := by
  cases B with
  | dag net req data setup sig hwf hc runs X => exact (txwin_false_of_fin h X).elim
  | cert dag late pot data targets setup sigD sigL hwf hpot hnz hwin rD rL X =>
    exact (txwin_false_of_fin h X).elim
  | exempt hh => exact hh

theorem row_inf {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    {c : Fin n} (row : Row ch sv k w c) (M : Nat) : ∃ t, M ≤ t ∧ riseB (ch c).req t = true := by
  obtain ⟨net, hwf, sig, data, R, runs, X, _⟩ := row
  exact txwin_inf X M

theorem rowG_inf {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    {c : Fin n} (row : RowG ch sv k w c) (M : Nat) : ∃ t, M ≤ t ∧ riseB (ch c).req t = true := by
  obtain ⟨net, hwf, sig, data, R, runs, X, _⟩ := row
  exact txwin_inf X M

/-- phys5_cls's per-operator hypothesis forces every sampled channel to be offered infinitely
often. -/
theorem cls_sampled_inf (ch : Fin NC → Chan) (sv : Nat → Nat) (c : Fin NC)
    (hs : isSampled c = true) (h : CellPcls ch sv (prodOf c)) (M : Nat) :
    ∃ t, M ≤ t ∧ riseB (ch c).req t = true := by
  obtain ⟨w, _, hd⟩ := h
  exact row_inf ((hd c (prod_mem c)).1 hs) M

theorem out0_sampled : isSampled out0 = true := by decide

/-- **Under the hypotheses of `gcd_hw_circuit_safe_phys5_cls`, out0 is offered infinitely
often** (one gcd computation, `start` offered at most once). -/
theorem phys5cls_out0_inf (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_P : ∀ o : Fin NO, CellPcls ch (srcV a b) o) (M : Nat) :
    ∃ t, M ≤ t ∧ riseB (ch out0).req t = true :=
  cls_sampled_inf ch _ out0 out0_sampled (H_CELLS_P _) M

/-! ## The gcd_hw witness run `chW` has finite event lists -/

def bnd : List Nat → Nat
  | [] => 0
  | a :: L => max (a + 1) (bnd L)

theorem lt_bnd : ∀ (L : List Nat) (x : Nat), x ∈ L → x < bnd L
  | [], x, h => by simp at h
  | a :: L, x, h => by
    simp only [bnd]
    rcases List.mem_cons.1 h with e | e
    · subst e; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_bnd L x e) (Nat.le_max_right _ _)

theorem bv_norise (L : List Nat) : ∀ t, bnd L ≤ t → riseB (Formal.Net.CapNet.Wit.bv L) t = false := by
  intro t ht
  have hn : t ∉ L := fun hm => by have := lt_bnd L t hm; omega
  simp [riseB, Formal.Net.CapNet.Wit.bv_st hn]

/-- Every channel of `chW` is offered only finitely often. -/
theorem chW_fin (c : Fin NC) : ∀ t, bnd (Formal.Net.CapNet.Wit.cdA c).rq ≤ t → riseB (Formal.Net.CapNet.Wit.chW c).req t = false :=
  bv_norise _

/-- **The hypothesis of `gcd_hw_circuit_safe_phys5_cls` fails on C-8t's run.** -/
theorem chW_not_cls : ¬ ∀ o : Fin NO, CellPcls Formal.Net.CapNet.Wit.chW (srcV 12 18) o := by
  intro h
  obtain ⟨t, ht, e⟩ := phys5cls_out0_inf 12 18 Formal.Net.CapNet.Wit.chW h (bnd (Formal.Net.CapNet.Wit.cdA out0).rq)
  rw [chW_fin out0 t ht] at e
  exact Bool.noConfusion e

/-- No channel of `chW` admits a `Row` (for any operator / ghost choice). -/
theorem chW_no_row {sv : Nat → Nat} {k : K NC} {w : Nat → Trace} (c : Fin NC) :
    ¬ Row Formal.Net.CapNet.Wit.chW sv k w c := by
  intro r
  obtain ⟨t, ht, e⟩ := row_inf r (bnd (Formal.Net.CapNet.Wit.cdA c).rq)
  rw [chW_fin c t ht] at e
  exact Bool.noConfusion e

/-- Every root certificate on `chW` is `exempt` (Held) in disguise. -/
theorem chW_bcert_is_held (c : Fin NC) (B : BCert (Formal.Net.CapNet.Wit.chW c)) : Held (Formal.Net.CapNet.Wit.chW c) :=
  bcert_fin_held (chW_fin c) B

end P12a

#print axioms P12a.txwin_inf
#print axioms P12a.bcert_fin_held
#print axioms P12a.phys5cls_out0_inf
#print axioms P12a.chW_not_cls
#print axioms P12a.chW_no_row
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe_phys2
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe_phys4
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe_phys5
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe_phys5_cls
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe_phys5_gen
#print axioms Formal.Net.CapNet.Gcd.fnOK_census
#print axioms Formal.Net.CapNet.Wit.gcd_hw_phys5_witness
#print axioms Formal.Net.CapstoneRefine.Wit.toy_row

/-! Independent census of the 176: which `fnOK` passes consult `Formal.Gen` at all. -/
open Formal.Net.CapNet.Gcd Formal.Net.OpsBusy3 in
#eval
  let ks := sampIds.map (fun c => (c, dpOf (ops.getD (prodT.getD c 0).val (Formal.Net.CapNet.K.sink 0))))
  (ks.length, (ks.filter (fun p => p.2 = DP.wire)).length, (ks.filter (fun p => p.2 = DP.shift)).length,
   (ks.filter (fun p => p.2 = DP.latch)).length, (ks.filter (fun p => p.2 = DP.dmux)).length,
   (ks.filter (fun p => p.2 = DP.open_)).length)
