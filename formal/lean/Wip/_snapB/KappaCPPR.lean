import Formal.Cells.OnGcdArbKappa

/-!
# Probe Bshp: common path pessimism removal (CPPR) in the κ corner model

Shard B, 2026-10-29. Notes: `formal/notes/B-kappa-cppr.md`.

Every arbiter race condition of OnGcdArbKappa (A0 fork, RT2/RT2b, RT1/RT1b, the ArbPin2
handover / opposite-sense forms) compares two path delays, `ΣP + a ≤ ΣQ + b`. When both
paths start with the same physical arcs (a fork stem, the shared prefix of the r_k net),
A's model (`CornerNat`: one shared corner, each ARC ID within `1 ± κ` of its nominal) gives
an arc id ONE delay per realization, so the arc is the same number on both sides.

## Plain-language problem statement

**Assumed.** A's corner model (`Formal.Core.Substrate.CornerNat`: H_ENDPOINTS, H_AFFINE,
H_SHARED_CORNER, H_SCATTER κ); one delay per arc id per realization (H_ONE_DELAY, as in
Bk2/Bk3). For the data part: Bar's UNTRUSTED extraction as transcribed in OnGcdArbKappa
(lit reading: `F = FAST_MIN`, `S = SLOW_MAX`, fs), and the source files' path accounting
(OnGcdArbA0's `late/early/Rsrv/As/A1r/A2r`, OnGcdArbFix's `m1/m2` with the r prefix `cr`,
ArbPin2's `a_k, b_k, c5, c6`).

**Proved (generic, §1).**
* `allOK_net`: for ANY two arc-id lists, the form for every realization on the full lists is
  equivalent to the form on the lists with the common multiset removed one-for-one (`net`,
  i.e. the symmetric difference of the multisets): common arcs cancel exactly.
* `allOK_iff_gen_net` (H_DIV on the net lists): that is iff `GenOK` on the net lists, so
  **GenOK on the symmetric difference is the exact check**; `sandwich_net` without H_DIV.
* `genOK_full_iff`: `GenOK` on the full lists is `GenOK` on the net lists with the extra
  term `2·κ·C_s` (C = the common arcs' endpoint sum) on the data side, at each endpoint:
  the uncancelled check is pessimistic by EXACTLY `2κ·C_s` (`genOK_net_of_full`: sound
  direction). Strict: `naive_pessimistic` (real data).

**Proved (data, §2–§4).**
* `fulls_common` (decided): the common arc ids of the 18 un-netted conditions: forks `ac`,
  `dS_k` (the A0 stem, one A0 fall event); mA/nA `ac`, `dS_k`, `d12`; every r-side form the
  r_k prefix `cr_k` (one r_k edge); mP/nP nothing. `fulls_net`: netting them gives exactly
  OnGcdArbKappa's forms (up to order). So Bk3's forms ARE the CPPR forms.
* `design_cppr_safe` / `design_cppr_tight`: on the FULL conditions, with the r prefixes as
  arcs of ANY endpoints, every arbiter condition holds for κ ≤ 16587/374773 (≈ 0.0443) and
  the binding one fails from 33181/749546: **the threshold does not move** under the
  identities the data supports (they were already cancelled).
* `split_design_safe`, `split_fork2_safe/_unsafe`: if instead the two identifications that
  rest on EQUAL NUMBERS or on rise = fall, not on one physical event, are undone (`d12`
  traversed by the A0 fall in P and by the A0 rise in Q of mA/nA; 7g's H_ARC_C, ua_k's
  A0-pin and g-pin arcs, in the forks), the design minimum is still ≥ 0.0443; the moved rows
  stay ≥ 0.2004 (fork2, seed 4 merge12.uarb2, from 0.2165).

**NOT covered.** Shared physical sub-structure inside one LUT (two pin arcs to one output
share the late mux stages and the output driver; prjxray gives no split): only bracketed by
arithmetic in the note, not in Lean. The `cons` reading (side-dependent endpoints, not one
model when arcs are shared). Per-traversal scatter of one arc at different times. κ itself.
The r prefix delays (not in the extraction; the theorems hold for any value).
-/

namespace Formal.Cells.KappaCPPR

open Formal.Core.Substrate
open Formal.Cells.ConstraintsKappa

/-! ## 1. Generic: common arcs cancel exactly -/

section Generic

variable {A : Type}

theorem pathDelay_perm (d : A → ℕ) {p q : List A} (h : p.Perm q) :
    pathDelay d p = pathDelay d q := (h.map d).sum_nat

theorem sumOver_perm (f : A → ℕ) {p q : List A} (h : p.Perm q) :
    sumOver f p = sumOver f q := (h.map f).sum_nat

theorem sumOver_append (f : A → ℕ) (p q : List A) :
    sumOver f (p ++ q) = sumOver f p + sumOver f q := by
  unfold sumOver; rw [List.map_append, List.sum_append]

/-- The form only depends on the multisets of arc ids. -/
theorem allOK_perm (M : CornerModel A) {P P' Q Q' : List A} (a b : ℕ)
    (hP : P.Perm P') (hQ : Q.Perm Q') : AllOK M P Q a b ↔ AllOK M P' Q' a b := by
  constructor
  · intro h d hd; rw [← pathDelay_perm d hP, ← pathDelay_perm d hQ]; exact h d hd
  · intro h d hd; rw [pathDelay_perm d hP, pathDelay_perm d hQ]; exact h d hd

variable [DecidableEq A]

/-- **One-for-one cancellation.** `net P Q = (C, P', Q')`: `C` is the multiset intersection
(each occurrence of an id in `P` that still has a partner in `Q` is paired with one), `P'`
and `Q'` the rest. `(P', Q')` is the symmetric difference of the two multisets, split by side. -/
def net : List A → List A → List A × List A × List A
  | [], Q => ([], [], Q)
  | e :: P, Q =>
    if e ∈ Q then (e :: (net P (Q.erase e)).1, (net P (Q.erase e)).2.1, (net P (Q.erase e)).2.2)
    else ((net P Q).1, e :: (net P Q).2.1, (net P Q).2.2)

theorem net_P : ∀ P Q : List A, P.Perm ((net P Q).1 ++ (net P Q).2.1)
  | [], Q => by simp [net]
  | e :: P, Q => by
    by_cases h : e ∈ Q
    · simp only [net, if_pos h]
      exact (net_P P (Q.erase e)).cons e
    · simp only [net, if_neg h]
      exact ((net_P P Q).cons e).trans List.perm_middle.symm

theorem net_Q : ∀ P Q : List A, Q.Perm ((net P Q).1 ++ (net P Q).2.2)
  | [], Q => by simp [net]
  | e :: P, Q => by
    by_cases h : e ∈ Q
    · simp only [net, if_pos h]
      exact (List.perm_cons_erase h).trans ((net_Q P (Q.erase e)).cons e)
    · simp only [net, if_neg h]
      exact net_Q P Q

theorem net_sub : ∀ P Q : List A, (net P Q).2.2.Sublist Q
  | [], Q => by simp [net]
  | e :: P, Q => by
    by_cases h : e ∈ Q
    · simp only [net, if_pos h]
      exact (net_sub P (Q.erase e)).trans List.erase_sublist
    · simp only [net, if_neg h]
      exact net_sub P Q

/-- After netting no id is on both sides (H_DISJ holds by construction). -/
theorem net_disj : ∀ P Q : List A, Disj (net P Q).2.1 (net P Q).2.2
  | [], Q => by intro x hx; simp [net] at hx
  | e :: P, Q => by
    by_cases h : e ∈ Q
    · simp only [net, if_pos h]
      exact net_disj P (Q.erase e)
    · simp only [net, if_neg h]
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact fun hq => h ((net_sub P Q).subset hq)
      · exact net_disj P Q x hx

/-- **CPPR is exact.** The form on the full paths holds for every realization iff it holds
on the netted paths. -/
theorem allOK_net (M : CornerModel A) (P Q : List A) (a b : ℕ) :
    AllOK M P Q a b ↔ AllOK M (net P Q).2.1 (net P Q).2.2 a b :=
  (allOK_perm M a b (net_P P Q) (net_Q P Q)).trans (allOK_cancel M _ _ _ a b)

/-- **The exact check is GenOK on the symmetric difference** (H_DIV on the net lists). -/
theorem allOK_iff_gen_net (M : CornerModel A) (P Q : List A) (a b : ℕ)
    (H_DIV : DivOK M (net P Q).2.1 (net P Q).2.2) :
    AllOK M P Q a b ↔ GenOK M.κ (M.path (net P Q).2.1) (M.path (net P Q).2.2) a b :=
  (allOK_net M P Q a b).trans (allOK_iff_gen M (net_disj P Q) H_DIV)

/-- Without H_DIV: GenOK on the net lists is sufficient, and necessary up to one ps of
rounding per NET arc. -/
theorem sandwich_net (M : CornerModel A) (P Q : List A) (a b : ℕ) :
    (GenOK M.κ (M.path (net P Q).2.1) (M.path (net P Q).2.2) a b → AllOK M P Q a b) ∧
    (AllOK M P Q a b → ∀ s : Bool, M.κ.hi * ep s (M.path (net P Q).2.1) + M.κ.den * a ≤
      M.κ.lo * ep s (M.path (net P Q).2.2) + M.κ.den * b +
        ((net P Q).2.1.length + (net P Q).2.2.length) * (M.κ.den - 1)) := by
  have h := sandwich M (a := a) (b := b) (net_disj P Q)
  exact ⟨fun g => (allOK_net M P Q a b).2 (h.1 g), fun g => h.2 ((allOK_net M P Q a b).1 g)⟩

theorem ep_split_P (M : CornerModel A) (P Q : List A) (s : Bool) :
    ep s (M.path P) = ep s (M.path (net P Q).1) + ep s (M.path (net P Q).2.1) := by
  rw [path_ep, path_ep, path_ep, sumOver_perm _ (net_P P Q), sumOver_append]

theorem ep_split_Q (M : CornerModel A) (P Q : List A) (s : Bool) :
    ep s (M.path Q) = ep s (M.path (net P Q).1) + ep s (M.path (net P Q).2.2) := by
  rw [path_ep, path_ep, path_ep, sumOver_perm _ (net_Q P Q), sumOver_append]

/-- **The pessimism of the uncancelled check, exactly.** GenOK on the full lists is GenOK on
the netted lists with `2·num·C_s` added to the data side (`C_s` = endpoint sum of the common
arcs), i.e. `2κ·C_s` ps, at each endpoint. -/
theorem genOK_full_iff (M : CornerModel A) (P Q : List A) (a b : ℕ) :
    GenOK M.κ (M.path P) (M.path Q) a b ↔ ∀ s : Bool,
      M.κ.hi * ep s (M.path (net P Q).2.1) + 2 * (M.κ.num * ep s (M.path (net P Q).1)) +
          M.κ.den * a ≤ M.κ.lo * ep s (M.path (net P Q).2.2) + M.κ.den * b := by
  rw [genOK_iff_ep]
  apply forall_congr'
  intro s
  rw [ep_split_P M P Q s, ep_split_Q M P Q s]
  have hk : M.κ.hi = M.κ.lo + 2 * M.κ.num := by
    have := M.κ.lo_add; unfold Kappa.hi; omega
  rw [hk]
  generalize ep s (M.path (net P Q).1) = c
  generalize ep s (M.path (net P Q).2.1) = x
  generalize ep s (M.path (net P Q).2.2) = y
  generalize M.κ.lo = l
  generalize M.κ.num = n
  generalize M.κ.den = dn
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

/-- The uncancelled check is sound but pessimistic: it implies the netted one. -/
theorem genOK_net_of_full (M : CornerModel A) (P Q : List A) (a b : ℕ)
    (h : GenOK M.κ (M.path P) (M.path Q) a b) :
    GenOK M.κ (M.path (net P Q).2.1) (M.path (net P Q).2.2) a b := by
  rw [genOK_iff_ep]
  intro s
  have := (genOK_full_iff M P Q a b).1 h s
  omega

end Generic

/-! ## 2. The routed gcd_hw conditions: which arcs are shared, by identity -/

open Formal.Cells.OnGcdArbKappa

/-- Arc ids of the un-netted conditions: Bar's elements, plus the r_k net prefixes before
the ugrant/ustate branch point (`cr1`, `cr2`; one routed wire each, H_R_SHARED/H_R_SPLIT;
their delays were NOT extracted, so the theorems below take them as arbitrary arcs). -/
inductive X
  | e (x : E)
  | cr1
  | cr2
  deriving DecidableEq, Repr

/-- The lit arcs, with arbitrary r-prefix arcs `cr false`, `cr true`. -/
def xArc (v : E → Quad) (cr : Bool → CArc) : X → CArc
  | .e x => mkArc (v x).1 (v x).2.2.2
  | .cr1 => cr false
  | .cr2 => cr true

def xModel (k : Kappa) (v : E → Quad) (cr : Bool → CArc) : CornerModel X := ⟨xArc v cr, k⟩

/-- Embed an E-list. -/
def ee (l : List E) : List X := l.map X.e

theorem xpath_e (k : Kappa) (v : E → Quad) (cr : Bool → CArc) (L : List E) :
    (xModel k v cr).path (ee L) = (litModel k v).path L := by
  simp only [CornerModel.path, ee, List.map_map]; rfl

theorem xpd_e (d : X → ℕ) (L : List E) : pathDelay d (ee L) = pathDelay (fun x => d (X.e x)) L := by
  simp only [pathDelay, ee, List.map_map]; rfl

theorem x_restrict {k : Kappa} {v : E → Quad} {cr : Bool → CArc} {d : X → ℕ}
    (h : (xModel k v cr).Realizes d) : (litModel k v).Realizes (fun x => d (X.e x)) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x => hc (X.e x)⟩

theorem allOK_lift {k : Kappa} {v : E → Quad} {cr : Bool → CArc} {P Q : List E} {a b : ℕ}
    (h : AllOK (litModel k v) P Q a b) : AllOK (xModel k v cr) (ee P) (ee Q) a b := by
  intro d hd
  rw [xpd_e, xpd_e]
  exact h _ (x_restrict hd)

theorem disj_lift {P Q : List E} (h : Disj P Q) : Disj (ee P) (ee Q) := by
  intro x hx hq
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨z, hz, hzy⟩ := List.mem_map.1 hq
  cases hzy
  exact h _ hy hz

/-- The source files' path pieces (OnGcdArbA0): the A0 route to ustate `As`, to ua1 `A1r`,
to ua2 `A2r` (each through the shared stem `ac`), and `Rsrv` = A0 → ustate → q → R0. -/
def Asl : List E := [.ac, .dS1, .dS2, .es, .ps]
def A1l : List E := [.ac, .dS1, .d12, .e1, .p1]
def A2l : List E := [.ac, .dS2, .d12, .e2, .p2]
def Rsl : List E := Asl ++ [.aq, .cq, .qs, .aRq]

/-- A condition before netting: the netted form of OnGcdArbKappa and the full paths. -/
structure Full where
  f : Form
  P : List X
  Q : List X

/-- The binding condition (seed 3 merge12.uarb1, RT1b server-free), un-netted. -/
def uRT1b : Full := ⟨F_rt1b, .cr2 :: ee [.rg2, .ag2r], .cr2 :: ee [.rs2, .aR2, .qgw, .pqg, .ag1q]⟩

/-- The 18 conditions, un-netted, transcribed from their definitions:
* forks (OnGcdArbA0 `late_k/early_k`, 7g): both paths from the A0 driver, prefix `c`
  = `ac + dS_k` (`fdl_k`) on both sides;
* RT2 (`mP mG mA mGG`, 7h) and RT2b (`nP nG nA nGG`, 7j) with `srv` for each server
  credit (`smin`, `2·smin`), the r_k prefix on both sides where both r_k branches occur
  (`Real7`: only `wr_kg − wr_ks` is fixed);
* RT1/RT1b (OnGcdArbFix `m1/m2`, server-free) and RT1s/RT1bs (with `wa0s = As`,
  `qf = aq`, `cq`, `srv`), r_k prefix `cr` on both sides (`Real1/Real2`);
* ArbPin2 (`B_k ≤ a_k + c_{5,6}`, `+1` in o1x/o2x), r_k prefix on both sides (H_R_SPLIT). -/
def fulls : List Full := [
  ⟨F_fork1, ee [.ac, .dS1, .d12, .e1, .p1],
    ee [.ac, .dS1, .dS2, .es, .ps, .aq, .cq, .qgw, .pqg, .ag1q, .gw1, .pg1]⟩,
  ⟨F_fork2, ee [.ac, .dS2, .d12, .e2, .p2],
    ee [.ac, .dS2, .dS1, .es, .ps, .aq, .cq, .qgw, .pqg, .ag2, .gw2, .pg2]⟩,
  ⟨F_mP, ee [.ac1, .fa1], ee (Rsl ++ [.srv])⟩,
  ⟨F_mG, .cr1 :: ee [.rg1, .ag1r, .gw1, .pg1, .ac1, .fa1],
    .cr1 :: ee ([.rs1, .aR1] ++ Rsl ++ [.srv] ++ A1l ++ [.srv])⟩,
  ⟨F_mA, ee (A1l ++ [.ac1]), ee (Rsl ++ [.srv] ++ A2l ++ [.ac2])⟩,
  ⟨F_mGG, .cr1 :: ee [.rg1, .ag1r, .gw1, .pg1, .ac1],
    .cr1 :: ee ([.rs1, .aR1] ++ Rsl ++ [.srv] ++ A2l ++ [.ac2, .srv])⟩,
  ⟨F_nP, ee [.ac2, .fa2], ee (Rsl ++ [.srv])⟩,
  ⟨F_nG, .cr2 :: ee [.rg2, .ag2r, .gw2, .pg2, .ac2, .fa2],
    .cr2 :: ee ([.rs2, .aR2] ++ Rsl ++ [.srv] ++ A2l ++ [.srv])⟩,
  ⟨F_nA, ee (A2l ++ [.ac2]), ee (Rsl ++ [.srv] ++ A1l ++ [.ac1])⟩,
  ⟨F_nGG, .cr2 :: ee [.rg2, .ag2r, .gw2, .pg2, .ac2],
    .cr2 :: ee ([.rs2, .aR2] ++ Rsl ++ [.srv] ++ A1l ++ [.ac1, .srv])⟩,
  ⟨F_rt1, .cr1 :: ee [.rg1, .ag1r], .cr1 :: ee [.rs1, .aR1, .qgw, .pqg, .ag2]⟩,
  uRT1b,
  ⟨F_rt1s, .cr1 :: ee [.rg1, .ag1r],
    .cr1 :: ee ([.rs1, .aR1, .qgw, .pqg, .ag2] ++ Asl ++ [.aq, .cq, .srv])⟩,
  ⟨F_rt1bs, .cr2 :: ee [.rg2, .ag2r],
    .cr2 :: ee ([.rs2, .aR2, .qgw, .pqg, .ag1q] ++ Asl ++ [.aq, .cq, .srv])⟩,
  ⟨F_h12, .cr1 :: ee [.rg1, .ag1r], .cr1 :: ee [.rs1, .aq, .cq, .qgw, .pqg, .ag2]⟩,
  ⟨F_h21, .cr2 :: ee [.rg2, .ag2r], .cr2 :: ee [.rs2, .aq, .cq, .qgw, .pqg, .ag1q]⟩,
  ⟨F_o1x, .cr2 :: ee [.rg2, .ag2r], .cr2 :: ee [.rs2, .aq, .cq, .qgw, .pqg, .ag2]⟩,
  ⟨F_o2x, .cr1 :: ee [.rg1, .ag1r], .cr1 :: ee [.rs1, .aq, .cq, .qgw, .pqg, .ag1q]⟩]

theorem fulls_forms : fulls.map Full.f = forms := rfl

/-- **Which conditions share arcs (by id), and which ones.** -/
theorem fulls_common : fulls.map (fun u => (net u.P u.Q).1) =
    [ee [.ac, .dS1], ee [.ac, .dS2], [], [.cr1], ee [.ac, .dS1, .d12], [.cr1], [], [.cr2],
      ee [.ac, .dS2, .d12], [.cr2], [.cr1], [.cr2], [.cr1], [.cr2], [.cr1], [.cr2], [.cr2],
      [.cr1]] := by decide +kernel

/-- **Netting the full conditions gives exactly OnGcdArbKappa's forms** (up to order). -/
theorem fulls_net : fulls.all (fun u => (net u.P u.Q).2.1.isPerm (ee u.f.P) &&
    (net u.P u.Q).2.2.isPerm (ee u.f.Q)) = true := by decide +kernel

theorem full_iff {u : Full} (hu : u ∈ fulls) (M : CornerModel X) (a b : ℕ) :
    AllOK M u.P u.Q a b ↔ AllOK M (ee u.f.P) (ee u.f.Q) a b := by
  have h := List.all_eq_true.1 fulls_net u hu
  simp only [Bool.and_eq_true, List.isPerm_iff] at h
  exact (allOK_net M u.P u.Q a b).trans (allOK_perm M a b h.1 h.2)

/-! ## 3. Thresholds with shared arcs cancelled: unchanged -/

/-- **Design headline (lit, CPPR).** For every arbiter, every condition in its FULL form,
every r-prefix arc `cr` (any endpoints) and every κ ≤ 16587/374773 ≈ 0.0443: the condition
holds on every realization of A's model. -/
theorem design_cppr_safe {v : E → Quad} (hv : v ∈ arbs) {u : Full} (hu : u ∈ fulls)
    (k : Kappa) (H_KAPPA : k.num * 374773 ≤ k.den * 16587) (cr : Bool → CArc) :
    AllOK (xModel k v cr) u.P u.Q u.f.a u.f.b := by
  rw [full_iff hu]
  apply allOK_lift
  have hf : u.f ∈ forms := by rw [← fulls_forms]; exact List.mem_map.2 ⟨u, hu, rfl⟩
  have hc := List.all_eq_true.1 (List.all_eq_true.1 arbs_cert v hv) u.f hf
  have := form_safe (by decide) hc k H_KAPPA
  rwa [model_lit] at this

theorem uRT1b_mem : uRT1b ∈ fulls := List.mem_of_getElem? (i := 11) rfl

/-- **And tight**: from κ ≥ 33181/749546 (≈ 0.044267) the binding FULL condition fails on
some realization, whatever the r2 prefix arc. So the CPPR threshold is 0.0443, as in Bk3. -/
theorem design_cppr_tight (k : Kappa) (H_KAPPA : k.den * 33181 ≤ k.num * 749546)
    (cr : Bool → CArc) :
    ¬ AllOK (xModel k v_g3_merge12_uarb1 cr) uRT1b.P uRT1b.Q 0 0 := by
  rw [full_iff uRT1b_mem]
  intro h
  have hd : Disj (ee F_rt1b.P) (ee F_rt1b.Q) := disj_lift (disj_of F_rt1b (by decide))
  have hrel := (sandwich (xModel k v_g3_merge12_uarb1 cr) hd).2 h false
  rw [xpath_e, xpath_e] at hrel
  have hcu : R_g3_merge12_uarb1_lit_rt1b.certUnsafe = true := by decide
  unfold Row.certUnsafe at hcu
  simp only [decide_eq_true_eq] at hcu
  have e1 : (litModel k v_g3_merge12_uarb1).path F_rt1b.P = R_g3_merge12_uarb1_lit_rt1b.D := rfl
  have e2 : (litModel k v_g3_merge12_uarb1).path F_rt1b.Q = R_g3_merge12_uarb1_lit_rt1b.R := rfl
  have e3 : (ee F_rt1b.P).length + (ee F_rt1b.Q).length = R_g3_merge12_uarb1_lit_rt1b.n := rfl
  rw [e1, e2, e3] at hrel
  exact unsafe_arith (by decide) (by decide) k.den_pos k.num_le H_KAPPA hcu hrel

/-- Non-vacuity: κ = 16587/374773 meets `H_KAPPA`, and every `xModel` is realised (at the
fast endpoint), whatever `cr`. -/
theorem design_cppr_nonvacuous :
    ∃ k : Kappa, k.num * 374773 ≤ k.den * 16587 ∧ ∀ (v : E → Quad) (cr : Bool → CArc),
      (xModel k v cr).Realizes (fun e => ((xModel k v cr).arc e).F) :=
  ⟨⟨16587, 374773, by decide, by decide⟩, Nat.le_refl _, fun _ _ => ⟨_, realizes_fast _⟩⟩

/-! ### The uncancelled check is strictly pessimistic (real data) -/

/-- **`naive_pessimistic`.** Seed d merge9.uarb1, client-1 A0 fork, κ = 1/5: GenOK on the
FULL paths (stem `ac + dS1` charged on both sides) fails, while the condition holds on every
realization (CPPR GenOK passes). The full check's own threshold there is ≈ 0.0934, the
CPPR one ≈ 0.5007 (note). -/
theorem naive_pessimistic :
    ¬ GenOK k5 ((litModel k5 v_gd_merge9_uarb1).path [.ac, .dS1, .d12, .e1, .p1])
        ((litModel k5 v_gd_merge9_uarb1).path
          [.ac, .dS1, .dS2, .es, .ps, .aq, .cq, .qgw, .pqg, .ag1q, .gw1, .pg1]) 0 0 ∧
      AllOK (litModel k5 v_gd_merge9_uarb1) [.ac, .dS1, .d12, .e1, .p1]
        [.ac, .dS1, .dS2, .es, .ps, .aq, .cq, .qgw, .pqg, .ag1q, .gw1, .pg1] 0 0 := by
  refine ⟨by decide, ?_⟩
  rw [allOK_net]
  have hp : (net [E.ac, .dS1, .d12, .e1, .p1]
      [E.ac, .dS1, .dS2, .es, .ps, .aq, .cq, .qgw, .pqg, .ag1q, .gw1, .pg1]).2.1.Perm F_fork1.P := by
    decide
  have hq : (net [E.ac, .dS1, .d12, .e1, .p1]
      [E.ac, .dS1, .dS2, .es, .ps, .aq, .cq, .qgw, .pqg, .ag1q, .gw1, .pg1]).2.2.Perm F_fork1.Q := by
    decide
  rw [allOK_perm _ 0 0 hp hq]
  have hc : certFor .lit F_fork1 v_gd_merge9_uarb1 1 5 = true := by decide
  have := form_safe (by decide) hc k5 (by decide)
  rw [model_lit] at this
  exact this

/-! ## 4. Identifications that rest on equal numbers or rise = fall, undone -/

/-- Split ids: `f x` is Bar's arc `x`; `s x` is a DIFFERENT physical arc with the same prjxray
numbers (the A0-rise traversal of a wire whose P-side use is the A0 fall; or the other input
pin's arc of the same LUT output). -/
inductive Y
  | f (x : E)
  | s (x : E)
  deriving DecidableEq, Repr

def yArc (v : E → Quad) : Y → CArc
  | .f x => mkArc (v x).1 (v x).2.2.2
  | .s x => mkArc (v x).1 (v x).2.2.2

def yModel (k : Kappa) (v : E → Quad) : CornerModel Y := ⟨yArc v, k⟩

def fs (l : List E) : List Y := l.map Y.f
def ss (l : List E) : List Y := l.map Y.s

/-- The four conditions whose netting used an identity not backed by one physical event:
* mA / nA: the Q side's `A2r` (`A1r`) is the A0 RISE reaching ua2 (ua1) after the server;
  the P side's `A1r` (`A2r`) is the A0 FALL. `ac`, `dS_k` still pair with the fall copy in
  `Rsrv`; `d12` does not (per-edge reading);
* forks: 7g's H_ARC_C makes ua_k's A0-pin arc and grant-pin arc one arc (equal numbers,
  checked by Bar); here they are two (A0 pin on the late side, g pin on the early side). -/
def splits : List (List Y × List Y) := [
  (fs (A1l ++ [.ac1]), fs (Rsl ++ [.srv]) ++ ss A2l ++ fs [.ac2]),
  (fs (A2l ++ [.ac2]), fs (Rsl ++ [.srv]) ++ ss A1l ++ fs [.ac1]),
  (fs [.ac, .dS1, .d12, .e1, .p1, .ac1],
    fs [.ac, .dS1, .dS2, .es, .ps, .aq, .cq, .qgw, .pqg, .ag1q, .gw1, .pg1] ++ ss [.ac1]),
  (fs [.ac, .dS2, .d12, .e2, .p2, .ac2],
    fs [.ac, .dS2, .dS1, .es, .ps, .aq, .cq, .qgw, .pqg, .ag2, .gw2, .pg2] ++ ss [.ac2])]

/-- Their common ids now: mA/nA lose `d12`, the forks keep only the stem. -/
theorem splits_common : splits.map (fun u => (net u.1 u.2).1) =
    [fs [.ac, .dS1], fs [.ac, .dS2], fs [.ac, .dS1], fs [.ac, .dS2]] := by decide +kernel

/-- Closed-form endpoint certificate `κ ≤ p/q` on two arcs (cf. OnGcdArbKappa.certFor). -/
def certG (D R : CArc) (a b p q : ℕ) : Bool :=
  decide (p * (ep false R + ep false D) + q * (ep false D + a) ≤ q * (ep false R + b)) &&
  decide (p * (ep true R + ep true D) + q * (ep true D + a) ≤ q * (ep true R + b))

theorem gen_of_certG {k : Kappa} {D R : CArc} {a b p q : ℕ} (hq : 0 < q)
    (hc : certG D R a b p q = true) (H_KAPPA : k.num * q ≤ k.den * p) : GenOK k D R a b := by
  unfold certG at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [genOK_iff_ep]
  intro s
  cases s
  · exact safe_arith hq k.num_le H_KAPPA hc.1
  · exact safe_arith hq k.num_le H_KAPPA hc.2

/-- Unsafe certificate at endpoint `s`: `pu/qu ≥ (R_s + b − D_s − a + n)/(R_s + D_s)`. -/
def certGU (D R : CArc) (a b n pu qu : ℕ) (s : Bool) : Bool :=
  decide (qu * (ep s R + b + n) ≤ pu * (ep s R + ep s D) + qu * (ep s D + a))

theorem split_safe {v : E → Quad} {P Q : List Y} {a b p q : ℕ} (hq : 0 < q)
    (hc : certG (pathArc ((net P Q).2.1.map (yArc v))) (pathArc ((net P Q).2.2.map (yArc v)))
      a b p q = true)
    (k : Kappa) (H_KAPPA : k.num * q ≤ k.den * p) : AllOK (yModel k v) P Q a b :=
  (sandwich_net (yModel k v) P Q a b).1 (gen_of_certG hq hc H_KAPPA)

theorem split_unsafe {v : E → Quad} {P Q : List Y} {a b pu qu : ℕ} {s : Bool} (hqu : 0 < qu)
    (hn : 0 < (net P Q).2.1.length + (net P Q).2.2.length)
    (hc : certGU (pathArc ((net P Q).2.1.map (yArc v))) (pathArc ((net P Q).2.2.map (yArc v)))
      a b ((net P Q).2.1.length + (net P Q).2.2.length) pu qu s = true)
    (k : Kappa) (H_KAPPA : k.den * pu ≤ k.num * qu) : ¬ AllOK (yModel k v) P Q a b := by
  intro h
  have hrel := (sandwich_net (yModel k v) P Q a b).2 h s
  unfold certGU at hc
  simp only [decide_eq_true_eq] at hc
  exact unsafe_arith hqu hn k.den_pos k.num_le H_KAPPA hc hrel

/-- Every split condition is certified at the design threshold on all 36 arbiters. -/
theorem splits_cert : arbs.all (fun v => splits.all (fun u =>
    certG (pathArc ((net u.1 u.2).2.1.map (yArc v))) (pathArc ((net u.1 u.2).2.2.map (yArc v)))
      0 0 16587 374773)) = true := by decide +kernel

/-- **The design minimum does not drop when the two number-based identifications are
undone**: every split condition holds on every realization for κ ≤ 16587/374773. -/
theorem split_design_safe {v : E → Quad} (hv : v ∈ arbs) {u : List Y × List Y} (hu : u ∈ splits)
    (k : Kappa) (H_KAPPA : k.num * 374773 ≤ k.den * 16587) : AllOK (yModel k v) u.1 u.2 0 0 :=
  split_safe (by decide) (List.all_eq_true.1 (List.all_eq_true.1 splits_cert v hv) u hu) k H_KAPPA

/-- The fork-2 split of seed 4 merge12.uarb2 (the lowest moved row). -/
def uF2 : List Y × List Y :=
  (fs [.ac, .dS2, .d12, .e2, .p2, .ac2],
    fs [.ac, .dS2, .dS1, .es, .ps, .aq, .cq, .qgw, .pqg, .ag2, .gw2, .pg2] ++ ss [.ac2])

/-- Without H_ARC_C its threshold is 121144/604431 ≈ 0.20043 (with it, Bk3: ≈ 0.2165). -/
theorem split_fork2_safe (k : Kappa) (H_KAPPA : k.num * 604431 ≤ k.den * 121144) :
    AllOK (yModel k v_g4_merge12_uarb2) uF2.1 uF2.2 0 0 :=
  split_safe (by decide) (by decide +kernel) k H_KAPPA

theorem split_fork2_unsafe (k : Kappa) (H_KAPPA : k.den * 242303 ≤ k.num * 1208862) :
    ¬ AllOK (yModel k v_g4_merge12_uarb2) uF2.1 uF2.2 0 0 :=
  split_unsafe (s := false) (by decide) (by decide +kernel) (by decide +kernel) k H_KAPPA

/-- Non-vacuity of the split statements: the bounds are meetable and `yModel` is realised. -/
theorem split_nonvacuous :
    (∃ k : Kappa, k.num * 604431 ≤ k.den * 121144) ∧
    (∃ k : Kappa, k.den * 242303 ≤ k.num * 1208862) ∧
    ∀ (k : Kappa) (v : E → Quad), (yModel k v).Realizes (fun e => ((yModel k v).arc e).F) :=
  ⟨⟨⟨121144, 604431, by decide, by decide⟩, Nat.le_refl _⟩,
    ⟨⟨242303, 1208862, by decide, by decide⟩, Nat.le_refl _⟩, fun _ _ => ⟨_, realizes_fast _⟩⟩

end Formal.Cells.KappaCPPR
