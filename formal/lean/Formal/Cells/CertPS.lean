import Formal.Cells.RaceCertPS

/-!
# Formal.Cells.CertPS — a generic hold-certificate checker on THE target's gates

Shard B, 2026-11-07. Generalises `RaceCertPS.ack_holds_at` (one hand-assembled certificate) to any certificate: a
list of rows (`KRow`, checked by `krowOK`), each controlling pin labelled with where its source's hold comes from:
the cause, a static premise, or an EARLIER row.

## Problem, plainly
Show, in every behaviour of THE circuit, that a node keeps its value until a cause has propagated through a
certificate's rows, from a Boolean check of the certificate plus value premises on the cause, the static nodes, and
each memory row's own state before its hold starts.

## Proved (standard axioms)
* `win`: each row's hold window `[st, en]`, computed from the premise windows and the rows' routed pin bands
  (`st` = max of source starts + hi, `en` = min of source ends + lo).
* `cert_sound`: if every row passes `krowOK` and its labels (`labOK`: label kinds, earlier-row indices, the pin's
  source node and controlled value match the label), then every row's node shows its value on its window.

## Not shown
Which certificates exist (Python, ctlcert.py); the premises.
-/

namespace Formal.Cells.CertPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.RaceLinkPS Formal.Net.CViewPS
  Formal.Cells.ViewPS Formal.Cells.SpecFbChain Formal.Cells.SpecCElemFact Formal.Cells.RaceCertPS

instance : Inhabited KRow := ⟨⟨0, [], [], [], false, 0, false, [], []⟩⟩

/-- A label: kind 0 = the cause, 1 = static premise number `k`, 2 = earlier row number `k`. -/
structure Lab where
  kind : Nat
  k : Nat
  deriving Repr, Inhabited

structure CRow where
  r : KRow
  labs : List Lab   -- indexed by pin; read only at the pins of `r.P`

instance : Inhabited CRow := ⟨⟨default, []⟩⟩

def CRow.lab (row : CRow) (j : Nat) : Lab := row.labs.getD j default

/-- The premise data: cause node and value, static nodes and values. -/
structure Prem where
  cn : Nat
  cv : Bool
  sn : List Nat
  sv : List Bool

/-- Window of a label's source: cause `[a, e]`, static `k`: `[a, E k]`, row `k`: `W k`. -/
def srcWin (a e : Nat) (E : Nat → Nat) (W : Nat → Nat × Nat) (l : Lab) : Nat × Nat :=
  if l.kind = 0 then (a, e) else if l.kind = 1 then (a, E l.k) else W l.k

def BIG : Nat := 10 ^ 15

/-- A row's window, given the windows `W` of the rows it reads. -/
def rowWin (p : DelayPar) (c : ℚ) (a e : Nat) (E : Nat → Nat) (W : Nat → Nat × Nat) (row : CRow) : Nat × Nat :=
  (row.r.P.foldr (fun j m => max m ((srcWin a e E W (row.lab j)).1 + row.r.hi p c j)) (max a (row.r.S p)),
   row.r.P.foldr (fun j m => min m ((srcWin a e E W (row.lab j)).2 + row.r.lo p c j)) BIG)

/-- All windows, by row index (a row reads only rows before it). -/
def win (p : DelayPar) (c : ℚ) (a e : Nat) (E : Nat → Nat) (rows : List CRow) (i : Nat) : Nat × Nat :=
  rowWin p c a e E (fun k => if k < i then win p c a e E rows k else (a + 1, a)) (rows.getD i default)
termination_by i
decreasing_by assumption

/-- The label check of row `i`. -/
def labOK (P : Prem) (rows : List CRow) (i : Nat) (row : CRow) : Bool :=
  row.r.P.all fun j =>
    let l := row.lab j
    if l.kind = 0 then (row.r.pins.getD j ([], 0)).2 == P.cn && fl row.r.bv j == P.cv
    else if l.kind = 1 then decide (l.k < P.sn.length) && (row.r.pins.getD j ([], 0)).2 == P.sn.getD l.k 0 &&
      fl row.r.bv j == P.sv.getD l.k false
    else l.kind == 2 && decide (l.k < i) && (row.r.pins.getD j ([], 0)).2 == (rows.getD l.k default).r.q &&
      fl row.r.bv j == (rows.getD l.k default).r.w

def certOK (P : Prem) (rows : List CRow) : Bool :=
  (List.range rows.length).all fun i => krowOK (rows.getD i default).r && labOK P rows i (rows.getD i default)

theorem foldr_max_ge (f : Nat → Nat) (b : Nat) : ∀ (l : List Nat), (b ≤ l.foldr (fun j m => max m (f j)) b) ∧
    ∀ j ∈ l, f j ≤ l.foldr (fun j m => max m (f j)) b
  | [] => by simp
  | x :: l => by
    obtain ⟨h1, h2⟩ := foldr_max_ge f b l
    simp only [List.foldr_cons, List.mem_cons]
    refine ⟨le_trans h1 (le_max_left _ _), fun j hj => ?_⟩
    rcases hj with rfl | hj
    · exact le_max_right _ _
    · exact le_trans (h2 j hj) (le_max_left _ _)

theorem foldr_min_le (f : Nat → Nat) (b : Nat) : ∀ (l : List Nat), ∀ j ∈ l, l.foldr (fun j m => min m (f j)) b ≤ f j
  | [] => by simp
  | x :: l => by
    have h2 := foldr_min_le f b l
    simp only [List.foldr_cons, List.mem_cons]
    intro j hj
    rcases hj with rfl | hj
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (h2 j hj)

/-- **Certificates are sound.** If the certificate passes `certOK`, the cause shows `cv` on `[a, e]`, each static node
its value on `[a, E k]`, and each memory row its value on its feedback window before its hold starts, then every
row's node shows its value on its window `win i`, in this behaviour at this corner. -/
theorem cert_sound {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) (P : Prem)
    (rows : List CRow) (hok : certOK P rows = true)
    (G : ∀ i, i < rows.length → CGateOK p c (rows.getD i default).r.g (rows.getD i default).r.src
      (rows.getD i default).r.arcs ((rows.getD i default).r.S p) x)
    (a e : Nat) (E : Nat → Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x P.cn t = P.cv)
    (hstat : ∀ k, k < P.sn.length → ∀ t, a ≤ t → t ≤ E k → x (P.sn.getD k 0) t = P.sv.getD k false)
    (hmem : ∀ i, i < rows.length → (rows.getD i default).r.mem = true →
      1 ≤ (rows.getD i default).r.lo p c (rows.getD i default).r.fb ∧
      ∀ t, (win p c a e E rows i).1 ≤ t + (rows.getD i default).r.hi p c (rows.getD i default).r.fb →
        t < (win p c a e E rows i).1 → x (rows.getD i default).r.q t = (rows.getD i default).r.w) :
    ∀ i, i < rows.length → ∀ t, (win p c a e E rows i).1 ≤ t → t ≤ (win p c a e E rows i).2 →
      x (rows.getD i default).r.q t = (rows.getD i default).r.w := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hok' := hok
  simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hok'
  obtain ⟨hk, hl⟩ := hok' i hi
  set row := rows.getD i default with hrow
  set W : Nat → Nat × Nat := fun k => if k < i then win p c a e E rows k else (a + 1, a) with hW
  have hwin : win p c a e E rows i = rowWin p c a e E W row := by rw [win]
  obtain ⟨hP, -, -, -, -, -⟩ := krow_facts hb hk
  have hklen : row.r.g.k = row.r.pins.length := by
    simp only [krowOK, Bool.and_eq_true, beq_iff_eq] at hk; exact hk.1.1.1.1.1.1
  -- every controlling pin's source holds on its label's window
  have hsrc : ∀ j ∈ row.r.P, ∀ t, (srcWin a e E W (row.lab j)).1 ≤ t → t ≤ (srcWin a e E W (row.lab j)).2 →
      x (row.r.src j) t = fl row.r.bv j := by
    intro j hj t t1 t2
    have hjk := hP j hj
    rw [ksrc_eq row.r (by omega)]
    simp only [labOK, List.all_eq_true] at hl
    have hlj := hl j hj
    simp only [srcWin] at t1 t2
    by_cases k0 : (row.lab j).kind = 0
    · simp only [k0, if_true, Bool.and_eq_true, beq_iff_eq] at hlj t1 t2
      rw [hlj.1, hlj.2]; exact hcause t t1 t2
    · by_cases k1 : (row.lab j).kind = 1
      · simp only [k1, Nat.one_ne_zero, if_true, if_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlj t1 t2
        rw [hlj.1.2, hlj.2]; exact hstat _ hlj.1.1 t t1 t2
      · simp only [k0, k1, if_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlj t1 t2
        obtain ⟨⟨⟨-, hlt⟩, hq⟩, hv⟩ := hlj
        simp only [hW, hlt, if_true] at t1 t2
        rw [hq, hv]
        exact ih _ hlt (by have := (hok' _ (by omega)).1; omega) t t1 t2
  have hst := foldr_max_ge (fun j => (srcWin a e E W (row.lab j)).1 + row.r.hi p c j) (max a (row.r.S p)) row.r.P
  have hen := foldr_min_le (fun j => (srcWin a e E W (row.lab j)).2 + row.r.lo p c j) BIG row.r.P
  intro t t1 t2
  rw [hwin] at t1 t2
  simp only [rowWin] at t1 t2
  cases hm : row.r.mem
  · exact krow_set hb hk hm (G i hi) (fun j => (srcWin a e E W (row.lab j)).1) (fun j => (srcWin a e E W (row.lab j)).2)
      hsrc t (by have := hst.1; omega) (fun j hj => ⟨by have := hst.2 j hj; omega, by have := hen j hj; omega⟩)
  · obtain ⟨hlo, hpre⟩ := hmem i hi hm
    rw [hwin] at hpre
    simp only [rowWin] at hpre
    refine krow_mem hb hk hm (G i hi) hlo (by have := hst.1; omega) hpre (fun j hj u u1 u2 => ?_) t t1 t2
    exact hsrc j hj u (by have := hst.2 j hj; omega) (by have := hen j hj; omega)

end Formal.Cells.CertPS
