import Formal.Core.XAudit.Design

/-!
# Formal.Core.XAudit.Fast — an array-based `XSim` simulator, proved equal to `XSim.val`

Probe A-xaudit. `XSim.hist` is written for the kernel: rows are lists and the
driver of a wire is found by `List.find?` over all gates, so one row costs
O(wires × gates + wires × window × pins × wires). That is fine for `decide`
on a cell and quadratic on a design (a 361-wire pipe takes 26 s for 2400
steps). `histF` computes the same rows with an `Array` driver table and
`Array` rows (O(wires × window × pins) per row).

* `histF_spec`: for every `s ≤ t` and wire `w`, entry `w` of row `s` of
  `histF … t` is `XSim.val gs u a0 s w`, provided every gate has `lo ≥ 1`
  (the hypothesis `XSim.sound` already needs).
* `auditF_eq`: so the executable may read its verdicts from `auditF`; every
  theorem of `Formal.Core.XAudit` about `audit` holds for it verbatim
  (`valF_sound`, `noXF_sound`).
-/

namespace Formal.Core.XAudit.Fast

open Formal.Core K3
open Formal.Core.XSim
open Formal.Core.TraceDiscrete (Sig)

variable {n : Nat}

/-- Read entry `i` of an array row (`X` out of range). -/
def rd (r : Array K3) (i : Nat) : K3 := r.getD i X

theorem rd_ofFn (f : Fin n → K3) (w : Fin n) : rd (Array.ofFn f) w.val = f w := by
  simp [rd, Array.getD, w.isLt]

/-- Driver table. -/
def drvArr (gs : List (LGate n)) : Array (Option (LGate n)) := Array.ofFn (driver gs)

theorem drvArr_get (gs : List (LGate n)) (w : Fin n) : (drvArr gs).getD w.val none = driver gs w := by
  simp [drvArr, Array.getD, w.isLt]

/-- The cell function on array rows. -/
def cellF (D : Array (Option (LGate n))) (u : Fin n → Nat → K3) (R : Nat → Array K3) (t : Nat)
    (w : Fin n) : K3 :=
  match D.getD w.val none with
  | none => u w t
  | some g => win g.lo g.hi (fun s => g.lut.keval (fun i => rd (R s) (g.ins i).val)) t

def row0F (D : Array (Option (LGate n))) (u : Fin n → Nat → K3) (a0 : Fin n → K3) : Array K3 :=
  Array.ofFn (fun w : Fin n => match D.getD w.val none with
    | none => u w 0
    | some _ => a0 w)

/-- `histF t = #[row 0, …, row t]`. -/
def histF (D : Array (Option (LGate n))) (u : Fin n → Nat → K3) (a0 : Fin n → K3) :
    Nat → Array (Array K3)
  | 0 => #[row0F D u a0]
  | t + 1 =>
      let h := histF D u a0 t
      h.push (Array.ofFn (cellF D u (fun s => h.getD s #[]) (t + 1)))

theorem histF_size (D : Array (Option (LGate n))) (u : Fin n → Nat → K3) (a0 : Fin n → K3) :
    ∀ t, (histF D u a0 t).size = t + 1
  | 0 => rfl
  | t + 1 => by simp [histF, histF_size D u a0 t]

theorem getD_push_lt {α : Type} (a : Array α) (x d : α) (s : Nat) (h : s < a.size) :
    (a.push x).getD s d = a.getD s d := by
  simp [Array.getD, h, Array.getElem_push, Nat.lt_succ_of_lt h]

theorem getD_push_eq {α : Type} (a : Array α) (x d : α) : (a.push x).getD a.size d = x := by
  simp [Array.getD]

theorem wmerge_congr (g g' : Nat → K3) (a : Nat) :
    ∀ m, (∀ j, j ≤ m → g (a + j) = g' (a + j)) → wmerge g a m = wmerge g' a m
  | 0, h => by simpa [wmerge] using h 0 (Nat.le_refl 0)
  | m + 1, h => by
      simp only [wmerge]
      rw [wmerge_congr g g' a m (fun j hj => h j (by omega))]
      have := h (m + 1) (Nat.le_refl _)
      rw [← Nat.add_assoc] at this
      rw [this]

theorem win_congr (lo hi : Nat) (g g' : Nat → K3) (t : Nat)
    (h : ∀ s, t - hi ≤ s → s ≤ (t - hi) + ((t - lo) - (t - hi)) → g s = g' s) :
    win lo hi g t = win lo hi g' t := by
  unfold win
  exact wmerge_congr g g' _ _ (fun j hj => h _ (by omega) (by omega))

/-- **The array simulator computes `XSim.val`.** -/
theorem histF_spec (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3)
    (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (hlh : ∀ g ∈ gs, g.lo ≤ g.hi) :
    ∀ t s, s ≤ t → ∀ w : Fin n, rd ((histF (drvArr gs) u a0 t).getD s #[]) w.val = val gs u a0 s w := by
  intro t
  induction t with
  | zero =>
      intro s hs w
      have : s = 0 := by omega
      subst this
      show rd (row0F (drvArr gs) u a0) w.val = _
      rw [row0F, rd_ofFn, val_zero, drvArr_get]
      cases driver gs w <;> rfl
  | succ t ih =>
      intro s hs w
      have hsz := histF_size (drvArr gs) u a0 t
      by_cases hst : s ≤ t
      · simp only [histF]
        rw [getD_push_lt _ _ _ _ (by omega)]
        exact ih s hst w
      have : s = t + 1 := by omega
      subst this
      have e : ∀ (r : Array K3), ((histF (drvArr gs) u a0 t).push r).getD (t + 1) #[] = r := by
        intro r; rw [← hsz]; exact getD_push_eq _ _ _
      simp only [histF]
      rw [e, rd_ofFn, val_succ]
      unfold cellF cell
      rw [drvArr_get]
      cases hd : driver gs w with
      | none => rfl
      | some g =>
          obtain ⟨hg, -⟩ := driver_some hd
          have := hlo g hg
          have := hlh g hg
          simp only
          apply win_congr
          intro s' h1 h2
          congr 1
          funext i
          rw [ih s' (by omega) (g.ins i), hist_getD gs u a0 t s' (by omega)]
          rfl

/-! ## The executable's entry points -/

open Formal.Core.XAudit

/-- What the executable computes (instead of `audit`). -/
def auditF (d : Design) (u : Fin d.n → Nat → K3) (T : Nat) : Array (Array K3) :=
  histF (drvArr (build d)) u a0X T

def valF (H : Array (Array K3)) (s w : Nat) : K3 := rd (H.getD s #[]) w

theorem auditF_eq (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T s : Nat) (hs : s ≤ T)
    (w : Fin d.n) : valF (auditF d u T) s w.val = valAt (audit d u T) T s w.val := by
  rw [valF, auditF, histF_spec _ _ _ (build_lo d hwf) (build_lohi d hwf) T s hs w,
    valAt_audit d u T s hs w]

/-- Soundness of the fast audit (from `audit_sound`). -/
theorem valF_sound (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) :
    ∀ s, s ≤ T → ∀ w : Fin d.n, valF (auditF d u T) s w.val ⊑ ofBool (x w s) := by
  intro s hs w
  rw [auditF_eq d hwf u T s hs w]
  exact audit_sound d hwf u T x hsat hin s hs w

/-- The X-free check on the fast rows. -/
def noXF (H : Array (Array K3)) (w t1 t2 : Nat) : Bool :=
  (List.range' t1 (t2 + 1 - t1)).all (fun s => valF H s w != X)

/-- **Meaning of "no X reported at `w` on `[t1, t2]`"** for the fast audit. -/
theorem noXF_sound (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (w : Fin d.n) (t1 t2 : Nat) (ht2 : t2 ≤ T) (h : noXF (auditF d u T) w.val t1 t2 = true)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) :
    ∀ s, t1 ≤ s → s ≤ t2 → x w s = pick (valF (auditF d u T) s w.val) := by
  intro s h1 h2
  simp only [noXF, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq] at h
  obtain ⟨v, hv⟩ := ne_X_iff.mp (h s ⟨h1, by omega⟩)
  rw [auditF_eq d hwf u T s (by omega) w] at hv ⊢
  rw [audit_binary d hwf u T x hsat hin s (by omega) w v hv, hv]
  cases v <;> rfl

/-- `rowsFixed` on the fast rows: rows `T - H .. T` all equal row `T`. -/
def rowsFixedF (H : Array (Array K3)) (T Hd : Nat) : Bool :=
  (List.range' (T - Hd) (Hd + 1)).all (fun s => H.getD s #[] == H.getD T #[])

theorem mkRow_length : ∀ (m : Nat) (f : Fin m → K3), (mkRow m f).length = m
  | 0, _ => rfl
  | m + 1, f => by simp [mkRow, mkRow_length m]

theorem arow_length (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3) :
    ∀ t, (arow gs u a0 t).length = n
  | 0 => mkRow_length _ _
  | t + 1 => by rw [arow_succ]; exact mkRow_length _ _

theorem arow_ext (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3) (s t : Nat)
    (h : ∀ w : Fin n, val gs u a0 s w = val gs u a0 t w) : arow gs u a0 s = arow gs u a0 t := by
  apply List.ext_getElem (by rw [arow_length, arow_length])
  intro i h1 h2
  have hi : i < n := by rw [arow_length] at h1; exact h1
  have := h ⟨i, hi⟩
  simp only [val, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

theorem rowsFixedF_spec (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (h : rowsFixedF (auditF d u T) T d.maxHi = true) :
    ∀ s, T - d.maxHi ≤ s → s ≤ T → arow (build d) u a0X s = arow (build d) u a0X T := by
  intro s h1 h2
  simp only [rowsFixedF, List.all_eq_true, List.mem_range'_1, beq_iff_eq] at h
  have e := h s ⟨h1, by omega⟩
  apply arow_ext
  intro w
  have hs := histF_spec (build d) u a0X (build_lo d hwf) (build_lohi d hwf) T s h2 w
  have hT := histF_spec (build d) u a0X (build_lo d hwf) (build_lohi d hwf) T T (Nat.le_refl _) w
  simp only [auditF] at e
  rw [← hs, ← hT, e]

/-- **Settled** (fast rows): inputs constant from `T ≥ 1`, the last
`maxHi + 1` fast rows equal ⇒ every binary value of row `T` holds in every
behaviour for all later time. -/
theorem settledF_forever (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat) (hT : 1 ≤ T)
    (hu : ∀ w, Undriven (build d) w → ∀ t, T ≤ t → u w t = u w T)
    (hfix : rowsFixedF (auditF d u T) T d.maxHi = true)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) (w : Fin d.n) (v : Bool)
    (hv : valF (auditF d u T) T w.val = ofBool v) : ∀ t, T ≤ t → x w t = v := by
  intro t ht
  have hs := val_stationary (build d) u a0X d.maxHi T hT (build_lo d hwf) (build_lohi d hwf)
    (build_hi d) hu (rowsFixedF_spec d hwf u T hfix) t w ht
  have hc := sound_circuit (build d) u a0X (build_lo d hwf) x hsat hin (fun _ _ => X_le _) t w
  rw [hs, ← valAt_audit d u T T (Nat.le_refl _) w, ← auditF_eq d hwf u T T (Nat.le_refl _) w, hv] at hc
  exact defined_eq hc rfl

end Formal.Core.XAudit.Fast
