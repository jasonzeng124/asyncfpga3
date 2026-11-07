import Formal.Net.OpsBusy2Held

/-!
# Probe C-8x4: handshake halves, per-channel data fields, and the re-labelling toolkit

C-8x2's relaxed cell `CellB` mixes two kinds of facts: the HANDSHAKE fields (wires, C-elements,
the select LUTs, which read only the handshake wires and the INPUT buses) and one DATA field per
output channel ("while this output is busy its bus is the cell function of the inputs"). C-8x4
derives the data fields of sampled channels from tcheck rows; for that the two halves must be
separable, per channel. Here:

* `CellW ch sv k w`: `CellB` with the internal witnesses explicit (`w 0`, `w 1`: the mux
  C-elements / the arbiter grants / the link enable; the whole `w` for the 3-input mux).
  `cellB_iff`: `CellB ch sv k ↔ ∃ w, CellW ch sv k w`.
* `fnOf sv k v b`: the cell's data function on an input snapshot (`v` = input buses, `b` = the
  arbiter's index bit `won`); `fval` = `fnOf` on the trace at `t`; `fcond` = the extra premise of
  the 3-input mux field (select < 3).
* `FieldOf ch sv k w c`: the data field of output `c` alone (for a link: the open and the hold
  field). `zdD`: the zero-delay output bus (`fval`; the latch content `latchD` for a link).
* **`HS ch sv k w`** (the handshake half): `CellW` on the trace whose OUTPUT buses are replaced by
  their zero-delay values (`modC ch k.outsC (zdD ..)`). Since no handshake field reads an output
  bus, this says exactly "the handshake fields hold" (for `Disj` cells).
* `cellW_reb` (the one transfer lemma): the handshake fields survive any change of the buses
  that keeps the input buses; the data fields are then supplied per output.
  Corollaries: `hs_of_cellW` (relaxed cell ⇒ handshake half), **`cellW_of_hs`** (handshake half
  + every output's field ⇒ relaxed cell), `cellW_modS` (handshake half + the fields of the
  outputs outside `S` ⇒ relaxed cell once the outputs in `S` are re-labelled).
* **`hs_protoT`**: the bounded protocol spec `OpProtoT` from the handshake half alone.
* **`hs_heldT_one`**: bounded structural bundling of ONE output from that output's field (the
  other outputs of the same operator may have no field yet).
-/

namespace Formal.Net.OpsBusy3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.OpsBusy2

variable {n : Nat}

/-! ## Relaxed cells with explicit witnesses -/

/-- `CellB` with its internal witnesses explicit. -/
def CellW (ch : Fin n → Chan) (sv : Nat → Nat) : K n → (Nat → Trace) → Prop
  | .forkG i os, _ => ForkB (ch i) (os.map ch)
  | .forkH i os _ _ _ _, _ => ForkB (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _, _ => JoinB (jg e js) (ins.map ch) (ch o)
  | .bjoin ins o ec ed, _ => JoinB (bg ec ed) (ins.map ch) (ch o)
  | .steerC j t f, _ => SteerB sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _, _ =>
      SteerB sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _, w => MuxB sel2 (ch x) (ch y) (ch c) (ch z) (w 0) (w 1)
  | .muxn c x0 x1 x2 z _, w => MuxNB selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) w
  | .amerge x y z _, w => AMergeB (ch x) (ch y) (ch z) (w 0) (w 1)
  | .link i o, w => LinkB (ch i) (ch o) (w 0)
  | .src z which _, _ => SrcB (ch z) (sv which)
  | .sink i, _ => Ops.Gcd.Sink (ch i)

/-- Two traces as a witness family. -/
def w2 (a b : Trace) : Nat → Trace
  | 0 => a
  | _ => b

theorem cellB_of_W {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (h : CellW ch sv k w) : CellB ch sv k := by
  cases k with
  | mux c x y z mw => exact ⟨w 0, w 1, h⟩
  | muxn c x0 x1 x2 z nw => exact ⟨w, h⟩
  | amerge x y z ww => exact ⟨w 0, w 1, h⟩
  | link i o => exact ⟨w 0, h⟩
  | forkG => exact h
  | forkH => exact h
  | join => exact h
  | bjoin => exact h
  | steerC => exact h
  | steerD => exact h
  | src => exact h
  | sink => exact h

theorem W_of_cellB {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} (h : CellB ch sv k) :
    ∃ w, CellW ch sv k w := by
  cases k with
  | mux c x y z mw => obtain ⟨j0, j1, M⟩ := h; exact ⟨w2 j0 j1, M⟩
  | muxn c x0 x1 x2 z nw => obtain ⟨j, M⟩ := h; exact ⟨j, M⟩
  | amerge x y z ww => obtain ⟨g1, g2, M⟩ := h; exact ⟨w2 g1 g2, M⟩
  | link i o => obtain ⟨c, L⟩ := h; exact ⟨fun _ => c, L⟩
  | forkG => exact ⟨fun _ _ => false, h⟩
  | forkH => exact ⟨fun _ _ => false, h⟩
  | join => exact ⟨fun _ _ => false, h⟩
  | bjoin => exact ⟨fun _ _ => false, h⟩
  | steerC => exact ⟨fun _ _ => false, h⟩
  | steerD => exact ⟨fun _ _ => false, h⟩
  | src => exact ⟨fun _ _ => false, h⟩
  | sink => exact ⟨fun _ _ => false, h⟩

theorem cellB_iff (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) :
    CellB ch sv k ↔ ∃ w, CellW ch sv k w :=
  ⟨W_of_cellB, fun ⟨_, h⟩ => cellB_of_W h⟩

/-! ## The data function of each cell and the per-channel field -/

/-- The arbiter stage's index bit (`won = g2 ∨ A2`); `false` for every other kind. -/
def wonOf (ch : Fin n → Chan) : K n → (Nat → Trace) → Nat → Bool
  | .amerge _ y _ _, w, t => w 1 t || (ch y).ack t
  | _, _, _ => false

/-- The cell function on an input snapshot (`v`: input buses; `b`: the arbiter's index bit). -/
def fnOf (sv : Nat → Nat) : K n → (Fin n → Nat) → Bool → Nat
  | .forkG i _, v, _ => v i
  | .forkH i _ _ _ _ _, v, _ => v i
  | .join ins _ e js _, v, _ => jg e js (ins.map v)
  | .bjoin ins _ ec ed, v, _ => bg ec ed (ins.map v)
  | .steerC _ _ _, _, _ => 0
  | .steerD j _ _ fd _, v, _ => fd.eval [v j / 2]
  | .mux c x y _ _, v, _ => if sel2 (v c) then v y else v x
  | .muxn c x0 x1 x2 _ _, v, _ => v (cx3 x0 x1 x2 (selD (v c)))
  | .amerge x y _ _, v, b => 2 * (if b then v y else v x) + Mux.b2n b
  | .link i _, v, _ => v i
  | .src _ which _, _, _ => sv which
  | .sink _, _, _ => 0

/-- The zero-delay value of the cell's output(s) at `t` (non-link kinds). -/
def fval (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (w : Nat → Trace) (t : Nat) : Nat :=
  fnOf sv k (fun i => (ch i).dat t) (wonOf ch k w t)

/-- The extra premise of the relaxed field (only the 3-input mux has one). -/
def fcond (ch : Fin n → Chan) : K n → Nat → Prop
  | .muxn c _ _ _ _ _, t => selD ((ch c).dat t) < 3
  | _, _ => True

/-- **The data field of output `c` alone.** -/
def FieldOf (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (w : Nat → Trace) (c : Fin n) : Prop :=
  match k with
  | .link i _ =>
      (∀ t, w 0 t = true → inTx (ch c) t = true → (ch c).dat t = (ch i).dat t) ∧
      (∀ t, w 0 (t + 1) = false → inTx (ch c) t = true → inTx (ch c) (t + 1) = true →
        (ch c).dat (t + 1) = (ch c).dat t)
  | _ => ∀ t, inTx (ch c) t = true → fcond ch k t → (ch c).dat t = fval ch sv k w t

/-- The zero-delay output buses. -/
def zdD (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (w : Nat → Trace) : Fin n → Nat → Nat :=
  match k with
  | .link i o => fun _ => latchD (w 0) (ch i).dat (ch o).dat
  | _ => fun _ t => fval ch sv k w t

/-! ## Congruences -/

theorem mem_insC_mux {c x y z : Fin n} {mw : MW} :
    c ∈ (K.mux c x y z mw).insC ∧ x ∈ (K.mux c x y z mw).insC ∧ y ∈ (K.mux c x y z mw).insC := by
  simp [K.insC]

theorem fnOf_congr (sv : Nat → Nat) (k : K n) {v v' : Fin n → Nat} (b : Bool)
    (h : ∀ i ∈ k.insC, v i = v' i) : fnOf sv k v b = fnOf sv k v' b := by
  cases k with
  | forkG i os => exact h i (by simp [K.insC])
  | forkH i os l hh d hs => exact h i (by simp [K.insC])
  | join ins o e js jw =>
    show jg e js (ins.map v) = jg e js (ins.map v')
    rw [List.map_congr_left (fun i (hi : i ∈ ins) => h i hi)]
  | bjoin ins o ec ed =>
    show bg ec ed (ins.map v) = bg ec ed (ins.map v')
    rw [List.map_congr_left (fun i (hi : i ∈ ins) => h i hi)]
  | steerC => rfl
  | steerD j t f fd sw =>
    show fd.eval [v j / 2] = fd.eval [v' j / 2]
    rw [h j (by simp [K.insC])]
  | mux c x y z mw =>
    show (if sel2 (v c) then v y else v x) = (if sel2 (v' c) then v' y else v' x)
    rw [h c (by simp [K.insC]), h x (by simp [K.insC]), h y (by simp [K.insC])]
  | muxn c x0 x1 x2 z nw =>
    show v (cx3 x0 x1 x2 (selD (v c))) = v' (cx3 x0 x1 x2 (selD (v' c)))
    rw [h c (by simp [K.insC])]
    apply h
    have hm := cx3_mem x0 x1 x2 (selD (v' c))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    simp only [K.insC, List.mem_cons, List.not_mem_nil, or_false]
    rcases hm with e | e | e <;> simp [e]
  | amerge x y z w =>
    show 2 * (if b then v y else v x) + Mux.b2n b = 2 * (if b then v' y else v' x) + Mux.b2n b
    rw [h x (by simp [K.insC]), h y (by simp [K.insC])]
  | link i o => exact h i (by simp [K.insC])
  | src => rfl
  | sink => rfl

/-- `modC` keeps the input buses of a `Disj` cell when `S` holds no input. -/
theorem fval_modC {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    {S : List (Fin n)} {D : Fin n → Nat → Nat} (hS : ∀ i ∈ k.insC, i ∉ S) (t : Nat) :
    fval (modC ch S D) sv k w t = fval ch sv k w t := by
  unfold fval
  have hw : wonOf (modC ch S D) k w t = wonOf ch k w t := by cases k <;> rfl
  rw [hw]
  exact fnOf_congr sv k _ (fun i hi => by rw [modC_out (hS i hi)])

theorem fcond_modC {ch : Fin n → Chan} {k : K n} {S : List (Fin n)} {D : Fin n → Nat → Nat}
    (hS : ∀ i ∈ k.insC, i ∉ S) (t : Nat) : fcond (modC ch S D) k t ↔ fcond ch k t := by
  cases k with
  | muxn c x0 x1 x2 z nw =>
    show selD ((modC ch S D c).dat t) < 3 ↔ selD ((ch c).dat t) < 3
    rw [modC_out (hS c (by simp [K.insC]))]
  | _ => exact Iff.rfl

/-- A field of an output outside `S` survives the re-labelling of `S`. -/
theorem fieldOf_modC_out {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    {S : List (Fin n)} {D : Fin n → Nat → Nat} (hS : ∀ i ∈ k.insC, i ∉ S) {c : Fin n}
    (hc : c ∉ S) (hF : FieldOf ch sv k w c) : FieldOf (modC ch S D) sv k w c := by
  cases k with
  | link i o =>
    have hi : modC ch S D i = ch i := modC_out (hS i (by simp [K.insC]))
    show (∀ t, w 0 t = true → inTx (modC ch S D c) t = true →
        (modC ch S D c).dat t = (modC ch S D i).dat t) ∧ _
    rw [hi, modC_out hc]; exact hF
  | _ =>
    intro t ht hcond
    rw [modC_out hc] at ht ⊢
    rw [fval_modC hS]
    exact hF t ht ((fcond_modC hS t).1 hcond)

/-- A re-labelled output with the zero-delay bus meets its field by construction. -/
theorem field_zd {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    {S : List (Fin n)} (hS : ∀ i ∈ k.insC, i ∉ S) {c : Fin n} (hc : c ∈ S) :
    FieldOf (modC ch S (zdD ch sv k w)) sv k w c := by
  cases k with
  | link i o =>
    have hi : modC ch S (zdD ch sv (.link i o) w) i = ch i := modC_out (hS i (by simp [K.insC]))
    refine ⟨fun t h _ => ?_, fun t h _ _ => ?_⟩
    · rw [hi, modC_in hc]
      show latchD (w 0) (ch i).dat (ch o).dat t = (ch i).dat t
      cases t with
      | zero => simp [latchD, h]
      | succ t => simp [latchD, h]
    · rw [modC_in hc, modC_in hc]
      show latchD (w 0) (ch i).dat (ch o).dat (t + 1) = latchD (w 0) (ch i).dat (ch o).dat t
      simp [latchD, h]
  | _ =>
    intro t _ _
    rw [modC_in hc, fval_modC hS]
    rfl

/-! ## The handshake half and the one transfer lemma -/

/-- Replace every bus (handshake wires unchanged). -/
def reb (ch : Fin n → Chan) (B : Fin n → Nat → Nat) (c : Fin n) : Chan :=
  ⟨(ch c).req, (ch c).ack, B c⟩

/-- **The handshake half**: the relaxed cell on the trace whose output buses show their
zero-delay values. -/
def HS (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (w : Nat → Trace) : Prop :=
  CellW (modC ch k.outsC (zdD ch sv k w)) sv k w

theorem map_ne_nil {α β : Type} {f g : α → β} {l : List α} (h : l.map f ≠ []) : l.map g ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- **Transfer.** The handshake fields do not read output buses, so they survive any bus
re-labelling that keeps the input buses; the data fields are supplied. -/
theorem cellW_reb {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (B : Fin n → Nat → Nat) (h : CellW ch sv k w) (hin : ∀ i ∈ k.insC, B i = (ch i).dat)
    (hF : ∀ c ∈ k.outsC, FieldOf (reb ch B) sv k w c) : CellW (reb ch B) sv k w := by
  cases k with
  | forkG i os =>
    refine ⟨map_ne_nil h.ne, ?_, ?_, ?_, h.initA, ?_⟩
    · intro o ho t hne; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact h.wire (ch c) (List.mem_map_of_mem hc) t hne
    · intro t hne o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact h.cel t hne (ch c) (List.mem_map_of_mem hc)
    · intro o ho t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact hF c hc t ht trivial
    · intro o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact h.initO (ch c) (List.mem_map_of_mem hc)
  | forkH i os l hh d hs =>
    refine ⟨map_ne_nil h.ne, ?_, ?_, ?_, h.initA, ?_⟩
    · intro o ho t hne; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact h.wire (ch c) (List.mem_map_of_mem hc) t hne
    · intro t hne o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact h.cel t hne (ch c) (List.mem_map_of_mem hc)
    · intro o ho t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact hF c hc t ht trivial
    · intro o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact h.initO (ch c) (List.mem_map_of_mem hc)
  | join ins o e js jw =>
    refine ⟨map_ne_nil h.ne, ?_, ?_, ?_, h.initO, ?_⟩
    · intro t hne i hi; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
      exact h.cel t hne (ch c) (List.mem_map_of_mem hc)
    · intro i hi t hne; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
      exact h.wire (ch c) (List.mem_map_of_mem hc) t hne
    · intro t ht
      rw [hF o (by simp [K.outsC]) t ht trivial, List.map_map]; rfl
    · intro i hi; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
      exact h.initI (ch c) (List.mem_map_of_mem hc)
  | bjoin ins o ec ed =>
    refine ⟨map_ne_nil h.ne, ?_, ?_, ?_, h.initO, ?_⟩
    · intro t hne i hi; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
      exact h.cel t hne (ch c) (List.mem_map_of_mem hc)
    · intro i hi t hne; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
      exact h.wire (ch c) (List.mem_map_of_mem hc) t hne
    · intro t ht
      rw [hF o (by simp [K.outsC]) t ht trivial, List.map_map]; rfl
    · intro i hi; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
      exact h.initI (ch c) (List.mem_map_of_mem hc)
  | steerC j tt f =>
    have hj : (reb ch B j).dat = (ch j).dat := hin j (by simp [K.insC])
    refine ⟨fun b t hne => ?_, h.orr, fun b t ht => ?_, h.initJ, h.initO⟩
    · rw [hj]; exact h.lut b t hne
    · cases b
      · exact hF f (by simp [K.outsC]) t ht trivial
      · exact hF tt (by simp [K.outsC]) t ht trivial
  | steerD j tt f fd sw =>
    have hj : (reb ch B j).dat = (ch j).dat := hin j (by simp [K.insC])
    refine ⟨fun b t hne => ?_, h.orr, fun b t ht => ?_, h.initJ, h.initO⟩
    · rw [hj]; exact h.lut b t hne
    · cases b
      · exact hF f (by simp [K.outsC]) t ht trivial
      · exact hF tt (by simp [K.outsC]) t ht trivial
  | mux c x y z mw =>
    have hc : (reb ch B c).dat = (ch c).dat := hin c (by simp [K.insC])
    refine ⟨fun t hne => ?_, fun t hne => ?_, h.zr, h.xa, h.ya, h.ca, fun t ht => ?_, h.i0, h.i1,
      h.iz, h.ix, h.iy, h.ic⟩
    · rw [hc]; exact h.cj0 t hne
    · rw [hc]; exact h.cj1 t hne
    · exact hF z (by simp [K.outsC]) t ht trivial
  | muxn c x0 x1 x2 z nw =>
    have hc : (reb ch B c).dat = (ch c).dat := hin c (by simp [K.insC])
    refine ⟨fun m hm t hne => ?_, h.zr, h.xa, h.ca, fun t ht h3 => ?_, h.ij, h.iz, h.ix, h.ic⟩
    · rw [hc]; exact h.cj m hm t hne
    · exact hF z (by simp [K.outsC]) t ht h3
  | amerge x y z ww =>
    exact ⟨h.H_ARB1, h.H_ARB2, h.H_ARB_EXCL, h.zr, h.H_AMERGE_RTZ, h.xa, h.ya,
      fun t ht => hF z (by simp [K.outsC]) t ht trivial, h.i1, h.i2, h.iz, h.ix, h.iy⟩
  | link i o =>
    have F := hF o (by simp [K.outsC])
    exact ⟨h.H_CEL_SI, h.H_ACK_DI, h.H_REQ_DI, F.1, F.2, h.ic, h.ii, h.io⟩
  | src z which d =>
    exact ⟨h.H_LUT_SI, fun t ht => hF z (by simp [K.outsC]) t ht trivial, h.iz⟩
  | sink i => exact ⟨h.wire, h.init⟩

theorem disj_out {k : K n} (hj : Disj k) : ∀ i ∈ k.insC, i ∉ k.outsC := hj

/-- Relaxed cell ⇒ handshake half. -/
theorem hs_of_cellW {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (hj : Disj k) (h : CellW ch sv k w) : HS ch sv k w :=
  cellW_reb (ch := ch) (fun c t => if c ∈ k.outsC then zdD ch sv k w c t else (ch c).dat t) h
    (fun i hi => by funext t; simp [hj i hi])
    (fun c hc => field_zd (S := k.outsC) hj hc)

/-- **Handshake half + every output's field ⇒ relaxed cell.** -/
theorem cellW_of_hs {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (hj : Disj k) (h : HS ch sv k w) (hF : ∀ c ∈ k.outsC, FieldOf ch sv k w c) :
    CellW ch sv k w :=
  cellW_reb (ch := modC ch k.outsC (zdD ch sv k w)) (fun c => (ch c).dat) h
    (fun i hi => by rw [modC_out (hj i hi)]) (fun c hc => hF c hc)

/-- Handshake half + the fields of the outputs outside `S` ⇒ relaxed cell with `S`
re-labelled to the zero-delay values. -/
theorem cellW_modS {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (hj : Disj k) (h : HS ch sv k w) {S : List (Fin n)} (hSo : ∀ c ∈ S, c ∈ k.outsC)
    (hF : ∀ c ∈ k.outsC, c ∉ S → FieldOf ch sv k w c) :
    CellW (modC ch S (zdD ch sv k w)) sv k w := by
  have hS : ∀ i ∈ k.insC, i ∉ S := fun i hi hiS => hj i hi (hSo i hiS)
  exact cellW_reb (ch := modC ch k.outsC (zdD ch sv k w))
    (fun c t => if c ∈ S then zdD ch sv k w c t else (ch c).dat t) h
    (fun i hi => by funext t; simp [hS i hi, modC, hj i hi])
    (fun c hc => by
      by_cases hcS : c ∈ S
      · exact (field_zd (ch := ch) (sv := sv) (k := k) (w := w) (S := S) hS hcS :)
      · exact (fieldOf_modC_out (D := zdD ch sv k w) hS hcS (hF c hc hcS) :))

/-! ## Protocol and one-output bundling from the handshake half -/

/-- **The bounded protocol spec from the handshake half alone.** -/
theorem hs_protoT {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (hj : Disj k) (h : HS ch sv k w) : OpProtoT ch k.insC k.outsC :=
  protoT_of_mod hj (cell_protoT_B _ sv k (cellB_of_W h) hj)

/-- **Bounded structural bundling of one output from its own field.** -/
theorem hs_heldT_one {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (hj : Disj k) (h : HS ch sv k w) (hs : StructK2 k = true) {c : Fin n} (hc : c ∈ k.outsC)
    (hF : FieldOf ch sv k w c) (t : Nat) (hi : ∀ c, Init (ch c))
    (hp : ∀ c s, s ≤ t → Rules (ch c) s)
    (hh : ∀ i ∈ k.insC, ∀ s, s ≤ t → HeldStep (ch i) s) : HeldStep (ch c) t := by
  have hSo : ∀ x ∈ k.outsC.filter (fun x => decide (x ≠ c)), x ∈ k.outsC :=
    fun x hx => (List.mem_filter.1 hx).1
  have hcS : c ∉ k.outsC.filter (fun x => decide (x ≠ c)) := by
    intro hx; have := (List.mem_filter.1 hx).2; simp at this
  have hS : ∀ i ∈ k.insC, i ∉ k.outsC.filter (fun x => decide (x ≠ c)) :=
    fun i hi hiS => hj i hi (hSo i hiS)
  have C := cellW_modS hj h hSo (fun x hx hxS => by
    by_cases e : x = c
    · rw [e]; exact hF
    · exact absurd (List.mem_filter.2 ⟨hx, by simp [e]⟩) hxS)
  have H := cellB_heldT _ sv k (cellB_of_W C) hs t (fun c => hi c) (fun c s hs => hp c s hs)
    (fun i hi' s hs' => by rw [modC_out (hS i hi')]; exact hh i hi' s hs') c hc
  rwa [modC_out hcS] at H

end Formal.Net.OpsBusy3
