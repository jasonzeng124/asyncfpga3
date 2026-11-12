import Formal.Net.CapstoneNetDef

/-!
# Probe C-8x2: busy-gated ("relaxed") cell data fields

C-8x proved that, under per-arc bounded-delay semantics and a tcheck verdict, the physical
capture-pin bus of a channel holds its zero-delay value at every instant the channel is
mid-transaction (`sampled_eq_zd`). It is NOT pinned down while the channel is idle: there the
physical bus may carry the next token's waves, glitches, anything. The 8f/8j/8l gate models
state their data fields at EVERY instant (`Join.dat : ∀ t, o.dat t = g (inputs at t)`, the
link's `H_LATCH_OPEN`/`H_LATCH_HOLD`, ...), so a physical observation can never be an Ops trace
directly; C-8x had to postulate a separate zero-delay trace and H_ZD_AGREE.

Here each data field is gated by the busy phase of the cell's OUTPUT channel:

| cell | old field (every `t`) | relaxed field (only when the output is mid-transaction) |
|---|---|---|
| fork | `o.dat t = a.dat t` | `inTx o t → o.dat t = a.dat t` |
| join / compute | `o.dat t = g (ins at t)` | `inTx o t → o.dat t = g (ins at t)` |
| steer | `(out b).dat t = f (j.dat t)` | `inTx (out b) t → ...` |
| mux / muxn / arbiter stage | `z.dat t = ...` | `inTx z t → ...` |
| link | `c t → o.dat t = i.dat t` and `¬c (t+1) → o.dat (t+1) = o.dat t` | `c t → inTx o t → o.dat t = i.dat t` and `¬c (t+1) → inTx o t → inTx o (t+1) → o.dat (t+1) = o.dat t` |
| source | `z.dat t = v` | `inTx z t → z.dat t = v` |

Every relaxed structure is implied by the old one (`cell_relax`), so every hypothesis built on
the relaxed model is WEAKER than the corresponding one on the old model.

Results:
* `cellB_loc`: a relaxed cell, re-labelled only on its OUTPUT buses at idle instants
  (`modC`), satisfies the OLD gate model; the re-labelling agrees with the real bus at every
  busy instant (for the link: given the protocol and the output's `Held`).
* `cell_proto_B`, `cell_op_B`: the Ops operator theorems (`OpProto`, `OpData`) hold for every
  relaxed cell kind of the capstone network, with the SAME token equations `Eqn`. Proof: the
  old theorems (`cell_proto`, `cell_op`) on the re-labelled trace, transferred back
  (`proto_of_mod`, `data_of_mod`): an Ops operator only ever reads an output bus at `r+1` for an
  offer `r`, a busy instant.
* `forkB_held`, `joinB_held`, `steerB_held`, `srcB_held`, `linkB_held`: on the relaxed model,
  `Held` of the output follows from `Held` of the inputs (the 8w `*_held` lemmas, which were
  proved only for the old all-time fields). These are the structural part of H_DERIVED.

Side condition `Disj k`: no channel is both an input and an output of the same operator
(checked for gcd_hw in `CapstoneRefine2Net`).
-/

namespace Formal.Net.OpsBusy
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet

/-! ## The relaxed gate models -/

structure ForkB (a : Chan) (os : List Chan) : Prop where
  ne : os ≠ []
  wire : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  cel : ∀ t, a.ack (t + 1) ≠ a.ack t → ∀ o ∈ os, o.ack t = a.ack (t + 1)
  dat : ∀ o ∈ os, ∀ t, inTx o t = true → o.dat t = a.dat t
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

structure JoinB (g : List Nat → Nat) (is : List Chan) (o : Chan) : Prop where
  ne : is ≠ []
  cel : ∀ t, o.req (t + 1) ≠ o.req t → ∀ i ∈ is, i.req t = o.req (t + 1)
  wire : ∀ i ∈ is, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  dat : ∀ t, inTx o t = true → o.dat t = g (is.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ is, i.ack 0 = false

structure SteerB (sel : Nat → Bool) (f : Nat → Nat) (j : Chan) (out : Bool → Chan) : Prop where
  lut : ∀ b t, (out b).req (t + 1) ≠ (out b).req t →
    (out b).req (t + 1) = (j.req t && (sel (j.dat t) == b))
  orr : ∀ t, j.ack (t + 1) ≠ j.ack t → j.ack (t + 1) = ((out true).ack t || (out false).ack t)
  dat : ∀ b t, inTx (out b) t = true → (out b).dat t = f (j.dat t)
  initJ : j.ack 0 = false
  initO : ∀ b, (out b).req 0 = false

structure MuxB (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) : Prop where
  cj0 : ∀ t, j0 (t + 1) ≠ j0 t → x.req t = j0 (t + 1) ∧ (c.req t && !sel (c.dat t)) = j0 (t + 1)
  cj1 : ∀ t, j1 (t + 1) ≠ j1 t → y.req t = j1 (t + 1) ∧ (c.req t && sel (c.dat t)) = j1 (t + 1)
  zr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j0 t || j1 t)
  xa : ∀ t, x.ack (t + 1) ≠ x.ack t → j0 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)
  ya : ∀ t, y.ack (t + 1) ≠ y.ack t → j1 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)
  ca : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  dat : ∀ t, inTx z t = true → z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

structure MuxNB (sel : Nat → Nat) (xs : Nat → Chan) (c z : Chan) (j : Nat → Trace) : Prop where
  cj : ∀ k, k < 3 → ∀ t, j k (t + 1) ≠ j k t →
    (xs k).req t = j k (t + 1) ∧ (c.req t && (sel (c.dat t) == k)) = j k (t + 1)
  zr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j 0 t || j 1 t || j 2 t)
  xa : ∀ k, k < 3 → ∀ t, (xs k).ack (t + 1) ≠ (xs k).ack t →
    j k t = (xs k).ack (t + 1) ∧ z.ack t = (xs k).ack (t + 1)
  ca : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  dat : ∀ t, inTx z t = true → sel (c.dat t) < 3 → z.dat t = (xs (sel (c.dat t))).dat t
  ij : ∀ k, k < 3 → j k 0 = false
  iz : z.req 0 = false
  ix : ∀ k, k < 3 → (xs k).ack 0 = false
  ic : c.ack 0 = false

structure AMergeB (x y z : Chan) (g1 g2 : Trace) : Prop where
  H_ARB1 : ∀ t, g1 (t + 1) ≠ g1 t → g1 (t + 1) = x.req t ∧ (g1 (t + 1) = true → g2 t = false ∧ z.ack t = false)
  H_ARB2 : ∀ t, g2 (t + 1) ≠ g2 t → g2 (t + 1) = y.req t ∧ (g2 (t + 1) = true → g1 t = false ∧ z.ack t = false)
  H_ARB_EXCL : ∀ t, (g1 t && g2 t) = false
  zr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (g1 t || g2 t)
  H_AMERGE_RTZ : ∀ t, z.req t = false → z.req (t + 1) = true → x.ack t = false ∧ y.ack t = false
  xa : ∀ t, x.ack (t + 1) ≠ x.ack t → g1 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)
  ya : ∀ t, y.ack (t + 1) ≠ y.ack t → g2 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)
  dat : ∀ t, inTx z t = true →
    z.dat t = 2 * (if (g2 t || y.ack t) then y.dat t else x.dat t) + Mux.b2n (g2 t || y.ack t)
  i1 : g1 0 = false
  i2 : g2 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false

open Formal.Cells.LinkHandshake (ctlB) in
structure LinkB (i o : Chan) (c : Trace) : Prop where
  H_CEL_SI : ∀ t, c (t + 1) ≠ c t → c (t + 1) = ctlB (i.req t) (o.ack t) (c t) false
  H_ACK_DI : ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = c t
  H_REQ_DI : ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t
  /-- transparent latch, observed only while the output channel is mid-transaction -/
  H_LATCH_OPEN_B : ∀ t, c t = true → inTx o t = true → o.dat t = i.dat t
  /-- opaque latch, observed only across a step inside one output transaction -/
  H_LATCH_HOLD_B : ∀ t, c (t + 1) = false → inTx o t = true → inTx o (t + 1) = true →
    o.dat (t + 1) = o.dat t
  ic : c 0 = false
  ii : i.ack 0 = false
  io : o.req 0 = false

structure SrcB (z : Chan) (v : Nat) : Prop where
  H_LUT_SI : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = !z.ack t
  dat : ∀ t, inTx z t = true → z.dat t = v
  iz : z.req 0 = false

variable {n : Nat}

/-- The relaxed gate-model hypothesis of each operator (mirrors `CapNet.Cell`). -/
def CellB (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .forkG i os => ForkB (ch i) (os.map ch)
  | .forkH i os _ _ _ _ => ForkB (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _ => JoinB (jg e js) (ins.map ch) (ch o)
  | .bjoin ins o ec ed => JoinB (bg ec ed) (ins.map ch) (ch o)
  | .steerC j t f => SteerB sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _ =>
      SteerB sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _ => ∃ j0 j1, MuxB sel2 (ch x) (ch y) (ch c) (ch z) j0 j1
  | .muxn c x0 x1 x2 z _ =>
      ∃ j, MuxNB selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .amerge x y z _ => ∃ g1 g2, AMergeB (ch x) (ch y) (ch z) g1 g2
  | .link i o => ∃ c, LinkB (ch i) (ch o) c
  | .src z which _ => SrcB (ch z) (sv which)
  | .sink i => Ops.Gcd.Sink (ch i)

/-- No channel is both an input and an output of the operator. -/
def Disj (k : K n) : Prop := ∀ c ∈ k.insC, c ∉ k.outsC

instance (k : K n) : Decidable (Disj k) := by unfold Disj; infer_instance

/-! ## The old model implies the relaxed one -/

theorem cell_relax (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : Cell ch sv k) :
    CellB ch sv k := by
  cases k with
  | forkG i os =>
    exact ⟨hc.ne, hc.wire, hc.cel, fun o ho t _ => hc.dat o ho t, hc.initA, hc.initO⟩
  | forkH i os l h d hs =>
    exact ⟨hc.ne, hc.wire, hc.cel, fun o ho t _ => hc.dat o ho t, hc.initA, hc.initO⟩
  | join ins o e js jw => exact ⟨hc.ne, hc.cel, hc.wire, fun t _ => hc.dat t, hc.initO, hc.initI⟩
  | bjoin ins o ec ed => exact ⟨hc.ne, hc.cel, hc.wire, fun t _ => hc.dat t, hc.initO, hc.initI⟩
  | steerC j t f => exact ⟨hc.lut, hc.orr, fun b t _ => hc.dat b t, hc.initJ, hc.initO⟩
  | steerD j t f fd sw => exact ⟨hc.lut, hc.orr, fun b t _ => hc.dat b t, hc.initJ, hc.initO⟩
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := hc
    exact ⟨j0, j1, M.cj0, M.cj1, M.zr, M.xa, M.ya, M.ca, fun t _ => M.dat t, M.i0, M.i1, M.iz,
      M.ix, M.iy, M.ic⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := hc
    exact ⟨j, M.cj, M.zr, M.xa, M.ca, fun t _ => M.dat t, M.ij, M.iz, M.ix, M.ic⟩
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact ⟨g1, g2, M.H_ARB1, M.H_ARB2, M.H_ARB_EXCL, M.zr, M.H_AMERGE_RTZ, M.xa, M.ya,
      fun t _ => M.dat t, M.i1, M.i2, M.iz, M.ix, M.iy⟩
  | link i o =>
    obtain ⟨c, L⟩ := hc
    exact ⟨c, L.H_CEL_SI, L.H_ACK_DI, L.H_REQ_DI, fun t h _ => L.H_LATCH_OPEN t h,
      fun t h _ _ => L.H_LATCH_HOLD t h, L.ic, L.ii, L.io⟩
  | src z which d => exact ⟨hc.H_LUT_SI, fun t _ => hc.dat t, hc.iz⟩
  | sink i => exact hc

/-! ## Re-labelling the output buses -/

/-- `ch` with the buses of the channels in `S` replaced by `D` (handshake wires unchanged). -/
def modC (ch : Fin n → Chan) (S : List (Fin n)) (D : Fin n → Nat → Nat) (c : Fin n) : Chan :=
  ⟨(ch c).req, (ch c).ack, fun t => if c ∈ S then D c t else (ch c).dat t⟩

variable {ch : Fin n → Chan} {S : List (Fin n)} {D : Fin n → Nat → Nat}

@[simp] theorem modC_req (c : Fin n) : (modC ch S D c).req = (ch c).req := rfl
@[simp] theorem modC_ack (c : Fin n) : (modC ch S D c).ack = (ch c).ack := rfl

theorem modC_in {c : Fin n} (h : c ∈ S) (t : Nat) : (modC ch S D c).dat t = D c t := by
  simp [modC, h]

theorem modC_out {c : Fin n} (h : c ∉ S) : modC ch S D c = ch c := by
  unfold modC; simp only [h, ite_false]

theorem inTx_mod (c : Fin n) (t : Nat) : inTx (modC ch S D c) t = inTx (ch c) t := rfl

theorem busy_of_off {c : Chan} {k r : Nat} (h : OffAt c k r) : inTx c (r + 1) = true := by
  have := h.1; simp [riseB] at this; simp [inTx, this.2]

/-- The re-labelling agrees with the real bus at every busy instant of the outputs. -/
def AgrOut (ch : Fin n → Chan) (outs : List (Fin n)) (D : Fin n → Nat → Nat) : Prop :=
  ∀ c ∈ outs, ∀ t, inTx (ch c) t = true → D c t = (ch c).dat t

/-- The winner stream depends on the bus only at offers. -/
theorem winner_congr {c c' : Chan} (hr : c'.req = c.req)
    (hd : ∀ r, riseB c.req r = true → c'.dat (r + 1) = c.dat (r + 1)) (k : Nat) :
    CM.winner c' k = CM.winner c k := by
  by_cases h : ∃ r, OffAt c k r
  · obtain ⟨r, hr'⟩ := h
    have hr'' : OffAt c' k r := by unfold OffAt; rw [hr]; exact hr'
    rw [CM.winner_at hr', CM.winner_at hr'', hd r hr'.1]
  · have h' : ¬ ∃ r, OffAt c' k r := by
      rintro ⟨r, hr'⟩; apply h; refine ⟨r, ?_⟩; unfold OffAt at hr' ⊢; rw [← hr]; exact hr'
    have e1 : CM.winner c k = false := by
      unfold CM.winner
      simp only [decide_eq_false_iff_not]
      rintro ⟨r, ho, _⟩; exact h ⟨r, ho⟩
    have e2 : CM.winner c' k = false := by
      unfold CM.winner
      simp only [decide_eq_false_iff_not]
      rintro ⟨r, ho, _⟩; exact h' ⟨r, ho⟩
    rw [e1, e2]

/-! ## Transfer of the operator theorems back to the real trace -/

theorem proto_of_mod {ins outs : List (Fin n)} (hS : ∀ c ∈ ins, c ∉ S)
    (h : OpProto (modC ch S D) ins outs) : OpProto ch ins outs := by
  refine ⟨fun t hi ho hh hp => ?_, fun c hc => h.initIn c hc, fun c hc => h.initOut c hc⟩
  exact h.ag t (fun c hc => hi c hc) (fun c hc => ho c hc)
    (fun c hc => by rw [modC_out (hS c hc)]; exact hh c hc) (fun s hs => hp s hs)

theorem data_of_mod {ins outs : List (Fin n)} {E : (Fin n → Nat → Nat) → Prop}
    (hS : ∀ c ∈ ins, c ∉ outs)
    (hA : (∀ c ∈ ins, Protocol (ch c)) → (∀ c ∈ outs, Protocol (ch c) ∧ Held (ch c)) →
      AgrOut ch outs D)
    (h : OpData (modC ch outs D) ins outs E) : OpData ch ins outs E := by
  intro hin hout c hc k r ho σ hag hE
  have A := hA (fun c hc => (hin c hc).1) hout
  have heldM : ∀ c ∈ outs, Held (modC ch outs D c) := by
    intro c hc t h0 h1
    rw [modC_in hc, modC_in hc, A c hc t h0, A c hc (t + 1) h1]
    exact (hout c hc).2 t h0 h1
  have hagM : Agree (modC ch outs D) σ r := by
    intro c' k' r' hr' ho'
    have e := hag c' k' r' hr' ho'
    by_cases hc' : c' ∈ outs
    · rw [modC_in hc', A c' hc' (r' + 1) (busy_of_off ho')]; exact e
    · rw [modC_out hc']; exact e
  have := h (fun c hc => by rw [modC_out (hS c hc)]; exact hin c hc)
    (fun c hc => ⟨(hout c hc).1, heldM c hc⟩) c hc k r ho σ hagM hE
  rw [modC_in hc, A c hc (r + 1) (busy_of_off ho)] at this
  exact this

theorem eqn_mod (om : Nat → Nat → Bool) (sv : Nat → Nat) (k : K n) :
    Eqn (modC ch S D) om sv k = Eqn ch om sv k := by
  cases k <;> rfl

end Formal.Net.OpsBusy
