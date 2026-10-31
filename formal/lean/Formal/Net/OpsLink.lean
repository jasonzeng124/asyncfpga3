import Formal.Net.Ops
import Formal.Cells.LinkHandshake

/-!
# Probe C-8l (1a): `bd_link` (the Muller link) as an operator of the Ops framework

`cells/rtl/bd_link.v` (Muller family, the default; `BD_LINK_DC` is not set):

    c       = C(req_in, ~ack_out)          bd_link_ctl = bd_c2n, INIT 0x00B200B200B200B2
    data_out = c ? data_in : data_out      bd_latch, enable = c (transparent while c is high)
    req_out = rdly(c)                      bd_delay DELAY (0 = wire)
    ack_in  = uack(c)                      bd_delay DACK, FASTRISE

The node function is B's `LinkHandshake.ctlB` with `rst = 0`; shard C's 11d
(`Formal.Gen.ProofsLink.bd_link_ctl_gate_B`) proves the LUT synthesized from the
real RTL computes exactly `ctlB`, so this cell model is the generated netlist's.

Gate model `Link i o c` (binary, SI/DI):
* H_CEL_SI: `c` moves only to `ctlB (i.req) (o.ack) c 0` of the previous tick
  (unbounded inertial delay of the C-element LUT with its feedback);
* H_WIRE_DI (ack): `i.ack` (= `ack_in`) moves only to the previous value of `c`
  (the DACK line plus wire: one unbounded inertial node). NOT isochronic with
  `req_out`: the two may lag `c` by different amounts;
* H_WIRE_DI (req): `o.req` (= `req_out`) moves only to the previous value of `c`
  (the DELAY line plus wire);
* H_LATCH_COMB: zero-delay transparent latch: while `c` is high
  `o.dat = i.dat`; when `c` is low, `o.dat` keeps its previous value. The real
  latch delay and enable skew are the link's 8a obligations (`Sep`, `Hold`,
  `SetupHold`: rules H/I/L), pushed into `Held` of the output channel as in 8f.

Reachable set: 18 states with two counters (`Wip/C8l/link_reach.py`),
closure re-checked by kernel `decide`.

Proved:
* `link_proto`, `link_op`: `OpProto` + `OpData` with the token equation of a
  FIFO stage, `σ o k = σ i k` (`linkEq`);
* `link_capacity`: ONE-PLACE: at every time, #`ack_in↑` ≤ #`ack_out↓` + 1
  (the link has accepted at most one token it has not delivered);
* `link_held`: H_BUNDLE of the output follows from H_BUNDLE of the input and
  the latch model (so a link's output channel needs no bundling hypothesis of
  its own in the zero-delay data model; its timing obligations are 8a's).
* `link_out_le`: #offers out ≤ #closes in + 1 (no token is invented).
-/

namespace Formal.Net.Ops.Link
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.LinkHandshake (ctlB)

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- One state of the link model plus the counters `d = 1 + #o.req↑ - #i.ack↓`
and `q = 1 + #i.ack↑ - #o.ack↓`. -/
structure LS where
  ir : Bool
  ia : Bool
  c : Bool
  orq : Bool
  oa : Bool
  d : Nat
  q : Nat
  deriving DecidableEq

def ltbl : List LS := [
  ⟨false, false, false, false, false, 1, 1⟩,
  ⟨true, false, false, false, false, 1, 1⟩,
  ⟨true, false, true, false, false, 1, 1⟩,
  ⟨false, false, false, false, true, 1, 2⟩,
  ⟨false, false, false, true, true, 1, 2⟩,
  ⟨false, true, true, false, false, 1, 2⟩,
  ⟨true, false, false, false, true, 1, 2⟩,
  ⟨true, false, false, true, true, 1, 2⟩,
  ⟨true, true, true, false, false, 1, 2⟩,
  ⟨false, true, false, false, false, 2, 1⟩,
  ⟨true, false, true, true, false, 2, 1⟩,
  ⟨true, false, true, true, true, 2, 1⟩,
  ⟨false, true, false, false, true, 2, 2⟩,
  ⟨false, true, false, true, true, 2, 2⟩,
  ⟨false, true, true, true, false, 2, 2⟩,
  ⟨false, true, true, true, true, 2, 2⟩,
  ⟨true, true, true, true, false, 2, 2⟩,
  ⟨true, true, true, true, true, 2, 2⟩
]

def lnxt (e : LS) (ir ia c orq oa : Bool) : LS :=
  ⟨ir, ia, c, orq, oa, e.d + b2n (!e.orq && orq) - b2n (e.ia && !ia),
   e.q + b2n (!e.ia && ia) - b2n (e.oa && !oa)⟩

def LConcl (e : LS) (ir ia c orq oa : Bool) : Prop :=
  let n := lnxt e ir ia c orq oa
  ltbl.contains n = true ∧
  n.d + b2n (e.ia && !ia) = e.d + b2n (!e.orq && orq) ∧
  n.q + b2n (e.oa && !oa) = e.q + b2n (!e.ia && ia) ∧
  ((!e.orq && orq) = true → e.c = true ∧ c = true ∧ (e.ir || e.ia) = true ∧
      (ir || ia) = true ∧ e.d = 1 ∧ (e.ia && !ia) = false) ∧
  ((e.orq || e.oa) = true → (orq || oa) = true → c = true →
      e.c = true ∧ (e.ir || e.ia) = true ∧ (ir || ia) = true)

instance (e : LS) (ir ia c orq oa : Bool) : Decidable (LConcl e ir ia c orq oa) := by
  unfold LConcl; exact inferInstance

set_option maxRecDepth 100000 in
/-- Closure of the reachable set under every step the gates and the
environment (four-phase sender on `i`, receiver on `o`) allow. -/
theorem link_closed : ∀ e ∈ ltbl,
    ∀ ir : Bool, (ir ≠ e.ir → e.ir = e.ia) →
    ∀ oa : Bool, (oa ≠ e.oa → e.oa ≠ e.orq) →
    ∀ c : Bool, (c ≠ e.c → c = ctlB e.ir e.oa e.c false) →
    ∀ ia : Bool, (ia ≠ e.ia → ia = e.c) →
    ∀ orq : Bool, (orq ≠ e.orq → orq = e.c) →
    LConcl e ir ia c orq oa := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The guarantees need only the link's own gates at the step. -/
theorem link_guar : ∀ e ∈ ltbl,
    ∀ ia : Bool, (ia ≠ e.ia → ia = e.c) →
    ∀ orq : Bool, (orq ≠ e.orq → orq = e.c) →
    (ia ≠ e.ia → e.ia ≠ e.ir) ∧ (orq ≠ e.orq → e.orq = e.oa) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Capacity: in every reachable state `q ∈ {1, 2}`. -/
theorem link_q : ∀ e ∈ ltbl, e.q ≤ 2 := by decide

theorem link_d : ∀ e ∈ ltbl, e.d ≤ 2 := by decide

theorem lmem {e : LS} (h : ltbl.contains e = true) : e ∈ ltbl := by simpa using h

/-- The gate model of one `bd_link` (Muller family). `c` is the controller node. -/
structure Link (i o : Chan) (c : Trace) : Prop where
  H_CEL_SI : ∀ t, c (t + 1) ≠ c t → c (t + 1) = ctlB (i.req t) (o.ack t) (c t) false
  H_ACK_DI : ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = c t
  H_REQ_DI : ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t
  H_LATCH_OPEN : ∀ t, c t = true → o.dat t = i.dat t
  H_LATCH_HOLD : ∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t
  ic : c 0 = false
  ii : i.ack 0 = false
  io : o.req 0 = false

variable {i o : Chan} {c : Trace}

def lst (i o : Chan) (c : Trace) (t d q : Nat) : LS :=
  ⟨i.req t, i.ack t, c t, o.req t, o.ack t, d, q⟩

theorem link_inv (L : Link i o c) (hi : i.req 0 = false) (ho : o.ack 0 = false) : ∀ t,
    (∀ s, s < t → SendStep i s ∧ RecvStep o s) →
    ∃ d q, ltbl.contains (lst i o c t d q) = true ∧
      cnt (riseB o.req) t + 1 = cnt (fallB i.ack) t + d ∧
      cnt (riseB i.ack) t + 1 = cnt (fallB o.ack) t + q := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨1, 1, ?_, rfl, rfl⟩
    simp only [lst, hi, ho, L.ic, L.ii, L.io]; decide
  | succ t ih =>
    intro hp
    obtain ⟨d, q, hm, h1, h2⟩ := ih (fun s hs => hp s (by omega))
    obtain ⟨si, ro⟩ := hp t (by omega)
    have K := link_closed _ (lmem hm) (i.req (t + 1)) si (o.ack (t + 1)) ro
      (c (t + 1)) (L.H_CEL_SI t) (i.ack (t + 1)) (L.H_ACK_DI t) (o.req (t + 1)) (L.H_REQ_DI t)
    obtain ⟨Km, Kd, Kq, _⟩ := K
    refine ⟨_, _, Km, ?_, ?_⟩
    · have e1 : cnt (riseB o.req) (t + 1) = cnt (riseB o.req) t +
          b2n (!o.req t && o.req (t + 1)) := rfl
      have e2 : cnt (fallB i.ack) (t + 1) = cnt (fallB i.ack) t +
          b2n (i.ack t && !i.ack (t + 1)) := rfl
      simp only [lst, lnxt] at Kd ⊢
      omega
    · have e1 : cnt (riseB i.ack) (t + 1) = cnt (riseB i.ack) t +
          b2n (!i.ack t && i.ack (t + 1)) := rfl
      have e2 : cnt (fallB o.ack) (t + 1) = cnt (fallB o.ack) t +
          b2n (o.ack t && !o.ack (t + 1)) := rfl
      simp only [lst, lnxt] at Kq ⊢
      omega

theorem link_proto (L : Link i o c) (hi : i.req 0 = false) (ho : o.ack 0 = false) : ∀ t,
    (∀ s, s < t → SendStep i s ∧ RecvStep o s) → RecvStep i t ∧ SendStep o t := by
  intro t hp
  obtain ⟨d, q, hm, _⟩ := link_inv L hi ho t hp
  exact link_guar _ (lmem hm) (i.ack (t + 1)) (L.H_ACK_DI t) (o.req (t + 1)) (L.H_REQ_DI t)

/-- The step facts at `t`, given both channels obey the protocol. -/
theorem link_step (L : Link i o c) (hpi : Protocol i) (hpo : Protocol o) (t : Nat) :
    ∃ d q, ltbl.contains (lst i o c t d q) = true ∧
      cnt (riseB o.req) t + 1 = cnt (fallB i.ack) t + d ∧
      cnt (riseB i.ack) t + 1 = cnt (fallB o.ack) t + q ∧
      LConcl (lst i o c t d q) (i.req (t + 1)) (i.ack (t + 1)) (c (t + 1)) (o.req (t + 1))
        (o.ack (t + 1)) := by
  obtain ⟨d, q, hm, h1, h2⟩ := link_inv L hpi.1.1 hpo.1.2 t (fun s _ => ⟨(hpi.2 s).1, (hpo.2 s).2⟩)
  exact ⟨d, q, hm, h1, h2, link_closed _ (lmem hm) _ (hpi.2 t).1 _ (hpo.2 t).2
    _ (L.H_CEL_SI t) _ (L.H_ACK_DI t) _ (L.H_REQ_DI t)⟩

/-- ONE-PLACE BUFFER: the link has accepted (`ack_in↑`) at most one token more
than it has delivered (`ack_out↓`). -/
theorem link_capacity (L : Link i o c) (hpi : Protocol i) (hpo : Protocol o) (t : Nat) :
    cnt (riseB i.ack) t ≤ cnt (fallB o.ack) t + 1 := by
  obtain ⟨d, q, hm, _, h2⟩ := link_inv L hpi.1.1 hpo.1.2 t (fun s _ => ⟨(hpi.2 s).1, (hpo.2 s).2⟩)
  have := link_q _ (lmem hm)
  simp only [lst] at this
  omega

/-- No token is invented: #offers out ≤ #closes in + 1, and every offer out is
matched by an input token (`d ≥ 1`). -/
theorem link_out_le (L : Link i o c) (hpi : Protocol i) (hpo : Protocol o) (t : Nat) :
    cnt (riseB o.req) t ≤ cnt (fallB i.ack) t + 1 := by
  obtain ⟨d, q, hm, h1, _⟩ := link_inv L hpi.1.1 hpo.1.2 t (fun s _ => ⟨(hpi.2 s).1, (hpo.2 s).2⟩)
  have := link_d _ (lmem hm)
  simp only [lst] at this
  omega

/-- While a channel is mid-transaction, its open token is the
`#ack↓`-th, offered strictly earlier. -/
theorem tx_open {ch : Chan} (hp : Protocol ch) {t : Nat} (h : inTx ch t = true) :
    ∃ r, r < t ∧ OffAt ch (cnt (fallB ch.ack) t) r := by
  have hi := rise_inv hp t
  rw [h] at hi
  simp only [ite_true] at hi
  obtain ⟨r, hr, hf, hc⟩ := cnt_witness _ t _ hi
  exact ⟨r, hr, hf, hc⟩

/-- H_BUNDLE of the output channel follows from H_BUNDLE of the input. -/
theorem link_held (L : Link i o c) (hpi : Protocol i) (hpo : Protocol o) (hh : Held i) :
    Held o := by
  intro t h0 h1
  obtain ⟨d, q, _, _, _, K⟩ := link_step L hpi hpo t
  have KH := K.2.2.2.2
  simp only [lst] at KH
  cases hc : c (t + 1)
  · exact L.H_LATCH_HOLD t hc
  · obtain ⟨hct, ht0, ht1⟩ := KH (by simpa [inTx] using h0) (by simpa [inTx] using h1) hc
    rw [L.H_LATCH_OPEN _ hc, L.H_LATCH_OPEN _ hct]
    exact hh t (by simpa [inTx] using ht0) (by simpa [inTx] using ht1)

/-! ## Network level -/

variable {C : Type}

/-- The link's token equation: a FIFO stage (the k-th token out is the k-th in). -/
def linkEq (ci co : C) (σ : C → Nat → Nat) : Prop := ∀ k, σ co k = σ ci k

theorem link_op (ch : C → Chan) (ci co : C) (c : Trace) (L : Link (ch ci) (ch co) c) :
    OpProto ch [ci] [co] ∧ OpData ch [ci] [co] (linkEq ci co) := by
  have mi : ci ∈ [ci] := List.mem_singleton_self _
  have mo : co ∈ [co] := List.mem_singleton_self _
  refine ⟨⟨fun t hi ho _ hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := link_proto L (hi ci mi).1 (ho co mo).2 t
      (fun s hs => ⟨((hp s hs).1 ci mi).1, ((hp s hs).2 co mo).2⟩)
    exact ⟨fun c' hc' => by rw [List.mem_singleton.1 hc']; exact h.1,
           fun c' hc' => by rw [List.mem_singleton.1 hc']; exact h.2⟩
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact L.ii
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact L.io
  · intro hin hout c' hc' k r hoff σ hag hE
    rw [List.mem_singleton.1 hc'] at hoff ⊢
    obtain ⟨hpi, hhi⟩ := hin ci mi
    have hpo := (hout co mo).1
    obtain ⟨d, q, _, h1, _, K⟩ := link_step L hpi hpo r
    have hr0 : (ch co).req r = false := by have := hoff.1; simp [riseB] at this; exact this.1
    have hr1 : (ch co).req (r + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
    have KO := K.2.2.2.1
    simp only [lst, hr0, hr1, Bool.not_false, Bool.true_and] at KO
    obtain ⟨_, hc1, htx0, htx1, hd, hnf⟩ := KO trivial
    subst hd
    -- the open input token is the k-th
    have hk : cnt (fallB (ch ci).ack) (r + 1) = k := by
      have e2 : cnt (fallB (ch ci).ack) (r + 1) = cnt (fallB (ch ci).ack) r +
          b2n ((ch ci).ack r && !(ch ci).ack (r + 1)) := rfl
      rw [e2, hnf]; simp only [b2n]; rw [hoff.2] at h1; simp; omega
    obtain ⟨ri, hri, hoffi⟩ := tx_open hpi (t := r + 1) (by simpa [inTx] using htx1)
    rw [hk] at hoffi
    have hri' : ri < r := by
      have hne : ri ≠ r := by
        intro he; subst he
        have := off_idle hpi hoffi.1
        simp [this.1, this.2] at htx0
      omega
    rw [hE k, L.H_LATCH_OPEN _ hc1, hag ci k ri hri' hoffi]
    exact (held_at hpi hhi hoffi (by omega) hk).symm

end Formal.Net.Ops.Link
