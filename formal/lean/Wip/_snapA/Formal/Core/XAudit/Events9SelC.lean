import Formal.Core.XAudit.Events9Sel
import Formal.Net.Ops

/-!
# Formal.Core.XAudit.Events9SelC — A's select-wire stability from C's H_BUNDLE

Probe E8SelC (shard A). Notes: `formal/notes/A-e8selc.md` §2.

`design_verdict9_sel` assumes, per real filtered pin and select literal, that the select
bit's PIN wire (the input of the steer gate / stage LUT, after its routed arc) holds a value
over an open-ended window. This file derives that premise from C's H_BUNDLE
(`Formal.Net.Ops.Held`) of ONE channel of C's model, read off A's wires:

* `busVal`, `chanOf`: C's `Handshake.Chan` built from three things on A's trace: the
  request wire, the acknowledge wire and the list of bus-bit wires (LSB first).
  `chanOf` IS the explicit map from a C channel to A's parsed wires.
* `held_const`: H_BUNDLE keeps the bus constant over any interval on which the channel
  is mid-transaction (`inTx`: req or ack high) at every step.
* `held_wire`: hence every listed bus wire is constant there.
* `route_hold`: a 1-input buffer gate (a routed arc of the parsed netlist) in band
  `[lo, hi]` turns a constant input on `[a, e]` into a constant output on `[a + hi, e + lo]`.
* `SelEnt`, **`entOK`** (decidable, evaluated by the `xselhold` executable on the parsed
  netlist): the map entry of a select literal names C's channel (a string, data only), its
  request, acknowledge and bus wires, the bus wire `dw` that is the select bit, and the
  route gate `rg`; `entOK` checks that `rg` is a 1-input BUFFER from `dw` to exactly the
  input wire of the select gate that `design_verdict9_sel` talks about, and that `dw` is one
  of the bus wires.
* `stab_of_held`: per pin, C's H_BUNDLE on the entry's channel plus
  H_SEL_TX (the channel is mid-transaction from `O k` until `hiC - selLo - lo(rg)` after the
  source's last time in transaction `k`) gives `design_verdict9_sel`'s stability premise
  with `S0 = O k + hi(rg)`, `vb = dw`'s value at `O k`.
* **`design_verdict9_selC`**: `design_verdict9` with SelOK at the real pins replaced by:
  `entOK` of the map (checked), C's H_BUNDLE on every mapped channel, H_SEL_TX, the setup
  `O k + hi(rg) + selHi ≤ R k + loC` (H_SEL_SETUP), the transaction-start bound `R`, and
  `sel = selFn` of the bus values at `O k`.

TRUSTED (not checked here): that the C channel named in an entry (C's `CapNet.Gcd.chanNames`
string) is the bdc channel whose request / acknowledge / bus nets are the entry's wires (the
untrusted map builder matches B's `ResetCapstoneMapData` net names against the routed
netnames). The Lean statements are about the channel `chanOf x rq ak ws` itself, so the
name is only a label: H_BUNDLE is assumed of THAT channel of A's trace.
NOT covered: H_BUNDLE itself (a hypothesis in C too: `Capstone.H_BUNDLE`, a ps-level bundling
contract on the routed wires, which C's tick model does not derive from delays), H_SEL_TX
(the hold half; `Events9SelHold` reduces it to a band check plus H_ACK_LAG), H_SEL_SETUP
(the setup half; C's tcheck rule E is its band analogue, not linked here).
-/

namespace Formal.Core.XAudit.Events9SelC

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9
open Formal.Core.XAudit.Events8Bridge
open Formal.Core.XAudit.Events9Sel

/-! ## C's channel on A's wires -/

/-- The bus value of a list of bits, least significant first. -/
def busVal : List Bool → Nat
  | [] => 0
  | b :: r => (if b then 1 else 0) + 2 * busVal r

theorem busVal_inj : ∀ {l1 l2 : List Bool}, l1.length = l2.length → busVal l1 = busVal l2 → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: r, b :: s, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [busVal] at h
    have hab : a = b := by cases a <;> cases b <;> simp at h <;> omega
    subst hab
    have : busVal r = busVal s := by cases a <;> simp at h <;> omega
    rw [busVal_inj hl this]

/-- **The map from a C channel to A's wires**: C's `Handshake.Chan` whose request and
acknowledge are A's wires `rq`, `ak` and whose bus is the bits of the wires `ws`. -/
def chanOf {n : Nat} (x : Fin n → Sig) (rq ak : Fin n) (ws : List (Fin n)) : Handshake.Chan :=
  ⟨x rq, x ak, fun t => busVal (ws.map (fun w => x w t))⟩

/-- H_BUNDLE holds the bus over every interval that is mid-transaction at every step. -/
theorem held_const {c : Handshake.Chan} (h : Ops.Held c) {a e : Nat}
    (htx : ∀ s, a ≤ s → s ≤ e → Ops.inTx c s = true) : ∀ t, a ≤ t → t ≤ e → c.dat t = c.dat a := by
  intro t
  induction t with
  | zero => intro ha _; have : a = 0 := by omega
            subst this; rfl
  | succ t ih =>
    intro ha he
    rcases Nat.eq_or_lt_of_le ha with hq | hq
    · rw [hq]
    · rw [h t (htx t (by omega) (by omega)) (htx (t + 1) ha he)]
      exact ih (by omega) (by omega)

/-- Every listed bus wire is constant on such an interval. -/
theorem held_wire {n : Nat} {x : Fin n → Sig} {rq ak : Fin n} {ws : List (Fin n)}
    (h : Ops.Held (chanOf x rq ak ws)) {a e : Nat}
    (htx : ∀ s, a ≤ s → s ≤ e → Ops.inTx (chanOf x rq ak ws) s = true)
    {w : Fin n} (hw : w ∈ ws) {t : Nat} (ha : a ≤ t) (he : t ≤ e) : x w t = x w a := by
  have hd := held_const h htx t ha he
  simp only [chanOf] at hd
  have hl := busVal_inj (by simp) hd
  exact (List.map_inj_left.mp hl) w hw

/-! ## A routed arc carries a constant -/

/-- A 1-input BUFFER gate: one input, INIT bit = that input. -/
def isBuf (g : GSpec) : Prop := g.k = 1 ∧ InitSpec g (fun v => v 0)

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include hsat h0 h1

/-- Gate `rg` (a buffer) reads its input through a warp in its band. -/
theorem buf_read {rg : Nat} (hg : rg < d.gates.length) (hb : isBuf (gt d rg)) (t : Nat) :
    x (d.wire (gt d rg).out) t = x (d.wire ((gt d rg).ins.getD 0 0)) (wf hsat rg 0 t) := by
  rw [gate_spec hsat h0 h1 hg hb.2 t]
  simp [hb.1]

/-- **A routed arc carries a constant**: input constant on `[a, e]` ⇒ output constant on
`[a + hi, e + lo]`. -/
theorem route_hold {rg : Nat} (hg : rg < d.gates.length) (hb : isBuf (gt d rg)) {v : Bool} {a e : Nat}
    (hin : ∀ s, a ≤ s → s ≤ e → x (d.wire ((gt d rg).ins.getD 0 0)) s = v)
    {t : Nat} (ha : a + (gt d rg).hi ≤ t) (he : t ≤ e + (gt d rg).lo) :
    x (d.wire (gt d rg).out) t = v := by
  have w := wf_warp hsat hg (by rw [hb.1]; omega)
  rw [buf_read hsat h0 h1 hg hb t]
  apply hin
  · have := w.early_le t; omega
  · have := w.le_late t; omega

end

/-! ## The map entries and their netlist check -/

/-- A map entry for one select literal: C's channel `name` (a label), its request /
acknowledge wires, its bus wires (LSB first), the bus wire `dw` that is this select bit, and
the route gate `rg` from `dw` to the select gate's input. Wires are indices into `d`. -/
structure SelEnt where
  name : String := ""
  rq : Nat := 0
  ak : Nat := 0
  ws : List Nat := []
  dw : Nat := 0
  rg : Nat := 0
  deriving Repr, Inhabited

/-- The entry's channel, on A's trace. -/
def SelEnt.ch {d : Design} (e : SelEnt) (x : Fin d.n → Sig) : Handshake.Chan :=
  chanOf x (d.wire e.rq) (d.wire e.ak) (e.ws.map d.wire)

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- **The consistency predicate of a map entry, on the parsed netlist** (decidable): `rg` is
a gate, a 1-input buffer, reading `dw` and driving exactly input `i` of the pin's select gate;
`dw` is one of the bus wires; every wire is a wire of `d`. -/
def entOK (j : Fin N) (p : Fin (net.ar j)) (i : Nat) (e : SelEnt) : Bool :=
  decide (e.rg < d.gates.length) && decide ((gt d e.rg).k = 1) &&
  decide (InitSpec (gt d e.rg) (fun v => v 0)) &&
  ((gt d e.rg).ins.getD 0 0 == e.dw) &&
  ((gt d e.rg).out == (gt d (selGate net rn j p)).ins.getD i 0) &&
  e.ws.contains e.dw && decide (e.rq < d.n) && decide (e.ak < d.n) && e.ws.all (fun w => decide (w < d.n))

theorem entOK_spec {j : Fin N} {p : Fin (net.ar j)} {i : Nat} {e : SelEnt} (h : entOK d net rn j p i e = true) :
    e.rg < d.gates.length ∧ isBuf (gt d e.rg) ∧ (gt d e.rg).ins.getD 0 0 = e.dw ∧
      (gt d e.rg).out = (gt d (selGate net rn j p)).ins.getD i 0 ∧ e.dw ∈ e.ws := by
  simp only [entOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, hk⟩, hs⟩, hin⟩, hout⟩, hw⟩, _⟩, _⟩, _⟩ := h
  exact ⟨hg, ⟨hk, hs⟩, hin, hout, hw⟩

end

/-! ## Stability of a select pin wire from H_BUNDLE -/

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include hsat h0 h1

/-- **Per-literal stability from C's H_BUNDLE.** For a checked entry `e` of select literal
`i` of a pin with select band low end `sLo` and copy band high end `cHi`: if the entry's
channel satisfies H_BUNDLE and (H_SEL_TX) is mid-transaction at every `s ≥ O k` with
`s + sLo + lo(rg) ≤ u + cHi` for every `u` in the source's transaction `k`, then the select
gate's input wire equals `dw`'s value at `O k` from `O k + hi(rg)` on, over exactly the window
`design_verdict9_sel` needs. -/
theorem stab_of_held {e : SelEnt} {L : Nat} {i : Nat}
    (hg : e.rg < d.gates.length) (hb : isBuf (gt d e.rg)) (hin : (gt d e.rg).ins.getD 0 0 = e.dw)
    (hout : (gt d e.rg).out = (gt d L).ins.getD i 0) (hw : e.dw ∈ e.ws)
    (hheld : Ops.Held (e.ch x)) (M : Nat → Nat) (O : Nat → Nat) (sLo cHi : Nat)
    (htx : ∀ k u s, M u = 2 * k + 1 → O k ≤ s → s + sLo + (gt d e.rg).lo ≤ u + cHi →
      Ops.inTx (e.ch x) s = true) :
    ∀ k t u, M u = 2 * k + 1 → O k + (gt d e.rg).hi ≤ t → t + sLo ≤ u + cHi →
      x (d.wire ((gt d L).ins.getD i 0)) t = x (d.wire e.dw) (O k) := by
  intro k t u hu ht htu
  have hlh := warp_lo_le_hi (wf_warp hsat hg (by rw [hb.1]; omega))
  rw [← hout]
  refine route_hold hsat h0 h1 hg hb (a := O k) (e := t - (gt d e.rg).lo) ?_ ht (by omega)
  intro s hs1 hs2
  rw [hin]
  have hmem : d.wire e.dw ∈ e.ws.map d.wire := List.mem_map.mpr ⟨e.dw, hw, rfl⟩
  exact held_wire (rq := d.wire e.rq) (ak := d.wire e.ak) hheld
    (fun s' h1' h2' => htx k u s' hu h1' (by omega)) hmem hs1 hs2

end

/-! ## The verdict with SelOK from C's H_BUNDLE at the real pins -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9` with SelOK at the real pins from C's H_BUNDLE.** Same checks and
hypotheses as `design_verdict9` (HDsub proved), plus a select map `m` whose entries pass
`entOK` on the parsed netlist (checked by `xselhold`), except that `bh.SelOK` is replaced by:
* SelOK at the VIRTUAL filtered pins (part of H_ARB);
* for every REAL filtered pin `(j, p)` and select literal `sb` (entry `e = m j p sb.1`):
  - **C's H_BUNDLE** `Ops.Held (e.ch x)` of the mapped channel, on A's trace;
  - **H_SEL_TX**: that channel is mid-transaction at every `s ≥ O k` with
    `s + selLo + lo(rg) ≤ u + hiC` for every copy and every `u` at which the source shows
    transaction `k` (the hold half; `Events9SelHold`);
  - **H_SEL_SETUP**: `O k + hi(rg) + selHi ≤ R k + loC` for every copy, with `R k` a lower
    bound of transaction `k`'s times (the setup half);
  - `sel` is `selFn` of the bus-wire values at `O k`. -/
theorem design_verdict9_selC (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (m : (j : Fin N) → Fin (net.ar j) → Nat → SelEnt)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts →
        (∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
          bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
          bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2)) →
        ∀ (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
          (O : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat),
        (∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          Ops.Held ((m j p sb.1).ch x)) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k u s, (rn j).virt = false →
          net.pk j p = PK.filt → sb ∈ selLits net rn j p → bh.M u (net.src j p) = 2 * k + 1 →
          O j p sb.1 k ≤ s → s + selLo d net rn j p + (gt d (m j p sb.1).rg).lo ≤ u + b.hiC j p i →
          Ops.inTx ((m j p sb.1).ch x) s = true) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
          sb ∈ selLits net rn j p →
          O j p sb.1 k + (gt d (m j p sb.1).rg).hi + selHi d net rn j p ≤ R j p k + b.loC j p i) →
        (∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
          bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u) →
        (∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
          sel (net.grp j p) k = selFn (selLits net rn j p)
            (fun i => x (d.wire (m j p i).dw) (O j p i k))) →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = Formal.Core.XAudit.Events.ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsv⟩ := design_beh8_sv hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R O hheld htx hsetup hwin hsel rB rX rL rG t j hv => ?_⟩
  let S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat :=
    fun j p i k => O j p i k + (gt d (m j p i).rg).hi
  let vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool :=
    fun j p i k => x (d.wire (m j p i).dw) (O j p i k)
  have hstab : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k t u, (rn j).virt = false →
      net.pk j p = PK.filt → sb ∈ selLits net rn j p → bh.M u (net.src j p) = 2 * k + 1 →
      S0 j p sb.1 k ≤ t → t + selLo d net rn j p ≤ u + b.hiC j p i →
      x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0)) t = vb j p sb.1 k := by
    intro j p sb i k t u hvf hk hsb hu ht htu
    obtain ⟨hg, hb, hin, hout, hw⟩ := entOK_spec d net rn (hm j p sb hvf hk hsb)
    exact stab_of_held hsat h0 h1 hg hb hin hout hw (hheld j p sb hvf hk hsb)
      (fun u => bh.M u (net.src j p)) (O j p sb.1) (selLo d net rn j p) (b.hiC j p i)
      (fun k u s h1' h2' h3' => htx j p sb i k u s hvf hk hsb h1' h2' h3') k t u hu ht htu
  have hselok : bh.SelOK :=
    selOK_real hsat hr bh hsv hvirt R S0 vb hwin
      (fun j p sb i k hvf hk hsb => hsetup j p sb i k hvf hk hsb) hstab hsel
  rw [← hreal j hv t]
  exact verdict9 bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hselok t j

end

end Formal.Core.XAudit.Events9SelC
