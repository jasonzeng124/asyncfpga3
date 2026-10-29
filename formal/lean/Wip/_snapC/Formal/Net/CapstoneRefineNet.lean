import Formal.Net.CapstoneRefine
import Formal.Net.CapstoneWalk
import Formal.Net.CapstoneWitness3

/-!
# Probe C-8x: network lift: tcheck rows ⇒ the capstone's H_BUNDLE

The capstone `gcd_hw_circuit_safe3` quantifies over Ops traces `ch` (zero-delay buses). Here a
physical observation of each channel is attached to `ch`:

* `pdat c t`: the bus of channel `c` at its capture pins (a number, as `bv` of the bits), with
  the channel's req/ack those of `ch c` (the Ops handshake wires ARE the physical ones, observed
  at the capture cell; `obsCh ch pdat c`);
* **H_ZD_AGREE**: while `c` is mid-transaction, the zero-delay Ops bus equals the observed bus
  (`(ch c).dat t = pdat c t`). This is the statement that the Ops trace is a refinement image
  of the physical run on the data side; see the note for what it costs (R2-R4).
* **H_RECV**: the receiver rule on every channel (`RecvStep`); 8w's `RecvStep` hypothesis.
  It cannot be taken from `gcd_hw_protocol`, which needs H_BUNDLE (circular).
* **H_TCHECK**: per channel a bundling certificate `BCert`: either a tcheck DAG row
  (rules A/E/F/J: `checkArr` PASS + well-formed netlist + H_TXWIN per transaction), a tcheck cert
  row (rules Hc/Rc/Fd/Z/X: the four conjuncts of `Tcheck.cverdict` + H_TXWIN), or `exempt`, an
  explicit physical `Held` for a channel no tcheck row covers (H_DERIVED; 8w: 376 of 465
  channels are of derived class: fork, link, steer, src outputs).

`held_net`: these give `∀ c, Held (ch c)`, the capstone's H_BUNDLE.
`gcd_hw_circuit_safe_phys`: H_CELLS + H_START_ONCE + the above ⇒ out0 latches only `Nat.gcd a b`.
`gcd_hw_phys_witness`: the 8t witness run with every channel `exempt` meets all hypotheses
(joint consistency only; the tcheck constructors' non-vacuity is `Wit.refine_witness`).
-/

namespace Formal.Net.CapstoneRefine
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing

/-- A per-channel bundling certificate. -/
inductive BCert (P : Chan) : Prop
  /-- tcheck DAG row PASS (`Tcheck.verdict = decide net.WF && checkArr ..`) with H_TXWIN. -/
  | dag (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) (sig : Nat → Nat → Trace)
      (hwf : net.WF) (hc : checkArr net req data setup = true) (runs : ∀ k, Run net (sig k))
      (X : TxWin P sig data (fun k v => changes (sig k req) v)) : BCert P
  /-- tcheck cert row PASS (the four conjuncts of `Tcheck.cverdict`) with H_TXWIN. -/
  | cert (dag late : Netlist) (pot : Nat → Nat) (data targets : List Nat) (setup : Nat)
      (sigD sigL : Nat → Nat → Trace) (hwf : dag.WF) (hpot : potOK late.arcs pot = true)
      (hnz : ∀ q ∈ targets, q ≠ 0)
      (hwin : ∀ d ∈ data, ∀ e l, winArr dag d = some (e, l) → ∀ q ∈ targets, l + setup ≤ pot q)
      (rD : ∀ k, Run dag (sigD k)) (rL : ∀ k, Run late (sigL k))
      (X : TxWin P sigD data (fun k v => ∃ q ∈ targets, changes (sigL k q) v)) : BCert P
  /-- H_DERIVED: no tcheck row; physical bundling assumed. -/
  | exempt (h : Held P) : BCert P

theorem held_of_bcert {P : Chan} (B : BCert P) (hinit : Init P) (hrecv : ∀ t, RecvStep P t) :
    Held P := by
  cases B with
  | dag net req data setup sig hwf hc runs X => exact held_dag hwf hc runs X hinit hrecv
  | cert dag late pot data targets setup sigD sigL hwf hpot hnz hwin rD rL X =>
    exact held_cert hwf hpot hnz hwin rD rL X hinit hrecv
  | exempt h => exact h

/-- The observed (physical) channel: the Ops handshake wires, the capture-pin bus. -/
def obsCh {C : Type} (ch : C → Chan) (pdat : C → Nat → Nat) (c : C) : Chan :=
  ⟨(ch c).req, (ch c).ack, pdat c⟩

/-- Physical bundling transfers to an Ops trace that agrees with it mid-transaction. -/
theorem held_of_agree {c P : Chan} (hreq : P.req = c.req) (hack : P.ack = c.ack)
    (hag : ∀ t, inTx c t = true → c.dat t = P.dat t) (hP : Held P) : Held c := by
  intro t h0 h1
  have e : ∀ u, inTx P u = inTx c u := fun u => by simp [inTx, hreq, hack]
  rw [hag t h0, hag (t + 1) h1]
  exact hP t (by rw [e]; exact h0) (by rw [e]; exact h1)

/-- **Network lift (any network)**: per-channel certificates + H_ZD_AGREE + H_RECV + reset ⇒
H_BUNDLE on every channel of the Ops trace. -/
theorem held_net {C : Type} (ch : C → Chan) (pdat : C → Nat → Nat)
    (H_INIT : ∀ c, Init (ch c))
    (H_RECV : ∀ c t, RecvStep (ch c) t)
    (H_ZD_AGREE : ∀ c t, inTx (ch c) t = true → (ch c).dat t = pdat c t)
    (H_TCHECK : ∀ c, BCert (obsCh ch pdat c)) : ∀ c, Held (ch c) := fun c =>
  held_of_agree rfl rfl (H_ZD_AGREE c)
    (held_of_bcert (H_TCHECK c) (H_INIT c) (H_RECV c))

end Formal.Net.CapstoneRefine

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Timing
open Formal.Net.CapstoneRefine

/-- Reset of every channel, from the gate models alone (no H_BUNDLE needed). -/
theorem gcd_hw_init (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o)) : ∀ c, Init (ch c) := fun c =>
  ⟨(cell_proto ch (srcV a b) (opAt (net.prod c)) (H_CELLS _) (dist_of _ (ops_ok _))).initOut c
      ((net.prod_iff c _).2 rfl),
   (cell_proto ch (srcV a b) (opAt (net.cons c)) (H_CELLS _) (dist_of _ (ops_ok _))).initIn c
      ((net.cons_iff c _).2 rfl)⟩

/-- **gcd_hw safety from the physical bundling certificates.** H_BUNDLE of
`gcd_hw_circuit_safe3` is replaced by: per channel, a tcheck row PASS with H_TXWIN (or an
explicit H_DERIVED exemption), H_ZD_AGREE and H_RECV. -/
theorem gcd_hw_circuit_safe_phys (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (pdat : Fin NC → Nat → Nat)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_RECV : ∀ c t, RecvStep (ch c) t)
    (H_ZD_AGREE : ∀ c t, inTx (ch c) t = true → (ch c).dat t = pdat c t)
    (H_TCHECK : ∀ c, BCert (obsCh ch pdat c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe3 a b ha hb ch H_CELLS
    (held_net ch pdat (gcd_hw_init a b ch H_CELLS) H_RECV H_ZD_AGREE H_TCHECK) H_START_ONCE

end Formal.Net.CapNet.Gcd

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapstoneRefine

/-- **Joint consistency** of the hypotheses of `gcd_hw_circuit_safe_phys` (8t's witness run,
observed bus = Ops bus, every channel `exempt`). It does NOT exercise the tcheck constructors;
`Formal.Net.CapstoneRefine.Wit.refine_witness` does, on one channel. -/
theorem gcd_hw_phys_witness :
    (∀ o : Fin NO, Cell chW (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chW start).req) t ≤ 1) ∧
    (∀ c t, RecvStep (chW c) t) ∧
    (∀ c t, inTx (chW c) t = true → (chW c).dat t = (fun c => (chW c).dat) c t) ∧
    (∀ c, BCert (obsCh chW (fun c => (chW c).dat) c)) :=
  ⟨w_cells, w_start_once,
   fun c t => ((gcd_hw_protocol 12 18 chW w_cells w_held c).2 t).2,
   fun _ _ _ => rfl,
   fun c => BCert.exempt (w_held c)⟩

end Formal.Net.CapNet.Wit
