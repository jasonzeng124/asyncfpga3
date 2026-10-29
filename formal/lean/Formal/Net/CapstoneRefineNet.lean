import Formal.Net.CapstoneRefine

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

`held_net`: these give `∀ c, Held (ch c)`, the capstone's H_BUNDLE, on ANY network.
The gcd_hw instance (`gcd_hw_circuit_safe_phys`) and its joint witness are in
`Formal.Net.CapstoneRefineGcd`.
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
  held_of_agree (c := ch c) (P := obsCh ch pdat c) rfl rfl (fun t h => H_ZD_AGREE c t h)
    (held_of_bcert (H_TCHECK c) (H_INIT c) (fun t => H_RECV c t))

end Formal.Net.CapstoneRefine
