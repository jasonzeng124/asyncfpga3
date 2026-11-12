import Formal.Net.OpsJoin
import Formal.Net.OpsFork
import Formal.Net.OpsSteer
import Formal.Net.CapstoneSrc

/-!
# Probe C-8w: in the zero-delay Ops model, H_BUNDLE propagates through cells

The capstone's `H_BUNDLE : ∀ c, Held (ch c)` is a hypothesis on traces that ALSO satisfy the
cells' zero-delay data equations (`Join.dat : o.dat t = g (inputs at t)`, `Fork.dat`,
`Steer.dat`, the link's H_LATCH_OPEN / H_LATCH_HOLD; H_DATA_COMB and H_LATCH_COMB of
`C-gcd_hw-hypotheses.md`). On such traces a channel's bus is a zero-delay function of upstream
buses, so whether it moves mid-transaction is a question of event ORDER (does an upstream bus move
while this channel is busy), not of delay. This file proves that, cell by cell, the output's
bundling follows from the inputs' bundling and the cell's handshake invariant:

* `join_held`  (bd_join + compute, and bjoin): output in transaction ⇒ every input in transaction
  (`JInv`), and the bus is `g` of the input buses;
* `fork_held`  (bd_fork): branch in transaction ⇒ input in transaction (`FInv`);
* `steer_held` (bd_steer): either branch in transaction ⇒ the joined input in transaction (`SInv`);
* `src_held`   (bd_src): the bus is constant;
* 8l's `Link.link_held` already gives the link stage.

Consequence for O6 (notes/C-8w-bundle.md): tcheck's rules cannot be "what discharges H_BUNDLE"
on the capstone's traces, because there H_BUNDLE is (per cell) a protocol consequence. The timing
content sits in the refinement from the physical circuit to these zero-delay traces (each latch
captures the zero-delay value; each select LUT reads the settled select), which is where
`Formal.Timing.Obl.held_of_tx` (physical bundling at a capture point, from tcheck verdicts)
is used.

What is NOT proved: the network-level statement "H_BUNDLE on every channel follows from the
sources". Each lemma below needs the inputs' `Held` at the SAME step, so on a cycle the
dependency is circular; closing it needs a storage argument (on every cycle some latch is closed
while the channels after it are busy) and also the mux, muxn and arbiter cells (not done here).
-/

namespace Formal.Net.CapstoneBundle
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.Ops.Join Formal.Net.Ops.Fork
  Formal.Net.Ops.Steer

theorem tx_of_jinv {or oa r k : Bool} (h : JInv or oa r k = true) (ho : (or || oa) = true) :
    (r || k) = true := by
  revert h ho; cases or <;> cases oa <;> cases r <;> cases k <;> simp [JInv]

theorem tx_of_finv {ar aa r k : Bool} (h : FInv ar aa r k = true) (ho : (r || k) = true) :
    (ar || aa) = true := by
  revert h ho; cases ar <;> cases aa <;> cases r <;> cases k <;> simp [FInv]

/-- **Join**: bundled inputs ⇒ bundled output. -/
theorem join_held {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : Join g is o)
    (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) (hh : ∀ i ∈ is, Held i) : Held o := by
  have hinv : ∀ t, ∀ i ∈ is, JInv (o.req t) (o.ack t) (i.req t) (i.ack t) = true :=
    fun t => join_inv J hpo.1.2 (fun i hi => (hpi i hi).1.1) t
      (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩)
  intro t h0 h1
  rw [J.dat t, J.dat (t + 1)]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hh i hi t (tx_of_jinv (hinv t i hi) h0) (tx_of_jinv (hinv (t + 1) i hi) h1)

/-- **Fork**: bundled input ⇒ every branch bundled. -/
theorem fork_held {a : Chan} {os : List Chan} (F : Fork a os) (hpa : Protocol a)
    (hpo : ∀ o ∈ os, Protocol o) (hh : Held a) : ∀ o ∈ os, Held o := by
  have hinv : ∀ t, ∀ o ∈ os, FInv (a.req t) (a.ack t) (o.req t) (o.ack t) = true :=
    fun t => fork_inv F hpa.1.1 (fun o ho => (hpo o ho).1.2) t
      (fun s _ => ⟨hpa.2 s, fun o ho => (hpo o ho).2 s⟩)
  intro o ho t h0 h1
  rw [F.dat o ho t, F.dat o ho (t + 1)]
  exact hh t (tx_of_finv (hinv t o ho) h0) (tx_of_finv (hinv (t + 1) o ho) h1)

theorem tx_of_sinv {jr ja s rT kT rF kF : Bool} (h : SInv jr ja s rT kT rF kF = true)
    (b : Bool) (ho : (if b then (rT || kT) else (rF || kF)) = true) : (jr || ja) = true := by
  revert h ho
  cases jr <;> cases ja <;> cases s <;> cases rT <;> cases kT <;> cases rF <;> cases kF <;>
    cases b <;> simp [SInv, FInv]

/-- **Steer**: bundled joined input ⇒ both branches bundled. -/
theorem steer_held {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b)) (hh : Held j) :
    ∀ b, Held (out b) := by
  have hinv := fun t => steer_inv S hpj.1.1 (fun b => (hpo b).1.2) hh t
    (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)
  intro b t h0 h1
  rw [S.dat b t, S.dat b (t + 1)]
  have tx : ∀ u, inTx (out b) u = true → inTx j u = true := by
    intro u hu
    apply tx_of_sinv (hinv u) b
    cases b <;> simpa [inTx] using hu
  exact congrArg f (hh t (tx t h0) (tx (t + 1) h1))

/-- **Source**: the bus is the constant literal. -/
theorem src_held {z : Chan} {v : Nat} (S : Capstone.Src z v) : Held z := by
  intro t _ _
  rw [S.dat t, S.dat (t + 1)]

end Formal.Net.CapstoneBundle
