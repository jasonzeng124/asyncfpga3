import Formal.Net.EndToEndRace
import Formal.Net.HandshakeMuller

/-!
# Probe C-8e: the verified checker accepts the routed pipe ⇒ the pipe is a FIFO

Connects track 8a (`muller_pipeline`: an n-stage Muller pipeline is a FIFO,
given per-link timing obligations `SetupHold`, `Sep`, `Hold` and a latch cell
contract `H_LATCH`) with track 10a (`check`, proved sound against the
bounded-delay `Run` semantics) through one theorem, `end_to_end`.

## Where the two time bases did not match, and the refinement

8a's `MullerStage` is a node-level speed-independent model: the C-element at
step `t` reads the CURRENT values of its neighbours' nodes (zero wire delay),
the fork of each node `c` is isochronic (`req_out = ack_in = latch enable`),
and data wires have zero delay. 10a's `Run` is a single-launch DAG: every arc
has a pin trace related to its source by a delay in `[lo, hi]`, node 0
switches once, and a cell is a zero-delay function of its pins. The
mismatches, and what is done about each:

1. **Wire delay at the C-element pins.** Here (`PipeRun`) every controller pin
   is the routed copy of its source: `R` pin of stage `k` =
   `shift (dR k) (x (k-1))`, `A` pin = `shift (dA k) (x (k+1))`, and the real
   `bd_c2n` INIT is evaluated on the PINS (`H_CEL`). The fork of each node is
   no longer isochronic: every branch has its own delay. 8a's node-level
   rules are then DERIVED, not assumed: `PinLink.protocol` proves the node
   pair of every link obeys the four-phase protocol, by a change-count
   invariant (`PinLink.inv`: the receiver never has more changes than the
   sender had `dR` ticks ago, the sender at most one more than the receiver
   had `dA` ticks ago). That gives 8a's `H_CEL_SI` (`cel_si`), with
   `H_NODE` true by construction (channels are defined at the nodes).
2. **Multi-token, cyclic run vs single launch.** The check is applied to a
   launch-relative race netlist (`EndToEndRace.fan2`). It transfers to EVERY
   token of the cyclic run because a fixed delay is time invariant (a pin is
   an exact shift of its source), so the response to any later event is the
   step response moved in time. The event-ordering facts that turn the
   per-path delay bounds into 8a's `Sep`/`Hold`/`SetupHold` are again the
   change counts (`PinLink.sep`, `PinLink.hold`, `PinLink.srcData`,
   `PinLink.openWidth`).
3. **Per-event vs per-run delay.** This works for 10a's `FixedRun` reading
   (H_FIXED_DELAY: one delay per arc per run, inside its interval), not for
   per-event `BoundedDelay`: with per-event delay a pin may echo an old value
   after following a new one (a glitch), the change counts of pin and node
   then differ, and the counting argument breaks. 10a's `corr` example shows
   that such glitches are exactly what makes the per-event semantics differ.
   Every `FixedRun` is a `Run`, so the checker side is unaffected.
4. **Data wires and the latch enable fan-out.** 8a's `H_LATCH` is a
   node-level contract with zero data-wire delay. Here it is DERIVED
   (`latch_contract`) from a pin-level LUT latch (`latchF`, the `B8` INIT of
   `bd_latch`, `latch_pair` covers both halves of the LUT6_2), whose D pin is
   `shift (dD j b) (Q j b)` (the data bus wire of bit `b`) and whose enable
   pin is `shift (dG j b) (x (j+1))` (the enable wire of that LUT). Three
   checks per bit make it hold: setup (`dD ≤ m-1`), hold
   (`dG ≤ dD + h`), and open width (the enable pin must see the open phase:
   `dG ≤ dR + dA + 1` over the next stage's round trip).

## The obligations as checker races (`checkPipe`)

All in `race2 E L s` form ("late path `L` + `s` ≤ early path `E`", run by
10a's `check` on the netlist `fan2 E L`). `R.req k`, `R.ack k`, `R.en j b`,
`R.dat j b` are the routed arc lists (wire / delay-element LUT / wire / LUT
pin, ...).
* source setup  `race2 (req 1) [] (m-2)`  (`SetupHold m h (ch 0)`, setup half)
* source hold   `race2 (ack 0) [] (h-1)`  (`SetupHold`, hold half)
* `Sep m` link j+1  `race2 (req (j+2)) [] (m-1)`  (rule I: the SDELAY line)
* `Hold h` link j+1 `race2 (ack (j+1)) [] (h-1)`  (rule H: the DACK line)
* latch j bit b: `race2 [(m-1,m-1)] (dat j b) 0`, `race2 (dat j b ++ [(h,h)]) (en j b) 0`,
  `race2 (req (j+2) ++ ack (j+1) ++ [(1,1)]) (en j b) 0`.
-/

namespace Formal.Net.EndToEnd
open Formal.Net Formal.Net.Handshake Formal.Timing Formal.Cells

/-! ## Change counts -/

/-- `s` changes between `t` and `t+1`. -/
def chg (s : Trace) (t : Nat) : Bool := decide (s (t + 1) ≠ s t)

/-- Number of changes of `s` before `t`. -/
def N (s : Trace) (t : Nat) : Nat := cnt (chg s) t

theorem N_zero (s : Trace) : N s 0 = 0 := rfl

theorem N_move {s : Trace} {t : Nat} (h : s (t + 1) ≠ s t) : N s (t + 1) = N s t + 1 := by
  simp [N, cnt, chg, h]

theorem N_stay {s : Trace} {t : Nat} (h : s (t + 1) = s t) : N s (t + 1) = N s t := by
  simp [N, cnt, chg, h]

theorem N_mono {s : Trace} {a b : Nat} (h : a ≤ b) : N s a ≤ N s b := cnt_mono _ h

theorem parity {s : Trace} (h0 : s 0 = false) : ∀ t, s t = decide (N s t % 2 = 1) := by
  intro t
  induction t with
  | zero => simp [h0, N_zero]
  | succ t ih =>
    by_cases h : s (t + 1) = s t
    · rw [N_stay h, h, ih]
    · rw [N_move h]
      have hn : s (t + 1) = !s t := by
        cases h1 : s t <;> cases h2 : s (t + 1) <;> simp_all
      rw [hn, ih]
      by_cases hp : N s t % 2 = 1
      · have : ¬ (N s t + 1) % 2 = 1 := by omega
        simp [hp, this]
      · have : (N s t + 1) % 2 = 1 := by omega
        simp [hp, this]

theorem par_eq {s s' : Trace} (h0 : s 0 = false) (h0' : s' 0 = false) {a b : Nat}
    (h : s a = s' b) : N s a % 2 = N s' b % 2 := by
  rw [parity h0 a, parity h0' b, decide_eq_decide] at h
  by_cases h1 : N s a % 2 = 1
  · have := h.mp h1; omega
  · have : ¬ N s' b % 2 = 1 := fun h2 => h1 (h.mpr h2)
    omega

theorem par_ne {s s' : Trace} (h0 : s 0 = false) (h0' : s' 0 = false) {a b : Nat}
    (h : s a ≠ s' b) : N s a % 2 ≠ N s' b % 2 := by
  intro he; apply h
  rw [parity h0 a, parity h0' b, he]

theorem val_eq {s s' : Trace} (h0 : s 0 = false) (h0' : s' 0 = false) {a b : Nat}
    (h : N s a % 2 = N s' b % 2) : s a = s' b := by
  rw [parity h0 a, parity h0' b, h]

theorem N_const {s : Trace} {a : Nat} : ∀ k, (∀ u, a ≤ u → u < a + k → s (u + 1) = s u) →
    N s (a + k) = N s a := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [← Nat.add_assoc, N_stay (h (a + k) (by omega) (by omega))]
    exact ih (fun u h1 h2 => h u h1 (by omega))

theorem stable_of {D : Trace} {a b : Nat} (h : ∀ t, a ≤ t → t < b → D (t + 1) = D t) :
    ∀ s, a ≤ s → s ≤ b → D s = D a := by
  intro s h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, s = a + k := ⟨s - a, by omega⟩
  clear h1
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, h (a + k) (by omega) (by omega)]; exact ih (by omega)

/-! ## One link with delayed pins on both ends -/

/-- A four-phase link between a sender node `p` and a receiver node `q`, each
reading the other through a fixed wire delay: the receiver's pin is
`p (t - dR)`, the sender's pin is `q (t - dA)` (`shift d s t = s (t - d)`,
`shift_eq`). Each party moves only when its PIN view allows (sender: equal;
receiver: different). This is what an excited-only C-element on its pins, a
pin-level source or a pin-level sink gives. -/
structure PinLink (p q : Trace) (dR dA : Nat) : Prop where
  p0 : p 0 = false
  q0 : q 0 = false
  send : ∀ t, p (t + 1) ≠ p t → p t = q (t - dA)
  recv : ∀ t, q (t + 1) ≠ q t → q t ≠ p (t - dR)

namespace PinLink
variable {p q : Trace} {dR dA : Nat}

/-- **Count invariant.** The receiver never has more changes than the sender
had `dR` ticks earlier; the sender has at most one more change than the
receiver had `dA` ticks earlier. -/
theorem inv (L : PinLink p q dR dA) : ∀ t, N q t ≤ N p (t - dR) ∧ N p t ≤ N q (t - dA) + 1 := by
  intro t
  induction t with
  | zero => simp [N_zero]
  | succ t ih =>
    have m1 : N p (t - dR) ≤ N p (t + 1 - dR) := N_mono (by omega)
    have m2 : N q (t - dA) ≤ N q (t + 1 - dA) := N_mono (by omega)
    have m3 : N p (t - dR) ≤ N p t := N_mono (by omega)
    have m4 : N q (t - dA) ≤ N q t := N_mono (by omega)
    constructor
    · by_cases hq : q (t + 1) = q t
      · rw [N_stay hq]; omega
      · rw [N_move hq]
        have := par_ne L.q0 L.p0 (L.recv t hq)
        omega
    · by_cases hp : p (t + 1) = p t
      · rw [N_stay hp]; omega
      · rw [N_move hp]
        have := par_eq L.p0 L.q0 (L.send t hp)
        omega

theorem send_eq (L : PinLink p q dR dA) {t : Nat} (hp : p (t + 1) ≠ p t) :
    N p t = N q (t - dA) := by
  have i := L.inv t
  have m3 : N p (t - dR) ≤ N p t := N_mono (by omega)
  have m4 : N q (t - dA) ≤ N q t := N_mono (by omega)
  have := par_eq L.p0 L.q0 (L.send t hp)
  omega

theorem recv_lt (L : PinLink p q dR dA) {t : Nat} (hq : q (t + 1) ≠ q t) :
    N q t < N p (t - dR) := by
  have i := L.inv t
  have := par_ne L.q0 L.p0 (L.recv t hq)
  omega

theorem bounds (L : PinLink p q dR dA) (t : Nat) : N q t ≤ N p t ∧ N p t ≤ N q t + 1 := by
  have i := L.inv t
  have m3 : N p (t - dR) ≤ N p t := N_mono (by omega)
  have m4 : N q (t - dA) ≤ N q t := N_mono (by omega)
  omega

/-- At a receiver move the sender is exactly one change ahead. -/
theorem at_recv (L : PinLink p q dR dA) {t : Nat} (hq : q (t + 1) ≠ q t) : N p t = N q t + 1 := by
  have := L.recv_lt hq
  have b := L.bounds t
  have m3 : N p (t - dR) ≤ N p t := N_mono (by omega)
  omega

/-- **The node pair obeys 8a's four-phase protocol.** -/
theorem protocol (L : PinLink p q dR dA) (d : Nat → Nat) : Protocol ⟨p, q, d⟩ := by
  refine ⟨⟨L.p0, L.q0⟩, fun t => ⟨fun hp => ?_, fun hq => ?_⟩⟩
  · have := L.send_eq hp
    have b := L.bounds t
    have m4 : N q (t - dA) ≤ N q t := N_mono (by omega)
    exact val_eq L.p0 L.q0 (by omega)
  · have := L.at_recv hq
    intro he
    have := par_eq L.q0 L.p0 he
    omega

/-- `Sep`: the receiver's next change after the sender's change at `e` comes
at least `dR + 1` ticks later. -/
theorem sep (L : PinLink p q dR dA) {m : Nat} (hm : m ≤ dR + 1) {e e' : Nat}
    (he : p (e + 1) ≠ p e) (he' : q (e' + 1) ≠ q e') (hlt : e < e') : e + m ≤ e' := by
  have h1 := L.recv_lt he'
  have h2 := L.bounds e'
  have h3 := N_move he
  have h4 : N p (e + 1) ≤ N p e' := N_mono (by omega)
  apply Classical.byContradiction; intro hc
  have : N p (e' - dR) ≤ N p e := N_mono (by omega)
  omega

/-- `Hold`: after the receiver's fall at `e'`, the sender stays low for
`dA + 1` ticks. -/
theorem hold (L : PinLink p q dR dA) {h : Nat} (hh : h ≤ dA + 1) {e' : Nat}
    (hq1 : q e' = true) (hq2 : q (e' + 1) = false) :
    ∀ s, e' < s → s ≤ e' + h → p s = false := by
  have hmv : q (e' + 1) ≠ q e' := by rw [hq1, hq2]; decide
  have ha := L.at_recv hmv
  have hodd : N q e' % 2 = 1 := by
    have := parity L.q0 e'; rw [hq1] at this; simpa using this.symm
  have key : ∀ k, k ≤ dA + 1 → N p (e' + k) = N p e' := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      by_cases hp : p (e' + k + 1) = p (e' + k)
      · rw [← Nat.add_assoc, N_stay hp]; exact ih (by omega)
      · have := L.send_eq hp
        have : N q (e' + k - dA) ≤ N q e' := N_mono (by omega)
        have := ih (by omega)
        omega
  intro s h1 h2
  have := key (s - e') (by omega)
  rw [show e' + (s - e') = s by omega] at this
  have hv := val_eq (s := p) (s' := p) L.p0 L.p0 (a := s) (b := e') (by rw [this])
  rw [hv, parity L.p0 e']
  simp; omega

/-- Open width: a sender high phase `(r, e]` lasts at least the round trip. -/
theorem openWidth (L : PinLink p q dR dA) {r e : Nat} (hr0 : p r = false) (hr1 : p (r + 1) = true)
    (he1 : p (e + 1) = false) (hopen : ∀ u, r < u → u ≤ e → p u = true) (hre : r < e) :
    r + dR + dA + 2 ≤ e := by
  have hmr : p (r + 1) ≠ p r := by rw [hr0, hr1]; decide
  have h1 := N_move hmr
  have h2 : N p (r + 1 + (e - (r + 1))) = N p (r + 1) :=
    N_const _ (fun u hu1 hu2 => by rw [hopen u (by omega) (by omega), hopen (u + 1) (by omega) (by omega)])
  rw [show r + 1 + (e - (r + 1)) = e by omega] at h2
  have hme : p (e + 1) ≠ p e := by rw [he1, hopen e hre (Nat.le_refl _)]; decide
  have h3 := L.send_eq hme
  obtain ⟨r2, hr2, hc2, hn2⟩ := cnt_witness (chg q) (e - dA) (N p r) (by
    show N q (e - dA) = N p r + 1; omega)
  have hq2 : q (r2 + 1) ≠ q r2 := by simpa [chg] using hc2
  have h4 := L.recv_lt hq2
  have hn2' : N q r2 = N p r := hn2
  apply Classical.byContradiction; intro hc
  have : N p (r2 - dR) ≤ N p r := N_mono (by omega)
  omega

/-- Source data: if the sender's data `D` changes only at the sender's rises,
then around every receiver fall `e` it is stable on `[e+1-m, e+h]`. -/
theorem srcData (L : PinLink p q dR dA) {D : Trace}
    (hD : ∀ t, D (t + 1) ≠ D t → p t = false ∧ p (t + 1) = true)
    {m h : Nat} (hm1 : 0 < m) (hm : m ≤ dR + 2) (hh : h ≤ dA + 1) {e : Nat}
    (hq1 : q e = true) (hq2 : q (e + 1) = false) :
    ∀ s, e + 1 - m ≤ s → s ≤ e + h → D s = D e := by
  have hmv : q (e + 1) ≠ q e := by rw [hq1, hq2]; decide
  have ha := L.at_recv hmv
  have hodd : N q e % 2 = 1 := by
    have := parity L.q0 e; rw [hq1] at this; simpa using this.symm
  have noch : ∀ t, e + 1 - m ≤ t → t < e + h → D (t + 1) = D t := by
    intro t ht1 ht2
    apply Classical.byContradiction; intro hc
    obtain ⟨hp0, hp1⟩ := hD t hc
    have hmp : p (t + 1) ≠ p t := by rw [hp0, hp1]; decide
    have hev : N p t % 2 = 0 := by
      have := parity L.p0 t; rw [hp0] at this
      have : ¬ N p t % 2 = 1 := by simpa using this.symm
      omega
    by_cases hte : e ≤ t
    · have h1 := L.send_eq hmp
      have h2 : N p e ≤ N p t := N_mono hte
      by_cases hle : t - dA ≤ e
      · have : N q (t - dA) ≤ N q e := N_mono hle
        omega
      · omega
    · have h1 := N_move hmp
      have h2 : N p (t + 1) ≤ N p e := N_mono (by omega)
      obtain ⟨r1, hr1, hc1, hn1⟩ := cnt_witness (chg q) e (N q e - 1) (by
        show N q e = N q e - 1 + 1; omega)
      have hq' : q (r1 + 1) ≠ q r1 := by simpa [chg] using hc1
      have h3 := L.recv_lt hq'
      have hn1' : N q r1 = N q e - 1 := hn1
      by_cases hle : r1 - dR ≤ t
      · have : N p (r1 - dR) ≤ N p t := N_mono hle
        omega
      · omega
  intro s h1 h2
  rw [stable_of noch s h1 h2, stable_of noch e (by omega) (by omega)]

end PinLink

/-! ## The latch cell -/

/-- `bd_latch`, odd-bit LUT6 (and the O5 half of the pair): INIT `B8B8…`,
pins `[I0 = d, I1 = en, I2 = q]`. -/
def INIT_latch : Nat := 0xB8B8B8B8B8B8B8B8
def latchF (d en q : Bool) : Bool := lutB INIT_latch [d, en, q, false, false, false]

theorem latchF_eq : ∀ d en q : Bool, latchF d en q = if en then d else q := by decide

/-- The paired `bd_latch` LUT6_2 (`64'hFF33_CC00_B8B8_B8B8`, `I5 = 1`): both
outputs are the same transparent-latch function, on bits `i` (O5) and `i+1` (O6). -/
def INIT_latch2 : Nat := 0xFF33CC00B8B8B8B8
theorem latch_pair : ∀ d0 en q0 d1 q1 : Bool,
    o5B INIT_latch2 [d0, en, q0, d1, q1, true] = (if en then d0 else q0) ∧
    o6B INIT_latch2 [d0, en, q0, d1, q1, true] = (if en then d1 else q1) := by decide

/-- One latch bit with enable pin `p (t - g)` and D pin `D (t - w)`: closed by
a node fall at `e` after an open phase `(r, e]` long enough for the enable pin
(`r + g + 1 ≤ e`), with D stable on `[e+1-m, e+h]`, `w + 1 ≤ m` and
`g ≤ w + h`, it outputs `D e` from `e+1` until the node reopens. -/
theorem latch_bit {p D O : Trace} {g w m h e r : Nat}
    (hcell : ∀ t, O (t + 1) = latchF (D (t - w)) (p (t - g)) (O t))
    (hopen : ∀ u, r < u → u ≤ e → p u = true) (how : r + g + 1 ≤ e)
    (hw : w + 1 ≤ m) (hg : g ≤ w + h)
    (hD : ∀ s, e + 1 - m ≤ s → s ≤ e + h → D s = D e) :
    ∀ k, (∀ u, e < u → u ≤ e + k + 1 → p u = false) → O (e + k + 1) = D e := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [hcell, latchF_eq, hopen (e - g) (by omega) (by omega)]
    exact hD _ (by omega) (by omega)
  | succ k ih =>
    intro hlow
    rw [show e + (k + 1) + 1 = (e + k + 1) + 1 by omega, hcell, latchF_eq]
    by_cases hc : e + k + 1 ≤ e + g
    · rw [hopen (e + k + 1 - g) (by omega) (by omega)]
      exact hD _ (by omega) (by omega)
    · rw [hlow (e + k + 1 - g) (by omega) (by omega)]
      exact ih (fun u h1 h2 => hlow u h1 (by omega))

/-! ## Bus values -/

/-- A `W`-bit bus as a number (bit 0 least significant). -/
def enc : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | W + 1, f => (if f 0 then 1 else 0) + 2 * enc W (fun b => f (b + 1))

theorem enc_congr : ∀ (W : Nat) (f g : Nat → Bool), (∀ b, b < W → f b = g b) → enc W f = enc W g
  | 0, _, _, _ => rfl
  | W + 1, f, g, h => by
    simp only [enc]
    rw [h 0 (by omega), enc_congr W _ _ (fun b hb => h (b + 1) (by omega))]

theorem enc_inj : ∀ (W : Nat) (f g : Nat → Bool), enc W f = enc W g → ∀ b, b < W → f b = g b
  | 0, _, _, _, b, hb => absurd hb (by omega)
  | W + 1, f, g, h, b, hb => by
    simp only [enc] at h
    have h0 : f 0 = g 0 ∧ enc W (fun b => f (b + 1)) = enc W (fun b => g (b + 1)) := by
      cases hf : f 0 <;> cases hg : g 0 <;> simp [hf, hg] at h ⊢ <;> omega
    cases b with
    | zero => exact h0.1
    | succ b => exact enc_inj W _ _ h0.2 b (by omega)

/-! ## The timed, routed pipeline -/

/-- One run of an `n`-stage `bd_pipe` (Muller stages, `bd_link` default build)
with a `W`-bit bus. Control nodes: `x 0` = source request, `x (j+1)` = node
`c` of stage `j`, `x (n+1)` = sink acknowledge. `Q 0 b` = source data bit
`b`, `Q (j+1) b` = stage `j`'s latch output. Each routed path has ONE delay
for the run (H_FIXED_DELAY; its arcs are tied to the routed intervals by
`Realizes`). -/
structure Pipe where
  x : Nat → Trace
  Q : Nat → Nat → Trace
  /-- `dR k`: node `x (k-1)` → req pin of `x k` (wire, SDELAY / DELAY line, wire, LUT pin). -/
  dR : Nat → Nat
  /-- `dA k`: node `x (k+1)` → ack pin of `x k` (wire, DACK line, wire, LUT pin). -/
  dA : Nat → Nat
  /-- `dG j b`: node `x (j+1)` → EN pin of stage `j`'s latch LUT for bit `b`. -/
  dG : Nat → Nat → Nat
  /-- `dD j b`: `Q j b` → D pin of stage `j`'s latch LUT for bit `b` (data bus wire). -/
  dD : Nat → Nat → Nat

/-- The gate-level hypotheses of a run (all named, see the notes for fidelity). -/
structure PipeRun (n W : Nat) (P : Pipe) : Prop where
  /-- H_RESET: every control node low at 0. -/
  H_RESET : ∀ k, k ≤ n + 1 → P.x k 0 = false
  /-- H_CEL (pin-level SI): stage node `x k` keeps its value or takes the real
  `bd_c2n` INIT evaluated on its PINS (routed copies of its neighbours). -/
  H_CEL : ∀ k, 1 ≤ k → k ≤ n → ∀ t, P.x k (t + 1) = P.x k t ∨
    P.x k (t + 1) = celN (shift (P.dR k) (P.x (k - 1)) t) (shift (P.dA k) (P.x (k + 1)) t) (P.x k t)
  /-- H_SRC: the source moves its request only when its ack pin equals it. -/
  H_SRC : ∀ t, P.x 0 (t + 1) ≠ P.x 0 t → P.x 0 t = shift (P.dA 0) (P.x 1) t
  /-- H_SNK: the sink moves its ack only when its req pin differs from it. -/
  H_SNK : ∀ t, P.x (n + 1) (t + 1) ≠ P.x (n + 1) t → P.x (n + 1) t ≠ shift (P.dR (n + 1)) (P.x n) t
  /-- H_SRC_DATA: source data bits change only together with a request rise. -/
  H_SRC_DATA : ∀ b, b < W → ∀ t, P.Q 0 b (t + 1) ≠ P.Q 0 b t → P.x 0 t = false ∧ P.x 0 (t + 1) = true
  /-- H_LATCH_CELL: the latch LUT on its pins, one tick of cell delay. -/
  H_LATCH_CELL : ∀ j, j < n → ∀ b, b < W → ∀ t, P.Q (j + 1) b (t + 1) =
    latchF (shift (P.dD j b) (P.Q j b) t) (shift (P.dG j b) (P.x (j + 1)) t) (P.Q (j + 1) b t)

/-- 8a's channels, at the nodes: link `j` has request `x j`, acknowledge
`x (j+1)` and data `Q j` read as a number. -/
def ch (W : Nat) (P : Pipe) (j : Nat) : Chan := ⟨P.x j, P.x (j + 1), fun t => enc W (fun b => P.Q j b t)⟩

/-- The routed netlist: one arc-interval list per path. -/
structure Route where
  req : Nat → Path
  ack : Nat → Path
  en : Nat → Nat → Path
  dat : Nat → Nat → Path

/-- The run's per-path delays are sums of per-arc delays inside the routed
intervals (H_FIXED_DELAY + H_ROUTE). -/
def Realizes (R : Route) (n W : Nat) (P : Pipe) : Prop :=
  (∀ k, 1 ≤ k → k ≤ n + 1 → ∃ ds, inPath ds (R.req k) ∧ ds.sum = P.dR k) ∧
  (∀ k, k ≤ n → ∃ ds, inPath ds (R.ack k) ∧ ds.sum = P.dA k) ∧
  (∀ j, j < n → ∀ b, b < W → ∃ ds, inPath ds (R.en j b) ∧ ds.sum = P.dG j b) ∧
  (∀ j, j < n → ∀ b, b < W → ∃ ds, inPath ds (R.dat j b) ∧ ds.sum = P.dD j b)

/-- **The pipeline check**: every obligation as a verified-checker race. -/
def checkPipe (R : Route) (n W m h : Nat) : Bool :=
  decide (0 < m) &&
  race2 (R.req 1) [] (m - 2) && race2 (R.ack 0) [] (h - 1) &&
  (List.range (n - 1)).all (fun j => race2 (R.req (j + 2)) [] (m - 1) && race2 (R.ack (j + 1)) [] (h - 1)) &&
  (List.range n).all (fun j => (List.range W).all (fun b =>
    race2 [(m - 1, m - 1)] (R.dat j b) 0 && race2 (R.dat j b ++ [(h, h)]) (R.en j b) 0 &&
    race2 (R.req (j + 2) ++ R.ack (j + 1) ++ [(1, 1)]) (R.en j b) 0))

/-- The obligations in delay form. -/
structure Timing (n W m h : Nat) (P : Pipe) : Prop where
  m_pos : 0 < m
  src_setup : m ≤ P.dR 1 + 2
  src_hold : h ≤ P.dA 0 + 1
  sep : ∀ j, j + 1 < n → m ≤ P.dR (j + 2) + 1
  hold : ∀ j, j + 1 < n → h ≤ P.dA (j + 1) + 1
  lat_setup : ∀ j, j < n → ∀ b, b < W → P.dD j b + 1 ≤ m
  lat_hold : ∀ j, j < n → ∀ b, b < W → P.dG j b ≤ P.dD j b + h
  lat_open : ∀ j, j < n → ∀ b, b < W → P.dG j b ≤ P.dR (j + 2) + P.dA (j + 1) + 1

theorem race_nil {E : Path} {s : Nat} (hc : race2 E [] s = true) {ds : List Nat}
    (h : inPath ds E) : s ≤ ds.sum := by
  have := race2_sound hc h (dsL := []) trivial
  simpa using this

/-- **Checker ⇒ obligations**, for every fixed-delay realization of the route. -/
theorem timing_of_check {R : Route} {n W m h : Nat} (hc : checkPipe R n W m h = true)
    {P : Pipe} (HR : Realizes R n W P) : Timing n W m h P := by
  simp only [checkPipe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at hc
  obtain ⟨⟨⟨⟨hm, hs1⟩, hs2⟩, hl⟩, hj⟩ := hc
  obtain ⟨Hreq, Hack, Hen, Hdat⟩ := HR
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ds, h1, h2⟩ := Hreq 1 (by omega) (by omega)
    have := race_nil hs1 h1; omega
  · obtain ⟨ds, h1, h2⟩ := Hack 0 (by omega)
    have := race_nil hs2 h1; omega
  · intro j hj1
    obtain ⟨ds, h1, h2⟩ := Hreq (j + 2) (by omega) (by omega)
    have := race_nil (hl j (by omega)).1 h1; omega
  · intro j hj1
    obtain ⟨ds, h1, h2⟩ := Hack (j + 1) (by omega)
    have := race_nil (hl j (by omega)).2 h1; omega
  · intro j hj1 b hb
    obtain ⟨ds, h1, h2⟩ := Hdat j hj1 b hb
    have := race2_sound (hj j hj1 b hb).1.1 (inPath_const (m - 1)) h1
    simp at this; omega
  · intro j hj1 b hb
    obtain ⟨ds, h1, h2⟩ := Hdat j hj1 b hb
    obtain ⟨dg, g1, g2⟩ := Hen j hj1 b hb
    have := race2_sound (hj j hj1 b hb).1.2 (inPath_append h1 (inPath_const h)) g1
    simp at this; omega
  · intro j hj1 b hb
    obtain ⟨dr, r1, r2⟩ := Hreq (j + 2) (by omega) (by omega)
    obtain ⟨da, a1, a2⟩ := Hack (j + 1) (by omega)
    obtain ⟨dg, g1, g2⟩ := Hen j hj1 b hb
    have := race2_sound (hj j hj1 b hb).2 (inPath_append (inPath_append r1 a1) (inPath_const 1)) g1
    simp at this; omega

/-! ## From the timed pipe to 8a's model -/

theorem celN_excited : ∀ r a q : Bool, q ≠ r → q ≠ a → celN r a q = !q := by decide

theorem flip {b c : Bool} (h : c ≠ b) : c = !b := by cases b <;> cases c <;> simp_all

/-- Every link of the routed pipe is a `PinLink`. -/
theorem links {n W : Nat} {P : Pipe} (H : PipeRun n W P) :
    ∀ k, k ≤ n → PinLink (P.x k) (P.x (k + 1)) (P.dR (k + 1)) (P.dA k) := by
  intro k hk
  refine ⟨H.H_RESET k (by omega), H.H_RESET (k + 1) (by omega), ?_, ?_⟩
  · intro t hmv
    by_cases hk0 : k = 0
    · subst hk0; have := H.H_SRC t hmv; rwa [shift_eq] at this
    · rcases H.H_CEL k (by omega) hk t with h | h
      · exact absurd h hmv
      · have := cel_change _ _ _ _ (Or.inr h) hmv
        simp only [shift_eq] at this; exact this.2
  · intro t hmv
    by_cases hkn : k = n
    · subst hkn; have := H.H_SNK t hmv; rwa [shift_eq] at this
    · rcases H.H_CEL (k + 1) (by omega) (by omega) t with h | h
      · exact absurd h hmv
      · have := cel_change _ _ _ _ (Or.inr h) hmv
        simp only [shift_eq, show k + 1 - 1 = k by omega] at this; exact this.1

theorem protocols {n W : Nat} {P : Pipe} (H : PipeRun n W P) :
    ∀ k, k ≤ n → Protocol (ch W P k) := fun k hk => (links H k hk).protocol _

/-- 8a's `H_CEL_SI` (node-level SI step) is DERIVED from the pin-level model. -/
theorem cel_si {n W : Nat} {P : Pipe} (H : PipeRun n W P) {j : Nat} (hj : j < n) :
    ∀ t, P.x (j + 1) (t + 1) = P.x (j + 1) t ∨
      P.x (j + 1) (t + 1) = celN (P.x j t) (P.x (j + 2) t) (P.x (j + 1) t) := by
  intro t
  by_cases hmv : P.x (j + 1) (t + 1) = P.x (j + 1) t
  · exact Or.inl hmv
  · right
    have r := ((protocols H j (by omega)).2 t).2 hmv
    have s := ((protocols H (j + 1) (by omega)).2 t).1 hmv
    simp only [ch] at r s
    rw [celN_excited _ _ _ r s]
    exact flip hmv

/-- 8a's `H_LATCH` is DERIVED from the pin-level latch, the routed enable and
data wires, and the timing obligations. -/
theorem latch_contract {n W m h : Nat} {P : Pipe} (H : PipeRun n W P) (T : Timing n W m h P)
    {j : Nat} (hj : j < n) :
    ∀ e, fallB (ch W P j).ack e = true →
      (∀ s, e + 1 - m ≤ s → s ≤ e + h → (ch W P j).dat s = (ch W P j).dat e) →
      ∀ s, e < s → (∀ u, e < u → u ≤ s → (ch W P j).ack u = false) →
        (ch W P (j + 1)).dat s = (ch W P j).dat e := by
  intro e hf hsh s hs hlow
  simp only [ch] at hf hsh hlow ⊢
  simp [fallB] at hf
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨r, hre, hr0, hr1, hopen⟩ := last_rise (P.x (j + 1)) (H.H_RESET (j + 1) (by omega)) e hf1
  have L := links H (j + 1) (by omega)
  have hw := L.openWidth hr0 hr1 hf2 hopen hre
  rw [show j + 1 + 1 = j + 2 by omega] at hw
  apply enc_congr
  intro b hb
  have hDb : ∀ s', e + 1 - m ≤ s' → s' ≤ e + h → P.Q j b s' = P.Q j b e :=
    fun s' h1 h2 => enc_inj W _ _ (hsh s' h1 h2) b hb
  have hcell : ∀ t, P.Q (j + 1) b (t + 1) =
      latchF (P.Q j b (t - P.dD j b)) (P.x (j + 1) (t - P.dG j b)) (P.Q (j + 1) b t) := by
    intro t; have := H.H_LATCH_CELL j hj b hb t; rwa [shift_eq, shift_eq] at this
  have := latch_bit (k := s - e - 1) hcell hopen
    (by have := T.lat_open j hj b hb; omega) (T.lat_setup j hj b hb) (T.lat_hold j hj b hb) hDb
    (fun u h1 h2 => hlow u h1 (by omega))
  rwa [show e + (s - e - 1) + 1 = s by omega] at this

theorem src_setupHold {n W m h : Nat} {P : Pipe} (H : PipeRun n W P) (T : Timing n W m h P) :
    SetupHold m h (ch W P 0) := by
  intro e hf s h1 h2
  simp only [ch] at hf ⊢
  simp [fallB] at hf
  have L := links H 0 (by omega)
  apply enc_congr
  intro b hb
  exact L.srcData (H.H_SRC_DATA b hb) T.m_pos T.src_setup T.src_hold hf.1 hf.2 s h1 h2

theorem sep_ok {n W m h : Nat} {P : Pipe} (H : PipeRun n W P) (T : Timing n W m h P)
    {j : Nat} (hj : j + 1 < n) : Sep m (ch W P j) (ch W P (j + 1)) := by
  intro e e' hf hf' hlt _
  simp only [ch] at hf hf'
  simp [fallB] at hf hf'
  have L := links H (j + 1) (by omega)
  exact L.sep (T.sep j hj) (by rw [hf.1, hf.2]; decide) (by rw [hf'.1, hf'.2]; decide) hlt

theorem hold_ok {n W m h : Nat} {P : Pipe} (H : PipeRun n W P) (T : Timing n W m h P)
    {j : Nat} (hj : j + 1 < n) : Hold h (ch W P j) (ch W P (j + 1)) := by
  intro e' s hf' h1 h2
  simp only [ch] at hf' ⊢
  simp [fallB] at hf'
  have L := links H (j + 1) (by omega)
  exact L.hold (T.hold j hj) hf'.1 hf'.2 s h1 h2

/-- Each routed stage is an 8a `MullerStage`. -/
theorem stage {n W m h : Nat} {P : Pipe} (H : PipeRun n W P) (T : Timing n W m h P)
    {j : Nat} (hj : j < n) : MullerStage m h (ch W P j) (ch W P (j + 1)) where
  H_NODE := fun _ => rfl
  H_RESET := H.H_RESET (j + 1) (by omega)
  H_CEL_SI := cel_si H hj
  H_LATCH := latch_contract H T hj

/-- The pipeline is a FIFO whenever the timing obligations hold. -/
theorem fifo_of_timing {n W m h : Nat} {P : Pipe} (H : PipeRun n W P) (T : Timing n W m h P)
    (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch W P j)) ∧
    (∀ t, cnt (fallB (ch W P n).ack) t ≤ cnt (fallB (ch W P 0).ack) t) ∧
    (∀ k e', TokAt (ch W P n) k e' →
      ∃ e, e < e' ∧ TokAt (ch W P 0) k e ∧ (ch W P n).dat e' = (ch W P 0).dat e) :=
  muller_pipeline (fun j hj => stage H T hj)
    (H.H_RESET 0 (by omega)) (H.H_RESET (n + 1) (Nat.le_refl _))
    (fun t _ => ((protocols H 0 (by omega)).2 t).1)
    (fun t _ => ((protocols H n (Nat.le_refl _)).2 t).2)
    (src_setupHold H T) (fun j hj => sep_ok H T hj) (fun j hj => hold_ok H T hj) hn

/-- **End to end.** If the verified checker accepts the routed netlist `R`
(`checkPipe R n W m h = true`), then every run of the `n`-stage pipeline built
from it (the gate hypotheses `PipeRun`, with per-arc delays inside the routed
intervals, `Realizes`) obeys the four-phase protocol on every link and is a
FIFO: the `k`-th token the sink takes is the `k`-th token the source gave,
and the sink never has more tokens than the source sent. -/
theorem end_to_end {R : Route} {n W m h : Nat} (hc : checkPipe R n W m h = true)
    {P : Pipe} (H : PipeRun n W P) (HR : Realizes R n W P) (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch W P j)) ∧
    (∀ t, cnt (fallB (ch W P n).ack) t ≤ cnt (fallB (ch W P 0).ack) t) ∧
    (∀ k e', TokAt (ch W P n) k e' →
      ∃ e, e < e' ∧ TokAt (ch W P 0) k e ∧ (ch W P n).dat e' = (ch W P 0).dat e) :=
  fifo_of_timing H (timing_of_check hc HR) hn

end Formal.Net.EndToEnd
