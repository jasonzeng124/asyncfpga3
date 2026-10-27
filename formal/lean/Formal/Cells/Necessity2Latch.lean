import Formal.Cells.ConstraintsLatchRst

/-!
# Necessity2Latch: `bd_latch_rst.setup_pulse` (H_PW) is tight to 1 tick

Probe Bsx2 (shard B). Row `bd_latch_rst.setup_pulse` was "sufficient; no
separate witness for the _rst INIT". The theorem is
`ConstraintsLatchRst.capture_rst_from_request` (window channels, Kleene
closure of the REAL INITs `64'h00B8..` / `64'hFFB8..`, pins d, en, q
(feedback), rst), whose enable-pulse hypothesis is

    H_PW : ehi + fhi ≤ W + elo.

## Result

`PwClaim init rv slack` is `capture_rst_from_request` with H_PW weakened by
`slack` (every other hypothesis verbatim). `pw0` (both INITs) is the
existing theorem; `pw1_false_rst0`, `pw1_false_rst1`: ONE tick of slack is
unsound, for both reset polarities. Counter-run (transport, every pin a
fixed delay inside its point window = one corner): d arc 1, en arc 1, loop
(wire + I2 arc) 3, rst arc 1 with rst tied low (released at 0); en high on
[10, 12) (W = 2), d = 1 from 0 on (data early, H_SETUP_DATA holds with
margin 9), H_HOLD and H_RST_DONE hold. `ehi + fhi = 4 = W + elo + 1`. The
latch is transparent at its pin on [11, 13), but its own 1 is still on the
3-tick loop when en closes, so q falls back to 0 at 13 and a runt train of
period 3 circulates forever (q = 1 iff t ≥ 11 ∧ t mod 3 ≠ 1); the
conclusion needs q = 1 on [11, 1001).

So the Lean form is **necessary at the boundary** (one tick, one parameter
point). The JSON form's extra +1 (`ehi + fhi + 1 ≤ W + elo`) is the Kleene
X window at equality (CElemStrict), not this binary run.
-/

namespace Formal.Cells.Necessity2Latch
open Formal.Cells Formal.Cells.Bundling Formal.Cells.ConstraintsLatchRst

/-- `capture_rst_from_request` with H_PW weakened by `slack`. -/
def PwClaim (init : Nat) (rv : Bool) (slack : Nat) : Prop :=
  IsRstLatch init rv →
  ∀ (d en q rst : Sig) (dlo dhi elo ehi flo fhi rlo rhi : Nat),
    RstGate init d en q rst dlo dhi elo ehi flo fhi rlo rhi →
    dlo ≤ dhi → elo ≤ ehi → flo ≤ fhi → rlo ≤ rhi → 1 ≤ flo →
    ∀ (Ton Toff Tnext Td Tnew Rl Tr Rlo W : Nat) (v : Bool),
    (∀ t, Ton ≤ t → t < Toff → en t = true) →
    (∀ t, Toff ≤ t → t < Tnext → en t = false) →
    (∀ t, Td ≤ t → t < Tnew → d t = v) →
    (∀ t, Rl ≤ t → rst t = false) →
    Rl + rhi ≤ max (Ton + ehi) (Td + dhi) →
    Tr + Rlo ≤ Ton → Ton + W ≤ Toff →
    Td + dhi + fhi ≤ Tr + Rlo + W + elo →
    ehi + fhi ≤ W + elo + slack →
    Toff + ehi ≤ Tnew + dlo →
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v

theorem pw0 (init : Nat) (rv : Bool) : PwClaim init rv 0 := by
  intro hI d en q rst dlo dhi elo ehi flo fhi rlo rhi hg h1 h2 h3 h4 h5
    Ton Toff Tnext Td Tnew Rl Tr Rlo W v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  exact capture_rst_from_request hI d en q rst dlo dhi elo ehi flo fhi rlo rhi hg h1 h2 h3 h4 h5
    Ton Toff Tnext Td Tnew Rl Tr Rlo W v a1 a2 a3 a4 a5 a6 a7 a8 (by omega) a10

/-! ## The counter-run -/

def pD : Sig := fun _ => true
def pEn : Sig := fun t => decide (10 ≤ t ∧ t < 12)
def pQ : Sig := fun t => decide (11 ≤ t ∧ t % 3 ≠ 1)

theorem rst0_bin : ∀ d en q : Bool, lutB RST0 [d, en, q, false, false, false] = (if en then d else q) := by
  decide
theorem rst1_bin : ∀ d en q : Bool, lutB RST1 [d, en, q, false, false, false] = (if en then d else q) := by
  decide

theorem pQ_eq (t : Nat) : pQ t = (if pEn (t - 1) then pD (t - 1) else pQ (t - 3)) := by
  by_cases h : 10 ≤ t - 1 ∧ t - 1 < 12
  · have : pEn (t - 1) = true := by simp [pEn]; omega
    rw [this]; simp [pQ, pD]; omega
  · have : pEn (t - 1) = false := by simp [pEn]; omega
    rw [this, Bool.eq_iff_iff]; simp [pQ]; omega

theorem pGate (init : Nat)
    (hb : ∀ d en q : Bool, lutB init [d, en, q, false, false, false] = (if en then d else q)) :
    RstGate init pD pEn pQ zero 1 1 1 1 3 3 1 1 :=
  transport_gate init [(pD, 1, 1, 1), (pEn, 1, 1, 1), (pQ, 3, 3, 3), (zero, 1, 1, 1),
      (zero, 0, 0, 0), (zero, 0, 0, 0)] pQ (by simp)
    (fun t => by
      show pQ t = lutB init [pD (t - 1), pEn (t - 1), pQ (t - 3), zero (t - 1), zero (t - 0),
        zero (t - 0)]
      rw [show zero (t - 1) = false from rfl, show zero (t - 0) = false from rfl, hb]
      exact pQ_eq t)

/-- The numbers: H_PW fails by exactly one tick (1 + 3 = 2 + 1 + 1); the
other hypotheses hold; q is 0 at 13, inside [11, 1001). -/
theorem p_viol : 1 + 3 = 2 + 1 + 1 ∧ 0 + 1 + 3 ≤ 10 + 0 + 2 + 1 ∧ 12 + 1 ≤ 1000 + 1 ∧
    0 + 1 ≤ max (10 + 1) (0 + 1) ∧ pQ 13 = false := by decide

theorem pw1_false_of (init : Nat) (rv : Bool) (hI : IsRstLatch init rv)
    (hb : ∀ d en q : Bool, lutB init [d, en, q, false, false, false] = (if en then d else q)) :
    ¬ PwClaim init rv 1 := by
  intro h
  have := h hI pD pEn pQ zero 1 1 1 1 3 3 1 1 (pGate init hb)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    10 12 1000 0 1000 0 10 0 2 true
    (fun t h1 h2 => by simp [pEn]; omega) (fun t h1 h2 => by simp [pEn]; omega)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    13 (by decide) (by omega)
  rw [p_viol.2.2.2.2] at this; exact absurd this (by decide)

theorem pw1_false_rst0 : ¬ PwClaim RST0 false 1 := pw1_false_of RST0 false rst0_isRst rst0_bin
theorem pw1_false_rst1 : ¬ PwClaim RST1 true 1 := pw1_false_of RST1 true rst1_isRst rst1_bin

end Formal.Cells.Necessity2Latch
