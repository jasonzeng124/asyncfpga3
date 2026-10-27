import Formal.Cells.Bundling

/-!
# Probe Bk: tighten.py rules K and L (`bd_link_dc`) against a derivation

Sources: cells/rtl/bd_link.v (`bd_link_dctl`, `bd_link_dc`, l.107-217),
cells/rtl/bd_latch.v (`bd_latch`), cells/verify/tighten.py rule L
(l.1969-2022) and rule K (l.2024-2118), helpers `latch_enables`
(l.1054-1076), `latch_data_pins` (l.1079-1089), `loop_wire` (l.1092-1100),
`req_guard` (l.1103-1106).

## Which latch each rule guards

Both rules guard the SAME latch: `<link>.lat`, the `bd_latch` of a
`bd_link_dc` (bit LUT6 `B8B8..` or LUT6_2 `FF33_CC00_B8B8_B8B8`), whose
enable is `lt`, the output of the controller's `ult` (LUT6 `0101..`,
`lt = ~b & ~a & ~gate`). The latch is transparent between tokens and CLOSES
when `b` rises (`ub`, `0000F320..`: set `req_in & ld & ~ack_out`).
`b` sets only when BOTH the request and `ld` (`uld`, `00000F08..`: set
`lt & s & ~a`) are up, so the close has two causes, and each rule times one:

* **K** (capture): the close caused by the REQUEST. The data, launched with
  the request at the sender, must be through its D arc and round the loop
  before `req -> b -> ult -> en pin` closes the latch.
* **L** (load / follow): the close caused by `ld` when the request was
  already up. After `lt` rises (reopen), `Q` must have followed `D` and
  gone round the loop before `lt -> ld -> b -> ult -> en pin` closes it.

In Bundling's capture condition H_SETUP
`max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo`, K is the DATA part
(`Td + dhi + fhi ≤ Toff + elo`) and L is the PULSE part
(`Ton + ehi + fhi ≤ Toff + elo`). Both rules use `loop_wire` for `fhi`, which
is the loop WIRE only: neither adds the feedback pin's own LUT arc (I2 for
O5/odd, I4 for O6), the term `Bundling.counter_rule_I` showed rule I lacks.

## What is proved here

* `ub_eq`, `ua_eq`, `uld_eq`, `ult_eq`: the four real controller INITs equal
  the header's set/reset equations (rst = 0, s = 1, I5 = 0).
* `RuleK`, `RuleL`: each rule's inequality exactly as the code computes it
  (one (en pin, d pin, driver) triple for K; the pairwise form of
  `max follow + guard ≤ tLd + tB + min close` for L).
* `setup_of_KL` / `dc_capture`: the corrected rules (feedback-pin arc added
  on the data/follow side), with named causal hypotheses, imply H_SETUP and
  hence (with Bundling's `capture`) that the bit holds the token.
* `coded_K_covered`, `coded_L_covered`: the coded rules imply the corrected
  ones whenever the guard is at least the feedback-pin arc.
* `counter_K`, `counter_L`: two complete transport traces of a WHOLE
  `bd_link_dc` stage (ub, ua, uld, ult with their real INITs, and an odd
  latch bit), each with a four-phase-legal environment, that pass BOTH
  rules K and L as coded at zero guard and still store a wrong token for
  ever (the loop circulates a pattern with a 0 in it).
-/

namespace Formal.Cells.RulesKL
open Formal.Cells Formal.Cells.Bundling

/-! ## 1. The controller's real INITs (cells/rtl/bd_link.v l.172-191) -/

/-- `ub`: pins `[req_in, ack_out, ld, b, rst, 0]` -> `b`. -/
def UB : Nat := 0x0000F3200000F320
/-- `ua`: pins `[req_in, b, ld, a, rst, 0]` -> `a`. -/
def UA : Nat := 0x0000FA800000FA80
/-- `uld`: pins `[lt, s, a, ld, rst, 0]` -> `ld` (LDN = 0: `s = 1`). -/
def ULD : Nat := 0x00000F0800000F08
/-- `ult`: pins `[b, a, gate, 0, 0, 0]` -> `lt` (BROAD = 1: `gate = ack_out`). -/
def ULT : Nat := 0x0101010101010101

theorem ub_eq : ∀ req ack ld b : Bool,
    lutB UB [req, ack, ld, b, false, false] = (req && ld && !ack || b && !(ack && !ld)) := by
  decide
theorem ua_eq : ∀ req b ld a : Bool,
    lutB UA [req, b, ld, a, false, false] = (req && b && ld || a && !(!req && !ld)) := by
  decide
theorem uld_eq : ∀ lt a ld : Bool,
    lutB ULD [lt, true, a, ld, false, false] = (lt && !a || ld && !a) := by
  decide
theorem ult_eq : ∀ b a g : Bool,
    lutB ULT [b, a, g, false, false, false] = (!b && !a && !g) := by
  decide

/-! ## 2. The rules exactly as tighten.py computes them

All quantities are the routed SDF numbers the code reads, in ps (here: ticks).
`guard` is `req_guard(None, t) = max(int(0.2 t), 200) + SLACK` (l.1103-1106);
it is left a free parameter, and the counter-traces use `guard = 0`.
Python's `margin = close - data - guard` is an integer; `margin < 0` is the
violation (l.2104, l.2015), so "passes" is `data + guard ≤ close`. -/

/-- Rule K's numbers for one (enable pin `p`, data pin `dp`, driver `drv`)
of one latch LUT `inst` (l.2084-2103). -/
structure KNums where
  /-- `timing.early(req_src).get(ctl)`: request source -> `b` output (l.2079). -/
  tReq : Nat
  /-- `d1 + d2` of `latch_enables`: `b` -> `ult` input wire + `ult` arc (l.1068-1075). -/
  dCtl : Nat
  /-- `d3` of `latch_enables`: `ult` output -> latch en pin wire. -/
  dFan : Nat
  /-- `min` arc out of the en pin `p` (l.2088-2089). -/
  enArcMin : Nat
  /-- `dict(edges[drv]).get(dp, 0)`: the data wire (l.2096). -/
  dWire : Nat
  /-- `max` arc out of `dp` (l.2097-2098). -/
  dArcMax : Nat
  /-- `loop_wire(edges, inst)`: max routed wire O5/O6 -> own input (l.2099). -/
  loopWire : Nat

/-- `t_close` (l.2088). -/
def KNums.close (n : KNums) : Nat := n.tReq + (n.dCtl + n.dFan) + n.enArcMin
/-- `t_data` (l.2096-2099): no feedback-pin arc. -/
def KNums.data (n : KNums) : Nat := n.dWire + n.dArcMax + n.loopWire

/-- Rule K passes this triple. The code takes the worst margin over all
triples, so passing rule K means `RuleK` for every triple. -/
def RuleK (n : KNums) (guard : Nat) : Prop := n.data + guard ≤ n.close

/-- Rule L's numbers for one latch enable pin `p` (l.2003-2012). -/
structure LPin where
  /-- `d1 + d2` of `latch_enables` (b -> ult -> lt). -/
  dCtl : Nat
  /-- `d3` of `latch_enables` (lt -> p wire). -/
  dFan : Nat
  /-- `min` arc out of `p` (l.2003-2004). -/
  enArcMin : Nat
  /-- `l_lt.get(p, 0)`: LATE lt -> p (l.2008-2009). -/
  lateWire : Nat
  /-- `max` arc out of `p` (l.2009-2010). -/
  enArcMax : Nat
  /-- `loop_wire(edges, inst(p))` (l.2011). -/
  loopWire : Nat

def LPin.close (p : LPin) : Nat := p.dCtl + p.dFan + p.enArcMin
/-- `t_follow`'s summand (l.2009-2011): no feedback-pin arc. -/
def LPin.follow (p : LPin) : Nat := p.lateWire + p.enArcMax + p.loopWire

/-- Rule L's numbers for one controller. -/
structure LNums where
  /-- `timing.early(lt, link).get(ld)` (l.1997). -/
  tLd : Nat
  /-- `timing.early(ld, link).get(ctl)` (l.1998). -/
  tB : Nat
  /-- the latch enable pins (`lat_pins`, l.2002). -/
  pins : List LPin

/-- Rule L passes: `max_p follow p + guard ≤ tLd + tB + min_p' close p'`
(l.2003-2015), in its equivalent pairwise form. -/
def RuleL (n : LNums) (guard : Nat) : Prop :=
  ∀ p ∈ n.pins, ∀ p' ∈ n.pins, p.follow + guard ≤ n.tLd + n.tB + p'.close

/-- The corrected rules: add the feedback pin's max arc `fbArc`
(SDF IOPATH I2->O5 / I4->O6 / I2->O) to the data / follow side. -/
def RuleK' (n : KNums) (fbArc guard : Nat) : Prop := n.data + fbArc + guard ≤ n.close
def RuleL' (n : LNums) (fbArc guard : Nat) : Prop :=
  ∀ p ∈ n.pins, ∀ p' ∈ n.pins, p.follow + fbArc + guard ≤ n.tLd + n.tB + p'.close

/-- The coded rules are sound whenever the guard covers the feedback arc
(nextpnr's flat 124 ps arc against the 200 ps guard floor), but only by
spending guardband meant for route scatter. -/
theorem coded_K_covered (n : KNums) (fbArc g : Nat) (h : RuleK n g) (hg : fbArc ≤ g) :
    RuleK' n fbArc (g - fbArc) := by
  unfold RuleK at h; unfold RuleK'; omega

theorem coded_L_covered (n : LNums) (fbArc g : Nat) (h : RuleL n g) (hg : fbArc ≤ g) :
    RuleL' n fbArc (g - fbArc) := by
  intro p hp p' hp'; have := h p hp p' hp'; omega

/-! ## 3. Soundness of the corrected rules

One latch bit, enable pin `p` (index `p` in rule L's list), rule K triple `n`
for the same bit. The latch windows (Bundling's `LatchRel`) are
`[dlo,dhi]` (D wire + D arc), `[elo,ehi]` (lt -> pin wire + I1 arc),
`[flo,fhi]` (loop wire + feedback-pin arc). Named hypotheses tie them to the
code's SDF numbers; each says "the SDF number bounds the physical delay"
and is testable by routed GLS at the slow/fast corners. -/

/-- **Derived setup for a `bd_link_dc` bit.** -/
theorem setup_of_KL (n : KNums) (L : LNums) (p : LPin) (hp : p ∈ L.pins)
    (fbArc g : Nat)
    (Ton Toff T0 Td dhi ehi elo fhi : Nat)
    -- H_LAUNCH: the data at the sender's driver is settled no later than the
    -- request leaves its source (rule K's "launched together", l.2034-2036;
    -- conservative by the sender's rule A lead).
    (H_LAUNCH : Td ≤ T0)
    -- H_LT_FALL_K: lt cannot fall before the request has reached b, b has
    -- risen, and that rise has crossed ult (ub's set needs req_in; lt's fall
    -- needs b, a or ack_out, and a/ack_out rise only after b). SDF-min path.
    (H_LT_FALL_K : T0 + n.tReq + n.dCtl ≤ Toff)
    -- H_LT_FALL_L: nor before lt's rise has set ld, ld has set b, and b has
    -- crossed ult (ub's set needs ld; uld's set needs lt). SDF-min path.
    (H_LT_FALL_L : Ton + L.tLd + L.tB + p.dCtl ≤ Toff)
    -- H_ELO / H_EHI: the en window at this bit is bounded by the SDF enable
    -- wire plus the I1 arc (min / max); rule K and L use the same pin.
    (H_ELO_K : n.dFan + n.enArcMin ≤ elo) (H_ELO_L : p.dFan + p.enArcMin ≤ elo)
    (H_EHI : ehi ≤ p.lateWire + p.enArcMax)
    -- H_DHI: D window ≤ data wire + max D arc.
    (H_DHI : dhi ≤ n.dWire + n.dArcMax)
    -- H_FHI: loop window ≤ loop wire + max feedback-pin arc.
    (H_FHI_K : fhi ≤ n.loopWire + fbArc) (H_FHI_L : fhi ≤ p.loopWire + fbArc)
    (hK : RuleK' n fbArc g) (hL : RuleL' L fbArc g) :
    max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo := by
  have h2 := hL p hp p hp
  unfold RuleK' KNums.data KNums.close at hK
  unfold LPin.follow LPin.close at h2
  omega

/-- **Capture for a `bd_link_dc` bit**: corrected K and L (any guard), the
causal hypotheses, and rule H's hold condition give the token in the bit
from settling until the enable can next reach it. -/
theorem dc_capture (d en q : Sig) (dlo dhi elo ehi flo fhi : Nat)
    (hLat : LatchRel d en q dlo dhi elo ehi flo fhi)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (n : KNums) (L : LNums) (p : LPin) (hp : p ∈ L.pins) (fbArc g : Nat)
    (Ton Toff Tnext T0 Td Tnew : Nat) (v : Bool)
    (h_on : ∀ t, Ton ≤ t → t < Toff → en t = true)
    (h_off : ∀ t, Toff ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_LAUNCH : Td ≤ T0)
    (H_LT_FALL_K : T0 + n.tReq + n.dCtl ≤ Toff)
    (H_LT_FALL_L : Ton + L.tLd + L.tB + p.dCtl ≤ Toff)
    (H_ELO_K : n.dFan + n.enArcMin ≤ elo) (H_ELO_L : p.dFan + p.enArcMin ≤ elo)
    (H_EHI : ehi ≤ p.lateWire + p.enArcMax)
    (H_DHI : dhi ≤ n.dWire + n.dArcMax)
    (H_FHI_K : fhi ≤ n.loopWire + fbArc) (H_FHI_L : fhi ≤ p.loopWire + fbArc)
    (hK : RuleK' n fbArc g) (hL : RuleL' L fbArc g)
    (H_HOLD : Toff + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v :=
  capture d en q dlo dhi elo ehi flo fhi hLat hdw hew hfw H_LOOP_POS
    Ton Toff Tnext Td Tnew v h_on h_off h_d
    (setup_of_KL n L p hp fbArc g Ton Toff T0 Td dhi ehi elo fhi H_LAUNCH H_LT_FALL_K
      H_LT_FALL_L H_ELO_K H_ELO_L H_EHI H_DHI H_FHI_K H_FHI_L hK hL) H_HOLD

/-! ## 4. Counter-trace K: the request closes the latch one I2 arc early

A whole `bd_link_dc` stage (W = 1, odd latch bit, BROAD = 1, LDN = 0,
DELAY = DACK = 0), every LUT a fixed transport delay, each pin's delay =
routed wire + that pin's arc:

| pin | delay | wire + arc |
|---|---|---|
| req_in -> ub | 1 | `tReq = 1` |
| ld, b, ack_out -> ub; req, b, ld, a -> ua; lt, a, ld -> uld | 1 | |
| b, a, ack_out -> ult | 1 | `dCtl = 1` |
| data -> latch I0 | 1 | wire 0 + D arc 1 |
| lt -> latch I1 | 1 | `dFan = 0` + en arc 1 |
| q -> latch I2 | 3 | loop wire 2 + **I2 arc 1** |

Environment: `ack_out = 0`, `rst = 0`; the sender raises `req_in` and the
data bit together at 8 (four-phase legal: `ack_in = a` is 0 then).
Rule K: `t_close = 1 + (1 + 0) + 1 = 3`, `t_data = 0 + 1 + 2 = 3`: margin 0.
Rule L: `follow = 0 + 1 + 2 = 3`, `close = 1 + 1 + 1 + 0 + 1 = 4`: margin 1.
H_SETUP: `8 + 1 + 3 ≤ 10 + 1` fails. The latch closes at 11 with the old 0
still in the I2 leg: `q` circulates 1,1,0 for ever. -/

def kReq : Sig := fun t => decide (8 ≤ t)
def kB : Sig := fun t => decide (9 ≤ t)
def kA : Sig := fun t => decide (10 ≤ t)
def kLd : Sig := fun t => decide (t < 11)
def kLt : Sig := fun t => decide (t < 10)
/-- the data bit: launched with the request -/
def kD : Sig := kReq

theorem kB_tr : Transport UB [(kReq, 1), (zero, 1), (kLd, 1), (kB, 1), (zero, 0), (zero, 0)] kB := by
  intro t
  show kB t = lutB UB [kReq (t - 1), false, kLd (t - 1), kB (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : kReq (t - 1) = true := by simp [kReq]; omega
    have h2 : kLd (t - 1) = false := by simp [kLd]; omega
    have h3 : kB (t - 1) = true := by simp [kB]; omega
    have h4 : kB t = true := by simp [kB]; omega
    rw [h1, h2, h3, h4]; decide

theorem kA_tr : Transport UA [(kReq, 1), (kB, 1), (kLd, 1), (kA, 1), (zero, 0), (zero, 0)] kA := by
  intro t
  show kA t = lutB UA [kReq (t - 1), kB (t - 1), kLd (t - 1), kA (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : kReq (t - 1) = true := by simp [kReq]; omega
    have h2 : kB (t - 1) = true := by simp [kB]; omega
    have h3 : kLd (t - 1) = false := by simp [kLd]; omega
    have h4 : kA (t - 1) = true := by simp [kA]; omega
    have h5 : kA t = true := by simp [kA]; omega
    rw [h1, h2, h3, h4, h5]; decide

theorem kLd_tr : Transport ULD [(kLt, 1), (one, 0), (kA, 1), (kLd, 1), (zero, 0), (zero, 0)] kLd := by
  intro t
  show kLd t = lutB ULD [kLt (t - 1), true, kA (t - 1), kLd (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : kLt (t - 1) = false := by simp [kLt]; omega
    have h2 : kA (t - 1) = true := by simp [kA]; omega
    have h3 : kLd (t - 1) = false := by simp [kLd]; omega
    have h4 : kLd t = false := by simp [kLd]; omega
    rw [h1, h2, h3, h4]; decide

theorem kLt_tr : Transport ULT [(kB, 1), (kA, 1), (zero, 1), (zero, 0), (zero, 0), (zero, 0)] kLt := by
  intro t
  show kLt t = lutB ULT [kB (t - 1), kA (t - 1), false, false, false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : kB (t - 1) = true := by simp [kB]; omega
    have h2 : kA (t - 1) = true := by simp [kA]; omega
    have h4 : kLt t = false := by simp [kLt]; omega
    rw [h1, h2, h4]; decide

/-- The trace's enable and data are Bundling's `caEn` / `caD`, so its latch
output is `caQ` (proved transport there). -/
theorem kLt_eq : kLt = caEn := rfl
theorem kD_eq : kD = caD := rfl

/-- Rule K's numbers on the trace. -/
def kK : KNums := ⟨1, 1, 0, 1, 0, 1, 2⟩
/-- Rule L's numbers on the trace (one enable pin). -/
def kL : LNums := ⟨1, 1, [⟨1, 0, 1, 0, 1, 2⟩]⟩

/-- **Counter-trace K.** Every LUT of the stage is a transport gate with its
real INIT; rules K and L as coded pass at zero guard; the corrected rule K
(feedback arc 1) fails; H_SETUP fails; and the bit, which saw `D = 1` from 8
on and whose enable is low from 10 on, holds 0 at every `11 + 3k`. -/
theorem counter_K :
    Transport UB [(kReq, 1), (zero, 1), (kLd, 1), (kB, 1), (zero, 0), (zero, 0)] kB ∧
    Transport UA [(kReq, 1), (kB, 1), (kLd, 1), (kA, 1), (zero, 0), (zero, 0)] kA ∧
    Transport ULD [(kLt, 1), (one, 0), (kA, 1), (kLd, 1), (zero, 0), (zero, 0)] kLd ∧
    Transport ULT [(kB, 1), (kA, 1), (zero, 1), (zero, 0), (zero, 0), (zero, 0)] kLt ∧
    Transport ODD [(kD, 1), (kLt, 1), (caQ, 3), (zero, 0), (zero, 0), (zero, 0)] caQ ∧
    LatchRel kD kLt caQ 1 1 1 1 3 3 ∧
    RuleK kK 0 ∧ RuleL kL 0 ∧ ¬ RuleK' kK 1 0 ∧
    ¬ (max (0 + 1) (8 + 1) + 3 ≤ 10 + 1) ∧
    (∀ t, 8 ≤ t → kD t = true) ∧ (∀ t, 10 ≤ t → kLt t = false) ∧
    (∀ k, caQ (11 + 3 * k) = false) := by
  refine ⟨kB_tr, kA_tr, kLd_tr, kLt_tr, caQ_transport,
    odd_latch (transport_gate ODD [(caD, 1, 1, 1), (caEn, 1, 1, 1), (caQ, 3, 3, 3),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] caQ (by simp) caQ_transport),
    by unfold RuleK; decide, ?_, by unfold RuleK'; decide, by decide, ?_, ?_, ?_⟩
  · intro p hp p' hp'
    simp [kL] at hp hp'; subst hp; subst hp'; decide
  · intro t h; simp [kD, kReq]; omega
  · intro t h; simp [kLt]; omega
  · intro k
    have a1 : ¬ 11 + 3 * k ≤ 8 := by omega
    have a2 : ¬ 11 + 3 * k ≤ 10 := by omega
    have a3 : (11 + 3 * k - 8) % 3 = 0 := by omega
    simp [caQ, a1, a2, a3]

/-! ## 5. Counter-trace L: the reopen pulse is one I2 arc too short

Same stage, now reopening on a new token with the request already up.
Pin delays as in trace K except: req_in -> ub is 2 (`tReq = 2`) and the
loop is 4 = loop wire 3 + **I2 arc 1**.

Environment (four-phase legal): initially a token is held (`b = a = 1`,
`ld = lt = 0`, `req_in = 1`, `q = d = 0`). The receiver acknowledges
(`ack_out` high on [2, 4), after `req_out = b` rose, low after it fell at 3);
the sender withdraws `req_in` at 2 (after `ack_in = a` rose), changes the
data bit to 1 at 3 and raises `req_in` again at 5 (after `a` fell at 3).
Then lt rises at 5, ld at 6, b at 7 (request already up), lt falls at 8.
Rule L: `follow = 0 + 1 + 3 = 4`, `close = 1 + 1 + (1 + 0 + 1) = 4`: margin 0.
Rule K: `t_close = 2 + 1 + 1 = 4`, `t_data = 0 + 1 + 3 = 4`: margin 0.
H_SETUP pulse part: `5 + 1 + 4 ≤ 8 + 1` fails. The bit holds 1,1,1,0
for ever: the new token (1) is corrupted. -/

def lReq : Sig := fun t => decide (t < 2 ∨ 5 ≤ t)
def lAck : Sig := fun t => decide (2 ≤ t ∧ t < 4)
def lB : Sig := fun t => decide (t < 3 ∨ 7 ≤ t)
def lA : Sig := fun t => decide (t < 3 ∨ 8 ≤ t)
def lLt : Sig := fun t => decide (5 ≤ t ∧ t < 8)
def lLd : Sig := fun t => decide (6 ≤ t ∧ t < 9)
def lD : Sig := fun t => decide (3 ≤ t)
def lQ : Sig := fun t => if t ≤ 5 then false else decide ((t - 6) % 4 ≠ 3)

theorem lB_tr : Transport UB [(lReq, 2), (lAck, 1), (lLd, 1), (lB, 1), (zero, 0), (zero, 0)] lB := by
  intro t
  show lB t = lutB UB [lReq (t - 2), lAck (t - 1), lLd (t - 1), lB (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : lReq (t - 2) = true := by simp [lReq]; omega
    have h2 : lAck (t - 1) = false := by simp [lAck]; omega
    have h3 : lLd (t - 1) = false := by simp [lLd]; omega
    have h4 : lB (t - 1) = true := by simp [lB]; omega
    have h5 : lB t = true := by simp [lB]; omega
    rw [h1, h2, h3, h4, h5]; decide

theorem lA_tr : Transport UA [(lReq, 1), (lB, 1), (lLd, 1), (lA, 1), (zero, 0), (zero, 0)] lA := by
  intro t
  show lA t = lutB UA [lReq (t - 1), lB (t - 1), lLd (t - 1), lA (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : lReq (t - 1) = true := by simp [lReq]; omega
    have h2 : lB (t - 1) = true := by simp [lB]; omega
    have h3 : lLd (t - 1) = false := by simp [lLd]; omega
    have h4 : lA (t - 1) = true := by simp [lA]; omega
    have h5 : lA t = true := by simp [lA]; omega
    rw [h1, h2, h3, h4, h5]; decide

theorem lLd_tr : Transport ULD [(lLt, 1), (one, 0), (lA, 1), (lLd, 1), (zero, 0), (zero, 0)] lLd := by
  intro t
  show lLd t = lutB ULD [lLt (t - 1), true, lA (t - 1), lLd (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : lLt (t - 1) = false := by simp [lLt]; omega
    have h2 : lA (t - 1) = true := by simp [lA]; omega
    have h3 : lLd (t - 1) = false := by simp [lLd]; omega
    have h4 : lLd t = false := by simp [lLd]; omega
    rw [h1, h2, h3, h4]; decide

theorem lLt_tr : Transport ULT [(lB, 1), (lA, 1), (lAck, 1), (zero, 0), (zero, 0), (zero, 0)] lLt := by
  intro t
  show lLt t = lutB ULT [lB (t - 1), lA (t - 1), lAck (t - 1), false, false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : lB (t - 1) = true := by simp [lB]; omega
    have h2 : lA (t - 1) = true := by simp [lA]; omega
    have h3 : lAck (t - 1) = false := by simp [lAck]; omega
    have h4 : lLt t = false := by simp [lLt]; omega
    rw [h1, h2, h3, h4]; decide

theorem lQ_tr : Transport ODD [(lD, 1), (lLt, 1), (lQ, 4), (zero, 0), (zero, 0), (zero, 0)] lQ := by
  intro t
  show lQ t = lutB ODD [lD (t - 1), lLt (t - 1), lQ (t - 4), false, false, false]
  rw [odd_bin]
  by_cases ht : t < 14
  · revert t; decide
  · have hen : lLt (t - 1) = false := by simp [lLt]; omega
    rw [hen]
    have a1 : ¬ t ≤ 5 := by omega
    have a3 : ¬ t - 4 ≤ 5 := by omega
    simp only [lQ, Bool.false_eq_true, a1, a3, ↓reduceIte]
    have : t - 6 = (t - 4 - 6) + 4 := by omega
    rw [this, Nat.add_mod_right]

def lK : KNums := ⟨2, 1, 0, 1, 0, 1, 3⟩
def lL : LNums := ⟨1, 1, [⟨1, 0, 1, 0, 1, 3⟩]⟩

/-- **Counter-trace L.** Every LUT of the stage is a transport gate with its
real INIT; rules K and L as coded pass at zero guard (both margin 0); the
corrected rule L (feedback arc 1) fails; the pulse part of H_SETUP fails;
and the bit, whose D is 1 from 3 on and whose enable is low from 8 on,
holds 0 at every `9 + 4k`. -/
theorem counter_L :
    Transport UB [(lReq, 2), (lAck, 1), (lLd, 1), (lB, 1), (zero, 0), (zero, 0)] lB ∧
    Transport UA [(lReq, 1), (lB, 1), (lLd, 1), (lA, 1), (zero, 0), (zero, 0)] lA ∧
    Transport ULD [(lLt, 1), (one, 0), (lA, 1), (lLd, 1), (zero, 0), (zero, 0)] lLd ∧
    Transport ULT [(lB, 1), (lA, 1), (lAck, 1), (zero, 0), (zero, 0), (zero, 0)] lLt ∧
    Transport ODD [(lD, 1), (lLt, 1), (lQ, 4), (zero, 0), (zero, 0), (zero, 0)] lQ ∧
    LatchRel lD lLt lQ 1 1 1 1 4 4 ∧
    RuleK lK 0 ∧ RuleL lL 0 ∧ ¬ RuleL' lL 1 0 ∧
    ¬ (max (5 + 1) (3 + 1) + 4 ≤ 8 + 1) ∧
    (∀ t, 5 ≤ t → t < 8 → lLt t = true) ∧ (∀ t, 8 ≤ t → lLt t = false) ∧
    (∀ t, 3 ≤ t → lD t = true) ∧
    (∀ k, lQ (9 + 4 * k) = false) := by
  refine ⟨lB_tr, lA_tr, lLd_tr, lLt_tr, lQ_tr,
    odd_latch (transport_gate ODD [(lD, 1, 1, 1), (lLt, 1, 1, 1), (lQ, 4, 4, 4),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] lQ (by simp) lQ_tr),
    by unfold RuleK; decide, ?_, ?_, by decide, ?_, ?_, ?_, ?_⟩
  · intro p hp p' hp'
    simp [lL] at hp hp'; subst hp; subst hp'; decide
  · intro h
    have := h _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)
    revert this; decide
  · intro t h1 h2; simp [lLt]; omega
  · intro t h; simp [lLt]; omega
  · intro t h; simp [lD]; omega
  · intro k
    have a1 : ¬ 9 + 4 * k ≤ 5 := by omega
    have a3 : (9 + 4 * k - 6) % 4 = 3 := by omega
    simp [lQ, a1, a3]

end Formal.Cells.RulesKL
