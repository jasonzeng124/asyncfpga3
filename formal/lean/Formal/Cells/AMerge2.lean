import Formal.Cells.AMergeSys
import Formal.Cells.AMergeGates

/-!
# Probe Cm, part 2: `bdc_amerge2_0` (the 2-input control_merge of gcd_hw)

`bdc/emit.py` `emit_amerge(0, 2)`, 7 instances in gcd_hw (`ucontrol_merge*`
with two predecessors), `W = 0` (control only: the result channel carries no
data, the `index` output is the only datum):

    bd_arbiter uarb1 (r1 = in0_req, A1 = in0_ack, r2 = in1_req, A2 = in1_ack,
                      R0 = r0, A0 = z_ack, g1, g2)
    index = g2 | in1_ack                      (inferred LUT2 E, H_YOSYS_MAP)
    uor   = LUT1 2 (r0) -> either
    udly  = bd_delay_gated (a = either, gate = r0) -> z_req

## Model (speed independent, `AMergeSys.Sys`)

Variables (bit = index):
`0 r1` (client 0, four-phase on `A1`), `1 r2` (client 1, on `A2`),
`2 ~q` (`ustate` O6, stored inverted so that state 0 is the reset state), `3 R0` (`ustate` O5), `4 g1` (`ugrant` O5),
`5 g2` (`ugrant` O6), `6 A1` (`ua1`), `7 A2` (`ua2`), `8 idx` (the inferred
LUT2), `9 either` (`uor`), `10 z_req` (`bd_delay_gated` as ONE buffer),
`11 z_ack` (the server: the `bd_fork` + consumers of the control_merge's two
outputs, abstracted as a four-phase server copying `z_req`),
`12 g2@idx`, `13 A2@idx` (the two data-path fork branches into the index LUT,
unbounded delay; isochronic when the flag says so).
Ghosts: `14-15 o` (owner of the server transaction: 0 none, 1 client 0,
2 client 1), `16 sv0`, `17 sv1` (the server has acknowledged that client's
token).

Isochronic (named, cited, not re-proved): every fork INSIDE `bd_arbiter`
(`r1`, `r2` to `ustate`/`ugrant`, `q` to `ugrant`, `A0` to
`ustate`/`ua1`/`ua2`, `g1`/`g2` to `ua1`/`ua2`) and the `A1`/`A2` forks to the
clients. These are the arbiter's own relative-timing facts, proved (or shown
needed) in `ArbA0Fork` (H_A0_FORK), `ArbHeldTimed` (RT1, RT2),
`ArbHandover` (zero-wire-delay protocol). `q`'s feedback is instantaneous
(H_FB_FAST). `q` is Boolean: no metastability (H_ARB_RESOLVED below).

## Spec (ghost automaton, as `MergeMuxSI`'s merge, with the owner chosen by
the arbiter state instead of by exclusive requests)

`z_req` rises only for the client the arbiter state names (`q` and that
client's request up), which is requesting, unacknowledged and not yet served; `z_req` falls only
after `z_ack` and after the owner's request fell; `z_ack` rises once per
token; a client's acknowledge rises only after the server acknowledged THAT
client's token, and falls only after the server transaction returned to zero.
So every output transaction carries exactly one input token. Data (`good`):
the two grants are never both high, and while `z_req` or `z_ack` is high
(the library's broad window: data held until the acknowledge falls) `index`
names the owner: `idx = 1` iff the owner is client 1.
-/

namespace Formal.Cells.AMerge2
open Formal.Cells.AMergeSys Formal.Cells.AMergeGates

/-- Which hypotheses are on (negative controls switch one off). -/
structure Hyp where
  /-- **H_RT1** (grant exclusion during handover): a grant rises only while
  the other grant is low. In this SI model it is a scheduling filter; it is
  exactly the conclusion of `ArbHeldTimed.rt1_exclusion` (and its mirror),
  which derives it from the arc inequality RT1 (r1-fall -> g1-fall beats
  r1-fall -> R0 -> server -> A0 -> q -> g2-rise) for every server slower than
  `smin` (H_SERVER_MIN). Test: GLS/board assertion `!(g1 & g2)` per arbiter
  (`hw/arb_prot` counts it: 0/96). -/
  rt1 : Bool
  /-- **H_RT2** (acknowledge return to zero): the server raises `A0` again only
  after the previous transaction's acknowledge C-element (`ua1`/`ua2`, excited
  to fall) has fallen. Exactly `ArbHeldTimed.A1_low_after` / RT2a
  (`rt2_exclusion_arcs`, fields `pulse`, `g1`). Test: GLS, min of
  A0-fall -> ... -> A0-rise against max A0-fall -> A1-fall. -/
  rt2 : Bool
  /-- **H_BUNDLED_IDX** (the wrapper's own bundling obligation, the one its
  header names): `z_req` rises only after the index cone has settled: the
  index LUT, its two input branches, and its drivers `g2`, `A2` are all
  quiescent. Physically: `A0`-fall -> `ua2` -> `A2`-fall -> `index` (the
  previous owner-1 token's tail) and `q` -> `g2` -> `index` both beat
  `q` -> `R0` -> `uor` -> `bd_delay_gated` -> `z_req`. The matched delay is
  what pays for it (rule A / `GcdCells.rises`). Test: GLS assertion
  "index stable at z_req rise", per instance. -/
  bidx : Bool
  /-- `g2` fork into the index LUT isochronic. -/
  isoG : Bool
  /-- `A2` fork into the index LUT isochronic. -/
  isoA : Bool

def rdG (H : Hyp) (s : Nat) : Bool := if H.isoG then tb s 5 else tb s 12
def rdA (H : Hyp) (s : Nat) : Bool := if H.isoA then tb s 7 else tb s 13

/-- `q`, stored inverted in bit 2 so that the all-zero state is the reset
state (`bd_arbiter` resets `q` to 1: `q = rst + ...`). -/
def qv (s : Nat) : Bool := !tb s 2

/-- The next-value vector (`Sys.nxv`): entry `k` is what variable `k` becomes
if it fires now. Gates are evaluated through `G` (the theorems use `gI`, the
real INITs). -/
def nxv (G : Gates) (H : Hyp) (s : Nat) : Nat := Sys.bits [
    (if tb s 0 == tb s 6 then !tb s 0 else tb s 0),  -- 0 client 0
    (if tb s 1 == tb s 7 then !tb s 1 else tb s 1),  -- 1 client 1
    !G.stA (tb s 0) (tb s 1) (qv s) (tb s 11),  -- 2 ustate O6 (inverted)
    G.r0A (tb s 0) (tb s 1) (qv s) (tb s 11),  -- 3 ustate O5
    G.gr1 (tb s 0) (tb s 1) (qv s),  -- 4 ugrant O5
    G.gr2 (tb s 0) (tb s 1) (qv s),  -- 5 ugrant O6
    G.c2 (tb s 4) (tb s 11) (tb s 6),  -- 6 ua1
    G.c2 (tb s 5) (tb s 11) (tb s 7),  -- 7 ua2
    G.idx2 (rdG H s) (rdA H s),  -- 8 index LUT2
    G.buf1 (tb s 3),  -- 9 uor
    tb s 9,  -- 10 bd_delay_gated
    tb s 10,  -- 11 server
    (if H.isoG then tb s 12 else tb s 5),  -- 12 g2@idx
    (if H.isoA then tb s 13 else tb s 7)  -- 13 A2@idx
  ]

/-- Per-variable view. -/
def nx (G : Gates) (H : Hyp) (s v : Nat) : Bool := (nxv G H s).testBit v

def exv (G : Gates) (H : Hyp) (s v : Nat) : Bool := nx G H s v != tb s v

/-- The filters; `e` is the excitation mask of `s` (`e.testBit k`: variable
`k` is excited). -/
def allow (H : Hyp) (e s v : Nat) : Bool :=
  (!H.rt1 || (if v = 4 ∧ tb s 4 = false then !tb s 5
              else if v = 5 ∧ tb s 5 = false then !tb s 4 else true)) &&
  (!H.rt2 || (if v = 11 ∧ tb s 11 = false then !e.testBit 6 && !e.testBit 7 else true)) &&
  (!H.bidx || (if v = 10 ∧ tb s 10 = false then
      !e.testBit 8 && !e.testBit 12 && !e.testBit 13 && !e.testBit 5 && !e.testBit 7 else true))

/-- The client the arbiter's state names: `q` with its request up (the one
`R0 = r1.q + r2.~q` is high for), 0 if none. -/
def winner (s : Nat) : Nat :=
  if qv s && tb s 0 then 1 else if !qv s && tb s 1 then 2 else 0

def fire (s v : Nat) : Nat :=
  let t := s ^^^ 2 ^ v
  if v = 10 then (if tb s 10 then t else setO 14 t (winner s))
  else if v = 11 then
    (if tb s 11 then setO 14 t 0
     else if getO 14 s = 1 then setB t 16 true
     else if getO 14 s = 2 then setB t 17 true else t)
  else if v = 6 then (if tb s 6 then setB t 16 false else t)
  else if v = 7 then (if tb s 7 then setB t 17 false else t)
  else t

/-- Client `c` (1 or 2) requests, is unacknowledged and unserved. -/
def cand (s c : Nat) : Bool :=
  if c = 1 then tb s 0 && !tb s 6 && !tb s 16 else tb s 1 && !tb s 7 && !tb s 17

def spec (s v : Nat) : Bool :=
  let o := getO 14 s
  if v = 10 then
    (if tb s 10 = false then
       o == 0 && !tb s 11 && winner s != 0 && cand s (winner s)
     else o != 0 && tb s 11 && !(if o == 1 then tb s 0 else tb s 1))
  else if v = 11 then
    (if tb s 11 = false then tb s 10 && o != 0 && !tb s (if o == 1 then 16 else 17)
     else !tb s 10)
  else if v = 6 then
    (if tb s 6 = false then tb s 16 && tb s 0 else tb s 16 && !tb s 0 && o != 1)
  else if v = 7 then
    (if tb s 7 = false then tb s 17 && tb s 1 else tb s 17 && !tb s 1 && o != 2)
  else true

def good (s : Nat) : Bool :=
  let o := getO 14 s
  !(tb s 4 && tb s 5) &&
  (!(tb s 10 || tb s 11) || (o != 0 && (tb s 8 == (o == 2))))

/-- The system. `waiting`: some client waits (request and acknowledge
differ) while every other client is at rest (both low), so the only thing
that can move is the circuit: then some gate/wire/server step must be allowed
(a token is never stranded). -/
def sys (G : Gates) (H : Hyp) : Sys where
  V := 14
  nxv := nxv G H
  allow := allow H
  fire := fire
  spec := spec
  good := good
  hzM := 3835  -- every variable except 2, 8, 12, 13
  live := fun v => decide (2 ≤ v)
  waiting := fun s =>
    (tb s 0 != tb s 6 || tb s 1 != tb s 7) &&
    (tb s 0 != tb s 6 || !tb s 0) && (tb s 1 != tb s 7 || !tb s 1)

/-- The proved configuration: H_RT1, H_RT2, H_BUNDLED_IDX on; the `g2` fork
into the index LUT delayed independently; the `A2` fork into the index LUT
isochronic (**H_IDX_ACK_FORK**, shown needed in `AMerge2Proof`). -/
def hOK : Hyp := ⟨true, true, true, false, true⟩

end Formal.Cells.AMerge2
