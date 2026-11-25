import Formal.Cells.AMergeSys
import Formal.Cells.AMergeGates

/-!
# Probe Cm, part 3: `bdc_amerge3_0` (the 3-input control_merge, two arbiters)

`bdc/emit.py` `emit_amerge(0, 3)`, 1 instance in gcd_hw
(`ucontrol_merge12`, DELAY 24). A CASCADE: arbiter 1 merges inputs 0 and 1,
arbiter 2 merges arbiter 1's output against input 2:

    bd_arbiter uarb1 (r1 = in0_req, A1 = in0_ack, r2 = in1_req, A2 = in1_ack,
                      R0 = acc1_req, A0 = acc1_ack, g1 = g1[1], g2 = g2[1])
    bd_arbiter uarb2 (r1 = acc1_req, A1 = acc1_ack, r2 = in2_req, A2 = in2_ack,
                      R0 = r0, A0 = z_ack, g1 = g1[2], g2 = g2[2])
    index[1] = g2[2] | in2_ack                          (LUT2 E)
    index[0] = (g2[1] | in1_ack) & ~(g2[2] | in2_ack)   (LUT4 000E)
    uor, udly (bd_delay_gated) on r0 -> z_req

So arbiter 1 is a CLIENT of arbiter 2: its `R0` is arbiter 2's `r1`, and
arbiter 2's acknowledge C-element `ua1` (`acc1_ack`) is arbiter 1's server.

## Model (speed independent, `AMergeSys.Sys`)

Variables: `0 c0`, `1 c1`, `2 c2` (clients, four-phase on their acks);
arbiter 1: `3 ~q1` (inverted: reset is `q = 1`), `4 R01` (= `acc1_req`),
`5 g11`, `6 g21`, `7 A11` (= `in0_ack`), `8 A21` (= `in1_ack`);
arbiter 2: `9 ~q2`, `10 R02` (= `r0`), `11 g12`, `12 g22`, `13 A12`
(= `acc1_ack`), `14 A22` (= `in2_ack`);
`15 idx0` (LUT4), `16 idx1` (LUT2), `17` unused (never excited),
`18 z_req` (`uor` and `bd_delay_gated` lumped as ONE delay element from
`R0`: both are buffers, H_DELAY_BUF), `19 z_ack` (server);
index-fork branches (unbounded delay unless the flag makes them isochronic):
`20 g21@idx0`, `21 g22@idx0`, `22 g22@idx1`.
Ghosts: `23-24 o` (owner: 0 none, 1/2/3 = client 0/1/2), `25-27 sv0..sv2`.

Isochronic and cited (as in `AMerge2`): every fork inside each `bd_arbiter`,
the cascade wires `acc1_req -> uarb2.{ustate, ugrant}` (arbiter 2's `r1`
fork) and `acc1_ack -> uarb1.{ustate, ua1, ua2}` (arbiter 1's `A0` fork,
H_A0_FORK) and `uarb2.ua1`'s own feedback (H_FB_FAST), the acknowledge forks
to the clients, and the acknowledge forks `in1_ack`, `in2_ack` into the index
LUTs (H_IDX_ACK_FORK, shown needed in `AMerge2Proof`).
-/

namespace Formal.Cells.AMerge3
open Formal.Cells.AMergeSys Formal.Cells.AMergeGates

structure Hyp where
  /-- **H_RT1** for BOTH arbiters: a grant rises only while its sibling grant
  is low (ArbHeldTimed.rt1_exclusion, per arbiter). -/
  rt1 : Bool
  /-- **H_RT2** for arbiter 2 (server = the environment's `z_ack`): `z_ack`
  rises only when neither `uarb2.ua1` nor `uarb2.ua2` is excited to fall. -/
  rt2a : Bool
  /-- **H_RT2_CASCADE** for arbiter 1, whose server is arbiter 2's `ua1`:
  `acc1_ack` (`uarb2.ua1`) rises only when neither `uarb1.ua1` nor
  `uarb1.ua2` is excited to fall. A relative-timing condition INSIDE the
  cell: the previous arbiter-1 owner's acknowledge must have fallen before
  arbiter 2 acknowledges arbiter 1 again (slack: a whole server round trip
  through `z_req`, the consumer and `z_ack`). Test: GLS, per instance. -/
  rt2b : Bool
  /-- **H_BUNDLED_IDX** (both index bits): `z_req` rises only with the two
  index LUTs, their input branches, and `g21`, `g22`, `A21`, `A22`
  quiescent. -/
  bidx : Bool
  /-- The `g2` forks into the index LUTs isochronic. -/
  isoG : Bool

def q1 (s : Nat) : Bool := !tb s 3
def q2 (s : Nat) : Bool := !tb s 9

def rd (H : Hyp) (s b drv : Nat) : Bool := if H.isoG then tb s drv else tb s b

/-- The next-value vector (`Sys.nxv`): entry `k` is what variable `k` becomes
if it fires now. Gates are evaluated through `G` (the theorems use `gI`, the
real INITs). -/
def nxv (G : Gates) (H : Hyp) (s : Nat) : Nat := Sys.bits [
    (if tb s 0 == tb s 7 then !tb s 0 else tb s 0),  -- 0 client 0
    (if tb s 1 == tb s 8 then !tb s 1 else tb s 1),  -- 1 client 1
    (if tb s 2 == tb s 14 then !tb s 2 else tb s 2),  -- 2 client 2
    !G.stA (tb s 0) (tb s 1) (q1 s) (tb s 13),  -- 3 uarb1.ustate O6
    G.r0A (tb s 0) (tb s 1) (q1 s) (tb s 13),  -- 4 uarb1.ustate O5
    G.gr1 (tb s 0) (tb s 1) (q1 s),  -- 5 uarb1.ugrant O5
    G.gr2 (tb s 0) (tb s 1) (q1 s),  -- 6 uarb1.ugrant O6
    G.c2 (tb s 5) (tb s 13) (tb s 7),  -- 7 uarb1.ua1
    G.c2 (tb s 6) (tb s 13) (tb s 8),  -- 8 uarb1.ua2
    !G.stA (tb s 4) (tb s 2) (q2 s) (tb s 19),  -- 9 uarb2.ustate O6
    G.r0A (tb s 4) (tb s 2) (q2 s) (tb s 19),  -- 10 uarb2.ustate O5
    G.gr1 (tb s 4) (tb s 2) (q2 s),  -- 11 uarb2.ugrant O5
    G.gr2 (tb s 4) (tb s 2) (q2 s),  -- 12 uarb2.ugrant O6
    G.c2 (tb s 11) (tb s 19) (tb s 13),  -- 13 uarb2.ua1
    G.c2 (tb s 12) (tb s 19) (tb s 14),  -- 14 uarb2.ua2
    G.idx3l (tb s 8) (rd H s 20 6) (rd H s 21 12) (tb s 14),  -- 15 index[0]
    G.idx2 (rd H s 22 12) (tb s 14),  -- 16 index[1]
    tb s 17,  -- 17 (unused)
    G.buf1 (tb s 10),  -- 18 uor + bd_delay_gated
    tb s 18,  -- 19 server
    (if H.isoG then tb s 20 else tb s 6),  -- 20 g21@idx0
    (if H.isoG then tb s 21 else tb s 12),  -- 21 g22@idx0
    (if H.isoG then tb s 22 else tb s 12)  -- 22 g22@idx1
  ]

/-- Per-variable view. -/
def nx (G : Gates) (H : Hyp) (s v : Nat) : Bool := (nxv G H s).testBit v

def exv (G : Gates) (H : Hyp) (s v : Nat) : Bool := nx G H s v != tb s v

/-- The filters; `e` is the excitation mask of `s` (`e.testBit k`: variable
`k` is excited). -/
def allow (H : Hyp) (e s v : Nat) : Bool :=
  (!H.rt1 || (if v = 5 ∧ tb s 5 = false then !tb s 6
              else if v = 6 ∧ tb s 6 = false then !tb s 5
              else if v = 11 ∧ tb s 11 = false then !tb s 12
              else if v = 12 ∧ tb s 12 = false then !tb s 11 else true)) &&
  (!H.rt2a || (if v = 19 ∧ tb s 19 = false then !e.testBit 13 && !e.testBit 14 else true)) &&
  (!H.rt2b || (if v = 13 ∧ tb s 13 = false then !e.testBit 7 && !e.testBit 8 else true)) &&
  (!H.bidx || (if v = 18 ∧ tb s 18 = false then
      !e.testBit 15 && !e.testBit 16 && !e.testBit 20 && !e.testBit 21 && !e.testBit 22 &&
      !e.testBit 6 && !e.testBit 12 && !e.testBit 8 && !e.testBit 14 else true))

/-- The client the two arbiter states name (1/2/3 = client 0/1/2, 0 none):
arbiter 2 points at arbiter 1 (`q2`, `acc1_req` up) and arbiter 1 at a
requesting client, or arbiter 2 points at client 2 with its request up. -/
def winner (s : Nat) : Nat :=
  if q2 s && tb s 4 then (if q1 s && tb s 0 then 1 else if !q1 s && tb s 1 then 2 else 0)
  else if !q2 s && tb s 2 then 3 else 0

def fire (s v : Nat) : Nat :=
  let t := s ^^^ 2 ^ v
  if v = 18 then (if tb s 18 then t else setO 23 t (winner s))
  else if v = 19 then
    (if tb s 19 then setO 23 t 0
     else if getO 23 s = 1 then setB t 25 true
     else if getO 23 s = 2 then setB t 26 true
     else if getO 23 s = 3 then setB t 27 true else t)
  else if v = 7 then (if tb s 7 then setB t 25 false else t)
  else if v = 8 then (if tb s 8 then setB t 26 false else t)
  else if v = 14 then (if tb s 14 then setB t 27 false else t)
  else t

/-- Request, acknowledge and served bits of client `c` (1..3). -/
def reqOf (s c : Nat) : Bool := if c = 1 then tb s 0 else if c = 2 then tb s 1 else tb s 2
def ackOf (s c : Nat) : Bool := if c = 1 then tb s 7 else if c = 2 then tb s 8 else tb s 14
def svOf (s c : Nat) : Bool := if c = 1 then tb s 25 else if c = 2 then tb s 26 else tb s 27

def cand (s c : Nat) : Bool := reqOf s c && !ackOf s c && !svOf s c

def spec (s v : Nat) : Bool :=
  let o := getO 23 s
  if v = 18 then
    (if tb s 18 = false then o == 0 && !tb s 19 && winner s != 0 && cand s (winner s)
     else o != 0 && tb s 19 && !reqOf s o)
  else if v = 19 then
    (if tb s 19 = false then tb s 18 && o != 0 && !svOf s o else !tb s 18)
  else if v = 7 ∨ v = 8 ∨ v = 14 then
    (let c := if v = 7 then 1 else if v = 8 then 2 else 3
     if tb s v = false then svOf s c && reqOf s c
     else svOf s c && !reqOf s c && o != c)
  else true

/-- Data: no arbiter ever has both grants high (exclusion), and in the broad
window the 2-bit index names the owner: client 0 -> 00, client 1 -> 01,
client 2 -> 10. (Two client acknowledges may legally overlap: a previous
owner's acknowledge still falling while the next owner's rises; that it does
fall is the persistence check.) -/
def good (s : Nat) : Bool :=
  let o := getO 23 s
  !(tb s 5 && tb s 6) && !(tb s 11 && tb s 12) &&
  (!(tb s 18 || tb s 19) ||
    (o != 0 && (tb s 15 == (o == 2)) && (tb s 16 == (o == 3))))

def sys (G : Gates) (H : Hyp) : Sys where
  V := 23
  nxv := nxv G H
  allow := allow H
  fire := fire
  spec := spec
  good := good
  hzM := 949751  -- every variable except 3, 9, 15, 16, 20, 21, 22
  live := fun v => decide (3 ≤ v)
  waiting := fun s =>
    (tb s 0 != tb s 7 || tb s 1 != tb s 8 || tb s 2 != tb s 14) &&
    (tb s 0 != tb s 7 || !tb s 0) && (tb s 1 != tb s 8 || !tb s 1) &&
    (tb s 2 != tb s 14 || !tb s 2)

/-- The proved configuration: every hypothesis on, the three index g-fork
branches delayed independently. -/
def hOK : Hyp := ⟨true, true, true, true, false⟩

end Formal.Cells.AMerge3
