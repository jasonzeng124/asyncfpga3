import Formal.Cells.AMergeSys
import Formal.Cells.AMergeGates

/-!
# Probe Cm, part 4: `bdc_muxn3_32` (the 3-way loop header of gcd_hw)

`bdc/emit.py` `emit_muxn(32, 3)`, 1 instance in gcd_hw (DELAY 12): `bd_mux`'s
structure with three inputs and a 2-bit index:

    sel[k] = ctl_req & (s == k)          (inferred LUT3s, H_YOSYS_MAP)
    j[k]   = bd_c2 uj_k (in_k_req, sel[k])
    |j     = LUT3 FE                     (inferred) -> uor -> bd_delay_gated -> z_req
    in_k_ack = bd_c2 ua_k (j[k], z_ack)
    ctl_ack  = z_ack
    z_data   = (s == 2) ? in2 : (s == 1) ? in1 : in0   (LUT5 per bit)

Unlike `bd_mux`, the decode is NOT folded into the join's LUT: `sel[k]` is its
own LUT3 and its own wire into `uj_k` (H_YOSYS_MAP), so there is one more gate
between `ctl_req` and each join.

## Model (speed independent, `AMergeSys.Sys`; the N = 3 version of
`MergeMuxSI.mux`)

Variables: `0 x0`, `1 x1`, `2 x2` (clients, four-phase on their acks),
`3 ctl_req` (control sender, four-phase on `ctl_ack = z_ack`), `4 s0`,
`5 s1` (the index, free data bits under H_CTL_HOLD / H_S_RANGE),
`6 sel0`, `7 sel1`, `8 sel2` (decode LUT3s), `9 j0`, `10 j1`, `11 j2`
(`uj_k`), `12 orj` (`|j` LUT3), `13` unused (never excited), `14 z_req` (`uor` and
`bd_delay_gated` lumped as ONE delay element from `|j`, H_DELAY_BUF), `15 z_ack` (server), `16 a0`, `17 a1`,
`18 a2` (`ua_k`), `19 j0@ua0`, `20 j1@ua1`, `21 j2@ua2` (the `j` fork
branches into the acknowledge C-elements; isochronic if the flag says so).
Ghosts: `22-23 o` (owner: 0 none, k+1 = input k), `24-26 sv0..sv2`,
`27 gk` (control token consumed).

Isochronic (named): `ctl_req -> {sel0, sel1, sel2}` and
`z_ack -> {ua0, ua1, ua2, ctl sender}` (the two forks `MergeMuxSI` proved
must be isochronic for `bd_mux`, `mux_needs_iso_za`, `mux_needs_iso_cr`);
`s -> {sel0, sel1, sel2, data LUTs}` read without skew (**H_S_PIN**, below);
`j -> |j` (the OR reads the joins directly).
-/

namespace Formal.Cells.MuxN3
open Formal.Cells.AMergeSys Formal.Cells.AMergeGates

structure Hyp where
  /-- **H_CTL_HOLD** (the `bdc_muxn` header's contract, "the index is
  ordinary channel data, held by the control channel's contract from
  ctl_req-rise to ctl_ack-fall"): `s` changes only while `ctl_req` is low and
  the control sender sees `ctl_ack` low. -/
  hold : Bool
  /-- **H_MUX_RTZ** (as `MergeMuxSI`): `z_ack` rises only when no `ua_k` is
  excited to fall. -/
  rtz : Bool
  /-- `j_k -> ua_k` forks isochronic. -/
  isoJ : Bool

/-- The index value `s1 s0`. -/
def sIdx (s : Nat) : Nat := (if tb s 4 then 1 else 0) + (if tb s 5 then 2 else 0)

def rdJ (H : Hyp) (s k : Nat) : Bool := if H.isoJ then tb s (9 + k) else tb s (19 + k)

/-- The next-value vector (`Sys.nxv`): entry `k` is what variable `k` becomes
if it fires now. Gates are evaluated through `G` (the theorems use `gI`, the
real INITs). -/
def nxv (G : Gates) (H : Hyp) (s : Nat) : Nat := Sys.bits [
    (if tb s 0 == tb s 16 then !tb s 0 else tb s 0),  -- 0 client 0
    (if tb s 1 == tb s 17 then !tb s 1 else tb s 1),  -- 1 client 1
    (if tb s 2 == tb s 18 then !tb s 2 else tb s 2),  -- 2 client 2
    (if tb s 3 == tb s 15 then !tb s 3 else tb s 3),  -- 3 ctl sender
    !tb s 4,  -- 4 index bits: free
    !tb s 5,  -- 5 index bits: free
    G.sel0 (tb s 4) (tb s 5) (tb s 3),  -- 6 decode 0
    G.sel1 (tb s 4) (tb s 5) (tb s 3),  -- 7 decode 1
    G.sel2 (tb s 4) (tb s 5) (tb s 3),  -- 8 decode 2
    G.c2 (tb s 0) (tb s 6) (tb s 9),  -- 9 uj0
    G.c2 (tb s 1) (tb s 7) (tb s 10),  -- 10 uj1
    G.c2 (tb s 2) (tb s 8) (tb s 11),  -- 11 uj2
    G.or3 (tb s 9) (tb s 10) (tb s 11),  -- 12 |j
    tb s 13,  -- 13 (unused)
    G.buf1 (tb s 12),  -- 14 uor + bd_delay_gated
    tb s 14,  -- 15 server
    G.c2 (rdJ H s 0) (tb s 15) (tb s 16),  -- 16 ua0
    G.c2 (rdJ H s 1) (tb s 15) (tb s 17),  -- 17 ua1
    G.c2 (rdJ H s 2) (tb s 15) (tb s 18),  -- 18 ua2
    (if H.isoJ then tb s 19 else tb s 9),  -- 19 j0@ua0
    (if H.isoJ then tb s 20 else tb s 10),  -- 20 j1@ua1
    (if H.isoJ then tb s 21 else tb s 11)  -- 21 j2@ua2
  ]

/-- Per-variable view. -/
def nx (G : Gates) (H : Hyp) (s v : Nat) : Bool := (nxv G H s).testBit v

def exv (G : Gates) (H : Hyp) (s v : Nat) : Bool := nx G H s v != tb s v

/-- **H_S_RANGE** (always on): the index is never 3. The producer in gcd_hw
is `bdc_amerge3_0`'s index, which `AMerge3Proof.amerge3_ok` shows names a
client 0..2 in its window; with `s = 3` no decode fires and the token would
wait for ever. -/
def H_S_RANGE (s v : Nat) : Bool :=
  if v = 4 then sIdx (s ^^^ 2 ^ 4) != 3
  else if v = 5 then sIdx (s ^^^ 2 ^ 5) != 3 else true

/-- The filters; `e` is the excitation mask of `s` (`e.testBit k`: variable
`k` is excited). -/
def allow (H : Hyp) (e s v : Nat) : Bool :=
  H_S_RANGE s v &&
  (!H.hold || (if v = 4 ∨ v = 5 then !tb s 3 && !tb s 15 else true)) &&
  (!H.rtz || (if v = 15 ∧ tb s 15 = false then
      !e.testBit 16 && !e.testBit 17 && !e.testBit 18 else true))

def fire (s v : Nat) : Nat :=
  let t := s ^^^ 2 ^ v
  if v = 14 then (if tb s 14 then t else setB (setO 22 t (sIdx s + 1)) 27 true)
  else if v = 15 then
    (if tb s 15 then setB (setO 22 t 0) 27 false
     else if getO 22 s = 1 then setB t 24 true
     else if getO 22 s = 2 then setB t 25 true
     else if getO 22 s = 3 then setB t 26 true else t)
  else if v = 16 then (if tb s 16 then setB t 24 false else t)
  else if v = 17 then (if tb s 17 then setB t 25 false else t)
  else if v = 18 then (if tb s 18 then setB t 26 false else t)
  else t

def reqOf (s c : Nat) : Bool := tb s (c - 1)
def ackOf (s c : Nat) : Bool := tb s (c + 15)
def svOf (s c : Nat) : Bool := tb s (c + 23)

/-- The mux specification automaton (`MergeMuxSI.xSpec` for three inputs):
`z_req` rises only with `ctl_req` high, an unconsumed control token, and the
input SELECTED BY `s` requesting, unacknowledged and not yet served (the
owner is set to that input); it falls only after `z_ack`, with the owner's
request and `ctl_req` low; `z_ack` once per token; an input's acknowledge
rises only after the server acknowledged THAT input's token and falls only
after the transaction returned to zero; the control sender drops `ctl_req`
only after `ctl_ack`. Hence only the selected input is ever acknowledged,
once per control token, and the other two keep their tokens. -/
def spec (s v : Nat) : Bool :=
  let o := getO 22 s
  if v = 14 then
    (if tb s 14 = false then
       o == 0 && !tb s 15 && tb s 3 && !tb s 27 &&
       reqOf s (sIdx s + 1) && !ackOf s (sIdx s + 1) && !svOf s (sIdx s + 1)
     else o != 0 && tb s 15 && !tb s 3 && !reqOf s o)
  else if v = 15 then
    (if tb s 15 = false then tb s 14 && o != 0 && !svOf s o else !tb s 14)
  else if v = 16 ∨ v = 17 ∨ v = 18 then
    (let c := v - 15
     if tb s v = false then svOf s c && reqOf s c
     else svOf s c && !reqOf s c && o != c)
  else if v = 3 then (if tb s 3 then tb s 15 else true)
  else true

/-- Data: in the broad window the index (the data LUTs' select) names the
owner, and the three joins are one-hot (the `bdc_muxn` header's claim that
makes the `|j` LUT glitch-free). -/
def good (s : Nat) : Bool :=
  let o := getO 22 s
  !(tb s 9 && tb s 10) && !(tb s 9 && tb s 11) && !(tb s 10 && tb s 11) &&
  (!(tb s 14 || tb s 15) || (o != 0 && sIdx s + 1 == o))

/-- A token and its control token are both present (or the transaction is
returning to zero), and every client is at rest or waiting: the circuit
must be able to move. -/
def waiting (s : Nat) : Bool :=
  (tb s 0 != tb s 16 || !tb s 0) && (tb s 1 != tb s 17 || !tb s 1) &&
  (tb s 2 != tb s 18 || !tb s 2) &&
  ((tb s 3 && !tb s 15 && reqOf s (sIdx s + 1) && !ackOf s (sIdx s + 1)) ||
   (!tb s 3 && tb s 15))

def sys (G : Gates) (H : Hyp) : Sys where
  V := 22
  nxv := nxv G H
  allow := allow H
  fire := fire
  spec := spec
  good := good
  hzM := 4194303  -- every variable
  live := fun v => decide (6 ≤ v)
  waiting := waiting

/-- The proved configuration: H_CTL_HOLD and H_MUX_RTZ on, the `j -> ua`
forks delayed independently. -/
def hOK : Hyp := ⟨true, true, false⟩

end Formal.Cells.MuxN3
