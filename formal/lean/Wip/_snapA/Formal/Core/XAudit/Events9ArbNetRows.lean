import Formal.Core.XAudit.Events9ArbNet

/-!
# Formal.Core.XAudit.Events9ArbNetRows — the arbiter trace conditions as edge-time ROWS

Probe E9ArbNet, part 2 (shard A). See `formal/notes/A-e9arbnet.md` §4.

`Events9ArbNet.ArbCond` (the per-arbiter trace conditions of `design_verdict9arbnet`) is a set
of statements about the traces: B1 / B2 / C for the four readers (`Events9Arb.RdOK`), the settle
bound `hstall` with `H`, and a quiet start. This file states, per arbiter and reader, the
edge-time INEQUALITIES ("rows") that the informal derivation in the notes (§4) reduces them to,
as integer margins over

* the per-pin bands of `d` that `ArbOK` checks (`bandsOf`, and ustate O6's request reads `P1Q`,
  `P2Q`),
* the certificate's per-pin bands of the A0 node's read of `R0` (`r0Read`: the least lower end of
  the bands of `jA`'s pins whose source is `jR`, plus its stage band),
* two environment lower bounds supplied from outside (`wf`, `wr`: A0 falls → the request rises,
  A0 rises → the request falls).

A row holds iff its margin is `≥ 0`. These are DEFINITIONS only: NO theorem here or elsewhere says
that the rows imply `ArbCond` (the derivation in the notes is informal and uses, besides the rows,
"q makes clean transitions" and "no re-request within a window", i.e. an uncontested schedule).
The settle bound has no row: `hstall` needs `H` ≥ the longest stretch of an A0-low phase before
its q flip, which no band bounds (idle time, and for a near tie no bound exists at all); the only
number is `hMax`, the largest `H` the corrected core's ctl band `[lo, 10^12]` allows.
-/

namespace Formal.Core.XAudit.Events9ArbNet

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events8Arb
open Formal.Core.XAudit.Events9Arb

/-- One reader's bands: its request read `Dr`, its q read `Dq`, ustate O6's read of the same
request `DrQ`, ustate O5's (R0's) read of it `DrR`. -/
structure RdBands where
  Dr : Nat × Nat
  Dq : Nat × Nat
  DrQ : Nat × Nat
  DrR : Nat × Nat
  deriving Repr

def lo (p : Nat × Nat) : Int := p.1
def hi (p : Nat × Nat) : Int := p.2
def sh2 (p : Nat × Nat) : Nat × Nat := (p.1 - 2, p.2 - 2)

section
variable {N : Nat} (d : Design) (a : ArbD N)

/-- The four readers (g1, g2, shadow 1, shadow 2; a shadow reads as ustate O5 two steps later). -/
def readers : List (String × RdBands) :=
  let B := bandsOf d a
  let q1 := bd d ((a.gQ, a.i1Q) :: a.p1Q)
  let q2 := bd d ((a.gQ, a.i2Q) :: a.p2Q)
  [("g1", ⟨B.g1 0, B.g1 2, q1, B.r0 0⟩), ("g2", ⟨B.g2 1, B.g2 2, q2, B.r0 1⟩),
   ("s1", ⟨sh2 (B.r0 0), sh2 (B.r0 2), q1, B.r0 0⟩), ("s2", ⟨sh2 (B.r0 1), sh2 (B.r0 2), q2, B.r0 1⟩)]

end

/-- The least lower delay of the A0 node's read of `R0` (over its pins from `jR` and their copies),
stage band included; `none` if `jA` does not read `jR`. -/
def r0Read {N : Nat} (net : Net4 N) (b : Bands4 net) (jA jR : Fin N) : Option Nat :=
  (List.finRange (net.ar jA)).foldl (fun acc p =>
    if net.src jA p = jR then
      (List.finRange (net.nc jA p)).foldl (fun acc' i =>
        let v := b.loC jA p i + b.loF jA
        some (match acc' with | some m => min m v | none => v)) acc
    else acc) none

/-! ## The rows (margins in steps; a row holds iff its margin is `≥ 0`) -/

/-- **B1** (RT1 / RT1b): the reader reads its request's FALL before it reads a q flip away from its
branch. ustate O6 flips q away from branch `b` only after reading `r_b` low, so the flip leaves
ustate at least `lo DrQ` after the fall; the reader reads it at least `lo Dq` later; it reads the
fall at most `hi Dr` after it (2 steps: the `y (t − 2)` of `RdOK`). -/
def rowB1 (r : RdBands) : Int := lo r.DrQ + lo r.Dq - hi r.Dr - 2

/-- **B2b** (rise from a settled read, q flips toward the branch): the reader's first read of the
flip is still in the A0-low phase as ustate sees it: after the flip, R0 rises (`lo DqR`, R0's q
read), A0 rises (`w3`, the A0 node's R0 read), ustate reads A0 high (`lo DA`); the reader's first
q read of the flip is at most `hi Dq − lo Dq` after it. -/
def rowB2b (DqR DA : Nat × Nat) (w3 : Nat) (r : RdBands) : Int :=
  lo DqR + (w3 : Int) + lo DA + lo r.Dq - hi r.Dq - 2

/-- **B2c** (rise from a settled read, same branch again, q unchanged): when the reader first reads
the NEW request, ustate has not yet seen the A0 rise that this request causes (via R0's request
read `DrR`, `w3`, `DA`). -/
def rowB2c (DA : Nat × Nat) (w3 : Nat) (r : RdBands) : Int :=
  lo r.DrR + (w3 : Int) + lo r.Dq + lo DA - hi r.Dr - 2

/-- **B2a** (same branch again): ustate reads A0 LOW (the phase is settled) before the reader reads
the new request: `wf` = lower bound from A0's fall to the request's rise (environment). -/
def rowB2a (DA : Nat × Nat) (wf : Nat) (r : RdBands) : Int :=
  (wf : Int) + lo r.Dr - hi r.Dq - hi DA - 2

/-- **C-lo** (a request fall is read only at unsettled times, lower side): when the reader reads the
fall, ustate already reads A0 high: `wr` = lower bound from A0's rise to the request's fall. -/
def rowClo (DA : Nat × Nat) (wr : Nat) (r : RdBands) : Int :=
  (wr : Int) + lo r.Dr - hi r.Dq - hi DA - 2

/-- **C-hi** (upper side): when the reader reads the fall, ustate still reads A0 high (A0 falls only
after R0 reads the request low, `DrR`, and the A0 node reads R0 low, `w4`). -/
def rowChi (DA : Nat × Nat) (w4 : Nat) (r : RdBands) : Int :=
  lo r.DrR + (w4 : Int) + lo r.Dq + lo DA - hi r.Dr - 2

/-- **N** (a NECESSARY condition for the corrected core, not for `RdOK`): the corrected core lets a
reader's enable follow A0 no earlier than `lo DA + lo Dq` (ctl band `lo DA + K − 1`, the reader's
ctl pin `lo Dq − K − 1`, two stage steps), while the real reader (an AND of its request and q)
follows its request at `lo Dr`, and the environment answers an A0 edge with a request edge no
earlier than `w` (`wf` / `wr`). If `w + lo Dr < lo DA + lo Dq` and a behaviour realises the
lower ends, a same-branch re-grant (or a request fall) of the real cell is earlier than any
corrected-core behaviour allows, i.e. `HARB7'` would be refuted on it (informal; not in Lean). -/
def rowN (DA : Nat × Nat) (w : Nat) (r : RdBands) : Int := (w : Int) + lo r.Dr - lo DA - lo r.Dq

/-- The environment lower bound `wf` / `wr` that B2a / C-lo need (the row's margin at `w = 0`,
negated). -/
def needW (DA : Nat × Nat) (r : RdBands) : Int := hi r.Dq + hi DA + 2 - lo r.Dr

/-- The largest settle bound `H` that `ArbCond.hi` (`H + K + hi DA ≤ 10^12`) allows. -/
def hMax {N : Nat} (d : Design) (a : ArbD N) : Int :=
  (10 ^ 12 : Int) - kOf (bandsOf d a) - hi ((bandsOf d a).st 4)

end Formal.Core.XAudit.Events9ArbNet
