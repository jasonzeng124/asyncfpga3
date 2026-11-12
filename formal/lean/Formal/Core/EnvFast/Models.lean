import Formal.Core.Env

/-!
# Formal.Core.EnvFast.Models — `Env` models checked with the fast checker

Definitions only. `link2Model` is a verbatim copy of `Formal.Core.Env.Wip.link2Model`
(`formal/lean/Wip/Env.lean`, which is not built and so cannot be imported).
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env

/-- bd_link with a W = 2 latch pair (LUT6_2 `bd_latch_u_L38`). Signals:
`req 0, c 1, ack 2, en 3, d0 4, d1 5, q0 6, q1 7, rdy 8, rst 9`. Same
environment discipline as `Env.linkModel` (W = 1): the sender moves both data
bits only while `req = c = 0` and before `rdy`; any four-phase receiver on
`c`/`ack`. -/
def link2Model (A : LinkAsm) : Model where
  n := 10
  gates := [.lut 1 bd_c2n_u .O [9, 1, 2, 0], .wire 3 1,
            .lut 6 bd_latch_u_L38 .O5 [7, 5, 6, 3, 4],
            .lut 7 bd_latch_u_L38 .O6 [7, 5, 6, 3, 4]]
  env := [(4, fun s => !bit s 8 && !bit s 0 && !bit s 1),
          (5, fun s => !bit s 8 && !bit s 0 && !bit s 1),
          (8, fun s => (!bit s 8 && !bit s 0 && !bit s 1) || (bit s 8 && bit s 0)),
          (0, fun s => (!bit s 0 && bit s 8 && !bit s 1) || (bit s 0 && bit s 1)),
          (2, fun s => bit s 2 != bit s 1)]
  prio := (if A.ruleH then [(3, 4), (3, 5), (3, 8)] else []) ++
          (if A.ruleL then [(6, 3), (7, 3)] else []) ++
          (if A.isoEn then [(3, 2)] else []) ++
          (if A.rxBundle then [(6, 2), (7, 2)] else [])
  inits := (List.range 16).map (· * 16)

/-- Data validity at the receiver for W = 2 (`Env.linkData` for both bits):
whenever the receiver may raise `ack`, both latch outputs hold the sender's
bits and are not excited. -/
def link2Data (M : Model) (s : Nat) : Bool :=
  !(bit (enMask M s) 2 && !bit s 2) ||
    (bit s 6 == bit s 4 && bit s 7 == bit s 5 && !bit (excMask M s) 6 && !bit (excMask M s) 7)

def link2Q (M : Model) (s : Nat) : Bool := live M s && link2Data M s

/-! ## bd_merge (control path)

`cells/rtl/bd_merge.v`: `either = x_req + y_req` (LUT2 `uor`), `z_req =
delay(either)` (the `bd_delay` line, modelled as one wire element with its own
unbounded delay), `x_ack = C(x_req, z_ack)`, `y_ack = C(y_req, z_ack)` (two
`bd_c2` LUTs), `sel = x_req + x_ack` (LUT2 `usel`). The data mux is not modelled.
Signals: `xr 0, yr 1, or 2, zr 3, za 4, xa 5, ya 6, sel 7, rst 8` (rst held 0,
reset released before the run starts; everything 0 at start). Environment: two
four-phase senders on `xr/xa` and `yr/ya`, any four-phase receiver on `zr/za`. -/

structure MergeAsm where
  /-- The cell's documented obligation (bd_merge.v header): an input may raise
  its request only when the other input's transaction has fully completed
  (its request and acknowledge are both low). -/
  excl : Bool
  /-- The select LUT settles before the x side moves again: `sel` (= x_req +
  x_ack) has followed an `x_ack` edge before `x_req` or `x_ack` changes next.
  Found by the checker: without it `sel` can be withdrawn (x_ack rises and
  falls before sel follows; or x_req rises again before sel has fallen, a
  static-1 MIC on the OR). -/
  selFast : Bool

def mergeModel (A : MergeAsm) : Model where
  n := 9
  gates := [.lut 2 bd_merge_uor .O [1, 0], .wire 3 2,
            .lut 5 bd_c2_u .O [8, 5, 4, 0], .lut 6 bd_c2_u .O [8, 6, 4, 1],
            .lut 7 bd_merge_usel .O [5, 0]]
  env := [(0, fun s => bit s 0 == bit s 5 && (bit s 0 || !A.excl || (!bit s 1 && !bit s 6))),
          (1, fun s => bit s 1 == bit s 6 && (bit s 1 || !A.excl || (!bit s 0 && !bit s 5))),
          (4, fun s => bit s 4 != bit s 3)]
  prio := if A.selFast then [(7, 0), (7, 5)] else []
  inits := [0]

/-- Token accounting at the merge: an acknowledge never rises while the OTHER
input's transaction is live (that acknowledge would be for a token the merge
never carried), and some transition is enabled. -/
def mergeQ (M : Model) (s : Nat) : Bool :=
  live M s &&
    !(bit (excMask M s) 6 && !bit s 6 && (bit s 0 || bit s 5)) &&
    !(bit (excMask M s) 5 && !bit s 5 && (bit s 1 || bit s 6))

end Formal.Core.EnvFast
