import Formal.Core.EnvFast.Data
import Formal.Core.EnvFast.Models

/-!
# Formal.Core.EnvFast.MuxModels — bd_mux and bd_merge-with-data models

Definitions only. Shard A. Notes: `formal/notes/A-envfast-2.md`.

LUT pins are the FREE pins ROOT FIRST (`LutAudit.opins`), from `LutCells`:
* `bd_mux_uj0` (bd_mux.v:68, I0..I5 = x_req, ctl_req, s, j0, rst, 0):
  `[rst, j0, s, ctl_req, x_req]`; `bd_mux_uj1` likewise with y.
* `bd_mux_uor` (I0 = j0, I1 = j1): `[j1, j0]`.
* `bd_c2_u` (I0 = a, I1 = b, I2 = q, I3 = rst): `[rst, q, b, a]`.
* `bd_datamux_u_L215` (W odd bit, LUT3, I0 = s, I1 = a, I2 = b; z = s ? b : a):
  `[b, a, s]`; `bd_datamux_u_L209` (LUT6_2 pair, I0 = s, I1 = a0, I2 = b0,
  I3 = a1, I4 = b1, I5 = 1): `[b1, a1, b0, a0, s]` for both O5 (bit 0) and O6
  (bit 1).

Common conventions (as `Env.linkModel`): `rst` held 0 and every signal 0 at
start (reset released after the loops cleared, H_RST_LONG); a sender's data
move only while its request and acknowledge are both low and before its private
"data is out" event `rdy`, and the request rises after `rdy` (H_BUNDLE, encoded
causally); any four-phase receiver on `z_req`/`z_ack`; `bd_delay` is one wire
element (`zr` follows `either`) with its own unbounded delay.
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env

/-! ## bd_mux, control path, every fork isochronic

Signals: `xr 0, yr 1, cr 2 (ctl_req), s 3, j0 4, j1 5, or 6 (either), zr 7,
za 8 (z_ack = ctl_ack), xa 9, ya 10, rst 11, rdc 12` (`rdc`: the control
sender's private "select is out" event). Senders x, y: four-phase on
`xr/xa`, `yr/ya`, requesting at will (the sources need not be exclusive). The
control sender: `s` moves only while `cr = 0`, `ctl_ack = 0` and before `rdc`
(the header: `s` is held from `ctl_req↑` until `ctl_ack↓`); `cr` rises after
`rdc`, falls after `ctl_ack↑`. -/

structure MuxAsm where
  /-- Return-to-zero of the acknowledges: while `x_ack` (`y_ack`) is excited
  (in particular falling after `z_ack↓`), `z_ack` does not fire. Not in the RTL
  header. -/
  rtz : Bool

def muxGates : List Gate :=
  [.lut 4 bd_mux_uj0 .O [11, 4, 3, 2, 0], .lut 5 bd_mux_uj1 .O [11, 5, 3, 2, 1],
   .lut 6 bd_mux_uor .O [5, 4], .wire 7 6,
   .lut 9 bd_c2_u .O [11, 9, 8, 4], .lut 10 bd_c2_u .O [11, 10, 8, 5]]

def muxEnv : List (Nat × (Nat → Bool)) :=
  [(0, fun s => bit s 0 == bit s 9),
   (1, fun s => bit s 1 == bit s 10),
   (3, fun s => !bit s 12 && !bit s 2 && !bit s 8),
   (12, fun s => (!bit s 12 && !bit s 2 && !bit s 8) || (bit s 12 && bit s 2)),
   (2, fun s => (!bit s 2 && bit s 12 && !bit s 8) || (bit s 2 && bit s 8)),
   (8, fun s => bit s 8 != bit s 7)]

def muxModel (A : MuxAsm) : Model where
  n := 13
  gates := muxGates
  env := muxEnv
  prio := if A.rtz then [(9, 8), (10, 8)] else []
  inits := [0]

/-- Token accounting: an acknowledge rises only for the input the control
selected (`x_ack↑` only with `s = 0`, `y_ack↑` only with `s = 1`); the receiver
may acknowledge only while `ctl_req` is high and exactly the selected join has
fired; and some transition is enabled. Signal positions as in `muxModel`. -/
def muxQ (M : Model) (s : Nat) : Bool :=
  live M s &&
    !(bit (excMask M s) 9 && !bit s 9 && bit s 3) &&
    !(bit (excMask M s) 10 && !bit s 10 && !bit s 3) &&
    !(bit (enMask M s) 8 && !bit s 8 &&
      !(bit s 2 && (if bit s 3 then bit s 5 && !bit s 4 else bit s 4 && !bit s 5)))

/-! ## bd_mux with the `z_ack` fork modelled

As `muxModel`, plus three wire elements for the branches of `z_ack`:
`zaX 13` (at `uxa`), `zaY 14` (at `uya`), `zaC 15` (`ctl_ack`, read by the
control sender). -/

structure MuxZaAsm where
  rtz : Bool
  /-- Every `z_ack` branch settles before `z_ack` changes again (no branch
  carries two transitions at once). -/
  zaSettle : Bool
  /-- The `z_ack` branch at `uxa` (`uya`) settles before `j0` (`j1`) changes:
  the round trip `z_ack → … → join` is slower than the fork skew. -/
  zaIso : Bool

def muxZaModel (A : MuxZaAsm) : Model where
  n := 16
  gates := [.lut 4 bd_mux_uj0 .O [11, 4, 3, 2, 0], .lut 5 bd_mux_uj1 .O [11, 5, 3, 2, 1],
            .lut 6 bd_mux_uor .O [5, 4], .wire 7 6,
            .lut 9 bd_c2_u .O [11, 9, 13, 4], .lut 10 bd_c2_u .O [11, 10, 14, 5],
            .wire 13 8, .wire 14 8, .wire 15 8]
  env := [(0, fun s => bit s 0 == bit s 9),
          (1, fun s => bit s 1 == bit s 10),
          (3, fun s => !bit s 12 && !bit s 2 && !bit s 15),
          (12, fun s => (!bit s 12 && !bit s 2 && !bit s 15) || (bit s 12 && bit s 2)),
          (2, fun s => (!bit s 2 && bit s 12 && !bit s 15) || (bit s 2 && bit s 15)),
          (8, fun s => bit s 8 != bit s 7)]
  prio := (if A.rtz then [(9, 8), (10, 8)] else []) ++
          (if A.zaSettle then [(13, 8), (14, 8), (15, 8)] else []) ++
          (if A.zaIso then [(13, 4), (14, 5)] else [])
  inits := [0]

/-! ## bd_mux with one `ctl_req` branch modelled

As `muxModel`, plus the branch `cr1 13` of `ctl_req` at `uj1` as a wire element
(`uj0` reads `ctl_req` directly). By the x/y, s/¬s symmetry of the cell this
also covers the branch at `uj0` alone; both branches lagging at once is not
covered (state count). -/

structure MuxCrAsm where
  rtz : Bool
  /-- The `ctl_req` branch settles before `ctl_req` changes again. -/
  crSettle : Bool
  /-- Hold of the select at the join pin: the `ctl_req` branch at `uj1` has
  fallen before `s` moves. -/
  sHold : Bool

def muxCrModel (A : MuxCrAsm) : Model where
  n := 14
  gates := [.lut 4 bd_mux_uj0 .O [11, 4, 3, 2, 0], .lut 5 bd_mux_uj1 .O [11, 5, 3, 13, 1],
            .lut 6 bd_mux_uor .O [5, 4], .wire 7 6,
            .lut 9 bd_c2_u .O [11, 9, 8, 4], .lut 10 bd_c2_u .O [11, 10, 8, 5], .wire 13 2]
  env := muxEnv
  prio := (if A.rtz then [(9, 8), (10, 8)] else []) ++
          (if A.crSettle then [(13, 2)] else []) ++
          (if A.sHold then [(13, 3)] else [])
  inits := [0]

/-! ## bd_mux with its data mux (W = 1)

As `muxModel`, plus `xd 13, yd 14, zd 15, rdx 16, rdy 17`: the data bits, the
output of `bd_datamux`'s odd-bit LUT3 (`z = s ? y : x`), and the data senders'
private "data is out" events. -/

structure MuxDAsm where
  rtz : Bool
  /-- Matched delay (rule A): the data mux output has settled before `z_req`
  fires. -/
  bundle : Bool
  /-- `true`: the y sender moves its data like x (27680 reachable states; the
  certificate is generated but too costly to kernel-check here, see notes).
  `false`: y's bit is held at 1 (x's starts at 0, so a wrong selection is
  visible); x's data moves. -/
  yMoves : Bool

def muxDEnvX : List (Nat × (Nat → Bool)) :=
  [(13, fun s => !bit s 16 && !bit s 0 && !bit s 9),
   (16, fun s => (!bit s 16 && !bit s 0 && !bit s 9) || (bit s 16 && bit s 0)),
   (0, fun s => (!bit s 0 && bit s 16 && !bit s 9) || (bit s 0 && bit s 9))]

def muxDEnvY (yMoves : Bool) : List (Nat × (Nat → Bool)) :=
  if yMoves then
    [(14, fun s => !bit s 17 && !bit s 1 && !bit s 10),
     (17, fun s => (!bit s 17 && !bit s 1 && !bit s 10) || (bit s 17 && bit s 1)),
     (1, fun s => (!bit s 1 && bit s 17 && !bit s 10) || (bit s 1 && bit s 10))]
  else [(1, fun s => bit s 1 == bit s 10)]

def muxDEnvC : List (Nat × (Nat → Bool)) :=
  [(3, fun s => !bit s 12 && !bit s 2 && !bit s 8),
   (12, fun s => (!bit s 12 && !bit s 2 && !bit s 8) || (bit s 12 && bit s 2)),
   (2, fun s => (!bit s 2 && bit s 12 && !bit s 8) || (bit s 2 && bit s 8)),
   (8, fun s => bit s 8 != bit s 7)]

def muxDModel (A : MuxDAsm) : Model where
  n := 18
  gates := muxGates ++ [.lut 15 bd_datamux_u_L215 .O [14, 13, 3]]
  env := muxDEnvX ++ muxDEnvY A.yMoves ++ muxDEnvC
  prio := (if A.rtz then [(9, 8), (10, 8)] else []) ++ (if A.bundle then [(15, 7)] else [])
  inits := [if A.yMoves then 0 else 2 ^ 14 + 2 ^ 15]

/-- The output channel's hold window `z_req↑ … z_ack↓`; `zd` is data. -/
def muxDSpec : DSpec := ⟨fun u => u == 15, fun s => bit s 7 || bit s 8⟩

/-- `muxQ`, and data validity: while the window is open, `z_data` is not
excited and equals the selected input's bit (`s ? y : x`). -/
def muxDQ (M : Model) (s : Nat) : Bool :=
  muxQ M s && (!(bit s 7 || bit s 8) ||
    (!bit (excMask M s) 15 && bit s 15 == (if bit s 3 then bit s 14 else bit s 13)))

/-! ## bd_merge with its data mux

`EnvFast.mergeModel`'s control path (`xr 0, yr 1, or 2, zr 3, za 4, xa 5, ya 6,
sel 7, rst 8`) plus `rdx 9, rdy 10, xd 11, yd 12, zd 13` (W = 1, the odd-bit
LUT3, `z = sel ? x : y`, i.e. `bd_datamux` with `a = y`, `b = x`), and for W = 2
`xd1 14, yd1 15, zd1 16` with the LUT6_2 pair (`zd` = O5, `zd1` = O6). The
senders now carry data: they move it only while their request and
acknowledge are low and before `rdy`, raise the request after `rdy` (and,
under `excl`, only when the other side is idle). -/

structure MergeDAsm where
  /-- bd_merge's documented obligation (see `MergeAsm.excl`). -/
  excl : Bool
  /-- `EnvFast.MergeAsm.selFast`: `sel` settles before `x_req`/`x_ack` move again. -/
  selFast : Bool
  /-- Matched delay (rule A): `sel` and the data mux outputs have settled
  before `z_req` fires. -/
  bundle : Bool

def mergeDModel (W : Nat) (A : MergeDAsm) : Model where
  n := if W = 2 then 17 else 14
  gates := [.lut 2 bd_merge_uor .O [1, 0], .wire 3 2,
            .lut 5 bd_c2_u .O [8, 5, 4, 0], .lut 6 bd_c2_u .O [8, 6, 4, 1],
            .lut 7 bd_merge_usel .O [5, 0]] ++
            (if W = 2 then [.lut 13 bd_datamux_u_L209 .O5 [14, 15, 11, 12, 7],
                            .lut 16 bd_datamux_u_L209 .O6 [14, 15, 11, 12, 7]]
             else [.lut 13 bd_datamux_u_L215 .O [11, 12, 7]])
  env := [(11, fun s => !bit s 9 && !bit s 0 && !bit s 5),
          (9, fun s => (!bit s 9 && !bit s 0 && !bit s 5) || (bit s 9 && bit s 0)),
          (0, fun s => (!bit s 0 && bit s 9 && !bit s 5 && (!A.excl || (!bit s 1 && !bit s 6))) ||
            (bit s 0 && bit s 5)),
          (12, fun s => !bit s 10 && !bit s 1 && !bit s 6),
          (10, fun s => (!bit s 10 && !bit s 1 && !bit s 6) || (bit s 10 && bit s 1)),
          (1, fun s => (!bit s 1 && bit s 10 && !bit s 6 && (!A.excl || (!bit s 0 && !bit s 5))) ||
            (bit s 1 && bit s 6)),
          (4, fun s => bit s 4 != bit s 3)] ++
          (if W = 2 then [(14, fun s => !bit s 9 && !bit s 0 && !bit s 5),
                          (15, fun s => !bit s 10 && !bit s 1 && !bit s 6)] else [])
  prio := (if A.selFast then [(7, 0), (7, 5)] else []) ++
          (if A.bundle then [(7, 3), (13, 3)] ++ (if W = 2 then [(16, 3)] else []) else [])
  inits := [0]

/-- Window `z_req↑ … z_ack↓`; `sel` and the data mux outputs are data. -/
def mergeDSpec : DSpec := ⟨fun u => u == 7 || u == 13 || u == 16, fun s => bit s 3 || bit s 4⟩

/-- `EnvFast.mergeQ` (token accounting, liveness) and data validity: while the
window is open, the data mux outputs are not excited and equal the bits of the
input whose transaction is live (x iff `x_req ∨ x_ack`). -/
def mergeDQ (W : Nat) (M : Model) (s : Nat) : Bool :=
  mergeQ M s && (!(bit s 3 || bit s 4) ||
    (!bit (excMask M s) 13 &&
      bit s 13 == (if bit s 0 || bit s 5 then bit s 11 else bit s 12) &&
      (W != 2 || (!bit (excMask M s) 16 &&
        bit s 16 == (if bit s 0 || bit s 5 then bit s 14 else bit s 15)))))

end Formal.Core.EnvFast
