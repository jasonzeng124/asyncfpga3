import Formal.Core.Prims.SeqLatch

/-!
# Formal.Core.Prims.SeqXray — prjxray-db numbers for the slice flops and latches

Shard A, probe PrimsSeq. Core Lean only. Notes: `formal/notes/A-prims-seq.md` §2.

## Source (transcribed by hand, integer ps)

`$TC/openxc7/share/nextpnr/prjxray-db/zynq7/timings/slicel.sdf` (`TIMESCALE 1ns`).

* `REG_INIT_FF` (the AFF..DFF bels, FDRE/FDSE/FDCE/FDPE): `IOPATH CLK Q (0.112::0.139)(0.274::0.34)`;
  `SETUP DIN (-0.055::-0.045)`, `HOLD DIN (0.194::0.241)`, `SETUP CE (0.088::0.109)`,
  `HOLD CE (-0.011::-0.009)`.
  `REG_INIT_FF_QL` (SR to 0): `IOPATH SR Q (0.246::0.306)(0.662::0.821)`, `RECOVERY SR (0.326::0.404)`,
  `REMOVAL SR (-0.305::-0.248)`. `REG_INIT_FF_QH` (SR to 1): `IOPATH SR Q (0.195::0.243)(0.476::0.591)`,
  `RECOVERY SR (0.288::0.358)`, same REMOVAL.
* `FF_INIT` (the A5FF..D5FF bels): `CLK Q (0.099::0.124)(0.244::0.303)`; `SETUP DIN (-0.057::-0.046)`,
  `HOLD DIN (0.181::0.225)`, CE as above. `FF_INIT_QL`: `SR Q (0.233::0.29)(0.616::0.764)`,
  `RECOVERY (0.326::0.404)`; `FF_INIT_QH`: `SR Q (0.182::0.227)(0.445::0.552)`, `RECOVERY (0.288::0.358)`.
* `REG_INIT_LAT` (LDCE/LDPE): `CE Q (0.13::0.162)(0.409::0.507)`, `CLK Q (0.129::0.16)(0.357::0.443)`,
  `D Q (0.073::0.092)(0.213::0.264)`; `SETUP DIN (-0.068::-0.056)`, `HOLD DIN (0.194::0.241)`.
  `REG_INIT_LAT_QL`: `SR Q (0.198::0.246)(0.638::0.791)`; `_QH`: `SR Q (0.164::0.204)(0.487::0.604)`.

## Corners

IOPATH triples are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`, fast and slow process corners
(NOT rise/fall; prjxray has no rise/fall split, so every band here is shared by both edges).
**TIMINGCHECK values have ONE pair only**: `prjxray/utils/makesdf.py` writes
`({SLOW_MIN}::{SLOW_MAX})` for SETUP/HOLD/RECOVERY/REMOVAL. So the shipped database has no
fast-corner window at all. Both corners below use the slow window (**H_WINDOW_SLOW_ONLY**: an
assumption, untested; a fast die may have a narrower or shifted aperture).

## Which end of each pair

A window must be at least as wide as silicon's (a wider window only produces more X):
`lo = -SETUP_MAX`, `hi = HOLD_MAX`, `srLo = -RECOVERY_MAX`, `srHi = REMOVAL_MAX`. Bands use
`[MIN, MAX]` of the chosen corner. The prjxray SETUP of DIN is negative: the D window lies
entirely AFTER the clock edge at the bel (+45..+241 ps), because the clock's path inside
the site is longer than D's. Windows are at the bel pins (prjxray's routing-bel hops, e.g.
`clk aff (0.029::0.036)(0.093::0.116)`, `ax aff (0.06::0.075)(0.165::0.205)`, are routing,
not part of these numbers: H_FF_PINREF).

For the sync R/S (FDRE/FDSE) prjxray gives no SETUP/HOLD on SR, only RECOVERY/REMOVAL, and
those are used as its window (**H_SR_SYNC_WINDOW**).

`res` (H_FF_RESOLVE / H_LAT_RESOLVE) has no prjxray value: it stays a parameter.
-/

namespace Formal.Core.Prims.Seq

/-- Process corner. -/
inductive XCorner where
  | fast
  | slow
  deriving DecidableEq, Repr

/-- AFF..DFF (`REG_INIT_FF`); `rv` selects the QL (reset, `false`) or QH (set, `true`) arcs. -/
def regFF (c : XCorner) (rv : Bool) (res : Nat) : FFTiming :=
  { cqLo := match c with | .fast => 112 | .slow => 274
    cqHi := match c with | .fast => 139 | .slow => 340
    dLo := 45, dHi := 241
    ceLo := -109, ceHi := -9
    srLo := if rv then -358 else -404, srHi := -248
    sqLo := match c, rv with | .fast, false => 246 | .slow, false => 662
                           | .fast, true => 195 | .slow, true => 476
    sqHi := match c, rv with | .fast, false => 306 | .slow, false => 821
                           | .fast, true => 243 | .slow, true => 591
    res := res }

/-- A5FF..D5FF (`FF_INIT`). -/
def ff5 (c : XCorner) (rv : Bool) (res : Nat) : FFTiming :=
  { cqLo := match c with | .fast => 99 | .slow => 244
    cqHi := match c with | .fast => 124 | .slow => 303
    dLo := 46, dHi := 225
    ceLo := -109, ceHi := -9
    srLo := if rv then -358 else -404, srHi := -248
    sqLo := match c, rv with | .fast, false => 233 | .slow, false => 616
                           | .fast, true => 182 | .slow, true => 445
    sqHi := match c, rv with | .fast, false => 290 | .slow, false => 764
                           | .fast, true => 227 | .slow, true => 552
    res := res }

/-- LDCE (`rv = false`) / LDPE (`rv = true`), `REG_INIT_LAT`. The gate band is the wider
of CLK->Q and CE->Q (H_LAT_GATE); `hLo = -dqHi(slow) = -264` (H_LAT_WINDOW: it also covers
`-SETUP_MAX = +56`), `hHi = HOLD_MAX = 241`. -/
def lat (c : XCorner) (rv : Bool) (res : Nat) : LatTiming :=
  { gqLo := match c with | .fast => 129 | .slow => 357
    gqHi := match c with | .fast => 162 | .slow => 507
    dqLo := match c with | .fast => 73 | .slow => 213
    dqHi := match c with | .fast => 92 | .slow => 264
    hLo := -264, hHi := 241
    sqLo := match c, rv with | .fast, false => 198 | .slow, false => 638
                           | .fast, true => 164 | .slow, true => 487
    sqHi := match c, rv with | .fast, false => 246 | .slow, false => 791
                           | .fast, true => 204 | .slow, true => 604
    res := res }

/-- Every prjxray flop instance is well formed, so `sim_rel`/`capture` apply to it. -/
theorem regFF_ok (c : XCorner) (rv : Bool) (res : Nat) : (regFF c rv res).Ok := by
  cases c <;> cases rv <;> decide

theorem ff5_ok (c : XCorner) (rv : Bool) (res : Nat) : (ff5 c rv res).Ok := by
  cases c <;> cases rv <;> decide

/-- Bands are nonempty and ordered at both corners. -/
theorem regFF_bands (c : XCorner) (rv : Bool) (res : Nat) :
    (regFF c rv res).cqLo ≤ (regFF c rv res).cqHi ∧ (regFF c rv res).sqLo ≤ (regFF c rv res).sqHi := by
  cases c <;> cases rv <;> decide

theorem lat_bands (c : XCorner) (rv : Bool) (res : Nat) :
    (lat c rv res).dqLo ≤ (lat c rv res).dqHi ∧ (lat c rv res).hLo ≤ (lat c rv res).hHi ∧
      (lat c rv res).gqLo ≤ (lat c rv res).gqHi := by
  cases c <;> cases rv <;> decide

/-- The D aperture of an AFF..DFF flop is `[e + 45, e + 241]`: it spans 196 ps (197 grid
steps) and starts 45 ps AFTER the clock edge. -/
theorem regFF_d_window (c : XCorner) (rv : Bool) (res : Nat) :
    (regFF c rv res).dHi - (regFF c rv res).dLo = 196 ∧ (regFF c rv res).dLo = 45 := by
  cases c <;> cases rv <;> decide

/-- The prjxray flop is non-vacuous at every corner. -/
theorem regFF_inhabited (c : XCorner) (async rv init : Bool) (res : Nat) (ck : Substrate.Sig)
    (r ce d : Substrate.KSig) : ∃ q, FlopRel (regFF c rv res) async rv init ck r ce d q :=
  flopRel_inhabited _ async rv init ck r ce d (regFF_ok c rv res)

/-- **H_WINDOW_SLOW_ONLY bites at the fast corner.** With the slow-only D hold (241 ps) and
the fast CK->Q minimum (112 ps), a flop feeding a flop on the same clock edge at zero wire
delay would violate hold (its D moves at `e + 112`, inside `[e + 45, e + 241]`); at the slow
corner it would not (`274 > 241`). So either fast-corner holds are shorter than the slow
ones (likely, not in the database) or every such pair needs ≥ 130 ps of wire. -/
theorem fast_hold_mismatch (res : Nat) :
    ((regFF .fast false res).cqLo : Int) < (regFF .fast false res).dHi ∧
      (regFF .slow false res).dHi < ((regFF .slow false res).cqLo : Int) := by decide

end Formal.Core.Prims.Seq
