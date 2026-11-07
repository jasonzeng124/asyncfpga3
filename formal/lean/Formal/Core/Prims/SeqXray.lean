import Formal.Core.Prims.SeqLatch
import Formal.Core.Prims.Xray

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

## SLICEM (added 2026-10-31, answering audit `53d5cc9` P10b: "windows are SLICEL-only")

The defs above (`regFF`, `ff5`, `lat`) are the SLICEL numbers. A SLICEM flop has a LONGER
D hold (`slicem.sdf` `REG_INIT_FF`: `HOLD DIN (0.211::0.262)` against SLICEL's 0.241), so
applying `regFF` to a SLICEM flop was on the unsafe side. `regFFM`/`ff5M`/`latM` are the
SLICEM numbers, transcribed by hand from prjxray-db master `zynq7/timings/slicem.sdf`
(fetched 2026-10-31; its SLICEL file reproduces every SLICEL number above, so it is the same
database as the toolchain's). `regFFAt`/`ff5At`/`latAt` select by `SiteType`; a statement
about a placed flop must use the site it is placed in (**H_FF_SITE**: the site type comes
from the routed netlist, not from this file). `regFFM`:
`CLK Q (0.118::0.147)(0.292::0.362)`, `SETUP DIN (-0.074::-0.06)`, `HOLD DIN (0.211::0.262)`,
`HOLD CE (-0.007::-0.005)`, `SETUP CE (0.088::0.109)`; `_QH`: `SR Q (0.197::0.245)(0.489::0.606)`,
`RECOVERY (0.314::0.389)`, `REMOVAL (-0.292::-0.238)`; `_QL`: `SR Q (0.247::0.308)(0.689::0.855)`,
`RECOVERY (0.279::0.347)`, `REMOVAL (-0.285::-0.232)`. `ff5M` (`FF_INIT`): `CLK Q
(0.102::0.127)(0.259::0.322)`, `SETUP DIN (-0.074::-0.06)`, `HOLD DIN (0.194::0.241)`, CE as
`regFFM`; `_QH`: `SR Q (0.184::0.229)(0.455::0.565)`, `RECOVERY (0.279::0.347)`, `REMOVAL
(-0.292::-0.238)`; `_QL`: `SR Q (0.233::0.29)(0.648::0.804)`, `RECOVERY (0.314::0.389)`,
`REMOVAL (-0.285::-0.232)`. `latM` (`REG_INIT_LAT`): `CE Q (0.129::0.161)(0.415::0.514)`,
`CLK Q (0.132::0.164)(0.378::0.469)`, `D Q (0.075::0.094)(0.214::0.265)`, `SETUP DIN
(-0.078::-0.064)`, `HOLD DIN (0.211::0.262)`; `_QH` `SR Q (0.161::0.201)(0.493::0.611)`; `_QL`
`SR Q (0.198::0.246)(0.645::0.8)`. (prjxray's SLICEM REG_INIT_FF lists the shorter
recovery under QL and the longer under QH, the reverse of SLICEL; transcribed as written.)
Not covered: the SLICEM LUTRAM/SRL write timing (no design here uses it as storage).
-/

namespace Formal.Core.Prims.Seq

/-- Process corner. -/
inductive XCorner where
  | fast
  | slow
  deriving DecidableEq, Repr

/-- The value at a corner: `cs c fast slow`. -/
def cs : XCorner → Nat → Nat → Nat
  | .fast, f, _ => f
  | .slow, _, s => s

/-- AFF..DFF (`REG_INIT_FF`); `rv` selects the QL (reset, `false`) or QH (set, `true`) arcs. -/
def regFF (c : XCorner) (rv : Bool) (res : Nat) : FFTiming :=
  { cqLo := cs c 112 274
    cqHi := cs c 139 340
    dLo := 45, dHi := 241
    ceLo := -109, ceHi := -9
    srLo := if rv then -358 else -404, srHi := -248
    sqLo := if rv then cs c 195 476 else cs c 246 662
    sqHi := if rv then cs c 243 591 else cs c 306 821
    res := res }

/-- A5FF..D5FF (`FF_INIT`). -/
def ff5 (c : XCorner) (rv : Bool) (res : Nat) : FFTiming :=
  { cqLo := cs c 99 244
    cqHi := cs c 124 303
    dLo := 46, dHi := 225
    ceLo := -109, ceHi := -9
    srLo := if rv then -358 else -404, srHi := -248
    sqLo := if rv then cs c 182 445 else cs c 233 616
    sqHi := if rv then cs c 227 552 else cs c 290 764
    res := res }

/-- LDCE (`rv = false`) / LDPE (`rv = true`), `REG_INIT_LAT`. The gate band is the wider
of CLK->Q and CE->Q (H_LAT_GATE); `hLo = -dqHi(slow) = -264` (H_LAT_WINDOW: it also covers
`-SETUP_MAX = +56`), `hHi = HOLD_MAX = 241`. -/
def lat (c : XCorner) (rv : Bool) (res : Nat) : LatTiming :=
  { gqLo := cs c 129 357
    gqHi := cs c 162 507
    dqLo := cs c 73 213
    dqHi := cs c 92 264
    hLo := -264, hHi := 241
    sqLo := if rv then cs c 164 487 else cs c 198 638
    sqHi := if rv then cs c 204 604 else cs c 246 791
    res := res }

/-- Every prjxray flop instance is well formed, so `sim_rel`/`capture` apply to it. -/
theorem regFF_ok (c : XCorner) (rv : Bool) (res : Nat) : (regFF c rv res).Ok := by
  cases c <;> cases rv <;> simp [regFF, cs, FFTiming.Ok]

theorem ff5_ok (c : XCorner) (rv : Bool) (res : Nat) : (ff5 c rv res).Ok := by
  cases c <;> cases rv <;> simp [ff5, cs, FFTiming.Ok]

/-- Bands are nonempty and ordered at both corners. -/
theorem regFF_bands (c : XCorner) (rv : Bool) (res : Nat) :
    (regFF c rv res).cqLo ≤ (regFF c rv res).cqHi ∧ (regFF c rv res).sqLo ≤ (regFF c rv res).sqHi := by
  cases c <;> cases rv <;> simp [regFF, cs]

theorem lat_bands (c : XCorner) (rv : Bool) (res : Nat) :
    (lat c rv res).dqLo ≤ (lat c rv res).dqHi ∧ (lat c rv res).hLo ≤ (lat c rv res).hHi ∧
      (lat c rv res).gqLo ≤ (lat c rv res).gqHi := by
  cases c <;> cases rv <;> simp [lat, cs]

/-- The D aperture of an AFF..DFF flop is `[e + 45, e + 241]`: it spans 196 ps (197 grid
steps) and starts 45 ps AFTER the clock edge. -/
theorem regFF_d_window (c : XCorner) (rv : Bool) (res : Nat) :
    (regFF c rv res).dHi - (regFF c rv res).dLo = 196 ∧ (regFF c rv res).dLo = 45 := by
  cases c <;> cases rv <;> simp [regFF, cs]

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
      (regFF .slow false res).dHi < ((regFF .slow false res).cqLo : Int) := by
  simp [regFF, cs]

/-! ### SLICEM -/

/-- AFF..DFF in a SLICEM (`slicem.sdf` `REG_INIT_FF`). -/
def regFFM (c : XCorner) (rv : Bool) (res : Nat) : FFTiming :=
  { cqLo := cs c 118 292
    cqHi := cs c 147 362
    dLo := 60, dHi := 262
    ceLo := -109, ceHi := -5
    srLo := if rv then -389 else -347, srHi := if rv then -238 else -232
    sqLo := if rv then cs c 197 489 else cs c 247 689
    sqHi := if rv then cs c 245 606 else cs c 308 855
    res := res }

/-- A5FF..D5FF in a SLICEM (`slicem.sdf` `FF_INIT`). -/
def ff5M (c : XCorner) (rv : Bool) (res : Nat) : FFTiming :=
  { cqLo := cs c 102 259
    cqHi := cs c 127 322
    dLo := 60, dHi := 241
    ceLo := -109, ceHi := -5
    srLo := if rv then -347 else -389, srHi := if rv then -238 else -232
    sqLo := if rv then cs c 184 455 else cs c 233 648
    sqHi := if rv then cs c 229 565 else cs c 290 804
    res := res }

/-- LDCE/LDPE in a SLICEM (`slicem.sdf` `REG_INIT_LAT`), same conventions as `lat`:
gate band = hull of CLK->Q and CE->Q, `hLo = -dqHi(slow) = -265` (covers `-SETUP_MAX = +64`). -/
def latM (c : XCorner) (rv : Bool) (res : Nat) : LatTiming :=
  { gqLo := cs c 129 378
    gqHi := cs c 164 514
    dqLo := cs c 75 214
    dqHi := cs c 94 265
    hLo := -265, hHi := 262
    sqLo := if rv then cs c 161 493 else cs c 198 645
    sqHi := if rv then cs c 201 611 else cs c 246 800
    res := res }

/-- Site-selected timing (H_FF_SITE: the site type is read from the placed netlist). -/
def regFFAt : Formal.Core.Prims.SiteType → XCorner → Bool → Nat → FFTiming
  | .slicel => regFF
  | .slicem => regFFM

def ff5At : Formal.Core.Prims.SiteType → XCorner → Bool → Nat → FFTiming
  | .slicel => ff5
  | .slicem => ff5M

def latAt : Formal.Core.Prims.SiteType → XCorner → Bool → Nat → LatTiming
  | .slicel => lat
  | .slicem => latM

theorem regFFM_ok (c : XCorner) (rv : Bool) (res : Nat) : (regFFM c rv res).Ok := by
  cases c <;> cases rv <;> simp [regFFM, cs, FFTiming.Ok]

theorem ff5M_ok (c : XCorner) (rv : Bool) (res : Nat) : (ff5M c rv res).Ok := by
  cases c <;> cases rv <;> simp [ff5M, cs, FFTiming.Ok]

theorem regFFAt_ok (s : Formal.Core.Prims.SiteType) (c : XCorner) (rv : Bool) (res : Nat) :
    (regFFAt s c rv res).Ok := by
  cases s
  · exact regFF_ok c rv res
  · exact regFFM_ok c rv res

theorem ff5At_ok (s : Formal.Core.Prims.SiteType) (c : XCorner) (rv : Bool) (res : Nat) :
    (ff5At s c rv res).Ok := by
  cases s
  · exact ff5_ok c rv res
  · exact ff5M_ok c rv res

theorem latM_bands (c : XCorner) (rv : Bool) (res : Nat) :
    (latM c rv res).dqLo ≤ (latM c rv res).dqHi ∧ (latM c rv res).hLo ≤ (latM c rv res).hHi ∧
      (latM c rv res).gqLo ≤ (latM c rv res).gqHi := by
  cases c <;> cases rv <;> simp [latM, cs]

/-- **The audit's point, as a theorem.** The SLICEM AFF..DFF and latch D holds (262 ps) are
longer than the SLICEL ones (241 ps), and neither D window contains the other (SLICEM starts
later, 60 against 45 ps). So the SLICEL window is not a safe stand-in for a SLICEM flop,
and a window valid for both sites must be the hull `[45, 262]`. -/
theorem slicem_hold_longer (c : XCorner) (rv : Bool) (res : Nat) :
    (regFF c rv res).dHi < (regFFM c rv res).dHi ∧ (lat c rv res).hHi < (latM c rv res).hHi ∧
      (regFF c rv res).dLo < (regFFM c rv res).dLo := by
  cases c <;> cases rv <;> simp [regFF, regFFM, lat, latM, cs]

/-- The SLICEM flop is non-vacuous at every corner. -/
theorem regFFM_inhabited (c : XCorner) (async rv init : Bool) (res : Nat) (ck : Substrate.Sig)
    (r ce d : Substrate.KSig) : ∃ q, FlopRel (regFFM c rv res) async rv init ck r ce d q :=
  flopRel_inhabited _ async rv init ck r ce d (regFFM_ok c rv res)

/-- H_WINDOW_SLOW_ONLY in a SLICEM: fast CK->Q min 118 lies inside the slow-only D window
`[60, 262]`, so a same-edge flop-to-flop pair needs >= 145 ps of wire; at the slow corner
`292 > 262`. -/
theorem fast_hold_mismatchM (res : Nat) :
    ((regFFM .fast false res).cqLo : Int) < (regFFM .fast false res).dHi ∧
      (regFFM .slow false res).dHi < ((regFFM .slow false res).cqLo : Int) := by
  simp [regFFM, cs]

end Formal.Core.Prims.Seq
