# A-prims-seq: digital semantics of the sequential primitives (FDRE/FDSE/FDCE/FDPE, LDCE/LDPE)

Probe PrimsSeq, shard A. Started 2026-10-28 (session died, draft in
`Wip/_snapA/Formal/Core/Prims/SeqNext.lean`); redone 2026-10-29 from 07:20 UTC.
North-star goal 1 ("the flops and latches, DSP48E1 and RAMB18E1 if a design uses them").

STATUS: done for flops and latches (6 Mathlib-free files, check.sh OK 08:34 UTC, §7). RAMB18E1 not modelled (next probe).

## Plan
1. `Formal/Core/Prims/SeqNext.lean`: next-state functions, exact Kleene extension,
   GLS SLICE_FFX next-state counterexamples (recovered draft, re-checked).
2. `Formal/Core/Prims/SeqXray.lean`: the prjxray-db numbers (CK->Q, SR->Q, D->Q, setup/hold,
   recovery/removal) as data, in integer ps, one corner per band.
3. `Formal/Core/Prims/SeqFlop.lean`: the timed flop as a relation on Core substrate signals
   (`Substrate.Sig`/`KSig`, 1 ps grid): aperture sampling, CK->Q band, bounded-X resolution,
   INIT, async CLR/PRE; theorems: capture, X-containment, priority, GLS trace counterexample.
4. `Formal/Core/Prims/SeqLatch.lean`: LDCE/LDPE: transparency, hold, closing-edge window.
5. (added) `SeqGls.lean` (GLS trace counterexample), `SeqSync.lean` (two-flop synchronizer).

## 1. Census: which sequential primitives the designs use

Sources read: `cells/rtl/*.v` (frozen library), `bdc/*.py` (the emitter), `cells/hw/*.v`
(board harnesses / rigs), the routed2x reports of the gcd_hw R5 routes
(`formal/tools-A/xaudit/gcd/inputs/routed2x_*_*.txt`), research `cells/gls/gen.py`.

| primitive | where | in an async datapath? |
|---|---|---|
| FDRE | `bd_mlink.v:141` (`bd_flink` bank, `always @(posedge ck)`: CE=1, R=0); gcd_hw rig (`cells/hw/gcd_hw.v`, 15 `always @(posedge ...)` blocks: hk/abs/cmp/lap/tck domains, 2-flop sampler `rs0/rs1`); `arb_mtbf.v` | gcd_hw core (`urig.udut`): **none** (routed2x kept 9764 cells: LUT, MUXF7/8, CARRY4 only); rig flops drive `idx[0..3]` into the core (free inputs = SLICE_FFX Q) and sample its outputs. `bd_flink` is not emitted by `bdc/emit.py` (no reference) |
| FDSE | gcd_hw rig (`rst_sr = 16'hFFFF`, power-up 1; research gen.py: "20 of the 247 flops here are FDSE"); `arb_mtbf.v` | no |
| FDCE / FDPE | none in any design (only C's test `formal/tools/gen/test/prims.v`) | no |
| LDCE / LDPE | none in any design. `bd_latch.v:11-21` says why storage is on LUTs, not the slice LDCE (LDCE.G sits on the slice clock pin) | no |
| DSP48E1 | ipow (`bdc` infers `*` with BD_DSP=1, default; `cells/flow.sh`), `cells/hw/mult*_ps.v` | ipow's DSPs are **combinational** (AREG=0, `flow.sh`: "-DBD_KEEP_OPERANDS ... AREG=0 -- the configuration kernels/ipow produces"). Registered DSP (AREG=1) only in the board test `mult_ps.v`. So not a sequential primitive of any design here: out of this probe (combinational; PrimsComb or a later probe) |
| RAMB18E1 | `bd_mem.v` (one RAMB18E1 x18, CLKARDCLK = buffered request, DOA_REG=0), memory kernels via `bdc/mem.py`; `cells/hw/mem_*_ps.v` | yes, in memory kernels (not gcd_hw). Not modelled here (time box); C's importer makes it OPAQUE. Suggested next probe |

So for gcd_hw the flops matter only at the rig boundary (inputs `idx`, `rig_rst`, and the rig's
samplers of async outputs: exactly the setup/hold-violation case). The `rig_rst` net is cut in
the audit (`--cut-net rig_rst`).

## 2. prjxray-db data (zynq7 `timings/slicel.sdf`, toolchain copy)

Integer ps, `(FAST_MIN..FAST_MAX) / (SLOW_MIN..SLOW_MAX)` for IOPATHs; timing checks have
ONE pair (see below).

| bel (prjxray cell) | arc | fast | slow |
|---|---|---|---|
| AFF..DFF `REG_INIT_FF` | CLK->Q | 112..139 | 274..340 |
| | SETUP / HOLD DIN | – | -55..-45 / 194..241 |
| | SETUP / HOLD CE | – | 88..109 / -11..-9 |
| `REG_INIT_FF_QL` (SR->0) | SR->Q | 246..306 | 662..821 |
| | RECOVERY / REMOVAL SR | – | 326..404 / -305..-248 |
| `REG_INIT_FF_QH` (SR->1) | SR->Q | 195..243 | 476..591 |
| | RECOVERY SR | – | 288..358 |
| A5FF..D5FF `FF_INIT` | CLK->Q | 99..124 | 244..303 |
| | SETUP / HOLD DIN | – | -57..-46 / 181..225 |
| `FF_INIT_QL` / `_QH` | SR->Q | 233..290 / 182..227 | 616..764 / 445..552 |
| latch `REG_INIT_LAT` | CLK->Q, CE->Q, D->Q | 129..160, 130..162, 73..92 | 357..443, 409..507, 213..264 |
| | SETUP / HOLD DIN | – | -68..-56 / 194..241 |
| `REG_INIT_LAT_QL` / `_QH` | SR->Q | 198..246 / 164..204 | 638..791 / 487..604 |

Findings from the data itself:
- **The shipped database has no fast-corner setup/hold/recovery/removal.**
  `prjxray/utils/makesdf.py` writes `({SLOW_MIN}::{SLOW_MAX})` for every TIMINGCHECK, while
  IOPATHs get both corners. So a fast-corner analysis has no aperture data; `SeqXray` uses
  the slow window at both corners (**H_WINDOW_SLOW_ONLY**, untested).
- The D setup is **negative**: the D window is `[e+45, e+241]` (AFF) / `[e+46, e+225]` (5FF)
  after the clock edge at the bel. CE's is before it: `[e-109, e-9]`. SR: `[e-404, e-248]`
  (to 0) / `[e-358, e-248]` (to 1).
- No rise/fall split anywhere (one band per arc, both edges).
- QL/QH = SR polarity (prjxray `tim2json.py`: "Q[LH] ... suffix determines polarity of the
  FF's set/reset input"). SR to 0 is the slower arc.
- For a sync R/S prjxray lists only RECOVERY/REMOVAL on SR, no SETUP/HOLD: used as the R/S
  window (**H_SR_SYNC_WINDOW**).
- Conservative ends: `lo = -SETUP_MAX`, `hi = HOLD_MAX` (a wider window only adds X).

## 3. The model (Lean)

Files (all Mathlib-free, on `Formal.Core.Substrate.Chan`'s `Sig`/`KSig`, 1 ps grid):
- `Formal/Core/Prims/SeqNext.lean` — next-state functions `bnext`/`knext` (R beats CE),
  exact Kleene extension (`knext_exact`, `sound_iff_le_knext`), GLS next-state `glsNext`
  and `gls_unsound`, `gls_hides_X_R`, `gls_hides_X_CE`.
- `Formal/Core/Prims/SeqFlop.lean` — `FlopRel` (the flop as a trace relation), its theorems,
  and the non-vacuity witness `sim`/`sim_rel`.
- `Formal/Core/Prims/SeqLatch.lean` — `LatchRel`, theorems, witness `lsim`/`lsim_rel`.
- `Formal/Core/Prims/SeqXray.lean` — prjxray instances `regFF`, `ff5`, `lat` (corner, SR
  polarity, `res`), well-formedness.
- `Formal/Core/Prims/SeqGls.lean` — the GLS `SLICE_FFX` as a relation (`GlsRel`) and the
  trace counterexample.

### What a setup/hold violation does (decision)
**Both, layered: X for a bounded window, then a definite nondeterministic binary value.**
At an edge `e` each input is read over its window (`ap`, the K3 meet over the window: its
value if constant, else X); the next state is `knext` of those reads. If it is X (a
violation that matters, or an X on CE/R that matters), Q is X on `(e+cqLo, e+cqHi+res]` and
from then on ONE binary value `b`, chosen by nobody (∃ b, held until the next edge).
Why: inside the window a digital model cannot say what the output does (runt, late edge,
oscillation), and K3 X is exactly "any binary waveform" (`Covers`); after it the node is a
storage node again with one value, but no digital fact decides which. `res` is
**H_FF_RESOLVE**, a named parameter (no MTBF, no analog). A violation that does not matter
(e.g. D moves while CE = 0) gives no X, because `knext` is the exact Kleene extension.

### Hypotheses named in the model
H_GRID (1 ps), H_CK_BINARY (clock binary, no runt/X; no min-pulse-width check), H_FF_PINREF
(windows at the bel pins, prjxray routing-bel hops are routing), H_FF_RESOLVE /
H_LAT_RESOLVE, H_GSR (time 0 = GSR release), H_WINDOW_SLOW_ONLY, H_SR_SYNC_WINDOW,
H_LAT_GATE (G and GE folded into one gate signal and band), H_LAT_WINDOW (latch closing
window `[c-264, c+241]` = D->Q slow max before, hold after).

## 4. Results (problem statements)

Each item: assumed / proved / not covered. All in `Formal.Core.Prims.Seq`.

**Flop relation `FlopRel T async rv init ck r ce d q`** (SeqFlop). One corner `T`; a binary
clock; K3 inputs and output. Rules: INIT before the first edge; per edge `e`, the aperture
reads and `knext`; old value up to `e+cqLo`, `merge old new` in the band, new value after
`cqHi` if definite, X up to `cqHi+res` and then ∃ one binary value if not; for FDCE/FDPE,
CLR/PRE held `sqHi` ⇒ `rv`, clean release ⇒ `rv` until a later edge; clocked rules apply
only while CLR/PRE stays low after the edge's window.
- `capture` — assumed: D = v on `[e+dLo, e+dHi]`, CE = 1 and R = 0 on their windows, no
  edge in `(e,t)`, `T.Ok`. Proved: Q = v at every `t > e + cqHi` until the next edge.
- `capture_hold` (CE = 0 keeps a definite state through the band), `capture_reset`
  (R/CLR = 1 on its window ⇒ `rv`, whatever CE and D).
- `x_contained` — assumed: only the relation. Proved: for every edge, ∃ b, Q = b on
  `(e+cqHi+res, next edge)` (and, for FDCE/FDPE, while CLR/PRE stays low). Whatever the
  inputs did: violations, X on CE/R, an X old state.
- `x_only_in_window` — a definite state at the edge can only be X inside `(e+cqLo, e+cqHi+res]`.
- `violation_X` — D takes two values inside its window, CE = 1, R = 0 cleanly ⇒ Q = X on
  all of `(e+cqLo, e+cqHi+res]` (the model is not optimistic about violations).
- `power_up` (INIT), `clr_priority` (CLR/PRE held `sqHi` ⇒ `rv`, regardless of the clock).
- `sim_rel` / `flopRel_inhabited` — **non-vacuity**: for every input and every `T.Ok`
  timing there is an output satisfying all rules (an explicit, recursively defined
  behaviour; the CLR/PRE rules and the clocked rules are proved mutually exclusive, which
  needs removal ≤ 0). So no theorem above is vacuous.
- NOT covered: the clock's own runts/X/min pulse width; how long resolution takes (`res`
  is a parameter); after a CLR runt or a CLR change inside a window the output is
  unconstrained until the next clean edge (weaker than silicon, sound); no rise/fall split.

**Latch relation `LatchRel T rv init g d clr q`** (SeqLatch).
- `latch_transparent`, `latch_transparent_le` — open (gate 1, CLR 0 for `M` ps) ⇒ Q = D's
  value over `[t-dqHi, t-dqLo]`; Q refines D at every step of that window (the K3 `Win`).
- `latch_hold` — clean close at `c`, D = v on `[c+hLo, c+hHi]` ⇒ Q = v while closed.
- `latch_x_contained`, `latch_violation_X` — bounded X then one definite value; a D change
  inside the closing window gives X up to `xend c`.
- `latch_clr_priority`, `latch_power_up`, `lsim_rel`/`latchRel_inhabited` (non-vacuity).
- NOT covered: G and GE as separate pins (H_LAT_GATE); a glitch/X on the gate leaves Q
  unconstrained until the latch reopens (no bounded containment without a clean close).

**prjxray instances** (SeqXray): `regFF`, `ff5`, `lat` at both corners, any `res`; `*_ok`,
`regFF_inhabited`. `fast_hold_mismatch`: with the slow-only hold (241) and the fast CK->Q min
(112), a same-edge flop-to-flop path at zero wire delay violates hold at the fast corner and
not at the slow one. Either fast holds are shorter (likely; not in the database) or every
such path needs ≥ 130 ps of wire. This is a consequence of H_WINDOW_SLOW_ONLY, not of silicon.

**Two-flop synchronizer** (SeqSync `sync_two_flop`). Assumed: two flops on one clock, flop 1
reads flop 0 through a fixed wire `w`; flop 1's CE = 1/R = 0 cleanly at `e'`; no edge in
`(e,e')` or `(e', e'+cqLo]`; `e+cqHi+res < e'`, `e+cqHi+res+w < e'+dLo`, `dHi ≤ cqLo+w`.
Flop 0's D is arbitrary. Proved: flop 1's output after `e'+cqHi` is one definite value
until its next edge (no X at all at flop 1). NOT covered: an X lasting longer than `res`,
clock skew, variable wire delay.

**GLS counterexample** (SeqGls; SeqNext at the next-state level). The research default
`SLICE_FFX` (`cells/gls/prims.v`, `if (SR) ... else if (CE) Q <= D`) is modelled as `GlsRel`
on violation-free runs. `gls_vs_kleene_ce`: FDRE, INIT 0, R = 0, D = 1, CE = X, one edge at
1000 ps: a GLS run with Q = 0 at all times and no violation message exists; EVERY Kleene
run has Q = X at `1000 + cqHi`; and the completion CE = 1 gives Q = 1 (so the GLS's definite
0 is contradicted by a real behaviour). `gls_vs_kleene_sr`: FDSE, SR = X, CE = 1, D = 0: GLS 0,
Kleene X, completion SR = 1 gives 1. `gls_vs_kleene_prjxray`: at both prjxray corners. NOT
shown: that any design here drives X into a CE/SR pin; a GLS pass simply cannot exclude it.

## 5. Comparison with the research GLS (read-only, origin/claude/research)

| item | GLS default `SLICE_FFX` | GLS_FID | this model |
|---|---|---|---|
| X on CE/SR | read as 0 (else branch) | same | Kleene (`knext`): X where completions disagree |
| setup/hold violation | Q <= x, sticky until the next capture; checked only when TSU > 0, with one TSU/THD = max over the pins | old or new next state after an exponential tail (Gaussian noise), never X | X for `cqHi+res`, then ∃ one value |
| window | TSU/THD = max over pins from nextpnr SDF | aperture from the SDF SETUPHOLDs (50 up to 371 ps, audit r11) | prjxray per pin (D, CE, SR separately; slow only) |
| async CLR/PRE (FDCE/FDPE) | **not modelled** (`always @(posedge CK)` only; SR is sync) | same | modelled. No design here uses FDCE/FDPE, so no current impact |
| INIT | `initial Q = INIT`, x INIT read as 0 | same | INIT |
| latch X | pessimistic (L1-L3 x where Kleene gives 0) | same | gate as K3; hold/transparent rules |

## 6. Not done / next
- RAMB18E1 (used by bd_mem in memory kernels): not modelled; suggested next probe (sync
  read on CLKARDCLK = buffered request edge, DOA_REG = 0, WRITE_FIRST).
- DSP48E1: combinational in every kernel here (AREG = 0); belongs with the combinational
  primitives.
- A refinement theorem between the K3 relation and a binary nondeterministic flop (every
  binary run is covered by the K3 run) is stated in prose only.

## 7. Check

```
formal/check.sh Formal/Core/Prims/SeqNext.lean Formal/Core/Prims/SeqFlop.lean \
  Formal/Core/Prims/SeqLatch.lean Formal/Core/Prims/SeqXray.lean \
  Formal/Core/Prims/SeqGls.lean Formal/Core/Prims/SeqSync.lean
...
[audit] 845 declarations checked
[check] OK
```
(2026-10-29 08:34 UTC; per-file mode with `-DautoImplicit=false`; 845 = these files plus
their imports. SeqNext alone: 131. Remaining compiler output: deprecation warnings for
`if_pos`/`if_neg` only.) No Wip files (nothing left unproved). Not yet in `Formal.lean`
or `lake build`: the lead adds the six modules.
