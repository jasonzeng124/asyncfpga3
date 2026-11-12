# A-events2pin: the per-pin own-feedback race checker (shard A)

Shard A, 2026-10-27. This closes open item 1 of `lean/Wip/Contradictions.lean` (X2,
`xevents2_pin`). The routed numbers below come from **nextpnr-xilinx sha256 9c732bc6303458df**:
`cells/verify/toolchain.sh` reported 9/9 fingerprints before every ring3/pipe3 build. The
gcd_hw R5 routed JSONs were rebuilt by the events5 probe and are md5-identical to
`tools-A/xaudit/gcd/inputs/builds.txt`. Delays are prjxray-db zynq7 (speed grade -1), computed by
`origin/claude/research:cells/gls/fid/xray_delay.py` (md5 99b10a6d).

## Verdict

**Works.**

- **Lean.** `xevents2pin` decides `Events2Strict.BackPin` on per-pin arcs. Its CLEAN verdict is
  an instance of `Events2PinMain.sound_pin`, which holds for **every per-pin behaviour of the
  parsed netlist**: each LUT reads each input pin through its own monotone warp, in that pin's
  own band. **H_ATOMIC_LUT is not used.** The netlist half that `Wip/Contradictions.lean` left
  open (a per-pin `toCircuit`) is `Events2PinDesign.design_behP`.
- **Tooling.** `pinbands.py` gives every logical LUT pin the band of the physical pin the placer
  put it on, so it respects the pin permutation. That band includes the pin's own prjxray
  site-pin delay. For every arc, the script checks this site-pin value against xray_delay's
  Inpin.
- **Measured.**
  - **What H_ATOMIC_LUT hides is the LUT's own pin-to-O band width.** It is 24 ps at slow, 11 ps
    at fast and 79 ps at mixed, and it is the same on every C-element of every design and seed
    (prjxray's LUT6 IOPATH rows are flat over A1..A6).
  - **The large per-pin skew lives in the site pins** (A1 up to 0.531 ns against A6 at 0.016
    ns). The existing atomic analyses already counted it, because xray_delay charges each
    site-pin delay to that pin's routed arc.
  - At one corner, every C-element pin of ring3, pipe3 and gcd_hw keeps a positive per-pin margin
    on all 4 seeds.
  - At the mixed corner, the per-pin check turns 1 to 4 more pins per gcd_hw seed to ≤ 0, on top
    of the races the atomic analysis already found.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events2PinDesign.lean` | new, **proved**. Per-pin netlist semantics and the link to `BehP` |
| `formal/lean/Formal/Core/XAudit/Events2Pin.lean` | new, **proved + executable main** (`xevents2pin`) |
| `formal/lean/Wip/Events2Pin.lean` | new, not built: one open shape (`gcd_pin`) and the open long-run certificates |
| `formal/tools-A/xaudit/pinbands.py` | new. Routed JSON + xray arcs → logical-order netlist + per-pin bands (and atomic bands for comparison) |
| `formal/tools-A/xaudit/pin/build.sh` | new. Routes ring3/pipe3 (toolchain.sh, fasm_audit, xray_delay) |
| `formal/tools-A/xaudit/pin/run.sh` | new. pinbands → xevents2pin, plus xevents2strict on the atomic bands, plus the negative control |
| `formal/tools-A/xaudit/pin/gcd.sh`, `gcdpin.py` | new. gcd_hw seeds d/3/4/5: events4 analysis → per-pin margins (untrusted) |
| `formal/tools-A/xaudit/pin/siteskew.py` | new. The site-pin term of every own-feedback LUT pin (untrusted report) |
| `formal/tools-A/xaudit/pin/results/` | outputs: `summary.txt`, `gcd_summary.txt`, `siteskew.txt`, and per design/seed/corner `*.pin.txt` (xevents2pin), `*.strict.txt` (xevents2strict, atomic), `*.pinbands.txt` |

`routed2x.py` and every other existing file are unchanged. `Events2Strict.lean` (the X2 probe's
file) is imported but not edited.

### Check

    cd /home/user/asyncfpga3/formal/lean && ../check.sh Formal/Core/XAudit/Events2Strict.lean \
        Formal/Core/XAudit/Events2PinDesign.lean Formal/Core/XAudit/Events2Pin.lean

Result: `[audit] 1195 declarations checked`, then the executable's own audit run with
`[audit] 1420 declarations checked`, and `[check] OK`. Wall time about 36 s.

- There is no sorry, admit, axiom, native_decide or bv_decide.
- Only deprecation warnings remain (`dif_pos`/`if_pos` names, as in `Events2Design`).
- `Events2Strict.lean` has to be listed first. It is not in lake's build yet, so its olean comes
  from `check.sh`'s overlay.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xevents2pin"
root = "Formal.Core.XAudit.Events2Pin"
```

Usage: `xevents2pin NETLIST.json --bands BANDS.json [--env LO:HI] [--top T] [--cap N]`. Until the
stanza exists, `pin/run.sh` runs it with `lean --run` on private oleans in
`/tmp/events2pin/olean`, through `slot.sh`. One run takes about 4 s.

### Reproduce

    formal/tools-A/xaudit/pin/build.sh ring3 1 2 3 4; formal/tools-A/xaudit/pin/build.sh pipe3 1 2 3 4
    formal/tools-A/xaudit/pin/run.sh        # ring3/pipe3 x 4 seeds x 3 corners + NEG
    formal/tools-A/xaudit/pin/gcd.sh        # gcd_hw seeds d 3 4 5 x 3 corners
    python3 -I formal/tools-A/xaudit/pin/siteskew.py <routed JSONs>

Environment for `build.sh`:
- `XRAY_DELAY=/tmp/events2pin/xray_delay.py`, written with
  `git show origin/claude/research:cells/gls/fid/xray_delay.py`.
- `PYLIB=<dir containing simplejson.py = "from json import *">:/tmp/gcdx/pylib` (intervaltree).

## 1. What is proved (Lean)

### `Events2PinDesign` (namespace `Formal.Core.XAudit.Events2Pin`)

- **`PinRel d pl g x`**, the per-pin gate relation.
  - The output at `t` is the INIT bit at the address formed by reading input index `i` at
    `f i t`.
  - Each `f i` is a monotone warp in the band `pl g i`. `pl : PinTab = GSpec → Nat → Nat × Nat`
    is the per-pin band table.
  - **`SatPin d pl x`**: every gate of the design satisfies `PinRel`.
- **`sat_pin_of_sat`**: every atomic behaviour (`Circuit.Sat`, one warp per gate) is a `SatPin`
  behaviour, provided each pin band contains its gate band. So the per-pin semantics only adds
  behaviours.
- **`OneOK`** (decidable): 1-input gates keep their own band.
  - `rel_of_pin1`: for such a gate, `PinRel` is the gate relation.
  - `chain_warp1` is `Events2.chain_warp` with hypotheses on 1-input gates only.
- **`lut_transport_pin`**: under `PinRel`, a recognised C-element LUT (`Recog2`, with the real
  INIT checked by `InitOK`) outputs `lutF` of:
  - input pin `p` read at `f p t`;
  - the feedback read at `f (ar j) t`;
  - the reset read at `f (ar j + 1) t`.
- **`pinsOf sm pl`** gives the stage `PinBands` from the table, using the bd_ce.v layout.
  **`PinOK`** (decidable) requires the pin arcs to be at least 1 step.
- **`design_behP`**: every `SatPin` behaviour of a recognised design is an
  `Events2Strict.BehP`, with bands `sm.bands` and `pinsOf sm pl`.
- **`design_safe_pin`**: under `BackPin`, every C-element output is `ph v (M t j)` at every time
  (`BehP.safe`), and `M` is monotone. It also gives **`cycle_le_pin`**: for every closed walk `w`,
  there are at most `wTok w` events in every window of `wLoP w` steps.
- `close`, `EnvOK`, `env_rel`, `env_pin`, `sat_pin_close`: the eager environment of `xevents2`
  as 1-input per-pin gates.
- `BandsOK` (decidable): no pin band is empty. The executable requires it, so `SatPin` is never
  vacuous for want of a warp (`shift_warp`).

### `Events2Pin` (namespace `Formal.Core.XAudit.Events2PinMain`, executable)

- **`sound_pin`** is what a CLEAN verdict means.
  - Hypotheses checked by the executable with compiled `decide`: `Recog2 (close d env) net sm`,
    `BackPin sm.bands (pinsOf sm pl) back`, `OneOK (close d env) pl`, `PinOK sm pl`, and
    `EnvOK` for every environment gate.
  - Modelling hypotheses:
    - `SatPin d pl x`, the per-pin semantics of every parsed gate;
    - `henv`, each handshake port answering its stage within its band;
    - `h0`;
    - reset high until `T`.
  - Conclusion: `M` exists, is monotone, every C-element output is `ph v (M t j)`, and the
    per-window bound holds.
- **`sound_pin_atomic`**: the old atomic behaviours are covered whenever the pin bands contain
  the gate bands.
- `BackPin` is `≤`, not strict. That is sound here: the per-pin model contains the stale-feedback
  behaviour of `Events2Strict.cx_unsafe`, and `BehP.safe` is proved for it. The strictness
  question of X2 disappears once the arcs are per-pin.

### Trusted

- The JSON parser (`Parse`).
- The pin-table reader (`readTable`/`splitPinKey`/`cellOfGate`).
- The recogniser and walk search, copied from `Events2MainStrict`.
- The printed numbers, including the atomic comparison margins. Those were cross-checked
  against `xevents2strict` on the same data (§3).
- The Lean compiler running the `Decidable` instances.

## 2. Tooling: where the per-pin delay is, and `pinbands.py`

### What routed2x.py already does (checked, not changed)

- **The physical pin is right.** nextpnr-xilinx's `fixupRouting` renames each LUT port after the
  tile pin the net actually arrived on (patches/README.md, lut-perm-sink). `X_ORIG_PORT_A<k>`
  records the logical input or inputs on that physical pin, and `fasm_audit.py` checks that
  record against the FASM. routed2x emits LUTs over the used physical pins in A1..A6 order, so
  its pin `I<i>` is a physical pin.
- **The site-pin delay is included, but not separated.**
  - xray_delay.py builds prjxray's RC tree with an `Inpin` leaf at the site pin the route
    entered. `sink_wire` follows the tile pin, which is the permuted one.
  - It adds that Inpin's intrinsic delay into the INTERCONNECT row, at all four corners. The TSV
    shows it in the column `inpin_smax_ps` (A1 516–540, A6 0).
  - So every routed arc in routed2x's bands already contains its own pin's site-pin delay, on
    both sides of the race. That includes the feedback arc.
- **The LUT is collapsed to one band.** It is `[min lo, max hi]` over that cell's IOPATH rows.
  For LUT6 O6 those rows are flat in prjxray-db (45/56/100/124 ps on every pin, seed d: 26,873
  rows), so nothing per-pin is lost there.
- **Consequence for xevents2.** routed2x's physical order breaks the bd_ce.v layout that
  `xevents2` recognises: the feedback is wherever the placer put it. So `xevents2` cannot run on
  routed2x output of a permuted C-element.

### pinbands.py (new)

- **Logical order.** It writes the LUT in LOGICAL pin order with the logical INIT. `InitOK` then
  recognises it, and recognition is a check that the order is right. Logical pin `l` gets the
  net and the delays of the physical pin `A<k>` with `l ∈ X_ORIG_PORT_A<k>`.
- **Band split.** For each pin:
  - `arcs` = the IC row minus the site-pin intrinsic of `A<k>` at the same corner column. This is
    exact: IC is the sum of intrinsics plus one RC term, and the Inpin has C = 0.
  - `pins` = site pin + IOPATH `A<k>`→O.
  - `sitepins` = the site pin alone.
  - `--atomic-bands` writes the routed2x convention: site pin inside the route, one LUT band.
- **Checks; the script stops if any fails.**
  - The prjxray SLOW_MAX site-pin value of the physical pin (read from `tile_type_*.json` via
    `tilegrid.json`) equals xray_delay's `inpin_smax_ps` on the same IC row. This held on every
    pin of every ring3/pipe3 build: 12 pins per ring3, 44 per pipe3.
  - The IC row is resolved by prjxray (flag `ok`), not nextpnr's number.
  - A logical input on no physical pin must not affect the INIT.
- **Scope.** LUT netlists (the xevents2 domain), IOB inputs as free ports. Any other cell
  stops it.
- **The permutation is real.** Of the logical→physical pin assignments, 12 of 18 are permuted in
  ring3 seed 1 and 37 of 50 in pipe3 seed 1 (`pin/results/*.pinbands.txt`). The own feedback
  lands on:
  - A1 (the slowest site pin, 0.516–0.531 ns slow max) in about 20 % of gcd_hw's 4,711
    own-feedback LUTs;
  - A5 in about 29 %;
  - never A6 (`siteskew.txt`).

## 3. Results

Each cell gives the min margin over all C-element pins, as **atomic → per-pin** (ps). The atomic
margin is Back with H_ATOMIC_LUT on the same prjxray data. The per-pin margin is BackPin.

- ring3/pipe3: xevents2pin. Its atomic number equals xevents2strict's on `--atomic-bands`; I
  compared them pin by pin on ring3 s1 indep.
- gcd_hw: events4 analysis plus the §4 correction (untrusted).
- Corners: slow `[SLOW_MIN, SLOW_MAX]`, fast `[FAST_MIN, FAST_MAX]`, mixed `[FAST_MIN, SLOW_MAX]`.
- Environment for pipe3 ports: an eager handshake partner answering within [1, 500] ps.

| design | corner | seed 1 / d | seed 2 / 3 | seed 3 / 4 | seed 4 / 5 | mean | per-pin skew eaten |
|---|---|---|---|---|---|---|---|
| ring3 | slow | 641 → 617 | 127 → 103 | 529 → 505 | 819 → 795 | 529 → 505 | 24 |
| ring3 | fast | 291 → 280 | 55 → 44 | 240 → 229 | 350 → 339 | 234 → 223 | 11 |
| ring3 | mixed | 11 → **−68** | −451 → −530 | −272 → −351 | 141 → 62 | −143 → −222 | 79 |
| pipe3 | slow | 219 → 195 | 104 → 80 | 370 → 346 | 556 → 532 | 312 → 288 | 24 |
| pipe3 | fast | 103 → 92 | 44 → 33 | 193 → 182 | 240 → 229 | 145 → 134 | 11 |
| pipe3 | mixed | −409 → −488 | −468 → −547 | −87 → −166 | −26 → −105 | −248 → −327 | 79 |
| gcd_hw R5 (d, 3, 4, 5) | slow | 961 → 937 | 772 → 748 | 779 → 755 | 210 → 186 | 681 → 657 | 24 |
| gcd_hw R5 | fast | 434 → 423 | 343 → 332 | 345 → 334 | 118 → 107 | 310 → 299 | 11 |
| gcd_hw R5 | mixed | −190 → −269 | −265 → −344 | −167 → −246 | −395 → −474 | −254 → −333 | 79 |

### Verdicts

- **ring3 and pipe3, one corner.** xevents2pin prints **CLEAN FOREVER** at slow and at fast on
  all 4 seeds (`sound_pin`), and xevents2strict agrees.
- **ring3 and pipe3, mixed corner.** **NOT PROVED** except ring3 seed 4. Ring3 seed 1 is the case
  that separates the two models: the atomic check is CLEAN (margin 11 ps, xevents2strict
  exit 0), and the per-pin check refuses.

### Pins with BackPin margin ≤ 0 (every one is at the mixed corner)

- **ring3.**
  - s1: u1 pin I0 ← u0 (−68; atomic 11, **new**).
  - s2: 3 pins (−530, −145, and −29 with atomic 50, **new**).
  - s3: 2 pins (−351, −187).
  - s4: none.
- **pipe3.**
  - s1: 4 pins (−488 … −267).
  - s2: 4 pins (−547 … −81).
  - s3: 1 pin (−166).
  - s4: 2 pins (−105, and −33 with atomic 46, **new**).
  - The −488/−547/−166/−105 pins are the `req_in`/`ack_out` port pins. They are evaluated with an
    environment that answers in 1 ps (the BOUNDARY line), so they measure the assumed environment
    as much as the route.
- **gcd_hw** (`pin/results/gcd_summary.txt`). Between 6 and 8 pins per seed. These are the
  pins with per-pin margin ≤ 0 and atomic margin > 0, listed by seed:
  - **d**: `ulink_n_trueResult_28 stage[2]` pins 0 and 1 (7 → −72, 20 → −59);
    `ucontrol_merge2.uarb1.ua2` pin 1 (26 → −53); `umux15.uya` pin 1 (53 → −26). The two known
    races `ulink_n_falseResult_41 stage[2]` (−190 → −269) and `ucontrol_merge4.uarb1.ua2`
    (−9 → −88) get worse.
  - **3**: `ulink_n_trueResult_28 stage[1]` pin 0 (44 → −35); `umux9.uj0` pin 1 (49 → −30).
  - **4**: `ulink_n_falseResult_55 stage[0]` pin 1 (43 → −36).
  - **5**: `ucontrol_merge12_f` pin 0 (6 → −73); `ulink_n_falseResult_91 stage[1]` pin 0
    (48 → −31).
  - Guarded-pin entry margins move by the same 79 ps. They were already negative at the mixed
    corner (events4).

### Negative control

`run.sh` makes the pin arc of ring3 s1 `u1.u/I2` (the own feedback) 2000 ps slower in the
`pins` table only. The atomic margin is unchanged at 641 ps, because the atomic model cannot see
it. xevents2pin reports `BackPin false`, 2 pins ≤ 0 with minimum −1383 ps, and **NOT PROVED**
(exit 1).

## 4. How much does per-pin skew eat?

The per-pin margin of pin `p` of stage `j` minus the atomic Back margin (both models with the site
pin counted once) is exactly

    BackPin − Back = loIO(p) − hiIO(feedback pin) + Σ_walk (loIO(pin) − loF)

where `IO` is the prjxray IOPATH row from that physical pin to O. `loF` is the minimum over the
LUT's pins, so the sum is ≥ 0. For LUT6 O6 every row is the same (45/56 fast, 100/124 slow), so
the change is **−(hiIO − loIO) = −24 ps slow, −11 ps fast, −79 ps mixed**, the same on every pin.
xevents2pin printed exactly that on all 24 ring3/pipe3 runs. For gcd, `gcdpin.py` applies the
bound `hiF − loF` of the stage LUT, which is exact for O6. All 784 real gcd stage pins have a
stage-LUT band width of 24/11/79.

So the cost of H_ATOMIC_LUT is small, and it is one number per corner:
- at one corner it is up to a quarter of the smallest margins (pipe3 seed 2 fast 44 → 33,
  ring3 seed 2 fast 55 → 44), and none goes to ≤ 0;
- at the mixed corner it is 79 ps, and that is enough to flip 1–4 pins per gcd seed.

**The site-pin part of the per-pin skew is large, but it was never hidden by H_ATOMIC_LUT.**
`siteskew.py` reports the term `s(p) = siteLo(p) − siteHi(feedback)` that the margin contains:

| | slow min / median / max (ps) | mixed min / median / max (ps) | pins with s(p) < 0 (slow) |
|---|---|---|---|
| ring3 (4 seeds, 6 pins each) | −418 … 308 (medians 55–226) | −479 … 61 | 0–2 of 6 |
| pipe3 (4 seeds, 24 pins each) | −429 … 308 (medians −5 to 112) | −493 … 61 | 9–12 of 24 |
| gcd_hw own-feedback LUTs (4 seeds, 13,522 pins each; latches included) | −468 … 308 (median 52–58) | −509 … 61 (median −172) | about 46 % |

- Both the atomic and the per-pin numbers above contain this term, because xray_delay puts it
  in the routed arc.
- **A delay model without site pins is wrong by `s(p)` on that pin.** nextpnr's SDF is such a
  model: a flat 124 ps LUT arc, no Inpin (C-11b, A-fidelity §7.2). Its error is up to −0.5 ns,
  i.e. optimistic, whenever the placer puts the feedback on A1/A2 and the input on A5/A6.
- Any race check fed from nextpnr's SDF rather than from xray_delay therefore needs the per-pin
  site delays. pinbands.py and xray_delay's IC rows both provide them.

## 5. Fidelity

| element | model | silicon | explicit hypothesis | how to test |
|---|---|---|---|---|
| LUT | per-pin transport (`PinRel`): each input index has its own monotone warp, band = site pin + IOPATH for that physical pin; output = INIT bit of the mixed-time address | a mux tree; each pin's select buffer and level give a pin-dependent delay; prjxray puts the pin dependence in the site pin, and the cell arc is flat | `SatPin` (H_PIN_FIFO, B's name): FIFO per pin, no inertial filtering, no runts | A-lut-tree's experiment: a ring through one LUT, rerouted onto each A_i. Routed GLS with per-pin transport delays (research F1) on `cx_unsafe`-shaped stimuli |
| own-feedback route + feedback pin | route warp `Q`, then pin warp `Fq` | the same | per-pin band from prjxray | as above |
| routes | transport in `[lo, hi]`, site pin removed and counted in the pin | buffered pips + RC, prjxray Elmore | per-arc band, one corner or mixed | ring scatter (research F3) |
| reset pin | its own warp, band from the table (default the gate band) | the same | released once (`hrst`) | — |
| environment (pipe3 ports) | eager partner, inverting/buffering channel within [1, 500] ps | the rig or the neighbour | `henv` | ports with a real sender |
| corners | slow/fast: every element in its one-corner band; mixed: each element independently anywhere in [FAST_MIN, SLOW_MAX] | one die at one point, plus local scatter | H_ONE_CORNER (slow/fast) or none (mixed) | A-fidelity's tracking hypothesis; the mixed corner is the sound-but-pessimistic bound |

- **What is still atomic.** The per-pin model takes every LUT input index separately. It still
  takes the output as the INIT of one address, i.e. no per-level mux-tree internal state, which
  is B's `muxTree` with per-level delays. Per-pin transport is the pure per-pin delay form
  (H_PIN_FIFO), which is A-lut-tree's channel form for a single pin change.
- **Discretisation.** `unit_ps` = 1, so the bands are exact integers in ps and `toSteps` loses
  nothing. `BackPin` with `≤` is sound in this model; no step-margin argument is needed.

## 6. What it buys, effort, and what is open

**What it buys.**
- X2's open item is closed. The C1 race gate can now be stated and checked as `BackPin` on
  routed per-pin data, with a kernel-checked meaning for every per-pin behaviour.
- The measurement shows exactly where the per-pin skew lives:
  - in the site pins, which were already counted when bands come from xray_delay, and are NOT
    counted in nextpnr's SDF;
  - in a flat LUT arc, which costs 24/11/79 ps.
- pinbands.py is the first exporter that keeps the bd_ce.v logical layout on a routed (permuted)
  design. Without it `xevents2*` cannot run on any routed C-element.

**Time.** About 3 h.

**Open (`Wip/Events2Pin.lean`).**
1. The long-run rate certificates (`UpCert`/`LoCert`) for `BehP`. The per-window bound is
   proved. About half a day.
2. gcd_hw has no kernel-checked per-pin verdict. Its control is outside the Events2 domain, and
   the Events4 integration `Beh4.safe` is itself open (A-events4, about 3.5 days). Once that
   exists, the per-pin version is the same change as here: `PinRel` per index in place of
   `toLGate_rel`. About 1 day. Until then the gcd numbers in §3 are untrusted analysis.
3. Exact per-pin IO rows for LUT6_2 O5 halves. They differ by a few ps per pin; `gcdpin.py`
   uses the safe bound `hiF − loF`. No gcd C-element is an O5 half: all 784 stage widths are
   flat.
