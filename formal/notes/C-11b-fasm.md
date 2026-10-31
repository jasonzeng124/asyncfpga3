# C-11b: netlist import from the ROUTED design (FASM / bitstream)

Track 11, probe b. Shard C. 2026-10-27.

## Verdict

**Works** for LUT-only designs (the C-element / latch / link cells, whose
logic is all LUT6 with feedback through the fabric). The physical LUT netlist
is read from the bits (FASM, or the FASM disassembled from the `.bit`), with
the placer's pin permutation and every pip, and Lean proves by `decide` that
it computes the logical cell's next-state function. **Works with effort ~2-3
weeks** for whole shipped designs (FFs, carry, F7/F8, DSP, clocking; see
"Effort"). Pip-level timing per corner is recoverable from prjxray-db except
where noted.

## What checks (run it)

    formal/tools/fasm2lean/check.sh           # ~1 min, from committed fixtures
    formal/tools/fasm2lean/route.sh SEED      # re-route one seed (~10 s), then check.sh

`check.sh` (last run: PASS):
1. seeds 1..4: the netlist extracted from nextpnr's FASM and from the FASM
   read back from the `.bit` (xc7frames2bit -> bitread -> prjxray bit2fasm)
   are identical (same sites, INITs, pin sources); the Lean data
   `Formal/Net/Fasm/CePairS<n>.lean` is generated from the read-back one.
2. compiles `Formal/Net/Fasm/{Basic,CePairS1..4,CePair}.lean` (core Lean, no
   Mathlib, ~4 s), scan.py clean, every theorem below depends only on
   `propext` (+ `Quot.sound` for the trace ones).
3. negative controls injected in the BITS (FASM features), extracted the
   same way into `Wip/C11b/`: one INIT bit cleared -> `¬ Spec` proved by
   decide; two INT pips re-pointed (b and rst swapped on pins B2/B3, both
   legal pips) -> `¬ Spec` proved; a second driver on a node (short) ->
   fasm2lean refuses the FASM.

Design: `formal/tools/fasm2lean/ce_pair.v`: `q1 = bd_c2(a, b, rst)`,
`q2 = bd_c2n(q1, c, rst)`, cells verbatim from `cells/rtl/bd_ce.v` (no
`.fasm` of a small design was in the repo; `cloud/fixtures` only has the
frontend). Flow = `cells/flow.sh`'s synth/pnr options plus `--freq 100` and
`--seed N`; `cells/verify/toolchain.sh` 9/9 ok, **nextpnr sha256
9c732bc6303458df**, `fasm_audit.py` PASS on every seed. Each seed placed the
two LUTs differently with a different physical pin order (e.g. seed 1 q1 =
BLUT of SLICE_X42Y95 with B1..B4 = q1, rst, b, a; seed 3 q1 has a, b, rst on
A3, A4, A5), so the theorem is checked against 4 genuinely different routes.

## Theorems (Formal/Net/Fasm/CePair.lean)

| name | statement |
|---|---|
| `next_state_s1..s4` | `Spec net ports`: for all 64 values of a, b, c, rst, q1, q2, the LUT the bits wire to port q1 is driven to `exc INIT_c2 a b q1 rst` and the one wired to q2 to `exc INIT_c2n q1 c q2 rst` (shard B's `exc`, RTL INITs). Stated by port NAME only: the same text for every seed. |
| `next_state_s1_bool` | the same as `~rst · maj(a,b,q1)` (via B's `c2_eq`) |
| `perm_matters_s1` | negative control: the logical INIT on the physical pins (no re-encoding: the lut-pinmap bug family) fails `Spec` |
| `swap_caught_s1` | negative control: two pin sources swapped fails `Spec` |
| `q1_loop_s1` | from the physical gate relations `Behaves` (H_LUT, H_ROUTE, H_TIE), the routed q1 LUT with its ROUTED feedback pin is shard B's `Loop INIT_c2` |
| `q1_follow_hold_s1` | B's `c2_follow_hold` for the routed cell |
| `q1_follow_hold_s1_ps` | the same with numbers: LUT [45, 124] ps, feedback route [213, 709] ps from the generated `pinDelay` (rfl-linked): inputs held 833 ps set the routed C-element |
| `q1_kleene_s1` | in B's Kleene `lutK` (X on any live pin), physical q1 LUT = logical bd_c2 LUT (81 cases) |

Open goals: none of the above is open. Not attempted: `Spec`-style
equivalence for a whole shipped design (see Effort).

## The tool: formal/tools/fasm2lean/fasm2lean.py

Inputs: a FASM, the XDC (only to name IOB sites via `package_pins.csv`), and
prjxray-db (`tilegrid.json`, `tileconn.json`, `tile_type_*.json`,
`ppips_*.db`). It does NOT read nextpnr's routed JSON, SDF, or yosys.
- LUT sites = `*.?LUT.INIT` features; INIT is physical (address A6..A1, A1 =
  bit 0), read as written (bit2fasm writes `INIT[61:0]` with leading zeros
  dropped; handled).
- Per physical pin, walks backwards over active pips through prjxray's
  wire -> node connectivity (tileconn) until a site output (SLICE A..D /
  ?MUX via `?OUTMUX.O6|O5`, IOB `I`) or a tie (`GND_WIRE`/`VCC_WIRE`).
- Checks: two active drivers on one node (short) -> exit 1; no driver
  (floating) -> exit 1; unmodelled source (FF Q, carry, F7/F8, other OUTMUX)
  -> exit 1; active pips not on any traced path are listed (0 here).
- **Implicit pips** (hypothesis H_IMPLICIT): pips with no config bits are
  never printed by bit2fasm: ppips `always`/`default` (CLB IMUX -> A1..A6,
  LOGIC_OUTS, IO_INT_INTERFACE, INT BYP_ALT -> BYP_BOUNCE, IOI I0/IBUF), and
  the tile json's pseudo pips (ILOGIC D -> O bypass). They are taken only for
  a node with no active pip and when exactly one candidate's source is driven;
  the ILOGIC D/DDLY choice is decided by the site feature `IDELMUXE3.P1`
  (direct) / `P0` (idelay) (prjxray `fuzzers/035-iob-ilogic/generate.py`).
  `ppips ... hint` (LUT route-throughs) are not taken. Test: the read-back
  netlist equals nextpnr's FASM netlist on 4 seeds (nextpnr prints most of
  these pips); a bitstream with a LUT route-through would currently fail loud.
- IOB naming: FASM `IOB_Y<k>` = site `Y % 2` (prjxray
  `fuzzers/030-iob/check_results.py`), cross-checked against IN/DRIVE features.
- Timing per pin (JSON + Lean `pinDelay`): every pip with prjxray's 4-corner
  intrinsic delay [fast_min fast_max slow_min slow_max], drive R, in C,
  pass/buffered flag; site-pin delays; an Elmore term per sink (timing.py's
  model lumped per node: driver R x (node C + loads), wire R x (C/2 + loads),
  loads = in_cap of every pip that is on and leaves the node, fanout
  included; units R[ohm]*C[fF]*1e-3 = ps per prjxray tile.py factors).
  `pinDelay = (sum fast_min, sum slow_max + ceil Elmore)`.

## What can and cannot be recovered

Recovered from the bits + prjxray-db, verified on 4 seeds:
- every used LUT's physical INIT and physical pin -> source map (= the netlist
  the board runs, routing included);
- every pip on every LUT input route and output route (~30-35 pips here);
- per pip: intrinsic delay at fast/slow x min/max, R, C; per site pin: delay;
  per node: wire R/C; per net: fanout loads.

Not recovered / not in the data:
- **Rise vs fall**: prjxray pips and site pins carry one delay per corner, no
  rise/fall split (cell arcs in `timings/*.sdf` have fast/slow, also no
  rise/fall: the two SDF triples are fast and slow, not rise and fall).
- **The pass-transistor distinction carries no timing.** In zynq7 prjxray-db
  all 20211 pips that have a delay are buffered; all 18762 pips marked
  `is_pass_transistor` have no delay and R = 0 (CLB/IOI fixed connections).
  So PROGRAM.md's "buffered vs pass-transistor pips" is, with this db, "every
  routing pip is a buffer"; a pass-transistor RC model has nothing to use.
- **RC per corner**: R and C are single numbers; only intrinsic delays vary by
  corner. Within-die variation, temperature, this die's position in the band:
  not in the data (that is the ring data's job).
- **Speed grade**: not stated in the db files I read (`part.yaml`,
  `timings/*.sdf` headers); the board is -1. To be checked (PROGRAM.md).
- The Elmore term is NOT cross-checked against `prjxray/timing.py` or
  claude/research's delay calculator (F1, not in this tree). Its size here
  (24-140 ps per pin) is plausible but unvalidated: `pinDelay`'s upper ends are
  candidates, and `q1_follow_hold_s1_ps` takes them as hypothesis `H_DW`.
- nextpnr's SDF for comparison (fixture `*.sdf`): it gives one number per arc
  (feedback B1 295 ps, inside [213, 709]; LUT IOPATH a flat 124 ps for every
  pin), while prjxray gives per-pin site delays from A6 0.007-0.016 ns to A1
  0.180-0.531 ns: **which physical pin the placer chose moves a cell's delay
  by up to ~0.5 ns at slow max**, and nextpnr's SDF does not show it (its
  lut-perm-sink patch fixes the interconnect part only).
- An all-zero LUT writes no INIT feature: invisible (a reader of it fails loud).

## Fidelity of every primitive model used

- **LUT**: shard B's `lutB`/`o6B`/`o5B` on the physical INIT and physical pin
  order (binary), and `lutK` (Kleene, H_KLEENE_LUT). The mux-tree order is
  irrelevant to `lutK` (B's `muxTree_eq_cloN`), so the physical permutation
  cannot change X behaviour in that model; it could in a model with
  per-level mux delays (A6 is the tree root electrically: fastest pin).
- **LUT delay**: window channel [45, 124] ps (prjxray LUT6 arc fast_min /
  slow_max), hypothesis H_LUT / H_DL, as B's `Loop.H_LUT`.
- **Routing**: every pin has its own trace, a window-channel copy of its source
  (H_ROUTE, per sink, so fanout branches differ). Faithful to "buffered pips +
  wires" as a bounded delay; it does not model glitch filtering or pulse
  shrinking along a route (involution channels would).
- **Ties**: constant (H_TIE); the tool proves the tie node has one driver.
- **IOB/ILOGIC**: an input port is the IOB `I` pin; ILOGIC is a combinational
  bypass when `IDELMUXE3.P1` (H_IMPLICIT). IBUF/OBUF delays not modelled here.
- Not modelled: FFs, carry, F7/F8, LUTRAM/SRL, DSP, BRAM, clocks.

## Effort to finish (estimates)

- FFs (Q as source, D/CE/SR/CLK as sinks, `ZINI`/`ZRST`/SR polarity
  features), F7/F8, carry (CARRY4 CO/O, DI/S): 3-5 days; the walk is generic,
  the work is the site-internal muxes (`?FFMUX`, `?OUTMUX`, `CEUSEDMUX`...),
  each a small table like `SITE_MUX`.
- DSP48E1 pins + attributes (fasm_audit.py already decodes the bug-prone
  ones), clock tree (BUFG/HCLK/GCLK pips), IOB/IOI attributes: 1 week.
- Whole-design equivalence against yosys: map yosys cells to sites using the
  routed JSON only as a HINT, then prove per LUT `fn(physical pins) =
  cell fn(logical pins)` under the net bijection the bits give (decide, 64
  cases per LUT; ~1-2k LUTs in gcd_hw: estimate minutes of kernel time). A
  structural per-LUT check suffices for sequential/feedback designs. 3-5 days.
- Feed the same netlist to the board-fidelity GLS (research F2) instead of
  nextpnr's JSON: the extractor's JSON already has the pins, pips and RC data
  a Verilog writer needs; ~2 days to emit Verilog with per-sink delays.
Total for whole shipped designs: ~2-3 weeks.

## What it buys the project

A proof about the netlist the board runs, not the one yosys/nextpnr claim:
the lut-pinmap class (INIT re-encoded for the wrong pin) and a mis-routed pin
(MutPips: the netlist, the routed JSON's X_ORIG_PORT map and therefore
`fasm_audit.py` would all still agree) are caught by `decide`. `fasm_audit.py`
checks INIT against nextpnr's own pin map; this checks the pins against the
pips. And B's cell theorems now apply to the routed instance, with the
feedback-route bound taken from the actual route.

## Non-vacuity (added by aud2, 2026-10-29)

The tree has no witness for `q1_follow_hold_s1_ps`. The audit's (C2.md 2d,
`Fasm_audit.lean::audit_behaves_witness`) discharges every hypothesis, but with constant-false
traces: it shows the hypotheses are consistent, not that the routed C-element ever switches. A
witness where an 833 ps input pulse actually sets q1 is open.

## Surprises / notes for the lead

- The sandbox was missing `libboost_python312/filesystem/program_options 1.83`
  (nextpnr would not start): installed with apt. prjxray Python needed
  `simplejson textx intervaltree`: installed with `python3 -m pip` (pip3 is a
  different interpreter here, as research/JOURNAL.md 2026-10-25 says).
- `xc7frames2bit` output is NOT byte-reproducible: two runs on the same FASM
  differ in 4 bytes at offset ~149 (header timestamp). CLAUDE.md's "compare
  the bitstreams with cmp" will report a difference on identical routes;
  compare FASM or frames (both reproducible here) or skip the header.
- `cells/flow.sh` passes no `--freq` (its designs have no clock, and its
  comment says neither router is timing-driven there; `build_hw.sh` adds it
  only with NEXTPNR_FREQ). route.sh passes `--freq 100` as CLAUDE.md asks.
- Lean 4.35 structure-instance syntax: `{ a := x,\n  b := y }` with the
  comma at end of line fails to parse here; the generator emits `⟨...⟩`.
- Built B's `Formal/Cells/CElemTiming.olean` (it was not built) to import it;
  B's source is untouched.
