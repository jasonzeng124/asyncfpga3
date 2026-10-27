# `gls/fid/`: the netlist the board runs, built from its bitstream

`cells/gls/` simulates nextpnr's routed JSON, which is what the tool meant to
build. Three of the four worst bugs here were in the bitstream, where that JSON,
the SDF and every simulation were correct (`patches/README.md`). This directory
rebuilds the design from the `.bit` itself, decoded by prjxray, and runs the
unchanged `gls/` flow on the result.

```
cells/gls/fid/build_fid.sh  cells/build/hw/gcd_hw  WORK  [bit|fasm]   # ~2 min + compile
cells/gls/fid/run_fid.sh    WORK  [-j N]                              # 16 vectors
GATE=1 build_fid.sh ...  &&  (cd WORK && vvp gate.vvp)                 # ANNOTATE_DONE gate
```

| file | what it does |
|---|---|
| `fasm2net.py` | `.bit` (through prjxray `bit2fasm` + `bitread`) or FASM, plus prjxray-db, gives `fasm_routed.json` (nextpnr-shaped, so `gen.py` reads it unchanged), `fasm.sdf`, `routes.tsv`, `stubs.tsv`, `pipnames.tsv` and `report.txt` |
| `fasm_equiv.py` | compares the routed JSON with the bits: cell set, config, every pin's driver, every LUT's function over every input assignment, and every net's pip set |
| `inject_pinmap.py` | negative control: the lut-pinmap bug's mechanism applied to live LUT pins |
| `build_fid.sh`, `run_fid.sh` | the `gls/build.sh` and `gls/run.sh` equivalents |

## What comes from where

* **Connectivity and every LUT function come from the bits only.** Each sink
  pin is traced upstream through:
  - active pips (FASM `TILE.DST.SRC`; a bidirectional LV/LH pip takes its
    direction from the feature);
  - always-on ppips (`ppips_*.db` "always", which carry no bits);
  - tile-to-tile wire joins (`tileconn.json`);
  - the "default" ppip, where an IMUX, BYP_ALT or FAN_ALT with no pip set
    reads VCC.

  The trace stops at a decoded site output or at a tile VCC_WIRE/GND_WIRE.
  Two drivers on one node, an undriven node, or a route that ends at a site
  output nothing configured drives is an error.
* **Which bels exist is decided by the bits.** A LUT6 whose upper half is
  configured always exists. Any other bel exists only if something the bits
  configure reads it.
* **The routed JSON is used for names only.** The RTL net names that the
  testbenches watch are attached to the bits' nets by driver bel pin
  (`FASM2NET_ALIAS`). The SDF is re-keyed onto bel-named cells. If the bits say
  a sink has a different driver than the SDF arc, `report.txt` counts a
  DRIVER MISMATCH.
* **Refused rather than mis-simulated:** LATCH, CLKINV, asynchronous SR,
  LUTRAM/SRL, DSP/BRAM, OLOGIC in any mode other than D1 to OQ, and a BUFGCTRL
  that does not reduce to O = I0. Every configured feature the decoder did not
  consume is listed in `report.txt`. On gcd_hw that list is empty.

## Naming (the convention F1's prjxray SDF is to use)

| thing | name | example |
|---|---|---|
| cell | its bel, as nextpnr's `NEXTPNR_BEL` writes it | `SLICE_X22Y80/D6LUT`, `BUFGCTRL_X0Y16/BUFGCTRL`, `IOB_X0Y34/IOB33/OUTBUF` |
| constant driver | `$VCC` / `$GND` (pin `Y`) | |
| net | its driver, `<bel>/<pin>`; constants `$const1` / `$const0` | `SLICE_X21Y73/A6LUT/O6` |
| wire | prjxray **node** name, from `NodeModel`'s rule (`specific_node_wires`, then `node_pattern_wires`, else the node's first `TILE/WIRE`) | `INT_L_X16Y79/NR1BEG0` |
| pip | prjxray tile pip `TILE.DST.SRC`, the FASM feature string (`pipnames.tsv` maps the ROUTING form to it) | `INT_L_X16Y80.IMUX_L47.NN2END0` |
| site pin | `SITEWIRE/<site>/<physical site pin>` | `SITEWIRE/SLICE_X22Y80/D5` |

`ROUTING` on every net uses nextpnr's grammar exactly
(`dst;src->dst;1` triples). A delay calculator that reads nextpnr's ROUTING
therefore reads the board's route the same way, and so does `gen.py`'s
`GLS_SCATTER_MODE=wire`. One difference: a LUT sink here is the PHYSICAL pin
the bits use (`D5`). nextpnr writes the pre-permutation cell pin through a
pseudo pip (`CLBLL_LL_D5->SITEWIRE/.../D1`).

**SDF onto this netlist.** Any SDF keyed by nextpnr cell names (nextpnr's own,
or F1's `xray_delay.py`, which uses nextpnr's as its template) goes through
`fasm2net.py --names ROUTED.json --sdf THAT.sdf`:

* Cell arcs move to the cell on the same bel.
* Each INTERCONNECT is keyed by its sink bel/pin, and its source is rewritten
  to the bits' driver.
* The text of the delay triple is kept verbatim, so `GLS_SDF_FIELD`
  min/typ/max still works.
* A sink the SDF has no arc for gets 0 ps. On gcd_hw these are the 16k pins
  nextpnr left unconnected, which the bits tie to a constant.

For per-pip delays, F1 can emit them keyed by `TILE.DST.SRC` and sum along
`routes.tsv`, which gives each sink's pip path from driver to sink.

## Results on gcd_hw (R5 + fast fall, nextpnr 9c732bc6303458df)

See `research/data/fid/f2_gcd_hw.md`.

## What this does NOT show

* **Delay.** The delays are nextpnr's, re-keyed. A right netlist with wrong
  delays is still not the board (F1).
* **Only what prjxray-db decodes.**
  - A bit the db does not know is invisible.
  - A feature with an all-zero encoding (`PRECYINIT.C0`, a BUFGCTRL input mux's
    default) reads as configured whenever the tile is in use. That is how the
    hardware behaves, and bit2fasm prints it.
  - The db's semantics (`default`/`always` ppips, the FASM `_Y0` = upper-site
    convention for IOB/OLOGIC) are trusted, not measured.
* **The site models are this script's reading of the slice.** They were
  cross-read against f4pga-xc-fasm2bels's `clb_models.py` and checked here only
  by agreement with nextpnr's JSON on one design. A shared misreading (for
  example F7AMUX input order) would be invisible to `fasm_equiv.py`.
* **The subset gcd_hw uses.** DSP48E1, latches and LUTRAM are refused, not
  modelled. ipow (DSP) cannot be built yet.
