# 04 — Synthesis flows

Scripts: `ref/ice40/run_flow.sh`, `ref/xc7/run_flow.sh`. §1–§5a apply to
netlists with **deliberate combinational loops** (LUT-feedback latches,
C-elements). Plain synchronous logic needs only §5b, §6, §7.

## 1. Keeping combinational loops alive

| Layer | Mechanism |
|---|---|
| yosys | every pin of every library LUT passes through `loop_breaker`, a `(* blackbox, keep *)` pass-through. Blackboxes are opaque to opt/abc ⇒ yosys never sees a loop ("Found 0 SCCs") and cannot optimize through, merge, or const-propagate across a library LUT pin. `keep` also blocks `opt_clean` sweeping. |
| nextpnr | `--ignore-loops`, required on both architectures; timing-graph construction aborts otherwise |

## 2. Pass ordering (load-bearing)

Dissolve breakers with `techmap -map loop_breaker_dissolve.v` (→
`assign Y = A`; nextpnr cannot place blackboxes) **after all optimization,
immediately before `write_json`**. No opt pass afterwards except
`opt_clean`. Enforce with `select -assert-none t:loop_breaker`.

Measured cost of dissolving *before* synthesis:

| Target | Result |
|---|---|
| iCE40 | "Found 87 SCCs"; **74 of 182** library LUTs eaten. Routes fine, silently corrupt. |
| xc7 | **117 of 182** survive (36% eaten); 135 LUT4 vs. correct 199 — **zero SCCs reported, zero errors** (`scc` cannot see through blackboxes) |

Cell-count invariants (§7) are the only witness.

## 3. iCE40 pass sequence

1. `read_verilog -lib -specify +/ice40/cells_sim.v` — native `SB_LUT4`
   instances resolve and pass through untouched.
2. `read_verilog -DSYNTHESIS -sv -I rtl <lib>`, then the design.
3. `setattr -mod -unset keep_hierarchy` — `(* keep_hierarchy *)` blocks
   `synth_ice40`'s flatten and yields a netlist nextpnr cannot ingest.
   Safe: loop protection is the blackboxes, not the hierarchy.
4. `synth_ice40` — the full pipeline is safe given the blackboxes; only
   generated datapath assigns get synthesized.
5. *(optional)* graft IO shim (§6).
6. Dissolve breakers (§2).
7. `delete t:$scopeinfo`; `write_json`.

```bash
nextpnr-ice40 --up5k --package sg48 --ignore-loops --json X.json --asc X.asc [--sdf X.sdf]
icepack X.asc X.bin
```

`--force` not needed. `--sdf` dumps routed IOPATH + INTERCONNECT delays
with netlist names preserved — the signoff data source (`05`).

## 4. xc7 pass sequence (openXC7)

Carrying iCE40 `SB_LUT4` into a Xilinx flow gives *stronger* isolation
than native cells:

1. `read_verilog -lib +/ice40/cells_sim.v` → `SB_LUT4` = empty blackbox,
   opaque to `synth_xilinx`.
2. `synth_xilinx -family xc7 -top T -flatten -nodsp -nosrl -nolutram -nobram`

   | Flag | Why |
   |---|---|
   | `-flatten` | **required** — `synth_xilinx` doesn't flatten by default and nextpnr cannot ingest hierarchical JSON |
   | `-nodsp` | multiplies stay in fabric; DSP inference is a separate deliberate step |
   | `-nosrl -nolutram -nobram` | clockless netlists have no clocked storage; forbid inference that can only misfire |

   Datapath maps to LUT1..6, MUXF7/F8, CARRY4.
3. `techmap -map sb_lut4_map.v` → Xilinx LUT4, 1:1, no opt passes nearby.
4. `scc`, then `select -clear` (`scc` *sets* the selection); must log
   "Found 0 SCCs". Not the library-integrity check — the count invariants
   are.
5. Dissolve breakers (§2); `delete t:$scopeinfo`; `write_json`.

**Init-bit math is the identity.** Both families index
`O = INIT[{I3,I2,I1,I0}]` (yosys's ice40 and xilinx `cells_sim.v` have
identical mux trees; prjxray's LUT4 INIT convention matches). Pins 1:1,
`INIT = LUT_INIT` verbatim.

`ref/xc7/check_lut_map.sh` SAT-proves this per build (~1 min): 12 miters +
16 anchors = **28 proofs, asserted exactly**. The battery includes the four
single-variable functions (`0xFF00`=I3, `0xF0F0`=I2, `0xCCCC`=I1,
`0xAAAA`=I0), catching pin permutation and init reversal. A pin-swapped map
was verified to FAIL.

**Do not remove the checker's `hierarchy` pass.** Without it, `flatten`
binds against unelaborated modules and silently drops INIT — both sides
collapse to constant 0 and every miter is vacuously equal (SAT problems of
6 variables / 4 clauses). This passed a deliberately-broken map once.

```bash
nextpnr-xilinx --chipdb xc7z010clg400.bin --xdc X.gen.xdc --ignore-loops \
  --json X.json --write X_routed.json --fasm X.fasm
python3 <prjxray-src>/utils/fasm2frames.py --db-root <db>/zynq7 \
  --part xc7z010clg400-1 X.fasm X.frames
xc7frames2bit --part_file <db>/zynq7/xc7z010clg400-1/part.yaml \
  --part_name xc7z010clg400-1 --frm_file X.frames --output_file X.bit
```

- The `fasm2frames` wrapper in `~/.local/bin` is broken (missing `utils`
  import). Call the prjxray source copy with `PYTHONPATH` = prjxray source
  + `openxc7/lib/python`. "falling back to slower textX parser" is benign.
- "No clocks found in design" ×2 is expected.

## 5. Silicon-killing traps

### 5a. Duplicate-net LUT pins get zeroed

A LUT with **the same net on two input pins**, merged onto a fracturable
slice by the placer, gets its FASM `INIT` mis-permuted to **all zero**.
Sim green, audits green, dead on silicon.

Fix at two points (`ref/xc7/dedup_lut_inputs_xc7.py`):
- pre-P&R fold on the yosys JSON — rewrite the truth table to one pin, tie
  extras to constant 0;
- post-route `--check` on the routed JSON — nonzero exit on a live merged
  pin.

Trigger is library-dependent (constant pins tied with literal `1'b0` never
trigger it; a duplicated live net triggers on every chain stage). Run the
gate regardless — abc9 restructuring can introduce the pattern.

### 5b. Post-route pin views lie under fracturable-LUT packing

When nextpnr packs two independent LUT4s onto one `SLICE_LUTX` (O5/O6
mode, whenever combined distinct inputs fit in 5 shared pins),
`ctx.cells[...].ports` for **either** logical LUT reports the physical
bel's full pin set, including the other cell's inputs. `pack_luts()` is a
1:1 rename; the ambiguity comes from **placement**.

Fix (`ref/xc7/timing_dump.py`): read the **pre-place** synth JSON with
stdlib `json` for ground-truth logical connectivity, then use its
`netnames` section to re-identify which physical A-port carries that net
**by name** post-route. Multi-bit buses need `f"{name}[{i}]"` reconstructed
from position in the `bits` array — bare-name lookup silently matches
nothing and surfaces as "0 contribution" everywhere. **Raise on an
unresolved probe; never score it zero.**

## 6. Constraints and IO budget

**xc7.** nextpnr-xilinx hard-errors on any pad without `IOSTANDARD`, and
its XDC parser rejects `[get_ports]` (parse error) and `[get_ports *]`
(matches nothing). There is no "allow unconstrained IO" flag. Generate
explicit `PACKAGE_PIN` + `IOSTANDARD LVCMOS33` per port bit from prjxray's
`package_pins.csv`, restricted to **PL banks 34/35** (banks 0/500/501/502
are config/PS). xc7z010clg400 has **100 PL pads**. For real hardware use a
checked-in XDC (`ref/zynq/ebaz4205.xdc`).

**ice40.** UP5K sg48 = 39 IO sites, one `SB_IO` per port bit. Over budget
⇒ shim: scalars pass through, wide inputs driven by one shared replicated
pin, wide outputs expose bit 0 (rest dangle — safe; yosys opt is over and
nextpnr never removes cells).

**Graft the shim after synthesis with a plain `flatten`.** Wrapping before
synthesis lets abc exploit `a == b == c` on the replicated bus (measured:
523 → 516 datapath LUTs), i.e. changes the design under measurement.
Assert counts match the unwrapped design.

## 7. Invariants to assert (exit nonzero on each)

- `loop_breaker` count after synthesis is a **positive multiple of 5**
  (4 inputs + output per library LUT); `count/5` = library LUTs, the
  remaining LUT4s are datapath.
- Library-LUT and carry counts **unchanged** by shim graft and by breaker
  dissolution; zero `loop_breaker` cells in the final netlist.
- xc7: the SB_LUT4→LUT4 retarget is 1:1 and changes no other cell count.
- Every "Found N SCCs" has N = 0; no loop-breaking log lines; no abc9
  `$__ABC9_SCC_BREAKER` cells **instantiated** (abc9 always *defines* that
  module — benign).
- LUT-map SAT check: exactly 28 proofs.
- Library LUT count matches the compiler's timing sidecar.
- nextpnr reached "Routing complete", no ERROR lines, output non-empty.

### Expected log noise

| Message | Meaning |
|---|---|
| "Removed N unused cells" (coarse synth) | datapath `$`-cell lowering |
| `opt_merge` "Removed a total of N cells" | CSE among datapath gates; library LUTs cannot merge (every input net is a distinct breaker output) |
| "ABC: Warning: The network is combinational." | no flip-flops |
| yosys `check` "no driver" mid-`-run` range | flow-position artifact |

## 8. Reference numbers (`addmul`, for smell-testing)

| Target | Numbers |
|---|---|
| UP5K sg48 | 523 SB_LUT4 pre-PnR (182 lib + 341 datapath) + 27 SB_CARRY → 525 ICESTORM_LC, 7 SB_IO, ~104 KB bin |
| xc7z010clg400-1 | 182 lib LUT4 + 53 LUT2, 9 LUT3, 17 LUT4, 20 LUT5, 184 LUT6, 52 MUXF7, 12 MUXF8, 8 CARRY4; 500 SLICE_LUTX; `.bit` ≈ 2.08 MB; flow ~80 s (~60 s = SAT check) |

`.bit` size varies a few bytes per run — the output path is embedded in the
header.
