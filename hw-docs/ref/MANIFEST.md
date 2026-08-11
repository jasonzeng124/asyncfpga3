# ref/ — working files

**Generic** = usable as-is. **Adapt** = logic is right, port names /
register maps / library paths are design-specific. **Read** = keep for the
technique.

Scripts are byte-identical to the validated originals, so their comments
sometimes cite documents that aren't here. `01`–`08` are the authority;
the code is kept unmodified because that's what was silicon-validated.

## Top level

| File | Kind | Purpose |
|---|---|---|
| `env.sh` | Generic | `source ref/env.sh [ice40\|xc7\|both]` |
| `nextpnr-getCellDelay.patch` | Generic | nextpnr-ice40 Python delay binding (already applied to the installed binary) |
| `audit_bundling.py` | Read | structural pre-route audit; ice40 + xc7 targets, RAM boundaries |

## `ice40/` — iCE40 flow (`04` §3)

| File | Kind |
|---|---|
| `run_flow.sh` | Adapt — netlist → routed `.bin` + sanity report |
| `synth.ys` | Adapt — template instantiated by `run_flow.sh` |
| `loop_breaker_dissolve.v` | Generic |

## `xc7/` — openXC7 flow (`04` §4)

| File | Kind | Purpose |
|---|---|---|
| `run_flow.sh` | Adapt | bare core → routed FASM/`.bit` + signoff |
| `build_ps.sh` | Adapt | PS7/AXI-wrapped bitstream; carries the margin guard |
| `synth.ys` | Adapt | |
| `loop_breaker_dissolve.v`, `sb_lut4_map.v` | Generic | |
| `check_lut_map.sh` | Generic | SAT-proves the LUT map, 28 proofs |
| `dedup_lut_inputs_xc7.py` | **Generic — do not skip** | duplicate-net LUT fix, `04` §5a |
| `timing_dump.py` | Adapt | `--post-route` hook; pre-place JSON pin resolution, `04` §5b |
| `timing_signoff.py` | Read/Adapt | routed-delay gate; docstring has the soundness argument |
| `postroute_audit_xc7.py` | Read | earlier post-route audit |

## `zynq/` — EBAZ4205 harnesses and drive scripts (`02`)

| File | Kind | Purpose |
|---|---|---|
| `ebaz4205.xdc` | Generic | board pins (LEDs: W14 red, W13 green) |
| `knapsack_ps_top.v` | Adapt | PS7 + GP0 slave + pulse adapter; silicon-proven |
| `fib_ps_top.v` | Adapt | same shape, alternate port naming |
| `knapsack_bench_top.v` | Adapt | + fabric repeat FSM, extended register map |
| `knapsack_jtag_top.v` | Adapt | BSCANE2/USER1, PS-free |
| `ledtest.v` | Generic | ring-oscillator blink; first-light bitstream |
| `xsct_knapsack.tcl` | **Read first** | BootROM catch, SLCR, memmap, 4-phase poking |
| `xsct_fib.tcl` | Adapt | same, alternate register naming |
| `xsdb_bench.tcl` | Adapt | drives the bench FSM |
| `xsdb_arm.tcl` | Adapt | loads/runs the ARM driver, mailbox polling |
| `svfgen_jtag.py` | Generic | SVF generator encoding the DAP-padding contract (`02` §6) |
| `openocd_ebaz4205.cfg` | **Unvalidated** | openocd not installed; ftdi block doesn't match this cable |

## `zynq-arm/` — bare-metal A9 driver (`02` §7)

| File | Kind |
|---|---|
| `knapsack_drive.c` | Adapt |
| `startup.S`, `ocm.ld`, `Makefile` | Generic — links at `0x20000`, MMU/caches off |

## `fomu/` — Fomu PVT (`03`)

| File | Kind | Purpose |
|---|---|---|
| `build.sh` | Adapt | audit-gated bitstream → `.dfu` |
| `fomu_pvt.pcf` | Generic | UWG30 pins |
| `fomu_uart_top.sv` | Adapt | USB-CDC harness; 3×`SB_GB` clock partition + `SB_WARMBOOT` on `'R'` |
| `fomu_top.sv` | Adapt | LED-only harness (no warmboot hook ⇒ physical replug) |
| `sync_timing_check.py` | Generic | sync-domain Fmax gate, `SYNC_MIN_FMAX_MHZ=33` |
| `postroute_checks.py` | Adapt | `--post-route` entry point wiring both checks |

Not included: the vendored USB-CDC core these harnesses instantiate.
