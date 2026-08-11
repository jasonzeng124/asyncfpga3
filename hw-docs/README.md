# FPGA tooling reference

# note from developer: do not entirely trust these docs, verify before using. most of it should be right, but some may be outdated/wrong/not applicable advice so do not treat it as absolute truth.

Toolchain, board, and flow facts for FPGA work on this workstation.
Target-independent except where marked. Combinational-loop and non-STA
signoff material applies to clockless / elastic / dataflow netlists.

Tool paths verified 2026-07-28. Hardware state not verified.

| File | Contents |
|---|---|
| [`01-toolchain.md`](01-toolchain.md) | Tool paths, env setup |
| [`02-zynq-ebaz4205.md`](02-zynq-ebaz4205.md) | xc7z010: JTAG, load routes, SLCR, AXI, recovery |
| [`03-ice40-fomu.md`](03-ice40-fomu.md) | iCE40UP5K: build, DFU flash, USB-CDC readback, limits |
| [`04-synthesis-flows.md`](04-synthesis-flows.md) | yosys/nextpnr flows, loop survival, silicon-killing traps |
| [`05-timing-signoff.md`](05-timing-signoff.md) | Non-STA signoff, delay sources, calibration constants |
| [`06-benchmarking.md`](06-benchmarking.md) | Cross-tool comparison rules |
| [`07-gotchas.md`](07-gotchas.md) | Failure modes |
| [`08-conventions.md`](08-conventions.md) | Standing preferences |
| [`ref/`](ref/MANIFEST.md) | Flow scripts, harnesses, drive scripts, gates |

## Machine state (2026-07-28)

| | |
|---|---|
| yosys, nextpnr-ice40, icestorm | present, **not on `$PATH`** |
| openXC7 + `xc7z010clg400` chipdb | present |
| Vivado Lab 2026.1 (`xsdb`, `hw_server`) | present |
| xc3sprog, openFPGALoader, fxload, FX2 firmware, arm-none-eabi-gcc | present |
| iverilog, vvp, dfu-util, clang, cmake, python3, pypy3 | present, on `$PATH` |
| ninja, openocd, verilator | not installed |
| JTAG cable attached to WSL | no (`lsusb` = root hubs only) |
| `hw_server` running | no |
| EBAZ4205 powered | unknown |

Cable was attached 2026-07-22; the Windows usbipd bind likely survives and
needs only re-attaching (`02` §2).

## Boards

| Board | Part | Interface | Status |
|---|---|---|---|
| EBAZ4205 | xc7z010clg400-1 | JTAG (Platform Cable USB II) | validated: load, PS bring-up, AXI drive, ARM driver, fabric FSM |
| Fomu PVT | iCE40UP5K-UWG30 | USB (DFU + CDC) | validated: designs streaming results over USB-CDC |

Never used on Zynq: UART/serial (no `/dev/ttyUSB*` has existed),
Ethernet, SD/NAND boot, u-boot, Linux, any PS software. Everything goes
over one JTAG cable.
