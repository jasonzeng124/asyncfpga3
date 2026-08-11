# 01 — Toolchain

Paths verified 2026-07-28. Open FPGA tools are source builds under
`~/dev2/lib/fpgatoolchain/` and are **not on `$PATH`**.

## iCE40

```bash
TC=~/dev2/lib/fpgatoolchain
export YOSYS="$TC/yosys/build/yosys"
export NEXTPNR="$TC/nextpnr/build/nextpnr-ice40"
export PATH="$TC/icestorm/icepack:$TC/icestorm/icetime:$PATH"
```

| Tool | Path |
|---|---|
| yosys | `$TC/yosys/build/yosys` |
| nextpnr-ice40 | `$TC/nextpnr/build/nextpnr-ice40` |
| icepack | `$TC/icestorm/icepack/icepack` |
| icetime | `$TC/icestorm/icetime/icetime` |

nextpnr-ice40 is patched with a `getCellDelay` Python binding
(`ref/nextpnr-getCellDelay.patch`). Optional — stock `--sdf` also exports
routed delays.

## Xilinx 7-series (openXC7)

```bash
source ~/dev2/lib/fpgatoolchain/openxc7/export.sh
```

Sets `PATH`, `PYTHONPATH`, `NEXTPNR_XILINX_PYTHON_DIR`, `PRJXRAY_DB_DIR`.
Ships **its own yosys** with `synth_xilinx` — distinct binary from the
ice40 one.

| Thing | Path |
|---|---|
| install root | `$TC/openxc7/` |
| nextpnr-xilinx | `$TC/openxc7/bin/nextpnr-xilinx` |
| yosys (synth_xilinx) | `$TC/openxc7/bin/yosys` |
| prjxray source (`fasm2frames.py`) | `$TC/openxc7-src/prjxray/` |
| prjxray db | `$TC/openxc7/share/nextpnr/prjxray-db` |
| chipdb xc7z010clg400 (prebuilt, 57 MB) | `$TC/openxc7/xc7z010clg400.bin` |
| nextpnr-xilinx source | `$TC/openxc7-src/nextpnr-xilinx` |

- Use the **non-`.bak`** nextpnr-xilinx. Both report
  `0.8.2-73-gf681eb3a`; the non-`.bak` has the fractured-LUT timing-model
  fix.
- Local boost::python bindings, absent upstream:

  ```python
  ctx.getCellDelay(cell, fromPort, toPort)         # -> (found, delay_ps)
  ctx.getRouteDelayPs(netName, cellName, portName) # -> ps, or -1
  ```

  An alternative to `--sdf` for routed picoseconds; `--sdf` also works
  (confirmed 2026-07-28).
- Source branch is `stable-backports`, not `main` (main = pybind11
  migration, ~2900 commits diverged, weaker Xilinx-arch support).
- Rebuild: `make -j8 nextpnr-xilinx` in the existing build dir (~2 min,
  reuses the `ARCH=xilinx` cache).

New chipdb (only for a different part):

```bash
pypy3 nextpnr-xilinx/xilinx/python/bbaexport.py \
  --device xc7z010clg400-1 --xray <prjxray-db>/artix7 \
  --metadata <meta>/zynq7 --bba X.bba
bbasm --l X.bba X.bin
```

`bbaexport` auto-swaps artix7 → zynq7 for xc7z parts. Use `pypy3`; builds
are slow.

## Vendor

`~/dev2/lib/vivado/2026.1/Vivado_Lab/bin/` — `hw_server`, **`xsdb`** (this
install has no `xsct`). No GUI, drivers, or license needed.

## JTAG / programming

| Tool | Path | Use |
|---|---|---|
| xc3sprog | `/usr/bin/xc3sprog` | PL load + chain scan |
| openFPGALoader 1.1.1 | `~/dev2/lib/jtag/openFPGALoader/build/openFPGALoader` | PL load + SVF playback |
| fxload | `/usr/sbin/fxload` | FX2 firmware upload |
| FX2 firmware | `~/dev2/lib/jtag/fw/xusb_xp2.hex` | irreplaceable — source URL is dead |
| dfu-util (Linux) | `/usr/bin/dfu-util` | present; Fomu uses the Windows binary (`03`) |
| arm-none-eabi-gcc | `/usr/bin/arm-none-eabi-gcc` | bare-metal A9 |

openocd not installed. `ref/zynq/openocd_ebaz4205.cfg` is unvalidated and
its `interface ftdi` block does not match this cable.

## Simulation / general

`iverilog` + `vvp` (`-g2012`), `python3`, `pypy3`, `clang`, `cmake`
(`~/.local/bin`).

- **ninja not installed** — LLVM-based builds defaulting to it need
  `-G "Unix Makefiles"` or an install.
- **verilator not installed** — hand-write iverilog TBs when driving
  another tool's generated RTL.

## Windows interop

Windows binaries in `~/docs/dev-win/`, run directly from WSL bash.
Convert paths with `wslpath -w`. Used for Fomu DFU flashing and serial
reads (`powershell.exe -Command ...`).
