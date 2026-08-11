# 03 — iCE40UP5K / Fomu PVT

iCE40UP5K-UWG30 on a USB-A-stub board. `foboot` v1.9.1 DFU bootloader in a
protected region ⇒ **unbrickable**. Built-in USB-CDC gives serial readback
with no extra hardware; flash cycles are fully software-driven (§3).

## 1. Build → `.dfu`

`ref/fomu/build.sh`:

```
yosys synth_ice40 (top = harness wrapping core)
  → write_json (pre-resolve, for structural audit)
  → techmap loop-breaker resolve; opt_clean; write_json
nextpnr-ice40 --up5k --package uwg30 --pcf fomu_pvt.pcf
              --ignore-loops --freq 48 --timing-allow-fail --opt-timing
              [--seed N] [--placer-heap-timingweight TW] [--no-promote-globals]
  → second nextpnr run with --post-route <checks.py>
icepack fomu.asc fomu.bin
cp → fomu.dfu ; dfu-suffix -v 1209 -p 70b1 -a fomu.dfu
```

| Flag | Why |
|---|---|
| `--ignore-loops` | required for combinational-loop netlists (`04`) |
| `--timing-allow-fail` | required for a clockless cone between registers; **silences real failures elsewhere** ⇒ pair with §5a's gate |
| `dfu-suffix -v 1209 -p 70b1` | Fomu application VID:PID |

Sweep knobs are env vars `SEED`, `TW`, `NPG`.

## 2. Flash

USB passthrough to WSL does **not** work for this device (usbipd breaks
Windows enumeration reproducibly). Use the Windows dfu-util via interop:

```bash
~/docs/dev-win/dfu-util/dfu-util-0.9-win64/dfu-util.exe \
   -D "$(wslpath -w build/fomu.dfu)"
```

Device must be in DFU mode (`1209:5bf0`).

## 3. Return to DFU without replug

Harnesses instantiate `SB_WARMBOOT` (S1=S0=0 → foboot = multiboot image 0)
triggered by receiving `'R'` on the CDC port.

1. Send `R` over serial. The write may throw "device not functioning" —
   expected; the FPGA reconfigures mid-call.
2. DFU appears in ~3 s.
3. Flash.

Physical replug is needed only when the running bitstream has no warmboot
hook. Put the hook in every harness.

## 4. Readback

USB-CDC builds enumerate as `USB Serial Device (COM6)`, VID:PID
`1D50:6130`.

Enumeration check — **poll with retries**; single 3-second checks give
false negatives:

```bash
powershell.exe -Command "Get-PnpDevice -PresentOnly | \
  Where-Object {\$_.InstanceId -like '*VID_1D50&PID_6130*'} | \
  Format-List FriendlyName,Status"
```

Read:

```bash
powershell.exe -Command "\$p=New-Object System.IO.Ports.SerialPort('COM6',115200); \
  \$p.Open(); Start-Sleep -Milliseconds 500; \$p.ReadExisting(); \$p.Close()"
```

## 5. Limits

### 5a. USB core Fmax floor ≈ 33 MHz by model

The vendored USB-CDC core cannot close 48 MHz on UP5K under nextpnr's
worst-case model. Measured enumeration threshold: **33.7–34.1 MHz works,
≤31.4 MHz reproducibly fails to enumerate**. Typical silicon ≈1.5× the
worst-case model (48/1.5 ≈ 32).

Gate separately, since `--timing-allow-fail` hides the USB core's real
failures: `ref/fomu/sync_timing_check.py`, `SYNC_MIN_FMAX_MHZ=33`, as a
`--post-route` hook.

After any netlist change:
- Re-sweep `SEED` — spread is ~28–34 MHz; one seed is not evidence.
- Keep harness glue off `clk_48mhz`; use the 3×`SB_GB` partition
  (`clk_drv` / `clk_smp` / `clk_48mhz`) in `ref/fomu/fomu_uart_top.sv`, or
  false register→async-cone→register paths drown placer criticality.
- Known-good: `SEED=11 TW=30 NPG=1` → 33.93 MHz.

### 5b. Congestion wall above ~50% LC

At 48–55% of UP5K LUTs, routing congests around the fixed-position USB
core's high-fanout clock-enable nets. Observed: est. Fmax 20–24 MHz
uniformly across 12 seeds, `--placer-heap-timingweight` 30 and 80, and a
datapath-width reduction — every knob <1 MHz. Not a seed-RNG problem.

Options: an hx8k-class board (4× LUTs) or a smaller design. Check
`ICESTORM_LC` utilization before assuming a sweep will help.

## 6. IO budget

| | |
|---|---|
| Fomu PVT | `--up5k --package uwg30`, pins in `ref/fomu/fomu_pvt.pcf` |
| Largest UP5K package (sg48) | 39 IO sites, one `SB_IO` per top-level port bit |
| Wide-IO designs | route on `hx8k ct256` |

Over the pad budget ⇒ post-synthesis IO shim (`04` §6).
