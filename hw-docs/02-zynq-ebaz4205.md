# 02 — Zynq-7010 / EBAZ4205

`xc7z010clg400-1`. Community pinout: `xjtuecho/EBAZ4205`. Driven from WSL2
over one Xilinx Platform Cable USB II (Waveshare clone). No Vivado GUI, no
Windows drivers, no PS software stack.

## 1. JTAG topology

| Position | TAP | IDCODE | IR |
|---|---|---|---|
| nearest TDI | ARM DAP | `0x4ba00477` | 4 |
| nearest TDO | PL TAP | `0x13722093` | 6 |

Total IR 10. Raw access to one TAP must pad the other (DAP BYPASS = `0xF`).
xsdb / xc3sprog / openFPGALoader `--index-chain` handle this; hand-written
SVF does not (§6).

- PL configuration over JTAG needs **zero PS cooperation**; the stock boot
  image may be mid-boot or hung.
- **PL is inert after configuration until the PS releases it** — level
  shifters default off, PL resets held. Needs §4. A self-contained
  bitstream (own oscillator, PL pins only) runs immediately after DONE.
- **`rst -system` clears the PL.** Reset first, program second.

## 2. Cable bring-up (WSL2)

Enumerates `03fd:0013` with no firmware; re-enumerates `03fd:0008` after
FX2 upload.

Windows, admin, once:

```
usbipd bind --busid 3-2
usbipd policy add --effect Allow --operation AutoBind --hardware-id 03fd:0008
usbipd attach --wsl --auto-attach --busid 3-2     # keep running
```

AutoBind pre-stages the post-firmware re-enumeration. Bus id `3-2` here.

WSL, once per cable power-cycle:

```bash
sudo fxload -v -t fx2 -I ~/dev2/lib/jtag/fw/xusb_xp2.hex -D /dev/bus/usb/001/00N
```

WSL, **every session** (no udev ⇒ root-only nodes; perms reset and the
node number changes on every re-enumeration):

```bash
sudo chmod 666 /dev/bus/usb/001/*
```

Requires user sudo. usbipd works for this cable; it does **not** work for
the Fomu (`03`).

## 3. Load routes

All take a standard `.bit`; no `.bin` conversion.

### 3a. xsdb + hw_server — load + PS + drive in one tool

```bash
$VIVADO_LAB/hw_server -d -s tcp::3121      # once per session
$VIVADO_LAB/xsdb script.tcl
```

```tcl
connect -url tcp:localhost:3121
targets                               ;# DAP + APU + 2x A9 + xc7z010
targets -set -filter {name =~ "APU*"}
rst -system
targets -set -filter {name =~ "xc7z010*"}
fpga -f my_design.bit                 ;# "FPGA done."
```

### 3b. xc3sprog — load-only, no server

```bash
xc3sprog -c xpc -j                   # chain scan, both TAPs
xc3sprog -c xpc -p 1 my_design.bit   # -p 1 = PL TAP; ~15 s
```

Also the non-destructive liveness probe. No PS access.

### 3c. openFPGALoader — load + SVF playback

```bash
openFPGALoader --cable xilinxPlatformCableUsb --index-chain 1 my_design.bit
openFPGALoader --cable xilinxPlatformCableUsb --index-chain 1 my_vectors.svf
```

`--index-chain` pads the DAP for **bitstreams** only; SVF is shifted raw
and must encode padding itself (§6).

### 3d. u-boot `fpga loadb` — unused

Needs a boot chain + serial/network. No serial device has appeared on this
machine.

## 4. PS bring-up (SLCR)

Required after `fpga -f` for any design touching a PS resource:

```tcl
mwr -force 0xF8000008 0xDF0D          ;# SLCR unlock
mwr -force 0xF8000170 0x00100A00      ;# FPGA0_CLK_CTRL: FCLK0 = IO PLL/10 = 100 MHz
mwr -force 0xF8000900 0xF             ;# LVL_SHFTR_EN
mwr -force 0xF8000240 0x0             ;# FPGA_RST_CTRL: release PL resets
mwr -force 0xF8000004 0x767B          ;# SLCR lock
```

| Clock | Value |
|---|---|
| PS_CLK crystal | 33.33 MHz |
| PLL lock | `PLL_STATUS = 0x3f` at reset FDIV, no programming needed |
| IO PLL | 1000 MHz ⇒ FCLK0 = 100 MHz (wall-clock 97.9–99.2) |
| ARM PLL | 666.67 MHz CPU |
| A9 global timer | CPU/2 = 333.33 MHz, 64-bit at `0xF8F00200` |

`*_PLL_CTRL = 0x...008` is `BYPASS_QUAL` (bypass *source select*), **not**
`BYPASS_FORCE` — PLL outputs are live. Misreading gives 30× clock errors;
calibrate against wall clock.

## 5. AXI drive (M_AXI_GP0, no PS software)

**Cold-catch CPU0.** Plain `stop` times out against the running boot
image. `rst -system` on APU, then an immediate tight `stop`-retry loop;
verify **`PC < 0x20000`** (BootROM, PC ≈ 0x608c, caches/MMU off). A fixed
post-reset sleep is a race. See `catch_cpu0_in_bootrom` in
`ref/zynq/xsct_knapsack.tcl`.

**Declare the map.** `memmap -addr 0x40000000 -size 0x1000 -flags 3`, once
per session, before any `mrd` / `mwr -force`.

**Echo AXI3 IDs.** GP0 is full AXI3; the PS interconnect routes responses
by 12-bit ID. A PL slave must capture `AWID`/`ARID` and echo `BID`/`RID`.
Tying them to 0 hangs every CPU access ("Timeout waiting for the
Instruction Complete bit") and wedges the DAP — sim stays green if the TB
drives ID 0.

### Harness register map

`ref/zynq/*_ps_top.v`: PS7 + BUFG + AXI3 slave FSM + registers + pulse
adapter + core. 2 physical pins (LEDs); data rides GP0 at `0x40000000`.

| Offset | Name | Access | Bits |
|---|---|---|---|
| 0x00 | CTRL | RW | `[0]=i_req [1]=o_ack [2]=rst` (rst powers up 1) |
| 0x04 | STATUS | RO | `[0]=i_ack` (sticky) `[1]=o_req` |
| 0x08 | I_DATA | RW | input word (readback = liveness echo) |
| 0x0C | O_DATA | RO | result |

Host 4-phase sequence: write I_DATA → `CTRL.i_req=1` → poll
`STATUS.i_ack==1` → `CTRL.i_req=0` → poll `STATUS.o_req==1` → read O_DATA
→ `CTRL.o_ack=1` → poll `STATUS.o_req==0` → `CTRL.o_ack=0`.

**Pulse adapter is mandatory** for a 4-phase core: holding `i_req` even
~1 µs past `i_ack` rise wedges it permanently, and hosts poke at ms
cadence. Core-facing `i_req` = flop set on the CTRL write, cleared
**asynchronously** by the core's `i_ack` rise; `STATUS.i_ack` = sticky
accepted view; core-facing `o_ack = ctrl_o_ack & o_req`.

Bench variant (`ref/zynq/knapsack_bench_top.v`, `xsdb_bench.tcl`) extends
the map (0x00–0x0C byte-compatible): `0x10 N_RUNS`, `0x14 CYCLES`,
`0x18 BCTRL`, `0x1C BSTATUS`, `0x20 LAT_MIN`, `0x24 LAT_MAX`. Drives N
runs in the FCLK0 domain, counts cycles in hardware, all async↔sync
crossings on 2-FF synchronizers.

### Drive tiers

| Tier | Per transaction | Use |
|---|---|---|
| host xsdb pokes | ~10 ms | first contact, debug |
| ARM bare-metal | ~34 µs | bulk validation |
| fabric FSM | true latency (24.4 µs measured) | performance numbers |

## 6. BSCANE2 (PS-free)

USER1..USER4 on the PL TAP, driven by SVF through openFPGALoader.
Empirically derived contract for this player + cable + chip — architecture
docs were not sufficient; re-derive from an IDCODE-readback experiment if
anything changes.

- `SIR 10` value = `(pl_instr << 4) | 0xF`. USER1 = `0x02` ⇒ `0x02F`.
- `SDR N+1` for an N-bit register: read data arrives **aligned in the low
  N bits** of TDO; write data must be **shifted LEFT by 1** on TDI (DAP
  bypass flop is in the write path).
- SVF `TDO`+`MASK` make playback self-checking — nonzero exit on
  mismatch, silent `Done` = all pass.
- openFPGALoader prints mismatches per-byte **without zero padding**.

Generator: `ref/zynq/svfgen_jtag.py`. Harness:
`ref/zynq/knapsack_jtag_top.v`.

## 7. ARM bare-metal (`ref/zynq-arm/`, driven by `xsdb_arm.tcl`)

~1.5 KB freestanding program in OCM; drives the protocol at bus speed,
reports via a mailbox read non-intrusively over the DAP.

- `-march=armv7-a -marm`, no libc, own `startup.S` + linker script.
- **MMU and caches OFF** — matches the BootROM catch point; no coherency
  footwork for JTAG mailbox reads.
- **Link at OCM `0x20000`**, not `0x0` — ROM may shadow `0x0..0x1FFFF`;
  `0x20000..0x2FFFF` is plain RAM in every boot state.
- **Verify after `dow`** — it reports success even when a region didn't
  stick; read back the entry vector before `con`.
- Capture timing deltas **before** signalling done.

## 8. Recovery

| Symptom | Cause | Fix |
|---|---|---|
| cable is `03fd:0013`, tools see nothing | FX2 firmware not loaded | §2 fxload |
| `lsusb` fine, tools say "no dongle" | root-only device node | `sudo chmod 666 /dev/bus/usb/001/*` |
| `stop` times out | boot chain running | `rst -system` + tight stop-retry (§5) |
| every `mrd 0x400xxxxx` times out, then DAP errors | slave not echoing AXI IDs, or PL resets/shifters held | fix IDs; rerun §4; `rst -system` on DAP |
| "Blocked address" | address not declared | `memmap` (§5) |
| PL loaded but inert | PS never released it | §4 |
| worked, then `rst -system`, now inert | system reset clears the PL | reprogram after every reset |
| only DAP enumerates ("APB AP transaction error") | DAP wedged by hung AXI | `rst -system` on the DAP target |

## 9. Session start

1. User: board powered, JTAG leads connected.
2. User: `sudo chmod 666 /dev/bus/usb/001/*`.
3. `xc3sprog -c xpc -j` → expect `0x4ba00477` + `0x13722093`.
4. Load a known-good bitstream and run its golden vectors before
   debugging new RTL — separates cable/board/PS/AXI health from design
   bugs in one command.
