# A-prims-ram: digital semantics of RAMB18E1 as bd_mem instantiates it

Probe PrimsRam, shard A. Started 2026-10-29 08:39 UTC. North-star goal 1 ("RAMB18E1 if a
design uses them"). Builds on PrimsSeq (`Formal/Core/Prims/SeqFlop.lean`: `ap`, `winVal`,
`EqOn`, `NoRise`, `lastRise`, `kmux`).

STATUS: in progress (plan + data written; Lean being written).

## Plan
1. Read bd_mem.v and its users (bdc/mem.py, bdc/emit.py), the prjxray BRAM SDF, the iverilog
   stand-in (cells/sim/bd_prims_sim.v), B's LibEndMemMlink MemPort.
2. `Formal/Core/Prims/Ram.lean`: Kleene word/address algebra (decoder, read, write, three
   write modes), the timed relation `RamRel`, theorems, non-vacuity witness.
3. `Formal/Core/Prims/RamXray.lean`: the prjxray numbers as data (integer ps).
4. `Formal/Core/Prims/RamBd.lean`: the bundled-data obligation of bd_mem, derived.

## 1. What bd_mem instantiates (verified from cells/rtl/bd_mem.v), and who uses it

Expected configuration confirmed: `RAMB18E1 RAM_MODE=TDP`, port A x18 read and write, port B
width 0 and tied off, `DOA_REG=0`, `WRITE_MODE_A=WRITE_FIRST`, `CLKARDCLK = ram_clk` = the
single explicit buffer (`LUT1 2'h2`, or BUFG when `USE_BUFG=1`; bdc emits USE_BUFG=0) after the
`DSETUP` bd_delay of `req`; `ack` = `DCO` bd_delay of the same `ram_clk` net. `ENARDEN=1`,
`REGCE=0`, `RSTRAM/RSTREG=0`, `ADDRARDADDR={addr,4'b0}` (word bits [13:4], 1024 x 16),
`DIADI=wdata`, `DIPADIP=0`, `WEA={we,we}`, `DOADO=rdata`. No INIT_xx / INIT_A: contents 0.
So the clock IS the request edge: synchronous read on CLKARDCLK, latch-mode output.

Users: `bdc/mem.py` (`bdc_memport[_arb]_<AW>_<DW>_<N>` instantiates `ram_count(dw)`
bd_mem's per port, `DW=16` each, one DSETUP/DCO pair per RAM); `bdc/emit.py` `_op_load`,
`_op_store`, `_op_mem_controller` (Dynamatic `handshake.load/store/mem_controller`).
**No kernel in `kernels/` uses memory**: kernels/README.md says they are "memory-free by
construction" (collatz, collatz64, ipow, isprime, xorshift; gcd_hw too). The memory path is
exercised by Dynamatic's own memory kernels (bdc/AUDIT.md names `single_loop`, `fir`, and
Dynamatic's `gcd`, which `slack.py` rejects at a mem_controller cycle) and by testbenches/
board rigs: `cells/tb/tb_bdc_mem.v`, `tb_bdc_memseq.v`, `tb_mem.v`, `cells/hw/mem_port_ps.v`,
`mem_arb_ps.v`, `mem_bist_ps.v` (board PASS recorded in bdc/AUDIT.md and cells/hw/MEM_DCO.md).
So RAMB18E1 is in no design the formal capstone covers; it matters for Stage-6 kernels.
