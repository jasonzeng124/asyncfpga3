`timescale 1ns / 1ps
// ---------------------------------------------------------------------------
// ps7_stub.v -- an EMPTY PS7 for simulation.
//
// The generated bench files (hw/gen_bench.py) contain two modules: the
// <kernel>_bench_gen_bridge, which is pure fabric and is what every bench
// here actually drives, and the <kernel>_bench_gen top, which wires that
// bridge to a real PS7 for the board.  A testbench only instantiates the
// bridge -- but iverilog elaborates every module that nothing instantiates as
// a potential root, so the PS7-bearing top gets elaborated too and the
// missing primitive fails the compile.  The bench never simulates it.
//
// So the stub is deliberately EMPTY: it exists to satisfy elaboration, not to
// model anything.  If a bench ever needs PS7 BEHAVIOUR it must not reach for
// this file -- it would silently get a device that drives nothing, which
// looks like a hang rather than an error.  Declare it per bench with
//     // requires: sim/ps7_stub.v
// rather than compiling it into the cell suite, so nothing depends on it by
// accident.
// ---------------------------------------------------------------------------
module PS7 (
    input  MAXIGP0ACLK,
    output MAXIGP0ARESETN,
    output MAXIGP0AWVALID, input MAXIGP0AWREADY,
    output [31:0] MAXIGP0AWADDR, output [11:0] MAXIGP0AWID,
    output MAXIGP0WVALID, input MAXIGP0WREADY,
    output [31:0] MAXIGP0WDATA, output [3:0] MAXIGP0WSTRB,
    input  MAXIGP0BVALID, output MAXIGP0BREADY,
    input  [1:0] MAXIGP0BRESP, input [11:0] MAXIGP0BID,
    output MAXIGP0ARVALID, input MAXIGP0ARREADY,
    output [31:0] MAXIGP0ARADDR, output [11:0] MAXIGP0ARID,
    input  MAXIGP0RVALID, output MAXIGP0RREADY,
    input  [31:0] MAXIGP0RDATA, input [1:0] MAXIGP0RRESP,
    input  MAXIGP0RLAST, input [11:0] MAXIGP0RID,
    // Directions here are the REAL PS7's, not whatever a bench happens to
    // leave unconnected: FCLKRESETN is an OUTPUT (the generator ties it off
    // with an empty connection) and FCLKCLKTRIGN is a 4-bit INPUT (driven
    // with 4'b0).  An earlier copy of this stub had both backwards, which
    // only surfaced as "expression not valid in assign l-value".
    output [3:0] FCLKCLK,
    output [3:0] FCLKRESETN,
    input  [3:0] FCLKCLKTRIGN
);
endmodule
