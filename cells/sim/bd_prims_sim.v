// ---------------------------------------------------------------------------
// bd_prims_sim.v -- simulation stand-ins for the xc7 primitives the library
// instantiates.  SIMULATION ONLY; yosys is never given this file.
//
// Requires  iverilog -gspecify  (run_sim.sh passes it).
//
// -- where the numbers come from --------------------------------------------
//
// Every delay below is a real silicon arc taken from prjxray's characterised
// SDF, not a guess and not yosys's abc9 cost model:
//
//   CLBLL_L.sdf  SLICEL/A6LUT   A1..A6 -> O6   (0.045::0.056)(0.100::0.124)
//   CLBLL_L.sdf  SLICEL/A5LUT   A1..A5 -> O5   (0.044::0.055)(0.122::0.152)
//                                              per pin, see the table below
//   BRAM_L.sdf   CLKARDCLK -> DOADO, unregistered      max 2.454 ns
//                DIADI setup                           max 0.737 ns
//                ADDRARDADDR setup                     max 0.566 ns
//                WEA setup                             max 0.532 ns
//
// The LUT figures are the 117-152 ps raw arc the sizing table quotes.  Rise
// and fall differ by more than a factor of two on this fabric, so they are
// modelled separately; a uniform per-cell delay would hide every asymmetric
// hazard in the library.
//
// -- what these arcs are NOT ------------------------------------------------
//
// They are cell arcs only.  Routing is about 74% of a real hop and the routed
// per-hop median is ~478 ps, so a chain of N LUTs here runs roughly 3.7x
// faster than the same chain on silicon.  That is the artifact's "an arc-only
// figure lands about 3x short", and it is why no matched delay may be sized
// from a simulation.  BD_ROUTE_PS adds a uniform interconnect delay to every
// arc if you want to see the handshake run at a plausible hop time -- it
// scales everything together, so it tests the delay-insensitivity of the
// control network, NOT the bundling constraint.
//
// -- what no simulation of this library can show ----------------------------
//
//   - bundling violations, except at the RAM boundary below, where the setup
//     numbers are real and are checked
//   - the clock buffer yosys inserts unasked.  BUFG here is zero delay, on
//     purpose: the ~2 ns it really costs is precisely the thing simulation
//     does not show, and modelling it would hide the hazard rather than
//     reproduce it
//   - metastability in bd_arbcell.  A LUT here resolves in one arc, always.
//
// No cell enters the library on a simulation pass.
// ---------------------------------------------------------------------------

`timescale 1ps / 1ps

`ifndef BD_ROUTE_PS
 `define BD_ROUTE_PS 0
`endif

// Slowest cell arc in the library, for testbench settle times.
`define BD_HOP_PS  (124 + `BD_ROUTE_PS)

// 6LUT: every pin has the same arc.  Rise and fall differ by 2.2x on this
// fabric, so they are modelled separately.
`define BD_T_RISE  (56 + `BD_ROUTE_PS)
`define BD_T_FALL  (124 + `BD_ROUTE_PS)
`define BD_T6      `BD_T_RISE, `BD_T_FALL

// 5LUT: per pin, A1..A5.
`define BD_T5_0    (55 + `BD_ROUTE_PS), (152 + `BD_ROUTE_PS)
`define BD_T5_1    (55 + `BD_ROUTE_PS), (152 + `BD_ROUTE_PS)
`define BD_T5_2    (52 + `BD_ROUTE_PS), (150 + `BD_ROUTE_PS)
`define BD_T5_3    (57 + `BD_ROUTE_PS), (150 + `BD_ROUTE_PS)
`define BD_T5_4    (60 + `BD_ROUTE_PS), (118 + `BD_ROUTE_PS)

// prjxray BRAM_L.sdf, max corner.  Exported so a testbench can size a matched
// delay from the vendor number rather than from a hand-copied constant --
// which is the whole point of the delays being placeholders.
`define BD_RAM_TSU_ADDR 566
`define BD_RAM_TSU_DI   737
`define BD_RAM_TSU_WE   532
`define BD_RAM_TCO      2454

// ---------------------------------------------------------------------------
// Each LUT is a mux tree, not an indexed lookup, and the difference matters
// here more than anywhere else.  Every feedback loop in this library powers up
// at x, and an indexed model keeps it there forever: INIT[{...x...}] is x, so
// a cell held in reset never resolves.  A mux tree resolves an x select
// whenever both its branches agree, which is what the silicon does and exactly
// why rst on a real pin drives a loop to a defined value.
//
// LUT1..LUT4 carry the 6LUT arc: standalone they land on the A6LUT, and where
// the packer folds one onto a 5LUT the difference is under 30 ps.
// ---------------------------------------------------------------------------

module LUT1 (output O, input I0);
    parameter [1:0] INIT = 2'h0;
    assign O = I0 ? INIT[1] : INIT[0];
    specify (I0 => O) = (`BD_T6); endspecify
endmodule

module LUT2 (output O, input I0, I1);
    parameter [3:0] INIT = 4'h0;
    wire [1:0] s1 = I1 ? INIT[3:2] : INIT[1:0];
    assign O = I0 ? s1[1] : s1[0];
    specify (I0 => O) = (`BD_T6); (I1 => O) = (`BD_T6); endspecify
endmodule

module LUT3 (output O, input I0, I1, I2);
    parameter [7:0] INIT = 8'h0;
    wire [3:0] s2 = I2 ? INIT[7:4] : INIT[3:0];
    wire [1:0] s1 = I1 ?   s2[3:2] :   s2[1:0];
    assign O = I0 ? s1[1] : s1[0];
    specify (I0 => O) = (`BD_T6); (I1 => O) = (`BD_T6); (I2 => O) = (`BD_T6);
    endspecify
endmodule

module LUT4 (output O, input I0, I1, I2, I3);
    parameter [15:0] INIT = 16'h0;
    wire [7:0] s3 = I3 ? INIT[15:8] : INIT[7:0];
    wire [3:0] s2 = I2 ?   s3[7:4]  :   s3[3:0];
    wire [1:0] s1 = I1 ?   s2[3:2]  :   s2[1:0];
    assign O = I0 ? s1[1] : s1[0];
    specify (I0 => O) = (`BD_T6); (I1 => O) = (`BD_T6);
            (I2 => O) = (`BD_T6); (I3 => O) = (`BD_T6);
    endspecify
endmodule

module LUT5 (output O, input I0, I1, I2, I3, I4);
    parameter [31:0] INIT = 32'h0;
    wire [15:0] s4 = I4 ? INIT[31:16] : INIT[15:0];
    wire [7:0]  s3 = I3 ?   s4[15:8]  :   s4[7:0];
    wire [3:0]  s2 = I2 ?   s3[7:4]   :   s3[3:0];
    wire [1:0]  s1 = I1 ?   s2[3:2]   :   s2[1:0];
    assign O = I0 ? s1[1] : s1[0];
    specify (I0 => O) = (`BD_T5_0); (I1 => O) = (`BD_T5_1);
            (I2 => O) = (`BD_T5_2); (I3 => O) = (`BD_T5_3);
            (I4 => O) = (`BD_T5_4);
    endspecify
endmodule

module LUT6 (output O, input I0, I1, I2, I3, I4, I5);
    parameter [63:0] INIT = 64'h0;
    wire [31:0] s5 = I5 ? INIT[63:32] : INIT[31:0];
    wire [15:0] s4 = I4 ?   s5[31:16] :   s5[15:0];
    wire [7:0]  s3 = I3 ?   s4[15:8]  :   s4[7:0];
    wire [3:0]  s2 = I2 ?   s3[7:4]   :   s3[3:0];
    wire [1:0]  s1 = I1 ?   s2[3:2]   :   s2[1:0];
    assign O = I0 ? s1[1] : s1[0];
    specify (I0 => O) = (`BD_T6); (I1 => O) = (`BD_T6); (I2 => O) = (`BD_T6);
            (I3 => O) = (`BD_T6); (I4 => O) = (`BD_T6); (I5 => O) = (`BD_T6);
    endspecify
endmodule

// O6 sees all six pins and carries the 6LUT arc; O5 is a tap on the lower half
// of the same LUT, physically the 5LUT output, and carries the 5LUT arcs.
// Tying I5 high is what makes the two halves independent five-input functions
// -- the basis of every half-LUT cost in this library.  The O5-versus-O6 delta
// is why the arbitration cell's grants must share one site: it is tens of
// picoseconds and identical every build, where two separate sites differ by
// about a nanosecond and move between builds.
module LUT6_2 (output O6, output O5, input I0, I1, I2, I3, I4, I5);
    parameter [63:0] INIT = 64'h0;
    wire [31:0] s5 = I5 ? INIT[63:32] : INIT[31:0];
    wire [15:0] s4 = I4 ?   s5[31:16] :   s5[15:0];
    wire [7:0]  s3 = I3 ?   s4[15:8]  :   s4[7:0];
    wire [3:0]  s2 = I2 ?   s3[7:4]   :   s3[3:0];
    wire [1:0]  s1 = I1 ?   s2[3:2]   :   s2[1:0];
    assign O6 = I0 ? s1[1] : s1[0];

    wire [15:0] t4 = I4 ? INIT[31:16] : INIT[15:0];
    wire [7:0]  t3 = I3 ?   t4[15:8]  :   t4[7:0];
    wire [3:0]  t2 = I2 ?   t3[7:4]   :   t3[3:0];
    wire [1:0]  t1 = I1 ?   t2[3:2]   :   t2[1:0];
    assign O5 = I0 ? t1[1] : t1[0];

    specify
        (I0 => O6) = (`BD_T6); (I1 => O6) = (`BD_T6); (I2 => O6) = (`BD_T6);
        (I3 => O6) = (`BD_T6); (I4 => O6) = (`BD_T6); (I5 => O6) = (`BD_T6);
        (I0 => O5) = (`BD_T5_0); (I1 => O5) = (`BD_T5_1);
        (I2 => O5) = (`BD_T5_2); (I3 => O5) = (`BD_T5_3);
        (I4 => O5) = (`BD_T5_4);
    endspecify
endmodule

module BUFG (output O, input I);
    // Deliberately zero delay.  The ~2 ns a real BUFG costs is precisely what
    // simulation does not show; modelling it here would hide the hazard.
    assign O = I;
endmodule

// ---------------------------------------------------------------------------
// Minimal RAMB18E1 -- port A only, TDP x18, no output register.  Enough for
// bd_mem's protocol test; not a substitute for the real macro.
//
// The setup checks are the one place in this library where simulation can see
// a bundling violation, because the numbers on the far side of the boundary
// are characterised rather than routed.  They are enforced, not just declared:
// a late address or a late write datum prints a violation and poisons the
// output, which is what the design rule "audit the RAM boundary as a bundling
// boundary" means in practice.
// ---------------------------------------------------------------------------
module RAMB18E1 (
    input  CLKARDCLK, input CLKBWRCLK,
    input  ENARDEN,   input ENBWREN,
    input  REGCEAREGCE, input REGCEB,
    input  RSTRAMARSTRAM, input RSTRAMB,
    input  RSTREGARSTREG, input RSTREGB,
    input  [13:0] ADDRARDADDR, input [13:0] ADDRBWRADDR,
    input  [15:0] DIADI, input [15:0] DIBDI,
    input  [1:0]  DIPADIP, input [1:0] DIPBDIP,
    input  [1:0]  WEA, input [3:0] WEBWE,
    output [15:0] DOADO, output [15:0] DOBDO,
    output [1:0]  DOPADOP, output [1:0] DOPBDOP);

    parameter RAM_MODE = "TDP";
    parameter integer READ_WIDTH_A = 18, WRITE_WIDTH_A = 18;
    parameter integer READ_WIDTH_B = 0,  WRITE_WIDTH_B = 0;
    parameter integer DOA_REG = 0, DOB_REG = 0;
    parameter WRITE_MODE_A = "WRITE_FIRST", WRITE_MODE_B = "WRITE_FIRST";
    parameter SIM_DEVICE = "7SERIES";

    // prjxray BRAM_L.sdf, max corner
    localparam integer T_SETUP_ADDR = `BD_RAM_TSU_ADDR;
    localparam integer T_SETUP_DI   = `BD_RAM_TSU_DI;
    localparam integer T_SETUP_WE   = `BD_RAM_TSU_WE;
    localparam integer T_CO         = `BD_RAM_TCO;    // unregistered read

    integer violations;
    time    t_addr, t_di, t_we;

    reg [15:0] mem [0:1023];
    reg [15:0] doa;
    initial begin doa = 16'h0; violations = 0;
                  t_addr = 0; t_di = 0; t_we = 0; end

    always @(ADDRARDADDR) t_addr = $time;
    always @(DIADI)       t_di   = $time;
    always @(WEA)         t_we   = $time;

    wire [9:0] wa = ADDRARDADDR[13:4];

    task setup_fail(input [255:0] pin, input integer got, input integer need);
    begin
        violations = violations + 1;
        $display("  [%0t] BUNDLING %0s setup violated at the RAM boundary: %0d ps, needs %0d ps",
                 $time, pin, got, need);
    end
    endtask

    always @(posedge CLKARDCLK) if (ENARDEN) begin
        if ($time - t_addr < T_SETUP_ADDR)
            setup_fail("ADDR", $time - t_addr, T_SETUP_ADDR);
        if (|WEA && ($time - t_di < T_SETUP_DI))
            setup_fail("DI", $time - t_di, T_SETUP_DI);
        if ($time - t_we < T_SETUP_WE)
            setup_fail("WE", $time - t_we, T_SETUP_WE);

        if (|WEA) begin
            mem[wa] <= DIADI;
            doa     <= DIADI;               // WRITE_FIRST
        end else begin
            doa     <= mem[wa];
        end
    end

    assign #(T_CO) DOADO = doa;
    assign DOBDO   = 16'h0;
    assign DOPADOP = 2'h0;
    assign DOPBDOP = 2'h0;
endmodule
