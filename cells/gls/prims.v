// ---------------------------------------------------------------------------
// prims.v -- simulation models for the bel-level primitives nextpnr-xilinx
// emits in gcd_hw_routed.json, shaped so that EVERY timing arc the routed SDF
// annotates has a specify path to land on.
//
// These are not Xilinx UNISIMs.  SLICE_LUTX / SELMUX2_1 / SLICE_FFX / ICBUF are
// nextpnr-xilinx bel names (and, for ICBUF, this flow's own), and there is no
// vendor model for them.  They are written against nextpnr-xilinx's sources
// (xilinx/pack.cc, xilinx/fasm.cc) for what each bel port means.
//
// TIMING LIVES ENTIRELY IN THE SPECIFY BLOCKS.  There is no #delay on any
// behavioural assignment.  iverilog's module-path delays are real delays on the
// output net -- verified on a two-inverter probe -- so a specify path is
// sufficient to break the zero-time feedback loops this netlist is full of
// (every C-element and every latch in the library is a LUT feeding its own
// input).  Mixing an assign delay with a path delay would add the two, so the
// assigns carry none and every number in the simulation comes from the SDF.
//
// The default values below are nextpnr's own nominal arcs and are what an arc
// gets if the SDF does not annotate it.  On this design that set is exactly the
// arcs nextpnr's timing model omits because the pin is tied off or the function
// does not read it -- proved, not assumed: no unrouted LUT pin in this netlist
// carries a live dependence.  They are never zero, so no combinational loop can
// close in zero time.
//
// SLICE_LUTX INIT is PHYSICALLY addressed (A1 = bit 0).  gen.py pre-applies
// nextpnr's X_ORIG_PORT_A<n> permutation, so this module is a plain decoder.
// ---------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none

// ---- ICBUF ------------------------------------------- one routed net hop --
// One instance per INTERCONNECT entry in the routed SDF, i.e. one per sink
// pin.  This exists because iverilog 11 parses (INTERCONNECT ...) and then
// applies nothing -- so the only way to get nextpnr's routed wire delays into
// the simulation is to make each of them an IOPATH on a cell of its own.
// It also makes the fanout of a driver arrive at its sinks at different times,
// which is the physical truth and is exactly what a bundled-data design's
// margin is spent on.
// The delay is a PARAMETER as well as an SDF target: netlist.v leaves it at
// the default and lets $sdf_annotate fill it in (that is the acceptance-gate
// build), while netlist_baked.v sets it from the same parsed SDF number at
// generation time.  Both carry identical delays -- proved by diffing a run --
// and the baked one exists only because iverilog's annotator does a linear
// scope scan per entry, which on 58k instances costs minutes of wall clock
// before time 0.
module ICBUF (input wire I, output wire O);
    parameter D = 1;
    assign O = I;
    specify (I => O) = D; endspecify
endmodule

// ---- SLICE_LUTX --------------------------------------------------- 1 LUT --
// One nextpnr SLICE_LUTX bel drives exactly one of O5/O6 (checked: no cell in
// this design connects both).  O6 is the full six-input function; O5 is
// architecturally restricted to A1..A5 and reads INIT[31:0].
module SLICE_LUTX (
    input  wire A1, A2, A3, A4, A5, A6,
    output wire O5, O6
);
    parameter [63:0] INIT = 64'h0;
    parameter TA1O6=124, TA2O6=124, TA3O6=124, TA4O6=124, TA5O6=124, TA6O6=124;
    parameter TA1O5=124, TA2O5=124, TA3O5=124, TA4O5=124, TA5O5=124;

    wire [31:0] s5 = A6 ? INIT[63:32] : INIT[31:0];
    wire [15:0] s4 = A5 ?   s5[31:16] :   s5[15:0];
    wire [ 7:0] s3 = A4 ?   s4[15:8]  :   s4[7:0];
    wire [ 3:0] s2 = A3 ?   s3[7:4]   :   s3[3:0];
    wire [ 1:0] s1 = A2 ?   s2[3:2]   :   s2[1:0];
    assign O6 = A1 ? s1[1] : s1[0];

    wire [15:0] t4 = A5 ? INIT[31:16] : INIT[15:0];
    wire [ 7:0] t3 = A4 ?   t4[15:8]  :   t4[7:0];
    wire [ 3:0] t2 = A3 ?   t3[7:4]   :   t3[3:0];
    wire [ 1:0] t1 = A2 ?   t2[3:2]   :   t2[1:0];
    assign O5 = A1 ? t1[1] : t1[0];

    specify
        (A1 => O6) = TA1O6; (A2 => O6) = TA2O6; (A3 => O6) = TA3O6;
        (A4 => O6) = TA4O6; (A5 => O6) = TA5O6; (A6 => O6) = TA6O6;
        (A1 => O5) = TA1O5; (A2 => O5) = TA2O5; (A3 => O5) = TA3O5;
        (A4 => O5) = TA4O5; (A5 => O5) = TA5O5;
    endspecify
endmodule

// ---- SELMUX2_1 ------------------------------------------ MUXF7 / MUXF8 --
// The bel's two data pins are named by the bare digits 0 and 1 in both the
// JSON and the SDF.  gen.py renames them D0/D1 on BOTH sides of the rewrite,
// so nothing here has to be an escaped identifier.
module SELMUX2_1 (
    input  wire D0, D1, S0,
    output wire OUT
);
    parameter TD0OUT=104, TD1OUT=104, TS0OUT=273;
    assign OUT = S0 ? D1 : D0;
    specify
        (D0 => OUT) = TD0OUT; (D1 => OUT) = TD1OUT; (S0 => OUT) = TS0OUT;
    endspecify
endmodule

// ---- SLICE_FFX ------------------------------------------ FDRE and FDSE --
// Both map to this bel and they differ only in what SR does.  X_ORIG_PORT_SR
// records which: "R" -> synchronous reset to 0, "S" -> synchronous set to 1.
// gen.py passes it as SRVAL.  20 of the 247 flops here are FDSE, and gcd_hw's
// rst_sr is built out of them -- modelled as FDRE it would never assert the
// rig's reset at all.  INIT is the configuration (global set/reset) value.
module SLICE_FFX (
    input  wire CK, D, CE, SR,
    output reg  Q
);
    parameter [0:0] INIT  = 1'b0;
    parameter [0:0] SRVAL = 1'b0;
    parameter TCKQ = 100;
    initial Q = INIT;

    always @(posedge CK)
        if (SR)      Q <= SRVAL;
        else if (CE) Q <= D;

    specify
        (posedge CK => (Q +: D)) = TCKQ;
        $setuphold(posedge CK, posedge D,  100, 100);
        $setuphold(posedge CK, negedge D,  100, 100);
        $setuphold(posedge CK, posedge CE, 100, 100);
        $setuphold(posedge CK, negedge CE, 100, 100);
    endspecify
endmodule

// ---- CARRY4 ------------------------------------------------------- 1 bel --
// Flat scalar bel ports (not UNISIM's buses).  The SDF annotates only the
// S*/CIN arcs; the DI* arcs it omits keep the nominal below.
module CARRY4 (
    input  wire CIN, CYINIT,
    input  wire DI0, DI1, DI2, DI3,
    input  wire S0, S1, S2, S3,
    output wire O0, O1, O2, O3,
    output wire CO0, CO1, CO2, CO3
);
    wire cin0 = CIN | CYINIT;
    assign CO0 = S0 ? cin0 : DI0;
    assign CO1 = S1 ? CO0  : DI1;
    assign CO2 = S2 ? CO1  : DI2;
    assign CO3 = S3 ? CO2  : DI3;
    assign O0  = S0 ^ cin0;
    assign O1  = S1 ^ CO0;
    assign O2  = S2 ^ CO1;
    assign O3  = S3 ^ CO2;

    parameter TCINCO0=271, TCINCO1=157, TCINCO2=228, TCINCO3=114;
    parameter TCINO0=222, TCINO1=334, TCINO2=239, TCINO3=313;
    parameter TCYINITCO0=271, TCYINITCO1=157, TCYINITCO2=228, TCYINITCO3=114;
    parameter TCYINITO0=222, TCYINITO1=334, TCYINITO2=239, TCYINITO3=313;
    parameter TDI0CO0=100, TDI0CO1=100, TDI0CO2=100, TDI0CO3=100;
    parameter TDI0O1=100, TDI0O2=100, TDI0O3=100, TDI1CO1=100;
    parameter TDI1CO2=100, TDI1CO3=100, TDI1O2=100, TDI1O3=100;
    parameter TDI2CO2=100, TDI2CO3=100, TDI2O3=100, TDI3CO3=100;
    parameter TS0CO0=340, TS0CO1=433, TS0CO2=514, TS0CO3=489;
    parameter TS0O0=223, TS0O1=400, TS0O2=520, TS0O3=584;
    parameter TS1CO1=469, TS1CO2=558, TS1CO3=513, TS1O1=205;
    parameter TS1O2=558, TS1O3=623, TS2CO2=296, TS2CO3=358;
    parameter TS2O2=228, TS2O3=330, TS3CO3=354, TS3O3=233;
    specify
        (CIN => CO0) = TCINCO0; (CIN => CO1) = TCINCO1; (CIN => CO2) = TCINCO2; (CIN => CO3) = TCINCO3;
        (CIN => O0) = TCINO0; (CIN => O1) = TCINO1; (CIN => O2) = TCINO2; (CIN => O3) = TCINO3;
        (CYINIT => CO0) = TCYINITCO0; (CYINIT => CO1) = TCYINITCO1; (CYINIT => CO2) = TCYINITCO2; (CYINIT => CO3) = TCYINITCO3;
        (CYINIT => O0) = TCYINITO0; (CYINIT => O1) = TCYINITO1; (CYINIT => O2) = TCYINITO2; (CYINIT => O3) = TCYINITO3;
        (DI0 => CO0) = TDI0CO0; (DI0 => CO1) = TDI0CO1; (DI0 => CO2) = TDI0CO2; (DI0 => CO3) = TDI0CO3;
        (DI0 => O1) = TDI0O1; (DI0 => O2) = TDI0O2; (DI0 => O3) = TDI0O3; (DI1 => CO1) = TDI1CO1;
        (DI1 => CO2) = TDI1CO2; (DI1 => CO3) = TDI1CO3; (DI1 => O2) = TDI1O2; (DI1 => O3) = TDI1O3;
        (DI2 => CO2) = TDI2CO2; (DI2 => CO3) = TDI2CO3; (DI2 => O3) = TDI2O3; (DI3 => CO3) = TDI3CO3;
        (S0 => CO0) = TS0CO0; (S0 => CO1) = TS0CO1; (S0 => CO2) = TS0CO2; (S0 => CO3) = TS0CO3;
        (S0 => O0) = TS0O0; (S0 => O1) = TS0O1; (S0 => O2) = TS0O2; (S0 => O3) = TS0O3;
        (S1 => CO1) = TS1CO1; (S1 => CO2) = TS1CO2; (S1 => CO3) = TS1CO3; (S1 => O1) = TS1O1;
        (S1 => O2) = TS1O2; (S1 => O3) = TS1O3; (S2 => CO2) = TS2CO2; (S2 => CO3) = TS2CO3;
        (S2 => O2) = TS2O2; (S2 => O3) = TS2O3; (S3 => CO3) = TS3CO3; (S3 => O3) = TS3O3;
    endspecify
endmodule

// ---- BUFGCTRL -------------------------------------------------- BUFG bel --
// All three came from a plain BUFG (X_ORIG_TYPE), with IS_S1/IS_CE1/
// IS_IGNORE1_INVERTED set so the I1 half of the glitchless mux is permanently
// deselected.  Modelled as the buffer that configuration reduces to.
module BUFGCTRL (
    input  wire I0, I1, S0, S1, CE0, CE1, IGNORE0, IGNORE1,
    output wire O
);
    parameter TI0O = 200;
    assign O = I0;
    specify (I0 => O) = TI0O; endspecify
endmodule

// ---- BSCAN ------------------------------------------------------ BSCANE2 --
// Passive stub: SEL low, so the JTAG user-DR machine never activates, gcd_hw's
// hold register stays at its 12'h0 power-on value and the readback shifter
// never runs.  That is precisely the free-running, no-JTAG condition a
// software-driven sweep leaves the part in between scans.  The SDF carries no
// timing for this cell.
module BSCAN (
    input  wire TDO,
    output wire CAPTURE, DRCK, RESET, RUNTEST, SEL, SHIFT, TCK, TDI, TMS, UPDATE
);
    assign CAPTURE = 1'b0, DRCK = 1'b0, RESET = 1'b0, RUNTEST = 1'b0,
           SEL = 1'b0, SHIFT = 1'b0, TCK = 1'b0, TDI = 1'b0, TMS = 1'b0,
           UPDATE = 1'b0;
endmodule

// ---- pads ------------------------------------------------------------------
// No SDF timing for any of these.  PAD's port is an INTERCONNECT destination
// in this design (the OBUF drives it), so it is modelled as an input.
module PAD (input wire PAD);
endmodule

module IOB33_OUTBUF (input wire IN, output wire OUT);
    assign OUT = IN;
endmodule

module PSEUDO_GND (output wire Y); assign Y = 1'b0; endmodule
module PSEUDO_VCC (output wire Y); assign Y = 1'b1; endmodule

`default_nettype wire
