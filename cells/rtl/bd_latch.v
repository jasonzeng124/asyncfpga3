// ---------------------------------------------------------------------------
// bd_latch.v -- transparent-high D-latch, and the matched delay line.
//
// Storage without a clock edge.  EN = 1 -> Q follows D; EN = 0 -> Q holds.
// The enable is not a clock: it comes from the local handshake, and the latch
// stays transparent for as long as it is high.
//
// Two bits share {EN, D_i, Q_i, D_j, Q_j} -- exactly five distinct inputs, so
// storage costs half a LUT per bit on a fractured LUT6_2.
//
// The storage is on LUTs, not on the slice's LDCE.  The reason is routing:
// LDCE.G lands on the slice clock pin (prjxray puts it in the FDRE.C column),
// reachable only through an interconnect tile's two CLK wires, each with four
// fabric sources.  A self-timed pipeline wants one locally generated enable
// per stage and stages are dense, so that per-tile ceiling is the
// disqualifier.  Keeping storage on LUTs also keeps the latch and the delay
// line on the same primitive, so the two track each other across voltage and
// temperature.
// ---------------------------------------------------------------------------

`default_nettype none

// -- plain variant, no reset ---------------------------------- W/2 LUTs ----
// The default, and what the whole datapath uses.  req is what makes data
// meaningful, so nothing reads a latch before its own request arrives and
// arbitrary power-up contents are never observed.
//
// Do not carry an initial token in one: an initial token is by definition
// read before anything has written it.
module bd_latch #(parameter W = 8)
                 (input wire [W-1:0] d, input wire en, output wire [W-1:0] q);
    genvar i;
    generate
        for (i = 0; i + 1 < W; i = i + 2) begin : pair
            (* keep *) LUT6_2 #(.INIT(64'hFF33_CC00_B8B8_B8B8)) u (
                .I0(d[i]),   .I1(en),     .I2(q[i]),
                .I3(d[i+1]), .I4(q[i+1]), .I5(1'b1),
                .O5(q[i]),   .O6(q[i+1]));
        end
        if (W % 2) begin : odd
            (* keep *) LUT6 #(.INIT(64'hB8B8_B8B8_B8B8_B8B8)) u (
                .I0(d[W-1]), .I1(en), .I2(q[W-1]),
                .I3(1'b0), .I4(1'b0), .I5(1'b0), .O(q[W-1]));
        end
    endgenerate
endmodule

// -- resettable variant ---------------------------------------- W LUTs -----
// rst folds into the feedback loop: {D, EN, Q, rst}.  That is a sixth pin on
// the pair, so the pair breaks and the bit costs a full LUT.  Affordable for
// a control bit, not for a word -- use it only where an initial value is
// genuinely read before anything writes it, which in practice means a loop's
// initial token.
module bd_latch_rst #(parameter W = 1, parameter [63:0] RESET_VALUE = 64'd0)
                     (input wire [W-1:0] d, input wire en, input wire rst,
                      output wire [W-1:0] q);
    genvar i;
    generate
        for (i = 0; i < W; i = i + 1) begin : gbit
            // Reset polarity is per bit: 16'h00B8 clears, 16'hFFB8 presets.
            localparam [63:0] INITB = RESET_VALUE[i] ? 64'hFFB8_FFB8_FFB8_FFB8
                                                     : 64'h00B8_00B8_00B8_00B8;
            (* keep *) LUT6 #(.INIT(INITB)) u (
                .I0(d[i]), .I1(en), .I2(q[i]), .I3(rst),
                .I4(1'b0), .I5(1'b0), .O(q[i]));
        end
    endgenerate
endmodule

// ---------------------------------------------------------------------------
// bd_delay -- matched delay line.
//
// N is a PLACEHOLDER.  Chain depth is tightened unconditionally after
// place-and-route from measured routed arrival times, never from source
// structure, a synthesis estimate or abc9's timing model.  The pass tightens;
// it never pads.
//
// A matched delay covers combinational logic inside one cell's own datapath,
// where there is no request to wait on.  That is the whole licence.  If you
// are reaching for one so a request will wait for a computation happening
// elsewhere, you want a fork and a join instead.
//
// Built from the same LUT primitive as the datapath it covers, so the two
// track each other across PVT.
//
// FASTFALL keeps the rising edge matched through N hops but lets the falling
// edge flush the chain in one LUT delay.  It is permitted only for consumers
// whose latch is transparent during the request rise/fall window; do not use
// it for edge-sampling consumers such as bd_mem's usetup or uco.
//
// FASTRISE is the mirror image (every stage an OR with the input): the fall
// takes N hops and the rise flushes in one.  It is the shape of an
// acknowledge delay, where only the fall -- the end of the sender's hold
// window -- has to be held back.
// ---------------------------------------------------------------------------
`ifdef __ICARUS__
`define BD_DELAY_SYM_CHAIN chain_sym
`define BD_DELAY_FAST_CHAIN chain_fast
`define BD_DELAY_SYM_G g_sym
`define BD_DELAY_FAST_G0 g_fast0
`define BD_DELAY_FAST_G1 g_fast1
`else
`define BD_DELAY_SYM_CHAIN chain
`define BD_DELAY_FAST_CHAIN chain
`define BD_DELAY_SYM_G g
`define BD_DELAY_FAST_G0 g
`define BD_DELAY_FAST_G1 g
`endif
module bd_delay #(parameter N = 4, parameter FASTFALL = 0,
                  parameter FASTRISE = 0)
                 (input wire a, output wire z);
    // AND with the input flushes the fall; OR with it flushes the rise.
    localparam [3:0] SIDE_INIT = FASTRISE ? 4'hE : 4'h8;
    generate
        if (N == 0) begin : bypass
            assign z = a;
        end
        if (N != 0 && !FASTFALL && !FASTRISE) begin : `BD_DELAY_SYM_CHAIN
            (* keep *) wire [N:0] s;
            assign s[0] = a;
            genvar i;
            for (i = 0; i < N; i = i + 1) begin : `BD_DELAY_SYM_G
                (* keep *) LUT1 #(.INIT(2'h2)) u (.I0(s[i]), .O(s[i+1]));
            end
            assign z = s[N];
        end
        if (N != 0 && (FASTFALL || FASTRISE)) begin : `BD_DELAY_FAST_CHAIN
            (* keep *) wire [N:0] s;
            assign s[0] = a;
            genvar i;
            for (i = 0; i < 1; i = i + 1) begin : `BD_DELAY_FAST_G0
                (* keep *) LUT1 #(.INIT(2'h2)) u (.I0(s[i]), .O(s[i+1]));
            end
            for (i = 1; i < N; i = i + 1) begin : `BD_DELAY_FAST_G1
                (* keep *) LUT2 #(.INIT(SIDE_INIT)) u (
                    .I0(s[i]), .I1(a), .O(s[i+1]));
            end
            assign z = s[N];
        end
    endgenerate
endmodule
`undef BD_DELAY_SYM_CHAIN
`undef BD_DELAY_FAST_CHAIN
`undef BD_DELAY_SYM_G
`undef BD_DELAY_FAST_G0
`undef BD_DELAY_FAST_G1

// ---------------------------------------------------------------------------
// bd_datamux -- z = s ? b : a, two bits to a fractured LUT6_2.
//
// {sel, x_i, y_i, x_j, y_j} is five distinct inputs, so W/2 LUTs.  Shared by
// the merge (sel ? x : y) and the mux (s ? y : x); the two differ only in
// which channel is wired to which port.
// ---------------------------------------------------------------------------
module bd_datamux #(parameter W = 8)
                   (input wire [W-1:0] a, input wire [W-1:0] b,
                    input wire s, output wire [W-1:0] z);
    genvar i;
    generate
        for (i = 0; i + 1 < W; i = i + 2) begin : pair
            LUT6_2 #(.INIT(64'hFFAA_5500_E4E4_E4E4)) u (
                .I0(s),      .I1(a[i]),   .I2(b[i]),
                .I3(a[i+1]), .I4(b[i+1]), .I5(1'b1),
                .O5(z[i]),   .O6(z[i+1]));
        end
        if (W % 2) begin : odd
            LUT3 #(.INIT(8'hE4)) u (
                .I0(s), .I1(a[W-1]), .I2(b[W-1]), .O(z[W-1]));
        end
    endgenerate
endmodule

`default_nettype wire
