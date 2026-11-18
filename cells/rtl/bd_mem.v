// ---------------------------------------------------------------------------
// bd_mem.v -- memory port.  The request manufactures the clock edge.
//
// SECOND HIGHEST RISK CELL.  Two matched delays: address and write-data setup
// before the manufactured edge, and clock-to-out before the acknowledge.
//
//     req --[ delta DSETUP ]--[ buffer ]--+--> RAMB18E1.CLK
//                                         |
//                                         +--[ delta DCO ]--> ack
//
// -- failure modes this cell owns -------------------------------------------
//
//   Automatic clock buffering.  yosys inserts a global buffer on anything
//   that looks like a clock pin, unasked.  Roughly two nanoseconds arrive on
//   a path a matched delay was sized against, and capture lands after the
//   acknowledge.  Simulation never shows it -- there is no buffer in the
//   simulation model.
//
//   Pipelined return-to-zero overlap.  Back-to-back accesses whose reset
//   phases overlap corrupt the port.  Known history of being misdiagnosed as
//   a margin problem and "fixed" by scaling guard delays, which never worked
//   because the mechanism is sequencing, not timing.
//
//   Vacuous audit.  If the structural audit treats a clock buffer as a
//   zero-depth source it truncates the strobe cone, reports a request arrival
//   of zero, and passes.
//
// -- design rules this cell implements --------------------------------------
//
//   Instantiate every buffer explicitly; never let a pass infer one.  The
//   USE_BUFG parameter picks which buffer exists, and there is always exactly
//   one named driver of the clock net.  With USE_BUFG = 0 the net carries
//   (* clkbuf_inhibit *) and the flow additionally passes -noclkbuf.
//
//   Keep the capture edge and the timing tap downstream of the same buffer.
//   ram_clk below is that single net; both the RAM and the acknowledge delay
//   read it.
//
//   Audit the RAM boundary as a bundling boundary: CLK is the request,
//   address and write data are the payload, same depth-slack rule as a latch.
//
//   Serialise accesses until the return-to-zero phase is proven complete.
//   Treat the port as a shared resource with a full four-phase cycle, not a
//   pipelined element.  A second read port is a second copy of this
//   structure; sharing one port between two requesters needs bd_arbiter.
//
// NOTE -- the schematic labels the stage between the setup delay and the RAM
// "pulse" without specifying its internals.  It is built here as the single
// explicit buffer the design rules demand, so CLK is high for as long as req
// is and the acknowledge is a level rather than a pulse.  Narrowing it into a
// true one-shot would make ack a pulse, which is not a four-phase
// acknowledge.
// ---------------------------------------------------------------------------

`default_nettype none

module bd_mem #(parameter AW      = 10,   // word address bits (RAMB18, x16)
                parameter DW      = 16,
                parameter DSETUP  = 8,    // placeholder: sized post-route
                parameter DCO     = 12,   // placeholder: sized post-route
                parameter USE_BUFG = 0)
    (input  wire             req,
     output wire             ack,
     input  wire [AW-1:0]    addr,
     input  wire [DW-1:0]    wdata,
     input  wire             we,
     output wire [DW-1:0]    rdata);

    // Address and write data are the payload; this delay is the bundling
    // guardband at the RAM boundary.
    wire strobe;
    bd_delay #(.N(DSETUP)) usetup (.a(req), .z(strobe));

    // Exactly one explicit driver of the clock net.  Nothing else may drive
    // it and no pass may insert anything into it.
    (* clkbuf_inhibit *) wire ram_clk;
    generate
        if (USE_BUFG) begin : gbufg
            BUFG ubuf (.I(strobe), .O(ram_clk));
        end else begin : gplain
            (* keep *) LUT1 #(.INIT(2'h2)) ubuf (.I0(strobe), .O(ram_clk));
        end
    endgenerate

    // The timing tap is downstream of the same buffer, on the same net.
    bd_delay #(.N(DCO)) uco (.a(ram_clk), .z(ack));

    wire [13:0] a14;
    assign a14 = {addr, 4'b0000};        // x18 port: word address is [13:4]

    RAMB18E1 #(.RAM_MODE("TDP"),
               .READ_WIDTH_A(18), .WRITE_WIDTH_A(18),
               .READ_WIDTH_B(0),  .WRITE_WIDTH_B(0),
               .DOA_REG(0), .DOB_REG(0),
               .WRITE_MODE_A("WRITE_FIRST"), .WRITE_MODE_B("WRITE_FIRST"),
               .SIM_DEVICE("7SERIES"))
        uram (
            .CLKARDCLK(ram_clk),      .CLKBWRCLK(1'b0),
            .ENARDEN(1'b1),           .ENBWREN(1'b0),
            .REGCEAREGCE(1'b0),       .REGCEB(1'b0),
            .RSTRAMARSTRAM(1'b0),     .RSTRAMB(1'b0),
            .RSTREGARSTREG(1'b0),     .RSTREGB(1'b0),
            .ADDRARDADDR(a14),        .ADDRBWRADDR(14'b0),
            .DIADI(wdata),            .DIBDI(16'b0),
            .DIPADIP(2'b0),           .DIPBDIP(2'b0),
            .WEA({2{we}}),            .WEBWE(4'b0),
            .DOADO(rdata),            .DOBDO(),
            .DOPADOP(),               .DOPBDOP());
endmodule

`default_nettype wire
