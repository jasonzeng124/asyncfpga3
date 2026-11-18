// ---------------------------------------------------------------------------
// rtl/optin/bd_mem_ff.v -- bd_mem (rtl/bd_mem.v) with both of its lines FASTFALL.
//
// The same cell, port for port, parameter for parameter and instance name for
// instance name (usetup, gplain.ubuf / gbufg.ubuf, uco, uram), so the sizing
// macros, verify/tighten.py rules B and C, corner_audit and the GLS RAM model
// treat it exactly as bd_mem.  The one difference: usetup and uco are
// bd_delay FASTFALL lines -- they RISE through DSETUP and DCO elements and
// FALL one element after their input.  bdc/mem.py instantiates it in place of
// bd_mem only under BDC_MEM_FASTFALL=1 (research/data/suite/memauto.md).
//
// Why a second module and not a parameter of bd_mem: a FASTFALL parameter on
// bd_mem, passed to its bd_delays, changed the routed netlist of a build that
// left it at 0 (farm memsum seed 1, route 6 rebuilt from its own sizes: SDF
// 0aeee7a1 with bd_mem.v as it was, 73576845 with the parameter added; gather
// seed 2 happened to come out identical) -- yosys names a derived module after
// the parameters given, so an explicit .FASTFALL(0) is a different module.
// bd_mem.v is left byte for byte as it was, and this file is NOT under rtl/*.v:
// a module merely present there (unused) changed the same route again
// (0aeee7a1 -> d63c74bf) -- every module read moves yosys's global auto-name
// counter, the names move, and nextpnr's placement with them.  So
// hw/build_bench.sh reads rtl/optin/bd_mem_ff.v only for a kernel that
// instantiates bd_mem_ff; every other build reads exactly the files it read
// before, and every netlist built without BDC_MEM_FASTFALL=1 is unchanged.
//
// Why the falls carry no obligation.  The RAM samples only the RISING edge of
// ram_clk: address / data / we setup (DSETUP) and clock-to-out (DCO) are
// rising-edge constraints and keep their full lines.  The return to zero is
// sequencing, and its order is kept by construction, not by length: every uco
// element is ANDed with ram_clk, so ack cannot fall before ram_clk has fallen
// at the line, and the station (bdc/mem.py `hold`) releases its operands --
// the only way a next request can rise -- only after the port's ack has
// fallen.  So the next rising edge still needs the whole handshake plus a full
// DSETUP rise after ram_clk fell: ram_clk's low phase is at least DSETUP's
// rise, its high phase at least DCO's rise (the request falls only after ack
// rose).  Address hold: the address is released one arc after ack falls, so
// at least pulse_high >= DCO's rise after the capture edge (bd_mem gives 2 x
// DCO; verify/tighten.py rule C states that 2x bound, which overstates here).
// What the line does change: a short low glitch on req would become a full
// clean low phase and a second rising edge (bd_mem passes it on as a glitch).
// req is the port's one-hot OR of station claims (p_req = joined & ~done) and
// of the bench's host slot, neither of which pulses low while high.  The GLS
// RAM model checks setup / hold windows but not the clock's minimum pulse
// width; the phases measured on gather's event graphs are 11-18 ns high and
// 37-42 ns low, an order above any RAMB18 minimum pulse width.
// ---------------------------------------------------------------------------

`default_nettype none

module bd_mem_ff #(parameter AW      = 10,   // word address bits (RAMB18, x16)
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
    bd_delay #(.N(DSETUP), .FASTFALL(1)) usetup (.a(req), .z(strobe));

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
    bd_delay #(.N(DCO), .FASTFALL(1)) uco (.a(ram_clk), .z(ack));

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
