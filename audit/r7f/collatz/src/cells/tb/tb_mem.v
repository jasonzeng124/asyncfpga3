// tb_mem.v -- the memory port, where the request manufactures the clock edge.
//
// This is the one place in the library where simulation can see a bundling
// violation, because it is the one place with a vendor primitive that has
// real setup numbers.  The RAM model carries prjxray's BRAM_L.sdf figures and
// enforces them, so an undersized matched delay is a message in the log
// rather than something only silicon would find.
//
// The bench presents address, write data, write enable AND the request in the
// same instant.  That is the worst case and it is also the honest one: at the
// cell's boundary the payload and the request arrive together, and DSETUP is
// the only thing standing between them and the RAM's setup window.  A bench
// that set the address early would pass with DSETUP = 0 and prove nothing.
//
// Both delays are sized here FROM THE VENDOR NUMBERS, not from a constant
// typed into the source -- ceil(t_su / one rise arc) and ceil(t_co / one rise
// arc).  Run at BD_ROUTE_PS = 0 that comes out at 14 links of setup and 44 of
// clock-to-out; run at 354 it comes out at 2 and 6.  Same expression, and the
// ratio is the arc-only-versus-routed gap the design review warns about.
// Neither number is a design constant: post-route sizing replaces both.

`timescale 1ps / 1ps

module tb_mem;

    localparam integer AW = 10;
    localparam integer DW = 16;
    localparam integer H  = `BD_HOP_PS;
    localparam integer T  = 12 * H;

    // The largest of the three setup windows is what the delay must cover.
    localparam integer TSU = (`BD_RAM_TSU_DI > `BD_RAM_TSU_ADDR)
                             ? `BD_RAM_TSU_DI : `BD_RAM_TSU_ADDR;
    // One rise arc is already spent in the explicit clock buffer, so the
    // chain needs one fewer than the total.
    localparam integer DSETUP = (TSU + `BD_T_RISE - 1) / `BD_T_RISE - 1;
    localparam integer DCO    = (`BD_RAM_TCO + `BD_T_RISE - 1) / `BD_T_RISE;

    integer errors = 0;
    integer i;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg              req   = 1'b0;
    reg  [AW-1:0]    addr  = 0;
    reg  [DW-1:0]    wdata = 0;
    reg              we    = 1'b0;
    wire             ack;
    wire [DW-1:0]    rdata;

    bd_mem #(.AW(AW), .DW(DW), .DSETUP(DSETUP), .DCO(DCO), .USE_BUFG(0)) dut (
        .req(req), .ack(ack), .addr(addr), .wdata(wdata), .we(we),
        .rdata(rdata));

    // The same port with no setup delay at all, driven by the same signals.
    // Nothing waits on its acknowledge; it exists so the check has teeth.
    wire bad_ack;  wire [DW-1:0] bad_rdata;
    bd_mem #(.AW(AW), .DW(DW), .DSETUP(0), .DCO(DCO), .USE_BUFG(0)) bad (
        .req(req), .ack(bad_ack), .addr(addr), .wdata(wdata), .we(we),
        .rdata(bad_rdata));

    // And the BUFG variant, to confirm it elaborates and works.  BUFG is
    // deliberately zero-delay in the model -- a real one is about two
    // nanoseconds, which is exactly the failure bd_mem's header is about, and
    // pretending otherwise in simulation would hide it -- so this instance
    // pays one more link to make up the arc the LUT buffer would have cost.
    wire g_ack;  wire [DW-1:0] g_rdata;
    bd_mem #(.AW(AW), .DW(DW), .DSETUP(DSETUP+1), .DCO(DCO), .USE_BUFG(1)) gbuf (
        .req(req), .ack(g_ack), .addr(addr), .wdata(wdata), .we(we),
        .rdata(g_rdata));

    // -- the acknowledge must follow the read data --------------------------
    // The whole purpose of DCO.  Measured, not assumed.
    time t_data = 0;
    integer co_margin_min = 1000000;
    reg watching = 1'b0;
    always @(rdata) if (watching) t_data = $time;
    always @(posedge ack) if (watching && t_data != 0)
        if (($time - t_data) < co_margin_min) co_margin_min = $time - t_data;

    // -- one four-phase access ----------------------------------------------
    // Payload and request in the same instant, deliberately.
    reg [DW-1:0] got;
    task access(input [AW-1:0] a, input [DW-1:0] d, input w);
    begin
        addr  = a;
        wdata = d;
        we    = w;
        req   = 1'b1;
        wait (ack === 1'b1);
        got   = rdata;
        req   = 1'b0;
        wait (ack === 1'b0);
        #(2 * T);
    end
    endtask

    initial begin
        $display("tb_mem");
        $display("  sized from the vendor numbers: DSETUP=%0d, DCO=%0d (one rise arc = %0d ps)",
                 DSETUP, DCO, `BD_T_RISE);

        #(2 * T);
        watching = 1'b1;

        // -- write a pattern ------------------------------------------------
        for (i = 0; i < 16; i = i + 1)
            access(i[AW-1:0], 16'hC000 + i[15:0], 1'b1);

        // -- read it back ---------------------------------------------------
        for (i = 0; i < 16; i = i + 1) begin
            access(i[AW-1:0], 16'h0000, 1'b0);
            if (got !== (16'hC000 + i[15:0])) begin
                errors = errors + 1;
                $display("  FAIL word %0d: read %h expected %h",
                         i, got, 16'hC000 + i[15:0]);
            end
        end

        // -- overwrite one word and read the neighbours ---------------------
        access(10'd7, 16'hBEEF, 1'b1);
        access(10'd7, 16'h0000, 1'b0);
        if (got !== 16'hBEEF) fail("overwrite did not take");
        access(10'd6, 16'h0000, 1'b0);
        if (got !== 16'hC006) fail("neighbour below was disturbed");
        access(10'd8, 16'h0000, 1'b0);
        if (got !== 16'hC008) fail("neighbour above was disturbed");

        // -- the two gates ---------------------------------------------------
        $display("  acknowledge follows read data by at least %0d ps (t_co is %0d ps)",
                 co_margin_min, `BD_RAM_TCO);
        if (co_margin_min <= 0)
            fail("acknowledge arrived before the read data settled");

        $display("  sized port:     %0d setup violations at the RAM boundary",
                 dut.uram.violations);
        $display("  BUFG port:      %0d", gbuf.uram.violations);
        $display("  DSETUP(0) port: %0d", bad.uram.violations);

        if (dut.uram.violations != 0)
            fail("the sized port violated the RAM's setup window");
        if (gbuf.uram.violations != 0)
            fail("the BUFG port violated the RAM's setup window");
        if (bad.uram.violations == 0)
            fail("the DSETUP(0) port showed no violation -- the gate has no teeth");

        if (errors == 0) $display("tb_mem PASS");
        else             $display("tb_mem FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #200_000_000;
        $display("tb_mem FAIL (timeout)");
        $finish;
    end
endmodule
