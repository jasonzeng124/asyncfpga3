// tb_bdc_memseq.v -- what a mem_controller's token release has to wait for.
//
// requires: build/gen/bdc_mem_units.v
//
// bdc/AUDIT.md section 7 records one assumption in the four-phase trace for a
// program-order token chain that could NOT be discharged by construction:
// releasing the token when `p_ack` falls races the previous station's `z_ack`
// fall.  The argument for it being safe was that the port path is roughly 20
// arcs against the consumer path's 2 -- which is a coincidence with good
// odds, not an argument.  This bench turns it into a measurement.
//
// WHY p_ack IS THE WRONG RELEASE POINT
//
// The station releases its operands from an asymmetric C-element,
//
//     hold = ~rst & (z_ack | (hold & p_ack))
//
// so `hold` -- and therefore `a_ack` -- falls only when z_ack AND p_ack are
// BOTH low.  p_ack is SHARED with every other station on the port.  A token
// released on p_ack alone can therefore start the next access while the
// previous station's consumer has not yet dropped z_ack, and the previous
// a_ack is still high.  If that next access is on the SAME station, its
// producer offers a new operand into an acknowledge that never fell, which
// is a four-phase violation on the a channel however healthy the data looks.
//
// So this bench issues repeated stores on ONE station and varies only where
// the sequencer waits:
//
//     default            release on a_ack falling      (the safe rule)
//     -DBDC_SEQ_EAGER    release on p_ack falling      (the questioned rule)
//
// and varies how slow the consumer is to return to zero, which is the term
// the "20 arcs against 2" argument is really about.  CONS_RTZ is that delay.
//
//     ./run_sim.sh tb_bdc_memseq
//
// The gate is not the data.  The data can be perfectly correct while the
// protocol is broken, which is the whole reason this file exists -- so the
// gate is a monitor on the a channel itself.

`timescale 1ps / 1ps

module tb_bdc_memseq;

    localparam integer AW = 10;
    localparam integer DW = 32;
    localparam integer H  = `BD_HOP_PS;
    localparam integer T  = 12 * H;

    localparam integer TSU = (`BD_RAM_TSU_DI > `BD_RAM_TSU_ADDR)
                             ? `BD_RAM_TSU_DI : `BD_RAM_TSU_ADDR;
    localparam integer DSETUP = (TSU + `BD_T_RISE - 1) / `BD_T_RISE - 1;
    localparam integer DCO    = (`BD_RAM_TCO + `BD_T_RISE - 1) / `BD_T_RISE;

    // How long the consumer sits on z_ack after the request has dropped.
    // This is the "2 arcs" in the argument being tested; make it comparable
    // to the port path and the argument has nothing left.
`ifndef BDC_SEQ_CONS_RTZ
 `define BDC_SEQ_CONS_RTZ (8 * H)
`endif
    localparam integer CONS_RTZ = `BDC_SEQ_CONS_RTZ;

    integer errors    = 0;
    integer i;
    integer naccess   = 0;
    integer nedges    = 0;
    integer noverlap  = 0;   // times an operand was offered into a live ack

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;

    reg              sa_req = 1'b0;   wire sa_ack;   reg [AW-1:0] sa_data = 0;
    reg              sd_req = 1'b0;   wire sd_ack;   reg [DW-1:0] sd_data = 0;
    wire             sz_req;          reg  sz_ack = 1'b0;

    reg              la_req = 1'b0;   wire la_ack;   reg [AW-1:0] la_data = 0;
    wire             lz_req;          reg  lz_ack = 1'b0;
    wire [DW-1:0]    lz_data;

    wire [1:0]         s_req, s_we;
    wire [2*AW-1:0]    s_addr;
    wire [2*DW-1:0]    s_wdata;
    wire               p_ack;
    wire [DW-1:0]      p_rdata;

    bdc_store_10_32 ust (
        .rst(rst),
        .a_req(sa_req), .a_ack(sa_ack), .a_data(sa_data),
        .d_req(sd_req), .d_ack(sd_ack), .d_data(sd_data),
        .z_req(sz_req), .z_ack(sz_ack),
        .p_req(s_req[0]), .p_ack(p_ack), .p_addr(s_addr[AW*0 +: AW]),
        .p_wdata(s_wdata[DW*0 +: DW]), .p_we(s_we[0]), .p_rdata(p_rdata));

    bdc_load_10_32 uld (
        .rst(rst),
        .a_req(la_req), .a_ack(la_ack), .a_data(la_data),
        .z_req(lz_req), .z_ack(lz_ack), .z_data(lz_data),
        .p_req(s_req[1]), .p_ack(p_ack), .p_addr(s_addr[AW*1 +: AW]),
        .p_wdata(s_wdata[DW*1 +: DW]), .p_we(s_we[1]), .p_rdata(p_rdata));

    bdc_memport_10_32_2 #(.DSETUP_0(DSETUP), .DCO_0(DCO),
                          .DSETUP_1(DSETUP), .DCO_1(DCO)) uport (
        .rst(rst), .s_req(s_req), .s_addr(s_addr), .s_wdata(s_wdata),
        .s_we(s_we), .p_ack(p_ack), .p_rdata(p_rdata));

    // -- THE GATE -----------------------------------------------------------
    // Four-phase on the a channel: an operand may only be offered into an
    // acknowledge that has already fallen.  This is the invariant the token
    // release rule is responsible for, and it is independent of whether the
    // data happens to come out right.
    reg watching = 1'b0;
    always @(posedge sa_req)
        if (watching && sa_ack !== 1'b0) begin
            noverlap = noverlap + 1;
            fail("store operand offered while its previous ack was still high");
        end
    always @(posedge la_req)
        if (watching && la_ack !== 1'b0) begin
            noverlap = noverlap + 1;
            fail("load operand offered while its previous ack was still high");
        end

    always @(posedge uport.umem0.ram_clk) nedges = nedges + 1;

    // -- the consumer, as its own process -----------------------------------
    // Inline in the sequencer it could never race anything; the point of the
    // experiment is that returning to zero takes the consumer real time.
    initial forever begin
        @(posedge sz_req);
        sz_ack = 1'b1;
        @(negedge sz_req);
        #(CONS_RTZ);
        sz_ack = 1'b0;
    end
    initial forever begin
        @(posedge lz_req);
        lz_ack = 1'b1;
        @(negedge lz_req);
        #(CONS_RTZ);
        lz_ack = 1'b0;
    end

    // -- the sequencer, which is what is actually under test ----------------
    task issue_store(input [AW-1:0] a, input [DW-1:0] d);
    begin
        sa_data = a;  sd_data = d;
        sa_req  = 1'b1;  sd_req = 1'b1;
        wait (sa_ack === 1'b1);
        sa_req  = 1'b0;  sd_req = 1'b0;
        naccess = naccess + 1;
`ifdef BDC_SEQ_EAGER
        wait (p_ack === 1'b0);
`else
        wait (sa_ack === 1'b0);
`endif
    end
    endtask

    reg [DW-1:0] got;
    task issue_load(input [AW-1:0] a);
    begin
        la_data = a;
        la_req  = 1'b1;
        wait (lz_req === 1'b1);
        got     = lz_data;
        wait (la_ack === 1'b1);
        la_req  = 1'b0;
        naccess = naccess + 1;
`ifdef BDC_SEQ_EAGER
        wait (p_ack === 1'b0);
`else
        wait (la_ack === 1'b0);
`endif
    end
    endtask

    initial begin
        $display("tb_bdc_memseq");
`ifdef BDC_SEQ_EAGER
        $display("  release rule: EAGER -- the token is released when p_ack falls");
`else
        $display("  release rule: SAFE -- the token is released when a_ack falls");
`endif
        $display("  consumer return-to-zero: %0d ps", CONS_RTZ);

        #(4 * T);  rst = 1'b0;  #(4 * T);
        watching = 1'b1;

        // Repeated stores on ONE station, which is the case the release rule
        // is responsible for: the same a channel, back to back.
        for (i = 0; i < 12; i = i + 1)
            issue_store(i[AW-1:0], {16'hC0D0 + i[15:0], 16'h0A00 + i[15:0]});

        // Then read them back, so a protocol failure that somehow left the
        // data intact is still distinguishable from one that did not.
        for (i = 0; i < 12; i = i + 1) begin
            issue_load(i[AW-1:0]);
            if (got !== {16'hC0D0 + i[15:0], 16'h0A00 + i[15:0]})
                fail("read back a word the sequence never stored");
        end

        $display("  %0d accesses issued, %0d manufactured clock edges at the RAM",
                 naccess, nedges);
        if (nedges != naccess)
            fail("the RAM did not see one rising edge per access");

        $display("  %0d operand(s) offered into a live acknowledge", noverlap);

        if (errors == 0) $display("tb_bdc_memseq PASS");
        else             $display("tb_bdc_memseq FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #(80000 * T);
        $display("  %0d accesses issued, %0d clock edges", naccess, nedges);
        $display("tb_bdc_memseq FAIL (timeout -- a station never returned to zero)");
        $finish;
    end

endmodule
