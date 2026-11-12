// tb_bdc_mem.v -- the memory station and its port, as bdc/mem.py generates them.
//
// requires: build/gen/bdc_mem_units.v
//
// Regenerate that file with:
//     python3 ../bdc/mem.py port:10:32:2 store:10:32 load:10:32 \
//             -o build/gen/bdc_mem_units.v
//
// WHY A STORE AND A LOAD ON ONE PORT, AND NOT A LOAD ON ITS OWN
//
// A RAMB18E1 powers up at zero and bd_mem has no INIT parameter, so a load
// with its own RAM reads a memory nothing ever wrote and would pass while
// proving nothing.  The only test that means anything is store-then-load
// through ONE port, which is why bdc/mem.py splits the port from the station.
//
// The testbench plays the part handshake's `mem_controller` will play: it
// sequences the two stations, one at a time, in program order.  What is under
// test is the station and the port, not the sequencer.
//
// THE CHECK THIS BENCH EXISTS FOR
//
// bd_mem's header names "pipelined return-to-zero overlap" as a failure this
// cell owns, and it is not a margin failure -- it is that a request rising
// while the manufactured clock is still high produces NO SECOND RISING EDGE,
// so the second access does not happen at all.  Nothing about the data would
// look wrong: the read returns the previous contents, which for a store-then-
// load test can easily be the value you expected.
//
// So the bench counts the RAM's own clock edges and compares them against the
// number of accesses issued.  A skipped access is then a number, not a guess.
// bdc/mem.py's header records reaching exactly that failure and what the fix
// is.  THE NEGATIVE CONTROL IS A SWITCH, not a hand edit, because a check that
// has never been seen to fail is not evidence:
//
//     BDC_MEM_NAIVE_ACK=1 python3 ../bdc/mem.py port:10:32:2 store:10:32 \
//             load:10:32 -o build/gen/bdc_mem_units.v
//     ./run_sim.sh tb_bdc_mem
//
// ties the operand acknowledges straight to z_ack -- what bd_join would do --
// and this bench then reports, from the first handover onwards:
//
//     FAIL load address released while the port was still acknowledging
//     FAIL a request rose while the port had not returned to zero
//
// Regenerate without the flag before doing anything else; a naive file left in
// build/gen is a design that does not work.

`timescale 1ps / 1ps

module tb_bdc_mem;

    localparam integer AW = 10;
    localparam integer DW = 32;
    localparam integer H  = `BD_HOP_PS;
    localparam integer T  = 12 * H;

    // Sized from the vendor numbers, exactly as tb_mem does it -- not from a
    // constant typed into this file.  Post-route sizing replaces both.
    localparam integer TSU = (`BD_RAM_TSU_DI > `BD_RAM_TSU_ADDR)
                             ? `BD_RAM_TSU_DI : `BD_RAM_TSU_ADDR;
    localparam integer DSETUP = (TSU + `BD_T_RISE - 1) / `BD_T_RISE - 1;
    localparam integer DCO    = (`BD_RAM_TCO + `BD_T_RISE - 1) / `BD_T_RISE;

    integer errors = 0;
    integer i;
    integer naccess = 0;      // accesses this bench issued
    integer nedges  = 0;      // rising edges the RAM actually saw

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;

    // -- the store station's channels ---------------------------------------
    reg              sa_req = 1'b0;   wire sa_ack;   reg [AW-1:0] sa_data = 0;
    reg              sd_req = 1'b0;   wire sd_ack;   reg [DW-1:0] sd_data = 0;
    wire             sz_req;          reg  sz_ack = 1'b0;

    // -- the load station's channels ----------------------------------------
    reg              la_req = 1'b0;   wire la_ack;   reg [AW-1:0] la_data = 0;
    wire             lz_req;          reg  lz_ack = 1'b0;
    wire [DW-1:0]    lz_data;

    // -- the shared port ----------------------------------------------------
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

    // The same slot signals into a port with no setup delay at all.  Nothing
    // waits on its acknowledge; it exists so the setup check has teeth, the
    // way tb_mem's `bad` instance does.
    wire bad_ack;  wire [DW-1:0] bad_rdata;
    bdc_memport_10_32_2 #(.DSETUP_0(0), .DCO_0(DCO),
                          .DSETUP_1(0), .DCO_1(DCO)) ubad (
        .rst(rst), .s_req(s_req), .s_addr(s_addr), .s_wdata(s_wdata),
        .s_we(s_we), .p_ack(bad_ack), .p_rdata(bad_rdata));

    // -- the return-to-zero monitor -----------------------------------------
    wire m_req = |s_req;
    always @(posedge m_req)
        if (p_ack !== 1'b0)
            fail("a request rose while the port had not returned to zero");

    // The manufactured clock edge, counted at the RAM itself.  This is the
    // observable that a skipped access shows up in and nothing else does.
    always @(posedge uport.umem0.ram_clk) nedges = nedges + 1;

    // -- the payload must still be there AFTER the edge ---------------------
    //
    // Rule B (verify/tighten.py) checks that address/data arrive BEFORE the
    // manufactured clock rises.  Nothing checks that they are still there
    // long enough after it, and the release path runs clock-fall -> DCO ->
    // p_ack -> the station's hold C-element -> the producer.  DCO is
    // therefore the hold guard too, and rule C sizes it for clock-to-out
    // alone.  Measure it rather than argue it.
    time    t_edge = 0;
    reg     watching = 1'b0;
    integer hold_addr_min = 1000000;
    integer hold_di_min   = 1000000;
    always @(posedge uport.umem0.ram_clk) t_edge = $time;
    always @(uport.umem0.addr)
        if (watching && t_edge != 0 && ($time - t_edge) < hold_addr_min)
            hold_addr_min = $time - t_edge;
    always @(uport.umem0.wdata)
        if (watching && t_edge != 0 && ($time - t_edge) < hold_di_min)
            hold_di_min = $time - t_edge;

    // -- the acknowledge must still follow the read data --------------------
    time    t_data = 0;
    integer co_margin_min = 1000000;
    always @(p_rdata) if (watching) t_data = $time;
    always @(posedge p_ack) if (watching && t_data != 0)
        if (($time - t_data) < co_margin_min) co_margin_min = $time - t_data;

    // -- one four-phase access through a station ----------------------------
    task do_store(input [AW-1:0] a, input [DW-1:0] d);
    begin
        sa_data = a;  sd_data = d;
        sa_req  = 1'b1;  sd_req = 1'b1;
        wait (sz_req === 1'b1);          // the port answered
        sz_ack  = 1'b1;                  // the completion was taken
        wait (sa_ack === 1'b1);
        sa_req  = 1'b0;  sd_req = 1'b0;  // release the operands
        wait (sz_req === 1'b0);
        sz_ack  = 1'b0;
        // The producer is not free until the acknowledge FALLS, and that is
        // the whole point: it falls when the port is quiet, not when the
        // consumer finished.
        wait (sa_ack === 1'b0);
        if (p_ack !== 1'b0)
            fail("store operands released while the port was still acknowledging");
        naccess = naccess + 1;
    end
    endtask

    reg [DW-1:0] got;
    task do_load(input [AW-1:0] a);
    begin
        la_data = a;
        la_req  = 1'b1;
        wait (lz_req === 1'b1);
        got     = lz_data;
        lz_ack  = 1'b1;
        wait (la_ack === 1'b1);
        la_req  = 1'b0;
        wait (lz_req === 1'b0);
        lz_ack  = 1'b0;
        wait (la_ack === 1'b0);
        if (p_ack !== 1'b0)
            fail("load address released while the port was still acknowledging");
        naccess = naccess + 1;
    end
    endtask

    initial begin
        $display("tb_bdc_mem");
        $display("  sized from the vendor numbers: DSETUP=%0d, DCO=%0d (one rise arc = %0d ps)",
                 DSETUP, DCO, `BD_T_RISE);

        #(4 * T);  rst = 1'b0;  #(4 * T);
        watching = 1'b1;

        // -- a pattern, stored then read back -------------------------------
        // 32 bits across two RAMs: the halves must not swap, and the upper
        // half must not be the lower half's shadow, so every word differs in
        // both halves and the halves are not equal to each other.
        for (i = 0; i < 16; i = i + 1)
            do_store(i[AW-1:0], {16'hBEE0 + i[15:0], 16'h0F00 + i[15:0]});

        for (i = 0; i < 16; i = i + 1) begin
            do_load(i[AW-1:0]);
            if (got !== {16'hBEE0 + i[15:0], 16'h0F00 + i[15:0]}) begin
                errors = errors + 1;
                $display("  FAIL word %0d: read %h expected %h",
                         i, got, {16'hBEE0 + i[15:0], 16'h0F00 + i[15:0]});
            end
        end

        // -- alternating store and load on the same port --------------------
        // Two stations taking the port in turn is the case the one-hot mux and
        // the return-to-zero hold both exist for; running them in blocks would
        // never exercise a handover.
        for (i = 0; i < 8; i = i + 1) begin
            do_store(10'd100 + i[AW-1:0], 32'hA5A50000 + i);
            do_load(10'd100 + i[AW-1:0]);
            if (got !== 32'hA5A50000 + i)
                fail("interleaved store/load did not round-trip");
            do_load(i[AW-1:0]);   // and the earlier block is undisturbed
            if (got !== {16'hBEE0 + i[15:0], 16'h0F00 + i[15:0]})
                fail("an interleaved access disturbed an earlier word");
        end

        // -- overwrite, and check the neighbours ----------------------------
        do_store(10'd7, 32'hDEADBEEF);
        do_load(10'd7);
        if (got !== 32'hDEADBEEF) fail("overwrite did not take");
        do_load(10'd6);
        if (got !== {16'hBEE6, 16'h0F06}) fail("neighbour below was disturbed");
        do_load(10'd8);
        if (got !== {16'hBEE8, 16'h0F08}) fail("neighbour above was disturbed");

        // -- the gates ------------------------------------------------------
        $display("  %0d accesses issued, %0d manufactured clock edges at the RAM",
                 naccess, nedges);
        if (nedges != naccess)
            fail("the RAM did not see one rising edge per access -- an access was swallowed");

        $display("  acknowledge follows read data by at least %0d ps (t_co is %0d ps)",
                 co_margin_min, `BD_RAM_TCO);
        if (co_margin_min <= 0)
            fail("acknowledge arrived before the read data settled");

        $display("  payload held after the edge: addr %0d ps (need %0d), data %0d ps (need %0d)",
                 hold_addr_min, `BD_RAM_THOLD_ADDR, hold_di_min, `BD_RAM_THOLD_DI);
        if (hold_addr_min < `BD_RAM_THOLD_ADDR)
            fail("the address changed too soon after the manufactured clock edge");
        if (hold_di_min < `BD_RAM_THOLD_DI)
            fail("the write data changed too soon after the clock edge");

        $display("  sized port:     %0d + %0d setup violations at the RAM boundary",
                 uport.umem0.uram.violations, uport.umem1.uram.violations);
        $display("  DSETUP(0) port: %0d + %0d",
                 ubad.umem0.uram.violations, ubad.umem1.uram.violations);

        if (uport.umem0.uram.violations != 0 || uport.umem1.uram.violations != 0)
            fail("the sized port violated the RAM's setup window");
        if (ubad.umem0.uram.violations == 0 && ubad.umem1.uram.violations == 0)
            fail("the DSETUP(0) port showed no violation -- the gate has no teeth");

        if (errors == 0) $display("tb_bdc_mem PASS");
        else             $display("tb_bdc_mem FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #500_000_000;
        $display("tb_bdc_mem FAIL (timeout, %0d accesses, %0d edges)", naccess, nedges);
        $finish;
    end
endmodule
