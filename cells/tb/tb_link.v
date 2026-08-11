// tb_link.v -- the simple Muller pipeline: occupancy, ordering, and data
// integrity through a stall.
//
// Occupancy is measured, not counted by the testbench: the sink is stalled,
// a free-running source pushes until it blocks, and what the source managed
// to complete IS the occupancy.  This matters because the obvious testbench
// -- push, and retract the request if nothing acknowledges -- is itself a
// protocol violation.  A four-phase sender may not withdraw a request that
// has not been acknowledged; there is no timeout in this protocol, and a
// testbench that uses one is testing a different protocol than the library
// implements.  Blocking forever is the correct behaviour of a full pipe, and
// the source blocking forever is how this bench observes it.

`timescale 1ps / 1ps

module tb_link;

    localparam integer W = 8;
    localparam integer N = 4;
    localparam integer H = `BD_HOP_PS;
    localparam integer TOTAL = 24;

    integer errors = 0;
    integer i;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;

    wire         req_in, ack_in;
    wire [W-1:0] data_in;
    wire         req_out, ack_out;
    wire [W-1:0] data_out;

    bd_source #(.W(W)) src (.req(req_in), .ack(ack_in), .data(data_in));

    bd_pipe #(.W(W), .N(N)) dut (
        .rst(rst),
        .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
        .req_out(req_out), .ack_out(ack_out), .data_out(data_out));

    bd_sink #(.W(W)) snk (.req(req_out), .ack(ack_out), .data(data_out));

    // The input channel is driven by a testbench source, so data genuinely
    // precedes the request and SETTLE stays 0.  The output channel is a
    // pipeline node, where the control wave outruns the data wave by up to one
    // latch arc per stage traversed -- see the header of rtl/bd_link.v.  That
    // bound, N latch arcs, is the tolerance; anything past it is a real
    // hold-window violation and still fails.
    bd_monitor #(.W(W), .CHAN("pipe-in"))                      mi
        (.req(req_in),  .ack(ack_in),  .data(data_in));
    bd_monitor #(.W(W), .CHAN("pipe-out"), .SETTLE(N*`BD_T_FALL)) mo
        (.req(req_out), .ack(ack_out), .data(data_out));

    // -- the same pipe with its outgoing request padded ---------------------
    // DELAY is the remedy the cell header prescribes for an edge-sampling
    // consumer.  Sized from the measured lead: verify/probes/pipe_skew.v puts it at
    // 441 ps on an empty four-stage pipe, and a LUT1 rise arc is 56 ps, so
    // eight links clear it and ten leave margin.  The point of this instance
    // is that its monitor runs with SETTLE(0) -- the strict bundled-data rule,
    // data valid before req -- and must still pass.
    localparam integer PAD = 10;

    wire         preq_in, pack_in;
    wire [W-1:0] pdata_in;
    wire         preq_out, pack_out;
    wire [W-1:0] pdata_out;

    bd_source #(.W(W)) psrc (.req(preq_in), .ack(pack_in), .data(pdata_in));
    bd_pipe #(.W(W), .N(N), .DELAY(PAD)) pdut (
        .rst(rst),
        .req_in(preq_in), .ack_in(pack_in), .data_in(pdata_in),
        .req_out(preq_out), .ack_out(pack_out), .data_out(pdata_out));
    bd_sink #(.W(W)) psnk (.req(preq_out), .ack(pack_out), .data(pdata_out));

    bd_monitor #(.W(W), .CHAN("padded-out"), .SETTLE(0)) mp
        (.req(preq_out), .ack(pack_out), .data(pdata_out));

    // -- the pusher.  Free-running; blocks of its own accord when the pipe is
    // full, and is torn down by $finish rather than by a timeout.
    reg go = 1'b0;
    initial begin
        wait (go);
        for (i = 0; i < TOTAL; i = i + 1) src.send(8'h10 + i[7:0]);
    end

    integer j;
    initial begin
        wait (go);
        for (j = 0; j < TOTAL; j = j + 1) psrc.send(8'h10 + j[7:0]);
    end

    integer occupancy;
    integer k;

    initial begin
        $display("tb_link");

        #(20 * H);
        rst = 1'b0;
        #(20 * H);
        mi.arm; mo.arm; mp.arm;

        // -- occupancy ------------------------------------------------------
        // Output stalled.  The source pushes until it blocks; what it
        // completed is what the pipe swallowed.  The controller family table
        // says half a token per stage.
        snk.stall = 1'b1;
        go        = 1'b1;
        #(400 * H);

        occupancy = src.nsent;
        $display("  occupancy of a %0d-stage pipe: %0d token(s)", N, occupancy);
        if (occupancy != N / 2)
            fail("occupancy is not half a token per stage");
        if (snk.n != 0)
            fail("stalled sink took a token");

        // -- drain and stream ------------------------------------------------
        // Releasing the sink must produce every token, in the order sent, with
        // the values intact -- the two it was holding and the rest behind them.
        snk.stall = 1'b0;
        for (k = 0; k < 8000 && (snk.n < TOTAL || psnk.n < TOTAL); k = k + 1) #H;

        if (psnk.n != TOTAL) begin
            errors = errors + 1;
            $display("  FAIL padded pipe delivered %0d of %0d tokens",
                     psnk.n, TOTAL);
        end
        for (k = 0; k < psnk.n && k < TOTAL; k = k + 1)
            if (psnk.seen[k] !== (8'h10 + k[7:0])) begin
                errors = errors + 1;
                $display("  FAIL padded token %0d: got %h expected %h",
                         k, psnk.seen[k], 8'h10 + k[7:0]);
            end

        if (snk.n != TOTAL) begin
            errors = errors + 1;
            $display("  FAIL pipe delivered %0d of %0d tokens", snk.n, TOTAL);
        end
        for (k = 0; k < snk.n && k < TOTAL; k = k + 1)
            if (snk.seen[k] !== (8'h10 + k[7:0])) begin
                errors = errors + 1;
                $display("  FAIL token %0d: got %h expected %h",
                         k, snk.seen[k], 8'h10 + k[7:0]);
            end

        errors = errors + mi.errors + mo.errors + mp.errors;
        if (errors == 0) $display("tb_link PASS");
        else             $display("tb_link FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #50_000_000;
        $display("tb_link FAIL (timeout)");
        $finish;
    end
endmodule
