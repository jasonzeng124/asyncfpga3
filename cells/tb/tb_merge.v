// tb_merge.v -- merge with exclusive inputs.
//
// Three properties, matching the three paragraphs of the cell's header:
//
//   the acknowledge is a C-element, not an AND.  x_ack must stay high after
//   x_req falls, until z_ack has fallen too.  An AND would collapse it a
//   phase early, and the bench watches for exactly that.
//
//   the select is req+ack, not req.  z_data must still be x's value at the
//   moment z_ack rises, which is a phase after x_req fell.
//
//   the idle input is untouched.  Whichever input did not fire must see its
//   acknowledge stay at zero for the whole transaction.
//
// The bench serialises the two inputs completely, because that is the cell's
// stated obligation -- not merely exclusive requests, but no second request
// until the first transaction has fully returned to zero.

`timescale 1ps / 1ps

module tb_merge;

    localparam integer W = 8;
    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer i;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;

    wire         x_req, x_ack;  wire [W-1:0] x_data;
    wire         y_req, y_ack;  wire [W-1:0] y_data;
    wire         z_req, z_ack;  wire [W-1:0] z_data;

    bd_source #(.W(W)) xsrc (.req(x_req), .ack(x_ack), .data(x_data));
    bd_source #(.W(W)) ysrc (.req(y_req), .ack(y_ack), .data(y_data));

    bd_merge #(.W(W), .DELAY(4)) dut (
        .rst(rst),
        .x_req(x_req), .x_ack(x_ack), .x_data(x_data),
        .y_req(y_req), .y_ack(y_ack), .y_data(y_data),
        .z_req(z_req), .z_ack(z_ack), .z_data(z_data));

    bd_sink #(.W(W)) zsnk (.req(z_req), .ack(z_ack), .data(z_data));

    bd_monitor #(.W(W), .CHAN("merge-x")) mx (.req(x_req), .ack(x_ack), .data(x_data));
    bd_monitor #(.W(W), .CHAN("merge-y")) my (.req(y_req), .ack(y_ack), .data(y_data));
    // z_req comes through the matched delay, z_data through select and mux;
    // the delay is what makes data lead the request, so SETTLE stays 0.
    bd_monitor #(.W(W), .CHAN("merge-z")) mz (.req(z_req), .ack(z_ack), .data(z_data));

    reg watching = 1'b0;

    // -- the acknowledge is a C-element ------------------------------------
    // The mistake being watched for is x_ack = x_req . z_ack, which would drop
    // the acknowledge the instant the request left.  A real C-element holds
    // until z_ack has gone too.  Checked a couple of arcs after req-fall, so
    // the collapse would have had time to propagate if it were going to.
    always @(negedge x_req) if (watching) begin
        #(2 * `BD_T_FALL);
        if (z_ack === 1'b1 && x_ack !== 1'b1)
            fail("x_ack collapsed after x_req-fall while z_ack was still high");
    end
    always @(negedge y_req) if (watching) begin
        #(2 * `BD_T_FALL);
        if (z_ack === 1'b1 && y_ack !== 1'b1)
            fail("y_ack collapsed after y_req-fall while z_ack was still high");
    end

    // -- the idle input is untouched ---------------------------------------
    // Not checked at the acknowledge edge: bd_source drops its request in the
    // same time step the acknowledge arrives, so reading req there is a race
    // with the source, not an observation of the cell.  A pending flag,
    // raised at req-rise and cleared at ack-fall, is edge-order independent.
    reg x_pending = 1'b0, y_pending = 1'b0;
    always @(posedge x_req) x_pending = 1'b1;
    always @(negedge x_ack) x_pending = 1'b0;
    always @(posedge y_req) y_pending = 1'b1;
    always @(negedge y_ack) y_pending = 1'b0;

    always @(posedge x_ack) if (watching && !x_pending)
        fail("x acknowledged without having requested");
    always @(posedge y_ack) if (watching && !y_pending)
        fail("y acknowledged without having requested");

    integer expect_n;

    initial begin
        $display("tb_merge");
        #(4 * T);
        rst = 1'b0;
        #(4 * T);
        mx.arm; my.arm; mz.arm; watching = 1'b1;

        // Strictly serialised, alternating and then in runs, so both the
        // switch and the repeat are exercised.
        expect_n = 0;
        for (i = 0; i < 8; i = i + 1) begin
            xsrc.send(8'h10 + i[7:0]);
            #(2 * T);
            expect_n = expect_n + 1;
            if (zsnk.n != expect_n) fail("merge dropped an x token");
            else if (zsnk.seen[expect_n-1] !== (8'h10 + i[7:0]))
                $display("  FAIL x value: got %h expected %h at %0t",
                         zsnk.seen[expect_n-1], 8'h10 + i[7:0], $time);

            ysrc.send(8'hA0 + i[7:0]);
            #(2 * T);
            expect_n = expect_n + 1;
            if (zsnk.n != expect_n) fail("merge dropped a y token");
            else if (zsnk.seen[expect_n-1] !== (8'hA0 + i[7:0]))
                $display("  FAIL y value: got %h expected %h at %0t",
                         zsnk.seen[expect_n-1], 8'hA0 + i[7:0], $time);
        end

        for (i = 0; i < 4; i = i + 1) begin
            ysrc.send(8'hC0 + i[7:0]);
            #(2 * T);
            expect_n = expect_n + 1;
        end
        for (i = 0; i < 4; i = i + 1) begin
            xsrc.send(8'h50 + i[7:0]);
            #(2 * T);
            expect_n = expect_n + 1;
        end
        if (zsnk.n != expect_n) begin
            errors = errors + 1;
            $display("  FAIL merge delivered %0d of %0d tokens",
                     zsnk.n, expect_n);
        end

        errors = errors + mx.errors + my.errors + mz.errors;
        if (errors == 0) $display("tb_merge PASS");
        else             $display("tb_merge FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #40_000_000;
        $display("tb_merge FAIL (timeout)");
        $finish;
    end
endmodule
