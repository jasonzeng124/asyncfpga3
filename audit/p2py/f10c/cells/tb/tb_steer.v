// tb_steer.v -- the condition rides in the bundle it steers.
//
// The property that matters is not "the AND gates work" but that both
// branches return to zero unconditionally when req does, and that a token
// only ever appears on one branch.

`timescale 1ps / 1ps

module tb_steer;

    localparam integer T = 12 * `BD_HOP_PS;

    integer errors = 0;
    integer i, n0, n1;
    reg [0:0] v;

    wire req, ack, req0, ack0, req1, ack1;
    wire [0:0] sdata;

    bd_source #(.W(1)) src (.req(req), .ack(ack), .data(sdata));

    bd_steer dut (.req(req), .s(sdata[0]), .ack(ack),
                  .req0(req0), .ack0(ack0), .req1(req1), .ack1(ack1));

    bd_sink #(.W(1)) sink0 (.req(req0), .ack(ack0), .data(sdata));
    bd_sink #(.W(1)) sink1 (.req(req1), .ack(ack1), .data(sdata));

    bd_monitor #(.W(1), .CHAN("steer-in"))   mi (.req(req),  .ack(ack),  .data(sdata));
    bd_monitor #(.W(1), .CHAN("steer-out0")) m0 (.req(req0), .ack(ack0), .data(sdata));
    bd_monitor #(.W(1), .CHAN("steer-out1")) m1 (.req(req1), .ack(ack1), .data(sdata));

    // Both branches live at once is the one thing this cell may never do.
    always @* if (req0 === 1'b1 && req1 === 1'b1) begin
        errors = errors + 1;
        $display("  FAIL both branches asserted at %0t", $time);
    end

    // Return to zero is unconditional: req low must force both branches low.
    reg watching = 1'b0;
    always @(negedge req) if (watching) begin
        #(2 * T);
        if (req0 !== 1'b0 || req1 !== 1'b0) begin
            errors = errors + 1;
            $display("  FAIL branch did not return to zero at %0t", $time);
        end
    end

    initial begin
        $display("tb_steer");
        #(4 * T);
        mi.arm; m0.arm; m1.arm; watching = 1'b1;

        for (i = 0; i < 24; i = i + 1) begin
            v  = $random;
            n0 = sink0.n;
            n1 = sink1.n;
            src.send(v);
            #(2 * T);
            if (v[0] === 1'b1) begin
                if (sink1.n != n1 + 1 || sink0.n != n0) begin
                    errors = errors + 1;
                    $display("  FAIL s=1 did not steer to branch 1 at %0t", $time);
                end
            end else begin
                if (sink0.n != n0 + 1 || sink1.n != n1) begin
                    errors = errors + 1;
                    $display("  FAIL s=0 did not steer to branch 0 at %0t", $time);
                end
            end
        end

        $display("  branch 0 took %0d, branch 1 took %0d, sent %0d",
                 sink0.n, sink1.n, src.nsent);
        if (sink0.n + sink1.n != src.nsent) begin
            errors = errors + 1;
            $display("  FAIL token count does not balance");
        end

        errors = errors + mi.errors + m0.errors + m1.errors;
        if (errors == 0) $display("tb_steer PASS");
        else             $display("tb_steer FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #20_000_000;
        $display("tb_steer FAIL (timeout)");
        $finish;
    end
endmodule
