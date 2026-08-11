// tb_forkjoin.v -- duals.  A fork broadcasts and joins acknowledges; a join
// joins requests and broadcasts the acknowledge.
//
// The property under test is the rendezvous itself: neither cell may complete
// while any one of its N partners is still outstanding.

`timescale 1ps / 1ps

module tb_forkjoin;

    localparam integer T = 12 * `BD_HOP_PS;
    localparam integer NF = 3;   // fork fan-out
    localparam integer NJ = 3;   // join fan-in

    integer errors = 0;
    integer i;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;

    // ------------------------------------------------------------------ fork
    wire freq, fack;
    wire [7:0] fdata;
    wire [NF-1:0] freq_out, fack_in;

    bd_source #(.W(8)) fsrc (.req(freq), .ack(fack), .data(fdata));
    bd_fork #(.N(NF)) ufork (.rst(rst), .req(freq), .ack(fack),
                             .req_out(freq_out), .ack_in(fack_in));

    genvar g;
    // A hierarchical reference needs a constant index, so each branch's count
    // is flattened into a bus the initial block can read with a variable.
    wire [16*NF-1:0] fcnt;
    generate
        for (g = 0; g < NF; g = g + 1) begin : fsinks
            bd_sink #(.W(8)) s (.req(freq_out[g]), .ack(fack_in[g]), .data(fdata));
            assign fcnt[16*g +: 16] = s.n[15:0];
        end
    endgenerate

    // The fork's acknowledge must not rise until every branch has.
    always @(posedge fack)
        if (fack_in !== {NF{1'b1}}) fail("fork acknowledged before all branches");

    // ------------------------------------------------------------------ join
    wire [NJ-1:0] jreq_in, jack_out;
    wire jreq, jack;
    wire [7:0] jdata;

    generate
        for (g = 0; g < NJ; g = g + 1) begin : jsrcs
            wire [7:0] d;
            bd_source #(.W(8)) s (.req(jreq_in[g]), .ack(jack_out[g]), .data(d));
        end
    endgenerate

    bd_join #(.N(NJ)) ujoin (.rst(rst), .req_in(jreq_in), .ack_out(jack_out),
                             .req(jreq), .ack(jack));
    assign jdata = 8'hAA;
    bd_sink #(.W(8)) jsink (.req(jreq), .ack(jack), .data(jdata));

    // The join's request must not rise until every input has.
    always @(posedge jreq)
        if (jreq_in !== {NJ{1'b1}}) fail("join fired before all inputs arrived");

    initial begin
        $display("tb_forkjoin");
        #(4 * T);
        rst = 1'b0;
        #(4 * T);

        // fork: every branch sees every token
        for (i = 0; i < 12; i = i + 1) fsrc.send(8'h40 + i[7:0]);
        #(4 * T);
        for (i = 0; i < NF; i = i + 1)
            if (fcnt[16*i +: 16] != 16'd12) begin
                errors = errors + 1;
                $display("  FAIL fork branch %0d took %0d of 12",
                         i, fcnt[16*i +: 16]);
            end

        // join: one output token per complete rendezvous.  The three senders
        // arrive in different orders each round, which is the point.
        for (i = 0; i < 12; i = i + 1) begin
            fork
                jsrcs[0].s.send(8'h11);
                begin #((i % 3) * T); jsrcs[1].s.send(8'h22); end
                begin #((i % 5) * T); jsrcs[2].s.send(8'h33); end
            join
        end
        #(4 * T);
        if (jsink.n != 12) begin
            errors = errors + 1;
            $display("  FAIL join produced %0d of 12 tokens", jsink.n);
        end

        if (errors == 0) $display("tb_forkjoin PASS");
        else             $display("tb_forkjoin FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #40_000_000;
        $display("tb_forkjoin FAIL (timeout)");
        $finish;
    end
endmodule
