
// Control-only bench endpoints -- bd_source/bd_sink from sim/bd_env.v, minus
// the data bus, for channels bdc/emit.py gives no data net at all (width 0).
// Same SETUP/HOLD constants as bd_env.v, so channel timing is comparable.
module simcheck_ctl_src (output reg req, input wire ack);
    integer nsent;
    initial begin req = 1'b0; nsent = 0; end
    task send;
    begin
        #3000;
        req = 1'b1;
        wait (ack === 1'b1);
        req = 1'b0;
        wait (ack === 1'b0);
        nsent = nsent + 1;
    end
    endtask
endmodule

module simcheck_ctl_snk #(parameter integer HOLD = 2000)
    (input wire req, output reg ack);
    integer n;
    initial begin ack = 1'b0; n = 0; end
    always begin
        wait (req === 1'b1);
        #HOLD;
        n = n + 1;
        ack = 1'b1;
        wait (req === 1'b0);
        #HOLD;
        ack = 1'b0;
    end
endmodule

`timescale 1ps / 1ps

module tb_countloop;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer cur = -1;
    reg rst = 1'b1;

    wire a_req, a_ack;
    wire [31:0] a_data;
    bd_source #(.W(32)) a_src (.req(a_req), .ack(a_ack), .data(a_data));
    wire n_req, n_ack;
    wire [31:0] n_data;
    bd_source #(.W(32)) n_src (.req(n_req), .ack(n_ack), .data(n_data));
    wire start_req, start_ack;
    simcheck_ctl_src start_src (.req(start_req), .ack(start_ack));
    wire out0_req, out0_ack;
    wire [31:0] out0_data;
    bd_sink #(.W(32)) out0_snk (.req(out0_req), .ack(out0_ack), .data(out0_data));
    wire p_end_req, p_end_ack;
    simcheck_ctl_snk p_end_snk (.req(p_end_req), .ack(p_end_ack));

    bdc_countloop uut (
        .rst(rst),
        .a_req(a_req), .a_ack(a_ack), .a_data(a_data),
        .n_req(n_req), .n_ack(n_ack), .n_data(n_data),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    initial begin
        $display("tb_countloop");
        #(176 * T);
        rst = 1'b0;
        #(8 * T);

        // -- vector 0: {'a': 0, 'n': 0} -> {'out0': 0}
        cur = 0;
        fork
            a_src.send(32'h00000000);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 1);
            wait (p_end_snk.n == 1);
        join
        $display("OUT 0 %0d", $signed(out0_snk.seen[0]));
        if (out0_snk.seen[0] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 0 ({'a': 0, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[0]), out0_snk.seen[0], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 1: {'a': 0, 'n': 1} -> {'out0': 0}
        cur = 1;
        fork
            a_src.send(32'h00000000);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 2);
            wait (p_end_snk.n == 2);
        join
        $display("OUT 1 %0d", $signed(out0_snk.seen[1]));
        if (out0_snk.seen[1] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 1 ({'a': 0, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[1]), out0_snk.seen[1], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 2: {'a': 0, 'n': -1} -> {'out0': 0}
        cur = 2;
        fork
            a_src.send(32'h00000000);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 3);
            wait (p_end_snk.n == 3);
        join
        $display("OUT 2 %0d", $signed(out0_snk.seen[2]));
        if (out0_snk.seen[2] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 2 ({'a': 0, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[2]), out0_snk.seen[2], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 3: {'a': 0, 'n': -2147483648} -> {'out0': 0}
        cur = 3;
        fork
            a_src.send(32'h00000000);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 4);
            wait (p_end_snk.n == 4);
        join
        $display("OUT 3 %0d", $signed(out0_snk.seen[3]));
        if (out0_snk.seen[3] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 3 ({'a': 0, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[3]), out0_snk.seen[3], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 4: {'a': 0, 'n': 5} -> {'out0': 10}
        cur = 4;
        fork
            a_src.send(32'h00000000);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 5);
            wait (p_end_snk.n == 5);
        join
        $display("OUT 4 %0d", $signed(out0_snk.seen[4]));
        if (out0_snk.seen[4] !== 32'h0000000a) begin
            errors = errors + 1;
            $display("  FAIL vector 4 ({'a': 0, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[4]), out0_snk.seen[4], $signed(32'h0000000a), 32'h0000000a);
        end
        #(4 * T);

        // -- vector 5: {'a': 1, 'n': 0} -> {'out0': 0}
        cur = 5;
        fork
            a_src.send(32'h00000001);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 6);
            wait (p_end_snk.n == 6);
        join
        $display("OUT 5 %0d", $signed(out0_snk.seen[5]));
        if (out0_snk.seen[5] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 5 ({'a': 1, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[5]), out0_snk.seen[5], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 6: {'a': 1, 'n': 1} -> {'out0': 1}
        cur = 6;
        fork
            a_src.send(32'h00000001);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 7);
            wait (p_end_snk.n == 7);
        join
        $display("OUT 6 %0d", $signed(out0_snk.seen[6]));
        if (out0_snk.seen[6] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 6 ({'a': 1, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[6]), out0_snk.seen[6], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 7: {'a': 1, 'n': -1} -> {'out0': 0}
        cur = 7;
        fork
            a_src.send(32'h00000001);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 8);
            wait (p_end_snk.n == 8);
        join
        $display("OUT 7 %0d", $signed(out0_snk.seen[7]));
        if (out0_snk.seen[7] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 7 ({'a': 1, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[7]), out0_snk.seen[7], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 8: {'a': 1, 'n': -2147483648} -> {'out0': 0}
        cur = 8;
        fork
            a_src.send(32'h00000001);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 9);
            wait (p_end_snk.n == 9);
        join
        $display("OUT 8 %0d", $signed(out0_snk.seen[8]));
        if (out0_snk.seen[8] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 8 ({'a': 1, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[8]), out0_snk.seen[8], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 9: {'a': 1, 'n': 5} -> {'out0': 11}
        cur = 9;
        fork
            a_src.send(32'h00000001);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 10);
            wait (p_end_snk.n == 10);
        join
        $display("OUT 9 %0d", $signed(out0_snk.seen[9]));
        if (out0_snk.seen[9] !== 32'h0000000b) begin
            errors = errors + 1;
            $display("  FAIL vector 9 ({'a': 1, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[9]), out0_snk.seen[9], $signed(32'h0000000b), 32'h0000000b);
        end
        #(4 * T);

        // -- vector 10: {'a': -1, 'n': 0} -> {'out0': 0}
        cur = 10;
        fork
            a_src.send(32'hffffffff);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 11);
            wait (p_end_snk.n == 11);
        join
        $display("OUT 10 %0d", $signed(out0_snk.seen[10]));
        if (out0_snk.seen[10] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 10 ({'a': -1, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[10]), out0_snk.seen[10], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 11: {'a': -1, 'n': 1} -> {'out0': -1}
        cur = 11;
        fork
            a_src.send(32'hffffffff);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 12);
            wait (p_end_snk.n == 12);
        join
        $display("OUT 11 %0d", $signed(out0_snk.seen[11]));
        if (out0_snk.seen[11] !== 32'hffffffff) begin
            errors = errors + 1;
            $display("  FAIL vector 11 ({'a': -1, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[11]), out0_snk.seen[11], $signed(32'hffffffff), 32'hffffffff);
        end
        #(4 * T);

        // -- vector 12: {'a': -1, 'n': -1} -> {'out0': 0}
        cur = 12;
        fork
            a_src.send(32'hffffffff);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 13);
            wait (p_end_snk.n == 13);
        join
        $display("OUT 12 %0d", $signed(out0_snk.seen[12]));
        if (out0_snk.seen[12] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 12 ({'a': -1, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[12]), out0_snk.seen[12], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 13: {'a': -1, 'n': -2147483648} -> {'out0': 0}
        cur = 13;
        fork
            a_src.send(32'hffffffff);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 14);
            wait (p_end_snk.n == 14);
        join
        $display("OUT 13 %0d", $signed(out0_snk.seen[13]));
        if (out0_snk.seen[13] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 13 ({'a': -1, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[13]), out0_snk.seen[13], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 14: {'a': -1, 'n': 5} -> {'out0': -3}
        cur = 14;
        fork
            a_src.send(32'hffffffff);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 15);
            wait (p_end_snk.n == 15);
        join
        $display("OUT 14 %0d", $signed(out0_snk.seen[14]));
        if (out0_snk.seen[14] !== 32'hfffffffd) begin
            errors = errors + 1;
            $display("  FAIL vector 14 ({'a': -1, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[14]), out0_snk.seen[14], $signed(32'hfffffffd), 32'hfffffffd);
        end
        #(4 * T);

        // -- vector 15: {'a': 2, 'n': 0} -> {'out0': 0}
        cur = 15;
        fork
            a_src.send(32'h00000002);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 16);
            wait (p_end_snk.n == 16);
        join
        $display("OUT 15 %0d", $signed(out0_snk.seen[15]));
        if (out0_snk.seen[15] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 15 ({'a': 2, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[15]), out0_snk.seen[15], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 16: {'a': 2, 'n': 1} -> {'out0': 2}
        cur = 16;
        fork
            a_src.send(32'h00000002);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 17);
            wait (p_end_snk.n == 17);
        join
        $display("OUT 16 %0d", $signed(out0_snk.seen[16]));
        if (out0_snk.seen[16] !== 32'h00000002) begin
            errors = errors + 1;
            $display("  FAIL vector 16 ({'a': 2, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[16]), out0_snk.seen[16], $signed(32'h00000002), 32'h00000002);
        end
        #(4 * T);

        // -- vector 17: {'a': 2, 'n': -1} -> {'out0': 0}
        cur = 17;
        fork
            a_src.send(32'h00000002);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 18);
            wait (p_end_snk.n == 18);
        join
        $display("OUT 17 %0d", $signed(out0_snk.seen[17]));
        if (out0_snk.seen[17] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 17 ({'a': 2, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[17]), out0_snk.seen[17], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 18: {'a': 2, 'n': -2147483648} -> {'out0': 0}
        cur = 18;
        fork
            a_src.send(32'h00000002);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 19);
            wait (p_end_snk.n == 19);
        join
        $display("OUT 18 %0d", $signed(out0_snk.seen[18]));
        if (out0_snk.seen[18] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 18 ({'a': 2, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[18]), out0_snk.seen[18], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 19: {'a': 2, 'n': 5} -> {'out0': 8}
        cur = 19;
        fork
            a_src.send(32'h00000002);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 20);
            wait (p_end_snk.n == 20);
        join
        $display("OUT 19 %0d", $signed(out0_snk.seen[19]));
        if (out0_snk.seen[19] !== 32'h00000008) begin
            errors = errors + 1;
            $display("  FAIL vector 19 ({'a': 2, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[19]), out0_snk.seen[19], $signed(32'h00000008), 32'h00000008);
        end
        #(4 * T);

        // -- vector 20: {'a': -2, 'n': 0} -> {'out0': 0}
        cur = 20;
        fork
            a_src.send(32'hfffffffe);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 21);
            wait (p_end_snk.n == 21);
        join
        $display("OUT 20 %0d", $signed(out0_snk.seen[20]));
        if (out0_snk.seen[20] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 20 ({'a': -2, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[20]), out0_snk.seen[20], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 21: {'a': -2, 'n': 1} -> {'out0': -2}
        cur = 21;
        fork
            a_src.send(32'hfffffffe);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 22);
            wait (p_end_snk.n == 22);
        join
        $display("OUT 21 %0d", $signed(out0_snk.seen[21]));
        if (out0_snk.seen[21] !== 32'hfffffffe) begin
            errors = errors + 1;
            $display("  FAIL vector 21 ({'a': -2, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[21]), out0_snk.seen[21], $signed(32'hfffffffe), 32'hfffffffe);
        end
        #(4 * T);

        // -- vector 22: {'a': -2, 'n': -1} -> {'out0': 0}
        cur = 22;
        fork
            a_src.send(32'hfffffffe);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 23);
            wait (p_end_snk.n == 23);
        join
        $display("OUT 22 %0d", $signed(out0_snk.seen[22]));
        if (out0_snk.seen[22] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 22 ({'a': -2, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[22]), out0_snk.seen[22], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 23: {'a': -2, 'n': -2147483648} -> {'out0': 0}
        cur = 23;
        fork
            a_src.send(32'hfffffffe);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 24);
            wait (p_end_snk.n == 24);
        join
        $display("OUT 23 %0d", $signed(out0_snk.seen[23]));
        if (out0_snk.seen[23] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 23 ({'a': -2, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[23]), out0_snk.seen[23], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 24: {'a': -2, 'n': 5} -> {'out0': -4}
        cur = 24;
        fork
            a_src.send(32'hfffffffe);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 25);
            wait (p_end_snk.n == 25);
        join
        $display("OUT 24 %0d", $signed(out0_snk.seen[24]));
        if (out0_snk.seen[24] !== 32'hfffffffc) begin
            errors = errors + 1;
            $display("  FAIL vector 24 ({'a': -2, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[24]), out0_snk.seen[24], $signed(32'hfffffffc), 32'hfffffffc);
        end
        #(4 * T);

        // -- vector 25: {'a': 2147483647, 'n': 0} -> {'out0': 0}
        cur = 25;
        fork
            a_src.send(32'h7fffffff);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 26);
            wait (p_end_snk.n == 26);
        join
        $display("OUT 25 %0d", $signed(out0_snk.seen[25]));
        if (out0_snk.seen[25] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 25 ({'a': 2147483647, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[25]), out0_snk.seen[25], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 26: {'a': 2147483647, 'n': 1} -> {'out0': 2147483647}
        cur = 26;
        fork
            a_src.send(32'h7fffffff);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 27);
            wait (p_end_snk.n == 27);
        join
        $display("OUT 26 %0d", $signed(out0_snk.seen[26]));
        if (out0_snk.seen[26] !== 32'h7fffffff) begin
            errors = errors + 1;
            $display("  FAIL vector 26 ({'a': 2147483647, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[26]), out0_snk.seen[26], $signed(32'h7fffffff), 32'h7fffffff);
        end
        #(4 * T);

        // -- vector 27: {'a': 2147483647, 'n': -1} -> {'out0': 0}
        cur = 27;
        fork
            a_src.send(32'h7fffffff);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 28);
            wait (p_end_snk.n == 28);
        join
        $display("OUT 27 %0d", $signed(out0_snk.seen[27]));
        if (out0_snk.seen[27] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 27 ({'a': 2147483647, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[27]), out0_snk.seen[27], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 28: {'a': 2147483647, 'n': -2147483648} -> {'out0': 0}
        cur = 28;
        fork
            a_src.send(32'h7fffffff);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 29);
            wait (p_end_snk.n == 29);
        join
        $display("OUT 28 %0d", $signed(out0_snk.seen[28]));
        if (out0_snk.seen[28] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 28 ({'a': 2147483647, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[28]), out0_snk.seen[28], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 29: {'a': 2147483647, 'n': 5} -> {'out0': 2147483645}
        cur = 29;
        fork
            a_src.send(32'h7fffffff);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 30);
            wait (p_end_snk.n == 30);
        join
        $display("OUT 29 %0d", $signed(out0_snk.seen[29]));
        if (out0_snk.seen[29] !== 32'h7ffffffd) begin
            errors = errors + 1;
            $display("  FAIL vector 29 ({'a': 2147483647, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[29]), out0_snk.seen[29], $signed(32'h7ffffffd), 32'h7ffffffd);
        end
        #(4 * T);

        // -- vector 30: {'a': -2147483648, 'n': 0} -> {'out0': 0}
        cur = 30;
        fork
            a_src.send(32'h80000000);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 31);
            wait (p_end_snk.n == 31);
        join
        $display("OUT 30 %0d", $signed(out0_snk.seen[30]));
        if (out0_snk.seen[30] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 30 ({'a': -2147483648, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[30]), out0_snk.seen[30], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 31: {'a': -2147483648, 'n': 1} -> {'out0': -2147483648}
        cur = 31;
        fork
            a_src.send(32'h80000000);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 32);
            wait (p_end_snk.n == 32);
        join
        $display("OUT 31 %0d", $signed(out0_snk.seen[31]));
        if (out0_snk.seen[31] !== 32'h80000000) begin
            errors = errors + 1;
            $display("  FAIL vector 31 ({'a': -2147483648, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[31]), out0_snk.seen[31], $signed(32'h80000000), 32'h80000000);
        end
        #(4 * T);

        // -- vector 32: {'a': -2147483648, 'n': -1} -> {'out0': 0}
        cur = 32;
        fork
            a_src.send(32'h80000000);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 33);
            wait (p_end_snk.n == 33);
        join
        $display("OUT 32 %0d", $signed(out0_snk.seen[32]));
        if (out0_snk.seen[32] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 32 ({'a': -2147483648, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[32]), out0_snk.seen[32], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 33: {'a': -2147483648, 'n': -2147483648} -> {'out0': 0}
        cur = 33;
        fork
            a_src.send(32'h80000000);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 34);
            wait (p_end_snk.n == 34);
        join
        $display("OUT 33 %0d", $signed(out0_snk.seen[33]));
        if (out0_snk.seen[33] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 33 ({'a': -2147483648, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[33]), out0_snk.seen[33], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 34: {'a': -2147483648, 'n': 5} -> {'out0': -2147483638}
        cur = 34;
        fork
            a_src.send(32'h80000000);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 35);
            wait (p_end_snk.n == 35);
        join
        $display("OUT 34 %0d", $signed(out0_snk.seen[34]));
        if (out0_snk.seen[34] !== 32'h8000000a) begin
            errors = errors + 1;
            $display("  FAIL vector 34 ({'a': -2147483648, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[34]), out0_snk.seen[34], $signed(32'h8000000a), 32'h8000000a);
        end
        #(4 * T);

        // -- vector 35: {'a': 1073741824, 'n': 0} -> {'out0': 0}
        cur = 35;
        fork
            a_src.send(32'h40000000);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 36);
            wait (p_end_snk.n == 36);
        join
        $display("OUT 35 %0d", $signed(out0_snk.seen[35]));
        if (out0_snk.seen[35] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 35 ({'a': 1073741824, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[35]), out0_snk.seen[35], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 36: {'a': 1073741824, 'n': 1} -> {'out0': 1073741824}
        cur = 36;
        fork
            a_src.send(32'h40000000);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 37);
            wait (p_end_snk.n == 37);
        join
        $display("OUT 36 %0d", $signed(out0_snk.seen[36]));
        if (out0_snk.seen[36] !== 32'h40000000) begin
            errors = errors + 1;
            $display("  FAIL vector 36 ({'a': 1073741824, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[36]), out0_snk.seen[36], $signed(32'h40000000), 32'h40000000);
        end
        #(4 * T);

        // -- vector 37: {'a': 1073741824, 'n': -1} -> {'out0': 0}
        cur = 37;
        fork
            a_src.send(32'h40000000);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 38);
            wait (p_end_snk.n == 38);
        join
        $display("OUT 37 %0d", $signed(out0_snk.seen[37]));
        if (out0_snk.seen[37] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 37 ({'a': 1073741824, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[37]), out0_snk.seen[37], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 38: {'a': 1073741824, 'n': -2147483648} -> {'out0': 0}
        cur = 38;
        fork
            a_src.send(32'h40000000);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 39);
            wait (p_end_snk.n == 39);
        join
        $display("OUT 38 %0d", $signed(out0_snk.seen[38]));
        if (out0_snk.seen[38] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 38 ({'a': 1073741824, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[38]), out0_snk.seen[38], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 39: {'a': 1073741824, 'n': 5} -> {'out0': 1073741834}
        cur = 39;
        fork
            a_src.send(32'h40000000);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 40);
            wait (p_end_snk.n == 40);
        join
        $display("OUT 39 %0d", $signed(out0_snk.seen[39]));
        if (out0_snk.seen[39] !== 32'h4000000a) begin
            errors = errors + 1;
            $display("  FAIL vector 39 ({'a': 1073741824, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[39]), out0_snk.seen[39], $signed(32'h4000000a), 32'h4000000a);
        end
        #(4 * T);

        // -- vector 40: {'a': 2147483646, 'n': 0} -> {'out0': 0}
        cur = 40;
        fork
            a_src.send(32'h7ffffffe);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 41);
            wait (p_end_snk.n == 41);
        join
        $display("OUT 40 %0d", $signed(out0_snk.seen[40]));
        if (out0_snk.seen[40] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 40 ({'a': 2147483646, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[40]), out0_snk.seen[40], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 41: {'a': 2147483646, 'n': 1} -> {'out0': 2147483646}
        cur = 41;
        fork
            a_src.send(32'h7ffffffe);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 42);
            wait (p_end_snk.n == 42);
        join
        $display("OUT 41 %0d", $signed(out0_snk.seen[41]));
        if (out0_snk.seen[41] !== 32'h7ffffffe) begin
            errors = errors + 1;
            $display("  FAIL vector 41 ({'a': 2147483646, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[41]), out0_snk.seen[41], $signed(32'h7ffffffe), 32'h7ffffffe);
        end
        #(4 * T);

        // -- vector 42: {'a': 2147483646, 'n': -1} -> {'out0': 0}
        cur = 42;
        fork
            a_src.send(32'h7ffffffe);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 43);
            wait (p_end_snk.n == 43);
        join
        $display("OUT 42 %0d", $signed(out0_snk.seen[42]));
        if (out0_snk.seen[42] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 42 ({'a': 2147483646, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[42]), out0_snk.seen[42], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 43: {'a': 2147483646, 'n': -2147483648} -> {'out0': 0}
        cur = 43;
        fork
            a_src.send(32'h7ffffffe);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 44);
            wait (p_end_snk.n == 44);
        join
        $display("OUT 43 %0d", $signed(out0_snk.seen[43]));
        if (out0_snk.seen[43] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 43 ({'a': 2147483646, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[43]), out0_snk.seen[43], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 44: {'a': 2147483646, 'n': 5} -> {'out0': 2147483644}
        cur = 44;
        fork
            a_src.send(32'h7ffffffe);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 45);
            wait (p_end_snk.n == 45);
        join
        $display("OUT 44 %0d", $signed(out0_snk.seen[44]));
        if (out0_snk.seen[44] !== 32'h7ffffffc) begin
            errors = errors + 1;
            $display("  FAIL vector 44 ({'a': 2147483646, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[44]), out0_snk.seen[44], $signed(32'h7ffffffc), 32'h7ffffffc);
        end
        #(4 * T);

        // -- vector 45: {'a': -2147483647, 'n': 0} -> {'out0': 0}
        cur = 45;
        fork
            a_src.send(32'h80000001);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 46);
            wait (p_end_snk.n == 46);
        join
        $display("OUT 45 %0d", $signed(out0_snk.seen[45]));
        if (out0_snk.seen[45] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 45 ({'a': -2147483647, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[45]), out0_snk.seen[45], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 46: {'a': -2147483647, 'n': 1} -> {'out0': -2147483647}
        cur = 46;
        fork
            a_src.send(32'h80000001);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 47);
            wait (p_end_snk.n == 47);
        join
        $display("OUT 46 %0d", $signed(out0_snk.seen[46]));
        if (out0_snk.seen[46] !== 32'h80000001) begin
            errors = errors + 1;
            $display("  FAIL vector 46 ({'a': -2147483647, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[46]), out0_snk.seen[46], $signed(32'h80000001), 32'h80000001);
        end
        #(4 * T);

        // -- vector 47: {'a': -2147483647, 'n': -1} -> {'out0': 0}
        cur = 47;
        fork
            a_src.send(32'h80000001);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 48);
            wait (p_end_snk.n == 48);
        join
        $display("OUT 47 %0d", $signed(out0_snk.seen[47]));
        if (out0_snk.seen[47] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 47 ({'a': -2147483647, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[47]), out0_snk.seen[47], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 48: {'a': -2147483647, 'n': -2147483648} -> {'out0': 0}
        cur = 48;
        fork
            a_src.send(32'h80000001);
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 49);
            wait (p_end_snk.n == 49);
        join
        $display("OUT 48 %0d", $signed(out0_snk.seen[48]));
        if (out0_snk.seen[48] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 48 ({'a': -2147483647, 'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[48]), out0_snk.seen[48], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 49: {'a': -2147483647, 'n': 5} -> {'out0': -2147483637}
        cur = 49;
        fork
            a_src.send(32'h80000001);
            n_src.send(32'h00000005);
            start_src.send;
            wait (out0_snk.n == 50);
            wait (p_end_snk.n == 50);
        join
        $display("OUT 49 %0d", $signed(out0_snk.seen[49]));
        if (out0_snk.seen[49] !== 32'h8000000b) begin
            errors = errors + 1;
            $display("  FAIL vector 49 ({'a': -2147483647, 'n': 5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[49]), out0_snk.seen[49], $signed(32'h8000000b), 32'h8000000b);
        end
        #(4 * T);

        // -- vector 50: {'a': -370043322, 'n': 11} -> {'out0': -370043391}
        cur = 50;
        fork
            a_src.send(32'he9f19646);
            n_src.send(32'h0000000b);
            start_src.send;
            wait (out0_snk.n == 51);
            wait (p_end_snk.n == 51);
        join
        $display("OUT 50 %0d", $signed(out0_snk.seen[50]));
        if (out0_snk.seen[50] !== 32'he9f19601) begin
            errors = errors + 1;
            $display("  FAIL vector 50 ({'a': -370043322, 'n': 11}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[50]), out0_snk.seen[50], $signed(32'he9f19601), 32'he9f19601);
        end
        #(4 * T);

        // -- vector 51: {'a': -770182796, 'n': 46} -> {'out0': 1099}
        cur = 51;
        fork
            a_src.send(32'hd217f174);
            n_src.send(32'h0000002e);
            start_src.send;
            wait (out0_snk.n == 52);
            wait (p_end_snk.n == 52);
        join
        $display("OUT 51 %0d", $signed(out0_snk.seen[51]));
        if (out0_snk.seen[51] !== 32'h0000044b) begin
            errors = errors + 1;
            $display("  FAIL vector 51 ({'a': -770182796, 'n': 46}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[51]), out0_snk.seen[51], $signed(32'h0000044b), 32'h0000044b);
        end
        #(4 * T);

        // -- vector 52: {'a': 689890323, 'n': -2} -> {'out0': 0}
        cur = 52;
        fork
            a_src.send(32'h291ee413);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 53);
            wait (p_end_snk.n == 53);
        join
        $display("OUT 52 %0d", $signed(out0_snk.seen[52]));
        if (out0_snk.seen[52] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 52 ({'a': 689890323, 'n': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[52]), out0_snk.seen[52], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 53: {'a': -1538305221, 'n': -2} -> {'out0': 0}
        cur = 53;
        fork
            a_src.send(32'ha44f533b);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 54);
            wait (p_end_snk.n == 54);
        join
        $display("OUT 53 %0d", $signed(out0_snk.seen[53]));
        if (out0_snk.seen[53] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 53 ({'a': -1538305221, 'n': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[53]), out0_snk.seen[53], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 54: {'a': -82771192, 'n': 17} -> {'out0': -82771040}
        cur = 54;
        fork
            a_src.send(32'hfb110308);
            n_src.send(32'h00000011);
            start_src.send;
            wait (out0_snk.n == 55);
            wait (p_end_snk.n == 55);
        join
        $display("OUT 54 %0d", $signed(out0_snk.seen[54]));
        if (out0_snk.seen[54] !== 32'hfb1103a0) begin
            errors = errors + 1;
            $display("  FAIL vector 54 ({'a': -82771192, 'n': 17}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[54]), out0_snk.seen[54], $signed(32'hfb1103a0), 32'hfb1103a0);
        end
        #(4 * T);

        // -- vector 55: {'a': 994836493, 'n': 58} -> {'out0': 1639}
        cur = 55;
        fork
            a_src.send(32'h3b4c000d);
            n_src.send(32'h0000003a);
            start_src.send;
            wait (out0_snk.n == 56);
            wait (p_end_snk.n == 56);
        join
        $display("OUT 55 %0d", $signed(out0_snk.seen[55]));
        if (out0_snk.seen[55] !== 32'h00000667) begin
            errors = errors + 1;
            $display("  FAIL vector 55 ({'a': 994836493, 'n': 58}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[55]), out0_snk.seen[55], $signed(32'h00000667), 32'h00000667);
        end
        #(4 * T);

        // -- vector 56: {'a': 1599955537, 'n': 34} -> {'out0': 691}
        cur = 56;
        fork
            a_src.send(32'h5f5d6251);
            n_src.send(32'h00000022);
            start_src.send;
            wait (out0_snk.n == 57);
            wait (p_end_snk.n == 57);
        join
        $display("OUT 56 %0d", $signed(out0_snk.seen[56]));
        if (out0_snk.seen[56] !== 32'h000002b3) begin
            errors = errors + 1;
            $display("  FAIL vector 56 ({'a': 1599955537, 'n': 34}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[56]), out0_snk.seen[56], $signed(32'h000002b3), 32'h000002b3);
        end
        #(4 * T);

        // -- vector 57: {'a': 61523952, 'n': 36} -> {'out0': 20470}
        cur = 57;
        fork
            a_src.send(32'h03aac7f0);
            n_src.send(32'h00000024);
            start_src.send;
            wait (out0_snk.n == 58);
            wait (p_end_snk.n == 58);
        join
        $display("OUT 57 %0d", $signed(out0_snk.seen[57]));
        if (out0_snk.seen[57] !== 32'h00004ff6) begin
            errors = errors + 1;
            $display("  FAIL vector 57 ({'a': 61523952, 'n': 36}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[57]), out0_snk.seen[57], $signed(32'h00004ff6), 32'h00004ff6);
        end
        #(4 * T);

        // -- vector 58: {'a': -382547043, 'n': 12} -> {'out0': 130}
        cur = 58;
        fork
            a_src.send(32'he932cb9d);
            n_src.send(32'h0000000c);
            start_src.send;
            wait (out0_snk.n == 59);
            wait (p_end_snk.n == 59);
        join
        $display("OUT 58 %0d", $signed(out0_snk.seen[58]));
        if (out0_snk.seen[58] !== 32'h00000082) begin
            errors = errors + 1;
            $display("  FAIL vector 58 ({'a': -382547043, 'n': 12}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[58]), out0_snk.seen[58], $signed(32'h00000082), 32'h00000082);
        end
        #(4 * T);

        // -- vector 59: {'a': -306692820, 'n': 37} -> {'out0': -306692578}
        cur = 59;
        fork
            a_src.send(32'hedb83d2c);
            n_src.send(32'h00000025);
            start_src.send;
            wait (out0_snk.n == 60);
            wait (p_end_snk.n == 60);
        join
        $display("OUT 59 %0d", $signed(out0_snk.seen[59]));
        if (out0_snk.seen[59] !== 32'hedb83e1e) begin
            errors = errors + 1;
            $display("  FAIL vector 59 ({'a': -306692820, 'n': 37}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[59]), out0_snk.seen[59], $signed(32'hedb83e1e), 32'hedb83e1e);
        end
        #(4 * T);

        // -- vector 60: {'a': -2133602558, 'n': -1} -> {'out0': 0}
        cur = 60;
        fork
            a_src.send(32'h80d3cf02);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 61);
            wait (p_end_snk.n == 61);
        join
        $display("OUT 60 %0d", $signed(out0_snk.seen[60]));
        if (out0_snk.seen[60] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 60 ({'a': -2133602558, 'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[60]), out0_snk.seen[60], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 61: {'a': 454235750, 'n': -2} -> {'out0': 0}
        cur = 61;
        fork
            a_src.send(32'h1b131666);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 62);
            wait (p_end_snk.n == 62);
        join
        $display("OUT 61 %0d", $signed(out0_snk.seen[61]));
        if (out0_snk.seen[61] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 61 ({'a': 454235750, 'n': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[61]), out0_snk.seen[61], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 62: {'a': -1472864752, 'n': 39} -> {'out0': -1472864971}
        cur = 62;
        fork
            a_src.send(32'ha835de10);
            n_src.send(32'h00000027);
            start_src.send;
            wait (out0_snk.n == 63);
            wait (p_end_snk.n == 63);
        join
        $display("OUT 62 %0d", $signed(out0_snk.seen[62]));
        if (out0_snk.seen[62] !== 32'ha835dd35) begin
            errors = errors + 1;
            $display("  FAIL vector 62 ({'a': -1472864752, 'n': 39}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[62]), out0_snk.seen[62], $signed(32'ha835dd35), 32'ha835dd35);
        end
        #(4 * T);

        // -- vector 63: {'a': -1847299308, 'n': 8} -> {'out0': 44}
        cur = 63;
        fork
            a_src.send(32'h91e47314);
            n_src.send(32'h00000008);
            start_src.send;
            wait (out0_snk.n == 64);
            wait (p_end_snk.n == 64);
        join
        $display("OUT 63 %0d", $signed(out0_snk.seen[63]));
        if (out0_snk.seen[63] !== 32'h0000002c) begin
            errors = errors + 1;
            $display("  FAIL vector 63 ({'a': -1847299308, 'n': 8}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[63]), out0_snk.seen[63], $signed(32'h0000002c), 32'h0000002c);
        end
        #(4 * T);

        // -- vector 64: {'a': 369860297, 'n': 2} -> {'out0': 3}
        cur = 64;
        fork
            a_src.send(32'h160b9ec9);
            n_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 65);
            wait (p_end_snk.n == 65);
        join
        $display("OUT 64 %0d", $signed(out0_snk.seen[64]));
        if (out0_snk.seen[64] !== 32'h00000003) begin
            errors = errors + 1;
            $display("  FAIL vector 64 ({'a': 369860297, 'n': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[64]), out0_snk.seen[64], $signed(32'h00000003), 32'h00000003);
        end
        #(4 * T);

        // -- vector 65: {'a': 1526361183, 'n': 22} -> {'out0': 693}
        cur = 65;
        fork
            a_src.send(32'h5afa6c5f);
            n_src.send(32'h00000016);
            start_src.send;
            wait (out0_snk.n == 66);
            wait (p_end_snk.n == 66);
        join
        $display("OUT 65 %0d", $signed(out0_snk.seen[65]));
        if (out0_snk.seen[65] !== 32'h000002b5) begin
            errors = errors + 1;
            $display("  FAIL vector 65 ({'a': 1526361183, 'n': 22}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[65]), out0_snk.seen[65], $signed(32'h000002b5), 32'h000002b5);
        end
        #(4 * T);

        // -- vector 66: {'a': 123056446, 'n': 55} -> {'out0': 123059235}
        cur = 66;
        fork
            a_src.send(32'h0755b13e);
            n_src.send(32'h00000037);
            start_src.send;
            wait (out0_snk.n == 67);
            wait (p_end_snk.n == 67);
        join
        $display("OUT 66 %0d", $signed(out0_snk.seen[66]));
        if (out0_snk.seen[66] !== 32'h0755bc23) begin
            errors = errors + 1;
            $display("  FAIL vector 66 ({'a': 123056446, 'n': 55}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[66]), out0_snk.seen[66], $signed(32'h0755bc23), 32'h0755bc23);
        end
        #(4 * T);

        // -- vector 67: {'a': -1775037983, 'n': 30} -> {'out0': 117}
        cur = 67;
        fork
            a_src.send(32'h963311e1);
            n_src.send(32'h0000001e);
            start_src.send;
            wait (out0_snk.n == 68);
            wait (p_end_snk.n == 68);
        join
        $display("OUT 67 %0d", $signed(out0_snk.seen[67]));
        if (out0_snk.seen[67] !== 32'h00000075) begin
            errors = errors + 1;
            $display("  FAIL vector 67 ({'a': -1775037983, 'n': 30}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[67]), out0_snk.seen[67], $signed(32'h00000075), 32'h00000075);
        end
        #(4 * T);

        // -- vector 68: {'a': -502198704, 'n': 8} -> {'out0': 28}
        cur = 68;
        fork
            a_src.send(32'he2110e50);
            n_src.send(32'h00000008);
            start_src.send;
            wait (out0_snk.n == 69);
            wait (p_end_snk.n == 69);
        join
        $display("OUT 68 %0d", $signed(out0_snk.seen[68]));
        if (out0_snk.seen[68] !== 32'h0000001c) begin
            errors = errors + 1;
            $display("  FAIL vector 68 ({'a': -502198704, 'n': 8}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[68]), out0_snk.seen[68], $signed(32'h0000001c), 32'h0000001c);
        end
        #(4 * T);

        // -- vector 69: {'a': 1907947485, 'n': 2} -> {'out0': 3}
        cur = 69;
        fork
            a_src.send(32'h71b8f7dd);
            n_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 70);
            wait (p_end_snk.n == 70);
        join
        $display("OUT 69 %0d", $signed(out0_snk.seen[69]));
        if (out0_snk.seen[69] !== 32'h00000003) begin
            errors = errors + 1;
            $display("  FAIL vector 69 ({'a': 1907947485, 'n': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[69]), out0_snk.seen[69], $signed(32'h00000003), 32'h00000003);
        end
        #(4 * T);

        // -- vector 70: {'a': 1286397399, 'n': 29} -> {'out0': 1286397433}
        cur = 70;
        fork
            a_src.send(32'h4cacddd7);
            n_src.send(32'h0000001d);
            start_src.send;
            wait (out0_snk.n == 71);
            wait (p_end_snk.n == 71);
        join
        $display("OUT 70 %0d", $signed(out0_snk.seen[70]));
        if (out0_snk.seen[70] !== 32'h4cacddf9) begin
            errors = errors + 1;
            $display("  FAIL vector 70 ({'a': 1286397399, 'n': 29}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[70]), out0_snk.seen[70], $signed(32'h4cacddf9), 32'h4cacddf9);
        end
        #(4 * T);

        // -- vector 71: {'a': -46109811, 'n': 19} -> {'out0': -46109920}
        cur = 71;
        fork
            a_src.send(32'hfd406b8d);
            n_src.send(32'h00000013);
            start_src.send;
            wait (out0_snk.n == 72);
            wait (p_end_snk.n == 72);
        join
        $display("OUT 71 %0d", $signed(out0_snk.seen[71]));
        if (out0_snk.seen[71] !== 32'hfd406b20) begin
            errors = errors + 1;
            $display("  FAIL vector 71 ({'a': -46109811, 'n': 19}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[71]), out0_snk.seen[71], $signed(32'hfd406b20), 32'hfd406b20);
        end
        #(4 * T);

        // -- vector 72: {'a': -1362726670, 'n': 31} -> {'out0': -1362725661}
        cur = 72;
        fork
            a_src.send(32'haec670f2);
            n_src.send(32'h0000001f);
            start_src.send;
            wait (out0_snk.n == 73);
            wait (p_end_snk.n == 73);
        join
        $display("OUT 72 %0d", $signed(out0_snk.seen[72]));
        if (out0_snk.seen[72] !== 32'haec674e3) begin
            errors = errors + 1;
            $display("  FAIL vector 72 ({'a': -1362726670, 'n': 31}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[72]), out0_snk.seen[72], $signed(32'haec674e3), 32'haec674e3);
        end
        #(4 * T);

        // -- vector 73: {'a': 1243041508, 'n': 57} -> {'out0': 1243041448}
        cur = 73;
        fork
            a_src.send(32'h4a174ee4);
            n_src.send(32'h00000039);
            start_src.send;
            wait (out0_snk.n == 74);
            wait (p_end_snk.n == 74);
        join
        $display("OUT 73 %0d", $signed(out0_snk.seen[73]));
        if (out0_snk.seen[73] !== 32'h4a174ea8) begin
            errors = errors + 1;
            $display("  FAIL vector 73 ({'a': 1243041508, 'n': 57}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[73]), out0_snk.seen[73], $signed(32'h4a174ea8), 32'h4a174ea8);
        end
        #(4 * T);

        // -- vector 74: {'a': -1809630501, 'n': 48} -> {'out0': 1512}
        cur = 74;
        fork
            a_src.send(32'h94233adb);
            n_src.send(32'h00000030);
            start_src.send;
            wait (out0_snk.n == 75);
            wait (p_end_snk.n == 75);
        join
        $display("OUT 74 %0d", $signed(out0_snk.seen[74]));
        if (out0_snk.seen[74] !== 32'h000005e8) begin
            errors = errors + 1;
            $display("  FAIL vector 74 ({'a': -1809630501, 'n': 48}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[74]), out0_snk.seen[74], $signed(32'h000005e8), 32'h000005e8);
        end
        #(4 * T);

        // -- vector 75: {'a': 426900782, 'n': 6} -> {'out0': 63}
        cur = 75;
        fork
            a_src.send(32'h1971fd2e);
            n_src.send(32'h00000006);
            start_src.send;
            wait (out0_snk.n == 76);
            wait (p_end_snk.n == 76);
        join
        $display("OUT 75 %0d", $signed(out0_snk.seen[75]));
        if (out0_snk.seen[75] !== 32'h0000003f) begin
            errors = errors + 1;
            $display("  FAIL vector 75 ({'a': 426900782, 'n': 6}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[75]), out0_snk.seen[75], $signed(32'h0000003f), 32'h0000003f);
        end
        #(4 * T);

        // -- vector 76: {'a': 1224636604, 'n': -5} -> {'out0': 0}
        cur = 76;
        fork
            a_src.send(32'h48fe78bc);
            n_src.send(32'hfffffffb);
            start_src.send;
            wait (out0_snk.n == 77);
            wait (p_end_snk.n == 77);
        join
        $display("OUT 76 %0d", $signed(out0_snk.seen[76]));
        if (out0_snk.seen[76] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 76 ({'a': 1224636604, 'n': -5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[76]), out0_snk.seen[76], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 77: {'a': 543112333, 'n': 44} -> {'out0': 690}
        cur = 77;
        fork
            a_src.send(32'h205f3c8d);
            n_src.send(32'h0000002c);
            start_src.send;
            wait (out0_snk.n == 78);
            wait (p_end_snk.n == 78);
        join
        $display("OUT 77 %0d", $signed(out0_snk.seen[77]));
        if (out0_snk.seen[77] !== 32'h000002b2) begin
            errors = errors + 1;
            $display("  FAIL vector 77 ({'a': 543112333, 'n': 44}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[77]), out0_snk.seen[77], $signed(32'h000002b2), 32'h000002b2);
        end
        #(4 * T);

        // -- vector 78: {'a': 1812363936, 'n': 48} -> {'out0': 2088}
        cur = 78;
        fork
            a_src.send(32'h6c067aa0);
            n_src.send(32'h00000030);
            start_src.send;
            wait (out0_snk.n == 79);
            wait (p_end_snk.n == 79);
        join
        $display("OUT 78 %0d", $signed(out0_snk.seen[78]));
        if (out0_snk.seen[78] !== 32'h00000828) begin
            errors = errors + 1;
            $display("  FAIL vector 78 ({'a': 1812363936, 'n': 48}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[78]), out0_snk.seen[78], $signed(32'h00000828), 32'h00000828);
        end
        #(4 * T);

        // -- vector 79: {'a': -158302298, 'n': 29} -> {'out0': -158302472}
        cur = 79;
        fork
            a_src.send(32'hf6907fa6);
            n_src.send(32'h0000001d);
            start_src.send;
            wait (out0_snk.n == 80);
            wait (p_end_snk.n == 80);
        join
        $display("OUT 79 %0d", $signed(out0_snk.seen[79]));
        if (out0_snk.seen[79] !== 32'hf6907ef8) begin
            errors = errors + 1;
            $display("  FAIL vector 79 ({'a': -158302298, 'n': 29}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[79]), out0_snk.seen[79], $signed(32'hf6907ef8), 32'hf6907ef8);
        end
        #(4 * T);

        // -- vector 80: {'a': 1328121145, 'n': 47} -> {'out0': 1328123042}
        cur = 80;
        fork
            a_src.send(32'h4f298539);
            n_src.send(32'h0000002f);
            start_src.send;
            wait (out0_snk.n == 81);
            wait (p_end_snk.n == 81);
        join
        $display("OUT 80 %0d", $signed(out0_snk.seen[80]));
        if (out0_snk.seen[80] !== 32'h4f298ca2) begin
            errors = errors + 1;
            $display("  FAIL vector 80 ({'a': 1328121145, 'n': 47}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[80]), out0_snk.seen[80], $signed(32'h4f298ca2), 32'h4f298ca2);
        end
        #(4 * T);

        // -- vector 81: {'a': 227914853, 'n': -5} -> {'out0': 0}
        cur = 81;
        fork
            a_src.send(32'h0d95b465);
            n_src.send(32'hfffffffb);
            start_src.send;
            wait (out0_snk.n == 82);
            wait (p_end_snk.n == 82);
        join
        $display("OUT 81 %0d", $signed(out0_snk.seen[81]));
        if (out0_snk.seen[81] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 81 ({'a': 227914853, 'n': -5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[81]), out0_snk.seen[81], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 82: {'a': 776237770, 'n': 7} -> {'out0': 776237791}
        cur = 82;
        fork
            a_src.send(32'h2e4472ca);
            n_src.send(32'h00000007);
            start_src.send;
            wait (out0_snk.n == 83);
            wait (p_end_snk.n == 83);
        join
        $display("OUT 82 %0d", $signed(out0_snk.seen[82]));
        if (out0_snk.seen[82] !== 32'h2e4472df) begin
            errors = errors + 1;
            $display("  FAIL vector 82 ({'a': 776237770, 'n': 7}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[82]), out0_snk.seen[82], $signed(32'h2e4472df), 32'h2e4472df);
        end
        #(4 * T);

        // -- vector 83: {'a': -123434737, 'n': 54} -> {'out0': 1029}
        cur = 83;
        fork
            a_src.send(32'hf8a4890f);
            n_src.send(32'h00000036);
            start_src.send;
            wait (out0_snk.n == 84);
            wait (p_end_snk.n == 84);
        join
        $display("OUT 83 %0d", $signed(out0_snk.seen[83]));
        if (out0_snk.seen[83] !== 32'h00000405) begin
            errors = errors + 1;
            $display("  FAIL vector 83 ({'a': -123434737, 'n': 54}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[83]), out0_snk.seen[83], $signed(32'h00000405), 32'h00000405);
        end
        #(4 * T);

        // -- vector 84: {'a': -983348643, 'n': 7} -> {'out0': -983348646}
        cur = 84;
        fork
            a_src.send(32'hc5634a5d);
            n_src.send(32'h00000007);
            start_src.send;
            wait (out0_snk.n == 85);
            wait (p_end_snk.n == 85);
        join
        $display("OUT 84 %0d", $signed(out0_snk.seen[84]));
        if (out0_snk.seen[84] !== 32'hc5634a5a) begin
            errors = errors + 1;
            $display("  FAIL vector 84 ({'a': -983348643, 'n': 7}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[84]), out0_snk.seen[84], $signed(32'hc5634a5a), 32'hc5634a5a);
        end
        #(4 * T);

        // -- vector 85: {'a': 1603312841, 'n': -5} -> {'out0': 0}
        cur = 85;
        fork
            a_src.send(32'h5f909cc9);
            n_src.send(32'hfffffffb);
            start_src.send;
            wait (out0_snk.n == 86);
            wait (p_end_snk.n == 86);
        join
        $display("OUT 85 %0d", $signed(out0_snk.seen[85]));
        if (out0_snk.seen[85] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 85 ({'a': 1603312841, 'n': -5}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[85]), out0_snk.seen[85], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 86: {'a': 1448568866, 'n': 50} -> {'out0': 1417}
        cur = 86;
        fork
            a_src.send(32'h56576822);
            n_src.send(32'h00000032);
            start_src.send;
            wait (out0_snk.n == 87);
            wait (p_end_snk.n == 87);
        join
        $display("OUT 86 %0d", $signed(out0_snk.seen[86]));
        if (out0_snk.seen[86] !== 32'h00000589) begin
            errors = errors + 1;
            $display("  FAIL vector 86 ({'a': 1448568866, 'n': 50}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[86]), out0_snk.seen[86], $signed(32'h00000589), 32'h00000589);
        end
        #(4 * T);

        // -- vector 87: {'a': -1655902217, 'n': 49} -> {'out0': -1655918737}
        cur = 87;
        fork
            a_src.send(32'h9d4ceff7);
            n_src.send(32'h00000031);
            start_src.send;
            wait (out0_snk.n == 88);
            wait (p_end_snk.n == 88);
        join
        $display("OUT 87 %0d", $signed(out0_snk.seen[87]));
        if (out0_snk.seen[87] !== 32'h9d4caf6f) begin
            errors = errors + 1;
            $display("  FAIL vector 87 ({'a': -1655902217, 'n': 49}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[87]), out0_snk.seen[87], $signed(32'h9d4caf6f), 32'h9d4caf6f);
        end
        #(4 * T);

        // -- vector 88: {'a': -1862049654, 'n': 7} -> {'out0': -1862049633}
        cur = 88;
        fork
            a_src.send(32'h9103608a);
            n_src.send(32'h00000007);
            start_src.send;
            wait (out0_snk.n == 89);
            wait (p_end_snk.n == 89);
        join
        $display("OUT 88 %0d", $signed(out0_snk.seen[88]));
        if (out0_snk.seen[88] !== 32'h9103609f) begin
            errors = errors + 1;
            $display("  FAIL vector 88 ({'a': -1862049654, 'n': 7}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[88]), out0_snk.seen[88], $signed(32'h9103609f), 32'h9103609f);
        end
        #(4 * T);

        // -- vector 89: {'a': 1454909253, 'n': 58} -> {'out0': 247}
        cur = 89;
        fork
            a_src.send(32'h56b82745);
            n_src.send(32'h0000003a);
            start_src.send;
            wait (out0_snk.n == 90);
            wait (p_end_snk.n == 90);
        join
        $display("OUT 89 %0d", $signed(out0_snk.seen[89]));
        if (out0_snk.seen[89] !== 32'h000000f7) begin
            errors = errors + 1;
            $display("  FAIL vector 89 ({'a': 1454909253, 'n': 58}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[89]), out0_snk.seen[89], $signed(32'h000000f7), 32'h000000f7);
        end
        #(4 * T);

        // Teeth: a channel that never produced a token would pass every
        // comparison above by having nothing to compare.  Assert the
        // count explicitly, on every output channel.
        if (out0_snk.n != 90) begin
            errors = errors + 1;
            $display("  FAIL out0 produced %0d token(s), expected 90", out0_snk.n);
        end
        if (p_end_snk.n != 90) begin
            errors = errors + 1;
            $display("  FAIL p_end produced %0d token(s), expected 90", p_end_snk.n);
        end

        if (errors == 0) $display("tb_countloop PASS");
        else             $display("tb_countloop FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #20000000000;
        $display("tb_countloop FAIL (timeout) on vector %0d", cur);
        $display("    src a: %0d sent, req=%b ack=%b", a_src.nsent, a_req, a_ack);
        $display("    src n: %0d sent, req=%b ack=%b", n_src.nsent, n_req, n_ack);
        $display("    src start: %0d sent, req=%b ack=%b", start_src.nsent, start_req, start_ack);
        $display("    snk out0: %0d seen, req=%b ack=%b", out0_snk.n, out0_req, out0_ack);
        $display("    snk p_end: %0d seen, req=%b ack=%b", p_end_snk.n, p_end_req, p_end_ack);
        $finish;
    end

`ifdef SIMCHECK_VCD
    initial begin
        $dumpfile("tb_countloop.vcd");
        $dumpvars(0, tb_countloop);
    end
`endif
endmodule