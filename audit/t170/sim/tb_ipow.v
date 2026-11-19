
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

module tb_ipow;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer cur = -1;
    reg rst = 1'b1;

    wire b_req, b_ack;
    wire [31:0] b_data;
    bd_source #(.W(32)) b_src (.req(b_req), .ack(b_ack), .data(b_data));
    wire e_req, e_ack;
    wire [31:0] e_data;
    bd_source #(.W(32)) e_src (.req(e_req), .ack(e_ack), .data(e_data));
    wire start_req, start_ack;
    simcheck_ctl_src start_src (.req(start_req), .ack(start_ack));
    wire out0_req, out0_ack;
    wire [31:0] out0_data;
    bd_sink #(.W(32)) out0_snk (.req(out0_req), .ack(out0_ack), .data(out0_data));
    wire p_end_req, p_end_ack;
    simcheck_ctl_snk p_end_snk (.req(p_end_req), .ack(p_end_ack));

    bdc_ipow uut (
        .rst(rst),
        .b_req(b_req), .b_ack(b_ack), .b_data(b_data),
        .e_req(e_req), .e_ack(e_ack), .e_data(e_data),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    initial begin
        $display("tb_ipow");
        #(204 * T);
        rst = 1'b0;
        #(8 * T);

        // -- vector 0: {'b': 0, 'e': 0} -> {'out0': 1}
        cur = 0;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 1);
            wait (p_end_snk.n == 1);
        join
        $display("OUT 0 %0d", $signed(out0_snk.seen[0]));
        if (out0_snk.seen[0] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 0 ({'b': 0, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[0]), out0_snk.seen[0], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 1: {'b': 0, 'e': 1} -> {'out0': 0}
        cur = 1;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 2);
            wait (p_end_snk.n == 2);
        join
        $display("OUT 1 %0d", $signed(out0_snk.seen[1]));
        if (out0_snk.seen[1] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 1 ({'b': 0, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[1]), out0_snk.seen[1], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 2: {'b': 0, 'e': -1} -> {'out0': 1}
        cur = 2;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 3);
            wait (p_end_snk.n == 3);
        join
        $display("OUT 2 %0d", $signed(out0_snk.seen[2]));
        if (out0_snk.seen[2] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 2 ({'b': 0, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[2]), out0_snk.seen[2], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 3: {'b': 0, 'e': 2} -> {'out0': 0}
        cur = 3;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 4);
            wait (p_end_snk.n == 4);
        join
        $display("OUT 3 %0d", $signed(out0_snk.seen[3]));
        if (out0_snk.seen[3] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 3 ({'b': 0, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[3]), out0_snk.seen[3], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 4: {'b': 0, 'e': -2} -> {'out0': 1}
        cur = 4;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 5);
            wait (p_end_snk.n == 5);
        join
        $display("OUT 4 %0d", $signed(out0_snk.seen[4]));
        if (out0_snk.seen[4] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 4 ({'b': 0, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[4]), out0_snk.seen[4], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 5: {'b': 0, 'e': 2147483647} -> {'out0': 0}
        cur = 5;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 6);
            wait (p_end_snk.n == 6);
        join
        $display("OUT 5 %0d", $signed(out0_snk.seen[5]));
        if (out0_snk.seen[5] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 5 ({'b': 0, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[5]), out0_snk.seen[5], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 6: {'b': 0, 'e': -2147483648} -> {'out0': 1}
        cur = 6;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 7);
            wait (p_end_snk.n == 7);
        join
        $display("OUT 6 %0d", $signed(out0_snk.seen[6]));
        if (out0_snk.seen[6] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 6 ({'b': 0, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[6]), out0_snk.seen[6], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 7: {'b': 0, 'e': 1073741824} -> {'out0': 0}
        cur = 7;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 8);
            wait (p_end_snk.n == 8);
        join
        $display("OUT 7 %0d", $signed(out0_snk.seen[7]));
        if (out0_snk.seen[7] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 7 ({'b': 0, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[7]), out0_snk.seen[7], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 8: {'b': 0, 'e': 2147483646} -> {'out0': 0}
        cur = 8;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 9);
            wait (p_end_snk.n == 9);
        join
        $display("OUT 8 %0d", $signed(out0_snk.seen[8]));
        if (out0_snk.seen[8] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 8 ({'b': 0, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[8]), out0_snk.seen[8], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 9: {'b': 0, 'e': -2147483647} -> {'out0': 1}
        cur = 9;
        fork
            b_src.send(32'h00000000);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 10);
            wait (p_end_snk.n == 10);
        join
        $display("OUT 9 %0d", $signed(out0_snk.seen[9]));
        if (out0_snk.seen[9] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 9 ({'b': 0, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[9]), out0_snk.seen[9], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 10: {'b': 1, 'e': 0} -> {'out0': 1}
        cur = 10;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 11);
            wait (p_end_snk.n == 11);
        join
        $display("OUT 10 %0d", $signed(out0_snk.seen[10]));
        if (out0_snk.seen[10] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 10 ({'b': 1, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[10]), out0_snk.seen[10], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 11: {'b': 1, 'e': 1} -> {'out0': 1}
        cur = 11;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 12);
            wait (p_end_snk.n == 12);
        join
        $display("OUT 11 %0d", $signed(out0_snk.seen[11]));
        if (out0_snk.seen[11] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 11 ({'b': 1, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[11]), out0_snk.seen[11], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 12: {'b': 1, 'e': -1} -> {'out0': 1}
        cur = 12;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 13);
            wait (p_end_snk.n == 13);
        join
        $display("OUT 12 %0d", $signed(out0_snk.seen[12]));
        if (out0_snk.seen[12] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 12 ({'b': 1, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[12]), out0_snk.seen[12], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 13: {'b': 1, 'e': 2} -> {'out0': 1}
        cur = 13;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 14);
            wait (p_end_snk.n == 14);
        join
        $display("OUT 13 %0d", $signed(out0_snk.seen[13]));
        if (out0_snk.seen[13] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 13 ({'b': 1, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[13]), out0_snk.seen[13], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 14: {'b': 1, 'e': -2} -> {'out0': 1}
        cur = 14;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 15);
            wait (p_end_snk.n == 15);
        join
        $display("OUT 14 %0d", $signed(out0_snk.seen[14]));
        if (out0_snk.seen[14] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 14 ({'b': 1, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[14]), out0_snk.seen[14], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 15: {'b': 1, 'e': 2147483647} -> {'out0': 1}
        cur = 15;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 16);
            wait (p_end_snk.n == 16);
        join
        $display("OUT 15 %0d", $signed(out0_snk.seen[15]));
        if (out0_snk.seen[15] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 15 ({'b': 1, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[15]), out0_snk.seen[15], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 16: {'b': 1, 'e': -2147483648} -> {'out0': 1}
        cur = 16;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 17);
            wait (p_end_snk.n == 17);
        join
        $display("OUT 16 %0d", $signed(out0_snk.seen[16]));
        if (out0_snk.seen[16] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 16 ({'b': 1, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[16]), out0_snk.seen[16], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 17: {'b': 1, 'e': 1073741824} -> {'out0': 1}
        cur = 17;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 18);
            wait (p_end_snk.n == 18);
        join
        $display("OUT 17 %0d", $signed(out0_snk.seen[17]));
        if (out0_snk.seen[17] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 17 ({'b': 1, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[17]), out0_snk.seen[17], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 18: {'b': 1, 'e': 2147483646} -> {'out0': 1}
        cur = 18;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 19);
            wait (p_end_snk.n == 19);
        join
        $display("OUT 18 %0d", $signed(out0_snk.seen[18]));
        if (out0_snk.seen[18] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 18 ({'b': 1, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[18]), out0_snk.seen[18], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 19: {'b': 1, 'e': -2147483647} -> {'out0': 1}
        cur = 19;
        fork
            b_src.send(32'h00000001);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 20);
            wait (p_end_snk.n == 20);
        join
        $display("OUT 19 %0d", $signed(out0_snk.seen[19]));
        if (out0_snk.seen[19] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 19 ({'b': 1, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[19]), out0_snk.seen[19], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 20: {'b': -1, 'e': 0} -> {'out0': 1}
        cur = 20;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 21);
            wait (p_end_snk.n == 21);
        join
        $display("OUT 20 %0d", $signed(out0_snk.seen[20]));
        if (out0_snk.seen[20] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 20 ({'b': -1, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[20]), out0_snk.seen[20], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 21: {'b': -1, 'e': 1} -> {'out0': -1}
        cur = 21;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 22);
            wait (p_end_snk.n == 22);
        join
        $display("OUT 21 %0d", $signed(out0_snk.seen[21]));
        if (out0_snk.seen[21] !== 32'hffffffff) begin
            errors = errors + 1;
            $display("  FAIL vector 21 ({'b': -1, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[21]), out0_snk.seen[21], $signed(32'hffffffff), 32'hffffffff);
        end
        #(4 * T);

        // -- vector 22: {'b': -1, 'e': -1} -> {'out0': 1}
        cur = 22;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 23);
            wait (p_end_snk.n == 23);
        join
        $display("OUT 22 %0d", $signed(out0_snk.seen[22]));
        if (out0_snk.seen[22] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 22 ({'b': -1, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[22]), out0_snk.seen[22], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 23: {'b': -1, 'e': 2} -> {'out0': 1}
        cur = 23;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 24);
            wait (p_end_snk.n == 24);
        join
        $display("OUT 23 %0d", $signed(out0_snk.seen[23]));
        if (out0_snk.seen[23] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 23 ({'b': -1, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[23]), out0_snk.seen[23], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 24: {'b': -1, 'e': -2} -> {'out0': 1}
        cur = 24;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 25);
            wait (p_end_snk.n == 25);
        join
        $display("OUT 24 %0d", $signed(out0_snk.seen[24]));
        if (out0_snk.seen[24] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 24 ({'b': -1, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[24]), out0_snk.seen[24], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 25: {'b': -1, 'e': 2147483647} -> {'out0': -1}
        cur = 25;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 26);
            wait (p_end_snk.n == 26);
        join
        $display("OUT 25 %0d", $signed(out0_snk.seen[25]));
        if (out0_snk.seen[25] !== 32'hffffffff) begin
            errors = errors + 1;
            $display("  FAIL vector 25 ({'b': -1, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[25]), out0_snk.seen[25], $signed(32'hffffffff), 32'hffffffff);
        end
        #(4 * T);

        // -- vector 26: {'b': -1, 'e': -2147483648} -> {'out0': 1}
        cur = 26;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 27);
            wait (p_end_snk.n == 27);
        join
        $display("OUT 26 %0d", $signed(out0_snk.seen[26]));
        if (out0_snk.seen[26] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 26 ({'b': -1, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[26]), out0_snk.seen[26], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 27: {'b': -1, 'e': 1073741824} -> {'out0': 1}
        cur = 27;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 28);
            wait (p_end_snk.n == 28);
        join
        $display("OUT 27 %0d", $signed(out0_snk.seen[27]));
        if (out0_snk.seen[27] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 27 ({'b': -1, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[27]), out0_snk.seen[27], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 28: {'b': -1, 'e': 2147483646} -> {'out0': 1}
        cur = 28;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 29);
            wait (p_end_snk.n == 29);
        join
        $display("OUT 28 %0d", $signed(out0_snk.seen[28]));
        if (out0_snk.seen[28] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 28 ({'b': -1, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[28]), out0_snk.seen[28], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 29: {'b': -1, 'e': -2147483647} -> {'out0': 1}
        cur = 29;
        fork
            b_src.send(32'hffffffff);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 30);
            wait (p_end_snk.n == 30);
        join
        $display("OUT 29 %0d", $signed(out0_snk.seen[29]));
        if (out0_snk.seen[29] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 29 ({'b': -1, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[29]), out0_snk.seen[29], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 30: {'b': 2, 'e': 0} -> {'out0': 1}
        cur = 30;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 31);
            wait (p_end_snk.n == 31);
        join
        $display("OUT 30 %0d", $signed(out0_snk.seen[30]));
        if (out0_snk.seen[30] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 30 ({'b': 2, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[30]), out0_snk.seen[30], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 31: {'b': 2, 'e': 1} -> {'out0': 2}
        cur = 31;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 32);
            wait (p_end_snk.n == 32);
        join
        $display("OUT 31 %0d", $signed(out0_snk.seen[31]));
        if (out0_snk.seen[31] !== 32'h00000002) begin
            errors = errors + 1;
            $display("  FAIL vector 31 ({'b': 2, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[31]), out0_snk.seen[31], $signed(32'h00000002), 32'h00000002);
        end
        #(4 * T);

        // -- vector 32: {'b': 2, 'e': -1} -> {'out0': 1}
        cur = 32;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 33);
            wait (p_end_snk.n == 33);
        join
        $display("OUT 32 %0d", $signed(out0_snk.seen[32]));
        if (out0_snk.seen[32] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 32 ({'b': 2, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[32]), out0_snk.seen[32], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 33: {'b': 2, 'e': 2} -> {'out0': 4}
        cur = 33;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 34);
            wait (p_end_snk.n == 34);
        join
        $display("OUT 33 %0d", $signed(out0_snk.seen[33]));
        if (out0_snk.seen[33] !== 32'h00000004) begin
            errors = errors + 1;
            $display("  FAIL vector 33 ({'b': 2, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[33]), out0_snk.seen[33], $signed(32'h00000004), 32'h00000004);
        end
        #(4 * T);

        // -- vector 34: {'b': 2, 'e': -2} -> {'out0': 1}
        cur = 34;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 35);
            wait (p_end_snk.n == 35);
        join
        $display("OUT 34 %0d", $signed(out0_snk.seen[34]));
        if (out0_snk.seen[34] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 34 ({'b': 2, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[34]), out0_snk.seen[34], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 35: {'b': 2, 'e': 2147483647} -> {'out0': 0}
        cur = 35;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 36);
            wait (p_end_snk.n == 36);
        join
        $display("OUT 35 %0d", $signed(out0_snk.seen[35]));
        if (out0_snk.seen[35] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 35 ({'b': 2, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[35]), out0_snk.seen[35], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 36: {'b': 2, 'e': -2147483648} -> {'out0': 1}
        cur = 36;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 37);
            wait (p_end_snk.n == 37);
        join
        $display("OUT 36 %0d", $signed(out0_snk.seen[36]));
        if (out0_snk.seen[36] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 36 ({'b': 2, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[36]), out0_snk.seen[36], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 37: {'b': 2, 'e': 1073741824} -> {'out0': 0}
        cur = 37;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 38);
            wait (p_end_snk.n == 38);
        join
        $display("OUT 37 %0d", $signed(out0_snk.seen[37]));
        if (out0_snk.seen[37] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 37 ({'b': 2, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[37]), out0_snk.seen[37], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 38: {'b': 2, 'e': 2147483646} -> {'out0': 0}
        cur = 38;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 39);
            wait (p_end_snk.n == 39);
        join
        $display("OUT 38 %0d", $signed(out0_snk.seen[38]));
        if (out0_snk.seen[38] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 38 ({'b': 2, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[38]), out0_snk.seen[38], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 39: {'b': 2, 'e': -2147483647} -> {'out0': 1}
        cur = 39;
        fork
            b_src.send(32'h00000002);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 40);
            wait (p_end_snk.n == 40);
        join
        $display("OUT 39 %0d", $signed(out0_snk.seen[39]));
        if (out0_snk.seen[39] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 39 ({'b': 2, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[39]), out0_snk.seen[39], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 40: {'b': -2, 'e': 0} -> {'out0': 1}
        cur = 40;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 41);
            wait (p_end_snk.n == 41);
        join
        $display("OUT 40 %0d", $signed(out0_snk.seen[40]));
        if (out0_snk.seen[40] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 40 ({'b': -2, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[40]), out0_snk.seen[40], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 41: {'b': -2, 'e': 1} -> {'out0': -2}
        cur = 41;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 42);
            wait (p_end_snk.n == 42);
        join
        $display("OUT 41 %0d", $signed(out0_snk.seen[41]));
        if (out0_snk.seen[41] !== 32'hfffffffe) begin
            errors = errors + 1;
            $display("  FAIL vector 41 ({'b': -2, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[41]), out0_snk.seen[41], $signed(32'hfffffffe), 32'hfffffffe);
        end
        #(4 * T);

        // -- vector 42: {'b': -2, 'e': -1} -> {'out0': 1}
        cur = 42;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 43);
            wait (p_end_snk.n == 43);
        join
        $display("OUT 42 %0d", $signed(out0_snk.seen[42]));
        if (out0_snk.seen[42] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 42 ({'b': -2, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[42]), out0_snk.seen[42], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 43: {'b': -2, 'e': 2} -> {'out0': 4}
        cur = 43;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 44);
            wait (p_end_snk.n == 44);
        join
        $display("OUT 43 %0d", $signed(out0_snk.seen[43]));
        if (out0_snk.seen[43] !== 32'h00000004) begin
            errors = errors + 1;
            $display("  FAIL vector 43 ({'b': -2, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[43]), out0_snk.seen[43], $signed(32'h00000004), 32'h00000004);
        end
        #(4 * T);

        // -- vector 44: {'b': -2, 'e': -2} -> {'out0': 1}
        cur = 44;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 45);
            wait (p_end_snk.n == 45);
        join
        $display("OUT 44 %0d", $signed(out0_snk.seen[44]));
        if (out0_snk.seen[44] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 44 ({'b': -2, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[44]), out0_snk.seen[44], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 45: {'b': -2, 'e': 2147483647} -> {'out0': 0}
        cur = 45;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 46);
            wait (p_end_snk.n == 46);
        join
        $display("OUT 45 %0d", $signed(out0_snk.seen[45]));
        if (out0_snk.seen[45] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 45 ({'b': -2, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[45]), out0_snk.seen[45], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 46: {'b': -2, 'e': -2147483648} -> {'out0': 1}
        cur = 46;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 47);
            wait (p_end_snk.n == 47);
        join
        $display("OUT 46 %0d", $signed(out0_snk.seen[46]));
        if (out0_snk.seen[46] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 46 ({'b': -2, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[46]), out0_snk.seen[46], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 47: {'b': -2, 'e': 1073741824} -> {'out0': 0}
        cur = 47;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 48);
            wait (p_end_snk.n == 48);
        join
        $display("OUT 47 %0d", $signed(out0_snk.seen[47]));
        if (out0_snk.seen[47] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 47 ({'b': -2, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[47]), out0_snk.seen[47], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 48: {'b': -2, 'e': 2147483646} -> {'out0': 0}
        cur = 48;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 49);
            wait (p_end_snk.n == 49);
        join
        $display("OUT 48 %0d", $signed(out0_snk.seen[48]));
        if (out0_snk.seen[48] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 48 ({'b': -2, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[48]), out0_snk.seen[48], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 49: {'b': -2, 'e': -2147483647} -> {'out0': 1}
        cur = 49;
        fork
            b_src.send(32'hfffffffe);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 50);
            wait (p_end_snk.n == 50);
        join
        $display("OUT 49 %0d", $signed(out0_snk.seen[49]));
        if (out0_snk.seen[49] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 49 ({'b': -2, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[49]), out0_snk.seen[49], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 50: {'b': 2147483647, 'e': 0} -> {'out0': 1}
        cur = 50;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 51);
            wait (p_end_snk.n == 51);
        join
        $display("OUT 50 %0d", $signed(out0_snk.seen[50]));
        if (out0_snk.seen[50] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 50 ({'b': 2147483647, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[50]), out0_snk.seen[50], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 51: {'b': 2147483647, 'e': 1} -> {'out0': 2147483647}
        cur = 51;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 52);
            wait (p_end_snk.n == 52);
        join
        $display("OUT 51 %0d", $signed(out0_snk.seen[51]));
        if (out0_snk.seen[51] !== 32'h7fffffff) begin
            errors = errors + 1;
            $display("  FAIL vector 51 ({'b': 2147483647, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[51]), out0_snk.seen[51], $signed(32'h7fffffff), 32'h7fffffff);
        end
        #(4 * T);

        // -- vector 52: {'b': 2147483647, 'e': -1} -> {'out0': 1}
        cur = 52;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 53);
            wait (p_end_snk.n == 53);
        join
        $display("OUT 52 %0d", $signed(out0_snk.seen[52]));
        if (out0_snk.seen[52] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 52 ({'b': 2147483647, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[52]), out0_snk.seen[52], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 53: {'b': 2147483647, 'e': 2} -> {'out0': 1}
        cur = 53;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 54);
            wait (p_end_snk.n == 54);
        join
        $display("OUT 53 %0d", $signed(out0_snk.seen[53]));
        if (out0_snk.seen[53] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 53 ({'b': 2147483647, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[53]), out0_snk.seen[53], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 54: {'b': 2147483647, 'e': -2} -> {'out0': 1}
        cur = 54;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 55);
            wait (p_end_snk.n == 55);
        join
        $display("OUT 54 %0d", $signed(out0_snk.seen[54]));
        if (out0_snk.seen[54] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 54 ({'b': 2147483647, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[54]), out0_snk.seen[54], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 55: {'b': 2147483647, 'e': 2147483647} -> {'out0': 2147483647}
        cur = 55;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 56);
            wait (p_end_snk.n == 56);
        join
        $display("OUT 55 %0d", $signed(out0_snk.seen[55]));
        if (out0_snk.seen[55] !== 32'h7fffffff) begin
            errors = errors + 1;
            $display("  FAIL vector 55 ({'b': 2147483647, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[55]), out0_snk.seen[55], $signed(32'h7fffffff), 32'h7fffffff);
        end
        #(4 * T);

        // -- vector 56: {'b': 2147483647, 'e': -2147483648} -> {'out0': 1}
        cur = 56;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 57);
            wait (p_end_snk.n == 57);
        join
        $display("OUT 56 %0d", $signed(out0_snk.seen[56]));
        if (out0_snk.seen[56] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 56 ({'b': 2147483647, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[56]), out0_snk.seen[56], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 57: {'b': 2147483647, 'e': 1073741824} -> {'out0': 1}
        cur = 57;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 58);
            wait (p_end_snk.n == 58);
        join
        $display("OUT 57 %0d", $signed(out0_snk.seen[57]));
        if (out0_snk.seen[57] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 57 ({'b': 2147483647, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[57]), out0_snk.seen[57], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 58: {'b': 2147483647, 'e': 2147483646} -> {'out0': 1}
        cur = 58;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 59);
            wait (p_end_snk.n == 59);
        join
        $display("OUT 58 %0d", $signed(out0_snk.seen[58]));
        if (out0_snk.seen[58] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 58 ({'b': 2147483647, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[58]), out0_snk.seen[58], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 59: {'b': 2147483647, 'e': -2147483647} -> {'out0': 1}
        cur = 59;
        fork
            b_src.send(32'h7fffffff);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 60);
            wait (p_end_snk.n == 60);
        join
        $display("OUT 59 %0d", $signed(out0_snk.seen[59]));
        if (out0_snk.seen[59] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 59 ({'b': 2147483647, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[59]), out0_snk.seen[59], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 60: {'b': -2147483648, 'e': 0} -> {'out0': 1}
        cur = 60;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 61);
            wait (p_end_snk.n == 61);
        join
        $display("OUT 60 %0d", $signed(out0_snk.seen[60]));
        if (out0_snk.seen[60] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 60 ({'b': -2147483648, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[60]), out0_snk.seen[60], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 61: {'b': -2147483648, 'e': 1} -> {'out0': -2147483648}
        cur = 61;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 62);
            wait (p_end_snk.n == 62);
        join
        $display("OUT 61 %0d", $signed(out0_snk.seen[61]));
        if (out0_snk.seen[61] !== 32'h80000000) begin
            errors = errors + 1;
            $display("  FAIL vector 61 ({'b': -2147483648, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[61]), out0_snk.seen[61], $signed(32'h80000000), 32'h80000000);
        end
        #(4 * T);

        // -- vector 62: {'b': -2147483648, 'e': -1} -> {'out0': 1}
        cur = 62;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 63);
            wait (p_end_snk.n == 63);
        join
        $display("OUT 62 %0d", $signed(out0_snk.seen[62]));
        if (out0_snk.seen[62] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 62 ({'b': -2147483648, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[62]), out0_snk.seen[62], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 63: {'b': -2147483648, 'e': 2} -> {'out0': 0}
        cur = 63;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 64);
            wait (p_end_snk.n == 64);
        join
        $display("OUT 63 %0d", $signed(out0_snk.seen[63]));
        if (out0_snk.seen[63] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 63 ({'b': -2147483648, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[63]), out0_snk.seen[63], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 64: {'b': -2147483648, 'e': -2} -> {'out0': 1}
        cur = 64;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 65);
            wait (p_end_snk.n == 65);
        join
        $display("OUT 64 %0d", $signed(out0_snk.seen[64]));
        if (out0_snk.seen[64] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 64 ({'b': -2147483648, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[64]), out0_snk.seen[64], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 65: {'b': -2147483648, 'e': 2147483647} -> {'out0': 0}
        cur = 65;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 66);
            wait (p_end_snk.n == 66);
        join
        $display("OUT 65 %0d", $signed(out0_snk.seen[65]));
        if (out0_snk.seen[65] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 65 ({'b': -2147483648, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[65]), out0_snk.seen[65], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 66: {'b': -2147483648, 'e': -2147483648} -> {'out0': 1}
        cur = 66;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 67);
            wait (p_end_snk.n == 67);
        join
        $display("OUT 66 %0d", $signed(out0_snk.seen[66]));
        if (out0_snk.seen[66] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 66 ({'b': -2147483648, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[66]), out0_snk.seen[66], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 67: {'b': -2147483648, 'e': 1073741824} -> {'out0': 0}
        cur = 67;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 68);
            wait (p_end_snk.n == 68);
        join
        $display("OUT 67 %0d", $signed(out0_snk.seen[67]));
        if (out0_snk.seen[67] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 67 ({'b': -2147483648, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[67]), out0_snk.seen[67], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 68: {'b': -2147483648, 'e': 2147483646} -> {'out0': 0}
        cur = 68;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 69);
            wait (p_end_snk.n == 69);
        join
        $display("OUT 68 %0d", $signed(out0_snk.seen[68]));
        if (out0_snk.seen[68] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 68 ({'b': -2147483648, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[68]), out0_snk.seen[68], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 69: {'b': -2147483648, 'e': -2147483647} -> {'out0': 1}
        cur = 69;
        fork
            b_src.send(32'h80000000);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 70);
            wait (p_end_snk.n == 70);
        join
        $display("OUT 69 %0d", $signed(out0_snk.seen[69]));
        if (out0_snk.seen[69] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 69 ({'b': -2147483648, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[69]), out0_snk.seen[69], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 70: {'b': 1073741824, 'e': 0} -> {'out0': 1}
        cur = 70;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 71);
            wait (p_end_snk.n == 71);
        join
        $display("OUT 70 %0d", $signed(out0_snk.seen[70]));
        if (out0_snk.seen[70] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 70 ({'b': 1073741824, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[70]), out0_snk.seen[70], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 71: {'b': 1073741824, 'e': 1} -> {'out0': 1073741824}
        cur = 71;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 72);
            wait (p_end_snk.n == 72);
        join
        $display("OUT 71 %0d", $signed(out0_snk.seen[71]));
        if (out0_snk.seen[71] !== 32'h40000000) begin
            errors = errors + 1;
            $display("  FAIL vector 71 ({'b': 1073741824, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[71]), out0_snk.seen[71], $signed(32'h40000000), 32'h40000000);
        end
        #(4 * T);

        // -- vector 72: {'b': 1073741824, 'e': -1} -> {'out0': 1}
        cur = 72;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 73);
            wait (p_end_snk.n == 73);
        join
        $display("OUT 72 %0d", $signed(out0_snk.seen[72]));
        if (out0_snk.seen[72] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 72 ({'b': 1073741824, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[72]), out0_snk.seen[72], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 73: {'b': 1073741824, 'e': 2} -> {'out0': 0}
        cur = 73;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 74);
            wait (p_end_snk.n == 74);
        join
        $display("OUT 73 %0d", $signed(out0_snk.seen[73]));
        if (out0_snk.seen[73] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 73 ({'b': 1073741824, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[73]), out0_snk.seen[73], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 74: {'b': 1073741824, 'e': -2} -> {'out0': 1}
        cur = 74;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 75);
            wait (p_end_snk.n == 75);
        join
        $display("OUT 74 %0d", $signed(out0_snk.seen[74]));
        if (out0_snk.seen[74] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 74 ({'b': 1073741824, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[74]), out0_snk.seen[74], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 75: {'b': 1073741824, 'e': 2147483647} -> {'out0': 0}
        cur = 75;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 76);
            wait (p_end_snk.n == 76);
        join
        $display("OUT 75 %0d", $signed(out0_snk.seen[75]));
        if (out0_snk.seen[75] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 75 ({'b': 1073741824, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[75]), out0_snk.seen[75], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 76: {'b': 1073741824, 'e': -2147483648} -> {'out0': 1}
        cur = 76;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 77);
            wait (p_end_snk.n == 77);
        join
        $display("OUT 76 %0d", $signed(out0_snk.seen[76]));
        if (out0_snk.seen[76] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 76 ({'b': 1073741824, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[76]), out0_snk.seen[76], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 77: {'b': 1073741824, 'e': 1073741824} -> {'out0': 0}
        cur = 77;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 78);
            wait (p_end_snk.n == 78);
        join
        $display("OUT 77 %0d", $signed(out0_snk.seen[77]));
        if (out0_snk.seen[77] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 77 ({'b': 1073741824, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[77]), out0_snk.seen[77], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 78: {'b': 1073741824, 'e': 2147483646} -> {'out0': 0}
        cur = 78;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 79);
            wait (p_end_snk.n == 79);
        join
        $display("OUT 78 %0d", $signed(out0_snk.seen[78]));
        if (out0_snk.seen[78] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 78 ({'b': 1073741824, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[78]), out0_snk.seen[78], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 79: {'b': 1073741824, 'e': -2147483647} -> {'out0': 1}
        cur = 79;
        fork
            b_src.send(32'h40000000);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 80);
            wait (p_end_snk.n == 80);
        join
        $display("OUT 79 %0d", $signed(out0_snk.seen[79]));
        if (out0_snk.seen[79] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 79 ({'b': 1073741824, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[79]), out0_snk.seen[79], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 80: {'b': 2147483646, 'e': 0} -> {'out0': 1}
        cur = 80;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 81);
            wait (p_end_snk.n == 81);
        join
        $display("OUT 80 %0d", $signed(out0_snk.seen[80]));
        if (out0_snk.seen[80] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 80 ({'b': 2147483646, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[80]), out0_snk.seen[80], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 81: {'b': 2147483646, 'e': 1} -> {'out0': 2147483646}
        cur = 81;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 82);
            wait (p_end_snk.n == 82);
        join
        $display("OUT 81 %0d", $signed(out0_snk.seen[81]));
        if (out0_snk.seen[81] !== 32'h7ffffffe) begin
            errors = errors + 1;
            $display("  FAIL vector 81 ({'b': 2147483646, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[81]), out0_snk.seen[81], $signed(32'h7ffffffe), 32'h7ffffffe);
        end
        #(4 * T);

        // -- vector 82: {'b': 2147483646, 'e': -1} -> {'out0': 1}
        cur = 82;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 83);
            wait (p_end_snk.n == 83);
        join
        $display("OUT 82 %0d", $signed(out0_snk.seen[82]));
        if (out0_snk.seen[82] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 82 ({'b': 2147483646, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[82]), out0_snk.seen[82], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 83: {'b': 2147483646, 'e': 2} -> {'out0': 4}
        cur = 83;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 84);
            wait (p_end_snk.n == 84);
        join
        $display("OUT 83 %0d", $signed(out0_snk.seen[83]));
        if (out0_snk.seen[83] !== 32'h00000004) begin
            errors = errors + 1;
            $display("  FAIL vector 83 ({'b': 2147483646, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[83]), out0_snk.seen[83], $signed(32'h00000004), 32'h00000004);
        end
        #(4 * T);

        // -- vector 84: {'b': 2147483646, 'e': -2} -> {'out0': 1}
        cur = 84;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 85);
            wait (p_end_snk.n == 85);
        join
        $display("OUT 84 %0d", $signed(out0_snk.seen[84]));
        if (out0_snk.seen[84] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 84 ({'b': 2147483646, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[84]), out0_snk.seen[84], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 85: {'b': 2147483646, 'e': 2147483647} -> {'out0': 0}
        cur = 85;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 86);
            wait (p_end_snk.n == 86);
        join
        $display("OUT 85 %0d", $signed(out0_snk.seen[85]));
        if (out0_snk.seen[85] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 85 ({'b': 2147483646, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[85]), out0_snk.seen[85], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 86: {'b': 2147483646, 'e': -2147483648} -> {'out0': 1}
        cur = 86;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 87);
            wait (p_end_snk.n == 87);
        join
        $display("OUT 86 %0d", $signed(out0_snk.seen[86]));
        if (out0_snk.seen[86] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 86 ({'b': 2147483646, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[86]), out0_snk.seen[86], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 87: {'b': 2147483646, 'e': 1073741824} -> {'out0': 0}
        cur = 87;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 88);
            wait (p_end_snk.n == 88);
        join
        $display("OUT 87 %0d", $signed(out0_snk.seen[87]));
        if (out0_snk.seen[87] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 87 ({'b': 2147483646, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[87]), out0_snk.seen[87], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 88: {'b': 2147483646, 'e': 2147483646} -> {'out0': 0}
        cur = 88;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 89);
            wait (p_end_snk.n == 89);
        join
        $display("OUT 88 %0d", $signed(out0_snk.seen[88]));
        if (out0_snk.seen[88] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 88 ({'b': 2147483646, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[88]), out0_snk.seen[88], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 89: {'b': 2147483646, 'e': -2147483647} -> {'out0': 1}
        cur = 89;
        fork
            b_src.send(32'h7ffffffe);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 90);
            wait (p_end_snk.n == 90);
        join
        $display("OUT 89 %0d", $signed(out0_snk.seen[89]));
        if (out0_snk.seen[89] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 89 ({'b': 2147483646, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[89]), out0_snk.seen[89], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 90: {'b': -2147483647, 'e': 0} -> {'out0': 1}
        cur = 90;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 91);
            wait (p_end_snk.n == 91);
        join
        $display("OUT 90 %0d", $signed(out0_snk.seen[90]));
        if (out0_snk.seen[90] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 90 ({'b': -2147483647, 'e': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[90]), out0_snk.seen[90], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 91: {'b': -2147483647, 'e': 1} -> {'out0': -2147483647}
        cur = 91;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 92);
            wait (p_end_snk.n == 92);
        join
        $display("OUT 91 %0d", $signed(out0_snk.seen[91]));
        if (out0_snk.seen[91] !== 32'h80000001) begin
            errors = errors + 1;
            $display("  FAIL vector 91 ({'b': -2147483647, 'e': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[91]), out0_snk.seen[91], $signed(32'h80000001), 32'h80000001);
        end
        #(4 * T);

        // -- vector 92: {'b': -2147483647, 'e': -1} -> {'out0': 1}
        cur = 92;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 93);
            wait (p_end_snk.n == 93);
        join
        $display("OUT 92 %0d", $signed(out0_snk.seen[92]));
        if (out0_snk.seen[92] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 92 ({'b': -2147483647, 'e': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[92]), out0_snk.seen[92], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 93: {'b': -2147483647, 'e': 2} -> {'out0': 1}
        cur = 93;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 94);
            wait (p_end_snk.n == 94);
        join
        $display("OUT 93 %0d", $signed(out0_snk.seen[93]));
        if (out0_snk.seen[93] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 93 ({'b': -2147483647, 'e': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[93]), out0_snk.seen[93], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 94: {'b': -2147483647, 'e': -2} -> {'out0': 1}
        cur = 94;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 95);
            wait (p_end_snk.n == 95);
        join
        $display("OUT 94 %0d", $signed(out0_snk.seen[94]));
        if (out0_snk.seen[94] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 94 ({'b': -2147483647, 'e': -2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[94]), out0_snk.seen[94], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 95: {'b': -2147483647, 'e': 2147483647} -> {'out0': -2147483647}
        cur = 95;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h7fffffff);
            start_src.send;
            wait (out0_snk.n == 96);
            wait (p_end_snk.n == 96);
        join
        $display("OUT 95 %0d", $signed(out0_snk.seen[95]));
        if (out0_snk.seen[95] !== 32'h80000001) begin
            errors = errors + 1;
            $display("  FAIL vector 95 ({'b': -2147483647, 'e': 2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[95]), out0_snk.seen[95], $signed(32'h80000001), 32'h80000001);
        end
        #(4 * T);

        // -- vector 96: {'b': -2147483647, 'e': -2147483648} -> {'out0': 1}
        cur = 96;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 97);
            wait (p_end_snk.n == 97);
        join
        $display("OUT 96 %0d", $signed(out0_snk.seen[96]));
        if (out0_snk.seen[96] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 96 ({'b': -2147483647, 'e': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[96]), out0_snk.seen[96], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 97: {'b': -2147483647, 'e': 1073741824} -> {'out0': 1}
        cur = 97;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 98);
            wait (p_end_snk.n == 98);
        join
        $display("OUT 97 %0d", $signed(out0_snk.seen[97]));
        if (out0_snk.seen[97] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 97 ({'b': -2147483647, 'e': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[97]), out0_snk.seen[97], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 98: {'b': -2147483647, 'e': 2147483646} -> {'out0': 1}
        cur = 98;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h7ffffffe);
            start_src.send;
            wait (out0_snk.n == 99);
            wait (p_end_snk.n == 99);
        join
        $display("OUT 98 %0d", $signed(out0_snk.seen[98]));
        if (out0_snk.seen[98] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 98 ({'b': -2147483647, 'e': 2147483646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[98]), out0_snk.seen[98], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 99: {'b': -2147483647, 'e': -2147483647} -> {'out0': 1}
        cur = 99;
        fork
            b_src.send(32'h80000001);
            e_src.send(32'h80000001);
            start_src.send;
            wait (out0_snk.n == 100);
            wait (p_end_snk.n == 100);
        join
        $display("OUT 99 %0d", $signed(out0_snk.seen[99]));
        if (out0_snk.seen[99] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 99 ({'b': -2147483647, 'e': -2147483647}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[99]), out0_snk.seen[99], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 100: {'b': 557127529, 'e': -1269035707} -> {'out0': 1}
        cur = 100;
        fork
            b_src.send(32'h21351769);
            e_src.send(32'hb45c0d45);
            start_src.send;
            wait (out0_snk.n == 101);
            wait (p_end_snk.n == 101);
        join
        $display("OUT 100 %0d", $signed(out0_snk.seen[100]));
        if (out0_snk.seen[100] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 100 ({'b': 557127529, 'e': -1269035707}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[100]), out0_snk.seen[100], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 101: {'b': 506690608, 'e': -779914030} -> {'out0': 1}
        cur = 101;
        fork
            b_src.send(32'h1e337c30);
            e_src.send(32'hd18374d2);
            start_src.send;
            wait (out0_snk.n == 102);
            wait (p_end_snk.n == 102);
        join
        $display("OUT 101 %0d", $signed(out0_snk.seen[101]));
        if (out0_snk.seen[101] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 101 ({'b': 506690608, 'e': -779914030}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[101]), out0_snk.seen[101], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 102: {'b': -528465477, 'e': 201064711} -> {'out0': 1242865939}
        cur = 102;
        fork
            b_src.send(32'he08041bb);
            e_src.send(32'h0bfc0107);
            start_src.send;
            wait (out0_snk.n == 103);
            wait (p_end_snk.n == 103);
        join
        $display("OUT 102 %0d", $signed(out0_snk.seen[102]));
        if (out0_snk.seen[102] !== 32'h4a14a113) begin
            errors = errors + 1;
            $display("  FAIL vector 102 ({'b': -528465477, 'e': 201064711}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[102]), out0_snk.seen[102], $signed(32'h4a14a113), 32'h4a14a113);
        end
        #(4 * T);

        // -- vector 103: {'b': 1126259074, 'e': -1985152565} -> {'out0': 1}
        cur = 103;
        fork
            b_src.send(32'h43215982);
            e_src.send(32'h89acf9cb);
            start_src.send;
            wait (out0_snk.n == 104);
            wait (p_end_snk.n == 104);
        join
        $display("OUT 103 %0d", $signed(out0_snk.seen[103]));
        if (out0_snk.seen[103] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 103 ({'b': 1126259074, 'e': -1985152565}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[103]), out0_snk.seen[103], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 104: {'b': -260003247, 'e': -1596169006} -> {'out0': 1}
        cur = 104;
        fork
            b_src.send(32'hf080aa51);
            e_src.send(32'ha0dc64d2);
            start_src.send;
            wait (out0_snk.n == 105);
            wait (p_end_snk.n == 105);
        join
        $display("OUT 104 %0d", $signed(out0_snk.seen[104]));
        if (out0_snk.seen[104] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 104 ({'b': -260003247, 'e': -1596169006}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[104]), out0_snk.seen[104], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 105: {'b': 293316103, 'e': 1608793710} -> {'out0': 1844243281}
        cur = 105;
        fork
            b_src.send(32'h117ba607);
            e_src.send(32'h5fe43e6e);
            start_src.send;
            wait (out0_snk.n == 106);
            wait (p_end_snk.n == 106);
        join
        $display("OUT 105 %0d", $signed(out0_snk.seen[105]));
        if (out0_snk.seen[105] !== 32'h6deceb51) begin
            errors = errors + 1;
            $display("  FAIL vector 105 ({'b': 293316103, 'e': 1608793710}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[105]), out0_snk.seen[105], $signed(32'h6deceb51), 32'h6deceb51);
        end
        #(4 * T);

        // -- vector 106: {'b': 730596189, 'e': -886713842} -> {'out0': 1}
        cur = 106;
        fork
            b_src.send(32'h2b8c035d);
            e_src.send(32'hcb25d20e);
            start_src.send;
            wait (out0_snk.n == 107);
            wait (p_end_snk.n == 107);
        join
        $display("OUT 106 %0d", $signed(out0_snk.seen[106]));
        if (out0_snk.seen[106] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 106 ({'b': 730596189, 'e': -886713842}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[106]), out0_snk.seen[106], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 107: {'b': -2056007405, 'e': -210706587} -> {'out0': 1}
        cur = 107;
        fork
            b_src.send(32'h8573d113);
            e_src.send(32'hf370df65);
            start_src.send;
            wait (out0_snk.n == 108);
            wait (p_end_snk.n == 108);
        join
        $display("OUT 107 %0d", $signed(out0_snk.seen[107]));
        if (out0_snk.seen[107] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 107 ({'b': -2056007405, 'e': -210706587}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[107]), out0_snk.seen[107], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 108: {'b': 1209365438, 'e': 1849479833} -> {'out0': 0}
        cur = 108;
        fork
            b_src.send(32'h481573be);
            e_src.send(32'h6e3cd299);
            start_src.send;
            wait (out0_snk.n == 109);
            wait (p_end_snk.n == 109);
        join
        $display("OUT 108 %0d", $signed(out0_snk.seen[108]));
        if (out0_snk.seen[108] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 108 ({'b': 1209365438, 'e': 1849479833}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[108]), out0_snk.seen[108], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 109: {'b': 1523617709, 'e': -427385234} -> {'out0': 1}
        cur = 109;
        fork
            b_src.send(32'h5ad08fad);
            e_src.send(32'he6869e6e);
            start_src.send;
            wait (out0_snk.n == 110);
            wait (p_end_snk.n == 110);
        join
        $display("OUT 109 %0d", $signed(out0_snk.seen[109]));
        if (out0_snk.seen[109] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 109 ({'b': 1523617709, 'e': -427385234}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[109]), out0_snk.seen[109], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 110: {'b': 796158711, 'e': -174647742} -> {'out0': 1}
        cur = 110;
        fork
            b_src.send(32'h2f746af7);
            e_src.send(32'hf5971642);
            start_src.send;
            wait (out0_snk.n == 111);
            wait (p_end_snk.n == 111);
        join
        $display("OUT 110 %0d", $signed(out0_snk.seen[110]));
        if (out0_snk.seen[110] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 110 ({'b': 796158711, 'e': -174647742}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[110]), out0_snk.seen[110], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 111: {'b': 1349057362, 'e': -1876887792} -> {'out0': 1}
        cur = 111;
        fork
            b_src.send(32'h5068fb52);
            e_src.send(32'h9020f710);
            start_src.send;
            wait (out0_snk.n == 112);
            wait (p_end_snk.n == 112);
        join
        $display("OUT 111 %0d", $signed(out0_snk.seen[111]));
        if (out0_snk.seen[111] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 111 ({'b': 1349057362, 'e': -1876887792}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[111]), out0_snk.seen[111], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 112: {'b': 1167955651, 'e': 454604960} -> {'out0': -3571583}
        cur = 112;
        fork
            b_src.send(32'h459d96c3);
            e_src.send(32'h1b18b8a0);
            start_src.send;
            wait (out0_snk.n == 113);
            wait (p_end_snk.n == 113);
        join
        $display("OUT 112 %0d", $signed(out0_snk.seen[112]));
        if (out0_snk.seen[112] !== 32'hffc98081) begin
            errors = errors + 1;
            $display("  FAIL vector 112 ({'b': 1167955651, 'e': 454604960}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[112]), out0_snk.seen[112], $signed(32'hffc98081), 32'hffc98081);
        end
        #(4 * T);

        // -- vector 113: {'b': 1260370025, 'e': -243358820} -> {'out0': 1}
        cur = 113;
        fork
            b_src.send(32'h4b1fb869);
            e_src.send(32'hf17ea39c);
            start_src.send;
            wait (out0_snk.n == 114);
            wait (p_end_snk.n == 114);
        join
        $display("OUT 113 %0d", $signed(out0_snk.seen[113]));
        if (out0_snk.seen[113] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 113 ({'b': 1260370025, 'e': -243358820}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[113]), out0_snk.seen[113], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 114: {'b': -580002372, 'e': 1444288124} -> {'out0': 0}
        cur = 114;
        fork
            b_src.send(32'hdd6dddbc);
            e_src.send(32'h5616167c);
            start_src.send;
            wait (out0_snk.n == 115);
            wait (p_end_snk.n == 115);
        join
        $display("OUT 114 %0d", $signed(out0_snk.seen[114]));
        if (out0_snk.seen[114] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 114 ({'b': -580002372, 'e': 1444288124}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[114]), out0_snk.seen[114], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 115: {'b': 2120101265, 'e': 1573254548} -> {'out0': 538936641}
        cur = 115;
        fork
            b_src.send(32'h7e5e2d91);
            e_src.send(32'h5dc5f594);
            start_src.send;
            wait (out0_snk.n == 116);
            wait (p_end_snk.n == 116);
        join
        $display("OUT 115 %0d", $signed(out0_snk.seen[115]));
        if (out0_snk.seen[115] !== 32'h201f8541) begin
            errors = errors + 1;
            $display("  FAIL vector 115 ({'b': 2120101265, 'e': 1573254548}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[115]), out0_snk.seen[115], $signed(32'h201f8541), 32'h201f8541);
        end
        #(4 * T);

        // -- vector 116: {'b': -24703952, 'e': -1577447394} -> {'out0': 1}
        cur = 116;
        fork
            b_src.send(32'hfe870c30);
            e_src.send(32'ha1fa101e);
            start_src.send;
            wait (out0_snk.n == 117);
            wait (p_end_snk.n == 117);
        join
        $display("OUT 116 %0d", $signed(out0_snk.seen[116]));
        if (out0_snk.seen[116] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 116 ({'b': -24703952, 'e': -1577447394}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[116]), out0_snk.seen[116], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 117: {'b': 1912041864, 'e': 1367980926} -> {'out0': 0}
        cur = 117;
        fork
            b_src.send(32'h71f77188);
            e_src.send(32'h5189bb7e);
            start_src.send;
            wait (out0_snk.n == 118);
            wait (p_end_snk.n == 118);
        join
        $display("OUT 117 %0d", $signed(out0_snk.seen[117]));
        if (out0_snk.seen[117] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 117 ({'b': 1912041864, 'e': 1367980926}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[117]), out0_snk.seen[117], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 118: {'b': -322918346, 'e': -1294081640} -> {'out0': 1}
        cur = 118;
        fork
            b_src.send(32'hecc0a836);
            e_src.send(32'hb2dde198);
            start_src.send;
            wait (out0_snk.n == 119);
            wait (p_end_snk.n == 119);
        join
        $display("OUT 118 %0d", $signed(out0_snk.seen[118]));
        if (out0_snk.seen[118] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 118 ({'b': -322918346, 'e': -1294081640}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[118]), out0_snk.seen[118], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 119: {'b': -788820812, 'e': 1038761289} -> {'out0': 0}
        cur = 119;
        fork
            b_src.send(32'hd0fb8cb4);
            e_src.send(32'h3dea3d49);
            start_src.send;
            wait (out0_snk.n == 120);
            wait (p_end_snk.n == 120);
        join
        $display("OUT 119 %0d", $signed(out0_snk.seen[119]));
        if (out0_snk.seen[119] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 119 ({'b': -788820812, 'e': 1038761289}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[119]), out0_snk.seen[119], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 120: {'b': 1572824819, 'e': 1023563364} -> {'out0': -1868792559}
        cur = 120;
        fork
            b_src.send(32'h5dbf66f3);
            e_src.send(32'h3d025664);
            start_src.send;
            wait (out0_snk.n == 121);
            wait (p_end_snk.n == 121);
        join
        $display("OUT 120 %0d", $signed(out0_snk.seen[120]));
        if (out0_snk.seen[120] !== 32'h909c7d11) begin
            errors = errors + 1;
            $display("  FAIL vector 120 ({'b': 1572824819, 'e': 1023563364}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[120]), out0_snk.seen[120], $signed(32'h909c7d11), 32'h909c7d11);
        end
        #(4 * T);

        // -- vector 121: {'b': 1957504098, 'e': 595671614} -> {'out0': 0}
        cur = 121;
        fork
            b_src.send(32'h74ad2462);
            e_src.send(32'h23813a3e);
            start_src.send;
            wait (out0_snk.n == 122);
            wait (p_end_snk.n == 122);
        join
        $display("OUT 121 %0d", $signed(out0_snk.seen[121]));
        if (out0_snk.seen[121] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 121 ({'b': 1957504098, 'e': 595671614}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[121]), out0_snk.seen[121], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 122: {'b': 462162276, 'e': 477993867} -> {'out0': 0}
        cur = 122;
        fork
            b_src.send(32'h1b8c0964);
            e_src.send(32'h1c7d9b8b);
            start_src.send;
            wait (out0_snk.n == 123);
            wait (p_end_snk.n == 123);
        join
        $display("OUT 122 %0d", $signed(out0_snk.seen[122]));
        if (out0_snk.seen[122] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 122 ({'b': 462162276, 'e': 477993867}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[122]), out0_snk.seen[122], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 123: {'b': -1305203664, 'e': -1832285403} -> {'out0': 1}
        cur = 123;
        fork
            b_src.send(32'hb2342c30);
            e_src.send(32'h92c98b25);
            start_src.send;
            wait (out0_snk.n == 124);
            wait (p_end_snk.n == 124);
        join
        $display("OUT 123 %0d", $signed(out0_snk.seen[123]));
        if (out0_snk.seen[123] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 123 ({'b': -1305203664, 'e': -1832285403}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[123]), out0_snk.seen[123], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 124: {'b': 1029357962, 'e': -644014854} -> {'out0': 1}
        cur = 124;
        fork
            b_src.send(32'h3d5ac18a);
            e_src.send(32'hd99d1cfa);
            start_src.send;
            wait (out0_snk.n == 125);
            wait (p_end_snk.n == 125);
        join
        $display("OUT 124 %0d", $signed(out0_snk.seen[124]));
        if (out0_snk.seen[124] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 124 ({'b': 1029357962, 'e': -644014854}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[124]), out0_snk.seen[124], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 125: {'b': 112956338, 'e': -1576920897} -> {'out0': 1}
        cur = 125;
        fork
            b_src.send(32'h06bb93b2);
            e_src.send(32'ha20218bf);
            start_src.send;
            wait (out0_snk.n == 126);
            wait (p_end_snk.n == 126);
        join
        $display("OUT 125 %0d", $signed(out0_snk.seen[125]));
        if (out0_snk.seen[125] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 125 ({'b': 112956338, 'e': -1576920897}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[125]), out0_snk.seen[125], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 126: {'b': -239649591, 'e': 233080908} -> {'out0': -327076895}
        cur = 126;
        fork
            b_src.send(32'hf1b73cc9);
            e_src.send(32'h0de4884c);
            start_src.send;
            wait (out0_snk.n == 127);
            wait (p_end_snk.n == 127);
        join
        $display("OUT 126 %0d", $signed(out0_snk.seen[126]));
        if (out0_snk.seen[126] !== 32'hec8133e1) begin
            errors = errors + 1;
            $display("  FAIL vector 126 ({'b': -239649591, 'e': 233080908}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[126]), out0_snk.seen[126], $signed(32'hec8133e1), 32'hec8133e1);
        end
        #(4 * T);

        // -- vector 127: {'b': 1787606853, 'e': 71062303} -> {'out0': -380684019}
        cur = 127;
        fork
            b_src.send(32'h6a8cb745);
            e_src.send(32'h043c531f);
            start_src.send;
            wait (out0_snk.n == 128);
            wait (p_end_snk.n == 128);
        join
        $display("OUT 127 %0d", $signed(out0_snk.seen[127]));
        if (out0_snk.seen[127] !== 32'he94f390d) begin
            errors = errors + 1;
            $display("  FAIL vector 127 ({'b': 1787606853, 'e': 71062303}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[127]), out0_snk.seen[127], $signed(32'he94f390d), 32'he94f390d);
        end
        #(4 * T);

        // -- vector 128: {'b': 7417103, 'e': 269704136} -> {'out0': -1352902783}
        cur = 128;
        fork
            b_src.send(32'h00712d0f);
            e_src.send(32'h10135bc8);
            start_src.send;
            wait (out0_snk.n == 129);
            wait (p_end_snk.n == 129);
        join
        $display("OUT 128 %0d", $signed(out0_snk.seen[128]));
        if (out0_snk.seen[128] !== 32'haf5c5781) begin
            errors = errors + 1;
            $display("  FAIL vector 128 ({'b': 7417103, 'e': 269704136}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[128]), out0_snk.seen[128], $signed(32'haf5c5781), 32'haf5c5781);
        end
        #(4 * T);

        // -- vector 129: {'b': -1096241019, 'e': 716628594} -> {'out0': -1469093543}
        cur = 129;
        fork
            b_src.send(32'hbea8b085);
            e_src.send(32'h2ab6e272);
            start_src.send;
            wait (out0_snk.n == 130);
            wait (p_end_snk.n == 130);
        join
        $display("OUT 129 %0d", $signed(out0_snk.seen[129]));
        if (out0_snk.seen[129] !== 32'ha86f6959) begin
            errors = errors + 1;
            $display("  FAIL vector 129 ({'b': -1096241019, 'e': 716628594}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[129]), out0_snk.seen[129], $signed(32'ha86f6959), 32'ha86f6959);
        end
        #(4 * T);

        // -- vector 130: {'b': -1550220208, 'e': 603028714} -> {'out0': 0}
        cur = 130;
        fork
            b_src.send(32'ha3998450);
            e_src.send(32'h23f17cea);
            start_src.send;
            wait (out0_snk.n == 131);
            wait (p_end_snk.n == 131);
        join
        $display("OUT 130 %0d", $signed(out0_snk.seen[130]));
        if (out0_snk.seen[130] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 130 ({'b': -1550220208, 'e': 603028714}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[130]), out0_snk.seen[130], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 131: {'b': 1813061133, 'e': -968676078} -> {'out0': 1}
        cur = 131;
        fork
            b_src.send(32'h6c111e0d);
            e_src.send(32'hc6432d12);
            start_src.send;
            wait (out0_snk.n == 132);
            wait (p_end_snk.n == 132);
        join
        $display("OUT 131 %0d", $signed(out0_snk.seen[131]));
        if (out0_snk.seen[131] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 131 ({'b': 1813061133, 'e': -968676078}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[131]), out0_snk.seen[131], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 132: {'b': -911621798, 'e': -872118375} -> {'out0': 1}
        cur = 132;
        fork
            b_src.send(32'hc9a9c15a);
            e_src.send(32'hcc048799);
            start_src.send;
            wait (out0_snk.n == 133);
            wait (p_end_snk.n == 133);
        join
        $display("OUT 132 %0d", $signed(out0_snk.seen[132]));
        if (out0_snk.seen[132] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 132 ({'b': -911621798, 'e': -872118375}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[132]), out0_snk.seen[132], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 133: {'b': -982822892, 'e': 2032536549} -> {'out0': 0}
        cur = 133;
        fork
            b_src.send(32'hc56b5014);
            e_src.send(32'h79260be5);
            start_src.send;
            wait (out0_snk.n == 134);
            wait (p_end_snk.n == 134);
        join
        $display("OUT 133 %0d", $signed(out0_snk.seen[133]));
        if (out0_snk.seen[133] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 133 ({'b': -982822892, 'e': 2032536549}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[133]), out0_snk.seen[133], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 134: {'b': -1699951590, 'e': -1767282707} -> {'out0': 1}
        cur = 134;
        fork
            b_src.send(32'h9aaccc1a);
            e_src.send(32'h96a967ed);
            start_src.send;
            wait (out0_snk.n == 135);
            wait (p_end_snk.n == 135);
        join
        $display("OUT 134 %0d", $signed(out0_snk.seen[134]));
        if (out0_snk.seen[134] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 134 ({'b': -1699951590, 'e': -1767282707}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[134]), out0_snk.seen[134], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 135: {'b': -51282432, 'e': -363798273} -> {'out0': 1}
        cur = 135;
        fork
            b_src.send(32'hfcf17e00);
            e_src.send(32'hea50e0ff);
            start_src.send;
            wait (out0_snk.n == 136);
            wait (p_end_snk.n == 136);
        join
        $display("OUT 135 %0d", $signed(out0_snk.seen[135]));
        if (out0_snk.seen[135] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 135 ({'b': -51282432, 'e': -363798273}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[135]), out0_snk.seen[135], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 136: {'b': -1140973224, 'e': -630757799} -> {'out0': 1}
        cur = 136;
        fork
            b_src.send(32'hbbfe2158);
            e_src.send(32'hda676659);
            start_src.send;
            wait (out0_snk.n == 137);
            wait (p_end_snk.n == 137);
        join
        $display("OUT 136 %0d", $signed(out0_snk.seen[136]));
        if (out0_snk.seen[136] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 136 ({'b': -1140973224, 'e': -630757799}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[136]), out0_snk.seen[136], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 137: {'b': -1069484920, 'e': -546994541} -> {'out0': 1}
        cur = 137;
        fork
            b_src.send(32'hc040f488);
            e_src.send(32'hdf658693);
            start_src.send;
            wait (out0_snk.n == 138);
            wait (p_end_snk.n == 138);
        join
        $display("OUT 137 %0d", $signed(out0_snk.seen[137]));
        if (out0_snk.seen[137] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 137 ({'b': -1069484920, 'e': -546994541}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[137]), out0_snk.seen[137], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 138: {'b': 1181635196, 'e': -1601729563} -> {'out0': 1}
        cur = 138;
        fork
            b_src.send(32'h466e527c);
            e_src.send(32'ha0878be5);
            start_src.send;
            wait (out0_snk.n == 139);
            wait (p_end_snk.n == 139);
        join
        $display("OUT 138 %0d", $signed(out0_snk.seen[138]));
        if (out0_snk.seen[138] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 138 ({'b': 1181635196, 'e': -1601729563}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[138]), out0_snk.seen[138], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 139: {'b': 1463904103, 'e': 1189911179} -> {'out0': 1444672439}
        cur = 139;
        fork
            b_src.send(32'h57416767);
            e_src.send(32'h46ec9a8b);
            start_src.send;
            wait (out0_snk.n == 140);
            wait (p_end_snk.n == 140);
        join
        $display("OUT 139 %0d", $signed(out0_snk.seen[139]));
        if (out0_snk.seen[139] !== 32'h561bf3b7) begin
            errors = errors + 1;
            $display("  FAIL vector 139 ({'b': 1463904103, 'e': 1189911179}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[139]), out0_snk.seen[139], $signed(32'h561bf3b7), 32'h561bf3b7);
        end
        #(4 * T);

        // -- vector 140: {'b': -1338288933, 'e': 7146404} -> {'out0': -1137589647}
        cur = 140;
        fork
            b_src.send(32'hb03b54db);
            e_src.send(32'h006d0ba4);
            start_src.send;
            wait (out0_snk.n == 141);
            wait (p_end_snk.n == 141);
        join
        $display("OUT 140 %0d", $signed(out0_snk.seen[140]));
        if (out0_snk.seen[140] !== 32'hbc31c271) begin
            errors = errors + 1;
            $display("  FAIL vector 140 ({'b': -1338288933, 'e': 7146404}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[140]), out0_snk.seen[140], $signed(32'hbc31c271), 32'hbc31c271);
        end
        #(4 * T);

        // -- vector 141: {'b': -291411844, 'e': -482624519} -> {'out0': 1}
        cur = 141;
        fork
            b_src.send(32'heea1687c);
            e_src.send(32'he33bbbf9);
            start_src.send;
            wait (out0_snk.n == 142);
            wait (p_end_snk.n == 142);
        join
        $display("OUT 141 %0d", $signed(out0_snk.seen[141]));
        if (out0_snk.seen[141] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 141 ({'b': -291411844, 'e': -482624519}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[141]), out0_snk.seen[141], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 142: {'b': 171122827, 'e': -1216991945} -> {'out0': 1}
        cur = 142;
        fork
            b_src.send(32'h0a33208b);
            e_src.send(32'hb7762d37);
            start_src.send;
            wait (out0_snk.n == 143);
            wait (p_end_snk.n == 143);
        join
        $display("OUT 142 %0d", $signed(out0_snk.seen[142]));
        if (out0_snk.seen[142] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 142 ({'b': 171122827, 'e': -1216991945}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[142]), out0_snk.seen[142], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 143: {'b': -1404283338, 'e': -1400158872} -> {'out0': 1}
        cur = 143;
        fork
            b_src.send(32'hac4c5636);
            e_src.send(32'hac8b4568);
            start_src.send;
            wait (out0_snk.n == 144);
            wait (p_end_snk.n == 144);
        join
        $display("OUT 143 %0d", $signed(out0_snk.seen[143]));
        if (out0_snk.seen[143] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 143 ({'b': -1404283338, 'e': -1400158872}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[143]), out0_snk.seen[143], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 144: {'b': 824039711, 'e': -770027786} -> {'out0': 1}
        cur = 144;
        fork
            b_src.send(32'h311dd91f);
            e_src.send(32'hd21a4ef6);
            start_src.send;
            wait (out0_snk.n == 145);
            wait (p_end_snk.n == 145);
        join
        $display("OUT 144 %0d", $signed(out0_snk.seen[144]));
        if (out0_snk.seen[144] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 144 ({'b': 824039711, 'e': -770027786}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[144]), out0_snk.seen[144], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 145: {'b': -199747289, 'e': -1133930543} -> {'out0': 1}
        cur = 145;
        fork
            b_src.send(32'hf4181927);
            e_src.send(32'hbc6997d1);
            start_src.send;
            wait (out0_snk.n == 146);
            wait (p_end_snk.n == 146);
        join
        $display("OUT 145 %0d", $signed(out0_snk.seen[145]));
        if (out0_snk.seen[145] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 145 ({'b': -199747289, 'e': -1133930543}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[145]), out0_snk.seen[145], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 146: {'b': 1145776670, 'e': -471201435} -> {'out0': 1}
        cur = 146;
        fork
            b_src.send(32'h444b2a1e);
            e_src.send(32'he3ea0965);
            start_src.send;
            wait (out0_snk.n == 147);
            wait (p_end_snk.n == 147);
        join
        $display("OUT 146 %0d", $signed(out0_snk.seen[146]));
        if (out0_snk.seen[146] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 146 ({'b': 1145776670, 'e': -471201435}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[146]), out0_snk.seen[146], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 147: {'b': 12524427, 'e': -885602335} -> {'out0': 1}
        cur = 147;
        fork
            b_src.send(32'h00bf1b8b);
            e_src.send(32'hcb36c7e1);
            start_src.send;
            wait (out0_snk.n == 148);
            wait (p_end_snk.n == 148);
        join
        $display("OUT 147 %0d", $signed(out0_snk.seen[147]));
        if (out0_snk.seen[147] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 147 ({'b': 12524427, 'e': -885602335}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[147]), out0_snk.seen[147], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 148: {'b': -415300803, 'e': 765615236} -> {'out0': -589730991}
        cur = 148;
        fork
            b_src.send(32'he73f033d);
            e_src.send(32'h2da25c84);
            start_src.send;
            wait (out0_snk.n == 149);
            wait (p_end_snk.n == 149);
        join
        $display("OUT 148 %0d", $signed(out0_snk.seen[148]));
        if (out0_snk.seen[148] !== 32'hdcd96b51) begin
            errors = errors + 1;
            $display("  FAIL vector 148 ({'b': -415300803, 'e': 765615236}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[148]), out0_snk.seen[148], $signed(32'hdcd96b51), 32'hdcd96b51);
        end
        #(4 * T);

        // -- vector 149: {'b': -1187427714, 'e': 1080722671} -> {'out0': 0}
        cur = 149;
        fork
            b_src.send(32'hb9394a7e);
            e_src.send(32'h406a84ef);
            start_src.send;
            wait (out0_snk.n == 150);
            wait (p_end_snk.n == 150);
        join
        $display("OUT 149 %0d", $signed(out0_snk.seen[149]));
        if (out0_snk.seen[149] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 149 ({'b': -1187427714, 'e': 1080722671}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[149]), out0_snk.seen[149], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 150: {'b': -670657820, 'e': -1369460932} -> {'out0': 1}
        cur = 150;
        fork
            b_src.send(32'hd80692e4);
            e_src.send(32'hae5faf3c);
            start_src.send;
            wait (out0_snk.n == 151);
            wait (p_end_snk.n == 151);
        join
        $display("OUT 150 %0d", $signed(out0_snk.seen[150]));
        if (out0_snk.seen[150] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 150 ({'b': -670657820, 'e': -1369460932}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[150]), out0_snk.seen[150], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 151: {'b': -502476185, 'e': -712081184} -> {'out0': 1}
        cur = 151;
        fork
            b_src.send(32'he20cd267);
            e_src.send(32'hd58e80e0);
            start_src.send;
            wait (out0_snk.n == 152);
            wait (p_end_snk.n == 152);
        join
        $display("OUT 151 %0d", $signed(out0_snk.seen[151]));
        if (out0_snk.seen[151] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 151 ({'b': -502476185, 'e': -712081184}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[151]), out0_snk.seen[151], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 152: {'b': -1161229753, 'e': -1100316011} -> {'out0': 1}
        cur = 152;
        fork
            b_src.send(32'hbac90a47);
            e_src.send(32'hbe6a8295);
            start_src.send;
            wait (out0_snk.n == 153);
            wait (p_end_snk.n == 153);
        join
        $display("OUT 152 %0d", $signed(out0_snk.seen[152]));
        if (out0_snk.seen[152] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 152 ({'b': -1161229753, 'e': -1100316011}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[152]), out0_snk.seen[152], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 153: {'b': -2117421440, 'e': -1361222429} -> {'out0': 1}
        cur = 153;
        fork
            b_src.send(32'h81cab680);
            e_src.send(32'haedd64e3);
            start_src.send;
            wait (out0_snk.n == 154);
            wait (p_end_snk.n == 154);
        join
        $display("OUT 153 %0d", $signed(out0_snk.seen[153]));
        if (out0_snk.seen[153] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 153 ({'b': -2117421440, 'e': -1361222429}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[153]), out0_snk.seen[153], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 154: {'b': 1290158962, 'e': -84358778} -> {'out0': 1}
        cur = 154;
        fork
            b_src.send(32'h4ce64372);
            e_src.send(32'hfaf8c986);
            start_src.send;
            wait (out0_snk.n == 155);
            wait (p_end_snk.n == 155);
        join
        $display("OUT 154 %0d", $signed(out0_snk.seen[154]));
        if (out0_snk.seen[154] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 154 ({'b': 1290158962, 'e': -84358778}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[154]), out0_snk.seen[154], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 155: {'b': -1510021377, 'e': -1298604792} -> {'out0': 1}
        cur = 155;
        fork
            b_src.send(32'ha5fee6ff);
            e_src.send(32'hb298dd08);
            start_src.send;
            wait (out0_snk.n == 156);
            wait (p_end_snk.n == 156);
        join
        $display("OUT 155 %0d", $signed(out0_snk.seen[155]));
        if (out0_snk.seen[155] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 155 ({'b': -1510021377, 'e': -1298604792}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[155]), out0_snk.seen[155], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 156: {'b': -510767204, 'e': -1212687487} -> {'out0': 1}
        cur = 156;
        fork
            b_src.send(32'he18e4f9c);
            e_src.send(32'hb7b7db81);
            start_src.send;
            wait (out0_snk.n == 157);
            wait (p_end_snk.n == 157);
        join
        $display("OUT 156 %0d", $signed(out0_snk.seen[156]));
        if (out0_snk.seen[156] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 156 ({'b': -510767204, 'e': -1212687487}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[156]), out0_snk.seen[156], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 157: {'b': -1393831883, 'e': 995153416} -> {'out0': 1150606689}
        cur = 157;
        fork
            b_src.send(32'hacebd035);
            e_src.send(32'h3b50d608);
            start_src.send;
            wait (out0_snk.n == 158);
            wait (p_end_snk.n == 158);
        join
        $display("OUT 157 %0d", $signed(out0_snk.seen[157]));
        if (out0_snk.seen[157] !== 32'h4494dd61) begin
            errors = errors + 1;
            $display("  FAIL vector 157 ({'b': -1393831883, 'e': 995153416}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[157]), out0_snk.seen[157], $signed(32'h4494dd61), 32'h4494dd61);
        end
        #(4 * T);

        // -- vector 158: {'b': -489921616, 'e': 1969192013} -> {'out0': 0}
        cur = 158;
        fork
            b_src.send(32'he2cc63b0);
            e_src.send(32'h755f7c4d);
            start_src.send;
            wait (out0_snk.n == 159);
            wait (p_end_snk.n == 159);
        join
        $display("OUT 158 %0d", $signed(out0_snk.seen[158]));
        if (out0_snk.seen[158] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 158 ({'b': -489921616, 'e': 1969192013}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[158]), out0_snk.seen[158], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 159: {'b': -682015593, 'e': -656460610} -> {'out0': 1}
        cur = 159;
        fork
            b_src.send(32'hd7594497);
            e_src.send(32'hd8df34be);
            start_src.send;
            wait (out0_snk.n == 160);
            wait (p_end_snk.n == 160);
        join
        $display("OUT 159 %0d", $signed(out0_snk.seen[159]));
        if (out0_snk.seen[159] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 159 ({'b': -682015593, 'e': -656460610}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[159]), out0_snk.seen[159], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // Teeth: a channel that never produced a token would pass every
        // comparison above by having nothing to compare.  Assert the
        // count explicitly, on every output channel.
        if (out0_snk.n != 160) begin
            errors = errors + 1;
            $display("  FAIL out0 produced %0d token(s), expected 160", out0_snk.n);
        end
        if (p_end_snk.n != 160) begin
            errors = errors + 1;
            $display("  FAIL p_end produced %0d token(s), expected 160", p_end_snk.n);
        end

        if (errors == 0) $display("tb_ipow PASS");
        else             $display("tb_ipow FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #20000000000;
        $display("tb_ipow FAIL (timeout) on vector %0d", cur);
        $display("    src b: %0d sent, req=%b ack=%b", b_src.nsent, b_req, b_ack);
        $display("    src e: %0d sent, req=%b ack=%b", e_src.nsent, e_req, e_ack);
        $display("    src start: %0d sent, req=%b ack=%b", start_src.nsent, start_req, start_ack);
        $display("    snk out0: %0d seen, req=%b ack=%b", out0_snk.n, out0_req, out0_ack);
        $display("    snk p_end: %0d seen, req=%b ack=%b", p_end_snk.n, p_end_req, p_end_ack);
        $finish;
    end

`ifdef SIMCHECK_VCD
    initial begin
        $dumpfile("tb_ipow.vcd");
        $dumpvars(0, tb_ipow);
    end
`endif
endmodule