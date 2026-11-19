
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

module tb_isprime;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer cur = -1;
    reg rst = 1'b1;

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

    bdc_isprime uut (
        .rst(rst),
        .n_req(n_req), .n_ack(n_ack), .n_data(n_data),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    initial begin
        $display("tb_isprime");
        #(596 * T);
        rst = 1'b0;
        #(8 * T);

        // -- vector 0: {'n': 0} -> {'out0': 0}
        cur = 0;
        fork
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 1);
            wait (p_end_snk.n == 1);
        join
        $display("OUT 0 %0d", $signed(out0_snk.seen[0]));
        if (out0_snk.seen[0] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 0 ({'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[0]), out0_snk.seen[0], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 1: {'n': 1} -> {'out0': 0}
        cur = 1;
        fork
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 2);
            wait (p_end_snk.n == 2);
        join
        $display("OUT 1 %0d", $signed(out0_snk.seen[1]));
        if (out0_snk.seen[1] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 1 ({'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[1]), out0_snk.seen[1], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 2: {'n': 2} -> {'out0': 1}
        cur = 2;
        fork
            n_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 3);
            wait (p_end_snk.n == 3);
        join
        $display("OUT 2 %0d", $signed(out0_snk.seen[2]));
        if (out0_snk.seen[2] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 2 ({'n': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[2]), out0_snk.seen[2], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 3: {'n': 3} -> {'out0': 1}
        cur = 3;
        fork
            n_src.send(32'h00000003);
            start_src.send;
            wait (out0_snk.n == 4);
            wait (p_end_snk.n == 4);
        join
        $display("OUT 3 %0d", $signed(out0_snk.seen[3]));
        if (out0_snk.seen[3] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 3 ({'n': 3}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[3]), out0_snk.seen[3], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 4: {'n': 4} -> {'out0': 0}
        cur = 4;
        fork
            n_src.send(32'h00000004);
            start_src.send;
            wait (out0_snk.n == 5);
            wait (p_end_snk.n == 5);
        join
        $display("OUT 4 %0d", $signed(out0_snk.seen[4]));
        if (out0_snk.seen[4] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 4 ({'n': 4}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[4]), out0_snk.seen[4], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 5: {'n': -1} -> {'out0': 0}
        cur = 5;
        fork
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 6);
            wait (p_end_snk.n == 6);
        join
        $display("OUT 5 %0d", $signed(out0_snk.seen[5]));
        if (out0_snk.seen[5] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 5 ({'n': -1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[5]), out0_snk.seen[5], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 6: {'n': -2147483648} -> {'out0': 0}
        cur = 6;
        fork
            n_src.send(32'h80000000);
            start_src.send;
            wait (out0_snk.n == 7);
            wait (p_end_snk.n == 7);
        join
        $display("OUT 6 %0d", $signed(out0_snk.seen[6]));
        if (out0_snk.seen[6] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 6 ({'n': -2147483648}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[6]), out0_snk.seen[6], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 7: {'n': 97} -> {'out0': 1}
        cur = 7;
        fork
            n_src.send(32'h00000061);
            start_src.send;
            wait (out0_snk.n == 8);
            wait (p_end_snk.n == 8);
        join
        $display("OUT 7 %0d", $signed(out0_snk.seen[7]));
        if (out0_snk.seen[7] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 7 ({'n': 97}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[7]), out0_snk.seen[7], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 8: {'n': 91} -> {'out0': 0}
        cur = 8;
        fork
            n_src.send(32'h0000005b);
            start_src.send;
            wait (out0_snk.n == 9);
            wait (p_end_snk.n == 9);
        join
        $display("OUT 8 %0d", $signed(out0_snk.seen[8]));
        if (out0_snk.seen[8] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 8 ({'n': 91}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[8]), out0_snk.seen[8], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 9: {'n': 7919} -> {'out0': 1}
        cur = 9;
        fork
            n_src.send(32'h00001eef);
            start_src.send;
            wait (out0_snk.n == 10);
            wait (p_end_snk.n == 10);
        join
        $display("OUT 9 %0d", $signed(out0_snk.seen[9]));
        if (out0_snk.seen[9] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 9 ({'n': 7919}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[9]), out0_snk.seen[9], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 10: {'n': 65521} -> {'out0': 1}
        cur = 10;
        fork
            n_src.send(32'h0000fff1);
            start_src.send;
            wait (out0_snk.n == 11);
            wait (p_end_snk.n == 11);
        join
        $display("OUT 10 %0d", $signed(out0_snk.seen[10]));
        if (out0_snk.seen[10] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 10 ({'n': 65521}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[10]), out0_snk.seen[10], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 11: {'n': 65537} -> {'out0': 1}
        cur = 11;
        fork
            n_src.send(32'h00010001);
            start_src.send;
            wait (out0_snk.n == 12);
            wait (p_end_snk.n == 12);
        join
        $display("OUT 11 %0d", $signed(out0_snk.seen[11]));
        if (out0_snk.seen[11] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 11 ({'n': 65537}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[11]), out0_snk.seen[11], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 12: {'n': 12401} -> {'out0': 1}
        cur = 12;
        fork
            n_src.send(32'h00003071);
            start_src.send;
            wait (out0_snk.n == 13);
            wait (p_end_snk.n == 13);
        join
        $display("OUT 12 %0d", $signed(out0_snk.seen[12]));
        if (out0_snk.seen[12] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 12 ({'n': 12401}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[12]), out0_snk.seen[12], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 13: {'n': 15943} -> {'out0': 0}
        cur = 13;
        fork
            n_src.send(32'h00003e47);
            start_src.send;
            wait (out0_snk.n == 14);
            wait (p_end_snk.n == 14);
        join
        $display("OUT 13 %0d", $signed(out0_snk.seen[13]));
        if (out0_snk.seen[13] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 13 ({'n': 15943}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[13]), out0_snk.seen[13], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 14: {'n': 7732} -> {'out0': 0}
        cur = 14;
        fork
            n_src.send(32'h00001e34);
            start_src.send;
            wait (out0_snk.n == 15);
            wait (p_end_snk.n == 15);
        join
        $display("OUT 14 %0d", $signed(out0_snk.seen[14]));
        if (out0_snk.seen[14] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 14 ({'n': 7732}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[14]), out0_snk.seen[14], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 15: {'n': 19616} -> {'out0': 0}
        cur = 15;
        fork
            n_src.send(32'h00004ca0);
            start_src.send;
            wait (out0_snk.n == 16);
            wait (p_end_snk.n == 16);
        join
        $display("OUT 15 %0d", $signed(out0_snk.seen[15]));
        if (out0_snk.seen[15] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 15 ({'n': 19616}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[15]), out0_snk.seen[15], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 16: {'n': 18652} -> {'out0': 0}
        cur = 16;
        fork
            n_src.send(32'h000048dc);
            start_src.send;
            wait (out0_snk.n == 17);
            wait (p_end_snk.n == 17);
        join
        $display("OUT 16 %0d", $signed(out0_snk.seen[16]));
        if (out0_snk.seen[16] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 16 ({'n': 18652}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[16]), out0_snk.seen[16], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 17: {'n': 13377} -> {'out0': 0}
        cur = 17;
        fork
            n_src.send(32'h00003441);
            start_src.send;
            wait (out0_snk.n == 18);
            wait (p_end_snk.n == 18);
        join
        $display("OUT 17 %0d", $signed(out0_snk.seen[17]));
        if (out0_snk.seen[17] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 17 ({'n': 13377}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[17]), out0_snk.seen[17], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 18: {'n': 9610} -> {'out0': 0}
        cur = 18;
        fork
            n_src.send(32'h0000258a);
            start_src.send;
            wait (out0_snk.n == 19);
            wait (p_end_snk.n == 19);
        join
        $display("OUT 18 %0d", $signed(out0_snk.seen[18]));
        if (out0_snk.seen[18] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 18 ({'n': 9610}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[18]), out0_snk.seen[18], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 19: {'n': 12031} -> {'out0': 0}
        cur = 19;
        fork
            n_src.send(32'h00002eff);
            start_src.send;
            wait (out0_snk.n == 20);
            wait (p_end_snk.n == 20);
        join
        $display("OUT 19 %0d", $signed(out0_snk.seen[19]));
        if (out0_snk.seen[19] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 19 ({'n': 12031}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[19]), out0_snk.seen[19], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 20: {'n': 5033} -> {'out0': 0}
        cur = 20;
        fork
            n_src.send(32'h000013a9);
            start_src.send;
            wait (out0_snk.n == 21);
            wait (p_end_snk.n == 21);
        join
        $display("OUT 20 %0d", $signed(out0_snk.seen[20]));
        if (out0_snk.seen[20] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 20 ({'n': 5033}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[20]), out0_snk.seen[20], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 21: {'n': 10245} -> {'out0': 0}
        cur = 21;
        fork
            n_src.send(32'h00002805);
            start_src.send;
            wait (out0_snk.n == 22);
            wait (p_end_snk.n == 22);
        join
        $display("OUT 21 %0d", $signed(out0_snk.seen[21]));
        if (out0_snk.seen[21] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 21 ({'n': 10245}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[21]), out0_snk.seen[21], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 22: {'n': 12052} -> {'out0': 0}
        cur = 22;
        fork
            n_src.send(32'h00002f14);
            start_src.send;
            wait (out0_snk.n == 23);
            wait (p_end_snk.n == 23);
        join
        $display("OUT 22 %0d", $signed(out0_snk.seen[22]));
        if (out0_snk.seen[22] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 22 ({'n': 12052}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[22]), out0_snk.seen[22], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 23: {'n': 14193} -> {'out0': 0}
        cur = 23;
        fork
            n_src.send(32'h00003771);
            start_src.send;
            wait (out0_snk.n == 24);
            wait (p_end_snk.n == 24);
        join
        $display("OUT 23 %0d", $signed(out0_snk.seen[23]));
        if (out0_snk.seen[23] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 23 ({'n': 14193}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[23]), out0_snk.seen[23], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 24: {'n': 8076} -> {'out0': 0}
        cur = 24;
        fork
            n_src.send(32'h00001f8c);
            start_src.send;
            wait (out0_snk.n == 25);
            wait (p_end_snk.n == 25);
        join
        $display("OUT 24 %0d", $signed(out0_snk.seen[24]));
        if (out0_snk.seen[24] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 24 ({'n': 8076}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[24]), out0_snk.seen[24], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 25: {'n': 16440} -> {'out0': 0}
        cur = 25;
        fork
            n_src.send(32'h00004038);
            start_src.send;
            wait (out0_snk.n == 26);
            wait (p_end_snk.n == 26);
        join
        $display("OUT 25 %0d", $signed(out0_snk.seen[25]));
        if (out0_snk.seen[25] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 25 ({'n': 16440}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[25]), out0_snk.seen[25], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 26: {'n': 7023} -> {'out0': 0}
        cur = 26;
        fork
            n_src.send(32'h00001b6f);
            start_src.send;
            wait (out0_snk.n == 27);
            wait (p_end_snk.n == 27);
        join
        $display("OUT 26 %0d", $signed(out0_snk.seen[26]));
        if (out0_snk.seen[26] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 26 ({'n': 7023}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[26]), out0_snk.seen[26], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 27: {'n': 7466} -> {'out0': 0}
        cur = 27;
        fork
            n_src.send(32'h00001d2a);
            start_src.send;
            wait (out0_snk.n == 28);
            wait (p_end_snk.n == 28);
        join
        $display("OUT 27 %0d", $signed(out0_snk.seen[27]));
        if (out0_snk.seen[27] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 27 ({'n': 7466}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[27]), out0_snk.seen[27], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 28: {'n': 8477} -> {'out0': 0}
        cur = 28;
        fork
            n_src.send(32'h0000211d);
            start_src.send;
            wait (out0_snk.n == 29);
            wait (p_end_snk.n == 29);
        join
        $display("OUT 28 %0d", $signed(out0_snk.seen[28]));
        if (out0_snk.seen[28] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 28 ({'n': 8477}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[28]), out0_snk.seen[28], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 29: {'n': 1255} -> {'out0': 0}
        cur = 29;
        fork
            n_src.send(32'h000004e7);
            start_src.send;
            wait (out0_snk.n == 30);
            wait (p_end_snk.n == 30);
        join
        $display("OUT 29 %0d", $signed(out0_snk.seen[29]));
        if (out0_snk.seen[29] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 29 ({'n': 1255}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[29]), out0_snk.seen[29], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 30: {'n': 8964} -> {'out0': 0}
        cur = 30;
        fork
            n_src.send(32'h00002304);
            start_src.send;
            wait (out0_snk.n == 31);
            wait (p_end_snk.n == 31);
        join
        $display("OUT 30 %0d", $signed(out0_snk.seen[30]));
        if (out0_snk.seen[30] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 30 ({'n': 8964}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[30]), out0_snk.seen[30], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 31: {'n': 4892} -> {'out0': 0}
        cur = 31;
        fork
            n_src.send(32'h0000131c);
            start_src.send;
            wait (out0_snk.n == 32);
            wait (p_end_snk.n == 32);
        join
        $display("OUT 31 %0d", $signed(out0_snk.seen[31]));
        if (out0_snk.seen[31] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 31 ({'n': 4892}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[31]), out0_snk.seen[31], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 32: {'n': 9619} -> {'out0': 1}
        cur = 32;
        fork
            n_src.send(32'h00002593);
            start_src.send;
            wait (out0_snk.n == 33);
            wait (p_end_snk.n == 33);
        join
        $display("OUT 32 %0d", $signed(out0_snk.seen[32]));
        if (out0_snk.seen[32] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 32 ({'n': 9619}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[32]), out0_snk.seen[32], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 33: {'n': 19188} -> {'out0': 0}
        cur = 33;
        fork
            n_src.send(32'h00004af4);
            start_src.send;
            wait (out0_snk.n == 34);
            wait (p_end_snk.n == 34);
        join
        $display("OUT 33 %0d", $signed(out0_snk.seen[33]));
        if (out0_snk.seen[33] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 33 ({'n': 19188}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[33]), out0_snk.seen[33], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 34: {'n': 2249} -> {'out0': 0}
        cur = 34;
        fork
            n_src.send(32'h000008c9);
            start_src.send;
            wait (out0_snk.n == 35);
            wait (p_end_snk.n == 35);
        join
        $display("OUT 34 %0d", $signed(out0_snk.seen[34]));
        if (out0_snk.seen[34] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 34 ({'n': 2249}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[34]), out0_snk.seen[34], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 35: {'n': 11557} -> {'out0': 0}
        cur = 35;
        fork
            n_src.send(32'h00002d25);
            start_src.send;
            wait (out0_snk.n == 36);
            wait (p_end_snk.n == 36);
        join
        $display("OUT 35 %0d", $signed(out0_snk.seen[35]));
        if (out0_snk.seen[35] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 35 ({'n': 11557}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[35]), out0_snk.seen[35], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 36: {'n': 13252} -> {'out0': 0}
        cur = 36;
        fork
            n_src.send(32'h000033c4);
            start_src.send;
            wait (out0_snk.n == 37);
            wait (p_end_snk.n == 37);
        join
        $display("OUT 36 %0d", $signed(out0_snk.seen[36]));
        if (out0_snk.seen[36] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 36 ({'n': 13252}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[36]), out0_snk.seen[36], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 37: {'n': 15661} -> {'out0': 1}
        cur = 37;
        fork
            n_src.send(32'h00003d2d);
            start_src.send;
            wait (out0_snk.n == 38);
            wait (p_end_snk.n == 38);
        join
        $display("OUT 37 %0d", $signed(out0_snk.seen[37]));
        if (out0_snk.seen[37] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 37 ({'n': 15661}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[37]), out0_snk.seen[37], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 38: {'n': 7876} -> {'out0': 0}
        cur = 38;
        fork
            n_src.send(32'h00001ec4);
            start_src.send;
            wait (out0_snk.n == 39);
            wait (p_end_snk.n == 39);
        join
        $display("OUT 38 %0d", $signed(out0_snk.seen[38]));
        if (out0_snk.seen[38] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 38 ({'n': 7876}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[38]), out0_snk.seen[38], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 39: {'n': 5790} -> {'out0': 0}
        cur = 39;
        fork
            n_src.send(32'h0000169e);
            start_src.send;
            wait (out0_snk.n == 40);
            wait (p_end_snk.n == 40);
        join
        $display("OUT 39 %0d", $signed(out0_snk.seen[39]));
        if (out0_snk.seen[39] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 39 ({'n': 5790}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[39]), out0_snk.seen[39], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 40: {'n': 16573} -> {'out0': 1}
        cur = 40;
        fork
            n_src.send(32'h000040bd);
            start_src.send;
            wait (out0_snk.n == 41);
            wait (p_end_snk.n == 41);
        join
        $display("OUT 40 %0d", $signed(out0_snk.seen[40]));
        if (out0_snk.seen[40] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 40 ({'n': 16573}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[40]), out0_snk.seen[40], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 41: {'n': 15313} -> {'out0': 1}
        cur = 41;
        fork
            n_src.send(32'h00003bd1);
            start_src.send;
            wait (out0_snk.n == 42);
            wait (p_end_snk.n == 42);
        join
        $display("OUT 41 %0d", $signed(out0_snk.seen[41]));
        if (out0_snk.seen[41] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 41 ({'n': 15313}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[41]), out0_snk.seen[41], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 42: {'n': 13570} -> {'out0': 0}
        cur = 42;
        fork
            n_src.send(32'h00003502);
            start_src.send;
            wait (out0_snk.n == 43);
            wait (p_end_snk.n == 43);
        join
        $display("OUT 42 %0d", $signed(out0_snk.seen[42]));
        if (out0_snk.seen[42] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 42 ({'n': 13570}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[42]), out0_snk.seen[42], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 43: {'n': 8864} -> {'out0': 0}
        cur = 43;
        fork
            n_src.send(32'h000022a0);
            start_src.send;
            wait (out0_snk.n == 44);
            wait (p_end_snk.n == 44);
        join
        $display("OUT 43 %0d", $signed(out0_snk.seen[43]));
        if (out0_snk.seen[43] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 43 ({'n': 8864}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[43]), out0_snk.seen[43], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 44: {'n': 11997} -> {'out0': 0}
        cur = 44;
        fork
            n_src.send(32'h00002edd);
            start_src.send;
            wait (out0_snk.n == 45);
            wait (p_end_snk.n == 45);
        join
        $display("OUT 44 %0d", $signed(out0_snk.seen[44]));
        if (out0_snk.seen[44] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 44 ({'n': 11997}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[44]), out0_snk.seen[44], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 45: {'n': 6510} -> {'out0': 0}
        cur = 45;
        fork
            n_src.send(32'h0000196e);
            start_src.send;
            wait (out0_snk.n == 46);
            wait (p_end_snk.n == 46);
        join
        $display("OUT 45 %0d", $signed(out0_snk.seen[45]));
        if (out0_snk.seen[45] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 45 ({'n': 6510}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[45]), out0_snk.seen[45], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 46: {'n': 18507} -> {'out0': 0}
        cur = 46;
        fork
            n_src.send(32'h0000484b);
            start_src.send;
            wait (out0_snk.n == 47);
            wait (p_end_snk.n == 47);
        join
        $display("OUT 46 %0d", $signed(out0_snk.seen[46]));
        if (out0_snk.seen[46] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 46 ({'n': 18507}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[46]), out0_snk.seen[46], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 47: {'n': 10711} -> {'out0': 1}
        cur = 47;
        fork
            n_src.send(32'h000029d7);
            start_src.send;
            wait (out0_snk.n == 48);
            wait (p_end_snk.n == 48);
        join
        $display("OUT 47 %0d", $signed(out0_snk.seen[47]));
        if (out0_snk.seen[47] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 47 ({'n': 10711}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[47]), out0_snk.seen[47], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 48: {'n': 8364} -> {'out0': 0}
        cur = 48;
        fork
            n_src.send(32'h000020ac);
            start_src.send;
            wait (out0_snk.n == 49);
            wait (p_end_snk.n == 49);
        join
        $display("OUT 48 %0d", $signed(out0_snk.seen[48]));
        if (out0_snk.seen[48] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 48 ({'n': 8364}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[48]), out0_snk.seen[48], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 49: {'n': 19170} -> {'out0': 0}
        cur = 49;
        fork
            n_src.send(32'h00004ae2);
            start_src.send;
            wait (out0_snk.n == 50);
            wait (p_end_snk.n == 50);
        join
        $display("OUT 49 %0d", $signed(out0_snk.seen[49]));
        if (out0_snk.seen[49] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 49 ({'n': 19170}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[49]), out0_snk.seen[49], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 50: {'n': 9476} -> {'out0': 0}
        cur = 50;
        fork
            n_src.send(32'h00002504);
            start_src.send;
            wait (out0_snk.n == 51);
            wait (p_end_snk.n == 51);
        join
        $display("OUT 50 %0d", $signed(out0_snk.seen[50]));
        if (out0_snk.seen[50] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 50 ({'n': 9476}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[50]), out0_snk.seen[50], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 51: {'n': 7272} -> {'out0': 0}
        cur = 51;
        fork
            n_src.send(32'h00001c68);
            start_src.send;
            wait (out0_snk.n == 52);
            wait (p_end_snk.n == 52);
        join
        $display("OUT 51 %0d", $signed(out0_snk.seen[51]));
        if (out0_snk.seen[51] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 51 ({'n': 7272}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[51]), out0_snk.seen[51], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // Teeth: a channel that never produced a token would pass every
        // comparison above by having nothing to compare.  Assert the
        // count explicitly, on every output channel.
        if (out0_snk.n != 52) begin
            errors = errors + 1;
            $display("  FAIL out0 produced %0d token(s), expected 52", out0_snk.n);
        end
        if (p_end_snk.n != 52) begin
            errors = errors + 1;
            $display("  FAIL p_end produced %0d token(s), expected 52", p_end_snk.n);
        end

        if (errors == 0) $display("tb_isprime PASS");
        else             $display("tb_isprime FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #20000000000;
        $display("tb_isprime FAIL (timeout) on vector %0d", cur);
        $display("    src n: %0d sent, req=%b ack=%b", n_src.nsent, n_req, n_ack);
        $display("    src start: %0d sent, req=%b ack=%b", start_src.nsent, start_req, start_ack);
        $display("    snk out0: %0d seen, req=%b ack=%b", out0_snk.n, out0_req, out0_ack);
        $display("    snk p_end: %0d seen, req=%b ack=%b", p_end_snk.n, p_end_req, p_end_ack);
        $finish;
    end

`ifdef SIMCHECK_VCD
    initial begin
        $dumpfile("tb_isprime.vcd");
        $dumpvars(0, tb_isprime);
    end
`endif
endmodule