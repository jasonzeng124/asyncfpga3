
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

module tb_collatz;

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

    bdc_collatz uut (
        .rst(rst),
        .n_req(n_req), .n_ack(n_ack), .n_data(n_data),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    initial begin
        $display("tb_collatz");
        #(180 * T);
        rst = 1'b0;
        #(8 * T);

        // -- vector 0: {'n': 1} -> {'out0': 0}
        cur = 0;
        fork
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 1);
            wait (p_end_snk.n == 1);
        join
        $display("OUT 0 %0d", $signed(out0_snk.seen[0]));
        if (out0_snk.seen[0] !== 32'h00000000) begin
            errors = errors + 1;
            $display("  FAIL vector 0 ({'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[0]), out0_snk.seen[0], $signed(32'h00000000), 32'h00000000);
        end
        #(4 * T);

        // -- vector 1: {'n': 2} -> {'out0': 1}
        cur = 1;
        fork
            n_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 2);
            wait (p_end_snk.n == 2);
        join
        $display("OUT 1 %0d", $signed(out0_snk.seen[1]));
        if (out0_snk.seen[1] !== 32'h00000001) begin
            errors = errors + 1;
            $display("  FAIL vector 1 ({'n': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[1]), out0_snk.seen[1], $signed(32'h00000001), 32'h00000001);
        end
        #(4 * T);

        // -- vector 2: {'n': 3} -> {'out0': 7}
        cur = 2;
        fork
            n_src.send(32'h00000003);
            start_src.send;
            wait (out0_snk.n == 3);
            wait (p_end_snk.n == 3);
        join
        $display("OUT 2 %0d", $signed(out0_snk.seen[2]));
        if (out0_snk.seen[2] !== 32'h00000007) begin
            errors = errors + 1;
            $display("  FAIL vector 2 ({'n': 3}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[2]), out0_snk.seen[2], $signed(32'h00000007), 32'h00000007);
        end
        #(4 * T);

        // -- vector 3: {'n': 6} -> {'out0': 8}
        cur = 3;
        fork
            n_src.send(32'h00000006);
            start_src.send;
            wait (out0_snk.n == 4);
            wait (p_end_snk.n == 4);
        join
        $display("OUT 3 %0d", $signed(out0_snk.seen[3]));
        if (out0_snk.seen[3] !== 32'h00000008) begin
            errors = errors + 1;
            $display("  FAIL vector 3 ({'n': 6}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[3]), out0_snk.seen[3], $signed(32'h00000008), 32'h00000008);
        end
        #(4 * T);

        // -- vector 4: {'n': 7} -> {'out0': 16}
        cur = 4;
        fork
            n_src.send(32'h00000007);
            start_src.send;
            wait (out0_snk.n == 5);
            wait (p_end_snk.n == 5);
        join
        $display("OUT 4 %0d", $signed(out0_snk.seen[4]));
        if (out0_snk.seen[4] !== 32'h00000010) begin
            errors = errors + 1;
            $display("  FAIL vector 4 ({'n': 7}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[4]), out0_snk.seen[4], $signed(32'h00000010), 32'h00000010);
        end
        #(4 * T);

        // -- vector 5: {'n': 27} -> {'out0': 111}
        cur = 5;
        fork
            n_src.send(32'h0000001b);
            start_src.send;
            wait (out0_snk.n == 6);
            wait (p_end_snk.n == 6);
        join
        $display("OUT 5 %0d", $signed(out0_snk.seen[5]));
        if (out0_snk.seen[5] !== 32'h0000006f) begin
            errors = errors + 1;
            $display("  FAIL vector 5 ({'n': 27}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[5]), out0_snk.seen[5], $signed(32'h0000006f), 32'h0000006f);
        end
        #(4 * T);

        // -- vector 6: {'n': 97} -> {'out0': 118}
        cur = 6;
        fork
            n_src.send(32'h00000061);
            start_src.send;
            wait (out0_snk.n == 7);
            wait (p_end_snk.n == 7);
        join
        $display("OUT 6 %0d", $signed(out0_snk.seen[6]));
        if (out0_snk.seen[6] !== 32'h00000076) begin
            errors = errors + 1;
            $display("  FAIL vector 6 ({'n': 97}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[6]), out0_snk.seen[6], $signed(32'h00000076), 32'h00000076);
        end
        #(4 * T);

        // -- vector 7: {'n': 871} -> {'out0': 178}
        cur = 7;
        fork
            n_src.send(32'h00000367);
            start_src.send;
            wait (out0_snk.n == 8);
            wait (p_end_snk.n == 8);
        join
        $display("OUT 7 %0d", $signed(out0_snk.seen[7]));
        if (out0_snk.seen[7] !== 32'h000000b2) begin
            errors = errors + 1;
            $display("  FAIL vector 7 ({'n': 871}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[7]), out0_snk.seen[7], $signed(32'h000000b2), 32'h000000b2);
        end
        #(4 * T);

        // -- vector 8: {'n': 1073741824} -> {'out0': 30}
        cur = 8;
        fork
            n_src.send(32'h40000000);
            start_src.send;
            wait (out0_snk.n == 9);
            wait (p_end_snk.n == 9);
        join
        $display("OUT 8 %0d", $signed(out0_snk.seen[8]));
        if (out0_snk.seen[8] !== 32'h0000001e) begin
            errors = errors + 1;
            $display("  FAIL vector 8 ({'n': 1073741824}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[8]), out0_snk.seen[8], $signed(32'h0000001e), 32'h0000001e);
        end
        #(4 * T);

        // -- vector 9: {'n': 823002} -> {'out0': 175}
        cur = 9;
        fork
            n_src.send(32'h000c8eda);
            start_src.send;
            wait (out0_snk.n == 10);
            wait (p_end_snk.n == 10);
        join
        $display("OUT 9 %0d", $signed(out0_snk.seen[9]));
        if (out0_snk.seen[9] !== 32'h000000af) begin
            errors = errors + 1;
            $display("  FAIL vector 9 ({'n': 823002}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[9]), out0_snk.seen[9], $signed(32'h000000af), 32'h000000af);
        end
        #(4 * T);

        // -- vector 10: {'n': 528854} -> {'out0': 164}
        cur = 10;
        fork
            n_src.send(32'h000811d6);
            start_src.send;
            wait (out0_snk.n == 11);
            wait (p_end_snk.n == 11);
        join
        $display("OUT 10 %0d", $signed(out0_snk.seen[10]));
        if (out0_snk.seen[10] !== 32'h000000a4) begin
            errors = errors + 1;
            $display("  FAIL vector 10 ({'n': 528854}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[10]), out0_snk.seen[10], $signed(32'h000000a4), 32'h000000a4);
        end
        #(4 * T);

        // -- vector 11: {'n': 650773} -> {'out0': 66}
        cur = 11;
        fork
            n_src.send(32'h0009ee15);
            start_src.send;
            wait (out0_snk.n == 12);
            wait (p_end_snk.n == 12);
        join
        $display("OUT 11 %0d", $signed(out0_snk.seen[11]));
        if (out0_snk.seen[11] !== 32'h00000042) begin
            errors = errors + 1;
            $display("  FAIL vector 11 ({'n': 650773}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[11]), out0_snk.seen[11], $signed(32'h00000042), 32'h00000042);
        end
        #(4 * T);

        // -- vector 12: {'n': 378922} -> {'out0': 192}
        cur = 12;
        fork
            n_src.send(32'h0005c82a);
            start_src.send;
            wait (out0_snk.n == 13);
            wait (p_end_snk.n == 13);
        join
        $display("OUT 12 %0d", $signed(out0_snk.seen[12]));
        if (out0_snk.seen[12] !== 32'h000000c0) begin
            errors = errors + 1;
            $display("  FAIL vector 12 ({'n': 378922}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[12]), out0_snk.seen[12], $signed(32'h000000c0), 32'h000000c0);
        end
        #(4 * T);

        // -- vector 13: {'n': 478637} -> {'out0': 76}
        cur = 13;
        fork
            n_src.send(32'h00074dad);
            start_src.send;
            wait (out0_snk.n == 14);
            wait (p_end_snk.n == 14);
        join
        $display("OUT 13 %0d", $signed(out0_snk.seen[13]));
        if (out0_snk.seen[13] !== 32'h0000004c) begin
            errors = errors + 1;
            $display("  FAIL vector 13 ({'n': 478637}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[13]), out0_snk.seen[13], $signed(32'h0000004c), 32'h0000004c);
        end
        #(4 * T);

        // -- vector 14: {'n': 808933} -> {'out0': 206}
        cur = 14;
        fork
            n_src.send(32'h000c57e5);
            start_src.send;
            wait (out0_snk.n == 15);
            wait (p_end_snk.n == 15);
        join
        $display("OUT 14 %0d", $signed(out0_snk.seen[14]));
        if (out0_snk.seen[14] !== 32'h000000ce) begin
            errors = errors + 1;
            $display("  FAIL vector 14 ({'n': 808933}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[14]), out0_snk.seen[14], $signed(32'h000000ce), 32'h000000ce);
        end
        #(4 * T);

        // -- vector 15: {'n': 244649} -> {'out0': 173}
        cur = 15;
        fork
            n_src.send(32'h0003bba9);
            start_src.send;
            wait (out0_snk.n == 16);
            wait (p_end_snk.n == 16);
        join
        $display("OUT 15 %0d", $signed(out0_snk.seen[15]));
        if (out0_snk.seen[15] !== 32'h000000ad) begin
            errors = errors + 1;
            $display("  FAIL vector 15 ({'n': 244649}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[15]), out0_snk.seen[15], $signed(32'h000000ad), 32'h000000ad);
        end
        #(4 * T);

        // -- vector 16: {'n': 65646} -> {'out0': 68}
        cur = 16;
        fork
            n_src.send(32'h0001006e);
            start_src.send;
            wait (out0_snk.n == 17);
            wait (p_end_snk.n == 17);
        join
        $display("OUT 16 %0d", $signed(out0_snk.seen[16]));
        if (out0_snk.seen[16] !== 32'h00000044) begin
            errors = errors + 1;
            $display("  FAIL vector 16 ({'n': 65646}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[16]), out0_snk.seen[16], $signed(32'h00000044), 32'h00000044);
        end
        #(4 * T);

        // -- vector 17: {'n': 807674} -> {'out0': 113}
        cur = 17;
        fork
            n_src.send(32'h000c52fa);
            start_src.send;
            wait (out0_snk.n == 18);
            wait (p_end_snk.n == 18);
        join
        $display("OUT 17 %0d", $signed(out0_snk.seen[17]));
        if (out0_snk.seen[17] !== 32'h00000071) begin
            errors = errors + 1;
            $display("  FAIL vector 17 ({'n': 807674}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[17]), out0_snk.seen[17], $signed(32'h00000071), 32'h00000071);
        end
        #(4 * T);

        // -- vector 18: {'n': 917020} -> {'out0': 64}
        cur = 18;
        fork
            n_src.send(32'h000dfe1c);
            start_src.send;
            wait (out0_snk.n == 19);
            wait (p_end_snk.n == 19);
        join
        $display("OUT 18 %0d", $signed(out0_snk.seen[18]));
        if (out0_snk.seen[18] !== 32'h00000040) begin
            errors = errors + 1;
            $display("  FAIL vector 18 ({'n': 917020}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[18]), out0_snk.seen[18], $signed(32'h00000040), 32'h00000040);
        end
        #(4 * T);

        // -- vector 19: {'n': 164705} -> {'out0': 183}
        cur = 19;
        fork
            n_src.send(32'h00028361);
            start_src.send;
            wait (out0_snk.n == 20);
            wait (p_end_snk.n == 20);
        join
        $display("OUT 19 %0d", $signed(out0_snk.seen[19]));
        if (out0_snk.seen[19] !== 32'h000000b7) begin
            errors = errors + 1;
            $display("  FAIL vector 19 ({'n': 164705}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[19]), out0_snk.seen[19], $signed(32'h000000b7), 32'h000000b7);
        end
        #(4 * T);

        // -- vector 20: {'n': 584356} -> {'out0': 177}
        cur = 20;
        fork
            n_src.send(32'h0008eaa4);
            start_src.send;
            wait (out0_snk.n == 21);
            wait (p_end_snk.n == 21);
        join
        $display("OUT 20 %0d", $signed(out0_snk.seen[20]));
        if (out0_snk.seen[20] !== 32'h000000b1) begin
            errors = errors + 1;
            $display("  FAIL vector 20 ({'n': 584356}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[20]), out0_snk.seen[20], $signed(32'h000000b1), 32'h000000b1);
        end
        #(4 * T);

        // -- vector 21: {'n': 936788} -> {'out0': 139}
        cur = 21;
        fork
            n_src.send(32'h000e4b54);
            start_src.send;
            wait (out0_snk.n == 22);
            wait (p_end_snk.n == 22);
        join
        $display("OUT 21 %0d", $signed(out0_snk.seen[21]));
        if (out0_snk.seen[21] !== 32'h0000008b) begin
            errors = errors + 1;
            $display("  FAIL vector 21 ({'n': 936788}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[21]), out0_snk.seen[21], $signed(32'h0000008b), 32'h0000008b);
        end
        #(4 * T);

        // -- vector 22: {'n': 260391} -> {'out0': 132}
        cur = 22;
        fork
            n_src.send(32'h0003f927);
            start_src.send;
            wait (out0_snk.n == 23);
            wait (p_end_snk.n == 23);
        join
        $display("OUT 22 %0d", $signed(out0_snk.seen[22]));
        if (out0_snk.seen[22] !== 32'h00000084) begin
            errors = errors + 1;
            $display("  FAIL vector 22 ({'n': 260391}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[22]), out0_snk.seen[22], $signed(32'h00000084), 32'h00000084);
        end
        #(4 * T);

        // -- vector 23: {'n': 652547} -> {'out0': 141}
        cur = 23;
        fork
            n_src.send(32'h0009f503);
            start_src.send;
            wait (out0_snk.n == 24);
            wait (p_end_snk.n == 24);
        join
        $display("OUT 23 %0d", $signed(out0_snk.seen[23]));
        if (out0_snk.seen[23] !== 32'h0000008d) begin
            errors = errors + 1;
            $display("  FAIL vector 23 ({'n': 652547}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[23]), out0_snk.seen[23], $signed(32'h0000008d), 32'h0000008d);
        end
        #(4 * T);

        // -- vector 24: {'n': 942694} -> {'out0': 170}
        cur = 24;
        fork
            n_src.send(32'h000e6266);
            start_src.send;
            wait (out0_snk.n == 25);
            wait (p_end_snk.n == 25);
        join
        $display("OUT 24 %0d", $signed(out0_snk.seen[24]));
        if (out0_snk.seen[24] !== 32'h000000aa) begin
            errors = errors + 1;
            $display("  FAIL vector 24 ({'n': 942694}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[24]), out0_snk.seen[24], $signed(32'h000000aa), 32'h000000aa);
        end
        #(4 * T);

        // -- vector 25: {'n': 556193} -> {'out0': 84}
        cur = 25;
        fork
            n_src.send(32'h00087ca1);
            start_src.send;
            wait (out0_snk.n == 26);
            wait (p_end_snk.n == 26);
        join
        $display("OUT 25 %0d", $signed(out0_snk.seen[25]));
        if (out0_snk.seen[25] !== 32'h00000054) begin
            errors = errors + 1;
            $display("  FAIL vector 25 ({'n': 556193}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[25]), out0_snk.seen[25], $signed(32'h00000054), 32'h00000054);
        end
        #(4 * T);

        // -- vector 26: {'n': 572194} -> {'out0': 221}
        cur = 26;
        fork
            n_src.send(32'h0008bb22);
            start_src.send;
            wait (out0_snk.n == 27);
            wait (p_end_snk.n == 27);
        join
        $display("OUT 26 %0d", $signed(out0_snk.seen[26]));
        if (out0_snk.seen[26] !== 32'h000000dd) begin
            errors = errors + 1;
            $display("  FAIL vector 26 ({'n': 572194}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[26]), out0_snk.seen[26], $signed(32'h000000dd), 32'h000000dd);
        end
        #(4 * T);

        // -- vector 27: {'n': 466758} -> {'out0': 107}
        cur = 27;
        fork
            n_src.send(32'h00071f46);
            start_src.send;
            wait (out0_snk.n == 28);
            wait (p_end_snk.n == 28);
        join
        $display("OUT 27 %0d", $signed(out0_snk.seen[27]));
        if (out0_snk.seen[27] !== 32'h0000006b) begin
            errors = errors + 1;
            $display("  FAIL vector 27 ({'n': 466758}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[27]), out0_snk.seen[27], $signed(32'h0000006b), 32'h0000006b);
        end
        #(4 * T);

        // -- vector 28: {'n': 352502} -> {'out0': 104}
        cur = 28;
        fork
            n_src.send(32'h000560f6);
            start_src.send;
            wait (out0_snk.n == 29);
            wait (p_end_snk.n == 29);
        join
        $display("OUT 28 %0d", $signed(out0_snk.seen[28]));
        if (out0_snk.seen[28] !== 32'h00000068) begin
            errors = errors + 1;
            $display("  FAIL vector 28 ({'n': 352502}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[28]), out0_snk.seen[28], $signed(32'h00000068), 32'h00000068);
        end
        #(4 * T);

        // -- vector 29: {'n': 632343} -> {'out0': 128}
        cur = 29;
        fork
            n_src.send(32'h0009a617);
            start_src.send;
            wait (out0_snk.n == 30);
            wait (p_end_snk.n == 30);
        join
        $display("OUT 29 %0d", $signed(out0_snk.seen[29]));
        if (out0_snk.seen[29] !== 32'h00000080) begin
            errors = errors + 1;
            $display("  FAIL vector 29 ({'n': 632343}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[29]), out0_snk.seen[29], $signed(32'h00000080), 32'h00000080);
        end
        #(4 * T);

        // -- vector 30: {'n': 813890} -> {'out0': 61}
        cur = 30;
        fork
            n_src.send(32'h000c6b42);
            start_src.send;
            wait (out0_snk.n == 31);
            wait (p_end_snk.n == 31);
        join
        $display("OUT 30 %0d", $signed(out0_snk.seen[30]));
        if (out0_snk.seen[30] !== 32'h0000003d) begin
            errors = errors + 1;
            $display("  FAIL vector 30 ({'n': 813890}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[30]), out0_snk.seen[30], $signed(32'h0000003d), 32'h0000003d);
        end
        #(4 * T);

        // -- vector 31: {'n': 380942} -> {'out0': 104}
        cur = 31;
        fork
            n_src.send(32'h0005d00e);
            start_src.send;
            wait (out0_snk.n == 32);
            wait (p_end_snk.n == 32);
        join
        $display("OUT 31 %0d", $signed(out0_snk.seen[31]));
        if (out0_snk.seen[31] !== 32'h00000068) begin
            errors = errors + 1;
            $display("  FAIL vector 31 ({'n': 380942}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[31]), out0_snk.seen[31], $signed(32'h00000068), 32'h00000068);
        end
        #(4 * T);

        // -- vector 32: {'n': 608968} -> {'out0': 66}
        cur = 32;
        fork
            n_src.send(32'h00094ac8);
            start_src.send;
            wait (out0_snk.n == 33);
            wait (p_end_snk.n == 33);
        join
        $display("OUT 32 %0d", $signed(out0_snk.seen[32]));
        if (out0_snk.seen[32] !== 32'h00000042) begin
            errors = errors + 1;
            $display("  FAIL vector 32 ({'n': 608968}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[32]), out0_snk.seen[32], $signed(32'h00000042), 32'h00000042);
        end
        #(4 * T);

        // -- vector 33: {'n': 644765} -> {'out0': 216}
        cur = 33;
        fork
            n_src.send(32'h0009d69d);
            start_src.send;
            wait (out0_snk.n == 34);
            wait (p_end_snk.n == 34);
        join
        $display("OUT 33 %0d", $signed(out0_snk.seen[33]));
        if (out0_snk.seen[33] !== 32'h000000d8) begin
            errors = errors + 1;
            $display("  FAIL vector 33 ({'n': 644765}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[33]), out0_snk.seen[33], $signed(32'h000000d8), 32'h000000d8);
        end
        #(4 * T);

        // -- vector 34: {'n': 246490} -> {'out0': 181}
        cur = 34;
        fork
            n_src.send(32'h0003c2da);
            start_src.send;
            wait (out0_snk.n == 35);
            wait (p_end_snk.n == 35);
        join
        $display("OUT 34 %0d", $signed(out0_snk.seen[34]));
        if (out0_snk.seen[34] !== 32'h000000b5) begin
            errors = errors + 1;
            $display("  FAIL vector 34 ({'n': 246490}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[34]), out0_snk.seen[34], $signed(32'h000000b5), 32'h000000b5);
        end
        #(4 * T);

        // -- vector 35: {'n': 911823} -> {'out0': 82}
        cur = 35;
        fork
            n_src.send(32'h000de9cf);
            start_src.send;
            wait (out0_snk.n == 36);
            wait (p_end_snk.n == 36);
        join
        $display("OUT 35 %0d", $signed(out0_snk.seen[35]));
        if (out0_snk.seen[35] !== 32'h00000052) begin
            errors = errors + 1;
            $display("  FAIL vector 35 ({'n': 911823}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[35]), out0_snk.seen[35], $signed(32'h00000052), 32'h00000052);
        end
        #(4 * T);

        // -- vector 36: {'n': 169129} -> {'out0': 227}
        cur = 36;
        fork
            n_src.send(32'h000294a9);
            start_src.send;
            wait (out0_snk.n == 37);
            wait (p_end_snk.n == 37);
        join
        $display("OUT 36 %0d", $signed(out0_snk.seen[36]));
        if (out0_snk.seen[36] !== 32'h000000e3) begin
            errors = errors + 1;
            $display("  FAIL vector 36 ({'n': 169129}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[36]), out0_snk.seen[36], $signed(32'h000000e3), 32'h000000e3);
        end
        #(4 * T);

        // -- vector 37: {'n': 255890} -> {'out0': 88}
        cur = 37;
        fork
            n_src.send(32'h0003e792);
            start_src.send;
            wait (out0_snk.n == 38);
            wait (p_end_snk.n == 38);
        join
        $display("OUT 37 %0d", $signed(out0_snk.seen[37]));
        if (out0_snk.seen[37] !== 32'h00000058) begin
            errors = errors + 1;
            $display("  FAIL vector 37 ({'n': 255890}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[37]), out0_snk.seen[37], $signed(32'h00000058), 32'h00000058);
        end
        #(4 * T);

        // -- vector 38: {'n': 272599} -> {'out0': 145}
        cur = 38;
        fork
            n_src.send(32'h000428d7);
            start_src.send;
            wait (out0_snk.n == 39);
            wait (p_end_snk.n == 39);
        join
        $display("OUT 38 %0d", $signed(out0_snk.seen[38]));
        if (out0_snk.seen[38] !== 32'h00000091) begin
            errors = errors + 1;
            $display("  FAIL vector 38 ({'n': 272599}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[38]), out0_snk.seen[38], $signed(32'h00000091), 32'h00000091);
        end
        #(4 * T);

        // -- vector 39: {'n': 999905} -> {'out0': 152}
        cur = 39;
        fork
            n_src.send(32'h000f41e1);
            start_src.send;
            wait (out0_snk.n == 40);
            wait (p_end_snk.n == 40);
        join
        $display("OUT 39 %0d", $signed(out0_snk.seen[39]));
        if (out0_snk.seen[39] !== 32'h00000098) begin
            errors = errors + 1;
            $display("  FAIL vector 39 ({'n': 999905}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[39]), out0_snk.seen[39], $signed(32'h00000098), 32'h00000098);
        end
        #(4 * T);

        // -- vector 40: {'n': 462649} -> {'out0': 76}
        cur = 40;
        fork
            n_src.send(32'h00070f39);
            start_src.send;
            wait (out0_snk.n == 41);
            wait (p_end_snk.n == 41);
        join
        $display("OUT 40 %0d", $signed(out0_snk.seen[40]));
        if (out0_snk.seen[40] !== 32'h0000004c) begin
            errors = errors + 1;
            $display("  FAIL vector 40 ({'n': 462649}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[40]), out0_snk.seen[40], $signed(32'h0000004c), 32'h0000004c);
        end
        #(4 * T);

        // -- vector 41: {'n': 97625} -> {'out0': 40}
        cur = 41;
        fork
            n_src.send(32'h00017d59);
            start_src.send;
            wait (out0_snk.n == 42);
            wait (p_end_snk.n == 42);
        join
        $display("OUT 41 %0d", $signed(out0_snk.seen[41]));
        if (out0_snk.seen[41] !== 32'h00000028) begin
            errors = errors + 1;
            $display("  FAIL vector 41 ({'n': 97625}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[41]), out0_snk.seen[41], $signed(32'h00000028), 32'h00000028);
        end
        #(4 * T);

        // -- vector 42: {'n': 583438} -> {'out0': 190}
        cur = 42;
        fork
            n_src.send(32'h0008e70e);
            start_src.send;
            wait (out0_snk.n == 43);
            wait (p_end_snk.n == 43);
        join
        $display("OUT 42 %0d", $signed(out0_snk.seen[42]));
        if (out0_snk.seen[42] !== 32'h000000be) begin
            errors = errors + 1;
            $display("  FAIL vector 42 ({'n': 583438}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[42]), out0_snk.seen[42], $signed(32'h000000be), 32'h000000be);
        end
        #(4 * T);

        // -- vector 43: {'n': 445470} -> {'out0': 94}
        cur = 43;
        fork
            n_src.send(32'h0006cc1e);
            start_src.send;
            wait (out0_snk.n == 44);
            wait (p_end_snk.n == 44);
        join
        $display("OUT 43 %0d", $signed(out0_snk.seen[43]));
        if (out0_snk.seen[43] !== 32'h0000005e) begin
            errors = errors + 1;
            $display("  FAIL vector 43 ({'n': 445470}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[43]), out0_snk.seen[43], $signed(32'h0000005e), 32'h0000005e);
        end
        #(4 * T);

        // -- vector 44: {'n': 898549} -> {'out0': 87}
        cur = 44;
        fork
            n_src.send(32'h000db5f5);
            start_src.send;
            wait (out0_snk.n == 45);
            wait (p_end_snk.n == 45);
        join
        $display("OUT 44 %0d", $signed(out0_snk.seen[44]));
        if (out0_snk.seen[44] !== 32'h00000057) begin
            errors = errors + 1;
            $display("  FAIL vector 44 ({'n': 898549}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[44]), out0_snk.seen[44], $signed(32'h00000057), 32'h00000057);
        end
        #(4 * T);

        // -- vector 45: {'n': 602217} -> {'out0': 115}
        cur = 45;
        fork
            n_src.send(32'h00093069);
            start_src.send;
            wait (out0_snk.n == 46);
            wait (p_end_snk.n == 46);
        join
        $display("OUT 45 %0d", $signed(out0_snk.seen[45]));
        if (out0_snk.seen[45] !== 32'h00000073) begin
            errors = errors + 1;
            $display("  FAIL vector 45 ({'n': 602217}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[45]), out0_snk.seen[45], $signed(32'h00000073), 32'h00000073);
        end
        #(4 * T);

        // -- vector 46: {'n': 877881} -> {'out0': 232}
        cur = 46;
        fork
            n_src.send(32'h000d6539);
            start_src.send;
            wait (out0_snk.n == 47);
            wait (p_end_snk.n == 47);
        join
        $display("OUT 46 %0d", $signed(out0_snk.seen[46]));
        if (out0_snk.seen[46] !== 32'h000000e8) begin
            errors = errors + 1;
            $display("  FAIL vector 46 ({'n': 877881}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[46]), out0_snk.seen[46], $signed(32'h000000e8), 32'h000000e8);
        end
        #(4 * T);

        // -- vector 47: {'n': 961224} -> {'out0': 139}
        cur = 47;
        fork
            n_src.send(32'h000eaac8);
            start_src.send;
            wait (out0_snk.n == 48);
            wait (p_end_snk.n == 48);
        join
        $display("OUT 47 %0d", $signed(out0_snk.seen[47]));
        if (out0_snk.seen[47] !== 32'h0000008b) begin
            errors = errors + 1;
            $display("  FAIL vector 47 ({'n': 961224}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[47]), out0_snk.seen[47], $signed(32'h0000008b), 32'h0000008b);
        end
        #(4 * T);

        // -- vector 48: {'n': 549123} -> {'out0': 177}
        cur = 48;
        fork
            n_src.send(32'h00086103);
            start_src.send;
            wait (out0_snk.n == 49);
            wait (p_end_snk.n == 49);
        join
        $display("OUT 48 %0d", $signed(out0_snk.seen[48]));
        if (out0_snk.seen[48] !== 32'h000000b1) begin
            errors = errors + 1;
            $display("  FAIL vector 48 ({'n': 549123}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[48]), out0_snk.seen[48], $signed(32'h000000b1), 32'h000000b1);
        end
        #(4 * T);

        // Teeth: a channel that never produced a token would pass every
        // comparison above by having nothing to compare.  Assert the
        // count explicitly, on every output channel.
        if (out0_snk.n != 49) begin
            errors = errors + 1;
            $display("  FAIL out0 produced %0d token(s), expected 49", out0_snk.n);
        end
        if (p_end_snk.n != 49) begin
            errors = errors + 1;
            $display("  FAIL p_end produced %0d token(s), expected 49", p_end_snk.n);
        end

        if (errors == 0) $display("tb_collatz PASS");
        else             $display("tb_collatz FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #20000000000;
        $display("tb_collatz FAIL (timeout) on vector %0d", cur);
        $display("    src n: %0d sent, req=%b ack=%b", n_src.nsent, n_req, n_ack);
        $display("    src start: %0d sent, req=%b ack=%b", start_src.nsent, start_req, start_ack);
        $display("    snk out0: %0d seen, req=%b ack=%b", out0_snk.n, out0_req, out0_ack);
        $display("    snk p_end: %0d seen, req=%b ack=%b", p_end_snk.n, p_end_req, p_end_ack);
        $finish;
    end

`ifdef SIMCHECK_VCD
    initial begin
        $dumpfile("tb_collatz.vcd");
        $dumpvars(0, tb_collatz);
    end
`endif
endmodule