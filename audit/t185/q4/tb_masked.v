
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

module tb_simcheck_varshift;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer cur = -1;
    reg rst = 1'b1;

    wire x_req, x_ack;
    wire [31:0] x_data;
    bd_source #(.W(32)) x_src (.req(x_req), .ack(x_ack), .data(x_data));
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

    bdc_varshift uut (
        .rst(rst),
        .x_req(x_req), .x_ack(x_ack), .x_data(x_data),
        .n_req(n_req), .n_ack(n_ack), .n_data(n_data),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    initial begin
        $display("tb_simcheck_varshift");
        #(268 * T);
        rst = 1'b0;
        #(8 * T);

        // -- vector 0: {'x': 252645940, 'n': 40} -> {'out0': 1154411406}
        cur = 0;
        fork
            x_src.send(32'h0f0f1234);
            n_src.send(32'h00000028);
            start_src.send;
            wait (out0_snk.n == 1);
            wait (p_end_snk.n == 1);
        join
        if (out0_snk.seen[0] !== 32'h44ceeb8e) begin
            errors = errors + 1;
            $display("  FAIL vector 0 ({'x': 252645940, 'n': 40}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[0]), out0_snk.seen[0], $signed(32'h44ceeb8e), 32'h44ceeb8e);
        end
        #(4 * T);

        // -- vector 1: {'x': 5, 'n': 3} -> {'out0': 321222768}
        cur = 1;
        fork
            x_src.send(32'h00000005);
            n_src.send(32'h00000003);
            start_src.send;
            wait (out0_snk.n == 2);
            wait (p_end_snk.n == 2);
        join
        if (out0_snk.seen[1] !== 32'h13257870) begin
            errors = errors + 1;
            $display("  FAIL vector 1 ({'x': 5, 'n': 3}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[1]), out0_snk.seen[1], $signed(32'h13257870), 32'h13257870);
        end
        #(4 * T);

        // -- vector 2: {'x': 0, 'n': 1} -> {'out0': 3733932309}
        cur = 2;
        fork
            x_src.send(32'h00000000);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 3);
            wait (p_end_snk.n == 3);
        join
        if (out0_snk.seen[2] !== 32'hde8f4915) begin
            errors = errors + 1;
            $display("  FAIL vector 2 ({'x': 0, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[2]), out0_snk.seen[2], $signed(32'hde8f4915), 32'hde8f4915);
        end
        #(4 * T);

        // -- vector 3: {'x': 4294967295, 'n': 256} -> {'out0': 1090190241}
        cur = 3;
        fork
            x_src.send(32'hffffffff);
            n_src.send(32'h00000100);
            start_src.send;
            wait (out0_snk.n == 4);
            wait (p_end_snk.n == 4);
        join
        if (out0_snk.seen[3] !== 32'h40fafba1) begin
            errors = errors + 1;
            $display("  FAIL vector 3 ({'x': 4294967295, 'n': 256}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[3]), out0_snk.seen[3], $signed(32'h40fafba1), 32'h40fafba1);
        end
        #(4 * T);

        // -- vector 4: {'x': 2147483648, 'n': 100} -> {'out0': 1093664349}
        cur = 4;
        fork
            x_src.send(32'h80000000);
            n_src.send(32'h00000064);
            start_src.send;
            wait (out0_snk.n == 5);
            wait (p_end_snk.n == 5);
        join
        if (out0_snk.seen[4] !== 32'h412ffe5d) begin
            errors = errors + 1;
            $display("  FAIL vector 4 ({'x': 2147483648, 'n': 100}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[4]), out0_snk.seen[4], $signed(32'h412ffe5d), 32'h412ffe5d);
        end
        #(4 * T);

        // -- vector 5: {'x': 2147483647, 'n': 64} -> {'out0': 1216801153}
        cur = 5;
        fork
            x_src.send(32'h7fffffff);
            n_src.send(32'h00000040);
            start_src.send;
            wait (out0_snk.n == 6);
            wait (p_end_snk.n == 6);
        join
        if (out0_snk.seen[5] !== 32'h4886e981) begin
            errors = errors + 1;
            $display("  FAIL vector 5 ({'x': 2147483647, 'n': 64}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[5]), out0_snk.seen[5], $signed(32'h4886e981), 32'h4886e981);
        end
        #(4 * T);

        // -- vector 6: {'x': 123, 'n': 4294967291} -> {'out0': 1540483477}
        cur = 6;
        fork
            x_src.send(32'h0000007b);
            n_src.send(32'hfffffffb);
            start_src.send;
            wait (out0_snk.n == 7);
            wait (p_end_snk.n == 7);
        join
        if (out0_snk.seen[6] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 6 ({'x': 123, 'n': 4294967291}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[6]), out0_snk.seen[6], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 7: {'x': 0, 'n': 0} -> {'out0': 1540483477}
        cur = 7;
        fork
            x_src.send(32'h00000000);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 8);
            wait (p_end_snk.n == 8);
        join
        if (out0_snk.seen[7] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 7 ({'x': 0, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[7]), out0_snk.seen[7], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 8: {'x': 2795375927, 'n': 6} -> {'out0': 1099122213}
        cur = 8;
        fork
            x_src.send(32'ha69e0d37);
            n_src.send(32'h00000006);
            start_src.send;
            wait (out0_snk.n == 9);
            wait (p_end_snk.n == 9);
        join
        if (out0_snk.seen[8] !== 32'h41834625) begin
            errors = errors + 1;
            $display("  FAIL vector 8 ({'x': 2795375927, 'n': 6}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[8]), out0_snk.seen[8], $signed(32'h41834625), 32'h41834625);
        end
        #(4 * T);

        // -- vector 9: {'x': 31936245, 'n': 4294967293} -> {'out0': 1540483477}
        cur = 9;
        fork
            x_src.send(32'h01e74ef5);
            n_src.send(32'hfffffffd);
            start_src.send;
            wait (out0_snk.n == 10);
            wait (p_end_snk.n == 10);
        join
        if (out0_snk.seen[9] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 9 ({'x': 31936245, 'n': 4294967293}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[9]), out0_snk.seen[9], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 10: {'x': 3943519387, 'n': 4294967293} -> {'out0': 1540483477}
        cur = 10;
        fork
            x_src.send(32'heb0d549b);
            n_src.send(32'hfffffffd);
            start_src.send;
            wait (out0_snk.n == 11);
            wait (p_end_snk.n == 11);
        join
        if (out0_snk.seen[10] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 10 ({'x': 3943519387, 'n': 4294967293}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[10]), out0_snk.seen[10], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 11: {'x': 281121487, 'n': 28} -> {'out0': 1143313681}
        cur = 11;
        fork
            x_src.send(32'h10c192cf);
            n_src.send(32'h0000001c);
            start_src.send;
            wait (out0_snk.n == 12);
            wait (p_end_snk.n == 12);
        join
        if (out0_snk.seen[11] !== 32'h44259511) begin
            errors = errors + 1;
            $display("  FAIL vector 11 ({'x': 281121487, 'n': 28}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[11]), out0_snk.seen[11], $signed(32'h44259511), 32'h44259511);
        end
        #(4 * T);

        // -- vector 12: {'x': 3851213332, 'n': 28} -> {'out0': 688378615}
        cur = 12;
        fork
            x_src.send(32'he58cda14);
            n_src.send(32'h0000001c);
            start_src.send;
            wait (out0_snk.n == 13);
            wait (p_end_snk.n == 13);
        join
        if (out0_snk.seen[12] !== 32'h2907d2f7) begin
            errors = errors + 1;
            $display("  FAIL vector 12 ({'x': 3851213332, 'n': 28}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[12]), out0_snk.seen[12], $signed(32'h2907d2f7), 32'h2907d2f7);
        end
        #(4 * T);

        // -- vector 13: {'x': 3391346070, 'n': 18} -> {'out0': 2934032885}
        cur = 13;
        fork
            x_src.send(32'hca23d596);
            n_src.send(32'h00000012);
            start_src.send;
            wait (out0_snk.n == 14);
            wait (p_end_snk.n == 14);
        join
        if (out0_snk.seen[13] !== 32'haee1c9f5) begin
            errors = errors + 1;
            $display("  FAIL vector 13 ({'x': 3391346070, 'n': 18}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[13]), out0_snk.seen[13], $signed(32'haee1c9f5), 32'haee1c9f5);
        end
        #(4 * T);

        // -- vector 14: {'x': 304571992, 'n': 71} -> {'out0': 1079046577}
        cur = 14;
        fork
            x_src.send(32'h12276658);
            n_src.send(32'h00000047);
            start_src.send;
            wait (out0_snk.n == 15);
            wait (p_end_snk.n == 15);
        join
        if (out0_snk.seen[14] !== 32'h4050f1b1) begin
            errors = errors + 1;
            $display("  FAIL vector 14 ({'x': 304571992, 'n': 71}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[14]), out0_snk.seen[14], $signed(32'h4050f1b1), 32'h4050f1b1);
        end
        #(4 * T);

        // -- vector 15: {'x': 2954383557, 'n': 12} -> {'out0': 2358907288}
        cur = 15;
        fork
            x_src.send(32'hb01850c5);
            n_src.send(32'h0000000c);
            start_src.send;
            wait (out0_snk.n == 16);
            wait (p_end_snk.n == 16);
        join
        if (out0_snk.seen[15] !== 32'h8c9a1198) begin
            errors = errors + 1;
            $display("  FAIL vector 15 ({'x': 2954383557, 'n': 12}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[15]), out0_snk.seen[15], $signed(32'h8c9a1198), 32'h8c9a1198);
        end
        #(4 * T);

        // -- vector 16: {'x': 276459715, 'n': 4294967294} -> {'out0': 1540483477}
        cur = 16;
        fork
            x_src.send(32'h107a70c3);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 17);
            wait (p_end_snk.n == 17);
        join
        if (out0_snk.seen[16] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 16 ({'x': 276459715, 'n': 4294967294}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[16]), out0_snk.seen[16], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 17: {'x': 3496735471, 'n': 0} -> {'out0': 1540483477}
        cur = 17;
        fork
            x_src.send(32'hd06bf2ef);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 18);
            wait (p_end_snk.n == 18);
        join
        if (out0_snk.seen[17] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 17 ({'x': 3496735471, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[17]), out0_snk.seen[17], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 18: {'x': 3434973101, 'n': 23} -> {'out0': 2775153258}
        cur = 18;
        fork
            x_src.send(32'hccbd87ad);
            n_src.send(32'h00000017);
            start_src.send;
            wait (out0_snk.n == 19);
            wait (p_end_snk.n == 19);
        join
        if (out0_snk.seen[18] !== 32'ha5697a6a) begin
            errors = errors + 1;
            $display("  FAIL vector 18 ({'x': 3434973101, 'n': 23}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[18]), out0_snk.seen[18], $signed(32'ha5697a6a), 32'ha5697a6a);
        end
        #(4 * T);

        // -- vector 19: {'x': 4075211834, 'n': 77} -> {'out0': 1713652451}
        cur = 19;
        fork
            x_src.send(32'hf2e6cc3a);
            n_src.send(32'h0000004d);
            start_src.send;
            wait (out0_snk.n == 20);
            wait (p_end_snk.n == 20);
        join
        if (out0_snk.seen[19] !== 32'h662442e3) begin
            errors = errors + 1;
            $display("  FAIL vector 19 ({'x': 4075211834, 'n': 77}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[19]), out0_snk.seen[19], $signed(32'h662442e3), 32'h662442e3);
        end
        #(4 * T);

        // -- vector 20: {'x': 51251132, 'n': 21} -> {'out0': 1176814395}
        cur = 20;
        fork
            x_src.send(32'h030e07bc);
            n_src.send(32'h00000015);
            start_src.send;
            wait (out0_snk.n == 21);
            wait (p_end_snk.n == 21);
        join
        if (out0_snk.seen[20] !== 32'h4624c33b) begin
            errors = errors + 1;
            $display("  FAIL vector 20 ({'x': 51251132, 'n': 21}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[20]), out0_snk.seen[20], $signed(32'h4624c33b), 32'h4624c33b);
        end
        #(4 * T);

        // -- vector 21: {'x': 1860881378, 'n': 53} -> {'out0': 1145941665}
        cur = 21;
        fork
            x_src.send(32'h6eeacbe2);
            n_src.send(32'h00000035);
            start_src.send;
            wait (out0_snk.n == 22);
            wait (p_end_snk.n == 22);
        join
        if (out0_snk.seen[21] !== 32'h444daea1) begin
            errors = errors + 1;
            $display("  FAIL vector 21 ({'x': 1860881378, 'n': 53}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[21]), out0_snk.seen[21], $signed(32'h444daea1), 32'h444daea1);
        end
        #(4 * T);

        // -- vector 22: {'x': 3495018956, 'n': 1} -> {'out0': 3734324013}
        cur = 22;
        fork
            x_src.send(32'hd051c1cc);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 23);
            wait (p_end_snk.n == 23);
        join
        if (out0_snk.seen[22] !== 32'hde95432d) begin
            errors = errors + 1;
            $display("  FAIL vector 22 ({'x': 3495018956, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[22]), out0_snk.seen[22], $signed(32'hde95432d), 32'hde95432d);
        end
        #(4 * T);

        // -- vector 23: {'x': 4106870634, 'n': 4294967295} -> {'out0': 1540483477}
        cur = 23;
        fork
            x_src.send(32'hf4c9df6a);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 24);
            wait (p_end_snk.n == 24);
        join
        if (out0_snk.seen[23] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 23 ({'x': 4106870634, 'n': 4294967295}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[23]), out0_snk.seen[23], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 24: {'x': 2426656434, 'n': 2} -> {'out0': 151207613}
        cur = 24;
        fork
            x_src.send(32'h90a3d6b2);
            n_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 25);
            wait (p_end_snk.n == 25);
        join
        if (out0_snk.seen[24] !== 32'h09033ebd) begin
            errors = errors + 1;
            $display("  FAIL vector 24 ({'x': 2426656434, 'n': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[24]), out0_snk.seen[24], $signed(32'h09033ebd), 32'h09033ebd);
        end
        #(4 * T);

        // -- vector 25: {'x': 724357918, 'n': 0} -> {'out0': 1540483477}
        cur = 25;
        fork
            x_src.send(32'h2b2cd31e);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 26);
            wait (p_end_snk.n == 26);
        join
        if (out0_snk.seen[25] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 25 ({'x': 724357918, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[25]), out0_snk.seen[25], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 26: {'x': 2650406264, 'n': 4294967294} -> {'out0': 1540483477}
        cur = 26;
        fork
            x_src.send(32'h9df9fd78);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 27);
            wait (p_end_snk.n == 27);
        join
        if (out0_snk.seen[26] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 26 ({'x': 2650406264, 'n': 4294967294}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[26]), out0_snk.seen[26], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 27: {'x': 3210981251, 'n': 50} -> {'out0': 1159625619}
        cur = 27;
        fork
            x_src.send(32'hbf63af83);
            n_src.send(32'h00000032);
            start_src.send;
            wait (out0_snk.n == 28);
            wait (p_end_snk.n == 28);
        join
        if (out0_snk.seen[27] !== 32'h451e7b93) begin
            errors = errors + 1;
            $display("  FAIL vector 27 ({'x': 3210981251, 'n': 50}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[27]), out0_snk.seen[27], $signed(32'h451e7b93), 32'h451e7b93);
        end
        #(4 * T);

        // -- vector 28: {'x': 2862021402, 'n': 1} -> {'out0': 3734641610}
        cur = 28;
        fork
            x_src.send(32'haa96fb1a);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 29);
            wait (p_end_snk.n == 29);
        join
        if (out0_snk.seen[28] !== 32'hde9a1bca) begin
            errors = errors + 1;
            $display("  FAIL vector 28 ({'x': 2862021402, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[28]), out0_snk.seen[28], $signed(32'hde9a1bca), 32'hde9a1bca);
        end
        #(4 * T);

        // -- vector 29: {'x': 1646621017, 'n': 1} -> {'out0': 3733130683}
        cur = 29;
        fork
            x_src.send(32'h62257159);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 30);
            wait (p_end_snk.n == 30);
        join
        if (out0_snk.seen[29] !== 32'hde830dbb) begin
            errors = errors + 1;
            $display("  FAIL vector 29 ({'x': 1646621017, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[29]), out0_snk.seen[29], $signed(32'hde830dbb), 32'hde830dbb);
        end
        #(4 * T);

        // -- vector 30: {'x': 886467130, 'n': 2} -> {'out0': 161874938}
        cur = 30;
        fork
            x_src.send(32'h34d66a3a);
            n_src.send(32'h00000002);
            start_src.send;
            wait (out0_snk.n == 31);
            wait (p_end_snk.n == 31);
        join
        if (out0_snk.seen[30] !== 32'h09a603fa) begin
            errors = errors + 1;
            $display("  FAIL vector 30 ({'x': 886467130, 'n': 2}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[30]), out0_snk.seen[30], $signed(32'h09a603fa), 32'h09a603fa);
        end
        #(4 * T);

        // -- vector 31: {'x': 1965940573, 'n': 19} -> {'out0': 1184954562}
        cur = 31;
        fork
            x_src.send(32'h752ddf5d);
            n_src.send(32'h00000013);
            start_src.send;
            wait (out0_snk.n == 32);
            wait (p_end_snk.n == 32);
        join
        if (out0_snk.seen[31] !== 32'h46a0f8c2) begin
            errors = errors + 1;
            $display("  FAIL vector 31 ({'x': 1965940573, 'n': 19}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[31]), out0_snk.seen[31], $signed(32'h46a0f8c2), 32'h46a0f8c2);
        end
        #(4 * T);

        // -- vector 32: {'x': 2797305277, 'n': 4294967293} -> {'out0': 1540483477}
        cur = 32;
        fork
            x_src.send(32'ha6bb7dbd);
            n_src.send(32'hfffffffd);
            start_src.send;
            wait (out0_snk.n == 33);
            wait (p_end_snk.n == 33);
        join
        if (out0_snk.seen[32] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 32 ({'x': 2797305277, 'n': 4294967293}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[32]), out0_snk.seen[32], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 33: {'x': 2930640335, 'n': 36} -> {'out0': 1166226059}
        cur = 33;
        fork
            x_src.send(32'haeae05cf);
            n_src.send(32'h00000024);
            start_src.send;
            wait (out0_snk.n == 34);
            wait (p_end_snk.n == 34);
        join
        if (out0_snk.seen[33] !== 32'h4583328b) begin
            errors = errors + 1;
            $display("  FAIL vector 33 ({'x': 2930640335, 'n': 36}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[33]), out0_snk.seen[33], $signed(32'h4583328b), 32'h4583328b);
        end
        #(4 * T);

        // -- vector 34: {'x': 284933393, 'n': 16} -> {'out0': 2630870337}
        cur = 34;
        fork
            x_src.send(32'h10fbbd11);
            n_src.send(32'h00000010);
            start_src.send;
            wait (out0_snk.n == 35);
            wait (p_end_snk.n == 35);
        join
        if (out0_snk.seen[34] !== 32'h9ccfe541) begin
            errors = errors + 1;
            $display("  FAIL vector 34 ({'x': 284933393, 'n': 16}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[34]), out0_snk.seen[34], $signed(32'h9ccfe541), 32'h9ccfe541);
        end
        #(4 * T);

        // -- vector 35: {'x': 254570184, 'n': 0} -> {'out0': 1540483477}
        cur = 35;
        fork
            x_src.send(32'h0f2c6ec8);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 36);
            wait (p_end_snk.n == 36);
        join
        if (out0_snk.seen[35] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 35 ({'x': 254570184, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[35]), out0_snk.seen[35], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 36: {'x': 2592172076, 'n': 51} -> {'out0': 2013986884}
        cur = 36;
        fork
            x_src.send(32'h9a81682c);
            n_src.send(32'h00000033);
            start_src.send;
            wait (out0_snk.n == 37);
            wait (p_end_snk.n == 37);
        join
        if (out0_snk.seen[36] !== 32'h780b0044) begin
            errors = errors + 1;
            $display("  FAIL vector 36 ({'x': 2592172076, 'n': 51}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[36]), out0_snk.seen[36], $signed(32'h780b0044), 32'h780b0044);
        end
        #(4 * T);

        // -- vector 37: {'x': 3044114698, 'n': 4294967293} -> {'out0': 1540483477}
        cur = 37;
        fork
            x_src.send(32'hb571810a);
            n_src.send(32'hfffffffd);
            start_src.send;
            wait (out0_snk.n == 38);
            wait (p_end_snk.n == 38);
        join
        if (out0_snk.seen[37] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 37 ({'x': 3044114698, 'n': 4294967293}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[37]), out0_snk.seen[37], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 38: {'x': 432620297, 'n': 13} -> {'out0': 3273626660}
        cur = 38;
        fork
            x_src.send(32'h19c94309);
            n_src.send(32'h0000000d);
            start_src.send;
            wait (out0_snk.n == 39);
            wait (p_end_snk.n == 39);
        join
        if (out0_snk.seen[38] !== 32'hc31f9424) begin
            errors = errors + 1;
            $display("  FAIL vector 38 ({'x': 432620297, 'n': 13}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[38]), out0_snk.seen[38], $signed(32'hc31f9424), 32'hc31f9424);
        end
        #(4 * T);

        // -- vector 39: {'x': 157276083, 'n': 46} -> {'out0': 1106205314}
        cur = 39;
        fork
            x_src.send(32'h095fd7b3);
            n_src.send(32'h0000002e);
            start_src.send;
            wait (out0_snk.n == 40);
            wait (p_end_snk.n == 40);
        join
        if (out0_snk.seen[39] !== 32'h41ef5a82) begin
            errors = errors + 1;
            $display("  FAIL vector 39 ({'x': 157276083, 'n': 46}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[39]), out0_snk.seen[39], $signed(32'h41ef5a82), 32'h41ef5a82);
        end
        #(4 * T);

        // -- vector 40: {'x': 3763376458, 'n': 4294967295} -> {'out0': 1540483477}
        cur = 40;
        fork
            x_src.send(32'he050914a);
            n_src.send(32'hffffffff);
            start_src.send;
            wait (out0_snk.n == 41);
            wait (p_end_snk.n == 41);
        join
        if (out0_snk.seen[40] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 40 ({'x': 3763376458, 'n': 4294967295}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[40]), out0_snk.seen[40], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 41: {'x': 4183948690, 'n': 0} -> {'out0': 1540483477}
        cur = 41;
        fork
            x_src.send(32'hf961fd92);
            n_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 42);
            wait (p_end_snk.n == 42);
        join
        if (out0_snk.seen[41] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 41 ({'x': 4183948690, 'n': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[41]), out0_snk.seen[41], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 42: {'x': 4210764904, 'n': 39} -> {'out0': 169945832}
        cur = 42;
        fork
            x_src.send(32'hfafb2c68);
            n_src.send(32'h00000027);
            start_src.send;
            wait (out0_snk.n == 43);
            wait (p_end_snk.n == 43);
        join
        if (out0_snk.seen[42] !== 32'h0a212ae8) begin
            errors = errors + 1;
            $display("  FAIL vector 42 ({'x': 4210764904, 'n': 39}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[42]), out0_snk.seen[42], $signed(32'h0a212ae8), 32'h0a212ae8);
        end
        #(4 * T);

        // -- vector 43: {'x': 3284605850, 'n': 20} -> {'out0': 1142993923}
        cur = 43;
        fork
            x_src.send(32'hc3c71b9a);
            n_src.send(32'h00000014);
            start_src.send;
            wait (out0_snk.n == 44);
            wait (p_end_snk.n == 44);
        join
        if (out0_snk.seen[43] !== 32'h4420b403) begin
            errors = errors + 1;
            $display("  FAIL vector 43 ({'x': 3284605850, 'n': 20}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[43]), out0_snk.seen[43], $signed(32'h4420b403), 32'h4420b403);
        end
        #(4 * T);

        // -- vector 44: {'x': 3701198645, 'n': 4294967293} -> {'out0': 1540483477}
        cur = 44;
        fork
            x_src.send(32'hdc9bcf35);
            n_src.send(32'hfffffffd);
            start_src.send;
            wait (out0_snk.n == 45);
            wait (p_end_snk.n == 45);
        join
        if (out0_snk.seen[44] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 44 ({'x': 3701198645, 'n': 4294967293}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[44]), out0_snk.seen[44], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 45: {'x': 1560469138, 'n': 1} -> {'out0': 3733252430}
        cur = 45;
        fork
            x_src.send(32'h5d02de92);
            n_src.send(32'h00000001);
            start_src.send;
            wait (out0_snk.n == 46);
            wait (p_end_snk.n == 46);
        join
        if (out0_snk.seen[45] !== 32'hde84e94e) begin
            errors = errors + 1;
            $display("  FAIL vector 45 ({'x': 1560469138, 'n': 1}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[45]), out0_snk.seen[45], $signed(32'hde84e94e), 32'hde84e94e);
        end
        #(4 * T);

        // -- vector 46: {'x': 1753457108, 'n': 4294967294} -> {'out0': 1540483477}
        cur = 46;
        fork
            x_src.send(32'h6883a1d4);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 47);
            wait (p_end_snk.n == 47);
        join
        if (out0_snk.seen[46] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 46 ({'x': 1753457108, 'n': 4294967294}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[46]), out0_snk.seen[46], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 47: {'x': 586013629, 'n': 78} -> {'out0': 1135071433}
        cur = 47;
        fork
            x_src.send(32'h22eddbbd);
            n_src.send(32'h0000004e);
            start_src.send;
            wait (out0_snk.n == 48);
            wait (p_end_snk.n == 48);
        join
        if (out0_snk.seen[47] !== 32'h43a7d0c9) begin
            errors = errors + 1;
            $display("  FAIL vector 47 ({'x': 586013629, 'n': 78}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[47]), out0_snk.seen[47], $signed(32'h43a7d0c9), 32'h43a7d0c9);
        end
        #(4 * T);

        // -- vector 48: {'x': 1367229591, 'n': 4294967294} -> {'out0': 1540483477}
        cur = 48;
        fork
            x_src.send(32'h517e4497);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 49);
            wait (p_end_snk.n == 49);
        join
        if (out0_snk.seen[48] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 48 ({'x': 1367229591, 'n': 4294967294}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[48]), out0_snk.seen[48], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // -- vector 49: {'x': 3347577147, 'n': 4294967294} -> {'out0': 1540483477}
        cur = 49;
        fork
            x_src.send(32'hc787f93b);
            n_src.send(32'hfffffffe);
            start_src.send;
            wait (out0_snk.n == 50);
            wait (p_end_snk.n == 50);
        join
        if (out0_snk.seen[49] !== 32'h5bd1e995) begin
            errors = errors + 1;
            $display("  FAIL vector 49 ({'x': 3347577147, 'n': 4294967294}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[49]), out0_snk.seen[49], $signed(32'h5bd1e995), 32'h5bd1e995);
        end
        #(4 * T);

        // Teeth: a channel that never produced a token would pass every
        // comparison above by having nothing to compare.  Assert the
        // count explicitly, on every output channel.
        if (out0_snk.n != 50) begin
            errors = errors + 1;
            $display("  FAIL out0 produced %0d token(s), expected 50", out0_snk.n);
        end
        if (p_end_snk.n != 50) begin
            errors = errors + 1;
            $display("  FAIL p_end produced %0d token(s), expected 50", p_end_snk.n);
        end

        if (errors == 0) $display("tb_simcheck_varshift PASS");
        else             $display("tb_simcheck_varshift FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #400000000;
        $display("tb_simcheck_varshift FAIL (timeout) on vector %0d", cur);
        $display("    src x: %0d sent, req=%b ack=%b", x_src.nsent, x_req, x_ack);
        $display("    src n: %0d sent, req=%b ack=%b", n_src.nsent, n_req, n_ack);
        $display("    src start: %0d sent, req=%b ack=%b", start_src.nsent, start_req, start_ack);
        $display("    snk out0: %0d seen, req=%b ack=%b", out0_snk.n, out0_req, out0_ack);
        $display("    snk p_end: %0d seen, req=%b ack=%b", p_end_snk.n, p_end_req, p_end_ack);
        $finish;
    end

`ifdef SIMCHECK_VCD
    initial begin
        $dumpfile("tb_simcheck_varshift.vcd");
        $dumpvars(0, tb_simcheck_varshift);
    end
`endif
endmodule