
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

module tb_xorshift;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer cur = -1;
    reg rst = 1'b1;

    wire seed_req, seed_ack;
    wire [31:0] seed_data;
    bd_source #(.W(32)) seed_src (.req(seed_req), .ack(seed_ack), .data(seed_data));
    wire rounds_req, rounds_ack;
    wire [31:0] rounds_data;
    bd_source #(.W(32)) rounds_src (.req(rounds_req), .ack(rounds_ack), .data(rounds_data));
    wire start_req, start_ack;
    simcheck_ctl_src start_src (.req(start_req), .ack(start_ack));
    wire out0_req, out0_ack;
    wire [31:0] out0_data;
    bd_sink #(.W(32)) out0_snk (.req(out0_req), .ack(out0_ack), .data(out0_data));
    wire p_end_req, p_end_ack;
    simcheck_ctl_snk p_end_snk (.req(p_end_req), .ack(p_end_ack));

    bdc_xorshift uut (
        .rst(rst),
        .seed_req(seed_req), .seed_ack(seed_ack), .seed_data(seed_data),
        .rounds_req(rounds_req), .rounds_ack(rounds_ack), .rounds_data(rounds_data),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    initial begin
        $display("tb_xorshift");
        #(200 * T);
        rst = 1'b0;
        #(8 * T);

        // -- vector 0: {'seed': 123, 'rounds': 0} -> {'out0': 123}
        cur = 0;
        fork
            seed_src.send(32'h0000007b);
            rounds_src.send(32'h00000000);
            start_src.send;
            wait (out0_snk.n == 1);
            wait (p_end_snk.n == 1);
        join
        $display("OUT 0 %0d", $signed(out0_snk.seen[0]));
        if (out0_snk.seen[0] !== 32'h0000007b) begin
            errors = errors + 1;
            $display("  FAIL vector 0 ({'seed': 123, 'rounds': 0}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[0]), out0_snk.seen[0], $signed(32'h0000007b), 32'h0000007b);
        end
        #(4 * T);

        // -- vector 1: {'seed': 123, 'rounds': 3} -> {'out0': 2101636938}
        cur = 1;
        fork
            seed_src.send(32'h0000007b);
            rounds_src.send(32'h00000003);
            start_src.send;
            wait (out0_snk.n == 2);
            wait (p_end_snk.n == 2);
        join
        $display("OUT 1 %0d", $signed(out0_snk.seen[1]));
        if (out0_snk.seen[1] !== 32'h7d446f4a) begin
            errors = errors + 1;
            $display("  FAIL vector 1 ({'seed': 123, 'rounds': 3}): out0 got %0d (0x%h) expected %0d (0x%h)", $signed(out0_snk.seen[1]), out0_snk.seen[1], $signed(32'h7d446f4a), 32'h7d446f4a);
        end
        #(4 * T);

        // Teeth: a channel that never produced a token would pass every
        // comparison above by having nothing to compare.  Assert the
        // count explicitly, on every output channel.
        if (out0_snk.n != 2) begin
            errors = errors + 1;
            $display("  FAIL out0 produced %0d token(s), expected 2", out0_snk.n);
        end
        if (p_end_snk.n != 2) begin
            errors = errors + 1;
            $display("  FAIL p_end produced %0d token(s), expected 2", p_end_snk.n);
        end

        if (errors == 0) $display("tb_xorshift PASS");
        else             $display("tb_xorshift FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #100000000;
        $display("tb_xorshift FAIL (timeout) on vector %0d", cur);
        $display("    src seed: %0d sent, req=%b ack=%b", seed_src.nsent, seed_req, seed_ack);
        $display("    src rounds: %0d sent, req=%b ack=%b", rounds_src.nsent, rounds_req, rounds_ack);
        $display("    src start: %0d sent, req=%b ack=%b", start_src.nsent, start_req, start_ack);
        $display("    snk out0: %0d seen, req=%b ack=%b", out0_snk.n, out0_req, out0_ack);
        $display("    snk p_end: %0d seen, req=%b ack=%b", p_end_snk.n, p_end_req, p_end_ack);
        $finish;
    end

`ifdef SIMCHECK_VCD
    initial begin
        $dumpfile("tb_xorshift.vcd");
        $dumpvars(0, tb_xorshift);
    end
`endif
endmodule