// tb_store1.v -- RTL testbench for a store kernel with ONE memref and two 32-bit operand words, through its
// --host-mem port (research/data/suite/stores.md).  Zero-wire-delay RTL (cells/sim/bd_prims_sim.v arcs): it shows
// the handshakes and the store lowering compute the C's answer and final array, nothing about routed timing.
// Per call (as ps7_bench.v does): fill the array through the host slot, run the kernel NRUNS times without
// refilling, check out0 against EXP each run, read every element back and check it against MEMEXP.
// Files (+plusargs): VEC= v2 vector file (memvec.py), EXP= oracle_mem.sh output, MEMEXP= the C's final contents,
// flattened to one hex word per line (stores.md says how), NCALLS=, NRUNS= (default 2).
// Prints TBSTORE call=J run=R out0=... exp=... ok|BAD, TBSTOREMEM call=J bad=K, and TBSTORE SUMMARY pass|FAIL.
`timescale 1ps/1ps
`ifndef K
 `define K bdc_fill
`endif
`ifndef DEPTH
 `define DEPTH 32
`endif
`ifndef AW
 `define AW 5
`endif
module tb_store1;
    localparam D = `DEPTH, W = 2 + D;
    reg rst = 1;
    reg n_req = 0, x_req = 0, a_start_req = 0, start_req = 0;
    reg [31:0] n_data = 0, x_data = 0;
    wire n_ack, x_ack, a_start_ack, start_ack;
    wire out0_req, a_end_req, p_end_req;
    reg out0_ack = 0, a_end_ack = 0, p_end_ack = 0;
    wire [31:0] out0_data;
    reg a_host_req = 0, a_host_we = 0;
    reg [`AW-1:0] a_host_addr = 0;
    reg [31:0] a_host_wdata = 0;
    wire a_host_ack;
    wire [31:0] a_host_rdata;
    `K dut (.rst(rst),
        .n_req(n_req), .n_ack(n_ack), .n_data(n_data),
        .x_req(x_req), .x_ack(x_ack), .x_data(x_data),
        .a_start_req(a_start_req), .a_start_ack(a_start_ack),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req), .out0_ack(out0_ack), .out0_data(out0_data),
        .a_end_req(a_end_req), .a_end_ack(a_end_ack),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack),
        .a_host_req(a_host_req), .a_host_ack(a_host_ack), .a_host_addr(a_host_addr),
        .a_host_wdata(a_host_wdata), .a_host_we(a_host_we), .a_host_rdata(a_host_rdata));

    reg [31:0] vec [0:W*16-1];
    reg [31:0] exp [0:15];
    reg [31:0] mexp [0:D*16-1];
    reg [1023:0] fv, fe, fm;
    integer ncalls, nruns, c, r, i, bad, fails, mbad;
    reg [31:0] rd, got;

    task host(input [`AW-1:0] a, input [31:0] d, input we, output [31:0] q);
        begin
            wait (a_host_ack === 1'b0);
            a_host_addr = a; a_host_wdata = d; a_host_we = we;
            #1000 a_host_req = 1;
            wait (a_host_ack === 1'b1);
            // sample late: in this RTL model bd_mem's placeholder DCO (12 LUT arcs, ~1.5 ns) is shorter than the
            // RAM model's clock-to-out (2.454 ns); post-route the chain is sized against it (rule C), here it is not
            #3000 q = a_host_rdata;
            a_host_req = 0;
            wait (a_host_ack === 1'b0);
            #1000;
        end
    endtask

    // one call: the four input channels and the three output channels, each its own four-phase handshake
    task run_call(input [31:0] nn, input [31:0] xx, output [31:0] res);
        begin
            fork
                begin n_data = nn; #200 n_req = 1; wait (n_ack === 1'b1); n_req = 0; wait (n_ack === 1'b0); end
                begin x_data = xx; #200 x_req = 1; wait (x_ack === 1'b1); x_req = 0; wait (x_ack === 1'b0); end
                begin #200 a_start_req = 1; wait (a_start_ack === 1'b1); a_start_req = 0; wait (a_start_ack === 1'b0); end
                begin #200 start_req = 1; wait (start_ack === 1'b1); start_req = 0; wait (start_ack === 1'b0); end
                begin wait (out0_req === 1'b1); res = out0_data; #300 out0_ack = 1; wait (out0_req === 1'b0); #300 out0_ack = 0; end
                begin wait (a_end_req === 1'b1); #300 a_end_ack = 1; wait (a_end_req === 1'b0); #300 a_end_ack = 0; end
                begin wait (p_end_req === 1'b1); #300 p_end_ack = 1; wait (p_end_req === 1'b0); #300 p_end_ack = 0; end
            join
            #2000;
        end
    endtask

    initial begin
        if (!$value$plusargs("VEC=%s", fv) || !$value$plusargs("EXP=%s", fe) || !$value$plusargs("MEMEXP=%s", fm) ||
            !$value$plusargs("NCALLS=%d", ncalls)) begin
            $display("TBSTORE SUMMARY FAIL (usage: +VEC= +EXP= +MEMEXP= +NCALLS=)"); $finish;
        end
        if (!$value$plusargs("NRUNS=%d", nruns)) nruns = 2;
        $readmemh(fv, vec); $readmemh(fe, exp); $readmemh(fm, mexp);
        fails = 0;
        #20000 rst = 0; #20000;
        for (c = 0; c < ncalls; c = c + 1) begin
            for (i = 0; i < D; i = i + 1) host(i, vec[c*W + 2 + i], 1'b1, rd);
            for (r = 0; r < nruns; r = r + 1) begin
                run_call(vec[c*W], vec[c*W + 1], got);
                $display("TBSTORE call=%0d run=%0d out0=%08x exp=%08x %s", c, r, got, exp[c], got === exp[c] ? "ok" : "BAD");
                if (got !== exp[c]) fails = fails + 1;
            end
            mbad = 0;
            for (i = 0; i < D; i = i + 1) begin
                host(i, 32'h0, 1'b0, rd);
                if (rd !== mexp[c*D + i]) begin
                    mbad = mbad + 1;
                    if (mbad <= 4) $display("TBSTOREMEM call=%0d a[%0d]=%08x want %08x", c, i, rd, mexp[c*D + i]);
                end
            end
            $display("TBSTOREMEM call=%0d bad=%0d", c, mbad);
            if (mbad) fails = fails + 1;
        end
        $display("TBSTORE SUMMARY %s (%0d failure(s), %0d calls x %0d runs) at %0t ps", fails ? "FAIL" : "pass", fails, ncalls, nruns, $time);
        $finish;
    end
    initial begin #2000000000; $display("TBSTORE SUMMARY FAIL (timeout at %0t ps: a handshake never completed)", $time); $finish; end
endmodule
