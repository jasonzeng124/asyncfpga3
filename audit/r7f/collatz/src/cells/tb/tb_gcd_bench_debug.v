`timescale 1ns / 1ps
// Throwaway diagnostic for the Section-5 UNIFORM-mode stall found by
// tb_gcd_bench_gen.v: peeks internal FSM/operand state every cycle so we can
// see exactly where it wedges and on what operand pair, instead of guessing
// from the outside through AXI polls alone.
//
// DUT is gcd_bench_gen_bridge, not gcd_bench_bridge -- see tb_gcd_bench_gen.v
// for why gcd alone gets the "_gen" suffix from build_bench.sh's --top.
//

// requires: sim/ps7_stub.v
// requires: build/gen/gcd_bench_gen.v
// requires: build/gen/gcd_kernel_bench.v

`include "build/gen/gcd_bench_gen.v"

module tb_gcd_bench_debug;
    localparam [31:0] CTRL=32'h00, OP0=32'h08, OP1=32'h0C, NRUNS=32'h14, BCTRL=32'h20, BSTATUS=32'h24;

    reg aclk = 1'b0;
    always #5 aclk = ~aclk;

    reg aresetn;
    reg awvalid, wvalid, bready, arvalid, rready;
    reg [31:0] awaddr, wdata, araddr;
    reg [11:0] awid, arid;
    reg [3:0] wstrb;
    wire awready, wready, bvalid, arready, rvalid;
    wire [1:0] bresp, rresp;
    wire [11:0] bid, rid;
    wire [31:0] rdata;
    wire core_i_ack, core_o_req;

    gcd_bench_gen_bridge dut (
        .aclk(aclk), .aresetn(aresetn),
        .awvalid(awvalid), .awready(awready), .awaddr(awaddr), .awid(awid),
        .wvalid(wvalid), .wready(wready), .wdata(wdata), .wstrb(wstrb),
        .bvalid(bvalid), .bready(bready), .bresp(bresp), .bid(bid),
        .arvalid(arvalid), .arready(arready), .araddr(araddr), .arid(arid),
        .rvalid(rvalid), .rready(rready), .rdata(rdata), .rresp(rresp), .rid(rid),
        .core_i_ack(core_i_ack), .core_o_req(core_o_req)
    );

    task automatic wr(input [31:0] addr, input [31:0] data);
        begin
            @(posedge aclk); #1;
            awaddr=addr; awid=12'h1; wdata=data; wstrb=4'hF;
            awvalid=1'b1; wvalid=1'b1; bready=1'b1;
            wait(bvalid===1'b1); #1;
            awvalid=1'b0; wvalid=1'b0;
            @(posedge aclk); #1; bready=1'b0;
        end
    endtask

    integer t;
    reg [2:0] st_prev;
    initial begin
        awvalid=0; wvalid=0; bready=0; arvalid=0; rready=0;
        awaddr=0; wdata=0; araddr=0; awid=0; arid=0; wstrb=4'hF;
        aresetn=1'b0;
        repeat (10) @(posedge aclk);
        aresetn=1'b1;
        repeat (5) @(posedge aclk);
        wr(CTRL, 32'h0);

        wr(OP0, 32'hACE1_2345);
        wr(NRUNS, 32'd20);
        wr(BCTRL, {28'b0, 2'b00, 1'b0, 1'b1});  // UNIFORM, start

        st_prev = 3'bxxx;
        for (t = 0; t < 200000; t = t + 1) begin
            @(posedge aclk);
            if (dut.st !== st_prev) begin
                $display("t=%0t st=%0d runs_done=%0d bench_op0=%h bench_op1=%h lat_ctr=%0d i_req=%b i_ack=%b o_req=%b lfsr=%h",
                          $time, dut.st, dut.runs_done, dut.bench_op0, dut.bench_op1,
                          dut.lat_ctr, dut.i_req_pl, dut.i_ack_pl, dut.o_req_pl, dut.lfsr);
                st_prev = dut.st;
            end
            if (dut.bench_done) begin
                $display("DONE at t=%0t, runs_done=%0d", $time, dut.runs_done);
                // This rig is a state TRACE, not an oracle -- it does not check
                // gcd's answers, and the trace above is the point of it.  But it
                // does distinguish completion from a stall, which is the failure
                // this bench was written to catch, so it reports that verdict
                // rather than leaving the gate to guess from a "DONE" line.
                if (dut.runs_done == 20) $display("tb_gcd_bench_debug PASS");
                else                     $display("tb_gcd_bench_debug FAIL -- finished with runs_done=%0d, expected 20", dut.runs_done);
                $finish;
            end
        end
        $display("STALLED: never finished 20 runs. Final: st=%0d runs_done=%0d bench_op0=%h bench_op1=%h",
                  dut.st, dut.runs_done, dut.bench_op0, dut.bench_op1);
        $display("tb_gcd_bench_debug FAIL -- stalled");
        $finish;
    end
endmodule
