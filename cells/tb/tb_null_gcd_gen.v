`timescale 1ns / 1ps

// ---------------------------------------------------------------------------
// tb_null_gcd_gen -- exercises the generated null-kernel control for gcd
// (hw/gen_bench.py --null), confirming the async-clearing pulse adapter
// (i_ack_latched/o_req_latched in the shared bridge FSM) resolves the
// deterministic S_WAIT_ACK hang WITHOUT padding the null kernel's own
// delay chain (bd_delay N=6/N=10, minimal -- see gen_bench.py's null-kernel
// comment). This reproduces the exact hang scenario diagnosed earlier
// (req_core's async-clear round trip completing entirely between two
// clock edges) with the fix now on the poller side instead.
//
// Run (after `python3 hw/gen_bench.py gcd --null --top gcd_null_bench_gen
// -o build/gen/gcd_null_bench_gen.v`, from cells/):
//   iverilog -g2012 -gspecify -Wall -Wno-timescale -s tb_null_gcd_gen \
//     -o build/sim/tb_null_gcd_gen.vvp \
//     sim/bd_prims_sim.v sim/bd_env.v rtl/*.v tb/tb_null_gcd_gen.v
//   vvp build/sim/tb_null_gcd_gen.vvp
// ---------------------------------------------------------------------------

`include "build/gen/gcd_null_bench_gen.v"

module tb_null_gcd_gen;
    localparam [31:0] CTRL=32'h00, OP0=32'h08, OP1=32'h0C, NRUNS=32'h14;
    localparam [31:0] BCTRL=32'h20, BSTATUS=32'h24, LATMIN=32'h28, LATMAX=32'h2C;

    reg aclk = 1'b0;
    always #5 aclk = ~aclk;   // 100 MHz

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

    gcd_null_bench_gen_bridge dut (
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
    task automatic rd(input [31:0] addr, output [31:0] data);
        begin
            @(posedge aclk); #1;
            araddr=addr; arid=12'h2; arvalid=1'b1; rready=1'b1;
            wait(rvalid===1'b1); #1;
            data=rdata;
            arvalid=1'b0;
            @(posedge aclk); #1; rready=1'b0;
        end
    endtask

    integer t, hi;
    reg [31:0] bstatus, latmin, latmax, hsum;
    initial begin
        awvalid=0; wvalid=0; bready=0; arvalid=0; rready=0;
        awaddr=0; wdata=0; araddr=0; awid=0; arid=0; wstrb=4'hF;
        aresetn=1'b0;
        repeat (10) @(posedge aclk);
        aresetn=1'b1;
        repeat (5) @(posedge aclk);
        wr(CTRL, 32'h0);
        wr(OP0, 32'hACE1_2345);
        wr(OP1, 32'h1234_5678);
        wr(NRUNS, 32'd50);
        wr(BCTRL, {28'b0, 2'b00, 1'b0, 1'b1});  // UNIFORM
        bstatus = 0;
        for (t = 0; t < 200_000; t = t + 1) begin
            @(posedge aclk);
            if (dut.bench_done) begin bstatus = 1; t = 200_000; end
        end
        if (!bstatus) begin
            $display("null STALL: st=%0d runs_done=%0d", dut.st, dut.runs_done);
            $display("null FAIL"); $finish;
        end
        rd(LATMIN, latmin); rd(LATMAX, latmax);
        hsum = 0;
        for (hi = 0; hi < 64; hi = hi + 1) hsum = hsum + dut.hist[hi];
        $display("null done: runs_done=%0d lat_min=%0d lat_max=%0d hist_sum=%0d",
                  dut.runs_done, latmin, latmax, hsum);
        if (dut.runs_done === 32'd50 && hsum === 32'd50)
            $display("null PASS");
        else
            $display("null FAIL");
        $finish;
    end
endmodule
