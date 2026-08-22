`timescale 1ns / 1ps

// ---------------------------------------------------------------------------
// tb_smoke_isprime_gen -- generic no-oracle UNIFORM-mode smoke test for the
// generated real-kernel bench bridge (hw/gen_bench.py). Confirms the
// async-clearing pulse adapter (i_ack_latched/o_req_latched) generalizes
// beyond gcd: runs a full batch to completion (no hang), and checks the
// histogram accounts for every run. This is a regression check, not a
// correctness oracle -- see tb_gcd_bench_gen.v for the kernel that DOES get
// a hand-checked oracle.
// ---------------------------------------------------------------------------


// requires: sim/ps7_stub.v
// requires: build/gen/isprime_bench_gen.v
// requires: build/gen/isprime_kernel_bench.v

`include "build/gen/isprime_bench_gen.v"

// Heartbeat interval in cycles; -DSMOKE_HB=1000 to watch a slow kernel.
// How many runs this SMOKE test drives.  It is deliberately NOT 80.
//
// What this bench exists to prove is structural: the async-clearing pulse
// adapter generalises past gcd, a batch reaches completion without stalling,
// and the histogram accounts for every run.  Eight runs establishes all three.
//
// Eighty does not, in any useful sense, establish more of them -- but it costs
// far more.  iverilog carries this design at roughly 20 simulated cycles per
// wall SECOND (the generated bench's `@*` over a 64-word histogram array is
// most of it), and a collatz trajectory is several hundred cycles per run, so
// eighty runs is around half an hour of wall clock for a gate that is supposed
// to be cheap.  That is why these five benches had never once been seen to
// finish.
//
// The VOLUME belongs on hardware, where it is nearly free and where the
// latency distribution is the actual deliverable -- see hw/gen_bench.py and
// the bench bitstreams.  Raise it here with -DSMOKE_RUNS=80 when you
// specifically want the long sim; expect it to take that half hour.
`ifndef SMOKE_RUNS
  `define SMOKE_RUNS 8
`endif

`ifndef SMOKE_HB
  `define SMOKE_HB 100_000
`endif

module tb_smoke_isprime_gen;
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

    isprime_bench_gen_bridge dut (
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
        wr(OP0, 32'h0000_002A);
        wr(OP1, 32'h0000_0007);
        wr(NRUNS, 32'd`SMOKE_RUNS);
        wr(BCTRL, {28'b0, 2'b00, 1'b0, 1'b1});  // UNIFORM
        bstatus = 0;
        // Heartbeat.  Without it, a bench that is merely SLOW and a bench that
        // is genuinely stuck look identical from outside: both print nothing
        // for as long as you are willing to wait, and the 2,000,000-cycle
        // watchdog below is itself far enough away that it is not reachable in
        // a sane wall-clock budget for the longer kernels.  runs_done moving is
        // the difference between the two, so say it out loud.
        for (t = 0; t < 2_000_000; t = t + 1) begin
            @(posedge aclk);
            if (t % `SMOKE_HB == 0 && t != 0)
                $display("%s heartbeat: cycle=%0d st=%0d runs_done=%0d",
                         "tb_smoke_isprime_gen", t, dut.st, dut.runs_done);
            if (dut.bench_done) begin bstatus = 1; t = 2_000_000; end
        end
        if (!bstatus) begin
            $display("isprime smoke STALL: st=%0d runs_done=%0d", dut.st, dut.runs_done);
            $display("tb_smoke_isprime_gen FAIL"); $finish;
        end
        rd(LATMIN, latmin); rd(LATMAX, latmax);
        hsum = 0;
        for (hi = 0; hi < 64; hi = hi + 1) hsum = hsum + dut.hist[hi];
        $display("isprime smoke done: runs_done=%0d lat_min=%0d lat_max=%0d hist_sum=%0d",
                  dut.runs_done, latmin, latmax, hsum);
        if (dut.runs_done === 32'd`SMOKE_RUNS && hsum === 32'd`SMOKE_RUNS && latmin <= latmax)
            $display("tb_smoke_isprime_gen PASS");
        else
            $display("tb_smoke_isprime_gen FAIL");
        $finish;
    end
endmodule
