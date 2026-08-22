`timescale 1ns / 1ps

// ---------------------------------------------------------------------------
// tb_gcd_bench_gen -- drives the GENERATED gcd_bench_gen_bridge (cells/hw/gen_bench.py
// output, build/gen/gcd_bench_gen.v) with raw AXI3 channel wiggles, the same
// way tb_gcd_ps_bridge.v drives hw/gcd_ps.v's bridge.  See that file for why
// PS7/BUFG never need to be simulated: this bench targets ...bench_bridge
// directly, which is never a PS7-instantiating module, so no PS7 stub is
// needed at all (unlike tb_gcd_ps_bridge.v, which includes the PS7-bearing
// top and so needs one).
//
// This is item 1 of the harness's validation order ("simulate first") and
// half of item 2 ("validate on hardware against gcd at SMALL N... your
// harness must agree") -- the small-N agreement check itself happens here in
// sim against a hand-computed oracle, before ever touching the board.
//
// The DUT module name below is gcd_bench_gen_bridge, not gcd_bench_bridge:
// build_bench.sh (see its own header) generates gcd with --top gcd_bench_gen
// specifically, to avoid colliding with hw/gcd_bench.v's own build/hw/gcd_bench/
// output directory -- a collision that would otherwise silently overwrite
// that hand-written harness's bitstream. Every OTHER kernel keeps the
// generator's default top name (see tb_smoke_*_gen.v), so this "_gen" suffix
// is a gcd-only wrinkle, not a general convention.
//
//
// Run (after `python3 cells/hw/gen_bench.py gcd --top gcd_bench_gen -o build/gen/gcd_bench_gen.v`
// and generating build/gen/gcd_kernel_bench.v -- see cells/hw/build_bench.sh):
//   iverilog -g2012 -gspecify -Wall -Wno-timescale -o build/sim/tb_gcd_bench_gen.vvp \
//     cells/sim/bd_prims_sim.v cells/sim/bd_env.v cells/rtl/*.v \
//     build/gen/gcd_kernel_bench.v build/gen/gcd_bench_gen.v cells/tb/tb_gcd_bench_gen.v
//   vvp build/sim/tb_gcd_bench_gen.vvp
// ---------------------------------------------------------------------------


// requires: sim/ps7_stub.v
// requires: build/gen/gcd_bench_gen.v
// requires: build/gen/gcd_kernel_bench.v

`include "build/gen/gcd_bench_gen.v"

module tb_gcd_bench_gen;

    // -- register map (byte addresses; word offset * 4 -- see gen_bench.py) -
    localparam [31:0] CTRL      = 32'h00;
    localparam [31:0] STATUS    = 32'h04;
    localparam [31:0] OP0       = 32'h08;
    localparam [31:0] OP1       = 32'h0C;
    localparam [31:0] ODATA     = 32'h10;
    localparam [31:0] NRUNS     = 32'h14;
    localparam [31:0] CYCLES    = 32'h18;
    localparam [31:0] PREPCYC   = 32'h1C;
    localparam [31:0] BCTRL     = 32'h20;
    localparam [31:0] BSTATUS   = 32'h24;
    localparam [31:0] LATMIN    = 32'h28;
    localparam [31:0] LATMAX    = 32'h2C;
    localparam [31:0] LASTOP0   = 32'h30;
    localparam [31:0] LASTOP1   = 32'h34;
    localparam [31:0] SIG       = 32'h38;
    localparam [31:0] MISM_ST   = 32'h3C;
    localparam [31:0] MISM_IDX  = 32'h40;
    localparam [31:0] MISM_VAL  = 32'h44;
    localparam [31:0] MISM_REF  = 32'h48;
    localparam [31:0] HIST_BASE = 32'h100;

    localparam integer POLL_MAX = 20000;
    localparam [11:0]  ID_DEFAULT = 12'h3E7;

    reg aclk = 1'b0;
    always #5 aclk = ~aclk;   // 100 MHz

    reg         aresetn;
    reg         awvalid, wvalid, bready, arvalid, rready;
    reg  [31:0] awaddr, wdata, araddr;
    reg  [11:0] awid, arid;
    reg  [3:0]  wstrb;
    wire        awready, wready, bvalid, arready, rvalid;
    wire [1:0]  bresp, rresp;
    wire [11:0] bid, rid;
    wire [31:0] rdata;
    wire        core_i_ack, core_o_req;

    gcd_bench_gen_bridge dut (
        .aclk (aclk), .aresetn (aresetn),
        .awvalid (awvalid), .awready (awready), .awaddr (awaddr), .awid (awid),
        .wvalid  (wvalid),  .wready  (wready),  .wdata  (wdata),  .wstrb (wstrb),
        .bvalid  (bvalid),  .bready  (bready),  .bresp  (bresp),  .bid   (bid),
        .arvalid (arvalid), .arready (arready), .araddr (araddr), .arid  (arid),
        .rvalid  (rvalid),  .rready  (rready),  .rdata  (rdata),
        .rresp   (rresp),   .rid     (rid),
        .core_i_ack (core_i_ack), .core_o_req (core_o_req)
    );

    integer errors = 0;

    task automatic axi_write(input [31:0] addr, input [31:0] data,
                              input [11:0] id, output [11:0] got_bid);
        begin
            @(posedge aclk); #1;
            awaddr = addr; awid = id; wdata = data; wstrb = 4'hF;
            awvalid = 1'b1; wvalid = 1'b1; bready = 1'b1;
            wait (bvalid === 1'b1);
            #1;
            got_bid = bid;
            awvalid = 1'b0; wvalid = 1'b0;
            @(posedge aclk); #1;
            bready = 1'b0;
        end
    endtask

    task automatic axi_read(input [31:0] addr, input [11:0] id,
                             output [31:0] got_data, output [11:0] got_rid);
        begin
            @(posedge aclk); #1;
            araddr = addr; arid = id;
            arvalid = 1'b1; rready = 1'b1;
            wait (rvalid === 1'b1);
            #1;
            got_data = rdata; got_rid = rid;
            arvalid = 1'b0;
            @(posedge aclk); #1;
            rready = 1'b0;
        end
    endtask

    task automatic wr(input [31:0] addr, input [31:0] data);
        reg [11:0] dummy_bid;
        begin axi_write(addr, data, ID_DEFAULT, dummy_bid); end
    endtask

    task automatic rd(input [31:0] addr, output [31:0] data);
        reg [11:0] dummy_rid;
        begin axi_read(addr, ID_DEFAULT, data, dummy_rid); end
    endtask

    task automatic check(input pass, input [1023:0] msg);
        begin
            if (pass) $display("  PASS  %0s", msg);
            else begin $display("  FAIL  %0s", msg); errors = errors + 1; end
        end
    endtask

    // rotate-left-1-then-XOR signature, matching gen_bench.py's hardware
    // update `sig <= {sig[30:0], sig[31]} ^ o_data_capture;` bit for bit --
    // this is literally "the host recomputes the expected signature in
    // software" from the spec, just done in the testbench instead of Python
    // so the sim gate can check it without leaving the simulator.
    function automatic [31:0] sig_step(input [31:0] s, input [31:0] v);
        begin
            sig_step = {s[30:0], s[31]} ^ v;
        end
    endfunction

    // ------------------------------------------------------------------
    // manual single-shot 4-phase path (same protocol as gcd_ps_bridge,
    // OP0/OP1 instead of A_DATA/B_DATA) -- proves the generalised register
    // map still drives the real bdc_gcd kernel correctly outside a batch.
    // ------------------------------------------------------------------
    task automatic run_manual(input [31:0] a, input [31:0] b,
                               input [31:0] want, input [1023:0] label);
        reg [31:0] v;
        reg        ok;
        integer    i;
        begin
            wr(OP0, a);
            wr(OP1, b);
            wr(CTRL, 32'h1);
            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(STATUS, v); if (v[0] === 1'b1) ok = 1'b1;
            end
            check(ok, {label, ": i_ack seen"});
            wr(CTRL, 32'h0);
            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(STATUS, v); if (v[1] === 1'b1) ok = 1'b1;
            end
            check(ok, {label, ": o_req seen"});
            rd(ODATA, v);
            check(v === want, {label, ": O_DATA correct"});
            if (v !== want) $display("        got %0d want %0d", v, want);
            wr(CTRL, 32'h2);
            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(STATUS, v); if (v[1] === 1'b0) ok = 1'b1;
            end
            check(ok, {label, ": o_req cleared"});
            wr(CTRL, 32'h0);
        end
    endtask

    task automatic poll_done(output [31:0] bstatus, input [1023:0] label);
        integer i;
        reg ok;
        begin
            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(BSTATUS, bstatus); if (bstatus[1] === 1'b1) ok = 1'b1;
            end
            check(ok, {label, ": BSTATUS.done seen"});
        end
    endtask

    reg  [31:0] rv, rv2, bstat;
    reg  [11:0] rid_got, bid_got;
    integer     h, hist_total;
    reg  [31:0] hist [0:63];

    initial begin
        awvalid=0; wvalid=0; bready=0; arvalid=0; rready=0;
        awaddr=0; wdata=0; araddr=0; awid=0; arid=0; wstrb=4'hF;
        aresetn = 1'b0;

        // ================================================================
        $display("== Section 1: reset + register readback ==");
        repeat (10) @(posedge aclk);
        aresetn = 1'b1;
        repeat (5) @(posedge aclk);
        rd(CTRL, rv);
        check(rv === 32'h4, "power-up reset: CTRL.rst set");
        wr(CTRL, 32'h0);
        rd(CTRL, rv);
        check(rv === 32'h0, "CTRL readback after release");

        wr(OP0, 32'hDEADBEEF); rd(OP0, rv);
        check(rv === 32'hDEADBEEF, "OP0 write/readback echo");
        wr(OP1, 32'hCAFEBABE); rd(OP1, rv);
        check(rv === 32'hCAFEBABE, "OP1 write/readback echo");

        // ================================================================
        $display("== Section 2: manual path through the real bdc_gcd ==");
        run_manual(32'd12, 32'd18, 32'd6, "gcd(12,18)=6");
        run_manual(32'd48, 32'd18, 32'd6, "gcd(48,18)=6");
        run_manual(32'd0,  32'd5,  32'd5, "gcd(0,5)=5");

        // ================================================================
        // Section 3: FIXED-mode batch.  Every run reruns OP0/OP1=48/18
        // (gcd=6) verbatim, so this checks: LAT_MIN==LAT_MAX (identical
        // inputs -> identical latency, the noise-floor claim from
        // hw/gcd_bench.v's header), PREP_CYCLES == 16*N_RUNS exactly (the
        // CYCLES-excludes-S_PREP fix), SIG matches the same rotate-XOR
        // recurrence computed here bit for bit, and MISMATCH stays clear
        // (a correct deterministic circuit run on identical inputs must
        // return the identical result every time).
        // ================================================================
        $display("== Section 3: FIXED-mode batch, repeatability + SIG + CYCLES ==");
        wr(OP0, 32'd48); wr(OP1, 32'd18);
        wr(NRUNS, 32'd6);
        wr(BCTRL, {28'b0, 2'b01, 1'b0, 1'b1});   // mode=1 (FIXED), start=1
        poll_done(bstat, "FIXED batch");
        check(bstat[31:16] === 16'd6, "FIXED batch: 6 runs completed");

        rd(ODATA, rv);
        check(rv === 32'd6, "FIXED batch: O_DATA == gcd(48,18) == 6");

        rd(LATMIN, rv); rd(LATMAX, rv2);
        check(rv === rv2, "FIXED batch: LAT_MIN == LAT_MAX (deterministic repeat)");
        if (rv !== rv2) $display("        LAT_MIN=%0d LAT_MAX=%0d", rv, rv2);

        rd(PREPCYC, rv);
        check(rv === 32'd96, "FIXED batch: PREP_CYCLES == 16*6 == 96 exactly");
        if (rv !== 32'd96) $display("        PREP_CYCLES=%0d", rv);

        rd(CYCLES, rv);
        check(rv > 32'd0, "FIXED batch: CYCLES nonzero");

        rd(MISM_ST, rv);
        check(rv[0] === 1'b0, "FIXED batch: no repeatability mismatch on identical inputs");

        rd(SIG, rv);
        begin : sig_check
            reg [31:0] want_sig;
            integer k;
            want_sig = 32'b0;
            for (k = 0; k < 6; k = k + 1) want_sig = sig_step(want_sig, 32'd6);
            check(rv === want_sig, "FIXED batch: SIG matches rotate-XOR(6,6) computed here");
            if (rv !== want_sig) $display("        SIG=%0h want=%0h", rv, want_sig);
        end

        wr(BCTRL, 32'h0);

        // ================================================================
        // Section 4: deliberate CRC/repeatability-mismatch exercise
        // ("corrupt a seed", per the harness's validation order item 4).
        // Start a FIXED batch on gcd(48,18)=6, let the first run complete
        // to establish the reference, then -- WHILE busy, exactly the
        // "host misbehaving" case the register map's own comment warns
        // against -- rewrite OP1 to 17 so gcd(48,17)=1.  FIXED mode
        // re-samples OP0/OP1 fresh every run, so run 1 onward see 17 and
        // legitimately diverge: this must set MISMATCH_STICKY with
        // MISMATCH_VAL==1, proving a real green run on Section 3 was not
        // just a comparator that never fires.  MISMATCH_IDX itself is only
        // checked to be >=1, not ==1: AXI polling (several clock cycles per
        // read) is slow next to the FSM, so run 1's own S_PREP sample point
        // can come and go before this testbench's corrupting write lands --
        // a real scheduling race in the TEST, not in the DUT, and pinning
        // an exact index would make the check flaky rather than meaningful.
        // ================================================================
        $display("== Section 4: deliberate corruption -- prove the mismatch path fires ==");
        wr(OP0, 32'd48); wr(OP1, 32'd18);
        wr(NRUNS, 32'd6);
        wr(BCTRL, {28'b0, 2'b01, 1'b0, 1'b1});   // mode=1 (FIXED), start=1

        // Wait for run 0 to retire (runs_done becomes 1) before corrupting,
        // so the reference is unambiguously gcd(48,18)=6.
        begin : wait_run0
            integer i;
            reg [31:0] bs;
            bs = 32'b0;
            for (i = 0; i < POLL_MAX && bs[31:16] < 16'd1; i = i + 1) rd(BSTATUS, bs);
            check(bs[31:16] >= 16'd1, "corruption test: run 0 retired before corrupting OP1");
        end
        wr(OP1, 32'd17);   // the deliberate corruption

        poll_done(bstat, "corruption test batch");
        rd(MISM_ST, rv);
        check(rv[0] === 1'b1, "corruption test: MISMATCH_STICKY set");
        rd(MISM_IDX, rv);
        check(rv >= 32'd1, "corruption test: MISMATCH_IDX >= 1 (not the reference run itself)");
        $display("        MISMATCH_IDX=%0d", rv);
        rd(MISM_VAL, rv);
        check(rv === 32'd1, "corruption test: MISMATCH_VAL == gcd(48,17) == 1");
        if (rv !== 32'd1) $display("        MISMATCH_VAL=%0d", rv);
        rd(MISM_REF, rv);
        check(rv === 32'd6, "corruption test: MISMATCH_REF == gcd(48,18) == 6 (run-0 reference)");

        wr(BCTRL, 32'h0);

        // ================================================================
        // Section 5: UNIFORM-mode batch -- must not hang (the domain-mask
        // fix), and the 64-bucket histogram must conservatively sum to the
        // run count no matter what latencies land in it.
        // ================================================================
        $display("== Section 5: UNIFORM-mode batch, histogram conservation ==");
        wr(OP0, 32'hACE1_2345);   // nonzero LFSR seed
        wr(NRUNS, 32'd64);
        wr(BCTRL, {28'b0, 2'b00, 1'b0, 1'b1});   // mode=0 (UNIFORM), start=1
        poll_done(bstat, "UNIFORM batch");
        check(bstat[31:16] === 16'd64, "UNIFORM batch: 64 runs completed (did not hang)");

        rd(LATMIN, rv); rd(LATMAX, rv2);
        check(rv <= rv2, "UNIFORM batch: LAT_MIN <= LAT_MAX");
        $display("        LAT_MIN=%0d LAT_MAX=%0d cycles", rv, rv2);

        hist_total = 0;
        for (h = 0; h < 64; h = h + 1) begin
            rd(HIST_BASE + h * 4, hist[h]);
            hist_total = hist_total + hist[h];
        end
        check(hist_total === 64, "UNIFORM batch: sum of 64 histogram buckets == run count");
        if (hist_total !== 64) $display("        hist_total=%0d", hist_total);

        wr(BCTRL, 32'h0);

        if (errors == 0) $display("tb_gcd_bench_gen PASS");
        else             $display("tb_gcd_bench_gen FAIL (%0d failures)", errors);
        $finish;
    end

    initial begin
        #4_000_000;   // 4 ms
        $display("tb_gcd_bench_gen FAIL (testbench timeout)");
        $finish;
    end

endmodule
