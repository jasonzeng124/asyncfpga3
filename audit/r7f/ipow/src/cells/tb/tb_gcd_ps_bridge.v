`timescale 1ns / 1ps

// ---------------------------------------------------------------------------
// tb_gcd_ps_bridge -- drives hw/gcd_ps.v's gcd_ps_bridge with raw AXI3
// channel wiggles, the same way the real PS7's M_AXI_GP0 would.
//
// gcd_ps (the top module) instantiates a PS7 hard macro, which cannot be
// simulated -- that is exactly why gcd_ps_bridge is factored out as its own
// module (see the comment above it in hw/gcd_ps.v).  This bench instantiates
// gcd_ps_bridge directly.  hw/gcd_ps.v is `include`d unmodified so that this
// bench and the synthesised design can never drift; the PS7/BUFG stubs below
// exist only so that file elaborates (gcd_ps itself is never instantiated,
// and is not the simulation root -- see run_sim.sh's -s below).
//
// gcd_ps_bridge instantiates bdc_gcd with no probe ports connected (see
// hw/gcd_ps.v), so the plain kernel -- not the --probe build gcd_rig.v
// needs -- is what has to exist.
//
// requires: sim/ps7_stub.v
// requires: build/gen/gcd_kernel_bench.v
//
// AXI3 IDs are the one thing every call site in this file gets deliberately
// wrong on purpose to get right: hw-docs/07 records that tying BID/RID to
// zero hangs every CPU access on real silicon while a testbench that drives
// ID 0 stays green throughout.  So no AXI transaction anywhere in this file,
// not even the housekeeping ones, ever uses ID 0 -- and Section 3 below
// checks the echo explicitly with two different non-zero IDs.
// ---------------------------------------------------------------------------

// -- unsimulatable hard-macro stubs, so hw/gcd_ps.v elaborates --------------
// Only gcd_ps_bridge is instantiated as DUT below.  These stand in for the
// ports gcd_ps's PS7/BUFG instances use, in case the simulator tries to
// elaborate gcd_ps as an unreferenced root; they carry no behaviour.
// PS7 stub now lives in sim/ps7_stub.v, declared in this file's header.

// BUFG already has a simulation stand-in in sim/bd_prims_sim.v (zero-delay,
// deliberately -- see its header); only PS7 is missing one.

`include "hw/gcd_ps.v"

module tb_gcd_ps_bridge;

    // -- register map (byte addresses, from hw/gcd_ps.v's header) ----------
    localparam [31:0] CTRL_ADDR   = 32'h00;
    localparam [31:0] STATUS_ADDR = 32'h04;
    localparam [31:0] A_DATA_ADDR = 32'h08;
    localparam [31:0] B_DATA_ADDR = 32'h0C;
    localparam [31:0] O_DATA_ADDR = 32'h10;

    // A generous, but bounded, cap on AXI-read polling iterations.  Actual
    // kernel latencies are tens to hundreds of clock edges at worst on this
    // simulation model; this cap is 10-100x that, so a real timeout means
    // the result genuinely never showed up, not that the margin was tight.
    localparam integer POLL_MAX = 5000;

    // A default non-zero ID for housekeeping transactions that are not
    // themselves testing ID plumbing (Section 3 does that explicitly).
    localparam [11:0] ID_DEFAULT = 12'h3E7;

    // ------------------------------------------------------------------
    // clock / DUT
    // ------------------------------------------------------------------
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

    gcd_ps_bridge dut (
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

    // ------------------------------------------------------------------
    // AXI3 register-slave BFM tasks.
    //
    // Both tasks hold VALID asserted from before the address/data-phase
    // accept cycle through the cycle the response channel (bvalid/rvalid)
    // actually rises -- this bridge's aw_en/do_write and ar/rvalid logic
    // both re-sample awvalid/wvalid (write) or arvalid (read) on the SAME
    // cycle the registered *ready lines are seen high, so dropping valid
    // one cycle early would silently swallow the transaction (no register
    // write / no rvalid ever, but no protocol complaint either).  bready /
    // rready are then held one cycle past that so the response channel
    // actually clears, instead of latching high forever.
    // ------------------------------------------------------------------
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

    // Convenience wrappers for callers that don't care about the ID echo.
    task automatic wr(input [31:0] addr, input [31:0] data);
        reg [11:0] dummy_bid;
        begin
            axi_write(addr, data, ID_DEFAULT, dummy_bid);
        end
    endtask

    task automatic rd(input [31:0] addr, output [31:0] data);
        reg [11:0] dummy_rid;
        begin
            axi_read(addr, ID_DEFAULT, data, dummy_rid);
        end
    endtask

    task automatic check(input pass, input [1023:0] msg);
        begin
            if (pass) $display("  PASS  %0s", msg);
            else begin
                $display("  FAIL  %0s", msg);
                errors = errors + 1;
            end
        end
    endtask

    // ------------------------------------------------------------------
    // full 4-phase host sequence through the real kernel, with a bounded,
    // self-reporting timeout on every poll.
    // ------------------------------------------------------------------
    task automatic run_gcd(input [31:0] a, input [31:0] b,
                            input [31:0] want, input [1023:0] label,
                            input do_hold, input integer hold_cycles);
        reg [31:0] v;
        reg        ok;
        integer    i;
        begin
            wr(A_DATA_ADDR, a);
            wr(B_DATA_ADDR, b);
            wr(CTRL_ADDR, 32'h1);          // i_req = 1

            if (do_hold) begin
                // The pulse adapter's whole reason to exist: a host that
                // keeps i_req asserted long past the kernel's own i_ack
                // must not wedge the entry chain.  Hold for thousands of
                // cycles -- far past any real i_ack latency in this model
                // -- with CTRL.i_req still =1 the entire time.
                repeat (hold_cycles) @(posedge aclk);
            end

            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(STATUS_ADDR, v);
                if (v[0] === 1'b1) ok = 1'b1;
            end
            if (!ok) begin
                $display("  FAIL  %0s: poll STATUS.i_ack timed out after %0d reads",
                          label, POLL_MAX);
                errors = errors + 1;
                disable run_gcd;
            end

            wr(CTRL_ADDR, 32'h0);          // i_req = 0

            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(STATUS_ADDR, v);
                if (v[1] === 1'b1) ok = 1'b1;
            end
            if (!ok) begin
                $display("  FAIL  %0s: poll STATUS.o_req timed out after %0d reads",
                          label, POLL_MAX);
                errors = errors + 1;
                disable run_gcd;
            end

            rd(O_DATA_ADDR, v);
            check(v === want,
                  {label, ": O_DATA"});
            if (v !== want)
                $display("        got %0d (0x%0h)  want %0d (0x%0h)", v, v, want, want);

            wr(CTRL_ADDR, 32'h2);          // o_ack = 1

            ok = 1'b0;
            for (i = 0; i < POLL_MAX && !ok; i = i + 1) begin
                rd(STATUS_ADDR, v);
                if (v[1] === 1'b0) ok = 1'b1;
            end
            if (!ok) begin
                $display("  FAIL  %0s: poll STATUS.o_req-clear timed out after %0d reads",
                          label, POLL_MAX);
                errors = errors + 1;
            end

            wr(CTRL_ADDR, 32'h0);          // o_ack = 0
        end
    endtask

    // ------------------------------------------------------------------
    // stimulus
    // ------------------------------------------------------------------
    reg  [31:0] rv;
    reg  [11:0] rid_got, bid_got;

    initial begin
        awvalid = 0; wvalid = 0; bready = 0; arvalid = 0; rready = 0;
        awaddr = 0; wdata = 0; araddr = 0; awid = 0; arid = 0; wstrb = 4'hF;
        aresetn = 1'b0;

        // ================================================================
        // Section 1: AXI reset behaviour.  CTRL.rst powers up 1 (kernel
        // held in reset) -- check it on the cold power-up reset AND on a
        // later reassertion, so this is not just a t=0 initial-value fluke.
        // ================================================================
        $display("== Section 1: reset behaviour ==");
        repeat (10) @(posedge aclk);
        aresetn = 1'b1;
        repeat (5) @(posedge aclk);

        rd(CTRL_ADDR, rv);
        check(rv === 32'h4, "power-up reset: CTRL.rst is set (bit2)");

        // Reassert and release again, mid-simulation, with the bench
        // otherwise idle.  Same claim, a second time, on a different clock
        // edge than the very first one.
        aresetn = 1'b0;
        repeat (7) @(posedge aclk);
        aresetn = 1'b1;
        repeat (5) @(posedge aclk);

        rd(CTRL_ADDR, rv);
        check(rv === 32'h4, "post-reassert reset: CTRL.rst is set (bit2) again");

        // ================================================================
        // Section 2: register readback.  Release reset via a CTRL write
        // (also the CTRL echo check), then check A_DATA/B_DATA echo.
        // ================================================================
        $display("== Section 2: register readback ==");
        wr(CTRL_ADDR, 32'h0);              // rst=0, i_req=0, o_ack=0
        rd(CTRL_ADDR, rv);
        check(rv === 32'h0, "CTRL write/readback: 0x0 echoes as 0x0 (reset released)");

        wr(A_DATA_ADDR, 32'hDEADBEEF);
        rd(A_DATA_ADDR, rv);
        check(rv === 32'hDEADBEEF, "A_DATA write/readback echo");

        wr(B_DATA_ADDR, 32'hCAFEBABE);
        rd(B_DATA_ADDR, rv);
        check(rv === 32'hCAFEBABE, "B_DATA write/readback echo");

        // ================================================================
        // Section 3: AXI ID plumbing.  BID must echo the write's AWID and
        // RID must echo the read's ARID -- non-zero, and at TWO different
        // values, so a constant (e.g. always-0) echo cannot pass silently.
        // ================================================================
        $display("== Section 3: AXI ID echo (BID/RID) ==");
        axi_write(A_DATA_ADDR, 32'h11111111, 12'hA5C, bid_got);
        check(bid_got === 12'hA5C, "BID echoes AWID=0xA5C on a write");

        axi_write(B_DATA_ADDR, 32'h22222222, 12'h37F, bid_got);
        check(bid_got === 12'h37F, "BID echoes AWID=0x37F on a different write");

        axi_read(A_DATA_ADDR, 12'hA5C, rv, rid_got);
        check(rid_got === 12'hA5C, "RID echoes ARID=0xA5C on a read");

        axi_read(B_DATA_ADDR, 12'h37F, rv, rid_got);
        check(rid_got === 12'h37F, "RID echoes ARID=0x37F on a different read");

        // ================================================================
        // Section 4: full 4-phase transactions through the real kernel.
        // ================================================================
        $display("== Section 4: end-to-end gcd through the real kernel ==");
        run_gcd(32'd12, 32'd18, 32'd6,  "gcd(12,18)=6",  1'b0, 0);
        run_gcd(32'd48, 32'd18, 32'd6,  "gcd(48,18)=6",  1'b0, 0);
        run_gcd(32'd0,  32'd5,  32'd5,  "gcd(0,5)=5",    1'b0, 0);
        run_gcd(32'd7,  32'd0,  32'd7,  "gcd(7,0)=7",    1'b0, 0);
        run_gcd(32'd17, 32'd5,  32'd1,  "gcd(17,5)=1",   1'b0, 0);
        run_gcd(32'd1,  32'd1,  32'd1,  "gcd(1,1)=1",    1'b0, 0);

        // ================================================================
        // Section 5: the pulse adapter.  Hold CTRL.i_req asserted for
        // thousands of cycles, well past the kernel's own i_ack, then
        // finish the transaction normally, then prove a SECOND transaction
        // still completes -- i.e. the long hold did not wedge the kernel.
        // ================================================================
        $display("== Section 5: pulse adapter survives a long-held i_req ==");
        run_gcd(32'd100, 32'd75, 32'd25, "gcd(100,75)=25 (i_req held 3000 cycles)",
                1'b1, 3000);
        run_gcd(32'd21,  32'd14, 32'd7,  "gcd(21,14)=7 (second transaction after the hold)",
                1'b0, 0);

        if (errors == 0) $display("tb_gcd_ps_bridge PASS");
        else             $display("tb_gcd_ps_bridge FAIL (%0d failures)", errors);
        $finish;
    end

    // A bench that hangs tells you nothing about which check hung.  Every
    // poll above is itself bounded by POLL_MAX; this is the outer backstop
    // in case a wait() elsewhere never resolves.
    initial begin
        #2_000_000;   // 2 ms
        $display("tb_gcd_ps_bridge FAIL (testbench timeout)");
        $finish;
    end

endmodule
