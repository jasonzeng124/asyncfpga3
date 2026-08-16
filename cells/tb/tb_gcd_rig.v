`timescale 1ps / 1ps

// ---------------------------------------------------------------------------
// tb_gcd_rig -- does hw/gcd_rig.v's environment actually run the kernel?
//
// The rig's whole hardware result is "err stayed at zero", and a rig that
// never ran produces exactly that.  Before spending a build and a board on it,
// this bench checks the four things that make its zeros mean something:
//
//   1. the ring turns at all -- one token, injected by reset into the env
//      node, is enough to keep asking for gcds forever with no oscillator;
//   2. it turns for EVERY vector, across the restart that changes the vector;
//   3. ok fires and err does not, on right answers;
//   4. err fires on a wrong one -- because a detector that cannot set is
//      indistinguishable in readback from a design that never misbehaved.
//
// The kernel itself is not what is in question here: bdc/simcheck.py's
// tb_simcheck_gcd already drives the real bdc_gcd through these same vectors.
// What is new and unproven is the RING -- so the module under test is
// hw/gcd_rig.v itself, `include'd rather than retyped, and the kernel is
// replaced by a stub with the same ports.
//
// The stub is built out of frozen cells (join -> matched delay -> two-stage
// pipe -> fork), not out of behavioural handshaking, for two reasons.  A
// hand-written four-phase model is the easiest place in a bench like this to
// put a bug that the real cells do not have.  And the stub's storage count is
// load-bearing: the env node is one stage, so a one-stage stub would close a
// TWO-stage ring, which tb_ring measures to be dead.  Two stages in the stub
// is the floor, and it is the same floor bdc/emit.py enforces on the kernel.
// ---------------------------------------------------------------------------

`include "hw/gcd_rig.v"

// -- the kernel's stand-in ---------------------------------------------------
module bdc_gcd (
    input  wire        rst,
    input  wire        a_req,     output wire        a_ack,  input wire [31:0] a_data,
    input  wire        b_req,     output wire        b_ack,  input wire [31:0] b_data,
    input  wire        start_req, output wire        start_ack,
    output wire        out0_req,  input  wire        out0_ack, output wire [31:0] out0_data,
    output wire        p_end_req, input  wire        p_end_ack);

    // Stein's algorithm, transcribed from dynamatic/integration-test/gcd/gcd.c
    // exactly as bdc/simcheck.py's ref_gcd is.  Signed, because in_int_t is.
    function [31:0] gcd_ref(input [31:0] ua, input [31:0] ub);
        integer a, b, diff, k;
        begin
            a = ua; b = ub;
            if (a == 0)      gcd_ref = ub;
            else if (b == 0) gcd_ref = ua;
            else begin
                k = 0;
                while (((a | b) & 1) == 0) begin a = a >>> 1; b = b >>> 1; k = k + 1; end
                while (a > 0 && (a & 1) == 0) a = a >>> 1;
                while (b > 0 && (b & 1) == 0) b = b >>> 1;
                while (a != 0) begin
                    diff = a - b;
                    if (a < b) b = a;
                    a = (diff >= 0) ? diff : -diff;
                    while (a > 0 && (a & 1) == 0) a = a >>> 1;
                end
                gcd_ref = b << k;
            end
        end
    endfunction

    // A kernel that can be made wrong in the cheapest possible way: one bit,
    // on one vector.  Only vector 6 -- gcd.c's own main() pair -- is
    // corrupted, so the second pass also checks that the per-vector sticky
    // names the RIGHT vector rather than merely going off somewhere.
    //
    // The switch is reached by hierarchical name because the stub's port list
    // has to stay exactly the real kernel's: gcd_rig.v instantiates bdc_gcd by
    // name, and an extra port it does not connect would read as z, not 0.
    wire [31:0] g = gcd_ref(a_data, b_data)
                  ^ ((tb_gcd_rig.inject && a_data == 32'h00798F20) ? 32'h1 : 32'h0);

    // join the three input channels, pay a matched delay for the compute,
    // then two storage stages, then fork to the two result channels.
    wire ireq, iack, dreq, oreq, oack;
    wire [2:0] iacks;
    bd_join #(.N(3)) uin (
        .rst(rst), .req_in({start_req, b_req, a_req}), .ack_out(iacks),
        .req(ireq), .ack(iack));
    assign {start_ack, b_ack, a_ack} = iacks;

    bd_delay #(.N(8)) ucomp (.a(ireq), .z(dreq));

    bd_pipe #(.W(32), .N(2)) upipe (
        .rst(rst), .req_in(dreq), .ack_in(iack), .data_in(g),
        .req_out(oreq), .ack_out(oack), .data_out(out0_data));

    bd_fork #(.N(2)) uout (
        .rst(rst), .req(oreq), .ack(oack),
        .req_out({p_end_req, out0_req}), .ack_in({p_end_ack, out0_ack}));
endmodule


module tb_gcd_rig;

    localparam integer H = `BD_HOP_PS;

    // Long enough for the slowest vector in the table to complete several
    // laps through the stub.  The real kernel is far slower; this window is
    // sized for the stub, and the hardware sizes its own from a ring counter.
    localparam integer HOLD   = 40  * H;   // reset asserted at each vector change
    localparam integer WINDOW = 600 * H;   // free running
    localparam integer MINLAP = 4;         // fewer laps than this is not "running"

    reg        rst    = 1'b1;
    reg        inject = 1'b0;   // read by the stub, by hierarchical name
    reg  [3:0] idx    = 4'd0;
    wire       lap, err_flt, ok_flt, probe;

    gcd_rig #(.IDXW(4), .WFILT(2)) uut (
        .rst(rst), .idx(idx),
        .lap(lap), .err_flt(err_flt), .ok_flt(ok_flt), .probe(probe));

    // The two stickies, in the bench, with the same set-dominant shape the
    // hardware gives them -- so what this bench passes on is what the board
    // reads back, not a different question.
    reg [15:0] err_sticky = 16'h0;
    reg [15:0] ok_sticky  = 16'h0;
    integer    laps = 0;

    always @(posedge err_flt) if (!rst) err_sticky[idx] <= 1'b1;
    always @(posedge ok_flt)  if (!rst) ok_sticky[idx]  <= 1'b1;
    always @(posedge lap)     if (!rst) laps = laps + 1;

    integer v, laps_at_start, nfail;

    task judge(input integer vec, input integer nlap,
               input reg got_ok, input reg got_err, input reg want_err);
        begin
            $write("  vec %2d  laps=%0d  ok=%0d err=%0d", vec, nlap, got_ok, got_err);
            if (nlap < MINLAP) begin
                $display("   FAIL -- the ring did not turn");
                nfail = nfail + 1;
            end else if (!got_ok && !want_err) begin
                $display("   FAIL -- no answer was ever checked");
                nfail = nfail + 1;
            end else if (got_err != want_err) begin
                $display("   FAIL -- expected err=%0d", want_err);
                nfail = nfail + 1;
            end else begin
                $display("   ok");
            end
        end
    endtask

    task sweep;
        begin
            err_sticky = 16'h0;
            ok_sticky  = 16'h0;
            for (v = 0; v < 16; v = v + 1) begin
                // idx moves ONLY while rst is asserted.  That is gcd_rig.v's
                // stated contract and hw/gcd_hw.v honours it the same way.
                rst = 1'b1;
                idx = v[3:0];
                #HOLD;
                laps_at_start = laps;
                rst = 1'b0;
                #WINDOW;
                rst = 1'b1;
                #(4 * H);
                judge(v, laps - laps_at_start, ok_sticky[v], err_sticky[v],
                      inject && (v == 6));
            end
        end
    endtask

    initial begin
        nfail = 0;

        // Pass 1: the rig must turn on every vector and call every answer right.
        $display("clean -- the ring must turn on all sixteen vectors, err must stay 0");
        inject = 1'b0;
        sweep;

        // Pass 2: the same rig, one bit wrong on one vector.  Without this the
        // clean pass above is indistinguishable from a detector that cannot
        // set at all -- which is the arb_prot lesson, and it is about this
        // rig's own construction, not about reproving an old bug.
        $display("injected -- one bit wrong on vector 6, err must set THERE and nowhere else");
        inject = 1'b1;
        sweep;

        if (nfail == 0) $display("tb_gcd_rig PASS");
        else            $display("tb_gcd_rig FAIL (%0d vector(s))", nfail);
        $finish;
    end

    // A bench that hangs tells you nothing about which vector hung.
    initial begin
        #(32 * (HOLD + WINDOW + 8 * H) + 1000 * H);
        $display("tb_gcd_rig FAIL (timeout)");
        $finish;
    end

endmodule
