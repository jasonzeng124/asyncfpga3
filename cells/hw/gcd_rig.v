// ---------------------------------------------------------------------------
// gcd_rig.v -- a compiled kernel, running on silicon, checking its own answers.
//
// Everything this project has measured on the board so far has been ONE CELL
// (ro_top: a delay line; arb_mtbf: bd_arbcell; arb_prot: bd_arbiter inside its
// protocol).  This is the first design that puts a whole COMPILED KERNEL on
// the die -- bdc/emit.py's output for dynamatic/integration-test/gcd, 6513
// occupied LUT sites of it -- and asks whether it computes gcd.
//
// -- THE ENVIRONMENT IS A RING, AND THAT IS THE POINT ------------------------
//
// The kernel has three input channels (a, b, start) and two output channels
// (out0, p_end).  This closes them into a single cycle:
//
//     c1 --fork--> a, b, start --> [ bdc_gcd ] --> out0 --delay--> c0
//      ^                                                            |
//      +------------------------------------------------------------+
//
// which is a closed ring, and so the ring invariant applies to it exactly as
// it applies to anything the compiler emits: occupancy must be strictly
// between empty and full or it deadlocks at reset, and neither state is a
// glitch you can wait out.  c1 is therefore a bd_c2n_SET and c0 a plain
// bd_c2n -- one token, present at reset, in a ring whose other stages all come
// up empty.  That single token is the whole stimulus.  There is no oscillator
// here and nothing free-runs: the kernel is asked for a gcd, answers, and is
// asked again, forever, at whatever rate it can manage.
//
// p_end is not in the ring and the env is two nodes rather than one.  Both of
// those are consequences of how the kernel actually behaves at its boundary,
// both were found by running it, and both are argued where they are built.
//
// One token also means exactly one gcd is ever in flight.  That is a real
// throughput sacrifice -- the dataflow graph would happily pipeline several --
// and it is what makes the answer checkable, because it is the only way the
// (a,b) presented at the input and the g arriving at the output are known to
// be the same transaction.  The number this measures is therefore LATENCY, not
// peak throughput, and it is the conservative end.
//
// -- WHY THE VECTOR NEVER MOVES WHILE THE RING IS RUNNING --------------------
//
// idx selects (a, b, expected) from the table below, combinationally.  It is
// a top-level input and the contract on it is: it may change ONLY while rst is
// asserted.  gcd_hw.v honours that by restarting the ring at each window edge.
//
// The alternative -- advancing the vector per lap, from a counter clocked off
// the completion -- was rejected.  The counter would update a BUFG plus a
// clock-to-out after the result request rose, while the env node re-requests
// within one LUT of it, so the kernel's next input handshake would begin
// against operands that were still moving.  That is a bundling violation, not
// a slow path, and padding the env request to cover it would mean sizing a
// matched delay against a global-buffer arc.  Holding the vector still for a
// whole window costs one restart per vector and has no timing content at all.
//
// -- HOW THIS SELF-REPORTS ---------------------------------------------------
//
// Same doctrine as hw/arb_prot.v, for the same reason: a rig whose result is
// "a sticky bit stayed at zero" cannot distinguish a correct kernel from a
// kernel that never ran, and both look identical in a readback.  So the result
// is a PAIR, built from the same LUT3, the same INIT and the same arm gate:
//
//   ok=1, err=0   the kernel answered, and every answer was right
//   ok=0          it never produced a checkable result; err=0 means nothing
//   err=1         the finding
//
// Both are width-filtered by WFILT links, the same discriminator arb_prot
// uses.  The filter is the second line of defence only: what actually makes
// the compare valid is that the request gating it has been padded to trail the
// data it describes.  See CMPD below.
// ---------------------------------------------------------------------------

`default_nettype none

module gcd_rig #(parameter integer IDXW  = 4,
                 parameter integer WFILT = 2,
                 parameter integer CMPD  = 16)
    (input  wire            rst,        // holds the ring; idx may move only here
     input  wire [IDXW-1:0] idx,        // which vector, stable while rst is low
     output wire            lap,        // one four-phase cycle per completed gcd
     output wire            err_flt,    // a wrong answer, width-filtered
     output wire            ok_flt,     // a right answer, width-filtered
     output wire            probe);     // liveness sample, meaning is in its variance

    // ---- the vector table --------------------------------------------------
    // Sixteen (a, b, expected) triples.  The first six are bdc/simcheck.py's
    // own vectors, so a hardware disagreement can be replayed in simulation
    // against a bench that is known to pass.  The rest widen the range the
    // kernel is asked to cover: the C source's two early returns (a==0, b==0),
    // equal operands, coprime operands, a pure power of two, and -- vector 6 --
    // the pair gcd.c's own main() calls the kernel with, which is the only one
    // that drives the k-loop deeply.
    //
    // Every expected value here was produced by bdc/simcheck.py's ref_gcd,
    // which is a transcription of the C, and independently agrees with
    // Python's math.gcd on all sixteen.
    // A function and a continuous assign, NOT an `always @*` block.  The block
    // is the obvious way to write this and it is wrong in simulation: @* waits
    // for an edge, idx starts at 0 and a sweep that starts at vector 0 never
    // gives it one, so the table reads X for the whole first vector and every
    // compare against it is meaningless.  This bench found that, and the same
    // shape would have shipped to the board looking fine.
    function [95:0] vector(input [3:0] i);
        case (i)
            4'd0:  vector = {32'h00000005, 32'h00000005, 32'h00000000};
            4'd1:  vector = {32'h00000007, 32'h00000000, 32'h00000007};
            4'd2:  vector = {32'h00000006, 32'h00000012, 32'h0000000C};
            4'd3:  vector = {32'h00000006, 32'h00000012, 32'h00000030};
            4'd4:  vector = {32'h00000001, 32'h00000001, 32'h00000001};
            4'd5:  vector = {32'h00000001, 32'h00000005, 32'h00000011};
            4'd6:  vector = {32'h00000020, 32'h12B87CA0, 32'h00798F20};
            4'd7:  vector = {32'h00000015, 32'h000001CE, 32'h0000042F};
            4'd8:  vector = {32'h00000006, 32'h000000C0, 32'h0000010E};
            4'd9:  vector = {32'h00001000, 32'h00001000, 32'h00010000};
            4'd10: vector = {32'h00018697, 32'h00018697, 32'h00018697};
            4'd11: vector = {32'h0000000C, 32'h000C0A14, 32'h0001E240};
            4'd12: vector = {32'h00000001, 32'h00000002, 32'h7FFFFFFF};
            4'd13: vector = {32'h00000001, 32'h000F423F, 32'h000F4240};
            4'd14: vector = {32'h0000000C, 32'h0000003C, 32'h00000024};
            4'd15: vector = {32'h00000100, 32'h00000300, 32'h00000400};
        endcase
    endfunction

    wire [95:0] vec = vector(idx);
    wire [31:0] a_v = vec[31:0];
    wire [31:0] b_v = vec[63:32];
    wire [31:0] g_v = vec[95:64];

    // ---- the kernel --------------------------------------------------------
    wire a_req, a_ack, b_req, b_ack, start_req, start_ack;
    wire out0_req, out0_ack, p_end_req, p_end_ack;
    wire [31:0] out0_data;

    bdc_gcd udut (
        .rst(rst),
        .a_req(a_req),         .a_ack(a_ack),         .a_data(a_v),
        .b_req(b_req),         .b_ack(b_ack),         .b_data(b_v),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req),   .out0_ack(out0_ack),   .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    // ---- fork the env request into the three input channels ----------------
    wire env_c, in_ack;
    wire [2:0] in_req, in_acks;
    assign in_acks = {start_ack, b_ack, a_ack};
    assign {start_req, b_req, a_req} = in_req;

    bd_fork #(.N(3)) ufork (
        .rst(rst), .req(env_c), .ack(in_ack),
        .req_out(in_req), .ack_in(in_acks));

    // ---- p_end is NOT part of the result -----------------------------------
    // It looks like a completion signal and it is not one.  In the compiled
    // kernel the function's control argument forks straight to the function's
    // control result:
    //
    //     assign n_arg2_req = start_req;                  (gcd_kernel.v)
    //     bd_fork #(.N(2)) ... .req_out({n0__1_req, n0__0_req})
    //     assign p_end_req  = n0__0_req;
    //
    // so p_end_req IS start_req, combinationally, with no storage between
    // them.  Joining it into the result and feeding that back to the node that
    // drives start would close a cycle with zero storage stages in it -- the
    // env's own version of the mistake bdc/emit.py's ring_depths() exists to
    // stop.  p_end therefore gets its own sink: ack = delay(req), which is
    // exactly rtl/bd_end.v's bd_snk, minus the data bus it has no need for.
    bd_delay #(.N(2)) upsnk (.a(p_end_req), .z(p_end_ack));

    // ---- the result channel, with its request padded -----------------------
    // out0_req LEADS out0_data by one latch arc -- rtl/bd_link.v's header says
    // so and measures it at 152 ps -- which is harmless for a latch consumer
    // and fatal for anything that samples the request EDGE.  The compare below
    // is exactly such a consumer, and so is the env node, whose acknowledge
    // ends the producer's hold window.
    //
    // So the request is delayed once, here, and everything downstream uses the
    // delayed copy.  Delaying only the compare would not work: res_req's high
    // time is a handful of LUTs (it falls as soon as the env node acknowledges
    // it), so a gate delayed past that samples nothing at all.  Delaying the
    // acknowledge too widens the valid window by the same amount it shifts the
    // gate, which is the whole point.
    //
    // CMPD is a matched delay and is sized like one: three elements to cover
    // the 152 ps latch arc (a bd_delay element is a LUT1 whose RISE arc is
    // 56 ps), about five more for the 32-bit compare tree's own depth, and the
    // rest is guardband.  It cost three wrong answers and one right answer
    // flagged as wrong to find that out.
    wire res_req, res_ack;
    bd_delay #(.N(CMPD)) urdly (.a(out0_req), .z(res_req));
    assign out0_ack = res_ack;

    // ---- the env, which is TWO stages and has to be --------------------------
    // The kernel acknowledges `start` only when it is finished -- start_ack is
    // C(p_end_ack, body_ack) and the body's control token threads the whole
    // computation -- so "the inputs were consumed" and "the result arrived"
    // are, at this boundary, the SAME instant.
    //
    // A single node cannot serve both.  It comes up holding, stays high for
    // the entire computation because in_ack has not risen yet, and is
    // therefore already high when the result request arrives; the rise that
    // was supposed to carry the token back is swallowed, the node falls once,
    // and nothing ever raises it again.  Measured, not deduced: the one-node
    // version turned zero laps on all sixteen vectors.
    //
    // Two nodes separate the two events.  c0 takes the result back, c1 hands
    // the next request out, and the token is passed from one to the other
    // exactly as it is between any two stages of a bd_pipe -- which is what
    // this is, with the SET on the output stage so the ring starts with one
    // token in it and c0 empty.
    wire env_c0;
    bd_c2n     uenv0 (.a(res_req), .b(env_c),  .rst(rst), .q(env_c0));
    bd_c2n_set uenv1 (.a(env_c0),  .b(in_ack), .rst(rst), .q(env_c));
    assign res_ack = env_c0;

    // ---- did it get the right answer? --------------------------------------
    // res_req high means both result channels have presented, so out0_data has
    // been stable since before it rose.  Gating the compare on res_req is what
    // makes that guarantee the compare's guarantee too.
    wire mism = |(out0_data ^ g_v);

    wire err_raw, ok_raw, err_d, ok_d;
    (* keep *) LUT2 #(.INIT(4'h8)) uerr_d (.I0(mism), .I1(res_req), .O(err_raw));
    (* keep *) LUT2 #(.INIT(4'h4)) uok_d  (.I0(mism), .I1(res_req), .O(ok_raw));

    bd_delay #(.N(WFILT)) uerr_w (.a(err_raw), .z(err_d));
    bd_delay #(.N(WFILT)) uok_w  (.a(ok_raw),  .z(ok_d));

    // (* keep *) is mandatory on both ANDs -- without it an optimiser folds
    // a & delay(a) back to a and the discriminator silently stops existing.
    (* keep *) LUT2 #(.INIT(4'h8)) uerr_a (.I0(err_raw), .I1(err_d), .O(err_flt));
    (* keep *) LUT2 #(.INIT(4'h8)) uok_a  (.I0(ok_raw),  .I1(ok_d),  .O(ok_flt));

    assign lap   = res_req;   // padded out0_req: one rise per delivered gcd
    assign probe = env_c;

endmodule

`default_nettype wire
