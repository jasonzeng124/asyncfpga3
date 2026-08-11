// ---------------------------------------------------------------------------
// bd_deco.v -- the decoupled pipeline controller.  One token a stage.
//
// NOT IN THE DESIGN REVIEW.  The review names this controller in its family
// table -- "1 token/stage" -- and states plainly that it was specified by what
// it must achieve and never derived.  This is the derivation.  Every number
// here is measured by tb_ctl, not quoted from there; nothing in this file has
// the review's authority behind it.
//
// It is the second attempt.  The first is kept in verify/attempts/ because the
// way it failed is what this one is designed against, and the rule it broke is
// the only rule that matters here:
//
//     THE STAGE MUST OWN ITS LATCH CLOSE.
//
// A stage that cannot decide when its own latch shuts has no latch.  The first
// attempt closed on "Rin low AND R high", and R is gated by the consumer -- so
// a consumer that took its time dropping an acknowledge held the latch open
// and the pipeline went transparent.  Below, the close is a function of Rin
// and nothing else.  The sender must drop Rin: that is its half of the
// handshake, not a favour.
//
// -- the equations -----------------------------------------------------------
//
//     L = ~rst . Rin . (L + ~F.~Aout)      latch enable, and Ain
//     F = ~rst . ~Aout . (Rin + F)         "this stage is loaded"
//     R = ~rst . ~Aout . (R + F.~L)        the outgoing request
//
// F is the third state the first attempt lacked, and what F is set BY is the
// part that took two goes.  An earlier version used F = L.Rin + F.~Aout, which
// needs L and Rin high at the same time -- and a sender that drops Rin the
// instant it sees Ain leaves that coincidence one arc wide.  tb_ctl caught it
// at once: a four-stage pipe reported no backpressure at all, because F never
// latched and the stage never believed it held anything.
//
// So F is set by Rin, and by nothing else.  Rin is high from Rin-rise to
// Rin-fall -- a whole sender round trip, the longest unambiguous window in the
// protocol.  No coincidence of two edges, no pulse to catch.  Setting F on a
// request that the stage is too full to accept is harmless, because a full
// stage already has F high.
//
// Read it as a sequence.  Rin rises with the stage free (F and Aout both low),
// so L rises: the latch opens and the sender is acknowledged.  F follows,
// while Rin is still high, and L holds itself up through its own L term -- no
// pulse.  The sender drops Rin and L falls: THE LATCH CLOSES, on Rin alone.
// Now F is high and L is low, so R rises and the value is offered onward.  The
// consumer acknowledges; R falls and F clears.  The consumer releases; only
// now, with F and Aout both low, may L reopen.
//
// -- what that ordering buys -------------------------------------------------
//
// The output data holds for the WHOLE window, req-rise to ack-FALL, which is
// the review's contract and not the weaker ack-rise one the first attempt
// offered.  data_out can only move when L reopens, and L cannot reopen until
// Aout has gone low.  So this controller composes with anything, including a
// simple stage -- the first attempt did not.
//
// And there is no race at the stage boundary.  Stage i's data moves only after
// stage i+1's latch has shut, because L_i needs Aout_i = L_i+1 low first.  The
// first attempt's whole margin was one arc of exactly that.
//
// -- cost ---------------------------------------------------------------------
//
// L and F touch {Rin, L, F, Aout, rst}: five pins, so they share ONE fractured
// LUT6_2.  R touches {F, L, R, Aout, rst}: five more, its own LUT6.  Two LUTs
// of control a stage, against the simple controller's half.  Per token stored:
//
//     simple      1 LUT of control + W   latch LUTs   (two stages, one token)
//     decoupled   2 LUTs of control + W/2 latch LUTs  (one stage,  one token)
//
// Break-even at W = 2; at W = 8 it is 6 LUTs a token against 9.  The wider the
// datapath the more it wins, which is the useful direction.
//
// Adjacent stages share nothing: stage i needs {R_i-1, L_i, F_i, L_i+1, rst}
// and stage i+1 needs {R_i, L_i+1, F_i+1, L_i+2, rst}, and there is no pairing
// across that.
//
// -- WHY THIS IS IN attempts/ AND NOT IN rtl/ ---------------------------------
//
// It does not conform, and the reason is worth more than the cell.
//
// The close is a function of Rin alone, which is what the first attempt got
// wrong -- but it means the latch is open for exactly as long as the SENDER
// holds Rin up after being acknowledged.  That window is not this stage's to
// set.  Swept directly (build/deco_turn.v, four stages, eight tokens):
//
//     sender turnaround      0 ps   8 of 8 accepted, latches hold xx
//     sender turnaround     60 ps   4 of 8 accepted, latches hold a0
//     sender turnaround   2000 ps   4 of 8 accepted, latches hold a0
//
// Correct everywhere except exactly zero, and zero is what tb_ctl presents,
// because bd_source drops req in the same timestep it sees ack.  Zero is not
// physical -- Ain has to cross a routed hop and Rin come back over another --
// so the conformance matrix is measuring a regime silicon cannot produce.
//
// That is not an acquittal.  A stage whose capture window is a partner's
// response time has an obligation the simple controller does not: the simple
// controller holds its latch from req-rise to ack-fall and is indifferent to
// how fast anyone turns round.  Trading that away for one token a stage may
// well be worth it -- but it is a trade, it was not in the design review, and
// nothing here has measured what it costs.  Resolving it means a source that
// models a physical turnaround, which changes a harness every bench shares.
//
// So: not disproved, not established, and not shipped.  tb_ctl asserts the
// measured state in both directions, so if this ever starts passing a
// zero-turnaround sender the bench says so rather than quietly going green.
//
// -- what is NOT established -------------------------------------------------
//
// Cycle time.  The review's family table distinguishes semi- from
// fully-decoupled by which combinational path through the stage is cut, and
// that is a throughput claim, not an occupancy one.  Nothing here measures
// throughput, so this file claims occupancy and composability and stops there.
// Calling it "fully decoupled" would be claiming something unmeasured.
// ---------------------------------------------------------------------------

`default_nettype none

// -- one stage's controller --------------------------------------- 2 LUTs ---
module bd_deco_ctl (input wire req_in, input wire ack_out, input wire rst,
                    output wire l, output wire f, output wire r);

    // O6 = F = ~rst . ~Aout . (Rin + F)
    // O5 = L = ~rst . Rin . (L + ~F.~Aout)
    (* keep *) LUT6_2 #(.INIT(64'h0000_00FA_0000_888A)) ulf (
        .I0(req_in), .I1(l), .I2(f), .I3(ack_out), .I4(rst), .I5(1'b1),
        .O5(l), .O6(f));

    // R = ~rst . ~Aout . (R + F.~L)
    (* keep *) LUT6 #(.INIT(64'h0000_00F2_0000_00F2)) ur (
        .I0(f), .I1(l), .I2(r), .I3(ack_out), .I4(rst), .I5(1'b0), .O(r));
endmodule

// -- one stage: controller + latch ----------------- 2 LUTs + W/2 LUTs -------
// DELAY pads the outgoing request for an edge-sampling consumer, exactly as in
// bd_link, and defaults to 0 for the same reason.
module bd_deco #(parameter W = 8, parameter integer DELAY = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);

    wire l, f, r;
    bd_deco_ctl ctl (.req_in(req_in), .ack_out(ack_out), .rst(rst),
                     .l(l), .f(f), .r(r));
    bd_latch #(.W(W)) lat (.d(data_in), .en(l), .q(data_out));

    assign ack_in = l;
    bd_delay #(.N(DELAY)) rdly (.a(r), .z(req_out));
endmodule

// -- N stages ---------------------------- 2N LUTs + N*W/2 LUTs --------------
// Stage i's request is stage i-1's R; stage i's acknowledge is stage i+1's L,
// which is stage i+1's Ain.
module bd_pipe_deco #(parameter W = 8, parameter N = 2,
                      parameter integer DELAY = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);

    wire [N-1:0] l, f, r;
    wire [N-1:0] rin  = (N == 1) ? req_in  : {r[N-2:0], req_in};
    wire [N-1:0] aout = (N == 1) ? ack_out : {ack_out, l[N-1:1]};

    wire [W*(N+1)-1:0] dat;
    assign dat[W-1:0] = data_in;

    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : stage
            bd_deco_ctl u (.req_in(rin[i]), .ack_out(aout[i]), .rst(rst),
                           .l(l[i]), .f(f[i]), .r(r[i]));
            bd_latch #(.W(W)) lat (.d(dat[W*i +: W]), .en(l[i]),
                                   .q(dat[W*(i+1) +: W]));
        end
    endgenerate

    assign data_out = dat[W*N +: W];
    assign ack_in   = l[0];
    bd_delay #(.N(DELAY)) rdly (.a(r[N-1]), .z(req_out));
endmodule

`default_nettype wire
