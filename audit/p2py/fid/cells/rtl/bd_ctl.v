// ---------------------------------------------------------------------------
// bd_ctl.v -- fork, join, steer, and the two protocol converters.
//
// Everything in this file except the fork/join rendezvous is stateless, so
// nothing here carries reset except where a C-element does.
// ---------------------------------------------------------------------------

`default_nettype none

// ---------------------------------------------------------------------------
// bd_fork -- broadcast the request, join the acknowledges.
//
// Data is broadcast too; a fork routes the handshake, and the copies are
// wires.  Cost is the rendezvous over the acknowledges: one LUT for fan-out
// up to four, a tree beyond that.
// ---------------------------------------------------------------------------
module bd_fork #(parameter N = 2)
    (input  wire             rst,
     input  wire             req,
     output wire             ack,
     output wire [N-1:0]     req_out,
     input  wire [N-1:0]     ack_in);

    assign req_out = {N{req}};
    bd_ctree #(.N(N)) u (.a(ack_in), .rst(rst), .q(ack));
endmodule

// ---------------------------------------------------------------------------
// bd_join -- the dual: join the requests, broadcast the acknowledge.
//
// The output data is the concatenation of the inputs, which is wiring.
// ---------------------------------------------------------------------------
module bd_join #(parameter N = 2)
    (input  wire             rst,
     input  wire [N-1:0]     req_in,
     output wire [N-1:0]     ack_out,
     output wire             req,
     input  wire             ack);

    bd_ctree #(.N(N)) u (.a(req_in), .rst(rst), .q(req));
    assign ack_out = {N{ack}};
endmodule

// ---------------------------------------------------------------------------
// bd_steer -- two AND gates over the same two wires.
//
//     req0 = req . ~s        req1 = req . s        ack = ack0 + ack1
//
// s is data, not a control wire.  The bundling contract holds it still from
// req-rise until ack-fall, a window that strictly contains the time req is
// high, so within a transaction s is a constant and a constant cannot glitch
// a branch.  Outside that window req is already low and req.s is zero
// whatever s does, so return to zero is immediate and unconditional on both
// branches.
//
// An earlier draft built this from two asymmetric C-elements to harden it
// against s moving mid-transaction.  The only thing that could move s
// mid-transaction is a violation of the bundling contract, and if that is
// broken the data being routed is invalid too.
//
// Two distinct inputs between both branches, so they share one fractured LUT
// with four pins spare -- the widest margin in the library.  No feedback
// wire, so no keep attribute, no loop for nextpnr to be told about, and no
// reset.  The acknowledge OR is a second LUT; it is safe as a plain OR
// because only one branch was ever requested.
//
// Data is broadcast to both branches ungated: the steer routes the request,
// never the data.
// ---------------------------------------------------------------------------
module bd_steer
    (input  wire  req,
     input  wire  s,
     output wire  ack,
     output wire  req0,
     input  wire  ack0,
     output wire  req1,
     input  wire  ack1);

    LUT6_2 #(.INIT(64'h8888_8888_2222_2222)) u (
        .I0(req), .I1(s), .I2(1'b0), .I3(1'b0), .I4(1'b0), .I5(1'b1),
        .O5(req0), .O6(req1));
    LUT2 #(.INIT(4'hE)) uack (.I0(ack0), .I1(ack1), .O(ack));
endmodule

// ---------------------------------------------------------------------------
// bd_bd2dr -- bundled to dual-rail.
//
//     t = req . d            f = req . ~d
//
// Pin for pin the same circuit as the steer, which is not a coincidence:
// steering a request down one of two branches and encoding it onto one of two
// rails are the same operation, and the branches are the rails.  Both rails
// are functions of {req, d}, so the pair costs one fractured LUT and the
// inverter costs nothing -- it folds into the AND that consumes it.
//
// The acknowledge is a wire: a dual-rail channel returns one.
// ---------------------------------------------------------------------------
module bd_bd2dr
    (input  wire  req,
     input  wire  d,
     output wire  ack,
     output wire  t,
     output wire  f,
     input  wire  ack_dr);

    LUT6_2 #(.INIT(64'h8888_8888_2222_2222)) u (
        .I0(req), .I1(d), .I2(1'b0), .I3(1'b0), .I4(1'b0), .I5(1'b1),
        .O5(f), .O6(t));
    assign ack = ack_dr;
endmodule

// ---------------------------------------------------------------------------
// bd_dr2bd -- dual-rail to bundled.
//
//     d = t                  req = delta(t + f)
//
// Decoding is the direction that costs a delay: d and req derive from the
// same two wires and would otherwise arrive together, which is exactly the
// bundling constraint being violated at the boundary.
//
// The rule for the compiler: bundled everywhere, dual-rail only on control
// channels that arrive separately from the data they steer, converters at
// that boundary.  When the condition rides in the bundle there is no boundary
// and no converter.
//
// ---------------------------------------------------------------------------
// THE SPACER EATS THE DATA.  Reported, not silently patched -- HOLD defaults
// to 0, which is the cell exactly as specified.
//
// d = t is correct for the whole of the valid phase and wrong for the phase
// after it.  Trace the two protocols against each other:
//
//   rails go valid      -> req rises a delay later
//   bundled receiver latches, raises ack
//   ack_dr IS ack, so the dual-rail sender now drops BOTH RAILS to the spacer
//   d = t collapses to 0 -- and req has not fallen yet, it falls a delay later
//   only after that does the receiver's latch close
//
// So d moves inside the bundled hold window, which runs to ack-fall and not to
// rail-fall.  A receiver that samples early -- a testbench, a synchroniser --
// never sees it.  A receiver that is a transparent latch, which is every
// consumer in this library, is still open when the rails collapse and closes
// on the spacer.  It captures zero.  tb_conv measures this on a DELAY(4),
// HOLD(0) instance: twelve hold-window violations in twenty-four transactions,
// exactly the transactions carrying a one.
//
// This is not a delay-sizing problem and no amount of DELAY fixes it.  The
// return-to-zero phases of the two protocols are driven by the same
// acknowledge and are one phase out of step by construction; the data has to
// be held across the difference, and holding is a latch.
//
// HOLD(1) holds it, and the right hold is not an ack-gated latch.  The rails
// already carry their own validity: the spacer is not "no data", it is "hold
// what you had".  That is a C-element, and the decoder is
//
//     d = C(t, ~f)      set on t.~f, reset on ~t.f, HOLD on the spacer
//
// Read the four codes.  Valid ONE  is t=1,f=0 -> both inputs agree high, set.
// Valid ZERO is t=0,f=1 -> both agree low, reset.  SPACER is t=0,f=0 -> the
// inputs disagree, so the C-element holds -- which is the entire fix.  The
// fourth code cannot occur, and gives a hold if it ever did.
//
// This costs NOTHING.  d touches {t, f, d} and either touches {t, f}: three
// distinct inputs between them, well under the five that let two functions
// share one fractured LUT6_2.  The OR that was a LUT2 becomes O6 of that same
// LUT, and the decode becomes O5.  One LUT before, one LUT after -- the design
// review's budget for this cell is met exactly, and an earlier version of this
// file that spent a whole extra LUT6 on an ack-gated latch was wrong to.
//
// It is also the stronger fix, not merely the cheaper one.  An ack-gated latch
// reopens at ack-FALL, and at ack-fall the rails are already sitting at the
// spacer, so d collapses on the closing edge of the very window it is meant to
// protect -- correct by one arc.  The C-element does not reopen until the next
// VALID code, which the dual-rail sender may not drive until it has seen
// ack_dr fall.  The value therefore stands from its own valid code, across the
// spacer, to the next valid code: the bundled hold window sits strictly inside
// that, with a full phase of margin on the closing side instead of an arc.
//
// AND IT TAKES NO RESET, which is unusual here -- every other feedback loop in
// this library has a reset pin, because a LUT loop has no power-up value.  The
// rule still holds; this loop just does not need the value.  The unknown it
// powers up holding is never READ: d is only ever consumed behind req, req
// only rises behind the matched delay off a valid code, and a valid code is
// exactly what overwrites d.  Whatever the loop settled to at power-up is
// gone before anything can look at it.
//
// That survives simulation as well as silicon, which is the part worth
// stating, because an X is stricter than a real fabric and would have found
// the hole if there were one.  A mux-tree LUT model merges bitwise: with an X
// on the feedback pin it evaluates both halves of the table and returns the
// agreed value wherever they agree.  On a valid code they always agree -- that
// is what "valid" means for a C-element, both inputs pulling the same way --
// so d resolves on the first token and the X never propagates.
//
// So the pin is not free-but-harmless, it is absent.  Three inputs, not four.
// ---------------------------------------------------------------------------
module bd_dr2bd #(parameter DELAY = 4, parameter HOLD = 0)
    (input  wire  t,
     input  wire  f,
     output wire  ack_dr,
     output wire  req,
     output wire  d,
     input  wire  ack);

    wire either;
    bd_delay #(.N(DELAY)) ud (.a(either), .z(req));
    assign ack_dr = ack;

    generate
        if (HOLD) begin : ghold
            // O6 = either = t + f
            // O5 = d      = majority(t, ~f, d)
            (* keep *) LUT6_2 #(.INIT(64'hEEEE_EEEE_B2B2_B2B2)) u (
                .I0(t), .I1(f), .I2(d), .I3(1'b0), .I4(1'b0), .I5(1'b1),
                .O5(d), .O6(either));
        end else begin : gbare
            LUT2 #(.INIT(4'hE)) uor (.I0(t), .I1(f), .O(either));
            assign d = t;
        end
    endgenerate
endmodule

`default_nettype wire
