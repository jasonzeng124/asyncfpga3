// ---------------------------------------------------------------------------
// bd_mlink.v -- MOUSETRAP link: two-phase, transition-signalled bundled data.
//
// bd_link (bd_link.v) is four-phase: a token costs the request/acknowledge
// pair two round trips, and the second -- the return to zero -- is pure
// protocol.  On the routed xorshift_round rows the cycle between two stages
// was 5.4 ns of which the matched delay was 2.8; the other 2.6 was the
// acknowledge, the request's fall and the acknowledge's fall, each a hop
// between tiles.  This link signals by TRANSITION instead: a request is a
// toggle, an acknowledge is a toggle, and a token costs the pair one trip.
//
// The controller is Singh and Nowick's MOUSETRAP.  The request passes
// through a latch bit of its own, enabled with the data (`ctl.uq`, so its
// output `done` leaves the stage with the bits it is bundled to), and the
// enable is one XNOR: the stage is transparent while done == ack_out (empty),
// opaque from the moment a request has passed until the stage after it has
// taken the data.
//
//    en   = rst | ~(done ^ ack_out)        ctl.uz, one LUT from done
//    done = latch(req_in, en)              ctl.uq
//    ack_in  = done
//    req_out = delay(done)                 rdly, symmetric: both edges matter
//
// The two timing assumptions, both checked on the route (mtrap: hold):
//
//  setup  D of every latch is stable before EN falls.  The request bit's
//         own D is the toggle that made done toggle, so it is stable by
//         construction; the data bits are stable by the bundling rule, which
//         is bd_link's: the request must not reach the next stage's D before
//         the data does, at every stage.
//
//  hold   This stage CLOSES on its own done (uz, one LUT, then the enable
//         fanout) and the stage before REOPENS on the same done (its uz, its
//         fanout, its latch, the logic between, the wire).  New data must
//         not reach D here before EN has fallen at every bit.  The reopen
//         is on the cycle, the close is not, so the margin is bought by
//         making the reopen slower, never the close: `uen` is a FASTFALL
//         line of NOPEN-1 links in front of uz, so the fall of en0 still
//         reaches en in one LUT while the rise takes NOPEN.
//
// Reset: en is forced high, every latch is transparent, and the source holds
// its request at zero, so every done is zero when reset releases.  No latch
// needs a reset of its own.
// ---------------------------------------------------------------------------

`default_nettype none

module bd_mlink_ctl #(parameter NOPEN = 1)
                     (input wire req_in, input wire ack, input wire rst,
                      output wire done, output wire en);
    wire en0, s;
    // I0 done, I1 ack, I2 rst: rst -> 1, else ~(done ^ ack).
    (* keep *) LUT3 #(.INIT(8'hF9)) ux (.I0(done), .I1(ack), .I2(rst), .O(en0));
    generate
        if (NOPEN <= 1) begin : direct
            assign en = en0;
        end
        if (NOPEN > 1) begin : slow_reopen
            bd_delay #(.N(NOPEN - 1), .FASTFALL(1)) uen (.a(en0), .z(s));
            // I0 s, I1 done, I2 ack, I3 rst: s & (rst | ~(done ^ ack)) -- the
            // XNOR again, so the close does not wait for ux.
            (* keep *) LUT4 #(.INIT(16'hAA82)) uz (
                .I0(s), .I1(done), .I2(ack), .I3(rst), .O(en));
        end
    endgenerate
    bd_latch #(.W(1)) uq (.d(req_in), .en(en), .q(done));
endmodule

module bd_mlink #(parameter W = 8, parameter DELAY = 4, parameter NOPEN = 1)
                 (input wire rst,
                  input wire req_in, output wire ack_in,
                  input wire [W-1:0] data_in,
                  output wire req_out, input wire ack_out,
                  output wire [W-1:0] data_out);
    wire en, done;
    bd_mlink_ctl #(.NOPEN(NOPEN)) ctl (.req_in(req_in), .ack(ack_out), .rst(rst),
                                       .done(done), .en(en));
    bd_latch #(.W(W)) lat (.d(data_in), .en(en), .q(data_out));
    assign ack_in = done;
    bd_delay #(.N(DELAY)) rdly (.a(done), .z(req_out));
endmodule

// ---------------------------------------------------------------------------
// bd_flink -- the same two-phase controller, with the data in FLIP-FLOPS.
//
// A MOUSETRAP stage closes its latches the moment the request arrives, so
// every data bit has to have gone through its mux-LUT and round its own
// feedback wire by then (tighten.loop_wire: 0 in the slice, up to ~730 ps
// when the router detours one bit of a bank), and the matched delay is sized
// by the worst bit.  A flip-flop clocked by that same moment has no loop to
// settle: D is sampled at the edge, setup one FF setup, hold one FF hold, and
// the storage costs no LUT at all -- the FFs sit in the cone's own slices.
//
//    ck   = ~rst & (done ^ ack_out)        ctl.uck: rises when a request
//                                          has passed, falls when the stage
//                                          after has taken the token
//    done = latch(req_in, ~ck)             ctl.uq, transparent while ck is 0
//    q    <= d  @posedge ck                the bank, one FDRE per bit
//
// The FF ignores the fall of ck, so the successor's acknowledge does nothing
// to the data; the request bit alone stays opaque until then, which is what
// keeps a stage from taking a second token before the first has been read.
// Hold: new data can only leave the predecessor after its own ck rises,
// which is after this done reached it and reopened its request bit; the FF
// hold is met by that whole path.  The clock is a fabric net, like every
// other wire here (-noclkbuf), and its skew across the bank is on the route
// like the latch enable's was.
//
// What the route says (xc7z010-1, xorshift_round, two of these stages, the
// FF timing from the chipdb -- patches/nextpnr-xilinx-ff-timing.patch;
// every number an SDF back-annotated GLS, none of it silicon): 201 LUT
// sites + 64 FFs against 222 LUTs for the best route-robust bd_link build
// (three stages, one of them slack); latency 7.4-8.0 ns (bd_link 7.0-7.3),
// fast-source interval 5.4-5.9 ns (5.4-5.5), stalled-consumer interval
// 8.3-8.8 ns (13.5-13.6).  The stalled column is the one two-phase was built
// for and it is the one that moves.  Route-robust status: of four fresh
// seeds, three pass every audit and both GLS runs; one passes GLS but
// fails the request bit's own loop audit -- the router took uq's feedback
// out of the slice (434 ps) and ck closes it in 424, so that seed is
// rejected.  Not integrated: every other cell in rtl/ is four-phase.
// ---------------------------------------------------------------------------

module bd_flink_ctl (input wire req_in, input wire ack, input wire rst,
                     output wire done, output wire ck);
    // I0 done, I1 ack, I2 rst: ~rst & (done ^ ack).
    (* keep *) LUT3 #(.INIT(8'h06)) uck (.I0(done), .I1(ack), .I2(rst), .O(ck));
    // I0 req_in, I1 ck, I2 done: ck ? done : req_in -- the request bit,
    // transparent while ck is low.
    (* keep *) LUT3 #(.INIT(8'hE2)) uq (.I0(req_in), .I1(ck), .I2(done), .O(done));
endmodule

module bd_flink #(parameter W = 8, parameter DELAY = 4)
                 (input wire rst,
                  input wire req_in, output wire ack_in,
                  input wire [W-1:0] data_in,
                  output wire req_out, input wire ack_out,
                  output reg [W-1:0] data_out);
    wire ck, done;
    bd_flink_ctl ctl (.req_in(req_in), .ack(ack_out), .rst(rst),
                      .done(done), .ck(ck));
    always @(posedge ck) data_out <= data_in;
    assign ack_in = done;
    bd_delay #(.N(DELAY)) rdly (.a(done), .z(req_out));
endmodule

`default_nettype wire
