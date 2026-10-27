// ---------------------------------------------------------------------------
// bd_semi_attempt.v -- a DERIVATION THAT DOES NOT WORK.  Kept as evidence.
//
// NOT PART OF THE LIBRARY.  It lives outside rtl/ deliberately: it is not a
// cell, it is a recorded negative result, and the reason it is recorded is
// that it fails in a way that says something useful about which coupling in
// the simple controller can be removed and which cannot.
//
// -- what was being attempted ------------------------------------------------
//
// The design review names a semi-decoupled controller in its family table --
// "1 token/stage, breaks DV" -- and states plainly that it was specified by
// what it must achieve and never derived.  The requirement, in its words: a
// stage must be able to accept a new token while the previous one is still
// being acknowledged.  This was an attempt at that derivation.
//
// -- the circuit --------------------------------------------------------------
//
// The simple controller has one node doing three jobs, and that is what costs
// it the occupancy: C_i is the latch enable, the outgoing request AND the
// incoming acknowledge, so the input handshake cannot finish until the output
// handshake has started.  Split the node in two:
//
//     L = ~rst . C(Rin, ~R)        latch enable, and the acknowledge
//     R = ~rst . C(L,  ~Aout)      the outgoing request
//     Ain = L
//
// Rin rises with the stage empty, so L rises: the latch opens and the sender
// is acknowledged at once.  L high with the output free makes R rise.  The
// sender drops Rin; L falls, because R is up and Rin is down; the latch closes
// and the input channel is free while R is still high waiting for Aout.
//
// -- two things it got right --------------------------------------------------
//
// THE OCCUPANCY IS REAL.  tb_semi measures it: a four-stage pipe holds four
// tokens against the simple controller's two.  One a stage, as specified.
//
// THE COST IS REAL, and it is a nice result on its own.  L and R between them
// touch {Rin, L, R, Aout, rst} -- five pins, so one fractured LUT6_2 per
// stage.  And the constant that falls out is 64'h0000_C0FC_0000_8E8E, which is
// bit for bit the constant bd_link_pair uses for two adjacent SIMPLE stages.
// The two circuits are the same function with the pins renamed,
//
//     (req_in, ci, cj, c_next)  <->  (Rin, L, R, Aout)
//
// differing only in what the nodes drive: in the simple pipe ci and cj are two
// stage controllers driving two latches and holding one token between them;
// here L drives the one latch and R drives the request, and the stage holds a
// token on its own.  Same control silicon, half the storage per token.
//
// -- AND THE THING IT GOT WRONG ----------------------------------------------
//
// L closes when Rin is low AND R is high.  Neither of those is under this
// stage's control, and that is the whole defect: A STAGE THAT CANNOT DECIDE
// WHEN ITS OWN LATCH CLOSES HAS NO LATCH.  It shows up from both directions,
// and tb_ctl measures both.
//
//   trigger 1, from upstream.  A sender that turns round quickly.  L falls one
//   arc after Rin falls; the stage upstream is freed one arc after that and
//   reopens; its new value reaches this latch one arc later still.  The margin
//   is a single arc, and a brisk sender eats it.  18 of 20 tokens wrong with
//   the source's setup at 300 ps -- no matter what the consumer does.
//
//   trigger 2, from downstream.  A consumer slow to drop its acknowledge.  R
//   rises only when Aout is low, so a consumer that holds its acknowledge
//   holds R down, and L never closes at all.  The pipe goes transparent and
//   the tokens collapse into one another.  9 of 20 wrong with the consumer
//   taking 6000 ps to let go -- even with a slow sender.
//
// The two are not the same KIND of defect, and tb_ctl asserts the difference
// in both timing regimes:
//
//   trigger 1 is a RACE, one arc wide.  At BD_ROUTE_PS=354 it is gone --
//   routing puts a hop in the path that has to lose, exactly the shape of the
//   arbiter's handover overlap.  A race that routing fixes is a post-route
//   check, not a defect.
//
//   trigger 2 is STRUCTURAL.  The outgoing request cannot rise while the
//   consumer holds its acknowledge, so the latch cannot close, and no routing
//   changes that.  It reproduces at 0 ps and at 354 ps, and it gets worse:
//   9 of 20 wrong arc-only, 15 of 20 with routing.
//
// Trigger 2 alone is why this cell can never ship.  Slack on the other side
// hides it, which is worth knowing: the first sweep that found this used a leisurely source and only
// ever varied the consumer, so it saw trigger 2 and concluded the problem was
// the consumer.  It was not.  tb_ctl separates them:
//
//     long setup only  (TSU 6000)                    0 of 20 wrong
//     long gap only    (GAP 6000)                    0 of 20 wrong
//     brisk sender     (TSU 300)                    18 of 20 wrong
//     slow sender and slow release                   9 of 20 wrong
//
// The simple controller fills every column of the same matrix, and it is not
// close: it is still correct with a consumer that takes 200000 ps to respond.
// There is no bound to find, because there a slow partner holds the latch
// CLOSED, which is the safe direction, and the latch closes only when BOTH
// neighbours agree -- so neither one can hold it open alone.
//
// -- what the negative result is worth ---------------------------------------
//
// The coupling that was removed was the load-bearing one.  Splitting the node
// made the close depend on signals the neighbours gate, and a gated close is
// an open latch.
//
// A correct decoupled stage therefore cannot get away with two nodes.  It
// needs a third piece of state that records "this stage is loaded",
// independent of both handshakes, so that the close is a decision the stage
// makes on its own -- which is why the published fully-decoupled controllers
// carry more state than looks necessary.  That is the next thing to derive,
// and this file is here so it is not derived the same way twice.
//
// tb/tb_ctl.v reproduces every number above and FAILS if the defect ever stops
// reproducing, because a defect that quietly disappears is a defect that was
// never understood.  It also runs the same matrix over the simple controller,
// so "the attempt is worse" is a measurement and not an opinion.
// ---------------------------------------------------------------------------

`default_nettype none

// -- one stage's controller ---------------------------------------- 1 LUT ---
module bd_semi_ctl (input wire req_in, input wire ack_out, input wire rst,
                    output wire l, output wire r);
    (* keep *) LUT6_2 #(.INIT(64'h0000_C0FC_0000_8E8E)) u (
        .I0(req_in), .I1(l), .I2(r), .I3(ack_out), .I4(rst), .I5(1'b1),
        .O5(l), .O6(r));
endmodule

// -- one stage: controller + latch ------------------ 1 LUT + W/2 LUTs -------
// DELAY pads the outgoing request for an edge-sampling consumer, exactly as in
// bd_link, and defaults to 0 for the same reason.
module bd_semi #(parameter W = 8, parameter integer DELAY = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);

    wire l, r;
    bd_semi_ctl ctl (.req_in(req_in), .ack_out(ack_out), .rst(rst),
                     .l(l), .r(r));
    bd_latch #(.W(W)) lat (.d(data_in), .en(l), .q(data_out));

    assign ack_in = l;
    bd_delay #(.N(DELAY)) rdly (.a(r), .z(req_out));
endmodule

// -- N stages -------------------------- N LUTs + N*W/2 LUTs -----------------
// Stage i's request comes from stage i-1's R; stage i's acknowledge is stage
// i+1's L, which is stage i+1's Ain.  Adjacent stages share nothing: stage i
// needs {R_i-1, L_i, R_i, L_i+1, rst} and stage i+1 needs {R_i, L_i+1, R_i+1,
// L_i+2, rst}, eight distinct pins between them.  So a semi-decoupled stage is
// a whole LUT where a simple one is half -- and holds twice the token.
module bd_pipe_semi #(parameter W = 8, parameter N = 2,
                      parameter integer DELAY = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);

    wire [N-1:0] l, r;
    wire [N-1:0] rin  = (N == 1) ? req_in  : {r[N-2:0], req_in};
    wire [N-1:0] aout = (N == 1) ? ack_out : {ack_out, l[N-1:1]};

    wire [W*(N+1)-1:0] dat;
    assign dat[W-1:0] = data_in;

    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : stage
            bd_semi_ctl u (.req_in(rin[i]), .ack_out(aout[i]), .rst(rst),
                           .l(l[i]), .r(r[i]));
            bd_latch #(.W(W)) lat (.d(dat[W*i +: W]), .en(l[i]),
                                   .q(dat[W*(i+1) +: W]));
        end
    endgenerate

    assign data_out = dat[W*N +: W];
    assign ack_in   = l[0];
    bd_delay #(.N(DELAY)) rdly (.a(r[N-1]), .z(req_out));
endmodule

`default_nettype wire
