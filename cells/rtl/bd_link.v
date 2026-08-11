// ---------------------------------------------------------------------------
// bd_link.v -- the simple (Muller) pipeline controller.
//
//     C_i = C(req_in, ~C_i+1)
//
// One node drives three things: the latch enable, the outgoing request, and
// the acknowledge returned to the sender.  That is why the data hold window
// ends at ack-fall and not at req-fall -- the latch is still transparent
// until ack drops, and C_i only falls in response to req-fall, a gate delay
// later.  Release data at req-fall and the next value walks through a latch
// that has not closed.
//
// Occupancy is half a token per stage, so two stages make one
// register-equivalent.  The semi- and fully-decoupled controllers are not
// here: they are specified by what they must achieve (letting a stage accept
// a new token while the previous one is still being acknowledged) and have
// not been derived.
//
// Two adjacent stages share {req, C_i, C_i+1, C_i+2, rst} -- five distinct
// pins, exactly the fracturing budget, so control is half a LUT per stage.
// One more control input anywhere and adjacent stages stop sharing.
//
// ---------------------------------------------------------------------------
// req_out LEADS data_out.  Measured, not assumed.
//
// A one-stage bd_link: verify/probes/link_skew.v reports req_out rising
// 152 ps before data_out settles, exactly the latch's own 5LUT fall arc.
// The reason is
// structural.  req_out is the C-element node itself, one arc from req_in;
// data_out is that same node driving a latch, so two arcs from req_in.  No
// wiring of a Muller stage makes the enable and the enabled data land
// together.
//
// A four-stage bd_pipe: verify/probes/pipe_skew.v reports 441 ps.  The lead
// GROWS WITH DEPTH, and this is the part worth understanding.  Filling an
// empty pipe sets off two waves.  The control wave hops C-element to C-element at one
// arc each; the data wave ripples latch to latch, also one arc each, but
// the latch arc is the slower of the two (152 ps fall against 55 ps on the
// controller pair).  The control wave therefore outruns its own data by the
// difference, once per stage.  Across N empty stages the request arrives
// roughly N*(t_latch - t_ctl) ahead of the value it is announcing.
//
// Inside this library that lead is harmless, and why it is harmless is the
// whole argument for the four-phase hold window.  Every consumer of a link
// output is a transparent latch, and it does not close at req-rise -- it
// closes at ack-fall, a full phase later.  A value that arrives some arcs
// behind its own request is still latched correctly, because nothing sampled
// on the edge.  The lead bites only at a boundary that SAMPLES the request
// edge: a BRAM clock pin, a synchronous vendor block, an off-library
// consumer.  There, and only there, req_out on its own is not a valid
// bundled-data request.
//
// bd_mem handles its own boundary with an explicit DSETUP line.  For any
// other edge-sampling consumer, DELAY inserts a matched line on req_out alone
// -- not on ack_in, which must keep ending the hold window at the node
// itself.  DELAY defaults to 0, which is the cell the design review costs:
// zero extra LUTs, identical to the frozen specification.  Set it only at a
// boundary that needs it, size it from the measured lead at that depth, and
// tighten it post-route like every other matched line.
// ---------------------------------------------------------------------------

`default_nettype none

// -- one stage's controller ------------------------------------- 1 LUT6 ----
module bd_link_ctl (input wire req_in, input wire c_next, input wire rst,
                    output wire c);
    bd_c2n u (.a(req_in), .b(c_next), .rst(rst), .q(c));
endmodule

// -- two stages' controllers, one fractured LUT6_2 --------------- 1 LUT -----
// ci = ~rst . C(req_in,  ~cj)
// cj = ~rst . C(ci,      ~c_next)     with c_next = C_i+2
module bd_link_pair (input wire req_in, input wire c_next, input wire rst,
                     output wire ci, output wire cj);
    (* keep *) LUT6_2 #(.INIT(64'h0000_C0FC_0000_8E8E)) u (
        .I0(req_in), .I1(ci), .I2(cj), .I3(c_next), .I4(rst), .I5(1'b1),
        .O5(ci), .O6(cj));
endmodule

// -- one pipeline stage: controller + latch -------- 1 LUT + W/2 LUTs -------
module bd_link #(parameter W = 8, parameter integer DELAY = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);

    wire c;
    bd_link_ctl ctl (.req_in(req_in), .c_next(ack_out), .rst(rst), .c(c));
    bd_latch #(.W(W)) lat (.d(data_in), .en(c), .q(data_out));

    // The node drives three things.  ack_in must stay the raw node: it is what
    // ends the sender's hold window, and delaying it would only lengthen the
    // window, never shorten it -- but it would also stop the pair of adjacent
    // controllers sharing a LUT.  req_out is the one that may need padding at
    // an edge-sampling boundary; see the header.
    bd_delay #(.N(DELAY)) rdly (.a(c), .z(req_out));
    assign ack_in = c;
endmodule

// -- N stages, paired ------------------ ceil(N/2) LUTs + N*W/2 LUTs -------
// Stages 0,1 share a LUT6_2, stages 2,3 share the next, and so on.  An odd
// final stage falls back to a whole LUT6.
// DELAY pads the pipeline's own outgoing request only -- the internal stage
// boundaries need nothing, because each one is a transparent latch.
module bd_pipe #(parameter W = 8, parameter N = 2, parameter integer DELAY = 0)
    (input  wire             rst,
     input  wire             req_in,
     output wire             ack_in,
     input  wire [W-1:0]     data_in,
     output wire             req_out,
     input  wire             ack_out,
     output wire [W-1:0]     data_out);

    genvar i;
    generate
    if (N == 1) begin : one
        bd_link #(.W(W), .DELAY(DELAY)) u (
            .rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
            .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
    end else begin : many
        wire [N-1:0] c;
        wire [N-1:0] rin = {c[N-2:0], req_in};   // rin[k] = stage k's request
        wire [N-1:0] nx  = {ack_out, c[N-1:1]};  // nx [k] = stage k+1's node

        for (i = 0; i + 1 < N; i = i + 2) begin : cpair
            bd_link_pair u (.req_in(rin[i]), .c_next(nx[i+1]), .rst(rst),
                            .ci(c[i]), .cj(c[i+1]));
        end
        if (N % 2) begin : codd
            bd_link_ctl u (.req_in(rin[N-1]), .c_next(nx[N-1]), .rst(rst),
                           .c(c[N-1]));
        end

        wire [W*(N+1)-1:0] dat;
        assign dat[W-1:0] = data_in;
        for (i = 0; i < N; i = i + 1) begin : lat
            bd_latch #(.W(W)) u (.d(dat[W*i +: W]), .en(c[i]),
                                 .q(dat[W*(i+1) +: W]));
        end
        assign data_out = dat[W*N +: W];
        bd_delay #(.N(DELAY)) rdly (.a(c[N-1]), .z(req_out));
        assign ack_in   = c[0];
    end
    endgenerate
endmodule

`default_nettype wire
