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
// Two adjacent stages could share {req, C_i, C_i+1, C_i+2, rst} -- five
// distinct pins, exactly the fracturing budget, half a LUT per stage -- and
// bd_pipe used to.  It no longer does: see DACK below.  A shared LUT feeds
// C_i+1 straight into C_i's equation, and that is exactly the wire the hold
// fix has to lengthen.  Control is one LUT per stage plus its DACK line, out
// of W/2 + 1 for the stage -- the pairing was never where the area was.
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
// the latch arc is the slower of the two (152 ps fall against 56 ps on the
// controller).  The control wave therefore outruns its own data by the
// difference, once per stage.  Across N empty stages the request arrives
// roughly N*(t_latch - t_ctl) ahead of the value it is announcing.
//
// Inside this library that lead is USUALLY harmless.  Every consumer of a
// link output is a transparent latch, and it does not close at req-rise --
// it closes when its node falls, a full phase later.  A value that arrives
// some arcs behind its own request is still latched correctly as long as it
// is in before THAT.  The lead bites for certain at a boundary that SAMPLES
// the request edge: a BRAM clock pin, a synchronous vendor block, an
// off-library consumer.  There, req_out on its own is not a valid
// bundled-data request.
//
// It also bites inside a pipe, and the old version of this header said it
// could not.  Stage i closes one controller arc after stage i-1's node
// fell; its data settles one LATCH arc after stage i-1's data did; the
// latch arc is the slower (152 against 124 ps in sim/bd_prims_sim.v).  Fill
// an empty pipe behind a source that returns to zero the moment it is
// acknowledged and the closing wave gains on the data wave by the
// difference at every stage: tb_link's 8-bit, 4-stage pipe latches X into
// stage 2 of token 0 with no request line between the stages.  The paired
// LUT6_2 controllers hid this in simulation -- the O5 fall arc happens to
// equal the latch's -- and no rule checked it on a route.  bd_pipe now
// carries a request line on every internal boundary (SDELAY, one element by
// default), and verify/tighten.py rule I sizes it from the route.
//
// bd_mem handles its own boundary with an explicit DSETUP line.  For any
// other edge-sampling consumer, DELAY inserts a matched line on req_out.
// DELAY defaults to 0, which is the cell the design review costs:
// zero extra LUTs, identical to the frozen specification.  Set it only at a
// boundary that needs it, size it from the measured lead at that depth, and
// tighten it post-route like every other matched line.
//
// ---------------------------------------------------------------------------
// ack_in FALLS BEFORE THE LATCH HAS CLOSED.  Also measured.
//
// The node drives W/2 latch enables and the acknowledge from the same pin,
// and on a routed 32-bit link the enable net reaches its last latch 1125 ps
// after its first (150 ps) while the acknowledge is already on its way to
// the sender.  A sender that releases data the moment ack falls -- which the
// protocol allows -- puts the next value on a latch that is still
// transparent.  Routed GLS of the fused xorshift kernel returned token 1 with
// two bits corrupted for exactly this reason; the stalled testbench had
// hidden it because it never released data within a nanosecond of ack-fall.
//
// DACK holds ack_in's FALL back by that many elements (bd_delay FASTRISE: the
// rise still flushes in one hop, so the forward handshake is untouched).
// verify/tighten.py rule H sizes it: the earliest the released data can reach
// a latch input, against the latest the enable falls.  For a link fed from
// inside the design that path runs through the sender's own controller and
// latch, and is often long enough on its own; a bd_pipe stage gets exactly
// that much credit from the stage before it and no more, so every stage of
// a pipe carries the line, sized by the same rule.  A link fed straight from
// a pin has no credit at all and is where DACK is largest.
// ---------------------------------------------------------------------------

`default_nettype none

// -- one stage's controller ------------------------------------- 1 LUT6 ----
module bd_link_ctl (input wire req_in, input wire c_next, input wire rst,
                    output wire c);
    bd_c2n u (.a(req_in), .b(c_next), .rst(rst), .q(c));
endmodule

// -- one pipeline stage: controller + latch -------- 1 LUT + W/2 LUTs -------
module bd_link #(parameter W = 8, parameter integer DELAY = 0,
                 parameter integer DACK = 0)
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

    // The node drives three things.  req_out may need padding at an
    // edge-sampling boundary; ack_in may need its fall held back until the
    // enable has reached every latch bit.  Both default to the bare node.
    bd_delay #(.N(DELAY)) rdly (.a(c), .z(req_out));
    bd_delay #(.N(DACK), .FASTRISE(1)) uack (.a(c), .z(ack_in));
endmodule

// -- N stages ---------------- N*(1 + DACK) + (N-1)*SDELAY + N*W/2 LUTs -------
// A chain of bd_links.  DELAY pads the pipeline's own outgoing request;
// SDELAY pads each internal one (see the header: the stage must not close
// before its data has crossed the latch in front of it).  DACK is per stage,
// because each stage's enable has its own fanout to close before the stage
// in front of it may reopen.
module bd_pipe #(parameter W = 8, parameter N = 2, parameter integer DELAY = 0,
                 parameter integer SDELAY = 1, parameter integer DACK = 0)
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
        bd_link #(.W(W), .DELAY(DELAY), .DACK(DACK)) u (
            .rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
            .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
    end else begin : many
        wire [N:0] r, a;                  // r[k] into stage k, a[k] out of it
        wire [W*(N+1)-1:0] dat;
        assign r[0] = req_in;
        assign ack_in = a[0];
        assign a[N] = ack_out;
        assign req_out = r[N];
        assign dat[W-1:0] = data_in;
        assign data_out = dat[W*N +: W];
        for (i = 0; i < N; i = i + 1) begin : stage
            bd_link #(.W(W), .DELAY(i + 1 == N ? DELAY : SDELAY),
                      .DACK(DACK)) u (
                .rst(rst),
                .req_in(r[i]), .ack_in(a[i]), .data_in(dat[W*i +: W]),
                .req_out(r[i+1]), .ack_out(a[i+1]),
                .data_out(dat[W*(i+1) +: W]));
        end
    end
    endgenerate
endmodule

`default_nettype wire
