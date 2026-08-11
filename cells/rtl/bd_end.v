// ---------------------------------------------------------------------------
// bd_end.v -- the two endpoints of a dataflow graph.
//
//     source     req = ~ack        a constant, offered forever
//     sink       ack = req         accept everything, keep nothing
//
// Both are one line, and both are exactly right, which is the reason they are
// worth a file rather than a comment somewhere.  A four-phase channel is a
// ring: req^ ack^ req_ ack_.  Close the ring on itself with an inversion and
// it free-runs at whatever rate the far end can take; close it without one and
// it mirrors, which is precisely "I accepted that".
//
// Names.  sim/bd_env.v already has bd_source and bd_sink -- the BENCH models,
// which sequence a scripted list of values and record what arrived.  These are
// the synthesisable endpoints and are deliberately named differently, because
// they are not the same thing and a bench that reaches for the wrong one
// should not compile.
//
// ---------------------------------------------------------------------------
// WHY THE INVERTER IS AN INSTANTIATED LUT1 AND NOT `assign req = ~ack`
//
// The library is simulated from rtl/ directly, so an `assign` here would be a
// zero-delay inversion sitting in a combinational loop through the consumer:
// the source would raise and drop its request forever inside one timestep and
// the simulator would never advance.  The LUT1 model in sim/bd_prims_sim.v
// carries the real 56/124 ps arc, so the ring runs at a finite rate and the
// bench can watch it.  Every other loop in this library is a C-element and got
// its delay for free by being a primitive; this one has to ask for it.
//
// That inverter is also a real combinational loop on the fabric.  It needs the
// keep attribute and nextpnr's --ignore-loops, same as every C-element -- and
// it will appear in tighten.py's state-node census as a loop.  It is the one
// loop in the library that is NOT storage: nothing is remembered, the ring
// just turns.  If a census number ever has to be explained, this is why it can
// exceed the count of latches and C-elements.
//
// ---------------------------------------------------------------------------
// THE TURNAROUND FLOOR
//
// This cell settles a question left open in verify/attempts/bd_deco_attempt.v.
// The semi-decoupled controller was measured against a swept sender turnaround
// and held its data at every value down to 60 ps, collapsing only at exactly
// zero -- which the bench model bd_source produces, because it drops req in
// the same timestep it sees ack.  The note there argued that zero is not
// physical.  bd_src is the argument made concrete: the real source's
// turnaround is one LUT arc, 56 ps rising through 124 ps falling before any
// routing at all, and routing roughly triples it.
//
// The general form is stronger than this one cell.  Every producer in this
// library derives its request from the consumer's acknowledge through at least
// one LUT -- a Muller stage's request IS a C-element with ack on a pin -- so
// the library has a structural turnaround floor of one arc, everywhere.  Zero
// is not a value any of these cells can present to another.
//
// ---------------------------------------------------------------------------
// BUNDLING
//
// bd_src takes no matched delay and needs none, which is unique to it.  The
// bundling obligation is that data is stable from req-rise to ack-fall; this
// data is stable from configuration to power-down.  A source of something that
// MOVES is not this cell -- it is a compute unit, or a memory port, and it
// pays for its delay like everything else.
//
// ---------------------------------------------------------------------------
// COST
//
// The sink is free: a wire, zero LUTs, and the unread data port is wiring that
// the emitter does not have to special-case.
//
// The source is one LUT as written, and a compiler should expect to get it
// back.  ~ack folds into whatever consumes req -- a join's C-element has the
// acknowledge on a pin already and can absorb the inversion by complementing
// its constant, for no cells at all.  That is a peephole for Stage 2, not
// something to build into the cell: a cell that is only correct once it has
// been optimised away is worse than a cell that costs one LUT.
// ---------------------------------------------------------------------------

`default_nettype none

// -- constant source: offers VAL, forever, as fast as the consumer takes it --
module bd_src #(parameter W = 8, parameter [W-1:0] VAL = {W{1'b0}})
    (output wire         req,
     input  wire         ack,
     output wire [W-1:0] data);

    (* keep *) LUT1 #(.INIT(2'h1)) u (.I0(ack), .O(req));
    assign data = VAL;
endmodule

// -- sink: accept every transaction immediately, discard the datum ----------
module bd_snk #(parameter W = 8)
    (input  wire         req,
     output wire         ack,
     input  wire [W-1:0] data);

    assign ack = req;
    // data is deliberately unread.  The port exists so a channel is a channel
    // everywhere and the emitter has one shape to emit.
endmodule

`default_nettype wire
