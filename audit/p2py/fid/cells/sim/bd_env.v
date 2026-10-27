// ---------------------------------------------------------------------------
// bd_env.v -- a four-phase source and sink for the testbenches, and the
// protocol monitor that watches every channel they drive.
//
// The monitor is the point.  A testbench that only checks values will pass a
// cell that acknowledges too early or releases data too soon, and those are
// the two mistakes this library is built around.  bd_monitor asserts, on
// every channel it is attached to:
//
//   P1  req and ack complete a full four-phase cycle in order
//       (req^, ack^, req_, ack_) with no phase skipped or repeated
//   P2  data is stable across the whole hold window req^ -> ack_
//   P3  the sender does not raise a new request before ack has returned to
//       zero
// ---------------------------------------------------------------------------

`timescale 1ps / 1ps

// -- four-phase sender ------------------------------------------------------
module bd_source #(parameter W = 8, parameter integer SETUP = 3000)
    (output reg req, input wire ack, output reg [W-1:0] data);

    integer nsent;
    initial begin req = 1'b0; data = {W{1'b0}}; nsent = 0; end

    // Data first, then the request: the matched-delay obligation, met in the
    // testbench by construction.  Data is not touched again until the next
    // send, so it holds past ack-fall.
    task send(input [W-1:0] v);
    begin
        data = v;
        #SETUP;
        req = 1'b1;
        wait (ack === 1'b1);
        req = 1'b0;
        wait (ack === 1'b0);
        nsent = nsent + 1;
    end
    endtask

    // Raise the request and return without waiting -- for testing a cell that
    // is supposed to leave a token untaken.
    task offer(input [W-1:0] v);
    begin
        data = v;
        #SETUP;
        req = 1'b1;
    end
    endtask

    task retract;
    begin
        req = 1'b0;
        wait (ack === 1'b0);
        nsent = nsent + 1;
    end
    endtask
endmodule

// -- four-phase receiver ----------------------------------------------------
module bd_sink #(parameter W = 8, parameter integer HOLD = 2000)
    (input wire req, output reg ack, input wire [W-1:0] data);

    reg [W-1:0] seen [0:255];
    integer n;
    reg stall;

    initial begin ack = 1'b0; n = 0; stall = 1'b0; end

    always begin
        wait (req === 1'b1 && stall === 1'b0);
        #HOLD;
        seen[n] = data;
        n = n + 1;
        ack = 1'b1;
        wait (req === 1'b0);
        #HOLD;
        ack = 1'b0;
    end
endmodule

// -- protocol monitor -------------------------------------------------------
// Call arm() once the channel has settled out of x.  Before that the monitor
// is deaf: a LUT feedback loop resolving from x produces real Verilog edges
// that are not protocol events, and counting them would bury the real ones.
//
// SETTLE is the one concession to physics.  At a Muller stage's output the
// request is the C-element node itself and the data is that node through a
// latch, so the request necessarily leads its own data by one LUT arc -- see
// the header of rtl/bd_link.v, and verify/probes/link_skew.v for the
// measurement.  SETTLE
// is how long after req-rise data may still be moving before the monitor
// counts it as a hold-window violation.  Leave it at 0 on any channel driven
// by a testbench source, where data genuinely precedes the request; set it to
// a couple of arcs on a channel driven by a pipeline output.  It is a
// tolerance on arrival skew, not a licence to move data mid-window: a change
// even one picosecond past SETTLE still fails.
// EARLY_RELEASE weakens P2 from "stable to ack-fall" to "stable to ack-rise".
// That is not a convenience: it is a different contract, and the only cells
// entitled to it are the ones that say so in their own header.  A decoupled
// pipeline stage releases its output the moment the consumer acknowledges,
// because that is exactly what buys it the extra token -- so its output
// channel can feed a consumer that captures by ack-rise and nothing else.
// Leave this at 0 everywhere else; a cell that needs it and has not earned it
// is a cell that will lose a token on somebody else's consumer.
module bd_monitor #(parameter W = 8, parameter CHAN = "?",
                    parameter integer SETTLE = 0,
                    parameter integer EARLY_RELEASE = 0)
    (input wire req, input wire ack, input wire [W-1:0] data);

    integer errors;
    reg [W-1:0] held;
    reg armed, go;
    time t_req;

    // state 0 idle, 1 req high, 2 req+ack, 3 ack high with req low
    reg [1:0] st;

    initial begin errors = 0; armed = 1'b0; go = 1'b0; st = 2'd0; t_req = 0; end

    task arm;
    begin
        go    = 1'b1;
        st    = 2'd0;
        armed = 1'b0;
    end
    endtask

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  [%0t] PROTOCOL %0s on channel %0s", $time, why, CHAN);
    end
    endtask

    // P1/P3: the phase order.
    always @(posedge req) if (go) begin
        if (st != 2'd0) fail("req rose out of phase");
        st    = 2'd1;
        held  = data;
        t_req = $time;
        armed = 1'b1;
    end
    always @(posedge ack) if (go) begin
        if (st != 2'd1) fail("ack rose out of phase");
        st = 2'd2;
        if (EARLY_RELEASE) armed = 1'b0;
    end
    always @(negedge req) if (go) begin
        if (st != 2'd2) fail("req fell out of phase");
        st = 2'd3;
    end
    always @(negedge ack) if (go) begin
        if (st != 2'd3) fail("ack fell out of phase");
        st    = 2'd0;
        armed = 1'b0;
    end

    // P2: the hold window ends at ack-fall, not req-fall.  This is the
    // property the whole library is shaped around, so it is checked on every
    // channel of every bench.
    always @(data)
        if (go && armed && ($time - t_req) > SETTLE)
            fail("data moved inside the hold window");
endmodule
