// tb_end.v -- the two endpoints, and the one thing that is surprising about
// them.
//
// A source is req = ~ack and a sink is ack = req.  Neither has any internal
// state, so there is no logic here to get wrong; what this bench is actually
// for is the two facts that only show up once the endpoints are wired to
// something:
//
//   A  bd_src has no reset pin and does not need one -- but it does need its
//      CONSUMER to define the acknowledge at power-up.  ~x is x.  A source
//      whose acknowledge never leaves x never starts, in simulation.  On
//      silicon an inverter ring always starts; a simulator is stricter, and
//      here that strictness is telling the truth about a real obligation:
//      every bd_src in a design must sit behind something that resets.
//
//   C  closed on a bare sink the pair is a ring oscillator with nothing to
//      define it, and it has to be kicked before it will run.  Its period is
//      then the round trip -- one rising arc plus one falling arc -- which is
//      measured here against the model rather than asserted, and which is the
//      simulation-scale rehearsal of the ring-oscillator calibration this
//      library still owes itself on real silicon.

`timescale 1ps / 1ps

module tb_end;

    localparam integer T = 12 * `BD_HOP_PS;
    localparam [7:0] VAL = 8'hA5;

    integer errors = 0;
    integer i, n0;

    // -- A: bd_src into the bench sink --------------------------------------
    // The bench sink's ack is a reg initialised to 0, which is what gives the
    // ring its starting value.  That is the resetting consumer, standing in
    // for the C-element a real graph would put here.
    wire        a_rq, a_ak;
    wire [7:0]  a_d;

    bd_src  #(.W(8), .VAL(VAL)) asrc (.req(a_rq), .ack(a_ak), .data(a_d));
    bd_sink #(.W(8))            asnk (.req(a_rq), .ack(a_ak), .data(a_d));

    // SETTLE 0: this datum is a tie-off and cannot move, so the hold window is
    // met by construction.  bd_src is the only cell in the library entitled to
    // say that.
    bd_monitor #(.W(8), .CHAN("src-out")) ma (.req(a_rq), .ack(a_ak), .data(a_d));

    // -- B: the bench source into bd_snk ------------------------------------
    wire        b_rq, b_ak;
    wire [7:0]  b_d;

    bd_source #(.W(8)) bsrc (.req(b_rq), .ack(b_ak), .data(b_d));
    bd_snk    #(.W(8)) bsnk (.req(b_rq), .ack(b_ak), .data(b_d));

    // No monitor on this channel, and that is a statement about bd_snk rather
    // than a gap.  Its acknowledge is a wire, so ack rises in the same
    // timestep as req and the two events carry the same timestamp; nothing can
    // order them, and a protocol monitor is exactly a thing that orders them.
    // The cell is still correct -- a wire cannot acknowledge a request that
    // has not arrived -- but it is worth knowing that a bare sink is the one
    // consumer in the library that answers in zero arcs, and that anything
    // written to assume its acknowledge is late will not find out here.

    // -- C: the ring --------------------------------------------------------
    wire        c_rq, c_ak;
    wire [7:0]  c_d;

    bd_src #(.W(8), .VAL(8'h3C)) csrc (.req(c_rq), .ack(c_ak), .data(c_d));
    bd_snk #(.W(8))              csnk (.req(c_rq), .ack(c_ak), .data(c_d));

    integer nedge = 0;
    time    t_now = 0, t_prev = 0;
    always @(posedge c_rq) begin
        t_prev = t_now;
        t_now  = $time;
        nedge  = nedge + 1;
    end

    // One turn of the ring is the inverter's rising arc plus its falling arc.
    // Both come from sim/bd_prims_sim.v, which takes them from prjxray.
    localparam integer PERIOD = (56 + `BD_ROUTE_PS) + (124 + `BD_ROUTE_PS);

    initial begin
        $display("tb_end");
        #(4 * T);
        // Arm on a phase boundary, not on a wall-clock delay.  Every other
        // channel in the library is idle between the bench's sends, so arming
        // after a settle time lands between transactions by default.  This one
        // is never idle -- a free-running source has no gap -- so the arm has
        // to be anchored, and ack-fall is the start of a cycle.
        @(negedge a_ak);
        ma.arm;

        // A: it started on its own, because its consumer defined the ack.
        n0 = asnk.n;
        #(200 * T);
        if (asnk.n <= n0) begin
            errors = errors + 1;
            $display("  FAIL bd_src did not free-run against a resetting consumer");
        end
        for (i = 0; i < asnk.n; i = i + 1)
            if (asnk.seen[i] !== VAL) begin
                errors = errors + 1;
                $display("  FAIL transaction %0d carried %02x, expected %02x",
                         i, asnk.seen[i], VAL);
            end
        $display("  source free-ran %0d transactions, every one %02x",
                 asnk.n, VAL);

        // B: the sink takes everything offered, in order, without stalling.
        for (i = 0; i < 24; i = i + 1) bsrc.send(i[7:0]);
        if (bsrc.nsent != 24) begin
            errors = errors + 1;
            $display("  FAIL sink accepted %0d of 24", bsrc.nsent);
        end else
            $display("  sink accepted 24 of 24");

        // C: the bare ring is still stopped, and that is the point.
        if (nedge != 0) begin
            errors = errors + 1;
            $display("  FAIL the bare ring started itself -- x must not resolve here");
        end

        // Kick it.  Holding the request low defines the acknowledge, which
        // defines the request, and the ring turns from there.
        force c_rq = 1'b0;
        #(4 * T);
        release c_rq;
        #(200 * T);

        if (nedge < 4) begin
            errors = errors + 1;
            $display("  FAIL the ring did not run after the kick (%0d edges)", nedge);
        end else if (t_now - t_prev != PERIOD) begin
            errors = errors + 1;
            $display("  FAIL ring period %0d ps, model says %0d ps",
                     t_now - t_prev, PERIOD);
        end else
            $display("  ring period %0d ps over %0d turns, matching the modelled arcs (%0d + %0d)", t_now - t_prev, nedge, 56 + `BD_ROUTE_PS, 124 + `BD_ROUTE_PS);

        errors = errors + ma.errors;
        if (errors == 0) $display("tb_end PASS");
        else             $display("tb_end FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #20_000_000;
        $display("tb_end FAIL (timeout)");
        $finish;
    end
endmodule
