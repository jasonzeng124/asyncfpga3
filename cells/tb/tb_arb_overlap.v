// ---------------------------------------------------------------------------
// tb_arb_overlap.v -- the grant-overlap margin in bd_arbcell, both timing
// regimes, and the width discriminator that separates a structural overlap
// from a real one.
//
// WHAT THIS BENCH ASSERTS
//
//   1. In the routed regime (BD_ROUTE_PS >= 50) an unmodified bd_arbcell
//      driven by two free-running, non-commensurate stimuli produces NO
//      g1&g2 overlap at all.
//
//   2. In the arc-only regime (BD_ROUTE_PS = 0) an overlap does appear, and
//      it is narrow -- one link of delay filtering removes every instance.
//
// Both are checked, because the second is what makes the first meaningful:
// a bench that only ran in the routed regime would pass without ever
// exercising the hazard it claims the margin covers.
//
// WHY THE OVERLAP EXISTS AT ALL.  Both grants read the same q, so when q
// toggles one grant must fall while the other rises.  On this fabric a LUT
// falls about 2.5x slower than it rises (prjxray: O5 rise 55 / fall 152,
// O6 rise 56 / fall 124 -- see sim/bd_prims_sim.v), so with cell arcs alone
// the falling grant is still high when the rising one arrives and g1&g2 is
// briefly true.  Interconnect delays both edges equally, so it does not
// widen the overlap; it moves the whole decode past it.  That is the
// "margin only routing supplies" bd_arb.v's header warns about, measured
// here rather than asserted.
//
// WHAT THIS BENCH DOES NOT SHOW.  Metastability.  A LUT here resolves in one
// arc, always (see bd_prims_sim.v's header).  Every overlap counted below is
// an ordinary digital hazard, and that is exactly why the width filter can
// be calibrated against it: everything this bench counts is the thing the
// filter must reject.  The rate at which a REAL metastable excursion
// survives that filter is a hardware measurement -- see verify/MTBF.md and
// hw/arb_mtbf.v -- and nothing here discharges it.
// ---------------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module tb_arb_overlap;

    // Two free-running stimuli at the hardware rig's measured ratio.
    // Deliberately not commensurate, so relative phase sweeps the whole
    // offset window rather than sampling one point in it.
    reg r1 = 1'b0, r2 = 1'b0;
    always #4108 r1 = ~r1;
    always #5461 r2 = ~r2;

    // The library cell, unmodified: nothing delayed, nothing added.
    wire g1, g2;
    bd_arbcell udut (.r1(r1), .r2(r2), .rst(1'b0), .g1(g1), .g2(g2));
    wire overlap = g1 & g2;

    // Width discriminator: an overlap survives only if it is still true one
    // link later.  (* keep *) matters on silicon, where an optimiser would
    // otherwise notice that a & delay(a) is "just a"; harmless here.
    wire ov_d, ov_filtered;
    bd_delay #(.N(1)) ufd (.a(overlap), .z(ov_d));
    LUT2 #(.INIT(4'h8)) ufa (.I0(overlap), .I1(ov_d), .O(ov_filtered));

    // Settle past the x-propagation at t=0 before counting anything: q comes
    // up unknown by construction and its first resolution is not an event.
    localparam time SETTLE = 60000;
    localparam time RUN    = 2000000;

    integer n_raw = 0, n_flt = 0;
    time    t_rise, w_min = 1000000, w_max = 0;

    always @(posedge overlap) if ($time > SETTLE) begin
        n_raw  = n_raw + 1;
        t_rise = $time;
    end
    always @(negedge overlap) if ($time > SETTLE && n_raw > 0) begin
        if ($time - t_rise < w_min) w_min = $time - t_rise;
        if ($time - t_rise > w_max) w_max = $time - t_rise;
    end
    always @(posedge ov_filtered) if ($time > SETTLE) n_flt = n_flt + 1;

    integer fail;
    initial begin
        #(RUN);
        fail = 0;

        $display("");
        $display("tb_arb_overlap: BD_ROUTE_PS=%0d, %0t ps of free-running stimulus",
                 `BD_ROUTE_PS, RUN);
        $display("  raw g1&g2 overlaps      : %0d", n_raw);
        if (n_raw > 0)
            $display("  overlap width           : %0t to %0t ps", w_min, w_max);
        $display("  surviving 1-link filter : %0d", n_flt);
        $display("");

        if (`BD_ROUTE_PS == 0) begin
            // Arc-only: the hazard must appear, or the bench is not
            // exercising what it claims to.
            if (n_raw == 0) begin
                $display("  FAIL: no overlap in the arc-only regime -- this bench");
                $display("        is no longer exercising the hazard it checks.");
                fail = 1;
            end else begin
                $display("  ok: hazard present with cell arcs alone (%0d)", n_raw);
            end
            // ...and one link of filtering must remove all of it.
            if (n_flt != 0) begin
                $display("  FAIL: %0d overlap(s) survived a one-link filter --", n_flt);
                $display("        wider than a fixed arc delta can explain.");
                fail = 1;
            end else begin
                $display("  ok: every overlap rejected by a one-link filter");
            end
        end else begin
            // Routed: the margin must hold outright.
            if (n_raw != 0) begin
                $display("  FAIL: %0d grant overlap(s) with routing delay --", n_raw);
                $display("        the exclusion margin does NOT hold.");
                fail = 1;
            end else begin
                $display("  ok: no grant overlap at all in the routed regime");
            end
        end

        $display("");
        if (fail) $display("tb_arb_overlap FAIL");
        else      $display("tb_arb_overlap PASS");
        $finish;
    end
endmodule

`default_nettype wire
