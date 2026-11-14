// ---------------------------------------------------------------------------
// tb_arb_overlap.v -- the grant-overlap margin in bd_arbcell, both timing
// regimes, and the width discriminator that separates a structural overlap
// from a real one.
//
// WHAT THIS BENCH ASSERTS (single-corner model, sim/bd_prims_sim.v)
//
//   1. In EVERY regime -- arc-only and routed, slow max and -DBD_FAST_MIN --
//      an unmodified bd_arbcell driven by two free-running, non-commensurate
//      stimuli produces NO g1&g2 overlap, over a run that is required to
//      contain at least MIN_FLIPS decisions (q toggles), so the absence is
//      not vacuous.
//
//   2. The one-link width filter rejects an injected overlap as wide as the
//      largest O5-versus-O6 arc difference in the model (W_HAZ, derived from
//      the macros: 28 ps at slow max, 3 ps at fast min), and PASSES one three
//      links wide.  Both halves are checked on a copy of the filter fed by a
//      synthetic pulse, because the cell itself (claim 1) no longer produces
//      anything for the filter to see.
//
// WHY THERE IS NO OVERLAP IN THIS MODEL.  Both grants read the same q, so
// when q toggles one grant must fall while the other rises.  But q toggles
// only once the losing request has already moved, and the grant of that
// request falls on the request itself (one arc), while the other grant rises
// only through q (two arcs: q, then the grant LUT).  At one corner the
// falling grant therefore leads by a whole arc -- 124 ps vs 124+150 at slow
// max, 44-45 vs 45+42..45 at fast min -- and interconnect adds to the
// two-arc path twice.  An earlier version of this bench REQUIRED an overlap
// arc-only (89 of them, 8-16 ps).  That came from reading prjxray's fast and
// slow corner bounds as rise and fall (56 vs 124/152): a fast-corner rise
// racing a slow-corner fall, which no single PVT point can produce.
//
// WHAT THE OVERLAP REALLY IS, AND WHY THIS BENCH CANNOT SHOW IT.  The
// transport per-pin model (cells/gls/fid_core.vh; research/data/fid/
// f3_model.md section 5) does show overlaps, 5-28 ps wide: O5 is up to 28 ps
// slower than O6 in the same site, which survives routing because routing
// delays both equally.  Every one was removed by the one-link filter.  The
// default model here is inertial (iverilog specify paths sample at fire and
// swallow a pulse narrower than the arc), so it cannot reproduce them; claim
// 1 is a statement about THIS model, not about silicon.  Claim 2 is what
// carries over: the filter rejects anything as wide as the O5/O6 delta.
//
// WHAT THIS BENCH DOES NOT SHOW.  Metastability.  A LUT here resolves in one
// arc, always (see bd_prims_sim.v's header).  The rate at which a REAL
// metastable excursion survives the filter is a hardware measurement -- see
// verify/MTBF.md and hw/arb_mtbf.v -- and nothing here discharges it.
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

    // Decisions actually made: the absence of overlap only means something
    // if q kept changing hands.
    integer n_flip = 0;
    always @(udut.q) if ($time > SETTLE) n_flip = n_flip + 1;
    localparam integer MIN_FLIPS = 100;

    // The filter, calibrated on injected pulses.  W_HAZ is the largest
    // |O5 - O6| arc difference the model has (per pin, from the macros); a
    // real same-site overlap is at most that wide.  W_WIDE is three links.
    function integer absdiff(input integer a, input integer b);
        absdiff = (a > b) ? a - b : b - a;
    endfunction
    function integer max2(input integer a, input integer b);
        max2 = (a > b) ? a : b;
    endfunction
    localparam integer W_HAZ = max2(1, max2(max2(
        max2(absdiff(`BD_LUT5_A1, `BD_LUT6_PS), absdiff(`BD_LUT5_A2, `BD_LUT6_PS)),
        max2(absdiff(`BD_LUT5_A3, `BD_LUT6_PS), absdiff(`BD_LUT5_A4, `BD_LUT6_PS))),
        absdiff(`BD_LUT5_A5, `BD_LUT6_PS)));
    localparam integer W_WIDE = 3 * `BD_T_RISE;

    reg  inj = 1'b0;
    wire inj_d, inj_f;
    bd_delay #(.N(1)) ucd (.a(inj), .z(inj_d));
    LUT2 #(.INIT(4'h8)) uca (.I0(inj), .I1(inj_d), .O(inj_f));
    integer n_inj_narrow = 0, n_inj_wide = 0, phase = 0;
    always @(posedge inj_f)
        if (phase == 1) n_inj_narrow = n_inj_narrow + 1;
        else if (phase == 2) n_inj_wide = n_inj_wide + 1;
    integer k;
    initial begin
        #(SETTLE);
        phase = 1;
        for (k = 0; k < 20; k = k + 1) begin
            inj = 1'b1; #(W_HAZ); inj = 1'b0; #(10 * W_WIDE);
        end
        phase = 2;
        for (k = 0; k < 20; k = k + 1) begin
            inj = 1'b1; #(W_WIDE); inj = 1'b0; #(10 * W_WIDE);
        end
        phase = 3;
    end

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

        $display("  q decisions (toggles)   : %0d (need >= %0d)", n_flip, MIN_FLIPS);
        $display("  injected %0d ps pulses passing the filter : %0d of 20 (must be 0)",
                 W_HAZ, n_inj_narrow);
        $display("  injected %0d ps pulses passing the filter : %0d of 20 (must be 20)",
                 W_WIDE, n_inj_wide);
        $display("");

        if (n_flip < MIN_FLIPS) begin
            $display("  FAIL: only %0d decisions -- the stimulus no longer exercises", n_flip);
            $display("        the handover, so 'no overlap' would be vacuous.");
            fail = 1;
        end
        // Claim 1: no overlap in this (inertial, single-corner) model, in any
        // regime.  See the header for why, and for what the transport model
        // shows instead.
        if (n_raw != 0) begin
            $display("  FAIL: %0d grant overlap(s) in the single-corner model --", n_raw);
            $display("        the falling grant no longer leads the rising one.");
            fail = 1;
        end else begin
            $display("  ok: no grant overlap over %0d decisions", n_flip);
        end
        if (n_flt != 0) begin
            $display("  FAIL: %0d overlap(s) survived a one-link filter --", n_flt);
            $display("        wider than a fixed arc delta can explain.");
            fail = 1;
        end
        // Claim 2: the filter rejects an O5/O6-delta-wide overlap and passes
        // a wide one.
        if (n_inj_narrow != 0) begin
            $display("  FAIL: the one-link filter passed %0d of 20 %0d ps pulses",
                     n_inj_narrow, W_HAZ);
            fail = 1;
        end else
            $display("  ok: the one-link filter rejects every %0d ps pulse", W_HAZ);
        if (n_inj_wide != 20) begin
            $display("  FAIL: the one-link filter passed only %0d of 20 %0d ps pulses",
                     n_inj_wide, W_WIDE);
            $display("        -- it is not a filter, it is a dead output.");
            fail = 1;
        end else
            $display("  ok: the one-link filter passes every %0d ps pulse", W_WIDE);

        $display("");
        if (fail) $display("tb_arb_overlap FAIL");
        else      $display("tb_arb_overlap PASS");
        $finish;
    end
endmodule

`default_nettype wire
