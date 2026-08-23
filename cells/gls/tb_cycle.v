// ---------------------------------------------------------------------------
// tb_cycle.v -- drive the routed gcd_hw netlist and log a timestamped
// transition trace of the loop ring, for measuring one iteration's period
// and where the time inside it goes (Q1-Q3 of the per-iteration cost
// breakdown).
//
// Structurally identical to tb_run.v (same two external steps: start the
// housekeeping ring, force the vector) -- see that file's header for why
// each is legitimate.  The only difference is what gets recorded: instead of
// lap/err/ok counters, cycle.vh's always-blocks $fdisplay every transition of
// every probed net (loop-ring channels + delay-chain taps) with its
// timestamp, bounded to the [+TLO, +THI] window so the trace file stays a
// function of the window asked for, not of the whole run.
// ---------------------------------------------------------------------------
`timescale 1ps/1ps

module tb_cycle;

`include "cycle.vh"

    top dut ();

    `include "signals.vh"   // route-specific wire numbers, from gen_signals.py

    integer vec, tend, tlo, thi;
    integer laps, hk_edges;
    time    t_last_lap, t_rst_rel, t_first_lap;
    reg     annotate;

    initial begin
        vec = 6; tend = 40000; tlo = 0; thi = 40000000; annotate = 0;
        if ($value$plusargs("VEC=%d", vec))   ;
        if ($value$plusargs("TEND=%d", tend)) ;   // ns, sim end
        if ($value$plusargs("TLO=%d", tlo))   ;   // ns, trace window start
        if ($value$plusargs("THI=%d", thi))   ;   // ns, trace window end
        if ($value$plusargs("ANNOTATE=%d", annotate)) ;
        y_t0 = tlo * 1000; y_t1 = thi * 1000;
        if (annotate) begin
            $sdf_annotate("annot.sdf", dut);
            $display("# sdf annotate done");
        end
        $display("# VEC=%0d TEND=%0dns TRACE=[%0d,%0d]ns", vec, tend, tlo, thi);
        force `IDX0 = vec[0];
        force `IDX1 = vec[1];
        force `IDX2 = vec[2];
        force `IDX3 = vec[3];
    end

    initial begin
        force `HK_FB = 1'b0;
        #50000;
        release `HK_FB;
        $display("# t=%0t ring released", $time);
    end

    initial begin laps = 0; hk_edges = 0;
                  t_last_lap = 0; t_first_lap = 0; t_rst_rel = 0; end

    always @(posedge `HK_CK) hk_edges = hk_edges + 1;

    always @(negedge `RIG_RST) begin
        t_rst_rel = $time;
        $display("# t=%0t rig reset released (por_done=%b, hk edges=%0d)",
                 $time, `POR_DONE, hk_edges);
    end

    always @(posedge `RIG_LAP) begin
        laps = laps + 1;
        if (laps == 1) t_first_lap = $time;
        t_last_lap = $time;
        $display("LAP %0d t=%0t", laps, $time);
    end

    initial begin
        forever begin
            #1000000;
            if ($time > tend * 1000) begin
                $display("SUMMARY vec=%0d laps=%0d t_end=%0t t_rst_rel=%0t t_first_lap=%0t t_last_lap=%0t",
                          vec, laps, $time, t_rst_rel, t_first_lap, t_last_lap);
                y_close;
                $display("# cycle_trace.txt written");
                $finish;
            end
        end
    end
endmodule
