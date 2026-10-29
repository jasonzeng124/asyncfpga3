// ---------------------------------------------------------------------------
// tb_run.v -- drive the routed gcd_hw netlist and report what it does.
//
// The design is self-driving: gcd_hw.v's own window sequencer, power-on reset
// and housekeeping ring are all in the netlist.  Two things have to be done
// from outside anyway.
//
// 1. START THE RING.  The housekeeping ring oscillator is a bd_delay chain
//    closed by an inverter, and it has no defined initial state: every LUT in
//    it comes up x, ~x is x, and it never starts.  On silicon it starts from
//    noise; in a four-state simulator it cannot.  So one node in the ring is
//    forced to a definite value for long enough for the whole chain to carry a
//    definite value (17 links, ~800 ps each, so 50 ns is ample) and then
//    released.  That is a simulation-setup step, not a design property -- the
//    force is on ONE node, it is released before anything is measured, and
//    nothing else in the design is touched.
//
// 2. CHOOSE THE VECTOR.  idx is advanced by gcd_hw's window sequencer at
//    win_edge, which is a 16-bit counter of housekeeping cycles: ~65536 * 14 ns
//    ~= 900 us of simulated time per window, and 16 windows is ~15 ms.  That is
//    not reachable here.  idx comes up 0 and holds, so vector 0 needs nothing;
//    any other vector is selected by forcing the four idx flop outputs, which
//    is exactly what the sequencer would have left them at and is legitimate
//    because gcd_rig's contract is that idx changes only under reset -- and the
//    force is applied before the design's own reset releases.
//
// Everything else -- reset, settling, the whole four-phase ring -- runs as
// built.
// ---------------------------------------------------------------------------
`timescale 1ps/1ps

module tb_run;

    // per-node last-transition timestamps, for locating a wedge
`include "probe.vh"


    top dut ();

    // ---- named nets, from nets.map (the routed JSON's own net names) --------
    // hk_fb    invhk/O6, the housekeeping ring's feedback node
    // hk_ck    the BUFG output that clocks every flop in the design
    // rig_lap  gcd_rig's res_req: one rise per delivered gcd
    // rig_err / rig_ok    the width-filtered verdicts
    // env_c0 / env_c      the two env C-elements that close the kernel's ring
    `include "signals.vh"   // route-specific wire numbers, from gen_signals.py

    integer vec, tend, quiet_ns, i;
    integer laps, errs, oks, hk_edges;
    time    t_last_lap, t_rst_rel, t_first_lap;
    reg     annotate;

    initial begin
        vec = 0; tend = 2000000; quiet_ns = 200000; annotate = 0;
        if ($value$plusargs("VEC=%d", vec))        ;
        if ($value$plusargs("TEND=%d", tend))      ;  // ns
        if ($value$plusargs("QUIET=%d", quiet_ns)) ;  // ns
        if ($value$plusargs("ANNOTATE=%d", annotate)) ;
        if (annotate) begin
            $sdf_annotate("annot.sdf", dut);
            $display("# sdf annotate done");
        end
        $display("# VEC=%0d TEND=%0dns QUIET=%0dns", vec, tend, quiet_ns);
        // ---- select the vector, in the SAME initial block that read it, so
        // the ordering of the two is not left to the scheduler.  This lands at
        // time 0, long before the design's own reset releases.
        force `IDX0 = vec[0];
        force `IDX1 = vec[1];
        force `IDX2 = vec[2];
        force `IDX3 = vec[3];
    end

    // ---- 2. kick the housekeeping ring -------------------------------------
    initial begin
        force `HK_FB = 1'b0;
        #50000;                 // 50 ns: 17 chain links at ~0.8 ns each
        release `HK_FB;
        $display("# t=%0t ring released", $time);
    end

    // ---- observation -------------------------------------------------------
    initial begin laps = 0; errs = 0; oks = 0; hk_edges = 0;
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
        if (laps <= 8 || laps % 100 == 0)
            $display("LAP %0d t=%0t mism=%b", laps, $time, `MISM);
    end
    always @(posedge `RIG_ERR) begin
        errs = errs + 1;
        if (errs <= 4) $display("ERR t=%0t lap=%0d", $time, laps);
    end
    always @(posedge `RIG_OK) begin
        oks = oks + 1;
        if (oks <= 4) $display("OK  t=%0t lap=%0d", $time, laps);
    end

    // ---- watchdog ----------------------------------------------------------
    // A four-phase ring that wedges simply stops producing events, so the
    // interesting number is when the last one happened, not whether the
    // simulator exits.
    integer last_hk, stuck_ns;
    initial begin
        last_hk = 0; stuck_ns = 0;
        forever begin
            #1000000;                       // 1 us of simulated time
            $display("# t=%0t hk=%0d laps=%0d errs=%0d oks=%0d rst=%b lastlap=%0t",
                     $time, hk_edges, laps, errs, oks, `RIG_RST, t_last_lap);
            if (hk_edges == last_hk) begin
                $display("RESULT ring-stopped: housekeeping oscillator dead at t=%0t", $time);
                summarise; $finish;
            end
            last_hk = hk_edges;
            if (t_rst_rel != 0 && ($time - t_last_lap) > quiet_ns*1000
                && ($time - t_rst_rel) > quiet_ns*1000) begin
                $display("RESULT deadlock: vec=%0d laps=%0d last lap at t=%0t, quiet for %0t",
                         vec, laps, t_last_lap, $time - t_last_lap);
                dump_probe(0);
                $display("# probe_last.txt written");
                summarise; $finish;
            end
            if ($time > tend*1000) begin
                $display("RESULT timeout: vec=%0d laps=%0d errs=%0d oks=%0d",
                         vec, laps, errs, oks);
                dump_probe(0);
                summarise; $finish;
            end
        end
    end

    task summarise;
        $display("SUMMARY vec=%0d laps=%0d errs=%0d oks=%0d hk=%0d t_end=%0t t_rst_rel=%0t t_first_lap=%0t t_last_lap=%0t",
                 vec, laps, errs, oks, hk_edges, $time,
                 t_rst_rel, t_first_lap, t_last_lap);
    endtask
endmodule
