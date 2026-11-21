// ---------------------------------------------------------------------------
// tb_pipe.v -- shard C: the routed target (cells/gls netlist + nextpnr SDF, baked) under a
// PIPELINED environment at the kernel boundary.  Copied from cells/gls/tb_run.v (ring kick,
// observation, watchdog) and changed only in the environment:
//
//  * gcd_rig's env node env_c (the ONE request of a, b, start: bd_fork) is forced by this
//    testbench instead of uenv1.  It is low until 20 ns after the rig's reset releases.
//  * Offer 1: idx = +V1 (default 9), env_c rises; when in_ack rises, env_c falls; when in_ack
//    falls the handshake of pair 1 is complete.
//  * PIPE=1 (default): idx := +V2 (default 4) at once, then +SU ps (default 2000) later env_c
//    rises again (pair 2), falls after in_ack rises, and stays low after in_ack falls.
//    PIPE=0 (control): the same, but pair 2 is offered only after the first lap (res_req
//    rise) has been acknowledged and has fallen: the sequential environment.
//  * out0's acknowledge (env_c0 = uenv0 = C(res_req, !env_c)) is left as built.
//
// The rig's comparator compares out0 with the expected gcd of the CURRENT idx; idx is V2 from
// the moment pair 2 is offered.  So with V1 = 9 (gcd 4096) and V2 = 4 (gcd 1): lap 1 with
// mism = 0 means the first result is 1 = pair 2's gcd (REORDERED); in order is lap 1 mism = 1
// (4096 vs 1), lap 2 mism = 0.
// ---------------------------------------------------------------------------
`timescale 1ps/1ps

module tb_pipe;
`ifdef PROBE
`include "probe.vh"   // cells/gls gen_probe.py: last transition of every node
`endif

    top dut ();
    `include "signals.vh"
    `define IN_ACK dut.n144588   // urig.in_ack (nets.map of the target route)

    integer v1, v2, su, pipe, tend, quiet_ns;
    integer laps, hk_edges;
    time    t_last_lap, t_rst_rel;
    reg     rst_seen;

    initial begin
        v1 = 9; v2 = 4; su = 2000; pipe = 1; tend = 400000; quiet_ns = 100000;
        if ($value$plusargs("V1=%d", v1)) ;
        if ($value$plusargs("V2=%d", v2)) ;
        if ($value$plusargs("SU=%d", su)) ;
        if ($value$plusargs("PIPE=%d", pipe)) ;
        if ($value$plusargs("TEND=%d", tend)) ;
        if ($value$plusargs("QUIET=%d", quiet_ns)) ;
        $display("# V1=%0d V2=%0d PIPE=%0d SU=%0dps TEND=%0dns", v1, v2, pipe, su, tend);
        force `IDX0 = v1[0]; force `IDX1 = v1[1]; force `IDX2 = v1[2]; force `IDX3 = v1[3];
        force `ENV_C = 1'b0;
    end

    initial begin
        force `HK_FB = 1'b0;
        #50000;
        release `HK_FB;
    end

    initial begin laps = 0; hk_edges = 0; t_last_lap = 0; t_rst_rel = 0; rst_seen = 0; end
    always @(posedge `HK_CK) hk_edges = hk_edges + 1;
    always @(negedge `RIG_RST) begin t_rst_rel = $time; rst_seen = 1;
        $display("# t=%0t rig reset released", $time); end

    always @(posedge `RIG_LAP) begin
        laps = laps + 1; t_last_lap = $time;
        #100;   // read the comparator inside the padded valid window
        $display("LAP %0d t=%0t mism=%b idx=%b%b%b%b", laps, $time, `MISM, `IDX3, `IDX2, `IDX1, `IDX0);
    end
    always @(`IN_ACK) $display("# t=%0t in_ack=%b", $time, `IN_ACK);
    always @(`ENV_C) $display("# t=%0t env_c=%b", $time, `ENV_C);

    // ---- the environment ----------------------------------------------------
    initial begin
        wait (rst_seen === 1'b1);
        #20000;
        force `ENV_C = 1'b1;                     // offer 1
        wait (`IN_ACK === 1'b1); #100 force `ENV_C = 1'b0;
        wait (`IN_ACK === 1'b0);
        $display("PAIR1-ACCEPTED t=%0t", $time);
        if (pipe == 0) begin
            wait (laps >= 1); wait (`RIG_LAP === 1'b0);
            $display("# t=%0t first result acknowledged (sequential env)", $time);
        end
        force `IDX0 = v2[0]; force `IDX1 = v2[1]; force `IDX2 = v2[2]; force `IDX3 = v2[3];
        #(su);
        force `ENV_C = 1'b1;                     // offer 2
        $display("PAIR2-OFFERED t=%0t laps=%0d", $time, laps);
        wait (`IN_ACK === 1'b1); #100 force `ENV_C = 1'b0;
        wait (`IN_ACK === 1'b0);
        $display("PAIR2-ACCEPTED t=%0t laps=%0d", $time, laps);
    end

    // ---- watchdog -------------------------------------------------------------
    initial begin
        forever begin
            #1000000;
            if (t_rst_rel != 0 && ($time - t_rst_rel) > quiet_ns*1000 && ($time - t_last_lap) > quiet_ns*1000) begin
                $display("RESULT quiet: laps=%0d last lap t=%0t, nothing for %0t", laps, t_last_lap, $time - t_last_lap);
`ifdef PROBE
                dump_probe(0); $display("# probe_last.txt written");
`endif
                $finish;
            end
            if ($time > tend*1000) begin
                $display("RESULT timeout: laps=%0d", laps); $finish;
            end
        end
    end
endmodule
