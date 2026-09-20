// tb_ctl.v -- the conformance suite every pipeline controller has to pass.
//
// This exists because of how the semi-decoupled attempt failed.  It looked
// right, it hit its occupancy target, its constant was elegant, and it was
// broken in a way that only showed up when a consumer took its time dropping
// an acknowledge.  That took a hand-trace and a parameter sweep to find.  It
// should have taken one run.
//
// So: every property that attempt violated, plus the ones the simple
// controller relies on, as a matrix over whatever controllers are in the tree.
// A candidate controller is conformant when it fills the row.
//
// -- the properties ----------------------------------------------------------
//
//   OCC   occupancy is what the controller claims, measured by stalling the
//         sink and counting what a free-running source completed.
//
//   FAST  data integrity against a brisk consumer.
//
//   SLOWA data integrity when the consumer is slow to ACKNOWLEDGE.  A
//         four-phase partner may take as long as it likes to say yes.
//
//   SLOWR data integrity when the consumer is slow to RELEASE -- slow to drop
//         its acknowledge after the request falls.  THIS IS THE ONE.  A
//         four-phase protocol may not bound how long a partner takes in any
//         phase, and this is the phase everybody forgets.  The attempt passes
//         everything else and dies here, because its latch closes on a signal
//         the consumer gates.
//
//   SLOWS data integrity when the SENDER is slow -- long setup, long gaps.
//
//   PROTO the four-phase order and the hold window on both channels, from
//         bd_monitor, against the review's contract (data stable to ack-FALL).
//
// Every stress is a DELAY, never a reordering: none of these rigs violate the
// protocol, they just take their time.  A controller that needs a partner to
// hurry is not a four-phase controller.
//
// -- one thing the sink is NOT allowed to do ---------------------------------
//
// It may not sample early.  A pipeline stage's request leads its own data --
// measured at 152 ps for one stage and 441 ps for four, see rtl/bd_link.v --
// so a consumer that latches a fixed short time after req-rise is reading
// mid-flight, and every controller in the tree "fails".  The first version of
// this bench sampled at 300 ps and produced exactly that: a matrix of failures
// that were the bench's fault.
//
// T_SAMPLE below is therefore derived from the library's own documented bound,
// N latch arcs plus a guardband, not chosen.  Sampling late is free; sampling
// early is a bug in the consumer, not in the controller.

`timescale 1ps / 1ps

// -- a consumer whose two phases can be slowed independently -----------------
// STALLED is a PARAMETER, not something a testbench pokes in.  It used to be
// poked: occ_rig assigned snk.stall from its own initial block, racing this
// module's initial, and Verilog does not order those.  It worked for two
// instances and silently did not for a third, which reported a pipe with no
// backpressure at all.  A race that only shows up on some instances is the
// worst kind of bench bug, so the knob is elaboration-time now.
module conf_sink #(parameter W = 8, parameter integer T_ACK = 300,
                   parameter integer T_REL = 300,
                   parameter integer STALLED = 0)
    (input wire req, output reg ack, input wire [W-1:0] data);
    reg [W-1:0] seen [0:255];
    integer n;
    reg stall;
    initial begin ack = 1'b0; n = 0; stall = (STALLED != 0); end
    always begin
        wait (req === 1'b1 && stall === 1'b0);
        #T_ACK;                       // slow to say yes
        seen[n] = data; n = n + 1;
        ack = 1'b1;
        wait (req === 1'b0);
        #T_REL;                       // slow to let go
        ack = 1'b0;
    end
endmodule

// -- one controller under one stress -----------------------------------------
module conf_rig #(parameter KIND = 0, parameter integer N = 4,
                  parameter integer W = 8, parameter integer TSU = 300,
                  parameter integer T_ACK = 300, parameter integer T_REL = 300,
                  parameter integer TOTAL = 20, parameter integer GAP = 0)
    (input wire rst, input wire go,
     output reg [15:0] wrong, output reg [15:0] delivered, output reg done);

    wire rq, ak, ro, ao;  wire [W-1:0] di, dout;

    bd_source #(.W(W), .SETUP(TSU)) src (.req(rq), .ack(ak), .data(di));
    generate
        if (KIND == 2) begin : g_deco
            bd_pipe_deco #(.W(W), .N(N)) dut (
                .rst(rst), .req_in(rq), .ack_in(ak), .data_in(di),
                .req_out(ro), .ack_out(ao), .data_out(dout));
        end else if (KIND == 1) begin : g_attempt
            bd_pipe_semi #(.W(W), .N(N)) dut (
                .rst(rst), .req_in(rq), .ack_in(ak), .data_in(di),
                .req_out(ro), .ack_out(ao), .data_out(dout));
        end else begin : g_simple
            bd_pipe #(.W(W), .N(N)) dut (
                .rst(rst), .req_in(rq), .ack_in(ak), .data_in(di),
                .req_out(ro), .ack_out(ao), .data_out(dout));
        end
    endgenerate
    conf_sink #(.W(W), .T_ACK(T_ACK), .T_REL(T_REL)) snk
        (.req(ro), .ack(ao), .data(dout));

    integer i;
    initial begin
        wrong = 0; delivered = 0; done = 1'b0;
        wait (go);
        for (i = 0; i < TOTAL; i = i + 1) begin
            src.send(8'h10 + i[7:0]);
            if (GAP) #GAP;
        end
        #(600 * (T_ACK + T_REL + TSU + 1));
        delivered = snk.n[15:0];
        for (i = 0; i < TOTAL; i = i + 1)
            if (snk.seen[i] !== (8'h10 + i[7:0])) wrong = wrong + 1;
        done = 1'b1;
    end
endmodule

// -- occupancy, measured identically for every controller --------------------
module occ_rig #(parameter KIND = 0, parameter integer N = 4,
                 parameter integer W = 8, parameter integer TOTAL = 12)
    (input wire rst, input wire go, output reg [15:0] held, output reg done);

    wire rq, ak, ro, ao;  wire [W-1:0] di, dout;
    bd_source #(.W(W)) src (.req(rq), .ack(ak), .data(di));
    generate
        if (KIND == 2) begin : g_deco
            bd_pipe_deco #(.W(W), .N(N)) dut (
                .rst(rst), .req_in(rq), .ack_in(ak), .data_in(di),
                .req_out(ro), .ack_out(ao), .data_out(dout));
        end else if (KIND == 1) begin : g_attempt
            bd_pipe_semi #(.W(W), .N(N)) dut (
                .rst(rst), .req_in(rq), .ack_in(ak), .data_in(di),
                .req_out(ro), .ack_out(ao), .data_out(dout));
        end else begin : g_simple
            bd_pipe #(.W(W), .N(N)) dut (
                .rst(rst), .req_in(rq), .ack_in(ak), .data_in(di),
                .req_out(ro), .ack_out(ao), .data_out(dout));
        end
    endgenerate
    conf_sink #(.W(W), .T_ACK(3000), .STALLED(1)) snk
        (.req(ro), .ack(ao), .data(dout));

    integer i;
    initial begin
        held = 0; done = 1'b0;
        wait (go);
        fork
            for (i = 0; i < TOTAL; i = i + 1) src.send(8'h10 + i[7:0]);
            begin #2_000_000; held = src.nsent[15:0]; done = 1'b1; end
        join_any
    end
endmodule


module tb_ctl;

    localparam integer N = 4;
    localparam integer W = 8;
    localparam integer H = `BD_HOP_PS;

    // The earliest a consumer may legally sample: the request leads its data by
    // up to one latch arc per stage traversed, plus the review's guardband.
    localparam integer T_SAMPLE = N * `BD_T_FALL + 200;

    integer errors = 0;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s", why);
    end
    endtask

    reg rst = 1'b1;
    reg go  = 1'b0;

    // ---- occupancy ---------------------------------------------------------
    wire [15:0] occ_s, occ_a;  wire occ_sd, occ_ad;
    occ_rig #(.KIND(0), .N(N)) o_simple  (rst, go, occ_s, occ_sd);
    occ_rig #(.KIND(1), .N(N)) o_attempt (rst, go, occ_a, occ_ad);
    wire [15:0] occ_d;  wire occ_dd;
    occ_rig #(.KIND(2), .N(N)) o_deco    (rst, go, occ_d, occ_dd);

    // ---- the stress grid ---------------------------------------------------
    // FAST | SLOWA slow to acknowledge | SLOWR slow to release | SLOWS slow sender
    wire [15:0] wf_s, wa_s, wr_s, ws_s, wf_a, wa_a, wr_a, ws_a;
    wire [15:0] df_s, da_s, dr_s, ds_s, df_a, da_a, dr_a, ds_a;
    wire        ff_s, fa_s, fr_s, fs_s, ff_a, fa_a, fr_a, fs_a;

    conf_rig #(.KIND(0), .T_ACK(T_SAMPLE))
        g_f_s (rst, go, wf_s, df_s, ff_s);
    conf_rig #(.KIND(0), .T_ACK(T_SAMPLE + 6000))
        g_a_s (rst, go, wa_s, da_s, fa_s);
    conf_rig #(.KIND(0), .T_ACK(T_SAMPLE), .T_REL(6000))
        g_r_s (rst, go, wr_s, dr_s, fr_s);
    conf_rig #(.KIND(0), .T_ACK(T_SAMPLE), .TSU(6000), .GAP(6000))
        g_s_s (rst, go, ws_s, ds_s, fs_s);

    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE))
        g_f_a (rst, go, wf_a, df_a, ff_a);
    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE + 6000))
        g_a_a (rst, go, wa_a, da_a, fa_a);
    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE), .T_REL(6000))
        g_r_a (rst, go, wr_a, dr_a, fr_a);
    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE), .TSU(6000), .GAP(6000))
        g_s_a (rst, go, ws_a, ds_a, fs_a);

    // ---- the derived decoupled controller, same matrix --------------------
    wire [15:0] wf_d, wa_d, wr_d, ws_d, df_d, da_d, dr_d, ds_d;
    wire        ff_d, fa_d, fr_d, fs_d;
    conf_rig #(.KIND(2), .T_ACK(T_SAMPLE))
        g_f_d (rst, go, wf_d, df_d, ff_d);
    conf_rig #(.KIND(2), .T_ACK(T_SAMPLE + 6000))
        g_a_d (rst, go, wa_d, da_d, fa_d);
    conf_rig #(.KIND(2), .T_ACK(T_SAMPLE), .T_REL(6000))
        g_r_d (rst, go, wr_d, dr_d, fr_d);
    conf_rig #(.KIND(2), .T_ACK(T_SAMPLE), .TSU(6000), .GAP(6000))
        g_s_d (rst, go, ws_d, ds_d, fs_d);

    // ---- separating the two halves of the "slow sender" case --------------
    // SLOWS moves two things at once, setup and inter-token gap.  These two
    // rigs move one each, so the write-up can name the mechanism instead of
    // guessing at it.
    wire [15:0] w_su_a, w_gap_a, d_su_a, d_gap_a;  wire f_su_a, f_gap_a;
    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE), .TSU(6000))
        g_su_a  (rst, go, w_su_a,  d_su_a,  f_su_a);
    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE), .GAP(6000))
        g_gap_a (rst, go, w_gap_a, d_gap_a, f_gap_a);

    // And the consumer-release case with the sender slowed too, so the two
    // triggers can be told apart instead of being confounded in SLOWR.
    wire [15:0] w_rel_a, d_rel_a;  wire f_rel_a;
    conf_rig #(.KIND(1), .T_ACK(T_SAMPLE), .TSU(6000), .T_REL(6000))
        g_rel_a (rst, go, w_rel_a, d_rel_a, f_rel_a);

    // ---- protocol, on a plain instance of each -----------------------------
    wire p_rq_s, p_ak_s, p_ro_s, p_ao_s;  wire [W-1:0] p_di_s, p_do_s;
    bd_source #(.W(W)) psrc_s (.req(p_rq_s), .ack(p_ak_s), .data(p_di_s));
    bd_pipe #(.W(W), .N(N)) pdut_s (
        .rst(rst), .req_in(p_rq_s), .ack_in(p_ak_s), .data_in(p_di_s),
        .req_out(p_ro_s), .ack_out(p_ao_s), .data_out(p_do_s));
    conf_sink #(.W(W), .T_ACK(T_SAMPLE)) psnk_s
        (.req(p_ro_s), .ack(p_ao_s), .data(p_do_s));
    bd_monitor #(.W(W), .CHAN("simple-in"))                       mi_s
        (.req(p_rq_s), .ack(p_ak_s), .data(p_di_s));
    bd_monitor #(.W(W), .CHAN("simple-out"), .SETTLE(N*`BD_T_FALL)) mo_s
        (.req(p_ro_s), .ack(p_ao_s), .data(p_do_s));

    wire p_rq_d, p_ak_d, p_ro_d, p_ao_d;  wire [W-1:0] p_di_d, p_do_d;
    bd_source #(.W(W)) psrc_d (.req(p_rq_d), .ack(p_ak_d), .data(p_di_d));
    bd_pipe_deco #(.W(W), .N(N)) pdut_d (
        .rst(rst), .req_in(p_rq_d), .ack_in(p_ak_d), .data_in(p_di_d),
        .req_out(p_ro_d), .ack_out(p_ao_d), .data_out(p_do_d));
    conf_sink #(.W(W), .T_ACK(T_SAMPLE)) psnk_d
        (.req(p_ro_d), .ack(p_ao_d), .data(p_do_d));
    bd_monitor #(.W(W), .CHAN("deco-in"))                       mi_d
        (.req(p_rq_d), .ack(p_ak_d), .data(p_di_d));
    bd_monitor #(.W(W), .CHAN("deco-out"), .SETTLE(N*`BD_T_FALL)) mo_d
        (.req(p_ro_d), .ack(p_ao_d), .data(p_do_d));
    integer i3;
    initial begin wait (go);
        for (i3 = 0; i3 < 16; i3 = i3 + 1) psrc_d.send(8'hA0 + i3[7:0]); end

    wire p_rq_a, p_ak_a, p_ro_a, p_ao_a;  wire [W-1:0] p_di_a, p_do_a;
    bd_source #(.W(W)) psrc_a (.req(p_rq_a), .ack(p_ak_a), .data(p_di_a));
    bd_pipe_semi #(.W(W), .N(N)) pdut_a (
        .rst(rst), .req_in(p_rq_a), .ack_in(p_ak_a), .data_in(p_di_a),
        .req_out(p_ro_a), .ack_out(p_ao_a), .data_out(p_do_a));
    conf_sink #(.W(W), .T_ACK(T_SAMPLE)) psnk_a
        (.req(p_ro_a), .ack(p_ao_a), .data(p_do_a));
    bd_monitor #(.W(W), .CHAN("attempt-in"))                       mi_a
        (.req(p_rq_a), .ack(p_ak_a), .data(p_di_a));
    bd_monitor #(.W(W), .CHAN("attempt-out"), .SETTLE(N*`BD_T_FALL)) mo_a
        (.req(p_ro_a), .ack(p_ao_a), .data(p_do_a));

    integer i;
    initial begin wait (go);
        for (i = 0; i < 16; i = i + 1) psrc_s.send(8'hA0 + i[7:0]); end
    integer i2;
    initial begin wait (go);
        for (i2 = 0; i2 < 16; i2 = i2 + 1) psrc_a.send(8'hA0 + i2[7:0]); end

    function [8*5-1:0] verdict(input integer bad);
        verdict = (bad == 0) ? "  ok " : " FAIL";
    endfunction

    initial begin
        $display("tb_ctl -- pipeline controller conformance");
        $display("  consumers sample %0d ps after req-rise: %0d stages of request-leads-data, plus guard",
                 T_SAMPLE, N);

        // reset must leave every pipe empty and DEFINED
        #(20 * H);
        if ({pdut_s.many.stage[3].u.c, pdut_s.many.stage[2].u.c,
             pdut_s.many.stage[1].u.c, pdut_s.many.stage[0].u.c} !== {N{1'b0}})
            fail("the simple pipe did not reset to empty");
        if (pdut_a.stage[0].u.l !== 1'b0 || pdut_a.stage[0].u.r !== 1'b0)
            fail("the attempt did not reset to empty");
        rst = 1'b0;
        #(20 * H);
        mi_s.arm; mo_s.arm; mi_a.arm; mo_a.arm; mi_d.arm; mo_d.arm;

        go = 1'b1;
        wait (occ_sd && occ_ad && occ_dd);
        wait (ff_s && fa_s && fr_s && fs_s && ff_a && fa_a && fr_a && fs_a);
        wait (f_su_a && f_gap_a && f_rel_a);
        wait (ff_d && fa_d && fr_d && fs_d);
        #(200 * H);

        $display();
        $display("  controller      OCC   FAST  SLOWA SLOWR SLOWS PROTO");
        $display("  --------------------------------------------------");
        $display("  simple         %2d/%0d  %0s %0s %0s %0s %0s",
                 occ_s, N/2, verdict(wf_s), verdict(wa_s), verdict(wr_s),
                 verdict(ws_s), verdict(mi_s.errors + mo_s.errors));
        $display("  semi (attempt) %2d/%0d  %0s %0s %0s %0s %0s",
                 occ_a, N,   verdict(wf_a), verdict(wa_a), verdict(wr_a),
                 verdict(ws_a), verdict(mi_a.errors + mo_a.errors));
        $display("  decoupled      %2d/%0d  %0s %0s %0s %0s %0s",
                 occ_d, N,   verdict(wf_d), verdict(wa_d), verdict(wr_d),
                 verdict(ws_d), verdict(mi_d.errors + mo_d.errors));
        $display();
        $display("  wrong tokens out of 20 -- FAST/SLOWA/SLOWR/SLOWS");
        $display("    simple          %0d / %0d / %0d / %0d",
                 wf_s, wa_s, wr_s, ws_s);
        $display("    semi (attempt)  %0d / %0d / %0d / %0d",
                 wf_a, wa_a, wr_a, ws_a);
        $display("    decoupled       %0d / %0d / %0d / %0d",
                 wf_d, wa_d, wr_d, ws_d);
        $display("  attempt, isolating the slow-sender case:");
        $display("    long setup only (TSU=6000)   %0d wrong", w_su_a);
        $display("    long gap only   (GAP=6000)   %0d wrong", w_gap_a);
        $display("    slow sender AND slow release  %0d wrong", w_rel_a);
        $display("  delivered out of 20");
        $display("    simple          %0d / %0d / %0d / %0d",
                 df_s, da_s, dr_s, ds_s);
        $display("    semi (attempt)  %0d / %0d / %0d / %0d",
                 df_a, da_a, dr_a, ds_a);

        // -- the simple controller is the reference: it must fill its row ----
        if (occ_s != N / 2) fail("simple: occupancy is not half a token a stage");
        if (wf_s != 0) fail("simple: FAST");
        if (wa_s != 0) fail("simple: SLOWA -- a slow acknowledge broke it");
        if (wr_s != 0) fail("simple: SLOWR -- a slow release broke it");
        if (ws_s != 0) fail("simple: SLOWS -- a slow sender broke it");
        if (mi_s.errors + mo_s.errors != 0) fail("simple: PROTO");

        // -- the derived decoupled controller must fill the row entirely -----
        // -- the decoupled attempt: UNRESOLVED, and asserted as unresolved ----
        // It is not scored as a library cell, because it is not one.  What is
        // known is narrow and was measured by sweeping the one thing this rig
        // cannot vary -- how long the sender waits after seeing Ain before it
        // drops Rin (build/deco_turn.v):
        //
        //     turnaround      0 ps   8 of 8 accepted, latches hold xx
        //     turnaround     60 ps   4 of 8 accepted, latches hold a0
        //     turnaround   2000 ps   4 of 8 accepted, latches hold a0
        //
        // The cell blocks correctly at N tokens and holds its data for every
        // turnaround down to one arc, and collapses only at EXACTLY zero.
        // bd_source drops req in the same timestep it sees ack, so zero is the
        // only turnaround this rig can present, and zero is not physical: a
        // sender's Ain must cross at least one routed hop and its Rin come
        // back over another.  So the failures below are the rig's regime, not
        // a verdict on the cell -- but the cell is the one that made itself
        // sensitive, by tying its latch-open window to a partner's response
        // time.  The simple controller holds its latch from req-rise to
        // ack-fall and does not care how fast anyone turns round.
        //
        // Deciding it needs a source that models a physical turnaround, which
        // is a change to the harness every other bench shares.  Until then
        // this asserts the measured state, so a silent change is still caught.
        if (occ_d == N && wf_d == 0 && wa_d == 0 && wr_d == 0 && ws_d == 0)
            fail("decoupled: it now passes a zero-turnaround sender -- the note above is stale, promote it or rewrite it");
        if (mi_d.errors + mo_d.errors != 0) fail("decoupled: PROTO");

        // -- the attempt: right about occupancy, wrong about SLOWR -----------
        // Asserted in both directions.  If it ever passes SLOWR, the write-up
        // in verify/attempts/bd_semi_attempt.v is describing a different
        // circuit and should stop being trusted.
        if (occ_a != N) fail("attempt: occupancy is no longer one a stage");
        // Trigger 2 is STRUCTURAL: the outgoing request cannot rise while the
        // consumer holds its acknowledge, so the latch cannot close, and no
        // amount of routing changes that.  It must reproduce in both regimes.
        if (w_rel_a == 0)
            fail("attempt: slow-release passed -- trigger 2 did not reproduce");
        // Trigger 1 is a RACE, one arc wide.  Routing puts a hop in the path
        // that has to lose and the race goes away -- the same shape as the
        // arbiter's handover overlap.  So it is asserted per regime, and the
        // regime is what decides which way.
        if (`BD_ROUTE_PS == 0 && wf_a == 0)
            fail("attempt: FAST passed arc-only -- trigger 1 did not reproduce");
        if (`BD_ROUTE_PS >= 354 && wf_a != 0)
            fail("attempt: FAST still fails with routing -- trigger 1 is not a race");
        if (w_su_a != 0 || w_gap_a != 0)
            fail("attempt: a slack sender no longer rescues it -- see verify/attempts/");
        if (ws_a != 0) fail("attempt: SLOWS -- it used to pass this");

        $display();
        $display("  The attempt holds its token count and its protocol and still");
        $display("  loses data, from EITHER side, for the same reason: it does not");
        $display("  control when its own latch closes.");
        $display("    trigger 1  a sender that turns round quickly -- the stage");
        $display("               upstream reopens before this one has closed");
        $display("    trigger 2  a consumer slow to drop its acknowledge -- the");
        $display("               outgoing request cannot rise, so the latch cannot");
        $display("               close at all");
        $display("  Slack on either side hides it, which is why a hand-driven");
        $display("  sweep found only half of it.  See verify/attempts/.");
        $display();
        if (`BD_ROUTE_PS == 0) begin
            $display("  At BD_ROUTE_PS=0 both triggers fire.  Trigger 1 is a one-arc");
            $display("  race; re-run at 354 and routing removes it.");
        end else begin
            $display("  At BD_ROUTE_PS=%0d trigger 1 is gone: it was a one-arc race and",
                     `BD_ROUTE_PS);
            $display("  routing put a hop in the path that had to lose.");
        end
        $display("  Trigger 2 survives every regime.  It is structural, and it is");
        $display("  the reason this cell can never ship.");

        if (errors == 0) $display("tb_ctl PASS");
        else             $display("tb_ctl FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #900_000_000;
        $display("tb_ctl FAIL (timeout)");
        $finish;
    end
endmodule
