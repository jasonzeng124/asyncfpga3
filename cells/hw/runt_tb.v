`timescale 1ps / 1ps

// ---------------------------------------------------------------------------
// runt_tb -- does hw/runt_top.v's rig run, and do its controls read right?
//
//   cd cells && mkdir -p build/sim && iverilog -g2012 -gspecify -Wall \
//       -Wno-timescale -DBD_ROUTE_PS=0 -o build/sim/runt_tb.vvp \
//       sim/bd_prims_sim.v rtl/bd_latch.v rtl/bd_ce.v hw/runt_top.v \
//       hw/runt_tb.v && vvp build/sim/runt_tb.vvp
//
// Add -DRUNT_TB_INJECT for the negative control: it pins one LONG cell's a
// pin and one NEG cell's b pin at 0, which turns them into a cell that never
// sets and a cell that always sets.  That run MUST print "runt_tb FAIL".
//
// The WHOLE top, BSCANE2 included: the bench drives the USER1 DR exactly the
// way the TAP does (Capture-DR, 48 x Shift-DR with TDO read before each
// shifting edge, Exit1, Update-DR), so the scan protocol, the hold-register
// field layout, the TCK<->rclk crossings, the FSM, the LFSR tallies and the
// descriptor ROM are all exercised by the same words runt_measure.py sends.
//
// WHAT THIS CANNOT SHOW, and is not asked to: anything about the runt.  The
// LUT models here are bd_prims_sim.v's -- one prjxray cell arc per LUT, zero
// routing, iverilog's own handling of a pulse narrower than a path delay.
// Whether a TEST cell captures, rejects or circulates in this simulation is a
// property of the simulator, which is exactly the thing the board is built to
// replace.  TEST outcomes are PRINTED, never checked.  What IS checked is
// what does not depend on that: the NEG and LONG controls (episodes of -8 and
// +8 LUTs, far from any threshold), PULSE emission at k >= 2, the masked-group
// zeros, the poison, the calibration count against the ring period this
// simulation actually produced, and the descriptor table against the plan
// rule written out again below (not copied from a run).
// ---------------------------------------------------------------------------

module runt_tb;

    localparam integer G = 8, S = 16, NI = 128, KC = 8;
    localparam integer TCKH = 5000;                 // 100 MHz TCK
    localparam [7:0] TAG = 8'h96;

    // ---- JTAG side, read by the BSCANE2 model below -------------------------
    reg j_tck = 1'b0, j_sel = 1'b0, j_cap = 1'b0, j_shift = 1'b0,
        j_upd = 1'b0, j_tdi = 1'b0;

    wire led_r, led_g;
    runt_top dut (.led_red(led_r), .led_green(led_g));

    integer errors = 0;
    task fail(input [8*120-1:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    // ---- the plan rule, written out independently of runt_top.v ------------
    // kind: 0 TEST 1 NEG 2 LONG 3 PULSE.  r = (slot + group) % 16.
    function integer p_kind(input integer i);
        integer r;
        begin
            r = ((i % S) + (i / S)) % S;
            p_kind = (r == 0) ? 1 : (r == 8) ? 2 : (r == 4 || r == 12) ? 3 : 0;
        end
    endfunction
    function integer p_ks(input integer n);     // 0 1 0 1 2 0 1 3 0 1 2 3
        case (n)
            4, 10:   p_ks = 2;
            7, 11:   p_ks = 3;
            1, 3, 6, 9: p_ks = 1;
            default: p_ks = 0;
        endcase
    endfunction
    function integer p_kb(input integer i);
        integer r, g, j;
        begin
            r = ((i % S) + (i / S)) % S;
            g = i / S;
            j = r - 1 - r / 4;
            case (p_kind(i))
                0: p_kb = p_ks((j + g) % 12);
                1: p_kb = 0;
                2: p_kb = KC;
                default: p_kb = (2 * g + ((r == 12) ? 1 : 0)) % 4;
            endcase
        end
    endfunction
    function integer p_ka(input integer i);
        p_ka = (p_kind(i) == 1) ? KC : 0;
    endfunction

    // x^8+x^6+x^5+x^4+1, XNOR, from 0 -- decoded by stepping, as the host does
    function integer undo(input [7:0] st);
        integer n;
        reg [7:0] x;
        begin
            undo = -1;
            x = 8'h00;
            for (n = 0; n < 255; n = n + 1) begin
                if (x == st && undo < 0) undo = n;
                x = {x[6:0], ~(x[7] ^ x[5] ^ x[4] ^ x[3])};
            end
        end
    endfunction

    // ---- the TAP's view of one USER1 DR scan --------------------------------
    task tck_cycle;
    begin
        #TCKH j_tck = 1'b1;
        #TCKH j_tck = 1'b0;
    end
    endtask

    task scan(input [47:0] din, output [47:0] dout);
        integer k;
        begin
            j_sel = 1'b1;
            tck_cycle;                              // Select-DR
            j_cap = 1'b1; tck_cycle; j_cap = 1'b0;  // Capture-DR
            j_shift = 1'b1;
            for (k = 0; k < 48; k = k + 1) begin    // Shift-DR, LSB first
                dout[k] = dut.sr_tdo;
                j_tdi = din[k];
                tck_cycle;
            end
            j_shift = 1'b0;
            tck_cycle;                              // Exit1-DR
            j_upd = 1'b1; tck_cycle; j_upd = 1'b0;  // Update-DR
            tck_cycle;                              // Run-Test/Idle
        end
    endtask

    reg [47:0] ctrl = 48'h0;
    reg [47:0] w;

    task u1(input [3:0] addr, output [47:0] dout);
        scan(ctrl | addr, dout);
    endtask

    task rd(input [3:0] addr, output [47:0] dout);
        reg [47:0] junk;
        begin
            u1(addr, junk);
            u1(addr, dout);
        end
    endtask

    function [47:0] mk(input integer T, input integer gm, input integer wexp,
                       input integer inst);
        mk = ({40'h0, T[7:0]} << 14) | ({40'h0, gm[7:0]} << 22)
           | ({44'h0, wexp[3:0]} << 30) | ({41'h0, inst[6:0]} << 7);
    endfunction

    task check_word(input [47:0] wd, input [3:0] addr);
        begin
            if (wd[47:40] !== TAG)  fail("tag");
            if (wd[35:32] !== addr) fail("addr echo");
        end
    endtask

    // ---- the ring clock, as this simulation produced it --------------------
    realtime last_r = 0, per_r = 0;
    always @(posedge dut.rclk) begin
        if (last_r > 0) per_r = $realtime - last_r;
        last_r = $realtime;
    end

    // ---- positive control for the edge counters ---------------------------
    // Nothing in this simulation circulates on its own, so without this the
    // multi and late tallies would never be seen to count, and a stuck-at-0
    // counter would pass.  During run 5 only, TEST cell OSC_I's q node is
    // driven as a 600 ps square wave from its launch until clr -- what the
    // transport model says a runt does -- and that cell must then read
    // emit = multi = late = T.
    localparam integer OSC_I = 1;               // g0 r1: TEST, k = 0
    reg osc_en = 1'b0, osc_chk = 1'b0;
    always begin
        @(posedge dut.inst[OSC_I].la);
        if (osc_en) begin
            force dut.inst[OSC_I].q = 1'b0;
            while (dut.clr !== 1'b1) begin
                #300 force dut.inst[OSC_I].q = 1'b1;
                #300 force dut.inst[OSC_I].q = 1'b0;
            end
            release dut.inst[OSC_I].q;
        end
    end

    // ---- one run: zero, go, wait for done, go low, read every counter ------
    integer one [0:NI-1], emt [0:NI-1], mul [0:NI-1], lat [0:NI-1];

    task run(input integer T, input integer gm, input integer wexp);
        integer i, n, guard;
        reg [47:0] base;
        begin
            base = mk(T, gm, wexp, 0);
            ctrl = base | 48'h20; u1(4'd2, w);           // zero = 1
            ctrl = base;          u1(4'd2, w);           // zero = 0
            ctrl = base | 48'h10; u1(4'd2, w);           // go = 1
            guard = 0;
            u1(4'd2, w);
            while (w[37] !== 1'b1 && guard < 4000) begin
                u1(4'd2, w);
                guard = guard + 1;
            end
            if (w[37] !== 1'b1) fail("run never reported done");
            ctrl = base; u1(4'd2, w);                    // go = 0
            rd(4'd2, w);
            check_word(w, 4'd2);
            if (w[7:0] !== T[7:0])   fail("status: trials completed != T");
            if (w[23:16] !== T[7:0]) fail("status: T latched wrong");
            if (w[31:24] !== gm[7:0]) fail("status: gmask latched wrong");
            if (w[10:8] !== 3'd0)    fail("status: FSM not back in IDLE");
            for (i = 0; i < NI; i = i + 1) begin
                ctrl = base | ({41'h0, i[6:0]} << 7);
                rd(4'd0, w);
                check_word(w, 4'd0);
                if (w[31:0] === 32'hFFFF_FFFF) fail("counter read poisoned after done");
                one[i] = undo(w[7:0]);
                emt[i] = undo(w[15:8]);
                mul[i] = undo(w[23:16]);
                lat[i] = undo(w[31:24]);
                if (one[i] < 0 || emt[i] < 0 || mul[i] < 0 || lat[i] < 0)
                    fail("counter holds a state the LFSR never reaches");
            end
            ctrl = base;
        end
    endtask

    // ---- judge one run's controls -------------------------------------------
    task judge(input integer T, input integer gm, input [8*8-1:0] tag);
        integer i, g, k, kind, nbad;
        integer t_n [0:3], t_one [0:3], t_emt [0:3], t_mul [0:3], t_lat [0:3];
        begin
            nbad = 0;
            for (k = 0; k < 4; k = k + 1) begin
                t_n[k] = 0; t_one[k] = 0; t_emt[k] = 0; t_mul[k] = 0; t_lat[k] = 0;
            end
            for (i = 0; i < NI; i = i + 1) begin
                g = i / S;
                kind = p_kind(i);
                k = p_kb(i);
                if (osc_chk && i == OSC_I) begin
                    if (emt[i] != T || mul[i] != T || lat[i] != T) begin
                        $display("    OSC inst %0d: emit %0d multi %0d late %0d, want %0d each",
                                 i, emt[i], mul[i], lat[i], T);
                        nbad = nbad + 1;
                    end else
                        $display("  %0s: forced-oscillation cell %0d read emit = multi = late = T",
                                 tag, i);
                end else if (!gm[g]) begin
                    if (one[i] || emt[i] || mul[i] || lat[i]) begin
                        $display("    inst %0d (group %0d, masked) %0d/%0d/%0d/%0d",
                                 i, g, one[i], emt[i], mul[i], lat[i]);
                        nbad = nbad + 1;
                    end
                end else if (kind == 1) begin
                    if (one[i] || emt[i] || mul[i] || lat[i]) begin
                        $display("    NEG inst %0d: ones %0d emit %0d multi %0d late %0d",
                                 i, one[i], emt[i], mul[i], lat[i]);
                        nbad = nbad + 1;
                    end
                end else if (kind == 2) begin
                    if (one[i] != T || emt[i] != T || mul[i] || lat[i]) begin
                        $display("    LONG inst %0d: ones %0d emit %0d multi %0d late %0d (T %0d)",
                                 i, one[i], emt[i], mul[i], lat[i], T);
                        nbad = nbad + 1;
                    end
                end else if (kind == 3) begin
                    if (one[i] || mul[i] || lat[i] || (k >= 2 && emt[i] != T)) begin
                        $display("    PULSE inst %0d k %0d: ones %0d emit %0d multi %0d late %0d",
                                 i, k, one[i], emt[i], mul[i], lat[i]);
                        nbad = nbad + 1;
                    end
                end else begin
                    t_n[k] = t_n[k] + 1;
                    t_one[k] = t_one[k] + one[i];
                    t_emt[k] = t_emt[k] + emt[i];
                    t_mul[k] = t_mul[k] + mul[i];
                    t_lat[k] = t_lat[k] + lat[i];
                end
            end
            if (nbad) fail({tag, ": a control instance read wrong"});
            else $display("  %0s: every NEG/LONG/PULSE%0s control read right (T = %0d)",
                          tag, (gm != 255) ? "/masked" : "", T);
            for (k = 0; k < 4; k = k + 1)
                if (t_n[k])
                    $display("  %0s: TEST k=%0d  %0d cells  ones %0d emit %0d multi %0d late %0d  (of %0d each; simulator semantics, not checked)",
                             tag, k, t_n[k], t_one[k], t_emt[k], t_mul[k], t_lat[k], T);
        end
    endtask

    integer i, n_mix, n1, calc, exp_c;
    realtime t0, t1;

    initial begin
        $display("runt_tb  (BD_ROUTE_PS=%0d)", `BD_ROUTE_PS);
        // A LUT loop powers up at x in simulation and stays there; on silicon
        // the ring free-runs from configuration.  Hold its node for longer
        // than one lap so the whole chain is defined, then let it go.
        force dut.rk_fb = 1'b0;
        #20000;
        release dut.rk_fb;
`ifdef RUNT_TB_INJECT
        // Negative control: inst 8 is LONG (g0 r8), inst 0 is NEG (g0 r0).
        force dut.inst[8].a = 1'b0;     // LONG never sets: ones = emit = 0
        force dut.inst[0].b = 1'b0;     // NEG sets after its late a: ones = T
        $display("  INJECTED: inst 8 (LONG) a pinned 0, inst 0 (NEG) b pinned 0");
`endif
        #200000;

        // 1. the scan path
        rd(4'd8, w);  check_word(w, 4'd8);  if (w[31:0] !== 32'hDEAD_BEEF) fail("const 8");
        rd(4'd9, w);  check_word(w, 4'd9);  if (w[31:0] !== 32'h5A5A_1234) fail("const 9");
        rd(4'd10, w); check_word(w, 4'd10); if (w[31:0] !== 32'h0000_0000) fail("const 10");
        ctrl = mk(8'h5A, 8'hA5, 4'h9, 7'h33) | 48'h40;   // cal set, nothing else
        rd(4'd13, w); check_word(w, 4'd13);
        if (w[31:0] !== {2'b00, ctrl[33:4]}) fail("control echo");
        ctrl = 48'h0; u1(4'd13, w);
        $display("  scan path: constants, tag, addr echo and control echo read right");

        // 2. the descriptor ROM against the rule
        n1 = 0;
        for (i = 0; i < NI; i = i + 1) begin
            ctrl = mk(0, 0, 0, i);
            rd(4'd3, w);
            check_word(w, 4'd3);
            if (w[3:0] != p_kb(i) || w[7:4] != p_ka(i) || w[9:8] != p_kind(i)
                || w[16:10] != i || w[31:24] != NI) begin
                n1 = n1 + 1;
                $display("    inst %0d: descriptor %h, rule kind %0d ka %0d kb %0d",
                         i, w[31:0], p_kind(i), p_ka(i), p_kb(i));
            end
        end
        if (n1) fail("descriptor ROM disagrees with the plan rule");
        else $display("  descriptors: all %0d instances match the plan rule", NI);
        ctrl = 48'h0;

        // 3. liveness of rclk, seen from TCK
        n_mix = 0; n1 = 0;
        for (i = 0; i < 16; i = i + 1) begin
            rd(4'd12, w);
            n1 = n1 + w[0];
            #(1700 + 1300 * i);
        end
        if (n1 == 0 || n1 == 16) fail("rclk sampler stuck -- the ring clock is not running");
        else $display("  liveness: rclk sampler returned %0d ones in 16", n1);

        // 4. calibration, against the period this simulation actually has
        ctrl = 48'h40; u1(4'd14, w); t0 = $realtime;
        rd(4'd14, w);
        if (w[31:0] !== 32'hFFFF_FFFF) fail("cal counter not poisoned while cal high");
        #(10_000_000);
        ctrl = 48'h0;  u1(4'd14, w); t1 = $realtime;
        rd(4'd14, w);
        calc = w[31:0];
        exp_c = (t1 - t0) / per_r;
        $display("  calibration: %0d rclk cycles counted, %0d expected from the ring period %0.0f ps",
                 calc, exp_c, per_r);
        if (calc < exp_c * 0.95 || calc > exp_c * 1.05)
            fail("calibration count disagrees with the ring period");

        // 5. a full run, all groups
        osc_en = 1'b1;
        run(6, 8'hFF, 0);
        osc_en = 1'b0;
        osc_chk = 1'b1;
        judge(6, 8'hFF, "all");
        osc_chk = 1'b0;

        // 6. one group alone: every other group's counters must read zero --
        //    which also proves `zero` cleared run 5's counts
        run(3, 8'h04, 0);
        judge(3, 8'h04, "grp2");

        // 7. counters are poisoned while the FSM runs
        ctrl = mk(3, 8'hFF, 4, 0) | 48'h20; u1(4'd0, w);
        ctrl = mk(3, 8'hFF, 4, 0);          u1(4'd0, w);
        ctrl = mk(3, 8'hFF, 4, 0) | 48'h10; u1(4'd0, w);
        rd(4'd0, w);
        if (w[36] !== 1'b1)               fail("busy not reported during a run");
        if (w[31:0] !== 32'hFFFF_FFFF)    fail("counter read not poisoned while busy");
        else $display("  poison: counter read during a run returned 0xFFFFFFFF, busy set");
        n1 = 0;
        while (w[37] !== 1'b1 && n1 < 4000) begin u1(4'd2, w); n1 = n1 + 1; end
        ctrl = mk(3, 8'hFF, 4, 0); u1(4'd2, w);

        if (errors == 0) $display("runt_tb PASS");
        else $display("runt_tb FAIL (%0d errors)", errors);
        $finish;
    end

    initial begin
        #(40_000_000_000);
        $display("runt_tb FAIL (timeout)");
        $finish;
    end
endmodule

// ---- primitives this rig instantiates that bd_prims_sim.v does not model ---

module BSCANE2 #(parameter integer JTAG_CHAIN = 1) (
    output wire CAPTURE, DRCK, RESET, RUNTEST, SEL, SHIFT, TCK, TDI, TMS, UPDATE,
    input  wire TDO);
    assign CAPTURE = runt_tb.j_cap;
    assign SEL     = runt_tb.j_sel;
    assign SHIFT   = runt_tb.j_shift;
    assign UPDATE  = runt_tb.j_upd;
    assign TCK     = runt_tb.j_tck;
    assign TDI     = runt_tb.j_tdi;
    assign DRCK = 1'b0, RESET = 1'b0, RUNTEST = 1'b0, TMS = 1'b0;
endmodule

module FDRE #(parameter [0:0] INIT = 1'b0) (
    output reg Q, input wire C, CE, R, D);
    initial Q = INIT;
    always @(posedge C) if (R) Q <= 1'b0; else if (CE) Q <= D;
endmodule

module FDCE #(parameter [0:0] INIT = 1'b0) (
    output reg Q, input wire C, CE, CLR, D);
    initial Q = INIT;
    always @(posedge C or posedge CLR)
        if (CLR) Q <= 1'b0; else if (CE) Q <= D;
endmodule
