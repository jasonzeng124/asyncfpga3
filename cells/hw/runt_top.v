// ---------------------------------------------------------------------------
// runt_top.v -- H_RUNT(w) on silicon: what a C-element LUT loop does when the
// episode that forces it is SHORTER than its own feedback loop.
//
// WHY THIS EXISTS.  Every C-element in rtl/bd_ce.v is one LUT6 whose output is
// wired back to its own I2.  bd_c2n sets on a.~b and holds on a tie.  If a
// rises and ~b falls again (b rises) before the new q has gone round the loop
// and arrived at I2, the LUT sees (a=1, b=1, q_in=0) and drives 0 again: the
// output carried a pulse of width ~w and nothing has latched it.  What happens
// to that pulse is a property of the fabric that no simulator here decides:
//
//   TRANSPORT model -- the pulse goes round the loop unchanged forever.  The
//   node oscillates at the loop period until something resets it, and any
//   circuit built from such a cell can lock up on one short episode.
//   INERTIAL / runt-killing fabric -- a pulse narrower than some w_min never
//   leaves the LUT, and one that does leave either dies on a later lap or
//   latches.  The cell then settles, to 0 or 1, and the only question is
//   where the threshold sits relative to the loop delay.
//
// The formal analysis (FOR-RESEARCH.md section 3) needs to know which.  This is
// the board half: NI copies of the cell, each forced by an episode of a
// different routed width w_i spanning roughly -200 .. +1500 ps, with the loop
// delay (~0.3-0.6 ns, LUT arc + O->I2 local route) in the middle of the range.
// Per-instance w_i is predicted afterwards from this build's routed prjxray SDF
// (not here); the cell names that prediction walks are listed by
// `hw/runt_measure.py --table`.
//
// ---------------------------------------------------------------------------
// ONE INSTANCE.  Two twin flops La and Lb (FDRE, rclk, same D, same edge).
//
//     a = bd_delay(KA)(La)  -> I0 of the cell under test
//     b = bd_delay(KB)(Lb)  -> I1
//     clr                   -> I3 (rst)          q = cell output, fed back to I2
//
// w = t(b reaches its pin) - t(a reaches its pin).  The flops are TWINS rather
// than one flop feeding both paths because KB = 0 must give a w near zero, and
// a = b = one net would make I0 and I1 the same signal (and invite the
// synthesiser to merge them).  Twins on one clock edge differ only by clock
// skew, clk->Q and routing -- all of which are in the SDF, so one prediction
// formula covers every instance.
//
// FOUR KINDS, rotated through the slots by group like ro_many_top's lengths,
// so kind and k are decorrelated from slot position and from group:
//
//     TEST   (96)  KA = 0, KB = k in {0,1,2,3} (32/32/16/16).  The experiment.
//                  k = 0 lands within a few hundred ps of zero either way, k = 1
//                  around one hop (~0.45 ns) -- i.e. right on the loop delay --
//                  and k = 2, 3 above it.  Routing smears each k into a
//                  continuum; that smear is the point.
//     NEG    (8)   KA = 8, KB = 0.  b rises ~3.5 ns BEFORE a: the cell is
//                  reset (a=0,b=1) and then holds 0 (1,1).  No force-high
//                  episode exists.  MUST read ones = emit = multi = late = 0.
//     LONG   (8)   KA = 0, KB = 8.  w ~ +3.5 ns >> loop.  MUST read ones =
//                  emit = T, multi = late = 0: a clean capture every trial.
//     PULSE  (16)  The same a/b/clr pins into a LUT3 computing a.~b.~clr --
//                  the cell under test with its feedback CUT.  It emits one
//                  pulse of width w and returns to 0 (KB = k as for TEST).
//                  This is the edge detector's calibration, the same idea as
//                  arb_mtbf's threshold channels: the thermometer below is
//                  clocked through fabric routing and has a minimum
//                  capturable pulse of its own; PULSE says what it is.  A
//                  PULSE with k = 3 (~1.4 ns) MUST read emit = T; if it does
//                  not, a zero multi count says nothing.  It also answers
//                  H_RUNT for an OPEN LUT, i.e. without the loop.
//
// Group g (0..7) of 16 slots s: r = (s + g) % 16.  r == 0 NEG, r == 8 LONG,
// r == 4 / 12 PULSE, everything else TEST.  The descriptor at address 3 reads
// the kind and both chain lengths back from the bitstream, so the host never
// has to trust that its copy of this rule matches the build.
//
// ---------------------------------------------------------------------------
// ONE TRIAL, in the ring-clock domain (rclk, a 31-link ring, ~35 MHz):
//
//     END     clr=1, L stays high .......... 4 cycles   (q forced 0 first)
//     CLR     clr=1, L=0 ................... 16 cycles  (chains settle at 0)
//     REL     clr=0, L=0 ................... 16 cycles  (a=b=0: hold at 0)
//     LAUNCH  L=1 for the masked groups .... 16 << wexp cycles; late_en rises
//                                            at the half-way point
//     TALLY   per-instance counters take the synchronised outcome
//     -> END
//
// clr is asserted BEFORE L falls and released only once a = b = 0 settled, so
// the falling L can never set a cell (rst dominates) and the release never
// lands on a set condition.  The window must be >= 1 us; at the predicted rclk
// the default wexp = 3 is 128 cycles, ~3.7 us, and the host measures rclk
// (address 14) and refuses to judge a window under 1 us.
//
// WHY ALL INSTANCES LAUNCH TOGETHER BY DEFAULT.  Power is not the issue: one
// trial switches ~2 flops and a few LUTs per instance, once.  The issue is
// coupling -- 128 simultaneous edges produce a supply dip in exactly the
// nanosecond the race is decided.  It is common mode (w and the loop delay
// shift together), so it should move the threshold far less than routing does,
// but "should" is not a measurement: gmask launches any subset of the eight
// groups, the instances of a masked group must then read all zeros (a
// crosstalk control), and runt_measure.py's RUNT_SPLIT=1 compares the capture
// fraction of each group alone against all-together.
//
// ---------------------------------------------------------------------------
// WHAT IS COUNTED, per instance, over the T trials of one run.  q's RISING
// edges clock a three-flop thermometer (FDCE, async-cleared by clr) through
// FABRIC routing -- no BUFG, one fabric clock per instance, the same thing
// hw/mem_port_ps.v's edge_cap does and bd_mem's USE_BUFG=0 strobe already
// routes on this part:
//
//     e0 <= 1        (>= 1 rising edge of q since clr released)
//     e1 <= e0       (>= 2 rising edges)
//     lt <= late_en  (>= 1 rising edge in the second half of the window)
//
// e0, e1, lt and q itself cross into rclk through two flops each and are
// tallied at the end of the window:
//
//     ones   trials q was 1 at the end of the window
//     emit   trials q rose at least once            (T - emit: runt rejected)
//     multi  trials q rose at least twice           (the runt went round)
//     late   trials q was STILL rising in the second half of the window
//            (a runt that circulates and does not die: the transport model)
//
// Read together:  emit=0                  -> rejected at the LUT
//                 emit=1 multi=0 ones=1   -> captured cleanly
//                 emit=1 multi=0 ones=0   -> one pulse left the LUT and died
//                 multi=1, late=0         -> went round, then settled
//                 late=1                  -> still oscillating ~0.5 window on
//                                            (ones is then a coin toss)
//
// The counters are 8-bit maximal LFSRs (x^8+x^6+x^5+x^4+1, XNOR, from 0), one
// LUT each instead of a carry chain: 512 of them, and the population was the
// whole reason to build this.  255 states, so T <= 254 per run; the host sums
// runs.  The host decodes them (runt_measure.py), and the controls validate
// that decode every run: LONG must decode to T, NEG to 0.
//
// THE EDGE COUNT HAS A FLOOR.  A slice FF clock pin has a minimum pulse width
// and its routing is a filter of its own, so a runt narrower than that floor
// circulating at ~2 GHz can go uncounted.  PULSE measures the floor for single
// pulses; late and a ones fraction strictly between 0 and T are the second
// witness.  A multi of zero is "no runt wider than the floor went round", not
// "no runt went round".
//
// ---------------------------------------------------------------------------
// READBACK.  ro_many_top's protocol: BSCANE2 USER1, BUFG on TCK, one 48-bit
// DR, CAPTURE strictly before UPDATE, TAG in the top byte (0x96 here, distinct
// from A5/55/3C/6D), constants at 8, 9 and 10, the async liveness sampler at
// 12, the control echo at 13.
//
// Written on UPDATE (bits [33:0] of the 48 shifted in):
//
//     [3:0]   addr    which register the NEXT capture presents
//     [4]     go      a rising edge (synchronised into rclk) starts a run;
//                     the FSM stays in DONE until go falls again
//     [5]     zero    while the FSM is idle, clear counters and snapshots
//     [6]     cal     the rclk calibration counter counts while high
//     [13:7]  inst    which instance addresses 0, 1, 3 present
//     [21:14] T       trials per run, 1..254 (latched at go)
//     [29:22] gmask   which groups launch (latched at go)
//     [33:30] wexp    window = 16 << wexp rclk cycles (latched at go)
//
// Loaded on CAPTURE:
//
//     [31:0]  data
//     [35:32] addr echo
//     [36]    busy  (FSM running, synchronised into TCK)
//     [37]    done  (FSM in DONE, synchronised into TCK)
//     [39:38] zero
//     [47:40] TAG = 0x96
//
// ADDRESSES.  0  counters of `inst`  {late, multi, emit, ones}, 8 bits each,
//                raw LFSR state.  0xFFFFFFFF while busy (poison, as ro_many).
//             1  outcome bits of `inst`: [3:0] {lt, e1, e0, q} as tallied on
//                the LAST trial, [7:4] the same four synchronised now.
//             2  status: [7:0] trials completed, [10:8] FSM state,
//                [23:16] T latched, [31:24] gmask latched.
//             3  descriptor of `inst`: [3:0] KB, [7:4] KA, [9:8] kind
//                (0 TEST 1 NEG 2 LONG 3 PULSE), [16:10] inst echo, [31:24] NI.
//             8, 9, 10  0xDEADBEEF, 0x5A5A1234, 0x00000000.
//             12 [0] an rclk-domain toggle sampled in TCK: the variance says
//                the ring clock is alive.
//             13 control echo, hold[33:4].
//             14 rclk cycles counted while cal was high (cleared on cal's
//                rising edge).  0xFFFFFFFF while cal is high.
//
// CROSSINGS.  go, zero, cal cross TCK -> rclk through two flops; T, gmask and
// wexp are quasi-static (written in a scan before the one that raises go, and
// read once, at go).  busy and done cross back through two TCK flops.  The
// counters, snapshot and status are read from TCK only while the FSM is idle
// or done -- static -- and address 0 is poisoned while busy.
//
// Build:  BD_RLOC=none NEXTPNR_FREQ=50 hw/build_hw.sh runt_top
// (the default `*)` source list in build_hw.sh -- bd_latch.v, bd_ce.v, bd_arb.v
// -- already holds bd_delay and bd_c2n; no build_hw.sh change is needed).
// ---------------------------------------------------------------------------

`default_nettype none

module runt_top (output wire led_red, output wire led_green);

    localparam integer G    = 8;          // groups (gmask bits)
    localparam integer S    = 16;         // slots per group
    localparam integer NI   = G * S;      // 128 instances
    localparam integer W    = 48;         // DR width, as ro_many_top
    localparam integer KC   = 8;          // control chain length (NEG, LONG)
    localparam integer RLEN = 31;         // rclk ring, links
    localparam [7:0]   TAG  = 8'h96;

    // ---- the instance plan -------------------------------------------------
    // 0 TEST, 1 NEG, 2 LONG, 3 PULSE.  hw/runt_measure.py mirrors this rule
    // and checks it against the descriptor the bitstream reads back.
    function integer rot_of(input integer i);
        rot_of = ((i % S) + (i / S)) % S;
    endfunction

    function integer kind_of(input integer i);
        integer r;
        begin
            r = rot_of(i);
            if (r == 0)                kind_of = 1;
            else if (r == 8)           kind_of = 2;
            else if (r == 4 || r == 12) kind_of = 3;
            else                       kind_of = 0;
        end
    endfunction

    // TEST: the j-th TEST slot of the group (r = 1,2,3,5,6,7,9,..,15 -> j =
    // 0..11) takes KSEQ[(j + g) % 12], KSEQ = 0 1 0 1 2 0 1 3 0 1 2 3, which is
    // 4/4/2/2 of k = 0/1/2/3 per group.  PULSE: k = (2g + (r == 12)) % 4.
    function integer kseq(input integer n);
        case (n)
            0: kseq = 0;  1: kseq = 1;  2: kseq = 0;  3: kseq = 1;
            4: kseq = 2;  5: kseq = 0;  6: kseq = 1;  7: kseq = 3;
            8: kseq = 0;  9: kseq = 1; 10: kseq = 2; default: kseq = 3;
        endcase
    endfunction

    function integer ka_of(input integer i);
        ka_of = (kind_of(i) == 1) ? KC : 0;
    endfunction

    function integer kb_of(input integer i);
        integer r, g, j;
        begin
            r = rot_of(i);
            g = i / S;
            j = r - 1 - r / 4;
            case (kind_of(i))
                0:       kb_of = kseq((j + g) % 12);
                1:       kb_of = 0;
                2:       kb_of = KC;
                default: kb_of = (2 * g + (r == 12 ? 1 : 0)) % 4;
            endcase
        end
    endfunction

    function [7:0] lfsr8(input [7:0] x);
        lfsr8 = {x[6:0], ~(x[7] ^ x[5] ^ x[4] ^ x[3])};
    endfunction

    // ---- BSCANE2 (USER1) ---------------------------------------------------
    wire bs_capture, bs_shift, bs_update, bs_sel;
    wire bs_tck_raw, bs_tdi;
    wire sr_tdo;

    (* keep *) BSCANE2 #(.JTAG_CHAIN(1)) bscan_i (
        .CAPTURE (bs_capture),
        .DRCK    (),                  // unused: DRCK does not pulse in UPDATE
        .RESET   (),
        .RUNTEST (),
        .SEL     (bs_sel),
        .SHIFT   (bs_shift),
        .TCK     (bs_tck_raw),
        .TDI     (bs_tdi),
        .TMS     (),
        .UPDATE  (bs_update),
        .TDO     (sr_tdo));

    wire tck;
    BUFG bufg_tck (.I(bs_tck_raw), .O(tck));

    // ---- hold register -----------------------------------------------------
    reg  [33:0] hold = 34'h0;
    wire [3:0]  hold_addr  = hold[3:0];
    wire        hold_go    = hold[4];
    wire        hold_zero  = hold[5];
    wire        hold_cal   = hold[6];
    wire [6:0]  hold_inst  = hold[13:7];
    wire [7:0]  hold_T     = hold[21:14];
    wire [7:0]  hold_gmask = hold[29:22];
    wire [3:0]  hold_wexp  = hold[33:30];

    // ---- the ring clock ----------------------------------------------------
    // Free-running from configuration, like ro_top's rings: a bd_delay chain
    // closed through one LUT1 inversion, onto a BUFG.  Its period is measured
    // (address 14), never assumed: the window length depends on it.
    wire rk_z, rk_fb, rclk;
    bd_delay #(.N(RLEN)) rk_d (.a(rk_fb), .z(rk_z));
    (* keep *) LUT1 #(.INIT(2'h1)) rk_inv (.I0(rk_z), .O(rk_fb));
    BUFG bufg_rclk (.I(rk_fb), .O(rclk));

    // ---- TCK -> rclk ------------------------------------------------------
    reg [1:0] go_s = 2'b00, zero_s = 2'b00, cal_s = 2'b00;
    always @(posedge rclk) begin
        go_s   <= {go_s[0],   hold_go};
        zero_s <= {zero_s[0], hold_zero};
        cal_s  <= {cal_s[0],  hold_cal};
    end

    // ---- the trial FSM ----------------------------------------------------
    localparam [2:0] ST_IDLE = 3'd0, ST_END = 3'd1, ST_CLR = 3'd2,
                     ST_REL  = 3'd3, ST_LAUNCH = 3'd4, ST_TALLY = 3'd5,
                     ST_DONE = 3'd6;

    reg [2:0]   st      = ST_IDLE;
    reg         go_prev = 1'b0;
    reg [19:0]  wc      = 20'd0;
    reg [7:0]   T_l     = 8'd0;
    reg [7:0]   gm_l    = 8'd0;
    reg [3:0]   wexp_l  = 4'd0;
    reg [7:0]   ntr     = 8'd0;
    reg         clr     = 1'b1;       // power-up: every cell held at 0
    reg         late_en = 1'b0;
    reg         tally   = 1'b0;
    reg         busy    = 1'b0;
    reg         done    = 1'b0;
    reg [G-1:0] lgo     = {G{1'b0}};

    wire [19:0] win  = 20'd16 << wexp_l;
    wire [19:0] half = win >> 1;

    always @(posedge rclk) begin
        go_prev <= go_s[1];
        tally   <= 1'b0;
        case (st)
        ST_IDLE: begin
            clr     <= 1'b1;
            lgo     <= {G{1'b0}};
            late_en <= 1'b0;
            busy    <= 1'b0;
            if (!go_s[1]) done <= 1'b0;
            if (go_s[1] && !go_prev) begin
                T_l    <= hold_T;
                gm_l   <= hold_gmask;
                wexp_l <= hold_wexp;
                ntr    <= 8'd0;
                wc     <= 20'd0;
                busy   <= 1'b1;
                done   <= 1'b0;
                st     <= (hold_T == 8'd0) ? ST_DONE : ST_CLR;
            end
        end
        ST_END: begin                       // clr high, L still high
            clr <= 1'b1;
            wc  <= wc + 20'd1;
            if (wc == 20'd3) begin
                wc <= 20'd0;
                st <= (ntr == T_l) ? ST_DONE : ST_CLR;
            end
        end
        ST_CLR: begin                       // clr high, L low
            clr <= 1'b1;
            lgo <= {G{1'b0}};
            wc  <= wc + 20'd1;
            if (wc == 20'd15) begin
                wc  <= 20'd0;
                clr <= 1'b0;
                st  <= ST_REL;
            end
        end
        ST_REL: begin                       // clr low, L low, a = b = 0
            wc <= wc + 20'd1;
            if (wc == 20'd15) begin
                wc  <= 20'd0;
                lgo <= gm_l;
                st  <= ST_LAUNCH;
            end
        end
        ST_LAUNCH: begin
            wc <= wc + 20'd1;
            if (wc == half) late_en <= 1'b1;
            if (wc == win - 20'd1) begin
                wc    <= 20'd0;
                tally <= 1'b1;
                st    <= ST_TALLY;
            end
        end
        ST_TALLY: begin                     // counters take s2 on this edge
            ntr     <= ntr + 8'd1;
            clr     <= 1'b1;
            late_en <= 1'b0;
            st      <= ST_END;
        end
        ST_DONE: begin
            clr     <= 1'b1;
            lgo     <= {G{1'b0}};
            late_en <= 1'b0;
            busy    <= 1'b0;
            done    <= 1'b1;
            if (!go_s[1]) st <= ST_IDLE;
        end
        default: st <= ST_IDLE;
        endcase
    end

    wire zero_now = (st == ST_IDLE) && zero_s[1];

    // ---- the instances -----------------------------------------------------
    wire [NI*32-1:0] cnt_flat;
    wire [NI*8-1:0]  bits_flat;
    wire [NI*10-1:0] desc_flat;

    genvar i;
    generate for (i = 0; i < NI; i = i + 1) begin : inst
        localparam integer KIND = kind_of(i);
        localparam integer KA   = ka_of(i);
        localparam integer KB   = kb_of(i);
        localparam [1:0]   KIND2 = KIND;
        localparam [3:0]   KA4   = KA;
        localparam [3:0]   KB4   = KB;

        wire la, lb, a, b, q;

        // Twin launch flops, same D, same edge.  Primitives, kept, so that
        // nothing merges them.
        (* keep *) FDRE #(.INIT(1'b0)) fa (.C(rclk), .CE(1'b1), .R(1'b0),
                                           .D(lgo[i / S]), .Q(la));
        (* keep *) FDRE #(.INIT(1'b0)) fb (.C(rclk), .CE(1'b1), .R(1'b0),
                                           .D(lgo[i / S]), .Q(lb));

        bd_delay #(.N(KA)) da (.a(la), .z(a));
        bd_delay #(.N(KB)) db (.a(lb), .z(b));

        if (KIND == 3) begin : pl
            // The cell with its loop cut: a.~b.~clr, same pin order as bd_c2n.
            (* keep *) LUT3 #(.INIT(8'h02)) u (.I0(a), .I1(b), .I2(clr), .O(q));
        end else begin : ce
            // The cell under test, unmodified: rtl/bd_ce.v.
            bd_c2n dut (.a(a), .b(b), .rst(clr), .q(q));
        end

        // The edge thermometer, clocked by q through fabric routing.
        wire e0, e1, lt;
        (* keep *) FDCE #(.INIT(1'b0)) t0 (.C(q), .CE(1'b1), .CLR(clr),
                                           .D(1'b1),    .Q(e0));
        (* keep *) FDCE #(.INIT(1'b0)) t1 (.C(q), .CE(1'b1), .CLR(clr),
                                           .D(e0),      .Q(e1));
        (* keep *) FDCE #(.INIT(1'b0)) t2 (.C(q), .CE(1'b1), .CLR(clr),
                                           .D(late_en), .Q(lt));

        // Into rclk, two flops each.
        reg [3:0] s1 = 4'h0, s2 = 4'h0, snap = 4'h0;
        reg [7:0] c_one = 8'h0, c_emit = 8'h0, c_multi = 8'h0, c_late = 8'h0;
        always @(posedge rclk) begin
            s1 <= {lt, e1, e0, q};
            s2 <= s1;
            if (zero_now) begin
                snap    <= 4'h0;
                c_one   <= 8'h0;
                c_emit  <= 8'h0;
                c_multi <= 8'h0;
                c_late  <= 8'h0;
            end else if (tally) begin
                snap <= s2;
                if (s2[0]) c_one   <= lfsr8(c_one);
                if (s2[1]) c_emit  <= lfsr8(c_emit);
                if (s2[2]) c_multi <= lfsr8(c_multi);
                if (s2[3]) c_late  <= lfsr8(c_late);
            end
        end

        assign cnt_flat[i*32 +: 32] = {c_late, c_multi, c_emit, c_one};
        assign bits_flat[i*8 +: 8]  = {s2, snap};
        assign desc_flat[i*10 +: 10] = {KIND2, KA4, KB4};
    end endgenerate

    // ---- calibration and liveness -----------------------------------------
    reg        cal_prev = 1'b0;
    reg [31:0] calc     = 32'h0;
    reg        rdiv     = 1'b0;
    reg [23:0] beat     = 24'h0;
    always @(posedge rclk) begin
        cal_prev <= cal_s[1];
        if (cal_s[1] && !cal_prev) calc <= 32'h0;
        else if (cal_s[1])         calc <= calc + 32'h1;
        rdiv <= ~rdiv;
        beat <= beat + 24'h1;
    end

    // ---- rclk -> TCK -------------------------------------------------------
    reg [1:0] busy_t = 2'b00, done_t = 2'b00, rs = 2'b00;
    always @(posedge tck) begin
        busy_t <= {busy_t[0], busy};
        done_t <= {done_t[0], done};
        rs     <= {rs[0], rdiv};
    end

    // ---- capture mux -------------------------------------------------------
    wire [31:0] cnt_sel  = cnt_flat[hold_inst * 32 +: 32];
    wire [7:0]  bits_sel = bits_flat[hold_inst * 8 +: 8];
    wire [9:0]  desc_sel = desc_flat[hold_inst * 10 +: 10];
    localparam [7:0] NI8 = NI;

    reg [31:0] mux_d;
    always @* begin
        case (hold_addr)
            4'd0:  mux_d = cnt_sel;
            4'd1:  mux_d = {24'h0, bits_sel};
            4'd2:  mux_d = {gm_l, T_l, 5'h0, st, ntr};
            4'd3:  mux_d = {NI8, 7'h0, hold_inst, desc_sel};
            4'd8:  mux_d = 32'hDEAD_BEEF;
            4'd9:  mux_d = 32'h5A5A_1234;
            4'd10: mux_d = 32'h0000_0000;
            4'd12: mux_d = {31'h0, rs[1]};
            4'd13: mux_d = {2'b00, hold[33:4]};
            4'd14: mux_d = calc;
            default: mux_d = 32'h0000_0000;
        endcase
    end

    wire poison = ((hold_addr == 4'd0) && busy_t[1])
               || ((hold_addr == 4'd14) && hold_cal);
    wire [31:0] cap_data = poison ? 32'hFFFF_FFFF : mux_d;

    wire [W-1:0] cap_word = {TAG,          // [47:40]
                             2'b00,        // [39:38]
                             done_t[1],    // [37]
                             busy_t[1],    // [36]
                             hold_addr,    // [35:32]
                             cap_data};    // [31:0]

    // ---- shift register ----------------------------------------------------
    reg [W-1:0] sr = {W{1'b0}};

    always @(posedge tck) begin
        if (bs_sel && bs_capture)     sr <= cap_word;
        else if (bs_sel && bs_shift)  sr <= {bs_tdi, sr[W-1:1]};
    end

    always @(posedge tck) begin
        if (bs_sel && bs_update) hold <= sr[33:0];
    end

    assign sr_tdo = sr[0];

    // Diagnostic only: red follows busy, green is an rclk heartbeat (~2 Hz).
    // Board LED polarity is suspected active-low (hw-docs 02).
    assign led_red   = busy;
    assign led_green = beat[23];

endmodule

`default_nettype wire
