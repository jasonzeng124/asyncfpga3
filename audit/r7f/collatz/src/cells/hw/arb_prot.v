// ---------------------------------------------------------------------------
// arb_prot.v -- the arbiter AS SHIPPED, on silicon, under sustained contention.
//
// hw/arb_mtbf.v measures bd_arbcell: the bare decision element, driven by two
// free-running rings, with no protocol, no server and no back-pressure.  That
// is the right scope for characterising the element and the WRONG scope for
// quoting a number about a compiled design, for two reasons:
//
//   1. bd_arbiter holds q while the shared resource is acknowledging, so its
//      two grants are separated by an entire server round-trip instead of
//      racing each other within ~100 ps.  Every grant-overlap mechanism
//      arb_mtbf spends its time on is a mechanism this configuration does not
//      have.
//   2. arb_mtbf's contention rate is set by two oscillators that ask ~10^8
//      times a second and ignore the answer.  A real client asks, waits, is
//      served, returns to zero, and only then asks again.  The rate at which
//      the decision element is actually put in the runt condition is set by
//      the handshake, not by a ring.
//
// So this design instantiates the cell a compiler would emit, wraps it in the
// protocol it was specified against, and asks the only two questions that
// remain once the hold is unconditional:
//
//   A.  Can both clients be acknowledged at once?   (A1 . A2)
//   B.  Can both grants be high at once?            (g1 . g2, width-filtered)
//
// Both must stay zero forever.  A is the protocol defect written up in
// rtl/bd_arb.v -- the unheld node manufactured half its acknowledges, and
// A1 . A2 is exactly its signature, because A1 = C(g1,A0) is still HOLDING
// high when g2 rises against a still-high A0.  B is the handover overlap.
//
// -- HOW THIS SELF-REPORTS ---------------------------------------------------
//
// A rig whose entire result is "two sticky bits stayed at zero" cannot tell a
// working arbiter from a dead one, and that failure mode is not hypothetical:
// every detector here is a LUT feedback latch, and a latch that never sets is
// indistinguishable from a latch that cannot.  So each instance carries a
// THIRD sticky on A1 ^ A2 -- normal, correct, exclusive service.  It uses the
// same LUT3, the same INIT, the same (* keep *) and the same arm gate as the
// two that must stay zero.
//
// The result is therefore a PAIR per instance, and only one pairing means
// anything:
//
//   serv=1, viol=0   the arbiter ran, the construction latches, nothing broke
//   serv=0           the instance never served anybody; its zeros prove
//                    nothing and it is excluded from the denominator
//   viol=1           the finding
//
// Instance 0's client-1 request additionally drives a BUFG and a 32-bit
// counter, so the handshake rate is measured on the die rather than estimated
// from ring lengths.  That is what converts elapsed time into arbitration
// events, which is the denominator MTBF is actually quoted against.
//
// -- WHAT THIS DOES NOT TEST -------------------------------------------------
//
// The metastability of q itself, directly.  Nothing can: a LUT hands on
// whatever level it is given, and the analog filter that would suppress an
// intermediate one is not buildable here.  What this measures is whether an
// intermediate q ever reaches an OUTPUT in a way the protocol can observe --
// which is the only form of the question a user of the cell cares about.
//
// The server is a delay chain, so it is the fastest legal four-phase consumer.
// A slower server holds A0 high longer, which widens the hold and can only
// reduce the exposure; this is therefore the hostile end of the range.
//
// Clients are self-timed off the arbiter's own acknowledges (r = delay(~A)),
// so they always want the resource back and contention is sustained for the
// whole run.  Their two chain lengths are unequal and coprime so the phase
// relationship between the two requests sweeps rather than sitting at one
// point -- the same argument tb_arb_overlap makes for its two oscillators.
// ---------------------------------------------------------------------------

`default_nettype none

module arb_prot (output wire led_red, output wire led_green);

    // Population size.  Every instance is bit-for-bit identical; what differs
    // between them is placement and routing, which is the only axis this part
    // varies along and the one that made 15 of arb_mtbf's 192 behave
    // differently from the other 177.
    localparam integer NARB  = 96;
    localparam integer NARBW = (NARB + 31) / 32;


    localparam integer W   = 48;      // DR width, same layout as ro_top
    localparam [7:0]   TAG = 8'h3C;   // distinct from ro_top's A5 and arb_mtbf's 55

    // Housekeeping ring: POR, arming, window timer, elapsed time.  Not a
    // stimulus -- nothing in the arbiters is driven from it.
    localparam integer HKLEN = 17;

    // Client and server chain lengths.  Unequal and coprime so the two
    // requests do not sit at a fixed phase; short, because the arbiter itself
    // contributes most of each loop and the point is a high handshake rate.
    localparam integer CLEN1 = 3;
    localparam integer CLEN2 = 5;
    localparam integer SLEN  = 2;

    // Width discriminator on the grant-overlap detector, same construction and
    // same measured passband as arb_mtbf's: rejects <=160 ps, passes >=320 ps.
    localparam integer WFILT = 2;

    // Explicit vectors for the configuration readback below: a bit-select on
    // an integer localparam is not portable across yosys and iverilog.
    localparam [7:0] NARB_V  = NARB;
    localparam [3:0] CLEN1_V = CLEN1;
    localparam [3:0] CLEN2_V = CLEN2;
    localparam [3:0] SLEN_V  = SLEN;
    localparam [3:0] WFILT_V = WFILT;

    // ---- BSCANE2 (USER1) ---------------------------------------------------
    wire bs_capture, bs_shift, bs_update, bs_sel;
    wire bs_tck_raw, bs_tdi;
    wire sr_tdo;

    (* keep *) BSCANE2 #(.JTAG_CHAIN(1)) bscan_i (
        .CAPTURE (bs_capture),
        .DRCK    (),
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

    // ---- hold register.  addr + run only, no clear bit, same as arb_mtbf --
    reg  [5:0] hold = 6'b00_0000;
    wire [4:0] hold_addr = hold[4:0];
    wire       hold_run  = hold[5];

    // ---- housekeeping ring and its counted clock ---------------------------
    wire hk_chain, hk_fb;
    bd_delay #(.N(HKLEN)) dhk (.a(hk_fb), .z(hk_chain));
    (* keep *) LUT1 #(.INIT(2'h1)) invhk (.I0(hk_chain), .O(hk_fb));

    wire hk_ck;
    BUFG bg_hk (.I(hk_fb), .O(hk_ck));

    reg  [1:0]  hk_run = 2'b00;
    reg  [31:0] hk_cnt = 32'h0;
    reg         hk_ovf = 1'b0;
    always @(posedge hk_ck) begin
        hk_run <= {hk_run[0], hold_run};
        if (hk_run[1])            hk_cnt <= hk_cnt + 32'h1;
        if (hk_run[1] && (&hk_cnt)) hk_ovf <= 1'b1;
    end

    // ---- power-on reset, then arming, exactly as arb_mtbf sequences them ---
    // por_done releases the arbiters; armed enables the sticky latches, much
    // later, so the settling transient that follows configuration is not
    // recorded as a result.  Both are shift registers rather than counters:
    // they carry no CARRY4 and start at 0 under the global set/reset.
    reg [23:0] por_sr = 24'h0;
    always @(posedge hk_ck)
        por_sr <= {por_sr[22:0], 1'b1};
    wire por_done = por_sr[23];

    wire arb_rst = ~por_done;

    localparam integer WINBITS = 16;
    reg [WINBITS-1:0] win_cnt = {WINBITS{1'b0}};
    always @(posedge hk_ck)
        win_cnt <= win_cnt + 1'b1;
    wire win_edge = &win_cnt;

    reg win_edge_d = 1'b0;
    always @(posedge hk_ck)
        win_edge_d <= win_edge;

    reg [31:0] arm_sr = 32'h0;
    always @(posedge hk_ck)
        if (win_edge_d && por_done)
            arm_sr <= {arm_sr[30:0], 1'b1};
    wire armed = arm_sr[31];

    // ---- the population ----------------------------------------------------
    wire [NARB-1:0] viol_sticky;   // A1 . A2      -- must stay 0
    wire [NARB-1:0] ovl_sticky;    // g1 . g2      -- must stay 0, width-filtered
    wire [NARB-1:0] serv_sticky;   // A1 ^ A2      -- must go 1, or the pair is void

    wire inst0_r1;
    wire [NARB-1:0] probe_A1, probe_A2;

    genvar ai;
    generate for (ai = 0; ai < NARB; ai = ai + 1) begin : arb
        wire r1, r2, A1, A2, R0, A0, g1, g2;

        // -- the cell under test, exactly as the library ships it ------------
        bd_arbiter uarb (
            .rst(arb_rst),
            .r1(r1), .A1(A1),
            .r2(r2), .A2(A2),
            .R0(R0), .A0(A0),
            .g1(g1), .g2(g2));

        // -- the shared server.  A0 = delay(R0) is the fastest legal
        // four-phase consumer: it acknowledges SLEN links after the request
        // arrives and returns to zero SLEN links after the request does.
        bd_delay #(.N(SLEN)) usrv (.a(R0), .z(A0));

        // -- two clients that always want it back.  r = delay(~A) is a
        // complete four-phase client: r rises, the arbiter and server take it,
        // A rises, r falls, A falls, r rises again.  The single inversion is
        // what makes the loop free-run; the chain sets its period.
        wire c1_n, c2_n;
        (* keep *) LUT1 #(.INIT(2'h1)) uinv1 (.I0(A1), .O(c1_n));
        (* keep *) LUT1 #(.INIT(2'h1)) uinv2 (.I0(A2), .O(c2_n));
        bd_delay #(.N(CLEN1)) uc1 (.a(c1_n), .z(r1));
        bd_delay #(.N(CLEN2)) uc2 (.a(c2_n), .z(r2));

        // -- A. both clients acknowledged at once.  The protocol defect. -----
        wire viol_raw;
        (* keep *) LUT2 #(.INIT(4'h8)) uviol_d (.I0(A1), .I1(A2), .O(viol_raw));
        (* keep *) LUT3 #(.INIT(8'hE0)) uviol_s (
            .I0(viol_raw), .I1(viol_sticky[ai]), .I2(armed),
            .O(viol_sticky[ai]));

        // -- B. both grants high at once, width-filtered.  Same two-LUT
        // discriminator arb_mtbf calibrated on this die; (* keep *) is
        // mandatory on the AND or an optimiser folds a & delay(a) to a. -----
        wire ovl_raw, ovl_d, ovl_flt;
        (* keep *) LUT2 #(.INIT(4'h8)) uovl_d (.I0(g1), .I1(g2), .O(ovl_raw));
        bd_delay #(.N(WFILT)) uovl_w (.a(ovl_raw), .z(ovl_d));
        (* keep *) LUT2 #(.INIT(4'h8)) uovl_a (.I0(ovl_raw), .I1(ovl_d), .O(ovl_flt));
        (* keep *) LUT3 #(.INIT(8'hE0)) uovl_s (
            .I0(ovl_flt), .I1(ovl_sticky[ai]), .I2(armed),
            .O(ovl_sticky[ai]));

        // -- C. normal exclusive service.  This is the one that must SET.
        // Same LUT3, same INIT, same arm gate as the two above, so if this
        // instance can latch at all, this bit says so -- and if it cannot,
        // the two zeros above are not evidence of anything.
        wire serv_raw;
        (* keep *) LUT2 #(.INIT(4'h6)) userv_d (.I0(A1), .I1(A2), .O(serv_raw));
        (* keep *) LUT3 #(.INIT(8'hE0)) userv_s (
            .I0(serv_raw), .I1(serv_sticky[ai]), .I2(armed),
            .O(serv_sticky[ai]));

        assign probe_A1[ai] = A1;
        assign probe_A2[ai] = A2;
        if (ai == 0) begin : tap
            assign inst0_r1 = r1;
        end
    end endgenerate

    // ---- handshake rate, measured on the die -------------------------------
    // Instance 0's client-1 request is a real oscillation whose period is the
    // whole arbitration loop.  Counting it converts elapsed seconds into
    // arbitration events, which is the denominator an MTBF is quoted against;
    // estimating it from chain lengths would ignore routing, and routing is
    // three quarters of every hop on this part.
    wire svc_ck;
    BUFG bg_svc (.I(inst0_r1), .O(svc_ck));

    reg  [1:0]  svc_run = 2'b00;
    reg  [31:0] svc_cnt = 32'h0;
    reg         svc_ovf = 1'b0;
    always @(posedge svc_ck) begin
        svc_run <= {svc_run[0], hold_run};
        if (svc_run[1])             svc_cnt <= svc_cnt + 32'h1;
        if (svc_run[1] && (&svc_cnt)) svc_ovf <= 1'b1;
    end

    // ---- readback padding --------------------------------------------------
    wire [NARBW*32-1:0] viol_pad = {{(NARBW*32 - NARB){1'b0}}, viol_sticky};
    wire [NARBW*32-1:0] ovl_pad  = {{(NARBW*32 - NARB){1'b0}}, ovl_sticky};
    wire [NARBW*32-1:0] serv_pad = {{(NARBW*32 - NARB){1'b0}}, serv_sticky};

    // ---- asynchronous liveness sample, TCK domain --------------------------
    // The value is meaningless; variance across repeated scans is the proof
    // that the arbiters are actually running rather than stuck at a value that
    // would fake a clean result.  ro_top's technique, same reasoning.
    localparam integer SB_W = 4;
    wire [SB_W-1:0] sample_bus = {probe_A1[1], probe_A2[0], probe_A1[0], hk_fb};
    reg  [SB_W-1:0] rs0 = {SB_W{1'b0}};
    reg  [SB_W-1:0] rs1 = {SB_W{1'b0}};
    always @(posedge tck) begin
        rs0 <= sample_bus;
        rs1 <= rs0;
    end

    // ---- capture mux -------------------------------------------------------
    reg [31:0] mux_d;
    reg        mux_o;
    always @* begin
        mux_d = 32'h0000_0000;
        mux_o = 1'b0;
        case (hold_addr)
            5'd0:  begin mux_d = hk_cnt;  mux_o = hk_ovf;  end
            5'd1:  begin mux_d = svc_cnt; mux_o = svc_ovf; end

            // Readback sanity: a fixed pattern proves the scan path, the
            // address decode and the bit order before any zero is believed.
            5'd2:  mux_d = 32'hDEAD_BEEF;
            5'd3:  mux_d = 32'h5A5A_1234;

            // Population size and configuration, so the reader never has to
            // assume what the bitstream was built with.
            5'd4:  mux_d = {8'h0, NARB_V, CLEN1_V, CLEN2_V, SLEN_V, WFILT_V};

            5'd5:  mux_d = {29'h0, armed, por_done, hold_run};
            5'd6:  mux_d = {28'h0, rs1};

            // A. protocol violation -- must read all zero
            5'd8:  mux_d = viol_pad[31:0];
            5'd9:  mux_d = viol_pad[63:32];
            5'd10: mux_d = viol_pad[95:64];

            // B. grant overlap, width-filtered -- must read all zero
            5'd12: mux_d = ovl_pad[31:0];
            5'd13: mux_d = ovl_pad[63:32];
            5'd14: mux_d = ovl_pad[95:64];

            // C. normal service -- must read all ONE, or A and B are void
            5'd16: mux_d = serv_pad[31:0];
            5'd17: mux_d = serv_pad[63:32];
            5'd18: mux_d = serv_pad[95:64];

            default: mux_d = 32'h0000_0000;
        endcase
    end

    // Poison a counter read taken while it is still running; the sticky bits
    // and the constants answer regardless.
    wire is_cnt = (hold_addr <= 5'd1);
    wire [31:0] cap_data = (is_cnt && hold_run) ? 32'hFFFF_FFFF : mux_d;

    wire [W-1:0] cap_word = {TAG,        // [47:40]
                             1'b0,       // [39]
                             mux_o,      // [38]
                             hold_run,   // [37]
                             hold_addr,  // [36:32]
                             cap_data};  // [31:0]

    // ---- shift register ----------------------------------------------------
    reg [W-1:0] sr = {W{1'b0}};

    wire         sr_ce = bs_sel && (bs_capture || bs_shift);
    wire [W-1:0] sr_d  = bs_capture ? cap_word : {bs_tdi, sr[W-1:1]};

    always @(posedge tck) begin
        if (sr_ce) sr <= sr_d;
    end

    wire hold_ce = bs_sel && bs_update;
    always @(posedge tck) begin
        if (hold_ce) hold <= sr[5:0];
    end

    assign sr_tdo = sr[0];

    // Diagnostic only -- see ro_top for why nothing here is measured by
    // looking at them.
    assign led_red   = hold_run;
    assign led_green = |viol_sticky | |ovl_sticky;

endmodule

`default_nettype wire
