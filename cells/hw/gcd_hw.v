// ---------------------------------------------------------------------------
// gcd_hw.v -- hw/gcd_rig.v on the die, with a JTAG readback.
//
// The rig is the experiment; this file is the instrumentation around it, and
// it is deliberately the same instrumentation hw/arb_prot.v uses: a BSCANE2 on
// USER1, a 48-bit capture word with a distinct tag, a housekeeping ring
// oscillator that supplies the only clock on the part, a power-on reset, and
// an arming delay so the settling transient after configuration is not
// recorded as a result.  Nothing here is new; see arb_prot.v for why each
// piece is shaped the way it is.
//
// What IS new is the window sequencer.  gcd_rig.v's contract is that idx may
// change only while rst is asserted, so the vector cannot simply be counted
// up: each window edge asserts the rig's reset, moves idx, holds the reset for
// a while, and then lets the ring run for the rest of the window.  Sixteen
// windows cover the whole table, and each window is long enough for millions
// of laps of the fast vectors and thousands of the slow ones.
//
// -- READING IT --------------------------------------------------------------
//
//   err (addr 8)   must read 0000 -- sixteen bits, one per vector
//   ok  (addr 9)   must read FFFF -- if a bit here is 0 then that vector's
//                  err bit is not evidence of anything, because the rig never
//                  produced a checkable answer for it
//
// Both arrays are built from the same LUT3, the same INIT and the same arm
// gate, so a vector whose ok bit set could have set its err bit.
//
// -- THE LATENCY MEASUREMENT -------------------------------------------------
//
// hold[10] pins the rig to a single vector, hold[9:6].  With that set, addr 0
// (elapsed housekeeping cycles) and addr 1 (completed gcds) are a direct
// latency measurement for that one vector, on silicon, with routing in it --
// the first performance number this project has for a compiled kernel rather
// than for a cell.  The housekeeping ring's own period is what converts cycles
// to seconds and hw/ro_measure.py already calibrates it.
//
// Sweeping hold[9:6] across all sixteen gives the latency profile.  Note the
// number is per-gcd LATENCY, not throughput: gcd_rig.v keeps exactly one
// transaction in flight on purpose, because that is what makes the answer
// attributable to the operands.
// ---------------------------------------------------------------------------

`default_nettype none

module gcd_hw (output wire led_red, output wire led_green);

    localparam integer NVEC  = 16;
    localparam integer IDXW  = 4;
    localparam integer WFILT = 2;
    localparam integer CMPD  = 16;

    localparam integer W   = 48;      // DR width, same layout as arb_prot
    localparam [7:0]   TAG = 8'h6D;   // distinct from ro_top A5, arb_mtbf 55, arb_prot 3C

    localparam integer HKLEN = 17;

    // Explicit vectors for the configuration readback: a bit-select on an
    // integer localparam is not portable across yosys and iverilog.
    localparam [7:0] NVEC_V  = NVEC;
    localparam [7:0] CMPD_V  = CMPD;
    localparam [3:0] HKLEN_V = HKLEN;
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

    // ---- hold register -----------------------------------------------------
    // addr + run, as arb_prot has them, plus the two fields that make the
    // latency sweep possible: which vector to pin to, and whether to pin.
    reg  [10:0] hold = 11'h0;
    wire [4:0]  hold_addr = hold[4:0];
    wire        hold_run  = hold[5];
    wire [3:0]  hold_vec  = hold[9:6];
    wire        hold_pin  = hold[10];

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
        if (hk_run[1])              hk_cnt <= hk_cnt + 32'h1;
        if (hk_run[1] && (&hk_cnt)) hk_ovf <= 1'b1;
    end

    // ---- power-on reset ----------------------------------------------------
    // A shift register, not a counter: it carries no CARRY4 and starts at 0
    // under the global set/reset.  24 stages, for the reason arb_mtbf.v
    // records -- a 4-stage window was too short for the delay chains to settle
    // after configuration, and the symptom was not a slow start but a
    // C(x,.) = x capture that never cleared.
    reg [23:0] por_sr = 24'h0;
    always @(posedge hk_ck)
        por_sr <= {por_sr[22:0], 1'b1};
    wire por_done = por_sr[23];

    // ---- the window sequencer ----------------------------------------------
    localparam integer WINBITS = 16;
    reg [WINBITS-1:0] win_cnt = {WINBITS{1'b0}};
    always @(posedge hk_ck)
        win_cnt <= win_cnt + 1'b1;
    wire win_edge = &win_cnt;

    reg win_edge_d = 1'b0;
    always @(posedge hk_ck)
        win_edge_d <= win_edge;

    // Each window edge restarts the ring and moves the vector.  The restart is
    // 16 housekeeping cycles out of 65536, so it costs 0.02% of the run -- far
    // below anything the latency measurement resolves -- and it is what buys
    // the rig its "idx moves only while rst is asserted" contract for free.
    reg [15:0] rst_sr = 16'hFFFF;
    always @(posedge hk_ck)
        rst_sr <= win_edge_d ? 16'hFFFF : {rst_sr[14:0], 1'b0};

    reg [IDXW-1:0] idx = {IDXW{1'b0}};
    always @(posedge hk_ck)
        if (win_edge_d)
            idx <= hold_pin ? hold_vec : (idx + 1'b1);

    wire rig_rst = ~por_done | rst_sr[15];

    // ---- arming ------------------------------------------------------------
    // Late, and never during a restart.  arm_sr is the slow global arm
    // arb_mtbf/arb_prot use; the second term reopens the gate a good margin
    // after each window's reset releases, so the ring's own start-up transient
    // is never a result.  A sticky that is already set stays set -- the gate
    // only stops new ones.
    reg [31:0] arm_sr = 32'h0;
    always @(posedge hk_ck)
        if (win_edge_d && por_done)
            arm_sr <= {arm_sr[30:0], 1'b1};

    reg [15:0] settle_sr = 16'h0;
    always @(posedge hk_ck)
        settle_sr <= rig_rst ? 16'h0 : {settle_sr[14:0], 1'b1};

    wire armed = arm_sr[31] & settle_sr[15];

    // ---- the rig -----------------------------------------------------------
    wire rig_lap, rig_err, rig_ok, rig_probe;

    gcd_rig #(.IDXW(IDXW), .WFILT(WFILT), .CMPD(CMPD)) urig (
        .rst(rig_rst), .idx(idx),
        .lap(rig_lap), .err_flt(rig_err), .ok_flt(rig_ok), .probe(rig_probe));

    // ---- per-vector stickies -----------------------------------------------
    // One bit per vector rather than one aggregate bit, so a finding names the
    // vector it happened on and can be replayed against bdc/simcheck.py, which
    // drives the same table from the same reference.
    wire [NVEC-1:0] err_sticky;
    wire [NVEC-1:0] ok_sticky;

    genvar vi;
    generate for (vi = 0; vi < NVEC; vi = vi + 1) begin : vec
        wire sel = (idx == vi[IDXW-1:0]);

        wire err_raw, ok_raw;
        (* keep *) LUT2 #(.INIT(4'h8)) uerr_g (.I0(rig_err), .I1(sel), .O(err_raw));
        (* keep *) LUT2 #(.INIT(4'h8)) uok_g  (.I0(rig_ok),  .I1(sel), .O(ok_raw));

        (* keep *) LUT3 #(.INIT(8'hE0)) uerr_s (
            .I0(err_raw), .I1(err_sticky[vi]), .I2(armed), .O(err_sticky[vi]));
        (* keep *) LUT3 #(.INIT(8'hE0)) uok_s (
            .I0(ok_raw),  .I1(ok_sticky[vi]),  .I2(armed), .O(ok_sticky[vi]));
    end endgenerate

    // ---- completed gcds, counted on the die --------------------------------
    // The rig's lap signal is a real four-phase request, one rise per delivered
    // result.  Counting it against hk_cnt is the latency measurement; there is
    // no other way to get it, since estimating from the graph would ignore
    // routing and routing is three quarters of every hop on this part.
    wire lap_ck;
    BUFG bg_lap (.I(rig_lap), .O(lap_ck));

    reg  [1:0]  lap_run = 2'b00;
    reg  [31:0] lap_cnt = 32'h0;
    reg         lap_ovf = 1'b0;
    always @(posedge lap_ck) begin
        lap_run <= {lap_run[0], hold_run};
        if (lap_run[1])               lap_cnt <= lap_cnt + 32'h1;
        if (lap_run[1] && (&lap_cnt)) lap_ovf <= 1'b1;
    end

    // ---- asynchronous liveness sample, TCK domain --------------------------
    // The value is meaningless; variance across repeated scans is the proof
    // that the ring is turning rather than sitting at a value that would fake
    // a clean result.  ro_top's technique, same reasoning.
    localparam integer SB_W = 4;
    wire [SB_W-1:0] sample_bus = {rig_probe, rig_lap, hk_fb, por_done};
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
            5'd1:  begin mux_d = lap_cnt; mux_o = lap_ovf; end

            // Readback sanity: a fixed pattern proves the scan path, the
            // address decode and the bit order before any zero is believed.
            5'd2:  mux_d = 32'hDEAD_BEEF;
            5'd3:  mux_d = 32'h5A5A_1234;

            // Configuration, so the reader never has to assume what the
            // bitstream was built with.
            5'd4:  mux_d = {NVEC_V, CMPD_V, HKLEN_V, WFILT_V, 8'h0};

            5'd5:  mux_d = {21'h0, hold_pin, hold_vec, idx, armed, por_done, hold_run};
            5'd6:  mux_d = {28'h0, rs1};

            // A wrong answer -- must read all zero
            5'd8:  mux_d = {16'h0, err_sticky};

            // A right answer -- must read all ONE, or addr 8 is void
            5'd9:  mux_d = {16'h0, ok_sticky};

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
        if (hold_ce) hold <= sr[10:0];
    end

    assign sr_tdo = sr[0];

    // Diagnostic only -- see ro_top for why nothing here is measured by
    // looking at them.
    assign led_red   = hold_run;
    assign led_green = |err_sticky;

endmodule

`default_nettype wire
