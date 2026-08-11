// ---------------------------------------------------------------------------
// ro_top.v -- the calibration experiment.
//
// THE QUESTION.  Every number verify/tighten.py produces comes from nextpnr's
// routed SDF, and every delay in this library is sized against those numbers.
// Nothing in the seven gates asks whether the SDF is TRUE -- whether this die,
// at this voltage and this temperature, actually behaves the way prjxray's
// characterisation says it does.  If the SDF is wrong by a constant factor,
// every matched delay in the library is wrong by that factor and no simulation
// will ever say so.
//
// THE MEASUREMENT.  Five ring oscillators, each one a bd_delay chain of a
// different length closed through a single inverter.  A ring's period is twice
// its loop delay, so the period is a direct, unamplified reading of the same
// quantity the SDF claims to predict -- and because the lengths differ, a
// straight-line fit through the five periods separates the two things that
// matter:
//
//   the SLOPE is picoseconds per bd_delay link, which is the number tighten.py
//   spends, and it is measured here free of any fixed overhead;
//
//   the INTERCEPT is the inverter plus the long route that closes the loop,
//   which is exactly the per-ring overhead that would otherwise contaminate a
//   single-ring measurement and be mistaken for per-link cost.
//
// A single ring cannot separate those two and would answer the wrong question.
//
// That said, the straight line turned out to be the weaker of the two
// analyses, and the reason is worth carrying: nextpnr does not place two rings
// the same way, so the routed cost of a link is NOT constant across them and
// the five points miss a straight line by as much as a quarter.  The real
// comparison is per ring, against that ring's own routed prediction, which
// already accounts for how it was placed.  The five lengths still earn their
// keep -- they are what turns one number into a trend, and they are how you
// find out that the error does not depend on length.
//
// WHY A RING AND NOT A DELAY LINE WITH AN EDGE PUT THROUGH IT.  Measuring one
// edge needs a time reference finer than the thing being measured, and there
// is none on this board -- the EBAZ4205 has no PL oscillator at all.  A ring
// converts a picosecond interval into a frequency, and a frequency is measured
// by counting, which needs no fast reference: only a long window and a wall
// clock.  The host's wall clock over a multi-second window is good to about a
// part in ten thousand, which is far better than the answer needs.
//
// WHY THE COUNTERS ARE COMPARED TO EACH OTHER TOO.  The ratios between rings
// share the host's window exactly, so they are independent of how well the
// wall clock is known.  The slope from the ratios is therefore the more
// trustworthy of the two results, and the absolute scale is what the wall
// clock adds on top.
//
// ---------------------------------------------------------------------------
// READBACK.  BSCANE2 on USER1, driven from hw_server through a raw JTAG DR
// shift, so no PS, no AXI, no boot chain and no external pin is involved:
// after configuration this design is self-contained and the only thing the
// host does is scan a 48-bit register.
//
// The DR is one 48-bit word.  Written on UPDATE:
//
//     [3:0]  addr    which register the NEXT capture presents
//     [4]    run     counters count while this is high
//     [5]    clear   counters and overflow flags reset while this is high
//
// Loaded on CAPTURE:
//
//     [31:0]  data       the register selected by the PREVIOUS update
//     [35:32] addr echo
//     [36]    run echo
//     [37]    overflow   sticky, for the selected counter
//     [39:38] zero
//     [47:40] TAG = 0xA5
//
// CAPTURE strictly precedes UPDATE inside one DR scan, so a single scan both
// reads the state as it was and commits the next selection.  The host reads a
// register by scanning its address and then scanning again.
//
// ADDRESSES.  0..4 are the five ring counters, shortest first.  8, 9 and 10
// are constants -- 0xDEADBEEF, 0x5A5A1234 and 0x00000000.  Three constants
// rather than one, and one of them zero, because a single nonzero constant
// proves only that SOMETHING came back: three prove that the address mux
// selects, that the shift alignment is right in both directions, and that the
// path is not stuck at ones or at zeros.  They are readable before any ring
// has ever been started, which makes them the bring-up check as well.
//
// 12 is the ring sampler, and it earned its place.  A counter that reads zero
// has two completely different causes -- the ring is not turning, or the
// control word never arrived -- with opposite fixes, and no amount of staring
// at a zero separates them.  This does: five flops sampling the ring nodes
// directly in the TCK domain, an asynchronous sample of a signal with no
// timing relationship to the sampling clock.  That is normally a bug and is
// here the whole point.  Scan it twenty times: a turning ring returns a
// mixture of ones and zeros, a stopped one returns the same bit every time.
// The value is meaningless; the VARIANCE is the measurement.  It costs five
// flops and no global buffer, which matters -- see the note on buffers below.
//
// A liveness scheme built from a toggle flop per ring and a sticky
// change-detector was tried first and cost about twenty flops.  It did not
// route: six global buffers is already at the edge of what this part's clock
// router manages, and no placement seed recovered it.  The sampler answers the
// same question for a quarter of the logic and no extra clock load.
//
// ---------------------------------------------------------------------------
// CROSSING OUT OF THE RING DOMAINS.  A counter is clocked by its own ring and
// read from the TCK domain, which is not a clock relationship at all.  Two
// things keep that honest.  run and clear cross INTO each ring through a
// two-stage synchroniser, so a counter never sees a half-changed enable.  And
// a counter is only ever read while it is stopped: reading one with run still
// asserted returns 0xFFFFFFFF, a value the counter cannot otherwise hold at
// the moment it is read, so a host that forgets to stop first gets an obvious
// poison rather than a plausible wrong number.
//
// The stop itself is not instantaneous -- it takes two ring edges to cross --
// but ring edges are nanoseconds and JTAG scans are milliseconds, so by the
// time the host can ask, the counter has been still for a million periods.
//
// ---------------------------------------------------------------------------
// WHAT THIS DESIGN DOES NOT MEASURE.  A ring runs at its own natural rate with
// no load on it but the next stage and one BUFG tap.  It is the delay of a
// chain, not the delay of a chain doing anything, and a matched delay in a
// real cell sits beside logic that is contending for the same routing.  So the
// slope this yields is a floor: a lower bound on what a link costs, measured
// under the friendliest conditions the fabric offers.  If the SDF disagrees
// with THIS, it disagrees with the easy case.
// ---------------------------------------------------------------------------

`default_nettype none

module ro_top (output wire led_red, output wire led_green);

    localparam integer K   = 5;          // rings
    localparam integer W   = 48;         // DR width
    localparam [7:0]   TAG = 8'hA5;

    // Ring lengths in bd_delay links.  Spread wide so the straight-line fit
    // has a long lever arm, and floored at 7 so even the fastest ring stays
    // well under the rate a 32-bit synchronous counter closes at on this part.
    function integer ro_len(input integer i);
        case (i)
            0:       ro_len = 7;
            1:       ro_len = 15;
            2:       ro_len = 31;
            3:       ro_len = 63;
            default: ro_len = 127;
        endcase
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
    reg  [5:0] hold = 6'b00_0000;
    wire [3:0] hold_addr = hold[3:0];
    wire       hold_run  = hold[4];
    wire       hold_clr  = hold[5];

    // ---- the rings ---------------------------------------------------------
    wire [K*32-1:0] cnt_flat;
    wire [K-1:0]    ovf;
    wire [K-1:0]    ring_raw;

    genvar i;
    generate for (i = 0; i < K; i = i + 1) begin : ro
        wire chain_z, fb;

        // The ring: one bd_delay chain -- the very cell tighten.py sizes --
        // closed through a single inversion.  Odd inversion count is what
        // makes it oscillate; an even one would just latch.
        bd_delay #(.N(ro_len(i))) d (.a(fb), .z(chain_z));
        (* keep *) LUT1 #(.INIT(2'h1)) inv (.I0(chain_z), .O(fb));

        wire ck;
        BUFG bg (.I(fb), .O(ck));

        reg [1:0]  srun = 2'b00;
        reg [1:0]  sclr = 2'b00;
        reg [31:0] c    = 32'h0;
        reg        o    = 1'b0;

        always @(posedge ck) begin
            srun <= {srun[0], hold_run};
            sclr <= {sclr[0], hold_clr};
            if (sclr[1]) begin
                c <= 32'h0;
                o <= 1'b0;
            end else if (srun[1]) begin
                c <= c + 32'h1;
                if (&c) o <= 1'b1;      // sticky: the window was too long
            end
        end

        assign cnt_flat[i*32 +: 32] = c;
        assign ovf[i] = o;
        assign ring_raw[i] = fb;

    end endgenerate


    // Sample each ring node straight into the TCK domain.  This is a
    // deliberate asynchronous sample of a signal with no timing relationship
    // to the sampling clock, which is normally a bug and is here the entire
    // point: it costs five flops and no global buffer, and it answers the one
    // question a dead counter cannot distinguish.  A ring that is turning is
    // uncorrelated with TCK, so repeated scans return a mixture of ones and
    // zeros; a ring that is stopped returns the same bit every time.
    //
    // The value is meaningless.  The VARIANCE is the measurement.
    reg [K-1:0] rs0 = {K{1'b0}};
    reg [K-1:0] rs1 = {K{1'b0}};
    always @(posedge tck) begin
        rs0 <= ring_raw;
        rs1 <= rs0;
    end

    // ---- capture mux -------------------------------------------------------
    reg [31:0] mux_d;
    reg        mux_o;
    always @* begin
        mux_d = 32'h0000_0000;
        mux_o = 1'b0;
        case (hold_addr)
            4'd0:  begin mux_d = cnt_flat[ 31:  0]; mux_o = ovf[0]; end
            4'd1:  begin mux_d = cnt_flat[ 63: 32]; mux_o = ovf[1]; end
            4'd2:  begin mux_d = cnt_flat[ 95: 64]; mux_o = ovf[2]; end
            4'd3:  begin mux_d = cnt_flat[127: 96]; mux_o = ovf[3]; end
            4'd4:  begin mux_d = cnt_flat[159:128]; mux_o = ovf[4]; end
            4'd8:  mux_d = 32'hDEAD_BEEF;
            4'd9:  mux_d = 32'h5A5A_1234;
            4'd10: mux_d = 32'h0000_0000;
            4'd12: mux_d = {27'h0, rs1};
            default: mux_d = 32'h0000_0000;
        endcase
    end

    // Poison a counter read taken while the counters are still running.  The
    // constants are exempt: they are the bring-up probe and must answer
    // whatever else is going on.
    wire is_cnt = (hold_addr <= 4'd4);
    wire [31:0] cap_data = (is_cnt && hold_run) ? 32'hFFFF_FFFF : mux_d;

    wire [W-1:0] cap_word = {TAG,        // [47:40]
                             2'b00,      // [39:38]
                             mux_o,      // [37]
                             hold_run,   // [36]
                             hold_addr,  // [35:32]
                             cap_data};  // [31:0]

    // ---- shift register ----------------------------------------------------
    reg [W-1:0] sr = {W{1'b0}};

    always @(posedge tck) begin
        if (bs_sel && bs_capture)     sr <= cap_word;
        else if (bs_sel && bs_shift)  sr <= {bs_tdi, sr[W-1:1]};
    end

    always @(posedge tck) begin
        if (bs_sel && bs_update) hold <= sr[5:0];
    end

    assign sr_tdo = sr[0];

    // Diagnostic only, and not depended on anywhere: red follows run, green is
    // the slowest ring divided down to about a hertz.  Board polarity on this
    // revision is suspected active-low (hw-docs 02), so "lit" may mean 0 --
    // which is exactly why nothing here is measured by looking at them.
    assign led_red   = hold_run;
    assign led_green = cnt_flat[128 + 22];

endmodule

`default_nettype wire
