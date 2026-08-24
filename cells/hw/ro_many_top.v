// ---------------------------------------------------------------------------
// ro_many_top.v -- the calibration experiment, as a POPULATION.
//
// WHY THIS EXISTS.  hw/ro_top.v measures five ring oscillators against their
// own routed SDF and hw/README.md carries the answer: measured = 0.975 x
// predicted, worst residual 8.5%.  verify/tighten.py spends that 8.5% as its
// guardband on every matched delay in the library.
//
// A rebuild disagreed with it.  Same RTL, same five rings, a different nextpnr
// placement: 0.933 scale, 30.7% worst residual, and this time the residual
// TRENDS with length (Spearman rho -0.90).  Ring 0 -- the shortest, at 7 links
// -- is the whole of the discrepancy, and short chains are most of what
// tighten.py emits.
//
// Five samples cannot tell those two apart:
//
//   nextpnr placed THAT ONE RING badly, in which case 30.7% is a tail draw
//   from a distribution whose bulk is much tighter, and the guardband question
//   is "what percentile does 8.5% buy";
//
//   or this REGION OF THE DIE is slow / short chains are systematically
//   mispredicted, in which case 8.5% is simply wrong and no percentile
//   argument rescues it.
//
// The difference is a distribution, and a distribution needs a population.
// This design is 128 rings instead of 5, which turns the guardband from the
// max of five samples into a percentile of a measured population, and turns
// "does the error trend with length" from a rank correlation over five points
// into a comparison of four distributions of 32 each.
//
// ---------------------------------------------------------------------------
// THE BLOCKER, AND THE WAY AROUND IT.
//
// In ro_top each ring clocks its own 32-bit counter, so each ring costs a
// BUFGCTRL.  Routed utilisation there is 6 of 32, and ro_top's own header
// records that 6 was already at the edge of what this part's clock router
// manages -- a 20-flop liveness scheme was abandoned for exactly that reason.
// 128 rings cannot each have a buffer.  LUTs are not the constraint (790 of
// the fabric's sites for five rings; the die has thousands spare).
//
// So the counters are TIME-MULTIPLEXED.  B = 8 measurement slots, each with
// its own BUFG and its own counter, and G = 16 groups scanned one at a time.
// Ring r has group g = r/B and slot b = r%B; only the rings of the selected
// group oscillate, and slot b's BUFG is driven by a G:1 mux that picks ring
// (sel_group*B + b).  Eight buffers total, independent of how many rings the
// population holds -- to add rings, add groups.
//
// WHY THE OTHER RINGS ARE STOPPED RATHER THAN LEFT RUNNING.  Two reasons and
// both matter.  Power: 128 rings turning at once is 16x the switching activity
// of 8, concentrated in fabric, and this design is its own heater -- a batch
// measured while the die is hot is not comparable to one measured cold, and
// the confound would be perfectly confounded with WHICH batch.  Gating to 8 at
// a time makes the switching activity CONSTANT across all sixteen batches, so
// whatever self-heating there is applies equally to every one of them.  And
// selection: a stopped ring holds a defined value, which is what lets the mux
// be a mux.
//
// WHY A MUX AND NOT AN OR TREE.  A disabled ring sits at fb = 1 (see the NAND
// below), so an OR of the group's ring nodes is stuck HIGH and the counter
// never sees an edge.  An AND would be stuck low for the mirrored reason once
// any ring stops.  The mux selects, and it selects the one node that is
// actually moving.  It lives OUTSIDE the ring loop, so its delay is not part
// of any period being measured -- the ring closes through its own NAND and
// nothing else.
//
// WHY THE LENGTHS ROTATE BY BOTH INDICES.  Ring r gets LENS[(g + b) % 4].
// Rotating by g alone would give every ring in a group the same length, so a
// batch effect (the die warmer on batch 9, a group whose enable arrived late)
// would land entirely on one length and read as a length effect.  Rotating by
// b alone would nail each length to one slot, so a slow counter, a slow BUFG,
// or an unlucky slot placement would read as a length effect instead.
// Rotating by BOTH decorrelates length from slot AND from group: each length
// appears in every group and in every slot, 32 instances each, and the
// measurement script can then ask whether high ratios cluster by slot or by
// group and get an answer that is not aliased onto length.
//
// ---------------------------------------------------------------------------
// THE ENABLE IS INSIDE THE LOOP AND IT COSTS NOTHING.
//
// ro_top closes each ring through one LUT1 inverter.  Here that LUT1 becomes a
// LUT2 NAND, INIT 4'h7: fb = ~(chain_z & en).
//
//   en = 1  ->  fb = ~chain_z, which is exactly ro_top's inverter, and the
//               loop oscillates with an odd inversion count.
//   en = 0  ->  fb = 1 unconditionally, the chain fills with a constant and
//               the ring stops in a defined state.
//
// A LUT2 and a LUT1 are the same physical LUT6 site with a different INIT, so
// the gate that stops the ring is free in area AND -- to the extent the SDF is
// believed at all, which is the very thing under test -- comparable in delay.
// Nothing was inserted into the loop that was not already there: the inversion
// that makes it oscillate is the same gate as the enable that stops it.
//
// The enable is not synchronised into the ring domain and does not need to be.
// It is combinational, the ring is free-running, and a glitch at the moment a
// group is selected cannot corrupt anything: the host selects the group, THEN
// clears the counters, THEN starts them.  By the time the window opens the
// selection has been settled for two JTAG scans, which is milliseconds.
//
// ---------------------------------------------------------------------------
// READBACK.  Unchanged from ro_top in every respect that the host code and the
// bring-up procedure depend on: BSCANE2 on USER1, a BUFG on TCK, one 48-bit DR
// with CAPTURE strictly before UPDATE, TAG = 0xA5 in the top byte, constants at
// 8, 9 and 10, the async ring sampler at 12.
//
// Written on UPDATE -- this is the one thing that grew, from 6 bits to 10:
//
//     [3:0]  addr    which register the NEXT capture presents
//     [4]    run     counters count while this is high
//     [5]    clear   counters and overflow flags reset while this is high
//     [9:6]  group   which group of eight rings oscillates and is muxed out
//
// Loaded on CAPTURE, byte for byte what ro_top loads:
//
//     [31:0]  data       the register selected by the PREVIOUS update
//     [35:32] addr echo
//     [36]    run echo
//     [37]    overflow   sticky, for the selected counter
//     [39:38] zero
//     [47:40] TAG = 0xA5
//
// THE DR IS NOT WIDENED, deliberately.  W = 48 is what the host's decode, its
// little-endian byte order and its field extraction are all written against,
// and widening it would silently invalidate every one of those without
// changing a single visible symptom -- a mis-aligned scan reads a plausible
// number.  The four new control bits fit in the unused top of the 48 shifted
// IN; nothing is needed in the direction shifted OUT.
//
// But a control field with no echo is a field you cannot prove arrived, and
// this one selects which sixteenth of the population is being measured -- get
// it wrong and every count is a real measurement of the wrong rings.  So
// ADDRESS 13 reads back {28'h0, hold[9:6]}.  It costs one mux leg and it turns
// "the group probably latched" into a readback the script checks on every
// batch before it believes a count.
//
// ADDRESSES.  0..7 are the eight slot counters -- NOT rings; which ring a slot
// held is (group, slot), and the group is what address 13 confirms.  8, 9 and
// 10 are the constants 0xDEADBEEF, 0x5A5A1234 and 0x00000000, readable before
// anything has been started, for the same reason ro_top has three and one of
// them zero: a single nonzero constant proves only that SOMETHING came back,
// three prove the address mux selects, that the shift alignment is right in
// both directions, and that the path is stuck neither at ones nor at zeros.
// 12 is the liveness sampler.  13 is the group echo.
//
// THE SAMPLER SAMPLES EIGHT NODES, NOT 128.  ro_top's header records that a
// twenty-flop liveness scheme did not route with six global buffers in play,
// and 128 flops in the TCK domain would be far worse.  It is also unnecessary:
// the question a dead counter cannot answer is "was the ring that this counter
// was actually clocked by turning", and that is the POST-MUX node, which is
// eight signals.  Sampling there tests the ring, the enable and the mux leg in
// one go -- strictly more of the path than sampling the ring nodes would.
// Scan it repeatedly: a turning ring is uncorrelated with TCK and returns a
// mixture, a stopped one returns the same bit every time.  The value is
// meaningless; the VARIANCE is the measurement.
//
// ---------------------------------------------------------------------------
// CROSSING OUT OF THE RING DOMAINS, unchanged from ro_top.  run and clear
// cross INTO each slot through a two-stage synchroniser so a counter never
// sees a half-changed enable, and a counter read while run is still asserted
// returns 0xFFFF_FFFF -- a value it cannot otherwise hold at the moment it is
// read, so a host that forgets to stop first gets an obvious poison instead of
// a plausible wrong number.  The stop takes two ring edges to cross, which is
// nanoseconds against a JTAG scan's milliseconds.
//
// OVERFLOW.  Sticky, per slot.  At an 8 s window the fastest ring here (7
// links, ~6 ns) reaches ~1.3e9, which fits 32 bits with room to spare.  A
// longer window does not, and the sticky bit is what says so rather than
// letting the count wrap into a plausible small number.
// ---------------------------------------------------------------------------

`default_nettype none

module ro_many_top (output wire led_red, output wire led_green);

    localparam integer B   = 8;          // measurement slots = BUFGs = counters
    localparam integer G   = 16;         // groups, scanned one at a time
    localparam integer K   = G * B;      // 128 rings
    localparam integer W   = 48;         // DR width -- do not widen, see header
    localparam [7:0]   TAG = 8'hA5;

    // Ring lengths in bd_delay links.  Ring r = g*B + b gets LENS[(g+b) % 4],
    // so each length appears 32 times, once in every group and once in every
    // slot per four.  See the header on why the rotation uses both indices.
    function integer ro_len(input integer g, input integer b);
        case ((g + b) % 4)
            0:       ro_len = 7;
            1:       ro_len = 15;
            2:       ro_len = 31;
            default: ro_len = 63;
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
    reg  [9:0] hold = 10'b0000_00_0000;
    wire [3:0] hold_addr  = hold[3:0];
    wire       hold_run   = hold[4];
    wire       hold_clr   = hold[5];
    wire [3:0] hold_group = hold[9:6];

    // ---- the rings ---------------------------------------------------------
    //
    // K rings, of which exactly the eight in group hold_group oscillate.  The
    // node published to the mux is fb, the NAND output -- the same node ro_top
    // taps for its BUFG and its sampler.
    wire [K-1:0] ring_fb;

    genvar g, b;
    generate for (g = 0; g < G; g = g + 1) begin : grp

        // One enable per group, fanning out to that group's eight rings.  A
        // plain comparison against the held group number; it crosses no clock
        // boundary because the rings have no clock.
        wire en = (hold_group == g[3:0]);

        for (b = 0; b < B; b = b + 1) begin : ro
            wire chain_z, fb;

            // The ring: one bd_delay chain -- the very cell tighten.py sizes
            // -- closed through a single inversion.  Odd inversion count is
            // what makes it oscillate; an even one would just latch.  The
            // inversion is a NAND rather than an inverter so that it also
            // stops the ring, at no cost: same LUT6 site, different INIT.
            //   INIT 4'h7 = ~(I1 & I0), so en=1 inverts and en=0 holds fb=1.
            bd_delay #(.N(ro_len(g, b))) d (.a(fb), .z(chain_z));
            (* keep *) LUT2 #(.INIT(4'h7)) inv (.I0(chain_z), .I1(en), .O(fb));

            assign ring_fb[g * B + b] = fb;
        end
    end endgenerate

    // ---- the eight measurement slots --------------------------------------
    wire [B*32-1:0] cnt_flat;
    wire [B-1:0]    ovf;
    wire [B-1:0]    slot_node;

    generate for (b = 0; b < B; b = b + 1) begin : slot

        // The G:1 mux.  Outside the ring, so its delay is not in any period
        // measured.  Selects rather than ORs because the fifteen rings not
        // selected are parked at 1 -- see the header.
        wire [G-1:0] cand;
        for (g = 0; g < G; g = g + 1) begin : leg
            assign cand[g] = ring_fb[g * B + b];
        end
        wire ck_raw = cand[hold_group];

        wire ck;
        BUFG bg (.I(ck_raw), .O(ck));

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

        assign cnt_flat[b*32 +: 32] = c;
        assign ovf[b] = o;
        assign slot_node[b] = ck_raw;

    end endgenerate

    // Sample each SELECTED ring node -- post mux, pre BUFG -- straight into
    // the TCK domain.  This is a deliberate asynchronous sample of a signal
    // with no timing relationship to the sampling clock, which is normally a
    // bug and is here the entire point.  Eight flops and no extra global
    // buffer, and it covers the ring, its enable and its mux leg at once: it
    // is the node the counter is actually clocked by.
    //
    // The value is meaningless.  The VARIANCE is the measurement.
    reg [B-1:0] rs0 = {B{1'b0}};
    reg [B-1:0] rs1 = {B{1'b0}};
    always @(posedge tck) begin
        rs0 <= slot_node;
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
            4'd5:  begin mux_d = cnt_flat[191:160]; mux_o = ovf[5]; end
            4'd6:  begin mux_d = cnt_flat[223:192]; mux_o = ovf[6]; end
            4'd7:  begin mux_d = cnt_flat[255:224]; mux_o = ovf[7]; end
            4'd8:  mux_d = 32'hDEAD_BEEF;
            4'd9:  mux_d = 32'h5A5A_1234;
            4'd10: mux_d = 32'h0000_0000;
            4'd12: mux_d = {24'h0, rs1};
            // The group echo.  Without it a wrong group is invisible: every
            // count is still a real measurement, of the wrong eight rings.
            4'd13: mux_d = {28'h0, hold_group};
            default: mux_d = 32'h0000_0000;
        endcase
    end

    // Poison a counter read taken while the counters are still running.  The
    // constants, the sampler and the group echo are exempt: they are the
    // bring-up and control probes and must answer whatever else is going on.
    wire is_cnt = (hold_addr <= 4'd7);
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
        if (bs_sel && bs_update) hold <= sr[9:0];
    end

    assign sr_tdo = sr[0];

    // Diagnostic only, and not depended on anywhere: red follows run, green is
    // slot 0's counter divided down.  Board polarity on this revision is
    // suspected active-low (hw-docs 02), so "lit" may mean 0 -- which is
    // exactly why nothing here is measured by looking at them.
    assign led_red   = hold_run;
    assign led_green = cnt_flat[22];

endmodule

`default_nettype wire
