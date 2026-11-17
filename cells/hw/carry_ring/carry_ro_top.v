// ---------------------------------------------------------------------------
// carry_ro_top.v -- where does THIS die sit in prjxray's CARRY4 and MUXF7 band?
//
// WHY.  research/SIM-VS-BOARD.md row 1-2: 128 LUT+wire rings put the board at
// x = 0.288 of [FAST_MIN, SLOW_MAX] for LUT and interconnect arcs, but CARRY4
// and F7/F8 (SELMUX2_1) arcs have never been measured, and no kernel latency
// can pin them (formal A13: in bundled data the cycle is set by matched LUT
// chains; moving CARRY/F7 over 0.2..1.0 moves collatz per-iteration time by
// 0.00 ns).  Yet the fastest candidates' weakest races (formal C36/C38/C42:
// xorshift item 35's loop-entry compare -> steer, collatz x0.55) depend on
// exactly that band.  This design measures it directly: ring oscillators whose
// loop runs through carry chains (and, separately, through MUXF7 select
// arcs), next to LUT-only rings of the ro_many kind, on one bitstream.
//
// INSTRUMENT.  hw/ro_many_top.v, unchanged in every respect the host depends
// on (hw/ro_many_measure.py's TCL drives this design as is): BSCANE2 USER1,
// 48-bit DR, TAG 0xA5, constants at 8/9/10, sampler at 12, group echo at 13,
// control word [3:0] addr, [4] run, [5] clear, [9:6] group.  8 slots (BUFG +
// 32-bit counter each), G = 8 groups of 8 rings scanned one at a time; only
// the selected group oscillates.  See ro_many_top.v's header for why each of
// those choices was made; nothing here reopens them.
//
// THE RINGS.  Ring r = g*8 + b has kind KIND[(g + b) % 8], so each kind sits
// once in every slot and once in every group (8 instances, 8 placements).
// Every ring closes through one LUT2 NAND, fb = ~(z & en) -- the ro_many
// inverter that also stops the ring -- and fb is the node the slot mux taps.
//
//   L8, L16   reference: fb -> 8 / 16 LUT1 buffers -> z.  ro_many's ring.
//   C1..C32   carry: fb -> 5 LUT1 buffers -> CARRY4[0].S0 -> CO3 -> COUT ->
//             CARRY4[1].CIN -> CO3 -> ... -> CARRY4[N-1].CO3 -> z.
//             CARRY4[0]: CYINIT = 1, DI = 0, S1..S3 = 1, so CO0 = S0 and
//             CO3 = S0; every later CARRY4: S = 1111 (propagate), DI = 0, so
//             CO3 = CIN.  The loop therefore holds S0->CO3 once and
//             CIN->CO3 N-1 times, and nothing else changes with N except the
//             one return wire from the chain's top back to the NAND.  The 5
//             buffers keep C1's period (~5 ns) inside what a BUFG + 32-bit
//             counter follows; they are the same in every carry ring and
//             cancel in any difference between lengths.
//   F8, F16   MUXF7 select path: fb -> 8 / 16 MUXF7 stages -> z, each stage
//             O = S ? I1 : I0 with I1 = 1, I0 = 0 (constant LUTs of the
//             stage's own slice), so O = S: the ring runs through the F7
//             S0 -> OUT arc (the select arc of every bd_mux) once per stage.
//             Same hop count as L8 / L16, so the difference is F7 S0->OUT
//             against LUT A->O6, per stage.
//
// THE CARRY S INPUTS ARE LUTs OF en: a CARRY4 S pin can only be driven by the
// LUT6 of its own slice, so each gets its own (* keep *) LUT1 of en.  Parked
// (en = 0), S = 0 everywhere, so every CO = DI = 0 and the NAND holds fb = 1;
// selecting the group turns S to 1 under CIN = 0 (no edge), and the NAND then
// releases exactly ONE edge.  None of these LUTs is in a loop.  (The MUXF7
// data inputs are constants instead -- see the F stage below for why.)
//
// WHAT IS MEASURED.  Per ring, prjxray gives each arc a [FAST_MIN, SLOW_MAX]
// band, so the period is linear in two numbers:
//     P = P_fast + x * (span of LUT, wire and site-pip arcs)
//                + y * (span of CARRY4 / SELMUX2_1 IOPATH arcs)
// exactly as cells/gls/gen.py annotates it with GLS_SDF_FIELD=band,
// GLS_SDF_BAND=x, GLS_SDF_BAND_CELL=CARRY4=y,SELMUX2_1=y.  The L rings pin x on
// this bitstream; the C rings give y_carry; the F rings give y_f7.
// hw/carry_ring/carry_fit.py does the fit and judges itself.
// ---------------------------------------------------------------------------

`default_nettype none

module carry_ro_top (output wire led_red, output wire led_green);

    localparam integer B   = 8;          // measurement slots = BUFGs = counters
    localparam integer G   = 8;          // groups, scanned one at a time
    localparam integer K   = G * B;      // 64 rings
    localparam integer W   = 48;         // DR width -- do not widen (ro_many)
    localparam integer PRE = 5;          // LUT buffers ahead of every carry chain
    localparam [7:0]   TAG = 8'hA5;

    // kind codes: 0 = L (LUT links), 1 = C (CARRY4 chain), 2 = F (MUXF7 chain)
    // KIND[(g+b)%8] = {L8, C1, C4, F8, C16, L16, C32, F16}
    function integer kcls(input integer g, input integer b);
        case ((g + b) % 8)
            0: kcls = 0;  1: kcls = 1;  2: kcls = 1;  3: kcls = 2;
            4: kcls = 1;  5: kcls = 0;  6: kcls = 1;  default: kcls = 2;
        endcase
    endfunction
    function integer klen(input integer g, input integer b);
        case ((g + b) % 8)
            0: klen = 8;  1: klen = 1;  2: klen = 4;  3: klen = 8;
            4: klen = 16; 5: klen = 16; 6: klen = 32; default: klen = 16;
        endcase
    endfunction

    // ---- BSCANE2 (USER1) -- as ro_many_top ---------------------------------
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

    reg  [9:0] hold = 10'b0000_00_0000;
    wire [3:0] hold_addr  = hold[3:0];
    wire       hold_run   = hold[4];
    wire       hold_clr   = hold[5];
    wire [3:0] hold_group = hold[9:6];

    // ---- the rings ---------------------------------------------------------
    wire [K-1:0] ring_fb;

    genvar g, b, i;
    generate for (g = 0; g < G; g = g + 1) begin : grp
        wire en = (hold_group == g[3:0]);

        for (b = 0; b < B; b = b + 1) begin : ro
            localparam integer KC = kcls(g, b);
            localparam integer N  = klen(g, b);
            wire z, fb;

            // the closing inversion, ro_many's NAND (INIT 4'h7 = ~(I1 & I0))
            (* keep *) LUT2 #(.INIT(4'h7)) inv (.I0(z), .I1(en), .O(fb));
            assign ring_fb[g * B + b] = fb;

            if (KC == 0) begin : lring
                (* keep *) wire [N:0] s;
                assign s[0] = fb;
                for (i = 0; i < N; i = i + 1) begin : lk
                    (* keep *) LUT1 #(.INIT(2'h2)) u (.I0(s[i]), .O(s[i+1]));
                end
                assign z = s[N];
            end

            if (KC == 1) begin : cring
                (* keep *) wire [PRE:0] s;
                assign s[0] = fb;
                for (i = 0; i < PRE; i = i + 1) begin : lk
                    (* keep *) LUT1 #(.INIT(2'h2)) u (.I0(s[i]), .O(s[i+1]));
                end
                (* keep *) wire [N:0] cy;      // cy[k] = CO3 of CARRY4 k-1
                for (i = 0; i < N; i = i + 1) begin : c4
                    // one LUT1 of en per static S pin: S can only come from
                    // the LUT6 of the CARRY4's own slice (see header)
                    wire s0, s1, s2, s3;
                    if (i == 0) begin : first
                        assign s0 = s[PRE];
                    end else begin : rest
                        (* keep *) LUT1 #(.INIT(2'h2)) us0 (.I0(en), .O(s0));
                    end
                    (* keep *) LUT1 #(.INIT(2'h2)) us1 (.I0(en), .O(s1));
                    (* keep *) LUT1 #(.INIT(2'h2)) us2 (.I0(en), .O(s2));
                    (* keep *) LUT1 #(.INIT(2'h2)) us3 (.I0(en), .O(s3));
                    wire [3:0] co, o;
                    (* keep *) CARRY4 cc (
                        .CI     (i == 0 ? 1'b0 : cy[i]),
                        .CYINIT (i == 0 ? 1'b1 : 1'b0),
                        .DI     (4'b0000),
                        .S      ({s3, s2, s1, s0}),
                        .CO     (co),
                        .O      (o));
                    assign cy[i+1] = co[3];
                end
                assign cy[0] = 1'b0;
                assign z = cy[N];
            end

            if (KC == 2) begin : fring
                (* keep *) wire [N:0] s;
                assign s[0] = fb;
                // I0 = 0, I1 = 1 as CONSTANTS (nextpnr ties each to a
                // constant LUT of the stage's slice), so every stage is a
                // buffer whether or not the group is selected.  A first
                // version used I1 = en, I0 = ~en: parked, every stage was an
                // INVERTER, and selecting the group flipped all of them at
                // once -- several edges injected into the ring, which then
                // ran at a fraction of its period (seen in the GLS: F8 at
                // 1.0 ns instead of 9.3).  Silicon would keep such a
                // multi-edge mode too.  With buffers the parked ring is all
                // ones and the NAND releases exactly one edge.
                for (i = 0; i < N; i = i + 1) begin : fk
                    (* keep *) MUXF7 m (.I0(1'b0), .I1(1'b1), .S(s[i]), .O(s[i+1]));
                end
                assign z = s[N];
            end
        end
    end endgenerate

    // ---- the eight measurement slots -- as ro_many_top ---------------------
    wire [B*32-1:0] cnt_flat;
    wire [B-1:0]    ovf;
    wire [B-1:0]    slot_node;

    generate for (b = 0; b < B; b = b + 1) begin : slot
        wire [G-1:0] cand;
        for (g = 0; g < G; g = g + 1) begin : leg
            assign cand[g] = ring_fb[g * B + b];
        end
        wire ck_raw = cand[hold_group[2:0]];

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
                if (&c) o <= 1'b1;
            end
        end

        assign cnt_flat[b*32 +: 32] = c;
        assign ovf[b] = o;
        assign slot_node[b] = ck_raw;
    end endgenerate

    reg [B-1:0] rs0 = {B{1'b0}};
    reg [B-1:0] rs1 = {B{1'b0}};
    always @(posedge tck) begin
        rs0 <= slot_node;
        rs1 <= rs0;
    end

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
            4'd13: mux_d = {28'h0, hold_group};
            default: mux_d = 32'h0000_0000;
        endcase
    end

    wire is_cnt = (hold_addr <= 4'd7);
    wire [31:0] cap_data = (is_cnt && hold_run) ? 32'hFFFF_FFFF : mux_d;

    wire [W-1:0] cap_word = {TAG, 2'b00, mux_o, hold_run, hold_addr, cap_data};

    reg [W-1:0] sr = {W{1'b0}};
    always @(posedge tck) begin
        if (bs_sel && bs_capture)     sr <= cap_word;
        else if (bs_sel && bs_shift)  sr <= {bs_tdi, sr[W-1:1]};
    end
    always @(posedge tck) begin
        if (bs_sel && bs_update) hold <= sr[9:0];
    end
    assign sr_tdo = sr[0];

    assign led_red   = hold_run;
    assign led_green = cnt_flat[22];

endmodule

`default_nettype wire
