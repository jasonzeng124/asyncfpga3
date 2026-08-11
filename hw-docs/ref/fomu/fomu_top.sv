// fomu_top -- standalone Fomu self-test harness for the async-hls `gcd`
// core. No USB device stack at all (usb_dp_pu tied low so the host never
// tries to enumerate us) -- this is a minimal first hardware bring-up,
// not a host-driven demo. Runs gcd(48, 36) = 12 once on power-up and
// shows the result on the RGB LED: blue while running, green if the
// result matches, red if it doesn't.
//
// The `gcd` core itself is clockless (see ../rtl/async_lib.v /
// ../README.md); clki/clk_48mhz here only drives this harness's
// synchronous glue (reset generator, one-shot request pulse, output
// latch) -- same role the icarus testbench plays in simulation, just
// realized as real synchronous logic since there's no host connection
// driving the handshake for this standalone test.
//
// Pin mapping (fomu/fomu_pvt.pcf) and the SB_RGBA_DRV instantiation
// follow https://github.com/jay20162016/fomu_async's hdl/fomu.sv (same
// author, cited as this project's inspiration in README.md).
module fomu_top (
    input        clki,
    inout        usb_dp,
    inout        usb_dn,
    output       usb_dp_pu,
    output       rgb0,
    output       rgb1,
    output       rgb2
);

    assign usb_dp_pu = 1'b0;   // no USB device stack -- don't enumerate
    assign usb_dp = 1'bz;
    assign usb_dn = 1'bz;

    wire clk_48mhz;
    SB_GB clk_gb (
        .USER_SIGNAL_TO_GLOBAL_BUFFER(clki),
        .GLOBAL_BUFFER_OUTPUT(clk_48mhz)
    );

    // Power-on reset: hold the async core's rst high for ~1.4ms (48MHz),
    // far more than the >=50ns CLAUDE.md requires in sim -- real silicon
    // needs time for the oscillator/PLL and the core's C-elements to
    // settle from a cold power-up.
    reg [15:0] reset_cnt = 0;
    wire async_rst = ~reset_cnt[15];
    always @(posedge clk_48mhz)
        if (!reset_cnt[15]) reset_cnt <= reset_cnt + 16'b1;

    // Fixed test vector: gcd(48, 36) = 12. i_data packs LSB-first (a in
    // low 16 bits, b in high 16 bits -- see the comment atop the
    // generated gcd.v and hlsc/build.py's state_rhs()).
    localparam [15:0] TEST_A   = 16'd48;
    localparam [15:0] TEST_B   = 16'd36;
    localparam [15:0] EXPECTED = 16'd12;
    wire [31:0] i_data = {TEST_B, TEST_A};

    // Single-shot request with PROPER 4-PHASE RTZ: raise i_req once
    // after reset, drop it as soon as i_ack is seen, never re-raise.
    // (An earlier version held i_req high forever, which -- per
    // alib_hlatch's ctl = C(~o_ack, i_req) -- freezes the entry chain
    // high, keeps the loop merge's a-side request up, and deadlocks
    // the while-ring after exactly one traversal. That, not a timing
    // gap, was the on-silicon "runs forever" failure; see
    // fomu_uart_top.sv where the UART instrumentation pinned it down.)
    reg started = 1'b0;
    reg i_req_r = 1'b0;
    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            started <= 1'b0;
            i_req_r <= 1'b0;
        end else if (!started) begin
            i_req_r <= 1'b1;
            started <= 1'b1;
        end else if (i_req_r && i_ack_q) begin
            i_req_r <= 1'b0;
        end
    end

    wire        i_ack, o_req;
    wire [15:0] o_data;
    reg         o_ack_r = 1'b0;
    wire        dbg_c3_req, dbg_c8_req, dbg_c9_req;

    gcd dut (
        .i_req(i_req_r), .i_ack(i_ack), .i_data(i_data),
        .o_req(o_req),   .o_ack(o_ack_r), .o_data(o_data),
        .rst(async_rst),
        .dbg_c3_req(dbg_c3_req), .dbg_c8_req(dbg_c8_req), .dbg_c9_req(dbg_c9_req)
    );

    // 2-flop synchronizers on the async core's outputs before they're
    // used in any clocked always-block. i_ack/o_req are genuinely
    // asynchronous signals from this harness's point of view (the gcd
    // core has no clock at all), so sampling them directly -- as an
    // earlier version of this file did -- is a real metastability risk;
    // nextpnr's post-route hold-violation report confirmed it (8
    // violations, all on i_ack/o_req/o_data nets feeding straight into
    // clocked registers with 0ps of margin). o_data itself doesn't need
    // its own synchronizer: invariant #1 (CLAUDE.md) guarantees data
    // settles before its request, and by the time o_req_q has been
    // through two synchronizer stages it's been stable far longer than
    // that -- so a direct read once o_req_q fires is safe.
    reg [1:0] i_ack_sync = 2'b00, o_req_sync = 2'b00;
    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            i_ack_sync <= 2'b00;
            o_req_sync <= 2'b00;
        end else begin
            i_ack_sync <= {i_ack_sync[0], i_ack};
            o_req_sync <= {o_req_sync[0], o_req};
        end
    end
    wire i_ack_q = i_ack_sync[1];
    wire o_req_q = o_req_sync[1];

    // Latch the result + comparison the moment o_req_q rises; o_ack
    // mirrors o_req (proper 4-phase passive receiver, lets the output
    // handshake and ready-token interlock fully return to zero).
    reg done = 1'b0;
    reg pass = 1'b0;
    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            done <= 1'b0; pass <= 1'b0; o_ack_r <= 1'b0;
        end else begin
            o_ack_r <= o_req_q;
            if (o_req_q && !done) begin
                done <= 1'b1;
                pass <= (o_data == EXPECTED);
            end
        end
    end

    // DIAGNOSTIC (first bring-up: core accepted i_req blue-blinked
    // forever, never turning green -- gcd never completed). Sticky-latch
    // i_ack/o_req individually so the LED shows exactly how far the
    // handshake got, instead of only the final done/pass result:
    //   blue forever   -> i_ack never asserted (core never even
    //                     accepted the input -- entry-side problem)
    //   red forever    -> i_ack seen but o_req never (input accepted,
    //                     internal computation/loop never finished)
    //   green          -> o_req seen (gcd actually completed; the
    //                     original done/pass logic above already
    //                     covers correctness once we get here)
    reg i_ack_seen = 1'b0, o_req_seen = 1'b0;
    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            i_ack_seen <= 1'b0; o_req_seen <= 1'b0;
        end else begin
            if (i_ack_q) i_ack_seen <= 1'b1;
            if (o_req_q) o_req_seen <= 1'b1;
        end
    end

    // DIAGNOSTIC 2 (UART instrumentation on real hardware showed i_ack
    // fires but o_req never does -- gcd's while loop never completes).
    // dbg_c3_req is the while-ring's top-of-loop hlatch (lat3) input
    // request: fires once for the initial entry, then once per loop
    // iteration (see build/gcd_tight_pass1/gcd.v: mg2 -> lat3 -> [cond,
    // steer, if-body, merge] -> lat17 -> lat18 -> loopback to mg2).
    // gcd(48,36) needs 3 iterations (48,36->12,36->12,24->12,12), so a
    // correct run sees this fire 4 times total before o_req. Instead of
    // UART (which broke USB enumeration when combined with this much
    // extra logic -- see git log), blink the count out on the LED:
    // iter_count+1 quick blinks per cycle, then a long pause, forever.
    reg [1:0] c3_req_sync = 2'b00;
    always @(posedge clk_48mhz)
        c3_req_sync <= async_rst ? 2'b00 : {c3_req_sync[0], dbg_c3_req};
    wire c3_req_q = c3_req_sync[1];

    reg       c3_req_prev = 1'b0;
    reg [3:0] iter_count  = 4'h0;
    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            c3_req_prev <= 1'b0;
            iter_count  <= 4'h0;
        end else begin
            c3_req_prev <= c3_req_q;
            if (c3_req_q && !c3_req_prev && iter_count != 4'hF)
                iter_count <= iter_count + 4'h1;
        end
    end

    // Blink-count sequencer: ~0.17s half-slots, (iter_count+1) blinks,
    // then PAUSE_SLOTS dark slots, then repeat.
    localparam SLOT_BITS   = 23;
    localparam PAUSE_SLOTS = 4'd6;
    reg [SLOT_BITS-1:0] sub_cnt  = 0;
    reg [3:0]           slot_idx = 0;
    wire [3:0] total_slots = iter_count + 4'd1 + PAUSE_SLOTS;
    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            sub_cnt <= 0; slot_idx <= 0;
        end else if (sub_cnt == {SLOT_BITS{1'b1}}) begin
            sub_cnt <= 0;
            slot_idx <= (slot_idx == total_slots - 4'd1) ? 4'd0 : slot_idx + 4'd1;
        end else begin
            sub_cnt <= sub_cnt + 1'b1;
        end
    end
    wire blink = (slot_idx <= iter_count) && !sub_cnt[SLOT_BITS-1];

    wire blue_lvl  = ~i_ack_seen;
    wire red_lvl   = (i_ack_seen & ~o_req_seen) | (o_req_seen & ~pass);
    wire green_lvl = o_req_seen & pass;

    // PVT board RGB-channel-to-pin mapping (differs from EVT/HACKER --
    // see im-tomu/fomu-workshop's hdl/verilog/blink/blink.v, the
    // upstream reference we cross-checked this against): RGB0PWM=green,
    // RGB1PWM=red, RGB2PWM=blue.
    SB_RGBA_DRV #(
        .CURRENT_MODE("0b1"),
        .RGB0_CURRENT("0b000011"),
        .RGB1_CURRENT("0b000011"),
        .RGB2_CURRENT("0b000011")
    ) rgb_driver (
        .CURREN(1'b1),
        .RGBLEDEN(1'b1),
        .RGB0PWM(green_lvl & blink),
        .RGB1PWM(red_lvl & blink),
        .RGB2PWM(blue_lvl & blink),
        .RGB0(rgb0),
        .RGB1(rgb1),
        .RGB2(rgb2)
    );

endmodule
