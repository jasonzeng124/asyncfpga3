// fomu_uart_top -- same gcd(48,36) self-test as fomu_top.sv, but reports
// status over a USB-CDC virtual serial port (vendored tinyfpga_bx_usbserial
// core, fomu/usb/*.v) instead of only the RGB LED, for real automated
// readback instead of eyeballing LED colors.
//
// Repeatedly transmits an 8-byte status line "X:HHHH\r\n" where X is
// B(lue, i_ack not seen yet)/R(ed, accepted but not done)/P(ass)/F(ail),
// and HHHH is the last-seen o_data value in hex (0000 until latched).
module fomu_uart_top (
    input        clki,
    inout        usb_dp,
    inout        usb_dn,
    output       usb_dp_pu,
    output       rgb0,
    output       rgb1,
    output       rgb2
);

    assign usb_dp_pu = 1'b1;   // this build DOES want USB enumeration

    // Three copies of the same 48MHz input clock, on three separate
    // global buffers. This is a TIMING-GRAPH partition, not a real
    // multi-clock design: every reg that DRIVES the clockless gcd core
    // sits on clk_drv, every reg that SAMPLES it sits on clk_smp, and
    // everything that must genuinely close at 48MHz (the USB-CDC core
    // + TX FSM) stays on clk_48mhz. The reg->async-cone->reg paths
    // through the gcd core thereby become cross-domain, which nextpnr
    // leaves unconstrained -- without this, those false paths sit at
    // ~-1000ns slack in the 48MHz domain and criticality-normalization
    // makes the placer treat the USB core's real -8ns paths as
    // zero-priority (measured: est fmax 34MHz -> broken enumeration).
    // All clk_drv/clk_smp <-> clk_48mhz crossings are either 2-flop
    // synchronized, quasi-static status bits, or reset -- a torn read
    // can at worst garble one status message, never corrupt the USB
    // core. Skew between the three copies is one-GB-insertion-delta
    // (sub-ns), irrelevant at these crossing rates.
    wire clk_48mhz, clk_drv, clk_smp;
    SB_GB clk_gb (
        .USER_SIGNAL_TO_GLOBAL_BUFFER(clki),
        .GLOBAL_BUFFER_OUTPUT(clk_48mhz)
    );
    SB_GB clk_gb_drv (
        .USER_SIGNAL_TO_GLOBAL_BUFFER(clki),
        .GLOBAL_BUFFER_OUTPUT(clk_drv)
    );
    SB_GB clk_gb_smp (
        .USER_SIGNAL_TO_GLOBAL_BUFFER(clki),
        .GLOBAL_BUFFER_OUTPUT(clk_smp)
    );

    reg [15:0] reset_cnt = 0;
    wire async_rst = ~reset_cnt[15];
    always @(posedge clk_drv)
        if (!reset_cnt[15]) reset_cnt <= reset_cnt + 16'b1;

    localparam [15:0] TEST_A   = 16'd48;
    localparam [15:0] TEST_B   = 16'd36;
    localparam [15:0] EXPECTED = 16'd12;
    wire [31:0] i_data = {TEST_B, TEST_A};

    // clk_drv domain: everything whose outputs feed the async core
    // (i_req, o_ack) launches from here.
    //
    // PROPER 4-PHASE ENTRY -- this fixed the on-silicon "while-loop
    // never completes" hang. An earlier version raised i_req once and
    // held it high forever ("one call"); but alib_hlatch's controller
    // only returns to zero when i_req=0 & o_ack=1, so a held-high
    // i_req freezes c0/lat1/c1 high, which keeps the loop merge's
    // a-side (and thus c3_req) high forever, and the loopback token's
    // b-side rise produces no new request edge: deadlock after exactly
    // one loop traversal (observed on hardware as R:111 / c3 stuck at
    // 1). The environment MUST complete the return-to-zero, exactly
    // like the generated simulation TB does: req up, wait ack, req
    // down. Single-shot behavior comes from never re-raising i_req,
    // not from holding it.
    reg started = 1'b0;
    reg i_req_r = 1'b0;
    always @(posedge clk_drv) begin
        if (async_rst) begin
            started <= 1'b0;
            i_req_r <= 1'b0;
        end else if (!started) begin
            i_req_r <= 1'b1;
            started <= 1'b1;
        end else if (i_req_r && i_ack_q) begin
            i_req_r <= 1'b0;   // RTZ: unblocks the ring's return-to-zero wave
        end
    end

    wire        i_ack, o_req;
    wire [15:0] o_data;
    reg         o_ack_r = 1'b0;
    wire        dbg_c3_req, dbg_c8_req, dbg_c9_req;
    wire        dbg_c11_req, dbg_c12_req, dbg_c15_req, dbg_c17_req;

    gcd dut (
        .i_req(i_req_r), .i_ack(i_ack), .i_data(i_data),
        .o_req(o_req),   .o_ack(o_ack_r), .o_data(o_data),
        .rst(async_rst),
        .dbg_c3_req(dbg_c3_req), .dbg_c8_req(dbg_c8_req), .dbg_c9_req(dbg_c9_req),
        .dbg_c11_req(dbg_c11_req), .dbg_c12_req(dbg_c12_req),
        .dbg_c15_req(dbg_c15_req), .dbg_c17_req(dbg_c17_req)
    );

    // 2-flop synchronizers on the async core's outputs -- see
    // fomu_top.sv for the full rationale (nextpnr's post-route
    // hold-violation report confirmed direct sampling was a real
    // metastability risk).
    // clk_smp domain: everything that samples the async core's
    // outputs (i_ack/o_req/o_data and the dbg taps) lands here.
    reg [1:0] i_ack_sync = 2'b00, o_req_sync = 2'b00;
    always @(posedge clk_smp) begin
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

    reg        done = 1'b0;
    reg        pass = 1'b0;
    reg [15:0] o_data_latched = 16'h0000;
    reg        i_ack_seen = 1'b0, o_req_seen = 1'b0;
    always @(posedge clk_smp) begin
        if (async_rst) begin
            done <= 1'b0; pass <= 1'b0;
            i_ack_seen <= 1'b0; o_req_seen <= 1'b0;
            o_data_latched <= 16'h0000;
        end else begin
            if (i_ack_q) i_ack_seen <= 1'b1;
            if (o_req_q && !done) begin
                done           <= 1'b1;
                pass           <= (o_data == EXPECTED);
                o_data_latched <= o_data;
            end
            if (o_req_q) o_req_seen <= 1'b1;
        end
    end

    // o_ack drives the async core, so it launches from clk_drv (its
    // input o_req_q is a clk_smp reg -- quasi-static crossing). Proper
    // 4-phase passive receiver: ack simply mirrors the (synchronized)
    // request, so the output handshake fully returns to zero and the
    // ready-token interlock can recycle. (The earlier version latched
    // o_ack high forever -- same held-high protocol violation as the
    // old i_req above.)
    always @(posedge clk_drv) begin
        if (async_rst) o_ack_r <= 1'b0;
        else           o_ack_r <= o_req_q;
    end

    // ---- loop-iteration instrumentation -----------------------------
    // dut.c3_req is the while-ring's top-of-loop hlatch (lat3) input
    // request: fires once for the initial entry, then once per loop
    // iteration (see build/gcd_tight_pass1/gcd.v: mg2 -> lat3 -> [cond,
    // steer, if-body, merge] -> lat17 -> lat18 -> loopback to mg2 -- the
    // 3-hlatch ring CLAUDE.md invariant #5 requires). gcd(48,36) needs 3
    // iterations (48,36->12,36->12,24->12,12), so a correct run should
    // see this fire 4 times total (1 entry + 3 iterations) before o_req.
    // Request-edge gray counters. A 4-phase req pulse can be shorter
    // than one 48MHz period (rise to RTZ is a handful of LUT hops), so
    // a clocked sampling counter can silently undercount; clocking a
    // counter BY the request edge itself catches every rise. Gray
    // coding makes the cross-domain read safe: a torn sample decodes
    // to either the old or the new count, never garbage. No reset --
    // ice40 DFFs power up to the declared init value, and the async
    // core is held in reset (all reqs low) until long after config.
    // Each counter is its own tiny "clock domain"; every path touching
    // it is cross-domain and thus unconstrained, so this adds zero
    // pressure on the USB core's 48MHz closure (see clock note above).
    `define REQ_GRAY_COUNTER(req, gray) \
        reg [3:0] gray``_bin = 4'h0;  reg [3:0] gray = 4'h0; \
        always @(posedge req) begin \
            gray``_bin <= gray``_bin + 4'd1; \
            gray <= (gray``_bin + 4'd1) ^ ((gray``_bin + 4'd1) >> 1); \
        end
    `REQ_GRAY_COUNTER(dbg_c12_req, c12_gray)
    `REQ_GRAY_COUNTER(dbg_c15_req, c15_gray)
    `REQ_GRAY_COUNTER(dbg_c17_req, c17_gray)

    // 2-flop sync each gray count into clk_smp, decode to binary.
    `define GRAY_SAMPLE(gray, cnt) \
        reg [3:0] gray``_s1 = 0, gray``_s2 = 0; \
        always @(posedge clk_smp) begin \
            gray``_s1 <= gray;  gray``_s2 <= gray``_s1; \
        end \
        wire [3:0] cnt = gray``_s2 ^ (gray``_s2 >> 1) ^ \
                         (gray``_s2 >> 2) ^ (gray``_s2 >> 3);
    `GRAY_SAMPLE(c12_gray, c12_cnt)
    `GRAY_SAMPLE(c15_gray, c15_cnt)
    `GRAY_SAMPLE(c17_gray, c17_cnt)

    // ---- USB-UART TX: repeatedly stream "X:ABC:HHHH\r\n" ----------------
    // X = B/R/P/F status (see above); A=c12 (lat12 out), B=c15 (mg16
    // merge out), C=c17 (lat18 out = loopback) request-rise counts --
    // chosen to bisect the dead zone found by the previous tap set
    // (c3=c8=c9=1: token died between the a>b steer and the loop-top);
    // HHHH = last-seen o_data value in hex. Decode (given c9=1):
    // 000 -> stuck in fdel11/lat12; 100 -> stuck in mg16; 110 -> stuck
    // in lat17/lat18; 111 -> stuck in mg2 (loop-top merge).
    function [7:0] hex_ascii(input [3:0] nib);
        hex_ascii = (nib < 10) ? (8'h30 + {4'b0, nib}) : (8'h41 + {4'b0, nib} - 8'd10);
    endfunction

    wire [7:0] status_char = !i_ack_seen        ? "B" :
                             !o_req_seen        ? "R" :
                             pass               ? "P" : "F";

    reg [3:0] msg_idx = 0;
    wire [7:0] msg_byte =
        (msg_idx == 4'd0)  ? status_char :
        (msg_idx == 4'd1)  ? ":" :
        (msg_idx == 4'd2)  ? hex_ascii(c12_cnt) :
        (msg_idx == 4'd3)  ? hex_ascii(c15_cnt) :
        (msg_idx == 4'd4)  ? hex_ascii(c17_cnt) :
        (msg_idx == 4'd5)  ? ":" :
        (msg_idx == 4'd6)  ? hex_ascii(o_data_latched[15:12]) :
        (msg_idx == 4'd7)  ? hex_ascii(o_data_latched[11:8]) :
        (msg_idx == 4'd8)  ? hex_ascii(o_data_latched[7:4]) :
        (msg_idx == 4'd9)  ? hex_ascii(o_data_latched[3:0]) :
        (msg_idx == 4'd10) ? 8'h0D : 8'h0A;

    // throttle: send one message roughly every ~130ms (48MHz / 2^23)
    reg [22:0] pace_cnt = 0;
    reg        sending  = 1'b0;

    wire       uart_in_ready;
    reg        uart_in_valid = 1'b0;
    reg  [7:0] uart_in_data  = 8'h00;

    always @(posedge clk_48mhz) begin
        if (async_rst) begin
            msg_idx <= 0; pace_cnt <= 0; sending <= 1'b0;
            uart_in_valid <= 1'b0;
        end else begin
            pace_cnt <= pace_cnt + 23'b1;
            if (!sending && pace_cnt == 0) begin
                sending       <= 1'b1;
                msg_idx       <= 0;
                uart_in_data  <= msg_byte;
                uart_in_valid <= 1'b1;
            end else if (uart_in_valid && uart_in_ready) begin
                if (msg_idx == 4'd11) begin
                    sending       <= 1'b0;
                    uart_in_valid <= 1'b0;
                end else begin
                    msg_idx       <= msg_idx + 4'b1;
                    uart_in_data  <= msg_byte;
                end
            end
        end
    end

    wire [7:0] uart_out_data;
    wire       uart_out_valid;
    wire [11:0] usb_debug;

    // UART-triggered return to the DFU bootloader: receiving 'R' over
    // the CDC port pulses SB_WARMBOOT.BOOT with S1/S0=00. Foboot is
    // multiboot image 0 and its REBOOT register maps IMAGE straight
    // onto SB_WARMBOOT S1/S0 (rm.fomu.im/reboot.html: "The bootloader
    // is image 0, so set these bits to 0 to reboot back into the
    // bootloader"), so this reconfigures the FPGA straight into DFU
    // mode -- fully software-controlled reflash, no physical replug.
    reg wb_boot = 1'b0;
    always @(posedge clk_48mhz)
        if (uart_out_valid && uart_out_data == "R") wb_boot <= 1'b1;
    SB_WARMBOOT warmboot (.BOOT(wb_boot), .S1(1'b0), .S0(1'b0));

    usb_uart u_usb_uart (
        .clk_48mhz     (clk_48mhz),
        .reset         (async_rst),
        .pin_usb_p     (usb_dp),
        .pin_usb_n     (usb_dn),
        .uart_in_data  (uart_in_data),
        .uart_in_valid (uart_in_valid),
        .uart_in_ready (uart_in_ready),
        .uart_out_data (uart_out_data),
        .uart_out_valid(uart_out_valid),
        .uart_out_ready(1'b1),   // no RX needed -- always sink incoming bytes
        .debug         (usb_debug)
    );

    // RGB kept as a coarse backup indicator (same PVT channel mapping as
    // fomu_top.sv), blinking so "board alive at all" is visible without
    // a host connected.
    reg [23:0] blink_cnt = 0;
    always @(posedge clk_48mhz) blink_cnt <= blink_cnt + 24'b1;
    wire blink = blink_cnt[23];
    wire blue_lvl  = !i_ack_seen;
    wire red_lvl   = i_ack_seen && !o_req_seen;
    wire green_lvl = o_req_seen && pass;

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
