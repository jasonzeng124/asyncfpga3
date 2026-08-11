// knapsack_jtag_top -- "Path C" JTAG-driven harness for the knapsack
// async-hls core on the EBAZ4205 (xc7z010clg400-1): a BSCANE2 (USER1)
// shift-register bridge instead of zynq/knapsack_ps_top.v's PS7/AXI
// register map. No PS7, no AXI, no ARM DAP involvement -- the host
// drives the 4-phase handshake entirely through PL-TAP USER1 DR scans
// (hand-generated SVF played by openFPGALoader; see zynq/svfgen_jtag.py,
// which is the single generator for both the hardware SVF and the
// simulation scan-vector file tests/tb_jtag_bridge.v plays).
//
// ------------------------------------------------------------------
// DR chain: one 32-bit bidirectional scan register on USER1.
//
// WRITE side (shift register committed to the hold register on UPDATE;
// hold levels drive the core directly):
//   bit  7:0   i_data[7:0] = cap
//   bit  8     i_req
//   bit  9     o_ack
//   bit  10    rst          (core reset, ACTIVE-HIGH)
//   bit  31:11 ignored on write
//
// READ side (loaded into the shift register on CAPTURE):
//   bit  7:0   echo of held i_data
//   bit  8     echo of held i_req
//   bit  9     echo of held o_ack
//   bit  10    echo of held rst
//   bit  11    i_ack  (core -> host, 2-stage TCK synchronizer)
//   bit  12    o_req  (core -> host, 2-stage TCK synchronizer)
//   bit  15:13 TAG = 3'b101 (constant; proves USER1/BSCANE2 hookup and
//              scan alignment before any core interaction)
//   bit  31:16 o_data[15:0] (raw, NOT synchronized -- see contract below)
//
// On the wire (EBAZ4205 cascaded chain, openFPGALoader SVF player,
// empirically verified 2026-07-20 via zynq/svf/idcode_check.svf):
//   SIR 10 = (0x02 << 4) | 0xF = 0x02F   (USER1 + ARM DAP BYPASS)
//   SDR 33 = the 32-bit word above in the LOW 32 bits (TDI and TDO),
//            DAP bypass bit as the TOP bit.
//
// ------------------------------------------------------------------
// TAP sequencing this design relies on (IEEE 1149.1 DR-scan path:
// Select-DR -> Capture-DR -> Shift-DR -> Exit1-DR -> Update-DR):
// CAPTURE strictly precedes UPDATE within one scan, so a single scan
// atomically reads the pre-scan status AND commits a new control word.
// The SVF generator uses this to e.g. check i_ack=1 in the same scan
// whose UPDATE drops i_req.
//
// TCK -> async-core CDC contract:
//  * Control bits (rst / i_req / o_ack / i_data) are LEVELS that change
//    only on UPDATE (one TCK edge). The bundled-data ordering
//    (data valid before req rise) is guaranteed by the GENERATOR, which
//    applies i_data with i_req=0 in one scan and raises i_req with the
//    same data in a later scan -- so no hardware bundling delay is
//    needed on the JTAG side. Do not merge those two scans.
//  * Status bits (i_ack, o_req) are asynchronous levels; they pass
//    through 2-stage TCK-domain synchronizers before the capture mux.
//  * o_data is captured RAW: by the bundled-data invariant it is stable
//    the whole time o_req=1, and the generator only trusts the o_data
//    field of a capture whose own o_req bit reads 1 (o_data settled
//    long before o_req even rose, let alone cleared the synchronizer).
//
// 4-PHASE PULSE ADAPTER (a deliberate deviation from the plain
// hold-register-drives-the-core design, forced by simulation): the
// compiled core requires PROMPT return-to-zero of i_req after i_ack.
// Holding i_req high merely 1 us past i_ack -- until the first
// while-ring iteration loops back to the loop-entry bdmux -- wedges the
// core PERMANENTLY (reproduced on the bare netlist in
// tests/tb_jtag_bridge debugging, 2026-07: hold of 100 ns completes,
// hold of 1/5/20/60/100 us all deadlock, tightened AND untightened
// builds alike). Mechanism: the held entry request keeps the entry
// latch's controller from returning to zero, so the loop-entry mux's
// entry-side request is still up when the loopback token arrives --
// mutual exclusion (core invariant #3) is violated and the select
// wedges. A JTAG environment cannot drop a level within a microsecond
// (scans are milliseconds apart), so the wrapper does the RTZ locally:
//  * i_req to the core is a FF SET from the hold word on UPDATE and
//    CLEARED asynchronously by i_ack's rise (auto-RTZ in ~ns, glitch-
//    free: it is a flop output, not a decoded level).
//  * The captured "i_ack" status bit is therefore the STICKY
//    "request accepted" flag (hold_ireq & ~req_core): it stays 1 until
//    the host drops its i_req bit, which is exactly the 4-phase view
//    the host expects; the raw core i_ack pulse would be too short to
//    observe over JTAG.
//  * o_ack to the core is hold_oack & o_req ("mirror o_req, don't
//    latch it high" -- the ack falls with the req it acknowledges, one
//    LUT after o_req's own fall, completing that RTZ promptly too).
// NOTE this same prompt-RTZ requirement indicts the knapsack_ps_top
// AXI plan (openocd pokes are also ms apart) -- see the bring-up docs.
//
// Power-up / configuration state: rst=1, i_req=0, o_ack=0 (FF INIT
// values, applied by GSR at the end of configuration), so the core sits
// safely in reset until the host explicitly clears rst. Test-Logic-Reset
// (BSCANE2's RESET output) asynchronously restores the same state, so
// every SVF that starts with STATE RESET begins from a known core-reset
// condition and an aborted run can be recovered by re-running the SVF.
//
// BSCANE2 gotchas honored here (bench notes, 2026-07-20):
//  * DRCK does NOT pulse in the Update-DR state -- nothing here is
//    clocked on DRCK. TCK goes through a BUFG and clocks everything;
//    qualification is (SEL & CAPTURE / SHIFT / UPDATE).
//  * TDO presents the shift register LSB; BSCANE2 internally retimes
//    TDO onto falling TCK, matching the tester's rising-edge sample.
//
// LEDs (W14 red / W13 green, zynq/ebaz4205.xdc): board polarity is
// suspected ACTIVE-LOW on this revision (ledtest bench note: red read
// dark while driven 1), so "lit" below likely means the wire is LOW.
//   led_red   = o_req  (result waiting / handshake stuck at output)
//   led_green = i_ack  (input accepted / handshake stuck at input)
// Both idle-low, so between calls both wires are 0.
module knapsack_jtag_top (
  output led_red,
  output led_green
);

  // ---- BSCANE2 (USER1) --------------------------------------------
  wire bs_capture, bs_shift, bs_update, bs_sel, bs_reset;
  wire bs_tck_raw, bs_tdi;
  wire sr_tdo;

  (* keep *) BSCANE2 #(.JTAG_CHAIN(1)) bscan_i (
    .CAPTURE (bs_capture),
    .DRCK    (),            // unused on purpose: no pulse in UPDATE
    .RESET   (bs_reset),
    .RUNTEST (),
    .SEL     (bs_sel),
    .SHIFT   (bs_shift),
    .TCK     (bs_tck_raw),
    .TDI     (bs_tdi),
    .TMS     (),
    .UPDATE  (bs_update),
    .TDO     (sr_tdo)
  );

  wire tck;
  BUFG bufg_tck (.I(bs_tck_raw), .O(tck));

  // ---- core-facing nets -------------------------------------------
  wire        i_ack_core, o_req_core;
  wire [15:0] o_data_core;

  // ---- hold register (committed on UPDATE) ------------------------
  // bit 10 = rst, 9 = o_ack, 8 = i_req, 7:0 = i_data.
  // INIT = rst asserted, handshakes idle; TLR restores the same.
  localparam [10:0] HOLD_INIT = 11'b100_0000_0000;
  reg [10:0] hold = HOLD_INIT;

  wire        hold_rst  = hold[10];
  wire        hold_oack = hold[9];
  wire        hold_ireq = hold[8];
  wire [7:0]  hold_data = hold[7:0];

  // ---- 4-phase pulse adapter (see header) --------------------------
  // req_core: set from the scanned word on UPDATE, cleared by the
  // core's own i_ack rise -- the prompt RTZ the core requires. Also
  // cleared in Test-Logic-Reset so an aborted run can't leave a
  // request pending. A clean flop output: no decode glitches reach
  // the core's request input.
  wire req_clr = i_ack_core | bs_reset;
  reg  req_core = 1'b0;
  always @(posedge tck or posedge req_clr) begin
    if (req_clr)                   req_core <= 1'b0;
    else if (bs_sel && bs_update)  req_core <= sr[8];
  end

  // Sticky "accepted" status: 1 from the moment the core acknowledged
  // (req_core cleared while the host still asserts its i_req bit)
  // until the host drops that bit. Both terms are flop outputs.
  wire i_ack_sticky = hold_ireq & ~req_core;

  // o_ack mirrors o_req: high only while the host has committed o_ack
  // AND the core still presents o_req, so it falls with o_req (~1 LUT
  // later) instead of being held high for milliseconds. hold_oack only
  // changes on UPDATE while o_req is stable, so this AND cannot glitch.
  wire o_ack_core = hold_oack & o_req_core;

  // ---- shift register + capture mux -------------------------------
  localparam [2:0] CAP_TAG = 3'b101;

  reg [1:0] sync_i_ack = 2'b00;
  reg [1:0] sync_o_req = 2'b00;

  wire [31:0] cap_word = {o_data_core,           // [31:16]
                          CAP_TAG,               // [15:13]
                          sync_o_req[1],         // [12]
                          sync_i_ack[1],         // [11]
                          hold};                 // [10:0] echo

  reg [31:0] sr = 32'h0;

  always @(posedge tck) begin
    sync_i_ack <= {sync_i_ack[0], i_ack_sticky};
    sync_o_req <= {sync_o_req[0], o_req_core};
    if (bs_sel && bs_capture)     sr <= cap_word;
    else if (bs_sel && bs_shift)  sr <= {bs_tdi, sr[31:1]};
  end

  always @(posedge tck or posedge bs_reset) begin
    if (bs_reset)                  hold <= HOLD_INIT;
    else if (bs_sel && bs_update)  hold <= sr[10:0];
  end

  assign sr_tdo = sr[0];

  // ---- the async core (delay-tightened netlist, do not regenerate) --
  knapsack knapsack_i (
    .i_req  (req_core),
    .i_ack  (i_ack_core),
    .i_data (hold_data),
    .o_req  (o_req_core),
    .o_ack  (o_ack_core),
    .o_data (o_data_core),
    .rst    (hold_rst)
  );

  assign led_red   = o_req_core;   // suspected active-low on the board
  assign led_green = i_ack_core;   // (lit-when-0); diagnostic only

endmodule
