// fib_ps_top -- PS7-driven harness for asyncfpga2's `fib` core on the
// EBAZ4205 (xc7z010clg400-1). Ported from async-hls-v2's zynq/gcd_ps_top.v
// (the same silicon-proven shape that ran knapsack/gcd on this exact
// board): PS's M_AXI_GP0 drives the core over a small AXI3 register
// slave instead of budgeting ~40 physical PL pins for fib's r_i/a_i/
// d_i[7:0]/r_o/a_o/d_o[31:0]/rst.
//
// PS7 configuration (MIO/clock/DDR) is NOT set by this bitstream -- the
// board's existing FSBL already did it before the PL is configured; this
// design only needs at least one FCLK enabled by that FSBL, consumed as
// FCLKCLK[0] via a BUFG, exactly as any Vivado-generated PS7 block design
// would (no Vivado in this toolchain).
//
// Register map (32-bit, byte addresses, AXI3 M_AXI_GP0 base + offset) --
// IDENTICAL layout to v2's harnesses (BRINGUP.md convention), so the same
// xsdb driver pattern (docs/hardware-bringup-notes.md 2a) applies verbatim
// except for the golden table:
//   0x00 CTRL   [0]=i_req [1]=o_ack [2]=rst   (write; level-driven, not a
//               strobe -- 4-phase protocol needs held levels)
//   0x04 STATUS [0]=i_ack [1]=o_req            (read-only)
//   0x08 I_DATA d_i[7:0]  (fib's n : u8)        (read/write, low byte only)
//   0x0C O_DATA d_o[31:0] (fib's return : u32)  (read-only, full word)
//
// RESET POLARITY -- the one non-mechanical change from v2's wrapper.
// asyncfpga2's `rst` is ACTIVE-LOW (project convention D3: rst=0 asserts,
// rst=1 runs), whereas v2's core (and this file's CTRL.rst bit, which
// "powers up 1" to hold the core in reset until software clears it) is
// active-HIGH internally. The core-facing reset is therefore inverted
// here (rst_pl = ~ctrl_rst) so ctrl_rst=1 at power-up drives fib's rst=0
// (asserted, correct) and software clearing ctrl_rst=0 drives rst=1
// (running, correct). Nothing else inverts: aresetn and the AXI-domain
// `negedge aresetn` register-reset block stay exactly as v2 has them --
// those are the PS7/AXI-clock-domain reset, unrelated to D3's core
// convention, and must not be "consistency fixed".
//
// 4-PHASE PULSE ADAPTER (ported verbatim from v2's knapsack/gcd
// bridges -- see their headers for the silicon-validated mechanism): a
// host that holds i_req high past i_ack for ~1 us wedges a while-ring
// core permanently, and fib IS a while-ring core (the iterative loop),
// so a ms-cadence AXI host would hit the same bug without this. The
// core-facing i_req is a FF set on the CTRL write and cleared
// asynchronously by i_ack's rise; STATUS.i_ack reports the sticky
// "request accepted" view; the core-facing o_ack is ctrl_o_ack & o_req.
// THE HOST-SIDE PROTOCOL IS UNCHANGED from the register-map table above.
//
// The AXI slave FSM + registers + adapter + core live in fib_ps_bridge
// (PS7 is an unsimulatable hard macro; the bridge is driven directly by
// a TB via raw AXI channel wiggles -- see
// tests/rtl/tb_fib_ps_bridge.sv, ported from v2's tb_ps_bridge.v).
module fib_ps_top (
  // physical: the board's two dedicated PL LEDs, driven from fib's
  // status for a cheap "is it alive" indicator independent of the AXI
  // link -- everything else goes over M_AXI_GP0, no other package pins
  // used.
  output led_red,
  output led_green
);

  wire [3:0]  fclkclk;
  wire        fclk0_bufg;
  wire        aresetn;

  wire        m_axi_gp0_aclk = fclk0_bufg;

  wire        awvalid, awready;
  wire [31:0] awaddr;
  wire [11:0] awid;
  wire        wvalid, wready;
  wire [31:0] wdata;
  wire [3:0]  wstrb;
  wire        bvalid, bready;
  wire [1:0]  bresp;
  wire [11:0] bid;
  wire        arvalid, arready;
  wire [31:0] araddr;
  wire [11:0] arid;
  wire        rvalid, rready;
  wire [31:0] rdata;
  wire [1:0]  rresp;
  wire [11:0] rid;

  // AW*/AR*/W* sideband fields (PROT/LEN/SIZE/BURST/LOCK/CACHE/QOS/LAST)
  // are PS7 OUTPUTS -- left unconnected, this single-beat register slave
  // ignores burst semantics entirely. BID/RID MUST echo AWID/ARID: the PS
  // interconnect routes responses by ID, and a constant-0 BID/RID hangs
  // every CPU access on real silicon (v2 bench finding, BRINGUP_SESSION.md
  // item 17). RLAST=1 is fine: injected/single-beat reads only.
  PS7 ps7_i (
    .MAXIGP0ACLK    (m_axi_gp0_aclk),
    .MAXIGP0ARESETN (aresetn),

    .MAXIGP0AWVALID (awvalid), .MAXIGP0AWREADY (awready),
    .MAXIGP0AWADDR  (awaddr),  .MAXIGP0AWID    (awid),

    .MAXIGP0WVALID  (wvalid),  .MAXIGP0WREADY  (wready),
    .MAXIGP0WDATA   (wdata),   .MAXIGP0WSTRB   (wstrb),

    .MAXIGP0BVALID  (bvalid),  .MAXIGP0BREADY  (bready),
    .MAXIGP0BRESP   (bresp),   .MAXIGP0BID     (bid),

    .MAXIGP0ARVALID (arvalid), .MAXIGP0ARREADY (arready),
    .MAXIGP0ARADDR  (araddr),  .MAXIGP0ARID    (arid),

    .MAXIGP0RVALID  (rvalid),  .MAXIGP0RREADY  (rready),
    .MAXIGP0RDATA   (rdata),   .MAXIGP0RRESP   (rresp),
    .MAXIGP0RLAST   (1'b1),    .MAXIGP0RID     (rid),

    .FCLKCLK        (fclkclk),
    .FCLKRESETN     (),
    .FCLKCLKTRIGN   (4'b0)
  );

  BUFG bufg_fclk0 (.I(fclkclk[0]), .O(fclk0_bufg));

  wire core_i_ack, core_o_req;

  fib_ps_bridge bridge_i (
    .aclk    (m_axi_gp0_aclk),
    .aresetn (aresetn),

    .awvalid (awvalid), .awready (awready), .awaddr (awaddr),
    .awid    (awid),
    .wvalid  (wvalid),  .wready  (wready),  .wdata  (wdata),
    .wstrb   (wstrb),
    .bvalid  (bvalid),  .bready  (bready),  .bresp  (bresp),
    .bid     (bid),
    .arvalid (arvalid), .arready (arready), .araddr (araddr),
    .arid    (arid),
    .rvalid  (rvalid),  .rready  (rready),  .rdata  (rdata),
    .rresp   (rresp),   .rid     (rid),

    .core_i_ack (core_i_ack),
    .core_o_req (core_o_req)
  );

  assign led_red   = core_i_ack;
  assign led_green = core_o_req;

endmodule

// AXI3 register slave + 4-phase pulse adapter + core: everything except
// the PS7/BUFG hard macros (same factoring as v2's knapsack/gcd bridges).
//
// Standard single-beat AXI4-Lite slave pattern (Xilinx's own AXI4-Lite
// peripheral template): AWREADY/WREADY only assert once BOTH awvalid and
// wvalid are seen, so the write completes in one cycle regardless of
// whether the master issues AW/W together or in either order -- all legal
// AXI3 orderings.
module fib_ps_bridge (
  input         aclk,
  input         aresetn,

  input         awvalid,
  output        awready,
  input  [31:0] awaddr,
  input  [11:0] awid,
  input         wvalid,
  output        wready,
  input  [31:0] wdata,
  input  [3:0]  wstrb,
  output        bvalid,
  input         bready,
  output [1:0]  bresp,
  output [11:0] bid,
  input         arvalid,
  output        arready,
  input  [31:0] araddr,
  input  [11:0] arid,
  output        rvalid,
  input         rready,
  output [31:0] rdata,
  output [1:0]  rresp,
  output [11:0] rid,

  // raw core handshake taps (LEDs on the board; convenience in sim)
  output        core_i_ack,
  output        core_o_req
);

  reg        axi_awready, axi_wready, axi_bvalid;
  reg        axi_arready, axi_rvalid;
  reg [3:0]  axi_awaddr, axi_araddr;
  reg [11:0] axi_bid, axi_rid;
  reg        aw_en;

  assign awready = axi_awready;
  assign wready  = axi_wready;
  assign bvalid  = axi_bvalid;
  assign bresp   = 2'b00;
  assign bid     = axi_bid;
  assign arready = axi_arready;
  assign rvalid  = axi_rvalid;
  assign rresp   = 2'b00;
  assign rid     = axi_rid;

  wire do_write = axi_awready && awvalid && axi_wready && wvalid;

  // ---- register file: CTRL/I_DATA are AXI-clock registers; STATUS/
  // O_DATA are synchronized samples of the async-domain signals.
  reg        ctrl_i_req, ctrl_o_ack, ctrl_rst;
  reg [31:0] i_data_reg;

  reg [1:0]  sync_i_ack, sync_o_req;
  reg [31:0] o_data_capture;

  wire i_ack_s = sync_i_ack[1];
  wire o_req_s = sync_o_req[1];

  wire        i_req_pl, o_ack_pl, rst_pl;
  wire        i_ack_pl, o_req_pl;
  wire [31:0] o_data_pl;

  // See file header: fib's rst is active-LOW (D3), ctrl_rst is
  // active-HIGH ("powers up 1" holds the core in reset) -- inverted here,
  // and ONLY here; aresetn/the AXI reset block below are untouched.
  assign rst_pl = ~ctrl_rst;

`ifdef PS_BRIDGE_NO_ADAPTER
  // Historical pre-adapter wiring, kept ONLY for wedge-reproduction sims
  // (tests/rtl/tb_fib_ps_bridge.sv -DPS_BRIDGE_NO_ADAPTER -DTB_EXPECT_WEDGE
  // proves the adapter below is load-bearing, not decorative -- holding
  // i_req at ms/us cadence past i_ack's rise permanently wedges a
  // while-ring core, and fib is one). Never build hardware with this
  // define.
  assign i_req_pl = ctrl_i_req;
  assign o_ack_pl = ctrl_o_ack;
  wire i_ack_host = i_ack_pl;
`else
  // ---- 4-phase pulse adapter (see file header; ported from the
  // silicon-validated zynq/knapsack_jtag_top.v via gcd_ps_top.v) --------
  wire req_clr = i_ack_pl | ~aresetn;
  reg  req_core = 1'b0;
  always @(posedge aclk or posedge req_clr) begin
    if (req_clr)                              req_core <= 1'b0;
    else if (do_write && axi_awaddr == 4'h0)  req_core <= wdata[0];
  end
  assign i_req_pl = req_core;

  // Sticky "accepted" status until the host clears CTRL.i_req.
  wire i_ack_host = ctrl_i_req & ~req_core;

  // o_ack mirrors o_req: falls with the req it acknowledges.
  assign o_ack_pl = ctrl_o_ack & o_req_pl;
`endif

  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      axi_awready <= 1'b0;
      axi_wready  <= 1'b0;
      axi_bvalid  <= 1'b0;
      axi_arready <= 1'b0;
      axi_rvalid  <= 1'b0;
      axi_bid     <= 12'b0;
      axi_rid     <= 12'b0;
      aw_en       <= 1'b1;
      ctrl_i_req  <= 1'b0;
      ctrl_o_ack  <= 1'b0;
      ctrl_rst    <= 1'b1;      // hold PL core in reset until software clears it
      sync_i_ack  <= 2'b0;
      sync_o_req  <= 2'b0;
      o_data_capture <= 32'b0;
    end else begin
      // synchronize clockless PL status into this clock domain
      sync_i_ack <= {sync_i_ack[0], i_ack_host};
      sync_o_req <= {sync_o_req[0], o_req_pl};
      o_data_capture <= o_data_pl;

      // write address/data channel handshake
      if (~axi_awready && awvalid && wvalid && aw_en) begin
        axi_awready <= 1'b1;
        axi_wready  <= 1'b1;
        axi_awaddr  <= awaddr[5:2];
        axi_bid     <= awid;        // response must carry the request's ID
        aw_en       <= 1'b0;
      end else begin
        axi_awready <= 1'b0;
        axi_wready  <= 1'b0;
        if (bvalid && bready) aw_en <= 1'b1;
      end

      if (do_write) begin
        case (axi_awaddr)
          4'h0: begin
            ctrl_i_req <= wdata[0];
            ctrl_o_ack <= wdata[1];
            ctrl_rst   <= wdata[2];
          end
          4'h2: i_data_reg <= wdata;
          default: ;
        endcase
      end

      // write response channel
      if (do_write && ~axi_bvalid) axi_bvalid <= 1'b1;
      else if (bready && axi_bvalid) axi_bvalid <= 1'b0;

      // read address channel
      if (~axi_arready && arvalid) begin
        axi_arready <= 1'b1;
        axi_araddr  <= araddr[5:2];
        axi_rid     <= arid;        // response must carry the request's ID
      end else begin
        axi_arready <= 1'b0;
      end

      // read data channel
      if (axi_arready && arvalid && ~axi_rvalid) axi_rvalid <= 1'b1;
      else if (axi_rvalid && rready) axi_rvalid <= 1'b0;
    end
  end

  reg [31:0] rdata_r;
  always @(*) begin
    case (axi_araddr)
      4'h0: rdata_r = {29'b0, ctrl_rst, ctrl_o_ack, ctrl_i_req};
      4'h1: rdata_r = {30'b0, o_req_s, i_ack_s};
      4'h2: rdata_r = i_data_reg;           // I_DATA is RW per the map
      4'h3: rdata_r = o_data_capture;
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

  fib fib_i (
    .r_i(i_req_pl), .a_i(i_ack_pl), .d_i(i_data_reg[7:0]),
    .r_o(o_req_pl), .a_o(o_ack_pl), .d_o(o_data_pl),
    .rst(rst_pl)
  );

  assign core_i_ack = i_ack_pl;
  assign core_o_req = o_req_pl;

endmodule
