// knapsack_ps_top -- PS7-driven harness for the knapsack async-hls core on
// the EBAZ4205 (xc7z010clg400-1). Structurally identical to
// zynq/gcd_ps_top.v (see its header for the full story: why AXI instead
// of package pins, how the .bit gets loaded, the PS7/FCLK assumptions,
// and the clock-domain crossing scheme) -- only the core and its data
// widths differ. knapsack is the first `mem` (BRAM-backed) core to go to
// hardware: beyond the handshake protocol, this build exists to validate
// the self-timed RAM strobe and the tagged merge/latch/steer shared port
// on real silicon, neither of which any silicon has ever exercised.
//
// Register map (32-bit, byte addresses, M_AXI_GP0 base + offset):
//   0x00 CTRL   [0]=i_req [1]=o_ack [2]=rst   (write; level-driven --
//               hold levels through the full 4-phase, never pulse)
//   0x04 STATUS [0]=i_ack [1]=o_req            (read-only)
//   0x08 I_DATA i_data[7:0] = cap              (read/write; readback is
//               the AXI-plumbing liveness echo used by xsct_knapsack.tcl)
//   0x0C O_DATA o_data[15:0] = best value      (read-only)
//
// 4-PHASE PULSE ADAPTER (2026-07-21, ported from zynq/knapsack_jtag_top.v
// after the JTAG harness validated it on silicon -- read that header for
// the full mechanism): the compiled core wedges PERMANENTLY if i_req is
// held high even ~1 us past i_ack's rise (until the first while-ring
// iteration loops back to the loop-entry bdmux; BRINGUP_SESSION.md item
// 11, reproduced at 1/5/20/60/100 us holds). Any AXI host -- openocd or
// xsct pokes are milliseconds apart -- is exactly such an environment, so
// CTRL.i_req as a plain level register (the original design of this file)
// could never have worked on hardware. The adapter does the RTZ locally:
//   * the core-facing i_req is a FF SET on a CTRL write with bit0=1 and
//     CLEARED asynchronously by the core's i_ack rise;
//   * STATUS bit0 reports the STICKY "request accepted" view
//     (ctrl_i_req & ~req_core): 1 from acceptance until the host clears
//     CTRL.i_req -- exactly the 4-phase level the host protocol expects;
//   * the core-facing o_ack is ctrl_o_ack & o_req ("mirror o_req, don't
//     latch it high"), so the output RTZ also completes in ~ns.
// THE HOST-SIDE PROTOCOL IS UNCHANGED: write I_DATA; CTRL.i_req=1; poll
// STATUS.i_ack==1; CTRL.i_req=0; poll STATUS.o_req==1; read O_DATA;
// CTRL.o_ack=1; poll STATUS.o_req==0; CTRL.o_ack=0. Poke pacing is
// irrelevant again, as BRINGUP.md always claimed -- the adapter is what
// makes that claim true.
//
// The AXI slave FSM + registers + adapter + core live in
// knapsack_ps_bridge below so tests/tb_ps_bridge.v can drive the raw AXI
// channels directly (PS7 is a hard macro -- unsimulatable); this top just
// wraps the bridge with PS7 + BUFG. `PS_BRIDGE_NO_ADAPTER` re-creates the
// original level-register wiring for the wedge-reproduction TB run ONLY;
// never build hardware with it.
module knapsack_ps_top (
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

  // Port split by PS7's actual direction -- see gcd_ps_top.v's note on
  // checking against yosys's techlibs/xilinx/cells_xtra.v.
  //
  // AWID/ARID -> BID/RID are NOT optional decoration: M_AXI_GP0 is a
  // full AXI3 port and the PS interconnect routes responses by ID. A
  // slave that answers with constant BID/RID=0 (this file's original
  // sin) never completes the CPU's read -- on the bench (2026-07-21,
  // xsdb) every injected LDR to 0x40000000 died with "Timeout waiting
  // for the Instruction Complete bit" and wedged the DAP, while OCM and
  // SLCR reads (real ID-reflecting slaves) worked fine. The bridge
  // captures each transaction's ID and echoes it (BRINGUP_SESSION.md
  // item 17).
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

  knapsack_ps_bridge bridge_i (
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
// the PS7/BUFG hard macros, so a testbench can drive the raw AXI channel
// wires (see the top header). Same slave FSM as gcd_ps_top.v.
// BID/RID echo AWID/ARID -- mandatory on a raw AXI3 GP port, see the
// note at the PS7 instantiation above.
module knapsack_ps_bridge (
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

  reg        ctrl_i_req, ctrl_o_ack, ctrl_rst;
  reg [7:0]  i_data_reg;

  reg [1:0] sync_i_ack, sync_o_req;
  reg [15:0] o_data_capture;

  wire i_ack_s = sync_i_ack[1];
  wire o_req_s = sync_o_req[1];

  wire i_req_pl, o_ack_pl, rst_pl;
  wire i_ack_pl, o_req_pl;
  wire [15:0] o_data_pl;

  assign rst_pl = ctrl_rst;

`ifdef PS_BRIDGE_NO_ADAPTER
  // Historical pre-adapter wiring, kept ONLY so tests/tb_ps_bridge.v can
  // demonstrate the wedge (BRINGUP_SESSION.md item 11). Never build
  // hardware with this define.
  assign i_req_pl = ctrl_i_req;
  assign o_ack_pl = ctrl_o_ack;
  wire i_ack_host = i_ack_pl;
`else
  // ---- 4-phase pulse adapter (see top header; ported from the
  // silicon-validated zynq/knapsack_jtag_top.v) ----------------------
  // req_core: set from CTRL bit0 on the host's write, cleared by the
  // core's own i_ack rise -- the prompt RTZ the core requires. A clean
  // flop output: no decode glitches reach the core's request input.
  wire req_clr = i_ack_pl | ~aresetn;
  reg  req_core = 1'b0;
  always @(posedge aclk or posedge req_clr) begin
    if (req_clr)                             req_core <= 1'b0;
    else if (do_write && axi_awaddr == 4'h0) req_core <= wdata[0];
  end
  assign i_req_pl = req_core;

  // Sticky "accepted" status: 1 from the moment the core acknowledged
  // (req_core cleared while the host still asserts CTRL.i_req) until
  // the host clears that bit -- the 4-phase level the host expects; the
  // raw core i_ack pulse is nanoseconds, unobservable over AXI polls.
  wire i_ack_host = ctrl_i_req & ~req_core;

  // o_ack mirrors o_req: falls with the req it acknowledges instead of
  // being held high for milliseconds. ctrl_o_ack only changes on a CTRL
  // write while o_req is stable, so this AND cannot glitch.
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
      ctrl_i_req <= 1'b0;
      ctrl_o_ack <= 1'b0;
      ctrl_rst   <= 1'b1;      // hold PL core in reset until software clears it
      sync_i_ack <= 2'b0;
      sync_o_req <= 2'b0;
      o_data_capture <= 16'b0;
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
          4'h2: i_data_reg <= wdata[7:0];
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
      4'h2: rdata_r = {24'b0, i_data_reg};  // I_DATA is RW per the map;
                                            // readback is the liveness echo
      4'h3: rdata_r = {16'b0, o_data_capture};
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

  knapsack knapsack_i (
    .i_req  (i_req_pl),
    .i_ack  (i_ack_pl),
    .i_data (i_data_reg),
    .o_req  (o_req_pl),
    .o_ack  (o_ack_pl),
    .o_data (o_data_pl),
    .rst    (rst_pl)
  );

  assign core_i_ack = i_ack_pl;
  assign core_o_req = o_req_pl;

endmodule
