// ipow_ps -- PS7-driven harness for the COMPILED ipow kernel, derived from
// hw/gcd_ps.v by changing only the kernel instance: ipow presents the same
// channel arity (two operand channels, a start, one result, a p_end), so the
// register map, the pulse adapter, the bd_fork env and the driver script are
// all unchanged.  A_DATA is the base, B_DATA the exponent, O_DATA the result.
//
// WHY THIS ONE.  ipow is the only kernel here containing a variable x
// variable multiply, so it is the first design in this project whose datapath
// includes DSP48E1 hard blocks -- and until this runs, no DSP has ever been
// exercised on this board.  cells/flow.sh and hw/build_hw.sh infer them by
// default (BD_DSP=0 opts out), which was only safe once verify/tighten.py
// could size a matched delay across one.
//
// Everything below is gcd_ps.v's, and the two must not drift.  Its header
// argues the PS7 wiring, the BID/RID echo, the active-HIGH reset, the pulse
// adapter and p_end's sink; none of that is repeated here.
//
// EBAZ4205 (xc7z010clg400-1).  Ported from hw-docs/ref/zynq/fib_ps_top.v,
// which is the silicon-proven shape that ran knapsack/gcd on this exact
// board.  The PS's M_AXI_GP0 drives the kernel over a small AXI3 register
// slave, so the design costs two package pins (the LEDs) instead of the
// ~100 that a/b/out0 plus handshakes would want.
//
// WHY THIS EXISTS ALONGSIDE gcd_hw.v
//
// gcd_hw.v answers "is the kernel right" with SIXTEEN vectors chosen at
// synthesis time and baked into a case statement.  That is a fine gate and a
// poor test: every claim it makes is a claim about vectors I picked.  This
// harness moves the vector source off the die entirely, so the operands can
// come from the host -- millions of them, random and adversarial, with the
// reference computed by software rather than by me.  gcd_hw.v stays; it is
// the self-contained one that needs no host at all.
//
// Register map (32-bit, byte addresses, M_AXI_GP0 base 0x40000000 + offset).
// 0x00/0x04 are byte-compatible with the convention in hw-docs 02 section 5,
// so the same xsdb driver pattern applies; gcd needs TWO operands, so the
// single I_DATA at 0x08 becomes A_DATA/B_DATA and the result moves to 0x10.
//
//   0x00 CTRL   [0]=i_req [1]=o_ack [2]=rst   (RW; rst powers up 1)
//   0x04 STATUS [0]=i_ack (sticky) [1]=o_req  (RO)
//   0x08 A_DATA gcd's a : i32                 (RW; readback is a liveness echo)
//   0x0C B_DATA gcd's b : i32                 (RW; same)
//   0x10 O_DATA gcd's return : i32            (RO)
//
// Host 4-phase sequence, unchanged from the convention:
//   write A_DATA, write B_DATA -> CTRL.i_req=1 -> poll STATUS.i_ack==1
//   -> CTRL.i_req=0 -> poll STATUS.o_req==1 -> read O_DATA -> CTRL.o_ack=1
//   -> poll STATUS.o_req==0 -> CTRL.o_ack=0.
//
// RESET POLARITY -- THE ONE PLACE THIS DIVERGES FROM fib_ps_top.v.
// That file inverts (rst_pl = ~ctrl_rst) because asyncfpga2's core is
// active-LOW.  bdc's kernels are active-HIGH: gcd_rig.v drives the same port
// with `rig_rst = ~por_done | rst_sr[15]`, which asserts HIGH.  So the
// inversion is DROPPED here and rst_pl = ctrl_rst directly.  ctrl_rst still
// powers up 1, which now means "asserted" for the same reason it meant
// "asserted" there -- the kernel is held in reset until software clears it.
// Copying fib's `~` would have released the kernel at power-up and held it
// in reset whenever software tried to run it, which is the kind of bug that
// looks like a dead design rather than an inverted signal.
//
// PS7 BRING-UP IS NOT DONE HERE AND IS NOT DONE BY AN FSBL.  fib_ps_top.v's
// header says the board's FSBL already configured MIO/clocks/DDR; hw-docs/
// 02 section 4 says otherwise for this board, and the doc is what this
// session is driving against: the PL is inert after configuration -- level
// shifters off, PL resets held -- until the SLCR sequence is poked in over
// xsdb, and that sequence must be re-run after every `fpga -f` and every
// `rst -system`.  This design consumes FCLKCLK[0] through an explicit BUFG
// and assumes nothing else.
//
// The BUFG is instantiated rather than inferred on purpose: hw-docs/07
// records that yosys' clkbufmap inserts one unasked, and that a matched
// delay timed from the PRE-buffer signal can be beaten by the ~2 ns the
// buffer adds.  Naming it keeps the capture clock and any timing tap on the
// same side of the same buffer.
module ipow_ps (
  // The board's two dedicated PL LEDs -- a liveness indicator that does not
  // depend on the AXI link being healthy.  Everything else rides GP0.
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

  // AW*/AR*/W* sideband (PROT/LEN/SIZE/BURST/LOCK/CACHE/QOS/LAST) are PS7
  // OUTPUTS and are left unconnected: this single-beat register slave has no
  // burst semantics to honour.  BID/RID MUST echo AWID/ARID -- the PS
  // interconnect routes responses by 12-bit ID, and tying them to 0 hangs
  // every CPU access and wedges the DAP, while a testbench that drives ID 0
  // stays green throughout (hw-docs/07, Hardware).
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

  ipow_ps_bridge bridge_i (
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

// AXI3 register slave + 4-phase pulse adapter + the compiled kernel:
// everything except the PS7/BUFG hard macros, which are unsimulatable, so
// this module is what a testbench drives with raw AXI channel wiggles.
//
// Standard single-beat AXI4-Lite slave pattern: AWREADY/WREADY assert only
// once BOTH awvalid and wvalid have been seen, so a write completes in one
// cycle whichever order the master issues AW and W in.
module ipow_ps_bridge (
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

  // raw kernel handshake taps -- the LEDs, and convenience in sim
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

  // ---- register file.  CTRL/A_DATA/B_DATA are AXI-clock registers;
  // STATUS and O_DATA are synchronized samples of the clockless kernel.
  reg        ctrl_i_req, ctrl_o_ack, ctrl_rst;
  reg [31:0] a_data_reg, b_data_reg;

  reg [1:0]  sync_i_ack, sync_o_req;
  reg [31:0] o_data_capture;

  wire i_ack_s = sync_i_ack[1];
  wire o_req_s = sync_o_req[1];

  wire        i_req_pl, o_ack_pl, rst_pl;
  wire        i_ack_pl, o_req_pl;
  wire [31:0] o_data_pl;

  // See the file header: bdc kernels reset ACTIVE-HIGH, so unlike
  // fib_ps_top.v there is no inversion here.
  assign rst_pl = ctrl_rst;

  // ---- 4-phase pulse adapter ---------------------------------------------
  // Not decorative.  hw-docs/07 records it as a hardware gotcha that
  // simulation cannot see: a host that holds i_req high past i_ack's rise --
  // and any host poking over JTAG/AXI does, by milliseconds -- freezes the
  // entry chain and deadlocks the kernel after one traversal, while a
  // generated testbench returns to zero correctly and stays green.  gcd is a
  // while-ring kernel, so it is exactly the shape that wedges.
  //
  // The kernel-facing i_req is a flop set by the CTRL write and cleared
  // ASYNCHRONOUSLY by the kernel's own i_ack, so the request drops on the
  // kernel's timescale rather than the host's.  STATUS.i_ack reports the
  // sticky "request was accepted" view instead, which is what a host polling
  // at ms cadence can actually observe.
  wire req_clr = i_ack_pl | ~aresetn;
  reg  req_core = 1'b0;
  always @(posedge aclk or posedge req_clr) begin
    if (req_clr)                              req_core <= 1'b0;
    else if (do_write && axi_awaddr == 4'h0)  req_core <= wdata[0];
  end
  assign i_req_pl = req_core;

  wire i_ack_host = ctrl_i_req & ~req_core;

  // o_ack mirrors o_req, so it falls with the request it acknowledges.
  // Latching it high is the same gotcha from the other end.
  assign o_ack_pl = ctrl_o_ack & o_req_pl;

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
      ctrl_rst    <= 1'b1;      // hold the kernel in reset until software clears it
      sync_i_ack  <= 2'b0;
      sync_o_req  <= 2'b0;
      o_data_capture <= 32'b0;
    end else begin
      // Bring the clockless status into this clock domain.  o_data is
      // captured unconditionally every cycle rather than on an edge of
      // o_req: rtl/bd_link.v's request LEADS its own data by about one latch
      // arc, so anything sampling on the request edge samples early.  A free
      // capture cannot be early, because the host only reads O_DATA after
      // o_req has survived two synchronizer stages, by which point the
      // captured word is several cycles old and the kernel is still holding
      // it.
      sync_i_ack <= {sync_i_ack[0], i_ack_host};
      sync_o_req <= {sync_o_req[0], o_req_pl};
      o_data_capture <= o_data_pl;

      // write address/data channel handshake
      if (~axi_awready && awvalid && wvalid && aw_en) begin
        axi_awready <= 1'b1;
        axi_wready  <= 1'b1;
        axi_awaddr  <= awaddr[5:2];
        axi_bid     <= awid;        // the response must carry the request's ID
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
          4'h2: a_data_reg <= wdata;
          4'h3: b_data_reg <= wdata;
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
        axi_rid     <= arid;        // the response must carry the request's ID
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
      4'h2: rdata_r = a_data_reg;          // RW per the map: readback echoes
      4'h3: rdata_r = b_data_reg;
      4'h4: rdata_r = o_data_capture;
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

  // ---- the compiled kernel and its environment ---------------------------
  // bdc_gcd presents three input channels (a, b, start) and two output
  // channels (out0, p_end), each four-phase bundled-data.  The single host
  // request has to become three, and the three acknowledges have to become
  // one: that is exactly bd_fork, which broadcasts the request and joins the
  // acknowledges through a C-element tree.  gcd_rig.v drives the same kernel
  // the same way.
  wire        a_ack, b_ack, start_ack;
  wire [2:0]  in_req;
  wire        p_end_req, p_end_ack;

  bd_fork #(.N(3)) ufork (
      .rst(rst_pl), .req(i_req_pl), .ack(i_ack_pl),
      .req_out(in_req), .ack_in({start_ack, b_ack, a_ack}));

  // p_end is NOT a completion signal, however much it reads like one.  In the
  // emitted kernel the function's control argument forks straight to the
  // function's control result, so p_end_req IS start_req combinationally,
  // with no storage between them.  Joining it into the result would close a
  // cycle containing zero storage stages -- the env's own version of the
  // mistake bdc/emit.py's ring_depths() exists to prevent.  It gets its own
  // sink instead.  gcd_rig.v argues this at length and reaches the same
  // wiring.
  bd_delay #(.N(2)) upsnk (.a(p_end_req), .z(p_end_ack));

  // A_DATA carries ipow's BASE and B_DATA its EXPONENT: the register map is
  // positional, and ipow's channels happen to be named b and e.  Keeping the
  // map identical to gcd_ps.v is what lets the same driver and the same host
  // sequence work unchanged.
  bdc_ipow udut (
      .rst       (rst_pl),
      .b_req     (in_req[0]), .b_ack     (a_ack),     .b_data (a_data_reg),
      .e_req     (in_req[1]), .e_ack     (b_ack),     .e_data (b_data_reg),
      .start_req (in_req[2]), .start_ack (start_ack),
      .out0_req  (o_req_pl),  .out0_ack  (o_ack_pl),  .out0_data (o_data_pl),
      .p_end_req (p_end_req), .p_end_ack (p_end_ack));

  assign core_i_ack = i_ack_pl;
  assign core_o_req = o_req_pl;

endmodule
