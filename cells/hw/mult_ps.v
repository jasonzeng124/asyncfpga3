// mult_ps -- the minimal reproducer for the DSP48E1 disagreement.
//
// ipow_ps gives wrong ANSWERS on this board when BD_DSP=1 and correct ones
// when BD_DSP=0: same RTL, same harness, same 2016 vectors, same seed.
// Everything above the toolchain has been cleared.  The source simulates
// correctly, and so does the POST-SYNTHESIS netlist against the toolchain's
// own cells_sim.v -- 4007 of 4007 vectors, including the exact operands the
// board gets wrong.  Lengthening the matched delay 4x does not fix it; it
// moves which vectors fail.  So it is not a bundled-data timing failure
// either.
//
// This design removes what is left to argue about.  It keeps gcd_ps.v's PS7
// shell and register map verbatim -- so the same driver runs against it --
// and replaces the compiled kernel with a single expression:
//
//     assign o_data_pl = a_data_reg * b_data_reg;
//
// The host writes the operands and reads the product back milliseconds
// later.  There is no request, no matched delay and no ring.  A wrong
// product here cannot be a handshake bug, a delay-sizing bug or a compiler
// bug, because this design contains none of those things.
//
// ---------------------------------------------------------------------------
// Below this line everything is gcd_ps.v's; see that file for the PS7
// wiring, the BID/RID echo and the active-HIGH reset.
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
module mult_ps (
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

  mult_ps_bridge bridge_i (
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
module mult_ps_bridge (
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
  // (* keep *) stops synth_xilinx absorbing these into the DSP's own AREG /
  // BREG.  Without it the operand registers move INSIDE the multiplier and
  // the DSP samples the AXI write bus directly, which is a different
  // configuration (AREG=1) from the one kernels/ipow produces (AREG=0,
  // operands arriving from bundled-data latches).  Keeping them outside makes
  // this reproducer the same shape as the kernel it stands in for.
  (* keep = "true" *) reg [31:0] a_data_reg, b_data_reg;

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

  // ---- trivial 4-phase responder ----------------------------------------
  // gcd_ps.v needs an asynchronous pulse adapter because a host holding i_req
  // past i_ack wedges a while-ring kernel.  There is no ring here and no
  // kernel -- the "computation" is a wire -- so the handshake is just enough
  // state to keep the SAME host driver working unchanged: acknowledge the
  // request immediately, raise o_req once the request has returned to zero,
  // drop it on o_ack.  All of it in the AXI clock domain, all of it trivially
  // correct, so that nothing here can be blamed for a wrong answer except the
  // multiply itself.
  reg seen, resp;
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      seen <= 1'b0;
      resp <= 1'b0;
    end else if (ctrl_rst) begin
      seen <= 1'b0;
      resp <= 1'b0;
    end else begin
      if (ctrl_i_req)          seen <= 1'b1;
      if (seen && !ctrl_i_req) resp <= 1'b1;
      if (ctrl_o_ack) begin
        resp <= 1'b0;
        seen <= 1'b0;
      end
    end
  end

  assign i_req_pl   = ctrl_i_req;
  assign o_req_pl   = resp;
  wire   i_ack_host = ctrl_i_req;
  assign o_ack_pl   = ctrl_o_ack;

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

  // ---- the entire datapath ------------------------------------------------
  // One 32x32 multiply, truncated to 32 bits.  No handshake around it, no
  // matched delay, no compiled kernel -- and the host reads O_DATA
  // MILLISECONDS after writing the operands, so there is no arrival time this
  // could get wrong.  If the board disagrees with a*b here, the disagreement
  // is in how the toolchain built the multiply and in nothing else.
  //
  // Build it both ways to make the comparison: BD_DSP=1 infers DSP48E1,
  // BD_DSP=0 builds the same expression from LUTs and carry chains.
  assign o_data_pl = a_data_reg * b_data_reg;

  assign core_i_ack = i_ack_host;
  assign core_o_req = o_req_pl;

endmodule
