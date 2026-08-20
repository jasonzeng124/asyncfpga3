// gcd_bench -- throughput and latency benchmark for the COMPILED gcd kernel
// on the EBAZ4205, in the shape hw-docs/ref/zynq/knapsack_bench_top.v
// established: the same PS7 + BUFG + AXI3 slave shell as hw/gcd_ps.v, around
// a bridge that ALSO contains an FCLK0-domain FSM driving the kernel's
// four-phase handshake autonomously N_RUNS times and counting cycles.
//
// WHY A FABRIC FSM AND NOT THE HOST
//
// hw-docs/02 section 5 puts host xsdb pokes at about 10 ms per AXI
// transaction and one gcd call at microseconds.  A latency measured from the
// host would be 99.9% JTAG overhead and would tell you about the cable.  The
// host here only starts a batch and reads the totals; everything timed
// happens in fabric.
//
// WHY THE OPERANDS MOVE, WHICH IS THE WHOLE POINT
//
// knapsack's bench reruns one input.  Doing that for gcd would measure
// almost nothing: gcd's running time is a function of its OPERANDS -- Stein's
// algorithm halves and subtracts until it converges -- and a bundled-data
// kernel finishes when it finishes rather than on a clock edge.  A benchmark
// that holds the input still would report a single number and hide exactly
// the property this whole backend exists to exploit.
//
// So there are two batch modes, selected by BCTRL[2]:
//
//   FIXED (0)  every run uses A_DATA/B_DATA.  LAT_MIN and LAT_MAX should come
//              out nearly equal; the spread is the measurement's own noise
//              floor, and it is what makes the LFSR spread below meaningful
//              rather than just a number.
//   LFSR  (1)  operands are drawn from a 32-bit LFSR seeded from A_DATA.
//              LAT_MIN/LAT_MAX then bracket the data dependence itself.
//
// Reporting min and max rather than a mean is deliberate: for an async
// kernel the interesting quantity is the SPREAD, and a mean is exactly the
// statistic that destroys it.  CYCLES/completed gives the mean if it is
// wanted.
//
// THROUGHPUT, HONESTLY.  This harness holds ONE transaction in flight: there
// is a single operand register pair, and the FSM does not issue run k+1 until
// run k has returned to zero.  So the throughput it reports is 1/latency and
// not the kernel's pipelined peak.  For gcd that is very nearly the whole
// truth anyway -- it is a while-ring kernel whose loop carries state, so a
// second transaction cannot enter the loop until the first has left it -- but
// it would NOT be the whole truth for a feed-forward kernel, and this comment
// is here so nobody quotes this number as one.
//
// Register map (32-bit byte offsets from M_AXI_GP0 base 0x40000000).
// 0x00-0x10 are identical to hw/gcd_ps.v, so the functional driver's poke
// sequence keeps working; the bench registers extend past it.  Note this map
// diverges from knapsack's by one slot from 0x10 on, because gcd takes two
// operands where knapsack took one.
//
//   0x00 CTRL     RW [0]=i_req [1]=o_ack [2]=rst   (manual path)
//   0x04 STATUS   RO [0]=i_ack (sticky) [1]=o_req  (manual path)
//   0x08 A_DATA   RW gcd's a -- also the bench's a, and the LFSR seed
//   0x0C B_DATA   RW gcd's b -- also the bench's b in FIXED mode
//   0x10 O_DATA   RO last result, captured on every completion (manual AND
//                 bench), so a batch stays checkable after the fact
//   0x14 N_RUNS   RW transactions per batch
//   0x18 CYCLES   RO total FCLK0 cycles for the batch, saturating
//   0x1C BCTRL    RW [0]=start (level; batch begins on its rise)
//                    [1]=bench_rst (level; aborts, zeroes counters)
//                    [2]=mode (0=FIXED, 1=LFSR)
//   0x20 BSTATUS  RO [0]=busy [1]=done [31:16]=completed runs
//   0x24 LAT_MIN  RO smallest per-run latency in cycles (0xFFFFFFFF until one
//                 completes)
//   0x28 LAT_MAX  RO largest per-run latency in cycles
//   0x2C LAST_A   RO the a of the most recent run (LFSR mode: which operands
//                 produced the result sitting in O_DATA)
//   0x30 LAST_B   RO the b of the most recent run
//
// Host batch protocol: write A_DATA/B_DATA and N_RUNS, set BCTRL, poll
// BSTATUS.done, read CYCLES/LAT_MIN/LAT_MAX/O_DATA, clear BCTRL.  Do not
// touch CTRL[0]/[1] while busy: the FSM owns the kernel handshake then.
// CTRL.rst must be 0.
//
// Everything else -- PS7 port wiring, why BID/RID must echo, the active-HIGH
// reset, the pulse adapter, the bd_fork env and p_end's sink -- is argued in
// hw/gcd_ps.v and is not repeated here.  The two files must not drift.
module gcd_bench (
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

  gcd_bench_bridge bridge_i (
    .aclk    (m_axi_gp0_aclk), .aresetn (aresetn),
    .awvalid (awvalid), .awready (awready), .awaddr (awaddr), .awid (awid),
    .wvalid  (wvalid),  .wready  (wready),  .wdata  (wdata),  .wstrb (wstrb),
    .bvalid  (bvalid),  .bready  (bready),  .bresp  (bresp),  .bid   (bid),
    .arvalid (arvalid), .arready (arready), .araddr (araddr), .arid  (arid),
    .rvalid  (rvalid),  .rready  (rready),  .rdata  (rdata),
    .rresp   (rresp),   .rid     (rid),
    .core_i_ack (core_i_ack), .core_o_req (core_o_req)
  );

  assign led_red   = core_i_ack;
  assign led_green = core_o_req;

endmodule


module gcd_bench_bridge (
  input         aclk,
  input         aresetn,
  input         awvalid, output awready, input [31:0] awaddr, input [11:0] awid,
  input         wvalid,  output wready,  input [31:0] wdata,  input [3:0] wstrb,
  output        bvalid,  input  bready,  output [1:0] bresp,  output [11:0] bid,
  input         arvalid, output arready, input [31:0] araddr, input [11:0] arid,
  output        rvalid,  input  rready,  output [31:0] rdata,
  output [1:0]  rresp,   output [11:0] rid,
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
  reg [31:0] a_data_reg, b_data_reg;
  reg [31:0] n_runs, cycles, lat_min, lat_max;
  reg        bctrl_start, bctrl_rst, bctrl_mode;
  reg [31:0] last_a, last_b;

  reg [1:0]  sync_i_ack, sync_o_req;
  reg [31:0] o_data_capture;

  wire i_ack_s = sync_i_ack[1];
  wire o_req_s = sync_o_req[1];

  wire        i_req_pl, o_ack_pl, rst_pl;
  wire        i_ack_pl, o_req_pl;
  wire [31:0] o_data_pl;

  assign rst_pl = ctrl_rst;   // bdc kernels reset ACTIVE-HIGH; see hw/gcd_ps.v

  // ---- the batch FSM ------------------------------------------------------
  localparam S_IDLE = 3'd0, S_PREP = 3'd1, S_ISSUE = 3'd2,
             S_WAIT_ACK = 3'd3, S_WAIT_RES = 3'd4, S_ACK = 3'd5,
             S_RTZ = 3'd6, S_NEXT = 3'd7;

  reg [2:0]  st;
  reg [31:0] runs_done, lat_ctr;
  reg [3:0]  prep_ctr;
  reg        bench_busy, bench_done, bench_set_req, bench_o_ack;
  reg [31:0] lfsr;
  reg [31:0] bench_a, bench_b;
  reg        start_d;

  wire       start_rise = bctrl_start & ~start_d;

  // The kernel sees the FSM's operands while a batch is running and the
  // host's registers otherwise.  This mux is a BUNDLED-DATA hazard if it ever
  // moves while a request is in flight -- the data would change under a
  // request that already claimed it was stable -- which is why the FSM sets
  // bench_a/bench_b in S_PREP and then spends prep_ctr cycles doing nothing
  // before it asserts a request in S_ISSUE.  At 100 MHz that settling window
  // is ~160 ns against a bundling requirement measured in nanoseconds, so it
  // is not a tight budget; it is a deliberate one.
  wire [31:0] a_to_core = bench_busy ? bench_a : a_data_reg;
  wire [31:0] b_to_core = bench_busy ? bench_b : b_data_reg;

  // Pulse adapter, shared by the manual and bench paths: the kernel-facing
  // request is SET here and cleared ASYNCHRONOUSLY by the kernel's own ack,
  // so it falls on the kernel's timescale no matter how slowly whoever set it
  // is running.  See hw/gcd_ps.v for why this is load-bearing.
  wire req_clr = i_ack_pl | ~aresetn;
  reg  req_core = 1'b0;
  always @(posedge aclk or posedge req_clr) begin
    if (req_clr)                                            req_core <= 1'b0;
    else if (bench_busy && bench_set_req)                   req_core <= 1'b1;
    else if (!bench_busy && do_write && axi_awaddr == 4'h0) req_core <= wdata[0];
  end
  assign i_req_pl = req_core;

  wire i_ack_host = ctrl_i_req & ~req_core;

  // o_ack always mirrors o_req so it falls with the request it answers.
  assign o_ack_pl = (bench_busy ? bench_o_ack : ctrl_o_ack) & o_req_pl;


  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      st <= S_IDLE; bench_busy <= 1'b0; bench_done <= 1'b0;
      bench_set_req <= 1'b0; bench_o_ack <= 1'b0;
      runs_done <= 32'b0; lat_ctr <= 32'b0; prep_ctr <= 4'b0;
      cycles <= 32'b0; lat_min <= 32'hFFFFFFFF; lat_max <= 32'b0;
      lfsr <= 32'h1; bench_a <= 32'b0; bench_b <= 32'b0;
      last_a <= 32'b0; last_b <= 32'b0; start_d <= 1'b0;
    end else begin
      start_d <= bctrl_start;
      bench_set_req <= 1'b0;

      if (bctrl_rst) begin
        st <= S_IDLE; bench_busy <= 1'b0; bench_done <= 1'b0;
        bench_o_ack <= 1'b0; runs_done <= 32'b0; cycles <= 32'b0;
        lat_min <= 32'hFFFFFFFF; lat_max <= 32'b0;
      end else begin
        if (bench_busy && cycles != 32'hFFFFFFFF) cycles <= cycles + 1;
        if (st != S_IDLE && st != S_NEXT)          lat_ctr <= lat_ctr + 1;

        case (st)
          S_IDLE: if (start_rise && n_runs != 32'b0) begin
                    bench_busy <= 1'b1; bench_done <= 1'b0;
                    runs_done  <= 32'b0; cycles <= 32'b0;
                    lat_min    <= 32'hFFFFFFFF; lat_max <= 32'b0;
                    lfsr       <= (a_data_reg == 32'b0) ? 32'h1 : a_data_reg;
                    st         <= S_PREP;
                  end

          // Choose this run's operands and let them settle before any
          // request claims they are stable.  FIXED mode reruns the host's
          // pair; LFSR mode draws a fresh one.  Operands are masked to 24
          // bits so a batch cannot spend its time on a pathological
          // near-2^31 pair and so both stay positive -- gcd of negatives is
          // a correctness question, not a throughput one.
          S_PREP: begin
                    if (prep_ctr == 4'd0) begin
                      if (bctrl_mode) begin
                        bench_a <= {8'b0, lfsr[23:0]} | 32'd1;
                        bench_b <= {8'b0, {lfsr[11:0], lfsr[23:12]}} | 32'd1;
                        lfsr    <= {lfsr[30:0], lfsr[31] ^ lfsr[21] ^ lfsr[1] ^ lfsr[0]};
                      end else begin
                        bench_a <= a_data_reg;
                        bench_b <= b_data_reg;
                      end
                    end
                    prep_ctr <= prep_ctr + 1;
                    if (prep_ctr == 4'd15) begin
                      prep_ctr <= 4'd0;
                      lat_ctr  <= 32'b0;
                      st       <= S_ISSUE;
                    end
                  end

          S_ISSUE: begin bench_set_req <= 1'b1; st <= S_WAIT_ACK; end

          // i_ack_s is the SYNCHRONIZED view, so every latency below carries
          // a constant two-cycle synchronizer offset.  It is constant, so it
          // cancels out of the MIN-to-MAX spread, which is the number this
          // benchmark is actually for.
          S_WAIT_ACK: if (i_ack_pl) st <= S_WAIT_RES;

          S_WAIT_RES: if (o_req_s) begin
                        last_a <= bench_a;
                        last_b <= bench_b;
                        if (lat_ctr < lat_min) lat_min <= lat_ctr;
                        if (lat_ctr > lat_max) lat_max <= lat_ctr;
                        bench_o_ack <= 1'b1;
                        st <= S_ACK;
                      end

          S_ACK:  st <= S_RTZ;

          S_RTZ:  if (!o_req_s) begin
                    bench_o_ack <= 1'b0;
                    st <= S_NEXT;
                  end

          S_NEXT: begin
                    runs_done <= runs_done + 1;
                    if (runs_done + 1 >= n_runs) begin
                      bench_busy <= 1'b0;
                      bench_done <= 1'b1;
                      st <= S_IDLE;
                    end else st <= S_PREP;
                  end

          default: st <= S_IDLE;
        endcase
      end
    end
  end

  // ---- AXI slave ----------------------------------------------------------
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      axi_awready <= 1'b0; axi_wready <= 1'b0; axi_bvalid <= 1'b0;
      axi_arready <= 1'b0; axi_rvalid <= 1'b0;
      axi_bid <= 12'b0;    axi_rid <= 12'b0;   aw_en <= 1'b1;
      ctrl_i_req <= 1'b0;  ctrl_o_ack <= 1'b0; ctrl_rst <= 1'b1;
      a_data_reg <= 32'b0; b_data_reg <= 32'b0;
      n_runs <= 32'b0;
      bctrl_start <= 1'b0; bctrl_rst <= 1'b0;  bctrl_mode <= 1'b0;
      sync_i_ack <= 2'b0;  sync_o_req <= 2'b0; o_data_capture <= 32'b0;
    end else begin
      sync_i_ack <= {sync_i_ack[0], i_ack_host};
      sync_o_req <= {sync_o_req[0], o_req_pl};
      o_data_capture <= o_data_pl;

      if (~axi_awready && awvalid && wvalid && aw_en) begin
        axi_awready <= 1'b1; axi_wready <= 1'b1;
        axi_awaddr  <= awaddr[5:2];
        axi_bid     <= awid;
        aw_en       <= 1'b0;
      end else begin
        axi_awready <= 1'b0; axi_wready <= 1'b0;
        if (bvalid && bready) aw_en <= 1'b1;
      end

      if (do_write) begin
        case (axi_awaddr)
          4'h0: begin ctrl_i_req <= wdata[0];
                      ctrl_o_ack <= wdata[1];
                      ctrl_rst   <= wdata[2]; end
          4'h2: a_data_reg <= wdata;
          4'h3: b_data_reg <= wdata;
          4'h5: n_runs     <= wdata;
          4'h7: begin bctrl_start <= wdata[0];
                      bctrl_rst   <= wdata[1];
                      bctrl_mode  <= wdata[2]; end
          default: ;
        endcase
      end

      if (do_write && ~axi_bvalid) axi_bvalid <= 1'b1;
      else if (bready && axi_bvalid) axi_bvalid <= 1'b0;

      if (~axi_arready && arvalid) begin
        axi_arready <= 1'b1;
        axi_araddr  <= araddr[5:2];
        axi_rid     <= arid;
      end else axi_arready <= 1'b0;

      if (axi_arready && arvalid && ~axi_rvalid) axi_rvalid <= 1'b1;
      else if (axi_rvalid && rready) axi_rvalid <= 1'b0;
    end
  end

  reg [31:0] rdata_r;
  always @(*) begin
    case (axi_araddr)
      4'h0: rdata_r = {29'b0, ctrl_rst, ctrl_o_ack, ctrl_i_req};
      4'h1: rdata_r = {30'b0, o_req_s, i_ack_s};
      4'h2: rdata_r = a_data_reg;
      4'h3: rdata_r = b_data_reg;
      4'h4: rdata_r = o_data_capture;
      4'h5: rdata_r = n_runs;
      4'h6: rdata_r = cycles;
      4'h7: rdata_r = {29'b0, bctrl_mode, bctrl_rst, bctrl_start};
      4'h8: rdata_r = {runs_done[15:0], 14'b0, bench_done, bench_busy};
      4'h9: rdata_r = lat_min;
      4'hA: rdata_r = lat_max;
      4'hB: rdata_r = last_a;
      4'hC: rdata_r = last_b;
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

  // ---- the kernel and its environment (identical to hw/gcd_ps.v) ----------
  wire       a_ack, b_ack, start_ack;
  wire [2:0] in_req;
  wire       p_end_req, p_end_ack;

  bd_fork #(.N(3)) ufork (
      .rst(rst_pl), .req(i_req_pl), .ack(i_ack_pl),
      .req_out(in_req), .ack_in({start_ack, b_ack, a_ack}));

  bd_delay #(.N(2)) upsnk (.a(p_end_req), .z(p_end_ack));

  bdc_gcd udut (
      .rst       (rst_pl),
      .a_req     (in_req[0]), .a_ack     (a_ack),     .a_data (a_to_core),
      .b_req     (in_req[1]), .b_ack     (b_ack),     .b_data (b_to_core),
      .start_req (in_req[2]), .start_ack (start_ack),
      .out0_req  (o_req_pl),  .out0_ack  (o_ack_pl),  .out0_data (o_data_pl),
      .p_end_req (p_end_req), .p_end_ack (p_end_ack));

  assign core_i_ack = i_ack_pl;
  assign core_o_req = o_req_pl;

endmodule
