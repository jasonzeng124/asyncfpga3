// knapsack_bench_top -- hardware benchmark harness for the knapsack
// async-hls core on the EBAZ4205 (xc7z010clg400-1). Same PS7+BUFG shell
// as zynq/knapsack_ps_top.v around knapsack_bench_bridge, which EXTENDS
// knapsack_ps_bridge's register map (0x00-0x0C byte-compatible: the
// existing xsct driver's poke sequence still works for functional
// checks) with an FCLK0-domain repeat FSM that drives the core's
// 4-phase handshake autonomously N_RUNS times and counts FCLK0 cycles.
//
// WHY: host-paced JTAG pokes (xsdb mwr/mrd) are milliseconds apart while
// one knapsack call is microseconds -- throughput/latency measured from
// the host would be 99.9% JTAG overhead. The repeat FSM keeps the
// measurement loop entirely in fabric; the host only starts the batch
// and reads the totals.
//
// Register map (32-bit, byte addresses, M_AXI_GP0 base + offset):
//   0x00 CTRL     RW [0]=i_req [1]=o_ack [2]=rst    (manual path,
//                 identical semantics to knapsack_ps_top.v: pulse
//                 adapter behind level-driven bits)
//   0x04 STATUS   RO [0]=i_ack(sticky) [1]=o_req    (manual path)
//   0x08 I_DATA   RW cap[7:0] -- ALSO the cap the bench FSM presents
//   0x0C O_DATA   RO LAST_RESULT: o_data[15:0] captured on each o_req
//                 rise (manual AND bench runs) -- correctness stays
//                 checkable after an autonomous batch
//   0x10 N_RUNS   RW number of back-to-back transactions in a batch
//   0x14 CYCLES   RO total FCLK0 cycles, first i_req assert -> run N's
//                 o_req RTZ completion (saturates at 0xFFFFFFFF)
//   0x18 BCTRL    RW [0]=bench_start (level; batch starts on its rise,
//                 clear it before the next batch)  [1]=bench_rst
//                 (level; aborts the FSM, zeroes counters/done)
//   0x1C BSTATUS  RO [0]=busy [1]=done [15:8]=runs_lo (low 8 bits of
//                 the completed-run counter -- progress/wedge diagnosis)
//   0x20 LAT_MIN  RO min per-run latency, cycles (0xFFFFFFFF until a
//                 run completes)
//   0x24 LAT_MAX  RO max per-run latency, cycles
//
// Host batch protocol: write I_DATA=cap, N_RUNS=N; BCTRL=1; poll
// BSTATUS.done==1; read CYCLES/LAT_MIN/LAT_MAX/O_DATA/BSTATUS; BCTRL=0.
// Do NOT touch CTRL bits 0/1 while busy=1 (the FSM owns the core
// handshake; the mux below switches on busy). CTRL.rst must stay 0.
//
// WEDGE-THRESHOLD ANALYSIS (the >=1 us i_req hold that permanently
// wedges the core -- knapsack_jtag_top.v header / BRINGUP_SESSION.md
// item 11): the bench FSM does NOT drop i_req synchronously. It reuses
// the silicon-validated pulse-adapter pattern: the core-facing request
// is a flop SET by the FSM and CLEARED ASYNCHRONOUSLY by the core's own
// i_ack rise, so the request falls nanoseconds after the ack at ANY
// FCLK0 rate -- the 1 us threshold cannot be approached. (Measured on
// the EBAZ4205: FCLK0 is 100 MHz with the standard SLCR recipe --
// IO PLL locked at FDIV=30, only BYPASS_QUAL set, so 1000/10 MHz; see
// BENCH.md's calibration section. Even a hypothetical SYNCHRONOUS drop
// -- i_ack 2-FF sync + 1 FSM cycle = 3 cycles -- would be 30 ns there,
// 33x under the threshold, and would only approach it below ~3 MHz.
// The async clear removes that floor entirely, so no FCLK0 assumption
// is load-bearing.) o_ack mirrors o_req combinationally
// (oack_ff & o_req), so the output RTZ also completes in ~ns. FCLK0
// rate therefore affects only measurement quantization (+-1-2 cycles
// per run at the synchronized endpoints), not protocol safety.
module knapsack_bench_top (
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
  // AWID/ARID -> BID/RID echo is NOT optional decoration: M_AXI_GP0 is
  // a full AXI3 port whose interconnect routes responses by ID; a slave
  // answering with constant BID/RID=0 hangs every CPU access on real
  // silicon (bench-found 2026-07-21, see knapsack_ps_top.v /
  // BRINGUP_SESSION.md item 17).
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

  knapsack_bench_bridge bridge_i (
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

// AXI3 register slave + manual 4-phase pulse adapter + bench repeat FSM
// + core: everything except the PS7/BUFG hard macros, so
// tests/tb_bench_bridge.v can drive the raw AXI channel wires (same
// factoring rationale as knapsack_ps_bridge). The AXI slave FSM is
// copied verbatim from knapsack_ps_bridge (including the mandatory
// BID/RID echo of AWID/ARID -- BRINGUP_SESSION.md item 17); the
// register decode grows from 4 to 10 registers (still within the
// existing awaddr[5:2] index).
module knapsack_bench_bridge (
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

  // ---- host-visible registers ---------------------------------------
  reg        ctrl_i_req, ctrl_o_ack, ctrl_rst;
  reg [7:0]  i_data_reg;
  reg [31:0] n_runs;
  reg        bench_start, bench_rst;

  reg [1:0]  sync_i_ack, sync_o_req;
  reg [15:0] o_data_capture;          // LAST_RESULT (see capture below)

  wire i_ack_s = sync_i_ack[1];
  wire o_req_s = sync_o_req[1];

  wire i_req_pl, o_ack_pl, rst_pl;
  wire i_ack_pl, o_req_pl;
  wire [15:0] o_data_pl;

  assign rst_pl = ctrl_rst;

  // ---- manual-path 4-phase pulse adapter (verbatim pattern from
  // knapsack_ps_bridge; see knapsack_ps_top.v header) ------------------
  wire req_clr = i_ack_pl | ~aresetn;
  reg  req_core = 1'b0;
  always @(posedge aclk or posedge req_clr) begin
    if (req_clr)                             req_core <= 1'b0;
    else if (do_write && axi_awaddr == 4'h0) req_core <= wdata[0];
  end

  wire i_ack_host = ctrl_i_req & ~req_core;

  // ---- bench repeat FSM (FCLK0/aclk domain) --------------------------
  // Drives the core through N_RUNS complete 4-phase transactions with
  // the cap held in I_DATA. Data-before-req is trivial: i_data_reg is
  // written long before bench_start and never changes during the batch.
  localparam [2:0] S_IDLE = 3'd0,
                   S_REQ  = 3'd1,   // (re)issue request when input idle
                   S_WACK = 3'd2,   // wait for the accept (req FF clear)
                   S_WORQ = 3'd3,   // wait for o_req rise
                   S_ACK  = 3'd4,   // assert o_ack (capture already done)
                   S_WRTZ = 3'd5;   // wait for o_req fall = RTZ complete

  reg [2:0]  bstate;
  reg        bench_busy, bench_done;
  reg        oack_ff;
  reg        counting;
  reg        bench_start_d;
  reg [31:0] runs_done;
  reg [31:0] cycles;                 // total, saturating
  reg [31:0] lat_cnt;                // per-run, saturating
  reg [31:0] lat_min, lat_max;

  // Core-facing bench request: the pulse-adapter flop again -- SET by
  // the FSM, CLEARED ASYNCHRONOUSLY by the core's i_ack rise (and by
  // bench_rst/reset so an abort can't leave a request pending). This is
  // what makes the request RTZ ns-scale at any FCLK0 rate (see the top
  // header's wedge-threshold analysis).
  wire bench_req_clr = i_ack_pl | ~aresetn | bench_rst;
  wire bench_req_set;
  reg  bench_req = 1'b0;
  always @(posedge aclk or posedge bench_req_clr) begin
    if (bench_req_clr)      bench_req <= 1'b0;
    else if (bench_req_set) bench_req <= 1'b1;
  end

  // 2-FF synchronizers into the aclk domain (matching the bridge's CDC
  // style). sync_breq samples the async-cleared request flop -- its
  // clear edge is asynchronous, hence the resynchronization. The raw
  // core i_ack pulse can be shorter than one aclk period (set + async
  // clear within ns), so the FSM never waits for a '1' on these: it
  // waits for the STICKY consequence (bench_req reading 0 after the
  // FSM set it) with a >=3-cycle settle so the set has provably
  // traversed the synchronizer first.
  reg [1:0] sync_breq, sync_iack_raw;

  wire breq_guard_ok = ~sync_iack_raw[1] & ~sync_breq[1];
  assign bench_req_set = (bstate == S_REQ) && breq_guard_ok;

  always @(posedge aclk) begin
    if (!aresetn || bench_rst) begin
      bstate        <= S_IDLE;
      bench_busy    <= 1'b0;
      bench_done    <= 1'b0;
      oack_ff       <= 1'b0;
      counting      <= 1'b0;
      bench_start_d <= 1'b0;
      runs_done     <= 32'b0;
      cycles        <= 32'b0;
      lat_cnt       <= 32'b0;
      lat_min       <= 32'hFFFF_FFFF;
      lat_max       <= 32'b0;
      sync_breq     <= 2'b0;
      sync_iack_raw <= 2'b0;
    end else begin
      bench_start_d <= bench_start;
      sync_breq     <= {sync_breq[0], bench_req};
      sync_iack_raw <= {sync_iack_raw[0], i_ack_pl};

      // free-running while measuring; state actions below may override
      if (counting && cycles  != 32'hFFFF_FFFF) cycles  <= cycles  + 1;
      if (counting && lat_cnt != 32'hFFFF_FFFF) lat_cnt <= lat_cnt + 1;

      case (bstate)
        S_IDLE: begin
          if (bench_start && !bench_start_d) begin
            if (n_runs == 32'b0) begin
              bench_done <= 1'b1;          // zero-length batch: no-op
            end else begin
              bench_busy <= 1'b1;
              bench_done <= 1'b0;
              runs_done  <= 32'b0;
              cycles     <= 32'b0;
              lat_min    <= 32'hFFFF_FFFF;
              lat_max    <= 32'b0;
              bstate     <= S_REQ;
            end
          end
        end

        S_REQ: begin
          // Input side must be idle (previous i_ack RTZ done, request
          // flop clear) before the next request rises. bench_req sets
          // on this same edge via bench_req_set; CYCLES starts/continues
          // from exactly this edge -- "first i_req assert".
          if (breq_guard_ok) begin
            counting <= 1'b1;
            lat_cnt  <= 32'b0;
            bstate   <= S_WACK;
          end
        end

        S_WACK: begin
          // Accepted == the flop we set reads back 0 (only i_ack clears
          // it). lat_cnt >= 3 guarantees the set itself has already
          // been seen through the 2-FF sync, so a fast ack (cleared
          // before the sync ever showed 1) isn't mistaken for "not yet
          // issued".
          if (lat_cnt >= 32'd3 && !sync_breq[1]) bstate <= S_WORQ;
        end

        S_WORQ: begin
          // o_data is captured by the shared o_req_s rise-edge capture
          // (below) on this same edge -- strictly before o_ack rises.
          if (o_req_s) bstate <= S_ACK;
        end

        S_ACK: begin
          oack_ff <= 1'b1;
          bstate  <= S_WRTZ;
        end

        S_WRTZ: begin
          // o_req falls ns after o_ack (async core); we observe the
          // fall through the synchronizer. That observation on run N
          // is the CYCLES stop event.
          if (!o_req_s) begin
            oack_ff   <= 1'b0;
            runs_done <= runs_done + 1;
            if (lat_cnt < lat_min) lat_min <= lat_cnt;
            if (lat_cnt > lat_max) lat_max <= lat_cnt;
            if (runs_done + 1 == n_runs) begin
              counting   <= 1'b0;
              bench_busy <= 1'b0;
              bench_done <= 1'b1;
              bstate     <= S_IDLE;
            end else begin
              bstate <= S_REQ;
            end
          end
        end

        default: bstate <= S_IDLE;
      endcase
    end
  end

  // ---- core-facing handshake mux -------------------------------------
  // bench_busy only changes while both paths are idle (the FSM finishes
  // the full RTZ before dropping busy; the host must leave CTRL bits
  // 0/1 at zero while busy), so the mux cannot glitch a live handshake.
  assign i_req_pl = bench_busy ? bench_req : req_core;
  // "Mirror o_req, don't latch it high": both paths AND their ack flop
  // with the live o_req so the ack falls with the req it acknowledges.
  assign o_ack_pl = (bench_busy ? oack_ff : ctrl_o_ack) & o_req_pl;

  // ---- AXI slave FSM (copied from knapsack_ps_bridge) ----------------
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
      i_data_reg <= 8'b0;
      n_runs     <= 32'b0;
      bench_start <= 1'b0;
      bench_rst   <= 1'b0;
      sync_i_ack <= 2'b0;
      sync_o_req <= 2'b0;
    end else begin
      // synchronize clockless PL status into this clock domain
      sync_i_ack <= {sync_i_ack[0], i_ack_host};
      sync_o_req <= {sync_o_req[0], o_req_pl};

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
          4'h4: n_runs     <= wdata;
          4'h6: begin
            bench_start <= wdata[0];
            bench_rst   <= wdata[1];
          end
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

  // ---- LAST_RESULT capture -------------------------------------------
  // One-shot on the SYNCHRONIZED o_req rise: at that edge the real
  // o_req has been high >= 2 aclk periods and no ack has been issued
  // yet (both ack paths react strictly after this edge), so o_data is
  // stable by the bundled-data invariant. Replaces knapsack_ps_bridge's
  // free-running capture; byte-compatible in practice because the host
  // only ever reads O_DATA after polling o_req==1.
  reg o_req_s_d;
  always @(posedge aclk) begin
    if (!aresetn) begin
      o_req_s_d      <= 1'b0;
      o_data_capture <= 16'b0;
    end else begin
      o_req_s_d <= o_req_s;
      if (o_req_s && !o_req_s_d) o_data_capture <= o_data_pl;
    end
  end

  // ---- read mux -------------------------------------------------------
  reg [31:0] rdata_r;
  always @(*) begin
    case (axi_araddr)
      4'h0: rdata_r = {29'b0, ctrl_rst, ctrl_o_ack, ctrl_i_req};
      4'h1: rdata_r = {30'b0, o_req_s, i_ack_s};
      4'h2: rdata_r = {24'b0, i_data_reg};
      4'h3: rdata_r = {16'b0, o_data_capture};
      4'h4: rdata_r = n_runs;
      4'h5: rdata_r = cycles;
      4'h6: rdata_r = {30'b0, bench_rst, bench_start};
      4'h7: rdata_r = {16'b0, runs_done[7:0], 6'b0, bench_done, bench_busy};
      4'h8: rdata_r = lat_min;
      4'h9: rdata_r = lat_max;
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
