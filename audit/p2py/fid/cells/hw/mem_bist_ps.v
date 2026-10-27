// mem_bist_ps.v -- B1: can openXC7 encode a RAMB18E1 correctly AT ALL?
//
// Deliberately has NOTHING to do with bd_mem.  bd_mem answers "is the
// ASYNCHRONOUS strobe-and-acknowledge wrapper around a RAMB18E1 safe"; this
// answers the strictly prior question "does the toolchain build a working
// RAMB18E1 at all", so a failure here is toolchain bug number five and every
// async question about bd_mem is moot until it's fixed.  No strobe
// generation, no bd_delay, no handshake: CLKARDCLK is tied straight to
// aclk, the same net every flip-flop in this harness already uses, exactly
// the way gcd_ps.v and every other PS harness in this tree treats aclk.
// That is what "ordinary synchronous RAM" means here.
//
// Walks every address (AW=10 -> 1024 words) and every data bit (DW=16),
// entirely IN HARDWARE -- a host-paced JTAG loop over 1024*16*2 accesses at
// ~100 ms/round-trip would take hours, and per hw-docs/02 section 5 and the
// project convention (see gcd_bench_top.v's fabric-FSM tier) an experiment
// must judge itself, not stream every vector to the host.  Three patterns,
// each covering the whole array:
//
//   walking-1  (pat 0): for k = 0..15, write (1<<k) to every address, then
//               read every address back and require exactly (1<<k).  Catches
//               a data bit stuck-at-0 (the target bit reads 0) or another bit
//               stuck-at-1 / bit-to-bit coupling (a bit that should be 0
//               reads 1).
//   walking-0  (pat 1): the bitwise complement of the above, every pass.
//               Catches the inverse stuck-at faults walking-1 cannot see.
//   addr=data  (pat 2): write addr (zero-extended to 16 bits) to every
//               address, read back and require rdata == addr.  Catches
//               addressing faults -- the wrong word written or read --
//               which a fixed-pattern test can't, because every address
//               looks the same to it.
//
// Self-reporting per hw-docs' own rule: STATUS.done/pass plus a first-
// mismatch record (pattern, bit, address, got, expected).  The host writes
// CTRL.rst=0 to start a run and polls STATUS.done -- no oscilloscope, no
// per-vector host traffic.
//
// Register map (32-bit, byte addresses, M_AXI_GP0 base 0x40000000 + offset).
//   0x00 CTRL        RW  [0]=rst (powers up 1; clearing it starts one run)
//   0x04 STATUS      RO  [0]=busy [1]=done [2]=pass (meaningful once done)
//   0x08 RESULT      RO  [31:0] total mismatch count over the whole run
//   0x0C FAIL_ADDR   RO  [9:0]  word address of the FIRST mismatch
//   0x10 FAIL_GOT    RO  [15:0] data actually read back at the first mismatch
//   0x14 FAIL_EXPECT RO  [15:0] data that should have been there
//   0x18 FAIL_TAG    RO  [1:0]=pattern (0=walk1,1=walk0,2=addr=data)
//                        [8:4]=bit index k (pattern 0/1 only)
//   0x1C PROGRESS    RO  [1:0]=pattern [8:4]=k [25:16]=addr -- live position,
//                        so a hang (rather than a fail) is diagnosable too.
//
// This harness reuses the board-proven PS7 + AXI3 register-slave shape from
// gcd_ps.v (itself ported from hw-docs/ref/zynq/fib_ps_top.v) rather than
// writing a new one.
module mem_bist_ps (
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

  wire bist_busy, bist_done;

  mem_bist_bridge bridge_i (
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

    .bist_busy (bist_busy),
    .bist_done (bist_done)
  );

  assign led_red   = bist_busy;
  assign led_green = bist_done;

endmodule

// AXI3 register slave (same single-beat pattern as gcd_ps_bridge) plus the
// BIST engine.  Everything lives on aclk -- there is no clockless core here
// at all, so unlike gcd_ps_bridge there is no pulse adapter and no CDC
// synchronizer: this is exactly the "ordinary synchronous" case B1 asks for.
module mem_bist_bridge (
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

  output        bist_busy,
  output        bist_done
);

  reg        axi_awready, axi_wready, axi_bvalid;
  reg        axi_arready, axi_rvalid;
  reg [4:0]  axi_awaddr, axi_araddr;
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

  reg ctrl_rst;   // powers up 1; software clears it to launch a run

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
      ctrl_rst    <= 1'b1;
    end else begin
      if (~axi_awready && awvalid && wvalid && aw_en) begin
        axi_awready <= 1'b1;
        axi_wready  <= 1'b1;
        axi_awaddr  <= awaddr[6:2];
        axi_bid     <= awid;
        aw_en       <= 1'b0;
      end else begin
        axi_awready <= 1'b0;
        axi_wready  <= 1'b0;
        if (bvalid && bready) aw_en <= 1'b1;
      end

      if (do_write) begin
        case (axi_awaddr)
          5'h0: ctrl_rst <= wdata[0];
          default: ;
        endcase
      end

      if (do_write && ~axi_bvalid) axi_bvalid <= 1'b1;
      else if (bready && axi_bvalid) axi_bvalid <= 1'b0;

      if (~axi_arready && arvalid) begin
        axi_arready <= 1'b1;
        axi_araddr  <= araddr[6:2];
        axi_rid     <= arid;
      end else begin
        axi_arready <= 1'b0;
      end

      if (axi_arready && arvalid && ~axi_rvalid) axi_rvalid <= 1'b1;
      else if (axi_rvalid && rready) axi_rvalid <= 1'b0;
    end
  end

  // ---- the BIST engine, driving a plain synchronous RAMB18E1 ------------
  localparam AW = 10;
  localparam DW = 16;

  reg          we;
  reg  [AW-1:0] addr;
  reg  [DW-1:0] wval;
  wire [DW-1:0] rval;

  wire [13:0] a14 = {addr, 4'b0000};   // x18 port: word address is [13:4]

  RAMB18E1 #(.RAM_MODE("TDP"),
             .READ_WIDTH_A(18), .WRITE_WIDTH_A(18),
             .READ_WIDTH_B(0),  .WRITE_WIDTH_B(0),
             .DOA_REG(0), .DOB_REG(0),
             .WRITE_MODE_A("WRITE_FIRST"), .WRITE_MODE_B("WRITE_FIRST"),
             .SIM_DEVICE("7SERIES"))
      uram (
          .CLKARDCLK(aclk),         .CLKBWRCLK(1'b0),
          .ENARDEN(1'b1),           .ENBWREN(1'b0),
          .REGCEAREGCE(1'b0),       .REGCEB(1'b0),
          .RSTRAMARSTRAM(1'b0),     .RSTRAMB(1'b0),
          .RSTREGARSTREG(1'b0),     .RSTREGB(1'b0),
          .ADDRARDADDR(a14),        .ADDRBWRADDR(14'b0),
          .DIADI(wval),             .DIBDI(16'b0),
          .DIPADIP(2'b0),           .DIPBDIP(2'b0),
          .WEA({2{we}}),            .WEBWE(4'b0),
          .DOADO(rval),             .DOBDO(),
          .DOPADOP(),               .DOPBDOP());

  // pattern generator: value to write, and the value a read at `addr` must
  // return once this pattern's write pass has completed.
  reg  [1:0] pat;                  // 0=walk1 1=walk0 2=addr=data
  reg  [3:0] k;
  wire [DW-1:0] cur_val = (pat == 2'd0) ? (16'h1 << k) :
                          (pat == 2'd1) ? ~(16'h1 << k) :
                          {6'b0, addr};

  localparam S_IDLE    = 4'd0,
             S_W_SETUP = 4'd1,
             S_W_ADV   = 4'd2,
             S_R_SETUP = 4'd3,
             S_R_WAIT  = 4'd4,
             S_R_CHECK = 4'd5,
             S_R_ADV   = 4'd6,
             S_NEXTPAT = 4'd7,
             S_DONE    = 4'd8;
  reg [3:0] st;

  reg [31:0] mismatch_count;
  reg        fail_latched;
  reg [AW-1:0] fail_addr;
  reg [DW-1:0] fail_got, fail_expect;
  reg [1:0]  fail_pat;
  reg [3:0]  fail_k;
  reg        run_pass;

  wire busy = (st != S_IDLE) && (st != S_DONE);
  assign bist_busy = busy;
  assign bist_done = (st == S_DONE);

  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      st <= S_IDLE;
    end else if (ctrl_rst) begin
      st <= S_IDLE;
    end else begin
      case (st)
        S_IDLE: begin
          pat <= 2'd0; k <= 4'd0; addr <= {AW{1'b0}};
          mismatch_count <= 32'd0;
          fail_latched <= 1'b0;
          run_pass <= 1'b1;
          we <= 1'b0;
          st <= S_W_SETUP;
        end
        S_W_SETUP: begin
          wval <= cur_val;
          we   <= 1'b1;
          st   <= S_W_ADV;
        end
        S_W_ADV: begin
          we <= 1'b0;
          if (addr == {AW{1'b1}}) begin
            addr <= {AW{1'b0}};
            st   <= S_R_SETUP;
          end else begin
            addr <= addr + 1'b1;
            st   <= S_W_SETUP;
          end
        end
        S_R_SETUP: begin
          we <= 1'b0;
          st <= S_R_WAIT;         // address now presented; RAM latency 1 clk
        end
        S_R_WAIT: begin
          st <= S_R_CHECK;
        end
        S_R_CHECK: begin
          if (rval !== cur_val) begin
            mismatch_count <= mismatch_count + 1'b1;
            run_pass <= 1'b0;
            if (!fail_latched) begin
              fail_latched <= 1'b1;
              fail_addr    <= addr;
              fail_got     <= rval;
              fail_expect  <= cur_val;
              fail_pat     <= pat;
              fail_k       <= k;
            end
          end
          st <= S_R_ADV;
        end
        S_R_ADV: begin
          if (addr == {AW{1'b1}}) begin
            addr <= {AW{1'b0}};
            st   <= S_NEXTPAT;
          end else begin
            addr <= addr + 1'b1;
            st   <= S_R_SETUP;
          end
        end
        S_NEXTPAT: begin
          if (pat == 2'd2) begin
            st <= S_DONE;
          end else if (k == 4'd15) begin
            pat <= pat + 1'b1;
            k   <= 4'd0;
            st  <= S_W_SETUP;
          end else begin
            k  <= k + 1'b1;
            st <= S_W_SETUP;
          end
        end
        S_DONE: /* hold until rst pulses */ ;
        default: st <= S_IDLE;
      endcase
    end
  end

  reg [31:0] rdata_r;
  always @(*) begin
    case (axi_araddr)
      5'h0: rdata_r = {31'b0, ctrl_rst};
      5'h1: rdata_r = {29'b0, bist_done && run_pass, bist_done, busy};
      5'h2: rdata_r = mismatch_count;
      5'h3: rdata_r = {22'b0, fail_addr};
      5'h4: rdata_r = {16'b0, fail_got};
      5'h5: rdata_r = {16'b0, fail_expect};
      5'h6: rdata_r = {23'b0, fail_k, fail_pat};
      5'h7: rdata_r = {6'b0, addr, 3'b0, k, pat};
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

endmodule
