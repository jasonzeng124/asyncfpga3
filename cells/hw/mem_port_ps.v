// mem_port_ps.v -- B2/B3: bd_mem itself, on silicon, through its own
// manufactured strobe.
//
// Unlike mem_bist_ps.v (B1, which bypasses bd_mem entirely to isolate the
// toolchain question), this harness instantiates cells/rtl/bd_mem.v UNCHANGED
// (rtl/ is frozen) and drives it only through req/addr/wdata/we/ack -- the
// same four-phase bundled-data interface any caller must use, serialized per
// bd_mem.v's own header: assert address+data+req together (the worst case,
// same convention tb_mem.v uses), wait for ack, drop req, wait for ack to
// fall (RTZ complete) before the next access.  The aclk-domain FSM issuing
// req is NOT the manufactured clock -- it is just a host-speed sequencer;
// req and ack cross into/out of it through a 2-FF synchronizer, same as
// gcd_ps.v's sync_i_ack/sync_o_req.  Waiting for the SYNCHRONIZED ack to
// fall before reasserting req is sufficient serialization: ack-fall is
// causally downstream of req-fall through the whole DSETUP -> strobe ->
// DCO chain, so by the time it is observed the request side has already
// gone quiet.
//
// bd_mem's DSETUP/DCO/USE_BUFG are all fixed at ELABORATION time via
// `defines (BD_MEM_DSETUP, BD_MEM_DCO, BD_MEM_USE_BUFG), not left as Verilog
// module parameters wired to a register -- these are exactly the placement-
// and-route-dependent quantities B2/B3 exist to pin down, and each answer is
// a different bitstream, not a runtime knob.  build_mem.sh passes them via
// BD_DEFINES, same mechanism hw/mult2_ps.v's BD_KEEP_OPERANDS uses.
//
// Two things get measured:
//
//   CORRECTNESS -- the same three self-checking patterns as mem_bist_ps.v
//   (walking-1, walking-0, addr=data), driven through bd_mem's real
//   handshake instead of a bare synchronous RAM.  Same self-reporting
//   register shape.
//
//   COST -- once correctness finishes, SPD_N back-to-back READ round trips
//   at a fixed address, timed by a free-running aclk cycle counter that only
//   runs during that phase.  Per-access latency = SPD_CYCLES / SPD_N / 100
//   MHz.  This is a DIFFERENTIAL measurement across builds (BUFG vs plain):
//   the synchronizer and sequencer overhead is identical in every build, so
//   it cancels in the difference even though it inflates the absolute
//   number.
`ifndef BD_MEM_DSETUP
 `define BD_MEM_DSETUP 8
`endif
`ifndef BD_MEM_DCO
 `define BD_MEM_DCO 12
`endif
`ifndef BD_MEM_USE_BUFG
 `define BD_MEM_USE_BUFG 0
`endif

module mem_port_ps (
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

  wire port_busy, port_done;

  mem_port_bridge bridge_i (
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

    .port_busy (port_busy),
    .port_done (port_done)
  );

  assign led_red   = port_busy;
  assign led_green = port_done;

endmodule

module mem_port_bridge (
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

  output        port_busy,
  output        port_done
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

  reg ctrl_rst;

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

  // ---- bd_mem itself, exactly as shipped in rtl/ -------------------------
  localparam AW = 10;
  localparam DW = 16;
  localparam integer SPD_N = 4096;

  reg           req;
  reg  [AW-1:0] addr;
  reg  [DW-1:0] wval;
  reg           we;
  wire          ack;
  wire [DW-1:0] port_rdata;

  bd_mem #(.AW(AW), .DW(DW),
           .DSETUP(`BD_MEM_DSETUP), .DCO(`BD_MEM_DCO),
           .USE_BUFG(`BD_MEM_USE_BUFG))
      udut (.req(req), .ack(ack), .addr(addr), .wdata(wval), .we(we),
            .rdata(port_rdata));

  // ack is asynchronous w.r.t. aclk -- bd_mem is self-timed, there is no
  // clock relationship to exploit -- so it crosses through a 2-FF
  // synchronizer before any control decision reads it, same practice as
  // gcd_ps.v's sync_i_ack/sync_o_req.
  reg [1:0] sync_ack;
  always @(posedge aclk or negedge aresetn)
      if (!aresetn) sync_ack <= 2'b0;
      else          sync_ack <= {sync_ack[0], ack};
  wire ack_s = sync_ack[1];

  reg  [1:0] pat;
  reg  [3:0] k;
  wire [DW-1:0] cur_val = (pat == 2'd0) ? (16'h1 << k) :
                          (pat == 2'd1) ? ~(16'h1 << k) :
                          {6'b0, addr};

  // Address+data+req must race on the SAME edge to exercise bd_mem's real
  // worst case (its own header: "assert address+data+req together").  The
  // *ADV states below advance addr one cycle before the *ASSERT states used
  // to (re-)assert req/we/wval -- which meant addr was always a full aclk
  // cycle stable before req rose, never actually racing ADDRARDADDR's setup
  // window against the manufactured strobe.  addr_p1/cur_val_next let the
  // *ADV states pre-compute the NEXT access's payload and drive it onto
  // we/req/wval on the SAME edge that addr itself advances; the *ASSERT
  // states still (redundantly, harmlessly) re-drive the same values every
  // cycle they wait for ack, so nothing here removes their old behavior,
  // it only makes the address-changing edge and the request-rising edge
  // the SAME edge, for every access after the first.
  wire [AW-1:0] addr_p1 = addr + 1'b1;
  wire [DW-1:0] cur_val_next = (pat == 2'd0) ? (16'h1 << k) :
                                (pat == 2'd1) ? ~(16'h1 << k) :
                                {6'b0, addr_p1};

  reg [DW-1:0] cap_val;

  localparam S_IDLE     = 5'd0,
             S_W_ASSERT  = 5'd1,
             S_W_DEASSRT = 5'd2,
             S_W_ADV     = 5'd3,
             S_R_ASSERT  = 5'd4,
             S_R_DEASSRT = 5'd5,
             S_R_CHECK   = 5'd6,
             S_R_ADV     = 5'd7,
             S_NEXTPAT   = 5'd8,
             S_SPD_ASSRT = 5'd9,
             S_SPD_DEASS = 5'd10,
             S_SPD_ADV   = 5'd11,
             S_DONE      = 5'd12;
  reg [4:0] st;

  reg [31:0] mismatch_count;
  reg        fail_latched;
  reg [AW-1:0] fail_addr;
  reg [DW-1:0] fail_got, fail_expect;
  reg [1:0]  fail_pat;
  reg [3:0]  fail_k;
  reg        run_pass;

  reg [31:0] spd_iter;
  reg [31:0] spd_cycles;
  reg        spd_counting;

  wire busy = (st != S_IDLE) && (st != S_DONE);
  assign port_busy = busy;
  assign port_done = (st == S_DONE);

  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      st <= S_IDLE;
      req <= 1'b0;
      spd_counting <= 1'b0;
    end else if (ctrl_rst) begin
      st  <= S_IDLE;
      req <= 1'b0;
      spd_counting <= 1'b0;
    end else begin
      if (spd_counting) spd_cycles <= spd_cycles + 1'b1;

      case (st)
        S_IDLE: begin
          pat <= 2'd0; k <= 4'd0; addr <= {AW{1'b0}};
          mismatch_count <= 32'd0;
          fail_latched   <= 1'b0;
          run_pass       <= 1'b1;
          // First access, pat=0 k=0: cur_val is 16'h1 independent of addr,
          // so it is safe to race wval/we/req with the addr reset here --
          // see the addr_p1/cur_val_next note above.
          wval <= 16'h1;
          we   <= 1'b1;
          req  <= 1'b1;
          st   <= S_W_ASSERT;
        end

        // -- correctness: write pass --------------------------------------
        S_W_ASSERT: begin
          wval <= cur_val;
          we   <= 1'b1;
          req  <= 1'b1;           // payload and request together (worst case)
          if (ack_s) st <= S_W_DEASSRT;
        end
        S_W_DEASSRT: begin
          req <= 1'b0;
          if (!ack_s) st <= S_W_ADV;
        end
        S_W_ADV: begin
          if (addr == {AW{1'b1}}) begin
            addr <= {AW{1'b0}};
            we   <= 1'b0;
            req  <= 1'b1;      // first read: races with the addr reset
            st   <= S_R_ASSERT;
          end else begin
            addr <= addr + 1'b1;
            wval <= cur_val_next;
            we   <= 1'b1;
            req  <= 1'b1;      // races with the addr advance above
            st   <= S_W_ASSERT;
          end
        end

        // -- correctness: read pass ---------------------------------------
        S_R_ASSERT: begin
          we  <= 1'b0;
          req <= 1'b1;
          if (ack_s) begin
            cap_val <= port_rdata;
            st      <= S_R_DEASSRT;
          end
        end
        S_R_DEASSRT: begin
          req <= 1'b0;
          if (!ack_s) st <= S_R_CHECK;
        end
        S_R_CHECK: begin
          if (cap_val !== cur_val) begin
            mismatch_count <= mismatch_count + 1'b1;
            run_pass <= 1'b0;
            if (!fail_latched) begin
              fail_latched <= 1'b1;
              fail_addr    <= addr;
              fail_got     <= cap_val;
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
            req  <= 1'b1;      // races with the addr advance above
            st   <= S_R_ASSERT;
          end
        end
        S_NEXTPAT: begin
          if (pat == 2'd2) begin
            // correctness walk complete -- move into the timed phase
            addr <= {AW{1'b0}};
            we   <= 1'b0;
            spd_iter     <= 32'd0;
            spd_cycles   <= 32'd0;
            spd_counting <= 1'b1;
            st <= S_SPD_ASSRT;
          end else if (k == 4'd15) begin
            pat <= pat + 1'b1;
            k   <= 4'd0;
            st  <= S_W_ASSERT;
          end else begin
            k  <= k + 1'b1;
            st <= S_W_ASSERT;
          end
        end

        // -- cost: SPD_N back-to-back read round trips, timed -------------
        S_SPD_ASSRT: begin
          req <= 1'b1;
          if (ack_s) st <= S_SPD_DEASS;
        end
        S_SPD_DEASS: begin
          req <= 1'b0;
          if (!ack_s) st <= S_SPD_ADV;
        end
        S_SPD_ADV: begin
          if (spd_iter == SPD_N - 1) begin
            spd_counting <= 1'b0;
            st <= S_DONE;
          end else begin
            spd_iter <= spd_iter + 1'b1;
            st <= S_SPD_ASSRT;
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
      5'h1: rdata_r = {28'b0, port_done && run_pass, port_done, busy, ack_s};
      5'h2: rdata_r = mismatch_count;
      5'h3: rdata_r = {22'b0, fail_addr};
      5'h4: rdata_r = {16'b0, fail_got};
      5'h5: rdata_r = {16'b0, fail_expect};
      5'h6: rdata_r = {23'b0, fail_k, fail_pat};
      5'h7: rdata_r = {6'b0, addr, 3'b0, k, pat};
      5'h8: rdata_r = spd_cycles;
      5'h9: rdata_r = SPD_N;
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

endmodule
