// mem_arb_ps.v -- the ARBITRATED bundled-data memory port, on silicon,
// exercised through a program-order TOKEN exactly the way
// cells/tb/tb_bdc_memseq.v's `BDC_SEQ_TOKEN mode drives it.
//
// This is a sibling of hw/mem_port_ps.v, not a replacement for it: mem_port_ps
// puts one bd_mem instance under a host-speed sequencer to answer "does
// bd_mem's own manufactured strobe work on real silicon."  This file answers
// a different question that bdc/AUDIT.md section 7 leaves explicitly open --
// "`mem_controller` is where the program order lives, and it is unbuilt" --
// by putting the design that section 7 built and simulated (two `:seq`
// stations sharing one `bdc_memport_arb_10_32_2`, ordered only by a token
// chain) under the same kind of manufactured-strobe pressure mem_port_ps put
// on bare bd_mem.  The PS7 instantiation, FCLK/BUFG wiring, aresetn/ctrl_rst
// reset discipline, AXI register-file bridge shape, and 2-FF synchronizer
// discipline on every async->aclk crossing are all copied structurally from
// mem_port_ps.v; anything that looks unfamiliar below is new because the
// design under test is new, not because the harness convention changed.
//
// -- THE DESIGN UNDER TEST, AND WHY IT IS WIRED THIS WAY -------------------
//
// Three generated modules (build/gen/bdc_mem_units.v, from
// `bdc/mem.py store:10:32:seq load:10:32:seq portarb:10:32:2`), wired
// EXACTLY as tb_bdc_memseq.v's `BDC_SEQ_TOKEN block wires them:
//
//   bdc_store_seq_10_32  on port slot 0
//   bdc_load_seq_10_32   on port slot 1
//   bdc_memport_arb_10_32_2  (bd_arbiter in front of two RAMB18E1s -- one
//                             gang per 16 bits of the 32-bit word)
//
// The store's completion channel IS the load's token: `store.z_req` drives
// `load.c_req`, `load.c_ack` drives `store.z_ack`.  bdc/AUDIT.md section 7
// spells out why this is ordinary channel composition and not a new cell --
// a store's z channel already carries no data, so `store.z -> load.c` is
// precisely a program-order edge -- and why nothing else may be added to
// order the two accesses: an EARLIER attempt wired the load's c_req from the
// store's c_ack instead of its z_req, which is not a handshake (an
// acknowledge is not a request), and the store's `hold` falls on its own
// schedule, pulling the load's request out from under it mid-join.  Compose
// channels, not acknowledges.  This file does not repeat that mistake, and
// does not add a second sequencing mechanism on top of the token -- the FSM
// below raises every operand concurrently, same as the testbench, and lets
// the token chain alone decide the order.
//
// The arbitrated port matters here because AUDIT.md section 7 also measured
// what happens without one: the PLAIN port under a token chain gets 12 RAM
// edges for 24 accesses (half the accesses silently never happen, because a
// station raises z_req -- its completion -- while its own p_req is still
// high, so the next station's token arrives before the port is free).  The
// arbiter makes each slot's claim exclusive, but is not by itself sufficient
// either: with `p_req = joined` a token chain on the arbitrated port
// deadlocks after one RAM edge, because the store will not free the port
// until the load completes and the load cannot start until the store frees
// it.  The `done` latch in bdc_store_seq_10_32 / bdc_load_seq_10_32 (`done =
// joined & (p_ack | done)`, `p_req = joined & ~done`) is what lets the port
// claim complete and release on the RAM's own schedule instead of the
// dataflow's.  All of that is inside the generated stations; this harness's
// job is only to drive them and check the result on real silicon, which
// simulation cannot do for the return-to-zero timing this design's own
// station comments call out (rule C's hold margin, DCO's role as an address
// hold guard, etc. -- section 7 again).
//
// -- DSETUP/DCO: WHY THE PLACEHOLDERS AND NOT verify/resize.sh's ANSWER ----
//
// bdc_memport_arb_10_32_2's two RAMB18E1 gangs each need their own
// DSETUP/DCO, fixed at ELABORATION time via `defines exactly the way
// mem_port_ps.v fixes BD_MEM_DSETUP/BD_MEM_DCO -- these are placement-and-
// route-dependent quantities, not runtime knobs, so a `parameter` wired to a
// register would be answering a question resize.sh already tried to answer
// and got wrong.
//
// bdc/AUDIT.md section 7 ("The routed answer, and a hole in the sizing loop
// that is not about memory") records that resize.sh's own tightened answer
// for this exact port -- UMEM0_USETUP 5 -- passed on the single unseeded
// route the loop trusts, and then FAILED rule B's setup window on 3 of 8
// independently seeded placer routes (-225, -266, -379 ps against a 737 ps
// window), while the untightened placeholder (USETUP 8) passed clean on all
// of them (+872 .. +2405 ps, 12/12 ok).  The scatter that causes this is
// about four delay links wide (clock arrival moved 4325 -> 5730 ps over six
// routes at fixed lengths), which is the ENTIRE tightening budget resize.sh
// spent to get from 8 down to 5.  So the tightened numbers are not merely
// unconfirmed, they are measured wrong on this design, and shortening a
// matched delay is the risky direction (too short is a setup violation no
// simulation can see; too long only costs cycles).  These `defines therefore
// stay at the untightened placeholders on purpose -- do not tighten them
// without re-reading section 7's seed table.
`ifndef BD_SZ_UPORT_UMEM0_USETUP
 `define BD_SZ_UPORT_UMEM0_USETUP 8
`endif
`ifndef BD_SZ_UPORT_UMEM1_USETUP
 `define BD_SZ_UPORT_UMEM1_USETUP 8
`endif
`ifndef BD_SZ_UPORT_UMEM0_UCO
 `define BD_SZ_UPORT_UMEM0_UCO 12
`endif
`ifndef BD_SZ_UPORT_UMEM1_UCO
 `define BD_SZ_UPORT_UMEM1_UCO 12
`endif

// -- THREE PHASES ------------------------------------------------------------
//
// Phase 1 (program order): for each of N addresses, issue one store/load
// pair -- the load reads the SAME address the store just wrote, ordered only
// by the token, exactly like tb_bdc_memseq.v's loop.  Mismatches counted in
// P1_MISMATCH.
//
// Phase 2 (the RAM actually holds it): bd_mem sets WRITE_MODE_A("WRITE_FIRST")
// (rtl/bd_mem.v), so on a same-edge access DOADO returns the data being
// WRITTEN -- AUDIT.md section 7 measured exactly this passthrough on the
// plain port ("the load read the store's payload without ever performing a
// read").  Phase 1's load is a SEPARATE transaction from its store (a whole
// second RAM edge, gated by the token), so it is not that passthrough -- but
// nothing in phase 1 proves the RAM still holds the value once the write
// that produced it is no longer the most recent thing that happened to that
// address.  Phase 2 re-reads all N addresses in a second, independent pass
// after phase 1 finishes, so a token/RAM interaction that only fools a
// same-generation read cannot hide behind it.
//
// Phase 2 still has to fire the token to get a load at all -- the load's
// c_req comes from the store's z_req, there is no other way to start one --
// so phase 2 RE-STORES the same payload to the same address immediately
// before re-reading it.  Be honest about what that does and does not prove:
// it demonstrates the value survives a SECOND transaction on the address,
// not that it survives with no write at all.  A read-only phase 2 would need
// wiring this design does not have (an unsequenced load station with no
// token input), and inventing that just to dodge this limit would be its own
// unaudited mechanism.  So phase 2 is exactly as strong as "re-store, then
// re-read comes back right," named as such, not as an unconditional proof
// the RAM retains data with no write in between.
//
// Phase 3 (cost): SPD_N back-to-back store/load pairs at a fixed address,
// timed by a free-running aclk cycle counter that runs only during this
// phase -- same shape as mem_port_ps.v's cost phase, same reason (the
// synchronizer/sequencer overhead is identical across builds and cancels in
// a differential comparison even though it inflates the absolute number).
//
// -- THE HANG DETECTOR --------------------------------------------------
//
// The failure this design exists to rule out is a deadlock -- the port claim
// never returning to zero, which AUDIT.md section 7 reports actually
// happening during bring-up (`p_req = joined` alone: one RAM edge, then
// nothing).  Every wait state below (S_WAIT_LZ, S_WAIT_TOK, S_RTZ) carries
// its own timeout counter; on expiry it latches which one fired into
// TIMEOUT_CODE and forces the FSM to S_DONE rather than hanging the AXI
// poller along with the fabric.  A harness that hangs reports nothing, which
// is exactly the failure mode a hang detector exists to make visible.
//
// -- WHAT THIS FILE DELIBERATELY DOES NOT DO -----------------------------
//
// No delay element anywhere, arbitrary or otherwise.  Every wait in the FSM
// below is a wait on a real, synchronized handshake signal (lz_req, tok_ack,
// la_ack) -- if a state ever needed a fixed number of cycles to "be safe" it
// would mean the protocol was misunderstood, not that a delay was missing.
// No LOC/BEL constraints and no clock buffer beyond the one BUFG this file's
// top level instantiates for aclk (same as mem_port_ps.v) -- bd_mem inside
// the generated port already fixes USE_BUFG=0 for both RAM gangs
// (bdc_memport_arb_10_32_2's own source), so build_mem.sh's -noclkbuf /
// stray-BUFG check should see exactly one BUFG in the FASM, same as
// mem_port_ps built with USE_BUFG=0.

module mem_arb_ps (
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

  wire port_busy, port_done, port_pass;

  mem_arb_bridge bridge_i (
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
    .port_done (port_done),
    .port_pass (port_pass)
  );

  // Unlike mem_port_ps.v (led_green = done, led_red = busy -- there, "it
  // finished" was the interesting event because that harness's checkers were
  // read out over xsdb regardless), THIS harness's spec is explicit: green
  // means every check passed AND nothing timed out, red means anything else
  // -- including "still running" and "finished but failed."  port_pass
  // already folds in done/timeout/both mismatch counts (see overall_pass in
  // mem_arb_bridge), so the LEDs are a direct, un-massaged copy of it.
  assign led_green = port_pass;
  assign led_red   = ~port_pass;

endmodule

module mem_arb_bridge (
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
  output        port_done,
  output        port_pass
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

  // ---- the design under test: two :seq stations + one arbitrated port, ---
  // wired exactly as tb_bdc_memseq.v's `BDC_SEQ_TOKEN block ------------------
  localparam AW = 10;
  localparam DW = 32;
  localparam integer N      = 64;    // addresses covered by phases 1 and 2
  localparam integer SPD_N  = 2048;  // timed store/load pairs in phase 3

  reg              sa_req, sd_req, la_req, tok_req, lz_ack;
  wire             sa_ack, sd_ack, tok_ack;
  wire             store_z_req, store_z_ack;  // store.z -> load.c: the token
  wire             la_ack;
  wire             lz_req;
  wire [DW-1:0]    lz_data;

  wire [1:0]       s_req, s_we, s_ack;
  wire [2*AW-1:0]  s_addr;
  wire [2*DW-1:0]  s_wdata;
  wire [DW-1:0]    p_rdata;

  // idx/phase select the address and payload; both are stable across an
  // entire access (S_ASSERT..S_RTZ) and only change in S_ADV, after the
  // request lines have already been dropped -- so unlike mem_port_ps.v's
  // *_ADV states, this FSM never needs to race an address change against a
  // req-rising edge on the same clock edge.  That race exists in
  // mem_port_ps.v only because it re-drives req every cycle to save a state;
  // bd_mem's own DSETUP/DCO already carry the setup obligation for the
  // manufactured clock, and this harness's job is to offer a stable operand
  // into the station, not to re-derive that timing budget.
  reg  [1:0]    phase;      // 0 = phase1, 1 = phase2, 2 = phase3 (SPD)
  reg  [AW-1:0] idx;

  localparam [DW-1:0] SPD_PAYLOAD = 32'hA5A5_5A5A;

  wire [AW-1:0] cur_addr    = (phase == 2'd2) ? {AW{1'b0}} : idx;
  // Same payload shape tb_bdc_memseq.v's TOKEN loop uses (i folded into both
  // halves of the word), so a mismatch reported here is directly comparable
  // to a mismatch tb_bdc_memseq.v would report for the same index.
  wire [DW-1:0] cur_payload = (phase == 2'd2) ? SPD_PAYLOAD :
                               {16'hC0D0 + {6'b0, idx}, 16'h0A00 + {6'b0, idx}};

  bdc_store_seq_10_32 ust (
      .rst(~aresetn | ctrl_rst),
      .c_req(tok_req), .c_ack(tok_ack),
      .a_req(sa_req), .a_ack(sa_ack), .a_data(cur_addr),
      .d_req(sd_req), .d_ack(sd_ack), .d_data(cur_payload),
      .z_req(store_z_req), .z_ack(store_z_ack),
      .p_req(s_req[0]), .p_ack(s_ack[0]), .p_addr(s_addr[AW*0 +: AW]),
      .p_wdata(s_wdata[DW*0 +: DW]), .p_we(s_we[0]), .p_rdata(p_rdata));

  bdc_load_seq_10_32 uld (
      .rst(~aresetn | ctrl_rst),
      .c_req(store_z_req), .c_ack(store_z_ack),
      .a_req(la_req), .a_ack(la_ack), .a_data(cur_addr),
      .z_req(lz_req), .z_ack(lz_ack), .z_data(lz_data),
      .p_req(s_req[1]), .p_ack(s_ack[1]), .p_addr(s_addr[AW*1 +: AW]),
      .p_wdata(s_wdata[DW*1 +: DW]), .p_we(s_we[1]), .p_rdata(p_rdata));

  bdc_memport_arb_10_32_2 #(.DSETUP_0(`BD_SZ_UPORT_UMEM0_USETUP),
                            .DCO_0(`BD_SZ_UPORT_UMEM0_UCO),
                            .DSETUP_1(`BD_SZ_UPORT_UMEM1_USETUP),
                            .DCO_1(`BD_SZ_UPORT_UMEM1_UCO)) uport (
      .rst(~aresetn | ctrl_rst), .s_req(s_req), .s_addr(s_addr),
      .s_wdata(s_wdata), .s_we(s_we), .s_ack(s_ack), .p_rdata(p_rdata));

  // sa_ack/sd_ack are not separately waited on: bdc_store_seq_10_32 ties
  // a_ack, d_ack and c_ack to the same internal `hold` C-element (see
  // build/gen/bdc_mem_units.v), so tok_ack rising/falling is the same event
  // as sa_ack/sd_ack rising/falling.  Watching tok_ack is therefore
  // sufficient and matches tb_bdc_memseq.v's TOKEN loop, which only ever
  // waits on tok_ack for the store side.

  // -- 2-FF synchronizers, one per async->aclk crossing, same discipline as
  // mem_port_ps.v's sync_ack / gcd_ps.v's sync_i_ack/sync_o_req.  All three
  // signals below are outputs of the self-timed fabric with no clock
  // relationship to aclk to exploit.
  reg [1:0] sync_lz_req, sync_tok_ack, sync_la_ack;
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      sync_lz_req  <= 2'b0;
      sync_tok_ack <= 2'b0;
      sync_la_ack  <= 2'b0;
    end else begin
      sync_lz_req  <= {sync_lz_req[0],  lz_req};
      sync_tok_ack <= {sync_tok_ack[0], tok_ack};
      sync_la_ack  <= {sync_la_ack[0],  la_ack};
    end
  end
  wire lz_req_s  = sync_lz_req[1];
  wire tok_ack_s = sync_tok_ack[1];
  wire la_ack_s  = sync_la_ack[1];

  // -- self-checking result registers --------------------------------------
  reg [31:0] p1_mismatch, p2_mismatch;
  reg        p1_fail_latched, p2_fail_latched;
  reg [AW-1:0] p1_fail_addr, p2_fail_addr;
  reg [DW-1:0] p1_fail_got, p1_fail_expect, p2_fail_got, p2_fail_expect;
  reg [DW-1:0] cap_val;

  reg [31:0] spd_cycles;
  reg        spd_counting;
  // `idx` is only AW=10 bits wide (0..1023) because that is all phases 1 and
  // 2 need to address N=64 locations -- SPD_N=2048 overflows it, so phase 3
  // counts its own iterations in a full-width counter instead of trying to
  // widen `idx` (and the address bus) just for a loop bound nothing else
  // needs.  `idx` itself is simply unused while phase==2; cur_addr already
  // forces the address to a fixed constant during phase 3.
  reg [31:0] spd_iter;

  // -- the hang detector: one shared counter, reset on entry to (or on
  // leaving) each wait state, checked inside that state's own branch below.
  localparam integer TIMEOUT_LIMIT = 24'd2_000_000; // ~20 ms at 100 MHz --
      // generous against an expected round trip of tens to low hundreds of
      // aclk cycles (DSETUP=8/DCO=12 delay-element budgets are a handful of
      // ns each), bounded so a genuine deadlock (AUDIT.md section 7's
      // `p_req = joined` failure mode) reports in well under a second of
      // wall time instead of hanging the xsdb poller forever.
  reg [23:0] tmo_cnt;
  localparam [1:0] TMO_NONE     = 2'd0,
                   TMO_WAIT_LZ  = 2'd1,
                   TMO_WAIT_TOK = 2'd2,
                   TMO_RTZ      = 2'd3;
  reg [1:0] timeout_code;
  reg       timeout_flag;

  localparam S_IDLE     = 3'd0,
             S_ASSERT   = 3'd1,
             S_WAIT_LZ  = 3'd2,
             S_WAIT_TOK = 3'd3,
             S_CHECK    = 3'd4,
             S_RTZ      = 3'd5,
             S_ADV      = 3'd6,
             S_DONE     = 3'd7;
  reg [2:0] st;

  wire busy = (st != S_IDLE) && (st != S_DONE);
  wire done = (st == S_DONE);
  wire overall_pass = done && !timeout_flag &&
                       (p1_mismatch == 32'd0) && (p2_mismatch == 32'd0);

  assign port_busy = busy;
  assign port_done = done;
  assign port_pass = overall_pass;

  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      st <= S_IDLE;
      {sa_req, sd_req, la_req, tok_req, lz_ack} <= 5'b0;
      spd_counting <= 1'b0;
    end else if (ctrl_rst) begin
      st <= S_IDLE;
      {sa_req, sd_req, la_req, tok_req, lz_ack} <= 5'b0;
      spd_counting <= 1'b0;
    end else begin
      if (spd_counting) spd_cycles <= spd_cycles + 1'b1;

      case (st)
        S_IDLE: begin
          phase <= 2'd0;
          idx   <= {AW{1'b0}};
          spd_iter <= 32'd0;
          p1_mismatch <= 32'd0;  p1_fail_latched <= 1'b0;
          p2_mismatch <= 32'd0;  p2_fail_latched <= 1'b0;
          timeout_flag <= 1'b0;  timeout_code <= TMO_NONE;
          tmo_cnt <= 24'd0;
          st <= S_ASSERT;
        end

        // -- offer address/payload and raise everything concurrently -- the
        // token chain is the only thing that orders the store before the
        // load, exactly as tb_bdc_memseq.v's `BDC_SEQ_TOKEN loop does.
        S_ASSERT: begin
          sa_req  <= 1'b1;
          sd_req  <= 1'b1;
          la_req  <= 1'b1;
          tok_req <= 1'b1;
          tmo_cnt <= 24'd0;
          st      <= S_WAIT_LZ;
        end

        S_WAIT_LZ: begin
          if (lz_req_s) begin
            cap_val <= lz_data;
            lz_ack  <= 1'b1;   // four-phase consumer: raise on req seen high
            tmo_cnt <= 24'd0;
            st      <= S_WAIT_TOK;
          end else if (tmo_cnt == TIMEOUT_LIMIT - 1) begin
            timeout_flag <= 1'b1;
            timeout_code <= TMO_WAIT_LZ;
            {sa_req, sd_req, la_req, tok_req} <= 4'b0;
            st <= S_DONE;
          end else begin
            tmo_cnt <= tmo_cnt + 1'b1;
          end
        end

        S_WAIT_TOK: begin
          if (tok_ack_s) begin
            sa_req  <= 1'b0;
            sd_req  <= 1'b0;
            la_req  <= 1'b0;
            tok_req <= 1'b0;
            tmo_cnt <= 24'd0;
            st      <= S_CHECK;
          end else if (tmo_cnt == TIMEOUT_LIMIT - 1) begin
            timeout_flag <= 1'b1;
            timeout_code <= TMO_WAIT_TOK;
            {sa_req, sd_req, la_req, tok_req} <= 4'b0;
            st <= S_DONE;
          end else begin
            tmo_cnt <= tmo_cnt + 1'b1;
          end
        end

        // -- the checker that can actually go red -----------------------
        S_CHECK: begin
          case (phase)
            2'd0: if (cap_val !== cur_payload) begin
              p1_mismatch <= p1_mismatch + 1'b1;
              if (!p1_fail_latched) begin
                p1_fail_latched <= 1'b1;
                p1_fail_addr    <= idx;
                p1_fail_got     <= cap_val;
                p1_fail_expect  <= cur_payload;
              end
            end
            2'd1: if (cap_val !== cur_payload) begin
              p2_mismatch <= p2_mismatch + 1'b1;
              if (!p2_fail_latched) begin
                p2_fail_latched <= 1'b1;
                p2_fail_addr    <= idx;
                p2_fail_got     <= cap_val;
                p2_fail_expect  <= cur_payload;
              end
            end
            default: ; // phase 3 (SPD) is timed only, not checked -- same as
                       // mem_port_ps.v's cost phase.
          endcase
          st <= S_RTZ;
        end

        // -- return to zero: drop lz_ack once its req has fallen, then wait
        // for the requests we already dropped to be acknowledged low too.
        S_RTZ: begin
          if (!lz_req_s) lz_ack <= 1'b0;
          if (!tok_ack_s && !la_ack_s) begin
            tmo_cnt <= 24'd0;
            st      <= S_ADV;
          end else if (tmo_cnt == TIMEOUT_LIMIT - 1) begin
            timeout_flag <= 1'b1;
            timeout_code <= TMO_RTZ;
            st <= S_DONE;
          end else begin
            tmo_cnt <= tmo_cnt + 1'b1;
          end
        end

        // Each branch below sets `st` itself, explicitly, rather than
        // falling through to one shared assignment after the case: `st` is
        // a nonblocking-assigned reg, so a trailing `if (st != S_DONE) st <=
        // S_ASSERT` after this case would read st's OLD value (still
        // S_ADV, never S_DONE) and unconditionally overwrite whatever the
        // phase==2 branch just scheduled -- the phase 3 termination would
        // never actually take effect and the FSM would loop forever after
        // SPD_N, silently, with no timeout to catch it since every wait
        // state along the way keeps succeeding normally.  Caught by
        // rereading this file before calling it done, not by the lint.
        S_ADV: begin
          case (phase)
            2'd0: if (idx == N - 1) begin
              idx <= {AW{1'b0}};  phase <= 2'd1;  st <= S_ASSERT;
            end else begin
              idx <= idx + 1'b1;  st <= S_ASSERT;
            end
            2'd1: if (idx == N - 1) begin
              idx <= {AW{1'b0}};  phase <= 2'd2;
              spd_counting <= 1'b1;  spd_cycles <= 32'd0;  spd_iter <= 32'd0;
              st <= S_ASSERT;
            end else begin
              idx <= idx + 1'b1;  st <= S_ASSERT;
            end
            2'd2: if (spd_iter == SPD_N - 1) begin
              spd_counting <= 1'b0;
              st <= S_DONE;
            end else begin
              spd_iter <= spd_iter + 1'b1;  st <= S_ASSERT;
            end
            default: st <= S_IDLE;
          endcase
        end

        S_DONE: /* hold until ctrl_rst pulses */ ;
        default: st <= S_IDLE;
      endcase
    end
  end

  reg [31:0] rdata_r;
  always @(*) begin
    case (axi_araddr)
      5'h0: rdata_r = {31'b0, ctrl_rst};
      5'h1: rdata_r = {26'b0, phase, overall_pass, timeout_flag, done, busy};
      5'h2: rdata_r = p1_mismatch;
      5'h3: rdata_r = p2_mismatch;
      5'h4: rdata_r = {30'b0, timeout_code};
      5'h5: rdata_r = spd_cycles;
      5'h6: rdata_r = SPD_N;
      5'h7: rdata_r = N;
      5'h8: rdata_r = {22'b0, p1_fail_addr};
      5'h9: rdata_r = p1_fail_got;
      5'ha: rdata_r = p1_fail_expect;
      5'hb: rdata_r = {22'b0, p2_fail_addr};
      5'hc: rdata_r = p2_fail_got;
      5'hd: rdata_r = p2_fail_expect;
      5'he: rdata_r = {17'b0, phase, st, idx}; // idx reads 0 during phase 3;
                                                // see SPD_ITER (0xf) instead
      5'hf: rdata_r = spd_iter;
      default: rdata_r = 32'b0;
    endcase
  end
  assign rdata = rdata_r;

endmodule
