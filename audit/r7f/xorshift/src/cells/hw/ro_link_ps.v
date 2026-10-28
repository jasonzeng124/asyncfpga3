// ---------------------------------------------------------------------------
// ro_link_ps.v -- what does ONE handshake stage actually cost?
//
// THE QUESTION.  On silicon every kernel costs a startlingly flat amount per
// loop iteration -- xorshift 104 ns, collatz 166, collatz64 190 -- almost
// independently of what the loop computes, and collatz64 pays only 15% more
// than collatz for twice the datapath width.  Dividing by the storage stages
// on each loop's ring gives 14.9 / 18.4 / 21.1 ns per stage.
//
// That is an AVERAGE, and an average cannot settle the question.  Two models
// predict it equally well:
//
//   (a) a stage costs only its FORWARD latency -- request through the logic
//       and the matched delay -- while the acknowledge and the return to zero
//       hide behind the token's progress through the following stages, which
//       is what a pipeline is supposed to do.  From this project's own routed
//       numbers (median wire 720 ps, logic 124 ps, delay element 274 ps) that
//       is roughly 2 ns for a stage with one LUT level.
//
//   (b) the ring pays all FOUR phases serially at every stage, because the
//       return to zero never overlaps forward progress at all.
//
// Those differ by about 4x, and 104/26 is about 4, so one average cannot tell
// them apart.  A SLOPE can, and that is the whole design of this rig.
//
// THE MEASUREMENT.  Five rings of bd_link stages, five different lengths, each
// holding exactly one token.  A ring with one token circulates forever and is
// its own oscillator, so no time reference finer than the interval being
// measured is needed -- only a counter and a window.  Same instrument as
// ro_top.v, which measured bd_delay chains this way and agreed with the routed
// SDF to 0.975.
//
//   the SLOPE is nanoseconds per STAGE, free of any fixed per-ring overhead;
//   the INTERCEPT is that overhead -- the wrap route, and whatever the ring
//   pays once per lap rather than once per stage.
//
// One ring cannot separate those two and would answer the wrong question.
// That is ro_top.v's argument for five lengths and it is why there are five
// here.
//
// WHY THE PS AND NOT ro_top's RAW JTAG.  ro_top had no clock at all, so its
// window was the host's wall clock over several seconds.  Here FCLK0 gives a
// 100 MHz reference on the die, so the window is counted in HARDWARE: the host
// writes a cycle count, the rig runs for exactly that many aclk cycles and
// stops itself.  The measurement no longer depends on how well the host's
// clock is known, or on JTAG latency, and the whole run reports itself.
//
// WHY PURE LINKS AND NO DATAPATH.  A kernel stage costs protocol PLUS a
// matched delay sized for that stage's logic, and in a kernel the two cannot
// be separated -- especially not while a constant shift still synthesises to
// a full 32-bit barrel shifter.  Here there is no logic at all: nothing sits
// between one controller and the next but wire and RO_DELAY.  Sweeping
// RO_DELAY and extrapolating to zero separates the protocol from the delay
// line, which is the split the kernel numbers cannot give.
//
// DELAY=0 IS NOT A VALID POINT ON THIS FABRIC, and the rig found that out
// rather than assuming it.  Built with RO_DELAY=0 the held census reads
// exactly 1.00 on every ring -- the reset makes one token, cleanly, every
// time -- and the running census then reads 1.4, 1.9, 3.6, 5.6, 9.6 against
// lengths 3, 4, 6, 8, 12.  Tokens are being CREATED in flight, and a Muller
// ring conserves them, so something is not behaving like a Muller ring.
//
// The mechanism is the C-element's implementation.  bd_c2n is one LUT6 whose
// own output comes back on I2, and a LUT with feedback is hazard-free only
// while its inputs do not switch too close together: the state it feeds back
// is the state from before the glitch.  Every stage here is one LUT from the
// next, so with no matched line the two inputs of every C-element arrive
// within a few hundred picoseconds of each other, and the feedback latches
// the glitch as a new token.  That case does not arise in a kernel, where
// req_out always carries a matched delay sized for the stage's logic, and
// that delay is exactly what separates the arrivals.
//
// So RO_DELAY is a swept axis, not a constant, and the census is the gate on
// each point: a ring whose census is not flat is not a Muller ring that day
// and its lap time means nothing.
//
// ONE TOKEN, AND HOW WE KNOW IT.  A bd_link comes up EMPTY -- its controller
// is bd_c2n, which resets to 0 -- and a ring of empty stages never moves.
// Exactly one stage has to come up HOLDING, and rtl/bd_ce.v already ships that
// cell: bd_c2n_set, "comes up at 1", the same primitive bd_arb uses for its
// held state.  Stage 0 of each ring is hand-wired below from bd_c2n_set plus
// bd_latch, which are the two primitives bd_link itself is built from.  rtl/
// is frozen and is not touched.
//
// A ring that came up with TWO tokens would run at twice the rate and would
// look exactly like a fast ring -- the one failure that could be mistaken for
// a result.  Two independent checks cover it, and it is worth being precise
// about which one does the work.
//
// The census samples every controller node into the aclk domain and reports
// the population count per ring.  It is a real measurement and it catches a
// DEAD ring immediately, but it does NOT measure token count, and an earlier
// version of this file claimed it did.  The reasoning was that a Muller stage
// holds half a token, so one token is a moving pair of high nodes whose count
// is independent of ring length.  The board disagrees: occupancy climbs with
// length while the LOW time per node stays near constant.  That is still one
// token -- the rise wave outruns the fall wave that chases it, so the high
// region grows until the low region is as narrow as the gates allow, and what
// circulates is a narrow LOW pulse.  Occupancy is a function of ring length
// and carries no information about how many tokens there are.
//
// What does carry it is the fit.  A ring holding T tokens ticks its counter T
// times per lap, so it sits at 1/T of the line through the other lengths --
// for T=2 that is a 50% residual, an order of magnitude outside routing
// scatter.  The token gate is therefore the per-point residual, and the
// census stays in as a liveness check and as the source of the low-pulse
// width, which is a genuinely useful number in its own right.
//
// THE COUNTER HAS TO CLOSE, AND THAT IS NOT FREE.  ro_top.v floored its rings
// at 7 links precisely so the fastest one stayed well under the rate a 32-bit
// counter closes at on this part.  This rig cannot take that way out: three
// stages is the whole point of the short end.  A 3-stage ring with no logic
// and no matched delay is six LUT-plus-wire hops per lap, which on this
// project's own routed medians is around 5 ns -- roughly 200 MHz, and a
// 32-bit binary counter on a -1 xc7z010 through openxc7 may well not close
// there.  A counter that does not close does not fail loudly; it undercounts,
// and an undercount at the short end would bend the fit in exactly the
// direction that makes the protocol look cheap.
//
// So the closure is GATED, not assumed.  nextpnr derives a clock from every
// BUFG output and prints its maximum frequency, and this rig measures each
// ring's actual lap rate.  A point counts only if
//
//     measured lap rate  <  nextpnr's Fmax for that ring's counter clock
//
// and any ring that fails is dropped and SAID to be dropped, not quietly
// kept.  The check costs nothing -- both numbers already exist -- and it is
// the difference between a slope and a slope-shaped artifact.
//
// ---------------------------------------------------------------------------
// REGISTERS (byte offset = word index * 4)
//
//   0x00  CTRL     [0] rst   -- holds every ring in reset and clears counters
//                  [1] start -- begin a window (write 1; self-clearing)
//                  [2] hold  -- keep stage 1 of every ring pinned low, so
//                               the ring stays frozen in the state reset
//                               built.  Census must read exactly 1.00 here.
//   0x04  WINDOW   window length in aclk cycles (100 MHz)
//   0x08  STATUS   [0] busy  [1] done  [2] any counter overflowed
//   0x0C  LENGTHS  {12'b0, n4,n3,n2,n1,n0} -- 4 bits each, so the host never
//                  hardcodes what the bitstream was actually built with
//   0x10  CENSUS   {12'b0, pc4,pc3,pc2,pc1,pc0} -- live occupancy, 4 bits
//                  each.  Read it MANY times while running and average; one
//                  reading is noise, the mean is the measurement.
//   0x20..0x30     COUNT0..COUNT4 -- laps.  Reading one while busy returns
//                  0xFFFFFFFF, a value a counter cannot otherwise hold at the
//                  instant it is read, so forgetting to stop is obvious
//                  rather than plausible.
//   0x40  SIG      0x5A5A1234, bring-up probe, answers whatever else is on
//   0x44  DELAY    RO_DELAY this bitstream was built with, so the sweep
//                  never has to trust its own filename
//   0x48  WIDTH    RO_WIDTH, likewise
// ---------------------------------------------------------------------------
// RO_DELAY -- bd_delay elements on every stage's outgoing request.  Set with
// BD_DEFINES=-DRO_DELAY=n; hw/run_ro_link.sh sweeps it.  See the DELAY=0
// note in the header.
`ifndef RO_DELAY
 `define RO_DELAY 0
`endif

// RO_WIDTH -- payload bits per stage.  8 is the rig's own default; the
// kernels carry 32, and bd_latch is W/2 LUTs, so a kernel stage's latch is
// four times this one's.  Swept to find out whether that is where the
// unexplained ~5 ns per kernel stage lives.  BD_DEFINES=-DRO_WIDTH=32.
`ifndef RO_WIDTH
 `define RO_WIDTH 8
`endif

module ro_link_ps (
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

  ro_link_bridge bridge_i (
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

module ro_link_bridge (
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


  // ---- the rings ---------------------------------------------------------
  localparam integer K    = 5;      // rings
  localparam integer MAXN = 12;     // longest ring, for array sizing
  localparam integer DW   = `RO_WIDTH;  // payload width, same on every ring

  // Ring lengths in bd_link stages -- see RN below.  Floored at 3 because
  // below three storage stages a four-phase ring does not circulate at all
  // (bdc/emit.py's RING_MIN_STAGES), and spread to 12 so the fit has a lever
  // arm.  They also bracket the kernels: xorshift's ring is 7 stages and
  // collatz's is 9, so the interesting range is interpolated, not
  // extrapolated.

  // ---- the run window, counted in hardware -------------------------------
  reg [31:0] window;
  reg [31:0] win_left;
  reg        busy, done;

  wire start_w = do_write && (axi_awaddr == 5'h0) && wdata[1];

  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      window   <= 32'd10_000_000;   // 100 ms at 100 MHz
      win_left <= 32'b0;
      busy     <= 1'b0;
      done     <= 1'b0;
    end else begin
      if (do_write && axi_awaddr == 5'h1) window <= wdata;
      if (ctrl_rst) begin
        busy <= 1'b0;
        done <= 1'b0;
      end else if (start_w && !busy) begin
        busy     <= 1'b1;
        done     <= 1'b0;
        win_left <= window;
      end else if (busy) begin
        if (win_left == 32'b0) begin
          busy <= 1'b0;
          done <= 1'b1;
        end else begin
          win_left <= win_left - 32'b1;
        end
      end
    end
  end

  // ---- releasing the reset without filling the ring ----------------------
  // The first version of this rig released one reset net to every controller
  // at once and every ring came up FULL -- the census read 1.5, 2.0, 3.8,
  // 5.4, 9.3 high nodes against lengths 3, 4, 6, 8, 12, which is N/2, which
  // is maximum occupancy.  Worth understanding, because the mechanism is not
  // specific to this rig.
  //
  // Stage 0 is held HIGH by reset, and a controller held high is an infinite
  // source of tokens: its successor sees req and goes high, its successor's
  // successor follows, and stage 0 cannot fall in response because reset is
  // still pinning it.  A single reset net has picoseconds of skew across a
  // die, a stage is picoseconds deep, and the ring fills in the gap.  Nothing
  // about that is a race the router could have won.
  //
  // The fix is to freeze the ring somewhere it cannot leak from, and release
  // that last.  With stage 1 pinned LOW, no stage in the ring can rise at
  // all: stages 2..N-1 each need their predecessor high and the chain is cut
  // at 1, and stage 0 needs stage N-1 high.  Stage 0 sits at 1 holding, every
  // other stage at 0, and the whole thing is genuinely quiescent -- so the
  // skew on ring_rst stops mattering, because there is no longer anything it
  // could race.  Two aclk cycles later gate_rst releases stage 1, and exactly
  // one token starts moving.
  //
  // The census is what tells us this worked, and it is the reason the census
  // is in the design rather than in a comment.
  reg [2:0] rst_seq;
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn)        rst_seq <= 3'b111;
    else if (ctrl_rst)   rst_seq <= 3'b111;
    else                 rst_seq <= {rst_seq[1:0], 1'b0};
  end

  // CTRL[2] holds the gate shut indefinitely, and it is there to settle one
  // question the census alone cannot: are the extra tokens created BY the
  // reset release, or acquired later while the ring is running?  With the
  // gate held, the ring is frozen in the state the reset built -- stage 0
  // high, every other stage low -- and the census must read exactly 1.00 on
  // every ring.  Release the gate and read it again.  A census that is 1.00
  // held and 9.65 running says the reset was clean and the ring gains tokens
  // in flight; a census already wrong while held says the reset never
  // produced one token in the first place.  Those are different defects with
  // different fixes and guessing between them is how a rig ends up measuring
  // the wrong thing confidently.
  reg ctrl_hold;
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) ctrl_hold <= 1'b0;
    else if (do_write && axi_awaddr == 5'h0) ctrl_hold <= wdata[2];
  end

  wire ring_rst = rst_seq[0];               // stages 0 and 2..N-1: first
  wire gate_rst = rst_seq[2] | ctrl_hold;   // stage 1 only: two cycles later
  wire run      = busy;

  wire [K*32-1:0] cnt_flat;
  wire [K-1:0]    ovf;
  wire [K*4-1:0]  pc_flat;
  wire [K*4-1:0]  len_flat;

  genvar i, s;
  generate for (i = 0; i < K; i = i + 1) begin : ring
    // 3, 4, 6, 8, 12.  Written as a constant expression on the genvar so
    // there is no constant-function call for the synthesiser to fold.
    localparam integer N = (i == 0) ? 3 : (i == 1) ? 4 :
                           (i == 2) ? 6 : (i == 3) ? 8 : 12;

    wire [MAXN-1:0]    cn;   // each stage's controller node
    wire [MAXN-1:0]    rq;   // each stage's req_out
    wire [MAXN*DW-1:0] dq;   // each stage's data_out

    for (s = 0; s < N; s = s + 1) begin : st
      // Predecessor's request and successor's acknowledge, closed round.  A
      // bd_link's ack_in IS its controller node -- see bd_link.v -- so the
      // successor's acknowledge is cn[s+1].
      wire          req_in  = rq[(s == 0)     ? (N-1) : (s-1)];
      wire          ack_out = cn[(s == N-1)   ? 0     : (s+1)];
      wire [DW-1:0] prev_d  = dq[((s == 0) ? (N-1) : (s-1))*DW +: DW];
      // Invert one payload bit at the wrap so the latches actually toggle
      // every lap.  A ring whose data never changes still oscillates, but it
      // would not be exercising the datapath latches a real stage carries.
      wire [DW-1:0] data_in = (s == 0) ? {prev_d[DW-1:1], ~prev_d[0]} : prev_d;

      if (s == 0) begin : head
        // The one stage that comes up HOLDING -- this is the token.  Built
        // from the same two primitives bd_link is, because the only
        // difference is which C-element resets high, and rtl/ is frozen.
        bd_c2n_set ctl (.a(req_in), .b(ack_out), .rst(ring_rst), .q(cn[0]));
        bd_latch #(.W(DW)) lat (.d(data_in), .en(cn[0]), .q(dq[0 +: DW]));
        // Same matched line as every other stage, so stage 0 is not
        // quietly the one fast stage in the ring.
        bd_delay #(.N(`RO_DELAY)) rdly0 (.a(cn[0]), .z(rq[0]));
      end else begin : body
        // Stage 1 is the gate -- see the rst_seq comment above.  It is an
        // ordinary bd_link in every other respect; only which reset it
        // listens to differs.
        bd_link #(.W(DW), .DELAY(`RO_DELAY)) u (
          .rst((s == 1) ? gate_rst : ring_rst),
          .req_in(req_in), .ack_in(cn[s]), .data_in(data_in),
          .req_out(rq[s]), .ack_out(ack_out), .data_out(dq[s*DW +: DW]));
      end
    end

    // Unused upper slots, so nothing floats into the census.
    for (s = N; s < MAXN; s = s + 1) begin : unused
      assign cn[s] = 1'b0;
      assign rq[s] = 1'b0;
      assign dq[s*DW +: DW] = {DW{1'b0}};
    end

    // ---- lap counter -----------------------------------------------------
    // cn[0] rises when the token reaches stage 0 and falls when it leaves, so
    // one rising edge is exactly one lap.
    wire ck;
    BUFG bg (.I(cn[0]), .O(ck));

    reg [2:0]  srun = 3'b000;
    reg [1:0]  sclr = 2'b00;
    reg [31:0] c    = 32'h0;
    reg        o    = 1'b0;

    // run and rst cross INTO the ring's own domain through two stages, so a
    // counter never sees a half-changed enable.  The crossing costs a couple
    // of ring periods at each end of the window and they cancel.
    //
    // The window CLEARS THE COUNTER AS IT OPENS, on the synchronised rising
    // edge of run, and that is not a convenience.  The obvious alternative --
    // clear the counters from ctrl_rst between runs -- cannot work here, and
    // the reason is worth writing down: ctrl_rst is also the RING reset, and
    // a ring in reset has its one controller node parked high and produces no
    // further edges at all.  The clear would be waiting on a clock that the
    // clear itself just stopped.  Clearing on run-rise instead keeps every
    // window independent without ever stopping the thing that clocks it, so
    // back-to-back windows are directly comparable -- which is exactly what
    // the doubling check in xsdb_ro_link.tcl needs to mean anything.
    always @(posedge ck) begin
      srun <= {srun[1:0], run};
      sclr <= {sclr[0], ring_rst};
      if (sclr[1]) begin
        c <= 32'h0;
        o <= 1'b0;
      end else if (srun[2:1] == 2'b01) begin
        c <= 32'h1;               // window just opened; this edge is lap 1
        o <= 1'b0;
      end else if (srun[1]) begin
        c <= c + 32'h1;
        if (&c) o <= 1'b1;        // sticky: the window was too long
      end
    end

    assign cnt_flat[i*32 +: 32] = c;
    assign ovf[i] = o;
    assign len_flat[i*4 +: 4] = N;

    // ---- token census ----------------------------------------------------
    // A deliberate asynchronous sample of signals with no relationship to the
    // sampling clock.  One reading is meaningless; the MEAN over many reads
    // is the measurement.  It answers the one question a plausible-looking
    // counter cannot: how many tokens were actually in the ring.
    //
    // What to expect.  A Muller stage's occupancy is half a token, so a
    // single token in flight is a moving pair of adjacent high nodes and the
    // popcount breathes between 1 and 2 -- mean somewhere near 1.5, and,
    // crucially, INDEPENDENT OF RING LENGTH.  That independence is the test.
    // Two tokens read roughly double at every length; a ring that never
    // started reads 0.  So the discriminator is not "is it 1", it is "is it
    // flat across the five lengths".
    reg [MAXN-1:0] cs0 = {MAXN{1'b0}};
    reg [MAXN-1:0] cs1 = {MAXN{1'b0}};
    always @(posedge aclk) begin
      cs0 <= cn;
      cs1 <= cs0;
    end

    integer b;
    reg [3:0] pc;
    always @* begin
      pc = 4'd0;
      for (b = 0; b < MAXN; b = b + 1)
        pc = pc + {3'b0, cs1[b]};
    end
    assign pc_flat[i*4 +: 4] = pc;

  end endgenerate

  assign port_busy = busy;
  assign port_done = done;

  // ---- readback ----------------------------------------------------------
  reg [31:0] rdata_r;
  always @(*) begin
    case (axi_araddr)
      5'h0:  rdata_r = {29'b0, ctrl_hold, busy, ctrl_rst};
      5'h1:  rdata_r = window;
      5'h2:  rdata_r = {29'b0, |ovf, done, busy};
      5'h3:  rdata_r = {12'b0, len_flat};
      5'h4:  rdata_r = {12'b0, pc_flat};
      5'h8:  rdata_r = cnt_flat[ 31:  0];
      5'h9:  rdata_r = cnt_flat[ 63: 32];
      5'ha:  rdata_r = cnt_flat[ 95: 64];
      5'hb:  rdata_r = cnt_flat[127: 96];
      5'hc:  rdata_r = cnt_flat[159:128];
      5'h10: rdata_r = 32'h5A5A_1234;
      5'h11: rdata_r = `RO_DELAY;
      5'h12: rdata_r = `RO_WIDTH;
      default: rdata_r = 32'b0;
    endcase
  end

  // Poison a counter read taken while the window is still open, so a host that
  // forgets to stop gets an obvious value rather than a plausible wrong one.
  // The census is exempt: it is precisely what you read WHILE it runs.
  wire is_cnt = (axi_araddr >= 5'h8) && (axi_araddr <= 5'hc);
  assign rdata = (is_cnt && busy) ? 32'hFFFF_FFFF : rdata_r;

endmodule
