// ---------------------------------------------------------------------------
// arb_mtbf.v -- verify/MTBF.md, on silicon.
//
// bd_arbcell (rtl/bd_arb.v) is the highest-risk cell in the library: its
// decision element is one LUT6 feedback loop, and a LUT is a digital mux tree
// that will propagate whatever voltage its input reaches, including a
// metastable one, straight to both grant outputs.  That is the one failure an
// analog mutex filter exists to prevent and a LUT fabric cannot build one.
// What is buildable is resolution time -- delay stages between the decision
// and its consumers, which buy MTBF exponentially without a filter.  The
// question is "what is the failure rate at depth N", and that is measurable
// only on hardware.  Nothing in tb_arb discharges the obligation: a Verilog
// LUT model resolves to 0 or 1 in zero time and can never produce the
// condition under test.
//
// THE CHANNELS.  Six independent bd_c2n_set decision elements share one pair
// of free-running ring oscillators (r1, r2) as stimulus.  Sharing the state
// node itself was considered and rejected: fanning a regenerative feedback
// net out to six loads changes its own loop gain and hence the very time
// constant under test.  Sharing the STIMULUS is fine -- r1/r2 are ordinary
// digital nets once past their own ring, ordinary fanout does not perturb an
// oscillator that isn't the thing being measured, and because the two rings
// are not frequency-locked their relative phase drifts continuously, so every
// channel sweeps the full offset window over a long run rather than sampling
// one fixed point in it.  Each channel's q feeds its OWN grant decoder
// through a bd_delay chain of a different length (0, 1, 2, 4, 8, 16 links) --
// the same fractured LUT6_2 bd_arbcell uses, reading the delayed copy instead
// of q directly.  Depth 0 is bd_delay's N=0 bypass, so that channel is
// bit-for-bit the library cell.
//
// THE DETECTOR HAS AN UNMEASURED DEAF ZONE, AND THIS DESIGN MEASURES IT
// INSTEAD OF TRUSTING IT.  anomaly = g1 & g2 is a glitch, and the sticky latch
// that catches it is a routed LUT2 feedback loop, not an ideal comparator --
// its minimum capturable pulse is some real number of picoseconds, not zero.
// A metastable excursion with a short resolution constant can be narrower
// than that floor, in which case hours of all-zero anomaly bits would prove
// "no anomaly wider than the detector's floor", not "no anomaly".  That is
// the same shape of trap as a counter reading zero for two opposite reasons.
// So six more channels (th[0..5]) generate a clean digital pulse of known
// width -- ring3 XOR bd_delay(N)(ring3), widths 1,2,3,4,6,8 links -- and feed
// it into the IDENTICAL sticky construction the anomaly channels use.  The
// smallest width that reliably trips its latch is the detector's floor,
// measured on this die in this bitstream, and it is what calibrates every
// all-zero anomaly result below it.
//
// NO CLEAR, ANYWHERE.  An earlier design (ro_top) had a clear bit and it
// nearly cost a measurement: a background hw_server chain poll can shift a
// stray word into this design's control register between scans, and a random
// bit landing on "clear" silently erases the one thing this experiment is
// waiting hours to see.  The fix there was `jtag lock`; the fix here is
// removing the class of bug -- these sticky bits latch once and hold for the
// life of the bitstream.  A monotonic first-occurrence bit is also the right
// semantics for this experiment: the interesting fact is WHETHER and roughly
// WHEN a channel first fires, not how many times, and if a fresh window is
// ever wanted the whole bitstream can be reloaded.  jtag lock is still used
// around every scan sequence, because an address bit flipping mid-experiment
// is still a nuisance even though nothing can be erased by accident anymore.
//
// EXPOSURE IS A RATE TIMES A WALL CLOCK, NOT AN ON-CHIP TOTAL.  r1 and r2
// free-run continuously regardless of anything the host does; what needs
// measuring is their edge rate, and that only takes an 8-second window, the
// same technique ro_top uses for ring period.  A 32-bit counter run
// continuously for hours would wrap every couple of minutes at these rates
// and answer nothing; run briefly, gated, read while stopped (the same
// CDC discipline ro_top documents: stop synchronised into the ring's own
// domain, then read from the TCK domain only once settled), the delta over
// one short window gives edges/second, and total exposure between two polls,
// possibly hours apart, is that rate times the host's wall clock.  The same
// short window is also the frequency-lock check MTBF.md's stimulus section
// implies but does not spell out: if r1's and r2's measured periods land on
// a suspiciously clean ratio, the rings may have injection-locked and parked
// at a fixed relative phase, which is exactly the "sits in a safe part of the
// window for hours and proves nothing" failure the whole two-oscillator
// design exists to avoid. arb_mtbf_measure.py checks the ratio every window.
//
// PLACEMENT.  MTBF.md requires both grants of a channel in ONE fractured
// site, because two separate LUTs have identical intrinsic delay but
// different, build-dependent routing, and an asymmetry that moves between
// builds makes a measured MTBF worthless the moment anything is rebuilt.
// hw/build_hw.sh does not carry over flow.sh's fracture check (nothing in
// ro_top is fractured), so this design's grant LUT6_2 instances are checked
// separately and explicitly by hw/check_fracture.py, against a recorded
// baseline, before any hours are spent.
//
// WHAT THIS DOES NOT TEST.  bd_arbcell alone, not bd_arbiter's handover
// protocol -- there is no A0/ack here, no HOLD_ON_ACK question, just the
// decision element and whether it can ever hand a live value to both grants
// at once.  And the two stimulus rings are unloaded, same caveat as ro_top:
// this is the easy case for the rings, though not for the decision element,
// which is under genuine two-sided contention the whole time it runs.
// ---------------------------------------------------------------------------

`default_nettype none

module arb_mtbf (output wire led_red, output wire led_green);

    localparam integer NCH = 6;     // anomaly-depth channels
    localparam integer NTH = 6;     // detector-threshold probe channels
    localparam integer W   = 48;    // DR width, same layout as ro_top
    localparam [7:0]   TAG = 8'h55; // distinct from ro_top's 0xA5, strictly alternating

    // Ring lengths for the two stimulus oscillators and the pulse generator.
    // Chosen prime and well apart from small integer ratios so the rings do
    // not sit near a natural injection-lock point; the calibration window
    // checks this empirically rather than trusting the choice.
    localparam integer RLEN0 = 17;   // r1
    localparam integer RLEN1 = 23;   // r2
    localparam integer RLEN2 = 13;   // ring3, threshold-probe source, uncounted

    function integer depth_of(input integer i);
        case (i)
            0: depth_of = 0;
            1: depth_of = 1;
            2: depth_of = 2;
            3: depth_of = 4;
            4: depth_of = 8;
            default: depth_of = 16;
        endcase
    endfunction

    function integer width_of(input integer i);
        case (i)
            0: width_of = 1;
            1: width_of = 2;
            2: width_of = 3;
            3: width_of = 4;
            4: width_of = 6;
            default: width_of = 8;
        endcase
    endfunction

    // ---- BSCANE2 (USER1) ---------------------------------------------------
    wire bs_capture, bs_shift, bs_update, bs_sel;
    wire bs_tck_raw, bs_tdi;
    wire sr_tdo;

    (* keep *) BSCANE2 #(.JTAG_CHAIN(1)) bscan_i (
        .CAPTURE (bs_capture),
        .DRCK    (),
        .RESET   (),
        .RUNTEST (),
        .SEL     (bs_sel),
        .SHIFT   (bs_shift),
        .TCK     (bs_tck_raw),
        .TDI     (bs_tdi),
        .TMS     (),
        .UPDATE  (bs_update),
        .TDO     (sr_tdo));

    wire tck;
    BUFG bufg_tck (.I(bs_tck_raw), .O(tck));

    // ---- hold register.  addr + run only -- no clear bit exists in this
    // design, see the header. ------------------------------------------------
    // Widened from 4 to 5 address bits when the Phase 2 window-latch negative
    // control (winctrl below) needed a 17th mux address and all 16 of the
    // old 4-bit space were already spoken for.
    reg  [5:0] hold = 6'b00_0000;
    wire [4:0] hold_addr = hold[4:0];
    wire       hold_run  = hold[5];

    // ---- the two counted stimulus rings (r1 = stim[0], r2 = stim[1]) -------
    wire [1:0]  stim_raw;
    wire [63:0] stim_cnt_flat;
    wire [1:0]  stim_ovf;

    genvar si;
    generate for (si = 0; si < 2; si = si + 1) begin : stim
        wire chain_z, fb;
        bd_delay #(.N(si == 0 ? RLEN0 : RLEN1)) d (.a(fb), .z(chain_z));
        (* keep *) LUT1 #(.INIT(2'h1)) inv (.I0(chain_z), .O(fb));

        wire ck;
        BUFG bg (.I(fb), .O(ck));

        reg [1:0]  srun = 2'b00;
        reg [31:0] c    = 32'h0;
        reg        o    = 1'b0;

        wire        c_ce = srun[1];
        wire [31:0] c_d  = c + 32'h1;
        wire        o_ce = srun[1] && (&c);
        always @(posedge ck) begin
            srun <= {srun[0], hold_run};
            if (c_ce) c <= c_d;
            if (o_ce) o <= 1'b1;
        end

        assign stim_cnt_flat[si*32 +: 32] = c;
        assign stim_ovf[si] = o;
        assign stim_raw[si] = fb;
    end endgenerate

    wire r1 = stim_raw[0];
    wire r2 = stim_raw[1];

    // ---- ring3: threshold-probe source, free-running, uncounted ------------
    wire ring3_chain, ring3_fb;
    bd_delay #(.N(RLEN2)) dring3 (.a(ring3_fb), .z(ring3_chain));
    (* keep *) LUT1 #(.INIT(2'h1)) invring3 (.I0(ring3_chain), .O(ring3_fb));
    wire ring3 = ring3_fb;

    // ---- power-on reset for the sticky latches, and ONLY the sticky
    // latches.  A combinational feedback loop's power-on state is undefined
    // -- confirmed on this exact board: a control channel wired so nothing
    // can ever set it (see ctrl_sticky below) still read 1 after a fresh
    // --program, meaning the OR-self-latch raced itself high during
    // configuration, not on any real signal.  An ordinary flip-flop does not
    // have this problem -- its INIT is GSR-guaranteed, which every other
    // register in this design already relies on (hold, sr, the stimulus
    // counters all start at their literal INIT values, confirmed by the
    // bring-up constant reads).  So: hold every sticky latch at 0 with an
    // ordinary counter's guaranteed-0 start, until it has had time to settle,
    // then release it forever.  Clocked from a free-running ring rather than
    // tck so it resolves within nanoseconds of configuration and does not
    // wait on the host ever issuing a JTAG scan.  This is per-instance
    // per-channel scope, not a live/host-reachable clear -- it cannot be
    // re-armed, re-triggered, or hit by a stray hw_server poll the way the
    // ro_top clear bit could; see the header for why that class of bug is
    // still avoided everywhere else in this design.
    //
    // Unconditional, no CE -- an implicit "hold when not counting" (an
    // earlier draft: `if (!por_done) por_cnt <= por_cnt+1`) failed PnR on
    // every seed with "Failed to route ... to CEUSEDMUX_OUT", the same
    // wide-fanout-control-net shape documented on the liveness sampler
    // earlier in this file.  A shift register that unconditionally shifts
    // in a constant 1 every cycle reaches the same fixed point -- once
    // every bit is 1 it stays 1 forever -- without ever needing a second
    // control signal.
    //
    // Width history: a first cut used 4 bits (~13 ns at this ring's rate)
    // and passed the ctrl_sticky check (0 on 3/3 fresh loads) but produced a
    // deterministic, non-monotonic anomaly pattern -- depths 0/4/8/16 FIRED
    // on poll #1 of every one of 3 fresh loads, depths 1/2 clean, every
    // single time.  Real metastability capture does not reproduce bit-for-
    // bit identically across configurations; a fixed artifact does.  The
    // ctrl_sticky check only proves the LATCH's own self-race is closed --
    // it cannot see a race on a latch whose I0 is a live combinational net
    // (here, q_dly after a bd_delay chain) that is still settling from
    // configuration when por_done releases, and a longer delay chain has
    // more wavefront to settle, which fits the depth-dependent pattern
    // exactly.  24 bits (~1e7 cycles, several orders of magnitude past any
    // plausible chain-settling time) replaces the 4-bit register; if the
    // pattern persists it is not a POR-timing artifact and the cause is
    // elsewhere, if it clears the 4-bit window was the cause.
    reg [23:0] por_sr = 24'h0;
    always @(posedge stim[0].ck)
        por_sr <= {por_sr[22:0], 1'b1};
    wire por_done = por_sr[23];


    // ---- THE ARBITERS' OWN RESET -------------------------------------------
    // bd_c2n_set carries rst on a real pin for exactly one reason, stated in
    // rtl/bd_arb.v's header: q may come up either way -- it only decides who
    // wins the first tie -- but it MUST come up DEFINED, because an
    // intermediate q is precisely the failure this whole rig exists to
    // measure.
    //
    // Every instance in this file used to tie that pin to 1'b0, which is
    // the one value that guarantees nothing.  A bare cross-coupled loop with
    // no defined initial value resolves out of whatever the fabric settles
    // into at configuration, and that resolution looks exactly like the
    // both-grants condition the detectors catch.  The symptom was
    // unmistakable once there were enough instances to see its shape:
    // 138 of 192 population bits latched within TWO SECONDS of the bitstream
    // load, after which the rate fell by about four orders of magnitude.  A
    // real failure rate is flat -- the cell does not know when it was
    // configured -- so that burst was configuration settling, not
    // metastability.  (The same burst was present at NPOP=24, where it read
    // as a plausible "about half the instances fired" and was mistaken for
    // data.)
    //
    // arb_rst is asserted from configuration until por_sr has shifted all
    // the way up, so every decision node is held at a defined q and only
    // starts free-running once the detectors are also armed.
    wire arb_rst = ~por_done;

    // ---- Phase 2: windowed hit-rate counters, one per existing anomaly
    // channel.  This is IN ADDITION to that channel's permanent sticky bit,
    // not a replacement -- the sticky bit's whole value is that it only has
    // to catch a glitch once, ever, across trillions of ring edges; a
    // self-clearing window has a live coverage hole (an event that occurs
    // but does not survive to the sampling edge is invisible), and that
    // miss rate is itself per-instance since the clear strobe's routed skew
    // differs per site -- the same kind of confound already suspected in
    // the per-channel capture floor.  What this buys that the sticky bit
    // cannot: whether a channel is firing once and going quiet (consistent
    // with a load-time event) or firing repeatedly as exposure accumulates
    // (consistent with a real rate), without waiting hours for the sticky
    // bit's one permanent transition to maybe happen.
    //
    // WINBITS cycles of stim[0].ck (r1's own free-running ring -- already
    // used by por_sr, not a new clock domain) define one window.  A counter
    // increments once per window if the channel's anomaly_raw was ever high
    // during it, so what is actually measured is windows-with-a-hit, which
    // equals the true event rate only if at most one event lands per
    // window.  That assumption is checkable, not assumed: rebuild with a
    // different WINBITS and confirm the count scales -- halving the window
    // should halve the count if it holds.
    //
    // Unconditional everywhere -- win_cnt always increments, the per-channel
    // latch's clear is level-based (not a gated enable), the synchronizer
    // always shifts, and hitcnt always adds 0 or 1 -- the same idiom as
    // por_sr/rs0/rs1 in this file, specifically to avoid re-opening the
    // is_ceused/CEUSEDMUX_OUT control-set routing failures already hit
    // twice building this design. win_edge_d delays the clear by one cycle
    // relative to win_edge so the synchronizer's sampled value reflects the
    // window that just closed, not a same-edge race against its own clear.
    localparam integer WINBITS = 16;

    reg [WINBITS-1:0] win_cnt = {WINBITS{1'b0}};
    always @(posedge stim[0].ck)
        win_cnt <= win_cnt + 1'b1;
    wire win_edge = &win_cnt;

    reg win_edge_d = 1'b0;
    always @(posedge stim[0].ck)
        win_edge_d <= win_edge;

    // ---- ARM THE DETECTORS LONG AFTER RELEASING THE ARBITERS ---------------
    // por_done does two jobs that must NOT happen at the same instant:
    // it releases the arbiters' reset, and it arms the sticky latches.  Doing
    // both together means the latches are listening at the exact moment 192
    // decision loops start free-running, and the resulting startup transient
    // is latched as if it were a result.  Wiring the reset up (see arb_rst
    // below) fixed the undefined-power-up half of the problem and did NOT fix
    // this half: with the two tied together, 124 of 124 raw bits and 40 of 40
    // filtered bits still latched within two seconds of the bitstream load.
    //
    // The reset is provably quiet on its own -- with rst=1 the cell holds
    // q=1, and the grant decoder at q=1 gives g1=r1, g2=0, so both grants can
    // never be high while reset is asserted.  The burst is entirely in the
    // window AFTER release, which is why it needs a separate, much later
    // signal rather than a longer reset.
    //
    // arm_cnt is free-running and saturating: ~2^29 cycles of stim[0].ck at
    // roughly 122 MHz is about 4.4 seconds, four orders of magnitude past the
    // couple-of-seconds window the burst actually occupies, and it costs
    // nothing to be generous here -- a multi-day run does not care about its
    // first five seconds.  Unconditional increment, no clock-enable, same
    // discipline as every other counter in this file (see win_cnt).
    // Built as a free-running prescaler plus a shift register rather than one
    // wide counter: a 29-bit counter needs a CARRY4 chain, and nextpnr could
    // not route one here ("Failed to route arc 0 of net 'arm_cnt[1]'" -- a
    // carry-chain arc inside a single slice).  A prescaler feeding a shift
    // register has no carry chain at all, and the same power-on-safety
    // argument as por_sr applies: both start at 0, which the global set/reset
    // guarantees, and only ever shift 1s in.
    // Built on the window timer this design ALREADY has rather than a counter
    // of its own.  Two attempts at a dedicated counter (a 29-bit one, then a
    // 24-bit prescaler feeding a shift register) both failed to route on
    // every seed 0-9, always on the same kind of arc -- a carry-chain hop
    // inside one slice, e.g. "Failed to route arc 0 of net 'arm_pre[1]'".
    // With ~200 arbiters already placed, this part has no room left for
    // another wide CARRY4 chain, and that is a placement fact rather than
    // seed luck.
    //
    // win_cnt (declared below, WINBITS=16) already free-runs on this clock
    // and already produces win_edge once every 2^16 cycles, which is ~538 us.
    // Counting 32 of those in a shift register gives ~17 ms of quiet time
    // before anything is armed.  That is shorter than the ~4.4 s originally
    // intended, but still four orders of magnitude past the settling the
    // burst actually needs: the measured transient is over within
    // microseconds of release, and 17 ms is the first 1e-7 of a two-day run.
    // A shift register also carries no CARRY4 and starts at 0 under the
    // global set/reset, the same power-on-safety argument as por_sr.
    reg [31:0] arm_sr = 32'h0;
    always @(posedge stim[0].ck)
        if (win_edge_d && por_done)
            arm_sr <= {arm_sr[30:0], 1'b1};
    wire armed = arm_sr[31];

    // ---- the anomaly channels: one bd_c2n_set + delay tap + grant decoder +
    // sticky latch per depth.  ugrant's INIT is bd_arbcell's, unmodified. ----
    localparam [63:0] GRANT_INIT = 64'h0C0C_0C0C_A0A0_A0A0;

    wire [NCH-1:0] anomaly_raw, anomaly_sticky, q_dly_probe;
    wire [NCH-1:0] ch_hitcnt_ovf;
    wire [23:0]    ch_hitcnt [0:NCH-1];

    // ---- WIDTH DISCRIMINATOR -----------------------------------------------
    // The raw g1&g2 net carries a STRUCTURAL glitch that has nothing to do
    // with metastability, and the ladder above was mostly counting it.
    //
    // Both grants read the same q, so when q toggles one grant must fall
    // while the other rises.  On this fabric a LUT falls about 2.5x slower
    // than it rises (prjxray: O5 rise 55 / fall 152, O6 rise 56 / fall 124 --
    // see sim/bd_prims_sim.v), so the falling grant is still high when the
    // rising one arrives, and g1&g2 goes high for the difference.  In
    // simulation that is an 8-16 ps pulse on EVERY q toggle, on a bare
    // bd_arbcell, at depth 0, with no delay chain anywhere -- 89 pulses in
    // 2 us, each one arriving a fixed 52 ps after a q edge and 108 ps after
    // the r2 edge that caused it.  A fixed causal chain, not a rare
    // coincidence, which is exactly why every hardware counter saturates.
    //
    // (Feeding q through bd_delay -- what the depth ladder does -- makes this
    // WORSE, not better: the decoder then reads a stale q against live r1/r2,
    // so the two can disagree over a window that grows with depth.  That is
    // the monotonic rise with depth seen both in simulation and on hardware.
    // It is a second hazard on top of the first, not resolution time.)
    //
    // A real metastable excursion lasts on the order of the resolution time
    // constant, which is what MTBF.md is trying to measure and is far longer
    // than a fixed 16 ps arc delta.  So the two are separable BY WIDTH:
    //
    //     filtered = raw & bd_delay(WFILT)(raw)
    //
    // A pulse survives only if it is still high WFILT links later.  In
    // simulation this rejects 89/89 of the structural glitches while passing
    // every known-width probe pulse of 2 links or more -- the same th[]
    // ladder construction used to calibrate the detector floor, so the
    // passband is measured here, not assumed.
    //
    // The RAW sticky bits and counters are kept alongside, never replaced:
    // the interesting number is the DIFFERENCE between raw and filtered, and
    // a filtered channel reading zero while its raw twin saturates is the
    // signature that says the raw count was structural all along.
    // WHY 2 AND NOT 1.  One link was tried first and is NOT ENOUGH, and the
    // hardware said so unambiguously.  Two population instances were given
    // windowed rate counters (see the PER-INSTANCE RATE note below): pop[0]
    // recorded a FILTERED event in 18% of all windows -- 991 per second,
    // growing linearly, sustained over the whole run -- while pop[96], same
    // logic, same stimulus, its raw detector equally proven, recorded exactly
    // zero.  Nothing at ~1 kHz is metastability on a cell whose loop delay is
    // ~100 ps, and metastability does not switch off entirely at one site and
    // run continuously at another.  It is the structural overlap, and one
    // link was clearing it at most sites and not at others.
    //
    // This build's own routed SDF says why, and the difference is a packer
    // choice nothing in the RTL controls.  Both instances route q to both
    // grant halves symmetrically (150 ps each) and both route O5 and O6 into
    // the detector symmetrically (150 ps each), so there is no interconnect
    // skew.  What differs is WHICH PHYSICAL LUT PIN q lands on, and the
    // intrinsic pin-to-output arc is not the same for every pin: at pop[0] q
    // enters the O5 half on A5 and takes 116 ps, against 124 ps to O6, so the
    // rising grant arrives 8 ps EARLY and the overlap widens; at pop[96] q
    // enters on A1 and takes 150 ps, so the rising grant arrives 26 ps LATE
    // and the overlap narrows.  Against the ~97 ps intrinsic fall-minus-rise
    // asymmetry of a LUT on this fabric (prjxray: O5 rise 55 / fall 152, O6
    // rise 56 / fall 124) that is roughly 105 ps of overlap at pop[0] and
    // roughly 71 ps at pop[96] -- straddling this filter's measured passband
    // edge, which rejects <=80 ps and passes >=160 ps at one link.  A 34 ps
    // packer decision therefore decides whether an instance reads as
    // permanently broken or perfectly clean, which is not a property of the
    // cell and must not be counted as one.
    //
    // Two links moves the rejection band to ~160 ps, above the worst-case
    // structural overlap at any pin assignment, so the whole population lands
    // below the floor for the structural reason and anything that survives
    // needs a different explanation.  The cost is one LUT1 per channel and
    // the arbiters are untouched -- this filter sits entirely downstream of
    // the grant decoder, so every instance is still bit-for-bit the library
    // cell.  Note the price: 2 links also rejects any real excursion shorter
    // than ~160 ps, so this measures the rate of ambiguity outliving 160 ps,
    // not the rate of ambiguity.  That is the honest form of the question --
    // MTBF is always quoted against a resolution time -- but it must be
    // quoted WITH the number, and the threshold ladder measures the number on
    // this die rather than assuming it.
    localparam integer WFILT = 2;

    // Sticky bits only, deliberately: a filtered twin of the Phase 2 window
    // counters was built first and cost ~162 more flip-flops, which pushed
    // the tck domain past what this part's global clock routing will take --
    // every seed 0-5 failed to route tck, identically, which is congestion
    // and not seed luck.  The sticky pair answers the question on its own:
    // raw saturates in microseconds, so if filtered stays 0 for hours the
    // structural glitch was the whole raw signal.  Counters can come back
    // later by retiring the ones on channels that turn out not to matter.
    wire [NCH-1:0] anomaly_flt, flt_sticky;

    genvar ci;
    generate for (ci = 0; ci < NCH; ci = ci + 1) begin : ch
        wire q_raw, q_dly, g1c, g2c;

        bd_c2n_set ustate (.a(r1), .b(r2), .rst(arb_rst), .q(q_raw));
        bd_delay #(.N(depth_of(ci))) udly (.a(q_raw), .z(q_dly));

        (* keep *) LUT6_2 #(.INIT(GRANT_INIT)) ugrant (
            .I0(r1), .I1(r2), .I2(q_dly), .I3(1'b0), .I4(1'b0), .I5(1'b1),
            .O5(g1c), .O6(g2c));

        assign anomaly_raw[ci]  = g1c & g2c;
        assign q_dly_probe[ci]  = q_dly;

        // width discriminator -- see the WFILT note above.  Two LUTs: a
        // delay chain and an AND.  (* keep *) on the AND so no optimiser can
        // notice that a & delay(a) is "just a" and fold the whole thing away;
        // the delay is the entire point and it is invisible to logic
        // optimisation.
        wire anom_d;
        bd_delay #(.N(WFILT)) uwdly (.a(anomaly_raw[ci]), .z(anom_d));
        (* keep *) LUT2 #(.INIT(4'h8)) uwand (
            .I0(anomaly_raw[ci]), .I1(anom_d), .O(anomaly_flt[ci]));

        // filtered sticky bit, identical construction to the raw one below
        (* keep *) LUT3 #(.INIT(8'hE0)) ufltsticky (
            .I0(anomaly_flt[ci]), .I1(flt_sticky[ci]), .I2(armed),
            .O(flt_sticky[ci]));

        // sticky_next = (set | sticky(fb)) & por_done -- latches on the first
        // pulse after power-on reset releases, and never releases itself
        // again.  Nothing feeds a live clear; por_done only ever goes 0->1,
        // once, self-timed from configuration -- see its declaration above.
        (* keep *) LUT3 #(.INIT(8'hE0)) usticky (
            .I0(anomaly_raw[ci]), .I1(anomaly_sticky[ci]), .I2(armed),
            .O(anomaly_sticky[ci]));

        // Phase 2 windowed counter for this channel -- see the header note
        // by win_cnt's declaration above for why this exists alongside,
        // never instead of, the sticky bit above.
        //
        // win_hit = anomaly_raw | (win_hit(fb) & ~win_edge_d), gated by
        // por_done for the same power-on reason every other feedback loop
        // in this file is: O = (I0 | (I1 & ~I2)) & I3 with I0=anomaly_raw,
        // I1=win_hit(fb), I2=win_edge_d, I3=por_done.
        wire win_hit;
        (* keep *) LUT4 #(.INIT(16'hAE00)) uwinlatch (
            .I0(anomaly_raw[ci]), .I1(win_hit), .I2(win_edge_d),
            .I3(armed), .O(win_hit));

        // 2-FF synchronizer -- win_hit is fed by an async latch and must not
        // touch the counter directly, same CDC discipline as every other
        // async-to-sync crossing in this design.
        reg sync1 = 1'b0, sync2 = 1'b0;
        always @(posedge stim[0].ck) begin
            sync1 <= win_hit;
            sync2 <= sync1;
        end

        wire hit_this_window = win_edge_d & sync2;

        // 24 bits: at WINBITS=16 and stim[0].ck in the low hundreds of MHz,
        // this is on the order of an hour before wrapping, not minutes --
        // still sticky-OR'd into an overflow flag rather than trusted to
        // never happen, same as the r1/r2 exposure counters.  Unconditional
        // add of 0 or 1 every cycle, never a clock-enable.
        reg [23:0] hitcnt = 24'h0;
        reg        hitcnt_ovf = 1'b0;
        always @(posedge stim[0].ck) begin
            hitcnt     <= hitcnt + {23'h0, hit_this_window};
            hitcnt_ovf <= hitcnt_ovf | (hit_this_window & (&hitcnt));
        end

        assign ch_hitcnt[ci]     = hitcnt;
        assign ch_hitcnt_ovf[ci] = hitcnt_ovf;
    end endgenerate

    // ---- Phase 1: a population of NPOP independent depth-0 channels, all
    // sharing r1/r2 as stimulus like every other channel in this file, none
    // of them wired to each other.  This answers a different question than
    // depth does: are the six ch[] detectors even comparable to begin with?
    // Each is a physically distinct LUT3/LUT6_2 pair at its own routed
    // site, with its own unknown, unmatched capture floor -- ch[4] (depth 8)
    // firing while ch[2]/ch[3] (depths 2, 4 -- shallower, so an easier catch
    // under any real decay law) stay clean is impossible if the six
    // detectors are identical, but unremarkable if they are not.  NPOP
    // instances at the SAME depth removes depth as a variable entirely: if
    // the fired-fraction across this population is uniform, the ch[]
    // channels are comparable and depth is the right explanation for their
    // differences; if a handful of instances dominate while most stay
    // clean, the capture floor itself varies per site and that is the
    // confound to chase, not depth.
    //
    // Deliberately plain sticky latches, no counters -- this experiment is
    // about per-instance comparability, not rate, and the plain latch is
    // the cheapest, lowest-placement-risk primitive that answers it. Named
    // pop[N].ugrant so check_fracture.py's existing ch[N].ugrant pattern
    // (generalised to match either prefix) also verifies these land
    // fractured, one site each, same MTBF.md precondition as every other
    // grant decoder in this file.
    //
    // Read back raw, not aggregated -- every instance's own bit, packed
    // into one word, not a popcount or OR of the group.  An aggregate would
    // throw away exactly the information (which instances, and whether the
    // same ones repeat across polls) this experiment exists to see.
    // NPOP is sized to fill the part, not to answer the comparability
    // question above -- that one was already answered at NPOP=24.  What a
    // large population buys is EXPOSURE: the failure rate this rig exists to
    // measure is a rate per instance-second, so N instances running for T
    // hours is N*T instance-hours, and 192 of them is nearly 5800x the
    // exposure of the single unmodified cell that ch[0] provides.  At
    // 6 LUT sites each (decision node, fractured decoder, filter delay,
    // filter AND, and two sticky latches) 192 instances cost ~1150 sites on
    // top of the ~1000 already here, comfortably inside this part's 17600 --
    // the binding constraint is not area but the 32-address readback mux,
    // which has exactly 12 free addresses left: 6 raw words and 6 filtered
    // words at 32 instances per word.
    //
    // EVERY INSTANCE IS READ BACK RAW AND FILTERED, SEPARATELY.  The raw bit
    // is the positive control: it is known to fire within microseconds (the
    // structural g1/g2 overlap, see the WFILT note above), so a raw bit that
    // is somehow still clean after hours means that instance's detector is
    // dead and its filtered zero proves nothing.  Without the pair, a
    // filtered population reading all-zero cannot be distinguished from a
    // population that was never listening.
    localparam integer NPOP  = 192;
    localparam integer NPOPW = (NPOP + 31) / 32;   // readback words

    wire [NPOP-1:0] pop_raw, pop_sticky, pop_flt, pop_flt_sticky;

    genvar pi;
    generate for (pi = 0; pi < NPOP; pi = pi + 1) begin : pop
        wire q_raw, g1c, g2c;

        bd_c2n_set ustate (.a(r1), .b(r2), .rst(arb_rst), .q(q_raw));

        (* keep *) LUT6_2 #(.INIT(GRANT_INIT)) ugrant (
            .I0(r1), .I1(r2), .I2(q_raw), .I3(1'b0), .I4(1'b0), .I5(1'b1),
            .O5(g1c), .O6(g2c));

        assign pop_raw[pi] = g1c & g2c;

        (* keep *) LUT3 #(.INIT(8'hE0)) usticky (
            .I0(pop_raw[pi]), .I1(pop_sticky[pi]), .I2(armed),
            .O(pop_sticky[pi]));

        // width discriminator, identical to the one on the ch[] channels
        wire praw_d;
        bd_delay #(.N(WFILT)) upwdly (.a(pop_raw[pi]), .z(praw_d));
        (* keep *) LUT2 #(.INIT(4'h8)) upwand (
            .I0(pop_raw[pi]), .I1(praw_d), .O(pop_flt[pi]));

        (* keep *) LUT3 #(.INIT(8'hE0)) upfltsticky (
            .I0(pop_flt[pi]), .I1(pop_flt_sticky[pi]), .I2(armed),
            .O(pop_flt_sticky[pi]));
    end endgenerate

    // Zero-padded to a whole number of 32-bit readback words.
    wire [NPOPW*32-1:0] pop_sticky_pad     = {{(NPOPW*32 - NPOP){1'b0}},
                                              pop_sticky};
    wire [NPOPW*32-1:0] pop_flt_sticky_pad = {{(NPOPW*32 - NPOP){1'b0}},
                                              pop_flt_sticky};

    // ---- PER-INSTANCE RATE, the only instrument here that can distinguish a
    // load-time burst from a steady failure rate -----------------------------
    //
    // A sticky bit records WHEN IT WAS FIRST READ, not when it fired.  The
    // first readback lands 5-20 s after --program, so every instance whose
    // rate exceeds roughly one event per ten seconds sets its bit before
    // anyone looks, and reads back as indistinguishable from one that fired
    // instantly at configuration.  The 192-instance population saturated its
    // sticky bits on the first poll of every build, and that observation is
    // equally consistent with (a) a configuration-settling burst and (b) a
    // genuinely high steady rate.  Two builds' worth of fixes aimed at (a)
    // -- a real arbiter reset, then arming the detectors 17 ms after
    // releasing them -- moved the number not at all, which is what a
    // measurement that cannot see the distinction is expected to do.
    //
    // A windowed counter can see it, because it accumulates: read it twice
    // an hour apart and a nonzero delta is exposure-proportional by
    // construction.  Static across hours means the events all happened
    // before the first read; growing means a real rate, and the growth rate
    // IS the aggregate rate.
    //
    // TWO INSTANCES, NOT AN AGGREGATE, and this is not a cost compromise.
    // The obvious construction is one counter on |pop_flt, buying 192x the
    // exposure for the same two counters.  It was built, and it read every
    // single window as a hit on both the raw and the filtered tree while
    // only 42 of 192 filtered STICKY bits were set -- an outright
    // contradiction, since a signal high in every 589 us window sets all 192
    // latches in milliseconds.  Tracing the routed netlist explains it: the
    // reduction's logic cone contains 64 inlined grant LUT6_2s.  (* keep *)
    // holds the width-filter LUT2 as a cell but does not stop abc from
    // re-decomposing the OR levels above it against the grants directly, and
    // the grants toggle on every arbitration edge, so the tree glitches
    // continuously on ordinary activity that contains no overlap at all.  A
    // reduction over async nets is not safe here at any width and the
    // aggregate was abandoned rather than patched.
    //
    // A counter wired to ONE instance's filtered output has no tree above it
    // -- the window latch reads the (* keep *) LUT2 directly, so there is no
    // logic between the measured net and the instrument that can invent an
    // edge.  It also drops the ~460 LUT sites the two trees cost.
    //
    // POSITIVE CONTROL COMES FREE.  Each chosen instance's raw sticky bit is
    // already read back individually in the words at 5/20-24, so a counter
    // whose instance has a clean raw bit is known-not-listening and its zero
    // carries no information -- the same pairing rule as the sticky words,
    // with no extra hardware.  Two instances at opposite ends of the
    // population index rather than one, because per-site capture floors are
    // known to differ and a single site is not the population; two disagreeing
    // is itself the finding.  Neither is a substitute for the 192 sticky bits
    // -- those answer "how many", these answer "how often".
    //
    // Counting windows-with-a-hit rather than events, same caveat and same
    // WINBITS-scaling check as the per-channel counters above.
    localparam integer RATE_A = 0;
    localparam integer RATE_B = 96;

    wire [1:0] rate_src = {pop_flt[RATE_B], pop_flt[RATE_A]};

    wire [1:0]  rate_ovf;
    wire [23:0] rate_cnt [0:1];

    genvar ai;
    generate for (ai = 0; ai < 2; ai = ai + 1) begin : poprate
        // identical construction to the ch[] windowed counters -- see the
        // win_cnt header and ch[].uwinlatch for the reasoning behind every
        // line of it, including why nothing here uses a clock enable.
        wire win_hit;
        (* keep *) LUT4 #(.INIT(16'hAE00)) uwinlatch (
            .I0(rate_src[ai]), .I1(win_hit), .I2(win_edge_d),
            .I3(armed), .O(win_hit));

        reg sync1 = 1'b0, sync2 = 1'b0;
        always @(posedge stim[0].ck) begin
            sync1 <= win_hit;
            sync2 <= sync1;
        end

        wire hit_this_window = win_edge_d & sync2;

        reg [23:0] hitcnt = 24'h0;
        reg        hitcnt_ovf = 1'b0;
        always @(posedge stim[0].ck) begin
            hitcnt     <= hitcnt + {23'h0, hit_this_window};
            hitcnt_ovf <= hitcnt_ovf | (hit_this_window & (&hitcnt));
        end

        assign rate_cnt[ai] = hitcnt;
        assign rate_ovf[ai] = hitcnt_ovf;
    end endgenerate

    // ---- the threshold channels: same sticky construction, driven by a
    // pulse of known width instead of a real anomaly. ------------------------
    wire [NTH-1:0] pulse_raw, thresh_sticky;

    genvar ti;
    generate for (ti = 0; ti < NTH; ti = ti + 1) begin : th
        wire dly;
        bd_delay #(.N(width_of(ti))) ud (.a(ring3), .z(dly));
        assign pulse_raw[ti] = ring3 ^ dly;

        (* keep *) LUT3 #(.INIT(8'hE0)) usticky (
            .I0(pulse_raw[ti]), .I1(thresh_sticky[ti]), .I2(por_done),
            .O(thresh_sticky[ti]));
    end endgenerate

    // ---- control channel: the check that found the bug this file's power-on
    // reset now fixes.  Identical sticky construction to every other one
    // above -- same LUT3, same INIT, same (* keep *), same por_done gate --
    // but I0 is tied to constant 0, so nothing can ever set it through I0.
    // Before por_done existed, this read 1 deterministically on every fresh
    // --program: the bare OR-self-latch raced itself high during
    // configuration, on this exact board, with nothing driving it.  Every
    // FIRED bit elsewhere in that run was that race, not a captured event.
    // Left wired in permanently rather than removed once "fixed", because a
    // future change to the por_cnt clock, width, or timing could reopen the
    // same race, and this is the only thing that would say so.  Reading 0
    // here does not prove any given anomaly bit is real -- it only proves
    // the construction CAN power up clean, on this die, this bitstream.
    wire ctrl_sticky;
    (* keep *) LUT3 #(.INIT(8'hE0)) uctrl_sticky (
        .I0(1'b0), .I1(ctrl_sticky), .I2(armed), .O(ctrl_sticky));

    // ---- negative control for the Phase 2 window-latch/sync/counter chain,
    // same idea as ctrl_sticky above but for the newer, more complex
    // construction: I0 tied to constant 0, so win_hit can never be set
    // through it, feeding the SAME latch/synchronizer/counter shape every
    // ch[] channel uses.  A nonzero winctrl_hitcnt after any real exposure
    // means that chain self-triggers -- read mux address 5'd16 before
    // trusting any ch_hitcnt value.
    wire winctrl_win_hit;
    (* keep *) LUT4 #(.INIT(16'hAE00)) uwinctrl_latch (
        .I0(1'b0), .I1(winctrl_win_hit), .I2(win_edge_d), .I3(armed),
        .O(winctrl_win_hit));

    reg winctrl_sync1 = 1'b0, winctrl_sync2 = 1'b0;
    always @(posedge stim[0].ck) begin
        winctrl_sync1 <= winctrl_win_hit;
        winctrl_sync2 <= winctrl_sync1;
    end

    wire winctrl_hit_this_window = win_edge_d & winctrl_sync2;

    reg [23:0] winctrl_hitcnt = 24'h0;
    reg        winctrl_hitcnt_ovf = 1'b0;
    always @(posedge stim[0].ck) begin
        winctrl_hitcnt     <= winctrl_hitcnt + {23'h0, winctrl_hit_this_window};
        winctrl_hitcnt_ovf <= winctrl_hitcnt_ovf |
                               (winctrl_hit_this_window & (&winctrl_hitcnt));
    end

    // ---- diagnostic: a spatial snapshot of a depth-16 chain at the instant
    // of its first anomaly, instead of a time-sampled trace.  bd_delay
    // (rtl/bd_latch.v) is a frozen library cell and a black box -- no
    // intermediate tap is exposed on its port list, and it must stay that
    // way (Stage 0 design review, unrelated to this diagnostic).  So this is
    // a LOCAL, structurally identical 16-stage LUT1 chain, own bd_c2n_set,
    // own grant decoder -- a diagnostic twin of ch[5] (depth 16), not ch[5]
    // itself, since tapping the real one isn't possible without touching
    // the frozen cell.
    //
    // No new clock domain, and that's the point: instead of sampling in
    // TIME (which needs a fast clock -- the fastest available, a ring, is
    // ~5-10 ns/sample, far too coarse to distinguish real metastability
    // from ordinary chain-propagation glitching), this captures in SPACE --
    // every one of the 16 intermediate stages simultaneously, so the
    // resolution is the chain's OWN per-link delay (~120 ps, from the
    // already-measured SDF), not a clock period.  s[0] is the raw arbiter
    // decision node before any delay; s[16] is what ch[5] actually reads.
    // If the anomaly correlates with several adjacent stages disagreeing
    // (a wavefront still mid-chain), that is chain-propagation glitching.
    // If every stage already agrees with s[16], the chain had already
    // settled and whatever tripped the grant decoder came from q itself,
    // not the chain -- genuine late-resolving metastability.
    //
    // Captured ONCE, on the first anomaly, then frozen forever -- same
    // never-live-cleared discipline as every sticky bit in this file.
    // Before that first anomaly each snapshot bit is NOT meaningful (it is
    // just transparently tracking its tap's live, fast-moving value) --
    // diag16_captured says which case a poll is looking at.
    wire diag16_q_raw, diag16_g1, diag16_g2;
    bd_c2n_set udiag16_state (.a(r1), .b(r2), .rst(arb_rst), .q(diag16_q_raw));

    (* keep *) wire [16:0] diag16_s;
    assign diag16_s[0] = diag16_q_raw;
    genvar dsi;
    generate for (dsi = 0; dsi < 16; dsi = dsi + 1) begin : diag16_chain
        (* keep *) LUT1 #(.INIT(2'h2)) u (
            .I0(diag16_s[dsi]), .O(diag16_s[dsi+1]));
    end endgenerate

    (* keep *) LUT6_2 #(.INIT(GRANT_INIT)) udiag16_grant (
        .I0(r1), .I1(r2), .I2(diag16_s[16]), .I3(1'b0), .I4(1'b0), .I5(1'b1),
        .O5(diag16_g1), .O6(diag16_g2));
    wire diag16_anomaly_raw = diag16_g1 & diag16_g2;

    wire diag16_captured;
    (* keep *) LUT3 #(.INIT(8'hE0)) udiag16_captured (
        .I0(diag16_anomaly_raw), .I1(diag16_captured), .I2(armed),
        .O(diag16_captured));

    // 17 chain taps + r1 + r2 = 19 transparent-until-captured latches.
    // O = captured ? O(fb) : tap -- transparent (tracks tap live) while
    // captured=0, freezes at whatever it last held the instant captured
    // flips to 1, forever after (captured only ever goes 0->1, once).
    wire [18:0] diag16_snap;
    genvar dti;
    generate for (dti = 0; dti < 19; dti = dti + 1) begin : diag16_tap
        wire live = (dti < 17) ? diag16_s[dti] : (dti == 17 ? r1 : r2);
        (* keep *) LUT3 #(.INIT(8'hCA)) u (
            .I0(live), .I1(diag16_snap[dti]), .I2(diag16_captured),
            .O(diag16_snap[dti]));
    end endgenerate

    // ---- same diagnostic, depth 8, a twin of ch[3].  Added because on this
    // specific build/placement ch[5] (depth 16) happens to be one of the
    // clean channels -- its diagnostic twin above could plausibly take as
    // long to fire as the original 18-hour run did.  ch[3] (depth 8) is
    // saturating in THIS build, so this twin should capture almost
    // immediately and give a look at a channel actively misbehaving right
    // now, rather than waiting on one that currently isn't.  Same
    // construction throughout, just N=8 instead of N=16 (9 chain taps + r1
    // + r2 = 11 snapshot bits instead of 19).
    wire diag8_q_raw, diag8_g1, diag8_g2;
    bd_c2n_set udiag8_state (.a(r1), .b(r2), .rst(arb_rst), .q(diag8_q_raw));

    (* keep *) wire [8:0] diag8_s;
    assign diag8_s[0] = diag8_q_raw;
    genvar dsi8;
    generate for (dsi8 = 0; dsi8 < 8; dsi8 = dsi8 + 1) begin : diag8_chain
        (* keep *) LUT1 #(.INIT(2'h2)) u (
            .I0(diag8_s[dsi8]), .O(diag8_s[dsi8+1]));
    end endgenerate

    (* keep *) LUT6_2 #(.INIT(GRANT_INIT)) udiag8_grant (
        .I0(r1), .I1(r2), .I2(diag8_s[8]), .I3(1'b0), .I4(1'b0), .I5(1'b1),
        .O5(diag8_g1), .O6(diag8_g2));
    wire diag8_anomaly_raw = diag8_g1 & diag8_g2;

    wire diag8_captured;
    (* keep *) LUT3 #(.INIT(8'hE0)) udiag8_captured (
        .I0(diag8_anomaly_raw), .I1(diag8_captured), .I2(armed),
        .O(diag8_captured));

    wire [10:0] diag8_snap;
    genvar dti8;
    generate for (dti8 = 0; dti8 < 11; dti8 = dti8 + 1) begin : diag8_tap
        wire live = (dti8 < 9) ? diag8_s[dti8] : (dti8 == 9 ? r1 : r2);
        (* keep *) LUT3 #(.INIT(8'hCA)) u (
            .I0(live), .I1(diag8_snap[dti8]), .I2(diag8_captured),
            .O(diag8_snap[dti8]));
    end endgenerate

    // ---- asynchronous liveness sample, TCK domain, same technique ro_top
    // uses: the value is meaningless, the variance across repeated scans is
    // the proof that r1, r2, ring3 and every decision node are actually
    // toggling and not stuck at the value that would fake a clean result.
    // Only as wide as the signals actually being watched -- padding this to
    // 32 bits with constant zero used to cost 17 real, always-zero FDREs per
    // rank (34 total across rs0/rs1), pure dead weight sitting in the most
    // physically contested part of the design, right next to sr/hold at
    // BSCANE2's fixed site. -------------------------------------------------
    localparam integer SB_W = NTH + NCH + 3;
    wire [SB_W-1:0] sample_bus = {pulse_raw, q_dly_probe, ring3, r2, r1};
    reg  [SB_W-1:0] rs0 = {SB_W{1'b0}};
    reg  [SB_W-1:0] rs1 = {SB_W{1'b0}};
    // Unconditional, matching ro_top: gating this by bs_sel was tried and
    // costs a wide-fanout CE net off BSCANE2's fixed physical location for
    // no benefit (tck itself only toggles during an active scan anyway, so
    // an unconditional sampler already only samples while something is
    // happening) -- ro_top's own header calls this out as "no extra clock
    // load", which is exactly the resource this design turned out to need.
    always @(posedge tck) begin
        rs0 <= sample_bus;
        rs1 <= rs0;
    end

    // ---- capture mux --------------------------------------------------------
    reg [31:0] mux_d;
    reg        mux_o;
    always @* begin
        mux_d = 32'h0000_0000;
        mux_o = 1'b0;
        case (hold_addr)
            5'd0:  begin mux_d = stim_cnt_flat[31:0];  mux_o = stim_ovf[0]; end
            5'd1:  begin mux_d = stim_cnt_flat[63:32]; mux_o = stim_ovf[1]; end
            5'd2:  mux_d = {{(32 - NCH){1'b0}}, anomaly_sticky};
            5'd3:  mux_d = {{(32 - NTH){1'b0}}, thresh_sticky};
            5'd4:  mux_d = {31'h0, ctrl_sticky};
            // Phase 1: the depth-0 population, raw and unaggregated -- each
            // of the 24 bits is one physically distinct instance's own
            // sticky bit, not a popcount or OR of the group.
            5'd5:  mux_d = pop_sticky_pad[31:0];   // pop[0..31], raw
            // Phase 2: per-channel windowed hit counters, one address per
            // existing anomaly channel (ch[0..5], depths 0/1/2/4/8/16) --
            // {7'h0, overflow, 24-bit window-hit count}. Same reasoning as
            // Phase 1: read individually, not summed, so a skewed
            // distribution across channels stays visible.
            5'd6:  mux_d = {7'h0, ch_hitcnt_ovf[0], ch_hitcnt[0]};
            5'd7:  mux_d = {7'h0, ch_hitcnt_ovf[1], ch_hitcnt[1]};
            5'd8:  mux_d = 32'hDEAD_BEEF;
            5'd9:  mux_d = 32'h5A5A_1234;
            // Population aggregate rate, raw at 10 and filtered at 25 -- the
            // pair that answers burst-versus-steady; see their declaration
            // for why the sticky words at 5/20-24 cannot.  Read as a PAIR
            // and read the DELTA between two polls, never the absolute
            // value: these arm with everything else, so their first sample
            // already contains whatever happened before the first poll, and
            // only the growth between samples is exposure-proportional.
            //
            // 10 used to return the all-zeros bring-up constant; the nonzero
            // constants at 8 and 9 still catch a stuck-at-0 readback path,
            // and the addresses were full.
            5'd10: mux_d = {7'h0, rate_ovf[0], rate_cnt[0]};
            5'd11: mux_d = {7'h0, ch_hitcnt_ovf[2], ch_hitcnt[2]};
            5'd12: mux_d = {{(32 - SB_W){1'b0}}, rs1};
            5'd13: mux_d = {7'h0, ch_hitcnt_ovf[3], ch_hitcnt[3]};
            5'd14: mux_d = {7'h0, ch_hitcnt_ovf[4], ch_hitcnt[4]};
            5'd15: mux_d = {7'h0, ch_hitcnt_ovf[5], ch_hitcnt[5]};
            // Negative control for the Phase 2 window-latch/sync/counter
            // chain itself -- I0 tied to constant 0, same construction as
            // every other channel's, so nothing can ever set win_hit through
            // it.  ctrl_sticky proved the plain LUT3 sticky construction is
            // trustworthy; this is the same proof for the newer, more
            // complex chain (latch + 2-FF sync + unconditional counter) that
            // Phase 2 depends on.  A nonzero count here means the chain
            // self-triggers and every Phase 2 number above is noise, not
            // signal -- read this BEFORE trusting any ch_hitcnt value.
            5'd16: mux_d = {7'h0, winctrl_hitcnt_ovf, winctrl_hitcnt};
            // Diagnostic depth-16 spatial snapshot -- bit 19 is
            // diag16_captured (read this first: 0 means the 19 snapshot
            // bits below it are still live/meaningless, not yet frozen),
            // bits [18:17] are the frozen r2/r1 values, bits [16:0] are the
            // 17 chain taps s[0] (raw q) through s[16] (what ch[5] reads).
            5'd17: mux_d = {12'h0, diag16_captured, diag16_snap};
            // Same as 5'd17 but the depth-8 twin: bit 11 is diag8_captured,
            // bits [10:9] are frozen r2/r1, bits [8:0] are s[0]..s[8].
            5'd18: mux_d = {20'h0, diag8_captured, diag8_snap};

            // ---- width-discriminated twins of everything above ------------
            // 19 is the filtered sticky set, the direct counterpart of the
            // raw one at address 2.  Read as a PAIR with address 2 -- a
            // filtered zero beside a raw saturation is the whole result.
            5'd19: mux_d = {{(32 - NCH){1'b0}}, flt_sticky};

            // ---- the population, raw and filtered, 32 instances per word --
            // Address 5 is pop[0..31] raw and stays where it was so an old
            // script still reads something meaningful; 20..24 continue it to
            // pop[191], and 26..31 are the width-filtered twins of all six.
            // Read as PAIRS: raw word k against filtered word k.  A raw bit
            // that is clean after hours means that instance is not
            // listening, and its filtered zero carries no information.
            5'd20: mux_d = pop_sticky_pad[63:32];      // pop[32..63]
            5'd21: mux_d = pop_sticky_pad[95:64];      // pop[64..95]
            5'd22: mux_d = pop_sticky_pad[127:96];     // pop[96..127]
            5'd23: mux_d = pop_sticky_pad[159:128];    // pop[128..159]
            5'd24: mux_d = pop_sticky_pad[191:160];    // pop[160..191]

            // filtered half of the aggregate rate pair opened at address 10
            5'd25: mux_d = {7'h0, rate_ovf[1], rate_cnt[1]};

            5'd26: mux_d = pop_flt_sticky_pad[31:0];   // filtered, pop[0..31]
            5'd27: mux_d = pop_flt_sticky_pad[63:32];
            5'd28: mux_d = pop_flt_sticky_pad[95:64];
            5'd29: mux_d = pop_flt_sticky_pad[127:96];
            5'd30: mux_d = pop_flt_sticky_pad[159:128];
            5'd31: mux_d = pop_flt_sticky_pad[191:160];
            default: mux_d = 32'h0000_0000;
        endcase
    end

    // Poison a counter read taken while it is still running -- only the two
    // counters need this; the sticky bits and constants answer regardless.
    wire is_cnt = (hold_addr <= 5'd1);
    wire [31:0] cap_data = (is_cnt && hold_run) ? 32'hFFFF_FFFF : mux_d;

    wire [W-1:0] cap_word = {TAG,        // [47:40]
                             1'b0,       // [39]
                             mux_o,      // [38]
                             hold_run,   // [37]
                             hold_addr,  // [36:32]
                             cap_data};  // [31:0]

    // ---- shift register ------------------------------------------------------
    // sr_ce/sr_d are written out explicitly for clarity, but note this alone
    // does NOT constrain yosys: xilinx_dffopt folds constant-under-capture
    // bits of cap_word (the TAG field, the 2'b00 reserved field) into per-bit
    // FDRE+R / FDSE+S cells rather than uniform FDRE+CE regardless of RTL
    // phrasing, confirmed by diffing this against ro_top.v's own 48-bit sr,
    // which shows the identical split and still routes -- so that split by
    // itself is not what was failing PnR here.  What DOES matter enough to
    // fix is the CE axis specifically: nextpnr-xilinx does not discover a
    // resulting half-slice control-set clash until after a full route, and
    // hw/build_hw.sh now skips xilinx_dffopt for exactly that reason (see
    // its synthesis step and hw/README.md).  Even with the pass skipped, the
    // fixed BSCANE2 site plus this design's channel logic is dense enough
    // that placement is still seed-sensitive; build_hw.sh pins a seed
    // checked for determinism rather than trusting the default.
    reg [W-1:0] sr = {W{1'b0}};

    wire         sr_ce = bs_sel && (bs_capture || bs_shift);
    wire [W-1:0] sr_d  = bs_capture ? cap_word : {bs_tdi, sr[W-1:1]};

    always @(posedge tck) begin
        if (sr_ce) sr <= sr_d;
    end

    wire hold_ce = bs_sel && bs_update;
    always @(posedge tck) begin
        if (hold_ce) hold <= sr[5:0];
    end

    assign sr_tdo = sr[0];

    // Diagnostic only -- see ro_top for why nothing here is measured by
    // looking at them.
    assign led_red   = hold_run;
    assign led_green = |anomaly_sticky;

endmodule

`default_nettype wire
