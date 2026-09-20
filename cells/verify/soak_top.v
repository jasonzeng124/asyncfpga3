// ---------------------------------------------------------------------------
// soak_top.v -- one of everything, in one design, for the place-and-route gate.
//
// This is not a functional design and is not meant to be one.  It exists so
// nextpnr-xilinx has to pack, place and route every cell in the library at
// once, on the real chipdb, with real feedback loops.  What it proves:
//
//   the split_lut6_2 packer patch is present and works -- a stock
//   nextpnr-xilinx fails on the first fractured cell with "no wire found for
//   port O5", so the library is unbuildable without it;
//
//   every (* keep *) combinational loop survives synthesis and placement, and
//   --ignore-loops is enough to get them routed;
//
//   the BRAM port's clock net is driven by exactly one explicit buffer, and
//   -noclkbuf plus clkbuf_inhibit keeps anything from inserting another.
//
// The board only breaks out two PL pins, so the whole design hangs off one
// input and collapses into one output.  Cells are cross-wired rather than all
// driven from the same net, so nothing is a duplicate of anything else and
// yosys cannot merge them away.
// ---------------------------------------------------------------------------

// Matched-delay lengths.  The numbers below are PLACEHOLDERS -- they are what
// a design starts with, before anything has been routed.  verify/tighten.py
// measures what they should be for an actual route and writes sizes.vh;
// verify/resize.sh feeds that back in and iterates.  Whether that iteration
// settles is not obvious in advance, because changing a chain's length moves
// the placement that produced its own measurement.
`ifdef BD_SIZES
 `include "sizes.vh"
`endif
`ifndef BD_SZ_UDEC
 `define BD_SZ_UDEC 16
`endif
`ifndef BD_SZ_UMERGE
 `define BD_SZ_UMERGE 6
`endif
`ifndef BD_SZ_UMUX
 `define BD_SZ_UMUX 4
`endif
`ifndef BD_SZ_UMEM_USETUP
 `define BD_SZ_UMEM_USETUP 8
`endif
`ifndef BD_SZ_UMEM_UCO
 `define BD_SZ_UMEM_UCO 12
`endif
// The spine's own matched delay.  upipe's data_out reaches usteer's select
// through four latches while its req_out leaves the last C node directly, so
// at DELAY(0) the request beats the select it is supposed to be steering by
// -1372 ps (raw) on the routed SDF -- rule E red at usteer across four placer
// seeds.  bdc/emit.py never emits this shape: emit_links() applies
// SELECT_PAD * n to any channel consumed as a select, precisely to cancel
// that lead, so this is the stress rig missing a delay the compiler always
// puts in, not a backend defect.  Number from verify/skew.py on the route it
// measured, then re-routed and re-measured; it is a per-build property like
// every other BD_SZ_* here.
`ifndef BD_SZ_UPIPE
 `define BD_SZ_UPIPE 10
`endif
// The pipe's acknowledge-fall hold (bd_link.v DACK), rule H's knob.
`ifndef BD_SZ_UPIPE_UACK
 `define BD_SZ_UPIPE_UACK 4
`endif
// The request line on each internal stage boundary (SDELAY), rule I's knob.
`ifndef BD_SZ_UPIPE_SDELAY
 `define BD_SZ_UPIPE_SDELAY 3
`endif

`default_nettype none

module soak_top (input wire pin_in, output wire pin_out);

    wire rst = pin_in;

    // A free-running spine: a pipeline whose output acknowledges itself and
    // whose input request comes back from its own acknowledge.  Nothing here
    // settles, which is the point -- every loop is live.
    wire        p_ack_in, p_req_out;
    wire [7:0]  p_data_out;
    wire        spine;
    bd_delay #(.N(3)) uspin (.a(p_ack_in), .z(spine));

    bd_pipe #(.W(8), .N(4), .DELAY(`BD_SZ_UPIPE), .SDELAY(`BD_SZ_UPIPE_SDELAY),
              .DACK(`BD_SZ_UPIPE_UACK)) upipe (
        .rst(rst),
        .req_in(~spine), .ack_in(p_ack_in), .data_in({7'h5A, pin_in}),
        .req_out(p_req_out), .ack_out(p_req_out), .data_out(p_data_out));

    // -- routing the handshake ----------------------------------------------
    wire s_ack, s_req0, s_req1;
    bd_steer usteer (.req(p_req_out), .s(p_data_out[0]), .ack(s_ack),
                     .req0(s_req0), .ack0(p_data_out[1]),
                     .req1(s_req1), .ack1(p_data_out[2]));

    wire [3:0] f_req_out;  wire f_ack;
    bd_fork #(.N(4)) ufork (.rst(rst), .req(s_req0), .ack(f_ack),
                            .req_out(f_req_out), .ack_in(p_data_out[7:4]));

    wire j_req;
    bd_join #(.N(4)) ujoin (.rst(rst), .req_in(f_req_out), .ack_out(),
                            .req(j_req), .ack(s_ack));

    // A tree past the four-input ceiling, so the recursive form is exercised.
    wire        src_req, snk_ack;
    wire [7:0]  src_data;
    wire t_q;
    bd_ctree #(.N(10)) utree (.a({src_req, f_req_out, p_data_out[3:0], j_req}),
                              .rst(rst), .q(t_q));

    // -- converters ----------------------------------------------------------
    wire enc_t, enc_f, enc_ack;
    bd_bd2dr uenc (.req(s_req1), .d(p_data_out[3]), .ack(enc_ack),
                   .t(enc_t), .f(enc_f), .ack_dr(t_q));

    wire dec_req, dec_d, dec_ackdr;
    bd_dr2bd #(.DELAY(`BD_SZ_UDEC), .HOLD(1)) udec (
        .t(enc_t), .f(enc_f), .ack_dr(dec_ackdr),
        .req(dec_req), .d(dec_d), .ack(p_data_out[6]));

    // -- merge and mux -------------------------------------------------------
    wire m_xack, m_yack, m_req;  wire [7:0] m_data;
    bd_merge #(.W(8), .DELAY(`BD_SZ_UMERGE)) umerge (
        .rst(rst),
        .x_req(dec_req), .x_ack(m_xack), .x_data(p_data_out),
        .y_req(j_req),   .y_ack(m_yack), .y_data({p_data_out[3:0], 4'hC}),
        .z_req(m_req),   .z_ack(t_q),    .z_data(m_data));

    // ctl_req and s must be the req/data pair of ONE channel -- bd_mux.v's
    // own header says so ("s is ordinary channel data, held by the control
    // channel's own contract").  dec_req/dec_d is that pair: bd_dr2bd pads
    // req behind d for exactly this reason (rtl/bd_ctl.v's DELAY on `either`).
    // t_q was here before and is not dec_d's own request -- an unrelated
    // free-running node paired with a select it has no contract with, which
    // is what verify/skew.py's rule E was catching.
    wire u_xack, u_yack, u_cack, u_req;  wire [7:0] u_data;
    bd_mux #(.W(8), .DELAY(`BD_SZ_UMUX)) umux (
        .rst(rst),
        .x_req(m_req),     .x_ack(u_xack), .x_data(m_data),
        .y_req(dec_req),   .y_ack(u_yack), .y_data(p_data_out),
        .ctl_req(dec_req), .ctl_ack(u_cack), .s(dec_d),
        .z_req(u_req),     .z_ack(m_xack), .z_data(u_data));

    // -- arbitration ---------------------------------------------------------
    wire a1, a2, r0, ag1, ag2;
    bd_arbiter uarb (
        .rst(rst), .r1(u_req), .A1(a1), .r2(m_req), .A2(a2),
        .R0(r0), .A0(u_cack), .g1(ag1), .g2(ag2));

    // -- endpoints -----------------------------------------------------------
    // The source's request goes into utree and its acknowledge comes back out
    // of it, so this is a real ring and not a stranded inverter -- which is the
    // only way the route gate sees what bd_src actually is.  The tree has rst
    // on a pin, so the ring has a value to start from; a bd_src whose consumer
    // does not reset has no starting value at all, which tb_end demonstrates
    // rather than assumes.
    //
    // It is also the one loop in this design that stores nothing.  The
    // state-node census tighten.py prints counts it, correctly, as a loop.
    bd_src #(.W(8), .VAL(8'hA5)) usrc (.req(src_req), .ack(t_q), .data(src_data));
    bd_snk #(.W(8))              usnk (.req(ag2), .ack(snk_ack), .data(src_data));

    // -- storage variants ----------------------------------------------------
    wire [3:0] lat_q;
    bd_latch_rst #(.W(4), .RESET_VALUE(64'h5)) ulr (
        .d(u_data[3:0]), .en(ag1), .rst(rst), .q(lat_q));

    // -- the memory port -----------------------------------------------------
    wire        mem_ack;
    wire [15:0] mem_rdata;
    bd_mem #(.AW(10), .DW(16), .DSETUP(`BD_SZ_UMEM_USETUP),
            .DCO(`BD_SZ_UMEM_UCO), .USE_BUFG(0)) umem (
        .req(r0), .ack(mem_ack),
        .addr({u_data, lat_q, ag2, ag1}), .wdata({u_data, m_data}),
        .we(a1), .rdata(mem_rdata));

    assign pin_out = ^{mem_rdata, mem_ack, a2, u_data, lat_q, dec_ackdr,
                       m_yack, u_yack, f_ack, enc_ack, s_ack, p_ack_in,
                       src_data, snk_ack};

endmodule

`default_nettype wire
