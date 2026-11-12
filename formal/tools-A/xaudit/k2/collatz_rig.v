// collatz_rig.v -- cells/hw/gcd_rig.v with bdc_collatz in place of bdc_gcd (probe K2).
//
// Same closed four-phase ring as gcd_rig.v (uenv0 = bd_c2n, uenv1 = bd_c2n_set,
// bd_fork to the inputs, urdly = bd_delay(CMPD) on out0_req, p_end sunk through
// a 2-element delay), same width-filtered err/ok checker.  Differences, and only
// these:
//   * the DUT is bdc_collatz (n, start) -> (out0, end); the fork has N = 2;
//   * no probe ports (collatz has no abs/cmp finding to watch);
//   * the vector ROM is {expected steps, n}, derived from kernels/collatz/collatz.c
//     (steps while n != 1: n even -> n >> 1, else 3n + 1), not from any run.
// The port list is gcd_rig's minus the abs_* / cmp_* probes.
// Not part of cells/: built only in an exported copy of the tree (k2/build_k2.sh).
`default_nettype none
module collatz_rig #(parameter integer IDXW  = 4,
                     parameter integer WFILT = 2,
                     parameter integer CMPD  = 16)
    (input  wire            rst,
     input  wire [IDXW-1:0] idx,
     output wire            lap,
     output wire            err_flt,
     output wire            ok_flt,
     output wire            probe,
     output wire [31:0]     res_data);

    // {expected, n}.  Vector 1 (n = 2 -> 1 step) is the formal tools' transaction:
    // short (one loop iteration) and its answer (1) is not the failure value 0.
    function [63:0] vector(input [3:0] i);
        case (i)
            4'd0:  vector = {32'd5,   32'd5};
            4'd1:  vector = {32'd1,   32'd2};
            4'd2:  vector = {32'd7,   32'd3};
            4'd3:  vector = {32'd8,   32'd6};
            4'd4:  vector = {32'd16,  32'd7};
            4'd5:  vector = {32'd111, 32'd27};
            4'd6:  vector = {32'd118, 32'd97};
            4'd7:  vector = {32'd170, 32'd703};
            4'd8:  vector = {32'd19,  32'd9};
            4'd9:  vector = {32'd9,   32'd12};
            4'd10: vector = {32'd20,  32'd19};
            4'd11: vector = {32'd23,  32'd25};
            4'd12: vector = {32'd106, 32'd31};
            4'd13: vector = {32'd109, 32'd41};
            4'd14: vector = {32'd2,   32'd4};
            4'd15: vector = {32'd111, 32'd1000};
        endcase
    endfunction
    wire [63:0] vec = vector(idx);
    wire [31:0] n_v = vec[31:0];
    wire [31:0] g_v = vec[63:32];

    wire n_req, n_ack, start_req, start_ack;
    wire out0_req, out0_ack, p_end_req, p_end_ack;
    wire [31:0] out0_data;

`ifdef COLLATZ_DUT_PARAMS
    bdc_collatz #(`COLLATZ_DUT_PARAMS) udut (
`else
    bdc_collatz udut (
`endif
        .rst(rst),
        .n_req(n_req),         .n_ack(n_ack),         .n_data(n_v),
        .start_req(start_req), .start_ack(start_ack),
        .out0_req(out0_req),   .out0_ack(out0_ack),   .out0_data(out0_data),
        .p_end_req(p_end_req), .p_end_ack(p_end_ack));

    wire env_c, in_ack;
    wire [1:0] in_req, in_acks;
    assign in_acks = {start_ack, n_ack};
    assign {start_req, n_req} = in_req;
    bd_fork #(.N(2)) ufork (
        .rst(rst), .req(env_c), .ack(in_ack),
        .req_out(in_req), .ack_in(in_acks));

    bd_delay #(.N(2)) upsnk (.a(p_end_req), .z(p_end_ack));

    wire res_req, res_ack;
    bd_delay #(.N(CMPD)) urdly (.a(out0_req), .z(res_req));
    assign out0_ack = res_ack;

    wire env_c0;
    bd_c2n     uenv0 (.a(res_req), .b(env_c),  .rst(rst), .q(env_c0));
    bd_c2n_set uenv1 (.a(env_c0),  .b(in_ack), .rst(rst), .q(env_c));
    assign res_ack = env_c0;

    wire mism = |(out0_data ^ g_v);
    wire err_raw, ok_raw, err_d, ok_d;
    (* keep *) LUT2 #(.INIT(4'h8)) uerr_d (.I0(mism), .I1(res_req), .O(err_raw));
    (* keep *) LUT2 #(.INIT(4'h4)) uok_d  (.I0(mism), .I1(res_req), .O(ok_raw));
    bd_delay #(.N(WFILT)) uerr_w (.a(err_raw), .z(err_d));
    bd_delay #(.N(WFILT)) uok_w  (.a(ok_raw),  .z(ok_d));
    (* keep *) LUT2 #(.INIT(4'h8)) uerr_a (.I0(err_raw), .I1(err_d), .O(err_flt));
    (* keep *) LUT2 #(.INIT(4'h8)) uok_a  (.I0(ok_raw),  .I1(ok_d),  .O(ok_flt));

    assign lap      = res_req;
    assign probe    = env_c;
    assign res_data = out0_data;
endmodule
`default_nettype wire
