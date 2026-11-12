// tb_f3_kleene_ff.v -- settled Q (incl. x) of SLICE_FFX (and a flop clocked
// through BUFGCTRL) for random D/CE/SR vectors with x, one clock pulse per
// vector; run_f3.sh diffs the default and the GLS_FID run: they must be
// identical (fid changes timing, not values).  Inputs move 500 ps before the
// rise and the pulses are 500 ps wide, outside every aperture and well above
// the fid minimum pulse width.  CK itself is x on ~3% of the pulses (0->x->0),
// which both models treat as an edge.  The flops keep their state from one
// vector to the next, so hold and the x stickiness are covered too.
// run_f3.sh also runs a MUTATED fid model (x on CE loads D) and requires it to
// differ: the check can fail.
`timescale 1ps/1ps
module tb_f3_kleene_ff;
    reg ck = 0; reg [2:0] v; integer i, seed;
    wire [3:0] q; wire gck;
    // x on D 15%, on CE 10%, SR mostly 0 (x 4%, 1 10%) or every flop is x
    function bitd(input integer r0); reg [30:0] r; begin r = r0[30:0]; bitd = (r % 20 < 3) ? 1'bx : r[4]; end endfunction
    function bitce(input integer r0); reg [30:0] r; begin r = r0[30:0]; bitce = (r % 20 < 2) ? 1'bx : r[5]; end endfunction
    function bitsr(input integer r0); reg [30:0] r; begin r = r0[30:0]; bitsr = (r % 50 < 2) ? 1'bx : (r % 50 < 7); end endfunction
    SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0), .TCKQ(300), .SEED(1)) u0 (.CK(ck), .D(v[0]), .CE(v[1]), .SR(v[2]), .Q(q[0]));
    SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b1), .TCKQ(250), .SEED(2)) u1 (.CK(ck), .D(v[0]), .CE(v[1]), .SR(v[2]), .Q(q[1]));
    SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b1), .TCKQ(120), .TSU(100), .THD(100), .SEED(3)) u2 (.CK(ck), .D(~v[0]), .CE(v[1]), .SR(v[2]), .Q(q[2]));
    BUFGCTRL #(.TI0O(90)) ub (.I0(ck), .I1(1'b0), .S0(1'b0), .S1(1'b0), .CE0(1'b1), .CE1(1'b1),
                              .IGNORE0(1'b1), .IGNORE1(1'b1), .O(gck));
    SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0), .TCKQ(300), .SEED(4)) u3 (.CK(gck), .D(v[0]), .CE(v[1]), .SR(v[2]), .Q(q[3]));
    integer r;
    initial begin
        seed = 23; v = 3'b0;
        #1000;
        for (i = 0; i < 3000; i = i + 1) begin
            v[0] = bitd($random(seed)); v[1] = bitce($random(seed)); v[2] = bitsr($random(seed));
            r = $random(seed);
            #500 ck = (r[30:0] % 100 < 3) ? 1'bx : 1'b1;
            #500 ck = 0;
            #1000 $display("%0d %b %b %b", i, v, ck, q);
        end
        $finish;
    end
endmodule
