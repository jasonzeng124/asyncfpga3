// tb_f3_kleene_c4.v -- settled outputs (incl. x) of CARRY4 and SLICE_LATX for
// random vectors with x on the inputs; run_f3.sh diffs the default and the
// GLS_FID run: they must be identical (fid changes timing, not values).
// The latch sees a fresh vector each step, so its state carries over: the
// comparison covers its hold behaviour too.
`timescale 1ps/1ps
module tb_f3_kleene_c4;
    reg [9:0] c; reg [3:0] l; integer i, s, seed;
    wire [3:0] o, co; wire q0, q1;
    CARRY4 u (.CIN(c[0]), .CYINIT(c[1]), .DI0(c[2]), .DI1(c[3]), .DI2(c[4]), .DI3(c[5]),
              .S0(c[6]), .S1(c[7]), .S2(c[8]), .S3(c[9]),
              .O0(o[0]), .O1(o[1]), .O2(o[2]), .O3(o[3]), .CO0(co[0]), .CO1(co[1]), .CO2(co[2]), .CO3(co[3]));
    SLICE_LATX #(.INIT(1'b0), .SRVAL(1'b0), .GHIGH(1'b1)) ul0 (.CK(l[0]), .D(l[1]), .CE(l[2]), .SR(l[3]), .Q(q0));
    SLICE_LATX #(.INIT(1'b1), .SRVAL(1'b1), .GHIGH(1'b0)) ul1 (.CK(l[0]), .D(l[1]), .CE(l[2]), .SR(l[3]), .Q(q1));
    // x on 15% of carry pins.  A latch's x is sticky (a closed latch keeps
    // it), so its pins are x more rarely and SR is mostly 0, or the latches
    // would be x on almost every line and compare nothing.
    function bitx(input integer r0); reg [30:0] r; begin r = r0[30:0]; bitx = (r % 20 < 3) ? 1'bx : r[4]; end endfunction
    function bitl(input integer r0); reg [30:0] r; begin r = r0[30:0]; bitl = (r % 50 < 1) ? 1'bx : r[4]; end endfunction
    function bitsr(input integer r0); reg [30:0] r; begin r = r0[30:0]; bitsr = (r % 50 < 1) ? 1'bx : (r % 50 < 6); end endfunction
    initial begin
        seed = 11;
        for (i = 0; i < 3000; i = i + 1) begin
            for (s = 0; s < 10; s = s + 1) c[s] = bitx($random(seed));
            l[0] = bitl($random(seed)); l[1] = bitx($random(seed));
            l[2] = bitl($random(seed)); l[3] = bitsr($random(seed));
            #2000 $display("%0d %b %b %b %b %b %b", i, c, o, co, l, q0, q1);
        end
        $finish;
    end
endmodule
