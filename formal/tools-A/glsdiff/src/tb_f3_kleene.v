// tb_f3_kleene.v -- settled outputs (incl. x) of SLICE_LUTX / SELMUX2_1 for
// random vectors with x on the inputs; run_f3.sh diffs the default and the
// GLS_FID run: they must be identical (fid changes timing, not values).
`timescale 1ps/1ps
module tb_f3_kleene;
    reg [5:0] a; reg [2:0] m; integer i, s, seed;
    reg [63:0] init [0:3];
    wire [3:0] o6, o5; wire om;
    genvar g;
    generate for (g = 0; g < 4; g = g + 1) begin : L
        SLICE_LUTX #(.INIT(g == 0 ? 64'h00E800E800E800E8 : g == 1 ? 64'h6996966996696996 :
                           g == 2 ? 64'hCAFEF00DDEADBEEF : 64'hFFB2FFB2ACACACAC)) u (
            .A1(a[0]), .A2(a[1]), .A3(a[2]), .A4(a[3]), .A5(a[4]), .A6(a[5]), .O5(o5[g]), .O6(o6[g]));
    end endgenerate
    SELMUX2_1 um (.D0(m[0]), .D1(m[1]), .S0(m[2]), .OUT(om));
    function bit3(input integer r); bit3 = (r % 10 < 3) ? 1'bx : r[4]; endfunction
    initial begin
        seed = 5;
        for (i = 0; i < 3000; i = i + 1) begin
            for (s = 0; s < 6; s = s + 1) a[s] = bit3($random(seed));
            for (s = 0; s < 3; s = s + 1) m[s] = bit3($random(seed));
            #1000 $display("%0d %b %b %b %b %b", i, a, m, o6, o5, om);
        end
        $finish;
    end
endmodule
