// Audit tb: X-propagation of SLICE_LUTX (O5,O6) and SELMUX2_1 for vectors in vec.txt
`timescale 1ps/1ps
module tb;
    parameter [63:0] INIT = 64'h0;
    reg [5:0] a; reg [2:0] m;   // a = {A6..A1}; m = {S0,D1,D0}
    wire o5, o6, mo;
    SLICE_LUTX #(.INIT(INIT)) u (.A1(a[0]), .A2(a[1]), .A3(a[2]), .A4(a[3]), .A5(a[4]), .A6(a[5]), .O5(o5), .O6(o6));
    SELMUX2_1 mx (.D0(m[0]), .D1(m[1]), .S0(m[2]), .OUT(mo));
    integer fd, r;
    initial begin
        fd = $fopen("vec.txt", "r");
        while (!$feof(fd)) begin
            r = $fscanf(fd, "%b %b\n", a, m);
            if (r == 2) begin #1000; $display("%b %b %b %b %b", a, m, o5, o6, mo); end
        end
        $finish;
    end
endmodule
