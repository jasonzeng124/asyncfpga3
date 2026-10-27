// Audit tb: random input traces into one SLICE_LUTX (pins A1..A3 live), log all
// pin and O6 events for offline model fitting (fit_delay.py).
`timescale 1ps/1ps
module tb;
    parameter [63:0] INIT = 64'h96;   // overridden with -P
    parameter D1 = 124, D2 = 124, D3 = 124;
    parameter SEED = 1;
    parameter NEV = 4000;
    reg a1 = 0, a2 = 0, a3 = 0;
    wire o;
    SLICE_LUTX #(.INIT(INIT), .TA1O6(D1), .TA2O6(D2), .TA3O6(D3))
        u (.A1(a1), .A2(a2), .A3(a3), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o));
    integer k, seed, gap, which;
    always @(o) $display("O %0d %b", $time, o);
    initial begin
        seed = SEED;
        #1000;
        for (k = 0; k < NEV; k = k + 1) begin
            gap = 1 + ({$random(seed)} % 220);
            if (({$random(seed)} % 10) == 0) gap = gap + 600;   // occasional quiet gap
            #gap;
            which = {$random(seed)} % 3;
            case (which)
              0: a1 = ~a1;
              1: a2 = ~a2;
              2: a3 = ~a3;
            endcase
            $display("I %0d %0d %b%b%b", $time, which, a1, a2, a3);
        end
        #2000 $finish;
    end
endmodule
