// Audit tb: characterise ICBUF (wire) specify-path delay semantics under iverilog.
// O6 = A1 (buffer), INIT bit i = i[0] -> 64'hAAAA_AAAA_AAAA_AAAA.
// Baked: parameters default (124).  -DANNOT: params set to 7, then $sdf_annotate
// of ic124.sdf sets A1->O6 back to 124 (proves annotation actually landed).
`timescale 1ps/1ps
module tb;
    localparam N = 12;
    reg  [N-1:0] a = 0;
    wire [N-1:0] o;
    always @(a) $display("IN  t=%0d a=%b", $time, a);
`ifdef ANNOT
    ICBUF #(.D(7)) u0 (.I(a[0]), .O(o[0]));
`else
    ICBUF #(.D(124)) u0 (.I(a[0]), .O(o[0]));
`endif
    always @(o[0]) $display("OUT ch0 t=%0d o=%b", $time, o[0]);
`ifdef ANNOT
    ICBUF #(.D(7)) u1 (.I(a[1]), .O(o[1]));
`else
    ICBUF #(.D(124)) u1 (.I(a[1]), .O(o[1]));
`endif
    always @(o[1]) $display("OUT ch1 t=%0d o=%b", $time, o[1]);
`ifdef ANNOT
    ICBUF #(.D(7)) u2 (.I(a[2]), .O(o[2]));
`else
    ICBUF #(.D(124)) u2 (.I(a[2]), .O(o[2]));
`endif
    always @(o[2]) $display("OUT ch2 t=%0d o=%b", $time, o[2]);
`ifdef ANNOT
    ICBUF #(.D(7)) u3 (.I(a[3]), .O(o[3]));
`else
    ICBUF #(.D(124)) u3 (.I(a[3]), .O(o[3]));
`endif
    always @(o[3]) $display("OUT ch3 t=%0d o=%b", $time, o[3]);
`ifdef ANNOT
    ICBUF #(.D(7)) u4 (.I(a[4]), .O(o[4]));
`else
    ICBUF #(.D(124)) u4 (.I(a[4]), .O(o[4]));
`endif
    always @(o[4]) $display("OUT ch4 t=%0d o=%b", $time, o[4]);
`ifdef ANNOT
    ICBUF #(.D(7)) u5 (.I(a[5]), .O(o[5]));
`else
    ICBUF #(.D(124)) u5 (.I(a[5]), .O(o[5]));
`endif
    always @(o[5]) $display("OUT ch5 t=%0d o=%b", $time, o[5]);
`ifdef ANNOT
    ICBUF #(.D(7)) u6 (.I(a[6]), .O(o[6]));
`else
    ICBUF #(.D(124)) u6 (.I(a[6]), .O(o[6]));
`endif
    always @(o[6]) $display("OUT ch6 t=%0d o=%b", $time, o[6]);
`ifdef ANNOT
    ICBUF #(.D(7)) u7 (.I(a[7]), .O(o[7]));
`else
    ICBUF #(.D(124)) u7 (.I(a[7]), .O(o[7]));
`endif
    always @(o[7]) $display("OUT ch7 t=%0d o=%b", $time, o[7]);
`ifdef ANNOT
    ICBUF #(.D(7)) u8 (.I(a[8]), .O(o[8]));
`else
    ICBUF #(.D(124)) u8 (.I(a[8]), .O(o[8]));
`endif
    always @(o[8]) $display("OUT ch8 t=%0d o=%b", $time, o[8]);
`ifdef ANNOT
    ICBUF #(.D(7)) u9 (.I(a[9]), .O(o[9]));
`else
    ICBUF #(.D(124)) u9 (.I(a[9]), .O(o[9]));
`endif
    always @(o[9]) $display("OUT ch9 t=%0d o=%b", $time, o[9]);
`ifdef ANNOT
    ICBUF #(.D(7)) u10 (.I(a[10]), .O(o[10]));
`else
    ICBUF #(.D(124)) u10 (.I(a[10]), .O(o[10]));
`endif
    always @(o[10]) $display("OUT ch10 t=%0d o=%b", $time, o[10]);
`ifdef ANNOT
    ICBUF #(.D(7)) u11 (.I(a[11]), .O(o[11]));
`else
    ICBUF #(.D(124)) u11 (.I(a[11]), .O(o[11]));
`endif
    always @(o[11]) $display("OUT ch11 t=%0d o=%b", $time, o[11]);
    // channel stimuli (all start at 0)
    initial begin
`ifdef ANNOT
        $sdf_annotate("ic124.sdf", tb);
`endif
        // ch0: the claimed example: pulse 1000-1120 then rise at 1130
        #1000 a[0]=1; #120 a[0]=0; #10 a[0]=1;
    end
    // ch1..ch6: isolated pulses of width 10,60,100,123,124,200 at 3000
    initial begin #3000 a[1]=1; #10  a[1]=0; end
    initial begin #3000 a[2]=1; #60  a[2]=0; end
    initial begin #3000 a[3]=1; #100 a[3]=0; end
    initial begin #3000 a[4]=1; #123 a[4]=0; end
    initial begin #3000 a[5]=1; #124 a[5]=0; end
    initial begin #3000 a[6]=1; #200 a[6]=0; end
    // ch7: step at 5000 then glitch low 5050-5060 (short negative runt after a step)
    initial begin #5000 a[7]=1; #50 a[7]=0; #10 a[7]=1; end
    // ch8: pulse 1000-1010 then rise at 1100 (late second edge, still within d of first)
    initial begin #1000 a[8]=1; #10 a[8]=0; #90 a[8]=1; end
    // ch9: two pulses 300 apart, each 200 wide
    initial begin #7000 a[9]=1; #200 a[9]=0; #100 a[9]=1; #200 a[9]=0; end
    // ch10: rise 9000, fall 9050, rise 9100, fall 9150 (train of 50ps pulses, gap 50)
    initial begin #9000 a[10]=1; #50 a[10]=0; #50 a[10]=1; #50 a[10]=0; end
    // ch11: plain step reference
    initial begin #1000 a[11]=1; end
    initial #12000 $finish;
endmodule
