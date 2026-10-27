// Audit tb: characterise SLICE_LUTX specify-path delay semantics under iverilog.
// O6 = A1 (buffer), INIT bit i = i[0] -> 64'hAAAA_AAAA_AAAA_AAAA.
// Baked: parameters default (124).  -DANNOT: params set to 7, then $sdf_annotate
// of lut124.sdf sets A1->O6 back to 124 (proves annotation actually landed).
`timescale 1ps/1ps
module tb;
    localparam N = 12;
    reg  [N-1:0] a = 0;
    wire [N-1:0] o;
    always @(a) $display("IN  t=%0d a=%b", $time, a);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u0 (.A1(a[0]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[0]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u0 (.A1(a[0]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[0]));
`endif
    always @(o[0]) $display("OUT ch0 t=%0d o=%b", $time, o[0]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u1 (.A1(a[1]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[1]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u1 (.A1(a[1]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[1]));
`endif
    always @(o[1]) $display("OUT ch1 t=%0d o=%b", $time, o[1]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u2 (.A1(a[2]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[2]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u2 (.A1(a[2]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[2]));
`endif
    always @(o[2]) $display("OUT ch2 t=%0d o=%b", $time, o[2]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u3 (.A1(a[3]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[3]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u3 (.A1(a[3]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[3]));
`endif
    always @(o[3]) $display("OUT ch3 t=%0d o=%b", $time, o[3]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u4 (.A1(a[4]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[4]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u4 (.A1(a[4]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[4]));
`endif
    always @(o[4]) $display("OUT ch4 t=%0d o=%b", $time, o[4]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u5 (.A1(a[5]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[5]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u5 (.A1(a[5]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[5]));
`endif
    always @(o[5]) $display("OUT ch5 t=%0d o=%b", $time, o[5]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u6 (.A1(a[6]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[6]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u6 (.A1(a[6]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[6]));
`endif
    always @(o[6]) $display("OUT ch6 t=%0d o=%b", $time, o[6]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u7 (.A1(a[7]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[7]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u7 (.A1(a[7]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[7]));
`endif
    always @(o[7]) $display("OUT ch7 t=%0d o=%b", $time, o[7]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u8 (.A1(a[8]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[8]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u8 (.A1(a[8]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[8]));
`endif
    always @(o[8]) $display("OUT ch8 t=%0d o=%b", $time, o[8]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u9 (.A1(a[9]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[9]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u9 (.A1(a[9]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[9]));
`endif
    always @(o[9]) $display("OUT ch9 t=%0d o=%b", $time, o[9]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u10 (.A1(a[10]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[10]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u10 (.A1(a[10]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[10]));
`endif
    always @(o[10]) $display("OUT ch10 t=%0d o=%b", $time, o[10]);
`ifdef ANNOT
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u11 (.A1(a[11]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[11]));
`else
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u11 (.A1(a[11]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[11]));
`endif
    always @(o[11]) $display("OUT ch11 t=%0d o=%b", $time, o[11]);
    // channel stimuli (all start at 0)
    initial begin
`ifdef ANNOT
        $sdf_annotate("lut124.sdf", tb);
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
