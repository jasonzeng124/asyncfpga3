// Audit tb: characterise SLICE_LUTX specify-path delay semantics under iverilog.
// O6 = A1 (buffer), INIT bit i = i[0] -> 64'hAAAA_AAAA_AAAA_AAAA.
// Baked: parameters default (124).  -DANNOT: params set to 7, then $sdf_annotate
// of lut124.sdf sets A1->O6 back to 124 (proves annotation actually landed).
`timescale 1ps/1ps
module tb;
    localparam N = 12;
    reg  [N-1:0] a = 0;
    wire [N-1:0] o;
    genvar i;
    generate for (i = 0; i < N; i = i + 1) begin : g
`ifdef ANNOT
        SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA), .TA1O6(7)) u (.A1(a[i]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[i]));
`else
        SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) u (.A1(a[i]), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(o[i]));
`endif
        always @(a[i]) $display("IN  ch%0d t=%0d a=%b", i, $time, a[i]);
        always @(o[i]) $display("OUT ch%0d t=%0d o=%b", i, $time, o[i]);
    end endgenerate
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
