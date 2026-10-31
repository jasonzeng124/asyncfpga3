// tb_f3_lut.v -- LUT/MUX delay semantics, self-checking against the
// TRANSPORT expectation (each input edge reaches the output one arc later).
// PASS requires the GLS_FID model; the default prims.v model must FAIL it
// (that is the negative control: cells/gls/fid/f3/run_f3.sh runs both).
//   T1  buffer, pulse 1000-1120 then rise 1130   (audit 1a: 1130 -> 1244)
//   T2  XOR3 cone, inputs 1000/1040/1100         (audit 5: settles 1224)
//       request at 1200: true margin -24 ps
//   T3  isolated 50 ps pulse through a buffer    (audit 2: swallowed)
//   T4  XOR2, A1 at 3000 and A2 at 3030: a 30 ps function hazard
//   T5  a change on a pin f does not read: no edge
//   T6  MUXF7 data pin, 50 ps pulse
`timescale 1ps/1ps
module tb_f3_lut;
    reg b = 0, x1 = 0, x2 = 0, x3 = 0, p = 0, h1 = 0, h2 = 0, n1 = 0, n2 = 0, md = 0;
    wire ob, ox, op, oh, on, om;
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) ub (.A1(b), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(ob));
    SLICE_LUTX #(.INIT(64'h96)) ux (.A1(x1), .A2(x2), .A3(x3), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(ox));
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) up (.A1(p), .A2(1'b0), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(op));
    SLICE_LUTX #(.INIT(64'h6)) uh (.A1(h1), .A2(h2), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(oh));
    SLICE_LUTX #(.INIT(64'hAAAAAAAAAAAAAAAA)) un (.A1(n1), .A2(n2), .A3(1'b0), .A4(1'b0), .A5(1'b0), .A6(1'b0), .O5(), .O6(on));
    SELMUX2_1 um (.D0(md), .D1(1'b0), .S0(1'b0), .OUT(om));

    integer eb = 0, ex = 0, ep = 0, eh = 0, en = 0, em = 0;
    time tb_last = 0, tx_last = 0;
    always @(ob) if ($time > 500) begin eb = eb + 1; tb_last = $time; $display("  ob  t=%0d %b", $time, ob); end
    always @(ox) if ($time > 500) begin ex = ex + 1; tx_last = $time; $display("  ox  t=%0d %b", $time, ox); end
    always @(op) if ($time > 500) begin ep = ep + 1; $display("  op  t=%0d %b", $time, op); end
    always @(oh) if ($time > 500) begin eh = eh + 1; $display("  oh  t=%0d %b", $time, oh); end
    always @(on) if ($time > 500) en = en + 1;
    always @(om) if ($time > 500) begin em = em + 1; $display("  om  t=%0d %b", $time, om); end

    reg cap;
    initial begin #1000 b = 1; #120 b = 0; #10 b = 1; end
    initial begin #1000 x1 = 1; #40 x2 = 1; #60 x3 = 1; end
    initial #1200 cap = ox;
    initial begin #2000 p = 1; #50 p = 0; end
    initial begin #3000 h1 = 1; #30 h2 = 1; end
    initial begin #4000 n2 = 1; #200 n2 = 0; end
    initial begin #5000 md = 1; #50 md = 0; end

    integer fail = 0;
    task chk(input c, input [8*64-1:0] what);
        begin if (!c) begin fail = fail + 1; $display("  FAIL %0s", what); end
              else $display("  ok   %0s", what); end
    endtask
    initial begin
        #8000;
        $display("T1 buffer: %0d edges, last at %0d (transport: 3 edges, last 1254)", eb, tb_last);
        chk(eb == 3 && tb_last == 1254, "T1 edge after 1130 arrives at 1254, not 1244");
        $display("T2 XOR3: %0d edges, settles %0d (transport: 3, 1224); value at request 1200 = %b (true 0)", ex, tx_last, cap);
        $display("   margin of a request at 1200 against the settle time: %0d ps", 1200 - $signed(tx_last));
        chk(ex == 3 && tx_last == 1224 && cap === 1'b0, "T2 XOR3 settles at 1224, margin -24 ps");
        chk(ep == 2, "T3 50 ps pulse passes");
        chk(eh == 2, "T4 30 ps function hazard on XOR2 appears");
        chk(en == 0, "T5 unread pin: no edge");
        chk(em == 2, "T6 MUXF7 passes a 50 ps pulse");
        if (fail) $display("tb_f3_lut FAIL (%0d)", fail); else $display("tb_f3_lut PASS");
        $finish;
    end
endmodule
