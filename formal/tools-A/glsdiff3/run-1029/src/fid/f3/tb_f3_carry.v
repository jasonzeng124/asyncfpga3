// tb_f3_carry.v -- CARRY4 delay semantics, self-checking against the TRANSPORT
// expectation: each output is the carry/xor function of its input pins, each
// pin delayed by its own arc to that output.  PASS requires the GLS_FID model;
// the default prims.v model (specify paths, sample at fire) must FAIL it --
// run_f3.sh runs both, and that failure is the negative control.
// Arcs are set explicitly here; expected times are input time + arc.
//   C1  O1 = S1 ^ CO0 with CO0 = S0 ? cin0 : DI0, cin0 = 1.  S0 and S1 rise
//       together at 1000.  The function is 0 before and after, but S1 reaches
//       O1 after TS1O1 = 205 and S0 after TS0O1 = 400: a hazard pulse
//       1205-1400 (the arrival order the arcs imply).
//   C2  isolated 50 ps pulse on S2 -> O2 (TS2O2 = 228): passes, 2228-2278
//   C3  S3 pulse 3000-3120 then rise 3130 -> O3 (TS3O3 = 233): three edges,
//       the last at 3363, not early
//   C4  CO3 of a 4-bit propagate chain: CIN at 4000 (TCINCO3 = 114) and DI3
//       does not matter (S3 = 1); plus a 40 ps CIN pulse at 5000 reaches CO3
//       as a 40 ps pulse at 5114
//   C5  one CIN edge reaches CO0 after TCINCO0 and O2 after TCINO2 (each output
//       its own arc; both models agree, a sanity row)
`timescale 1ps/1ps
module tb_f3_carry;
    // instance h: hazard on O1 (cin0 = CYINIT = 1, DI0 = 0)
    reg hs0 = 0, hs1 = 0;
    wire h_o1;
    CARRY4 #(.TS1O1(205), .TS0O1(400)) uh (
        .CIN(1'b0), .CYINIT(1'b1), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
        .S0(hs0), .S1(hs1), .S2(1'b0), .S3(1'b0),
        .O0(), .O1(h_o1), .O2(), .O3(), .CO0(), .CO1(), .CO2(), .CO3());
    // instance p: pulses on S2 -> O2, S3 -> O3 (O_k = S_k ^ carry, carry 0)
    reg ps2 = 0, ps3 = 0;
    wire p_o2, p_o3;
    CARRY4 #(.TS2O2(228), .TS3O3(233)) up (
        .CIN(1'b0), .CYINIT(1'b0), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
        .S0(1'b0), .S1(1'b0), .S2(ps2), .S3(ps3),
        .O0(), .O1(), .O2(p_o2), .O3(p_o3), .CO0(), .CO1(), .CO2(), .CO3());
    // instance c: full propagate chain, CIN -> CO3 / CO0 / O2
    reg cin = 0;
    wire c_co3, c_co0, c_o2;
    CARRY4 #(.TCINCO3(114), .TCINCO0(271), .TCINO2(239)) uc (
        .CIN(cin), .CYINIT(1'b0), .DI0(1'b0), .DI1(1'b0), .DI2(1'b0), .DI3(1'b0),
        .S0(1'b1), .S1(1'b1), .S2(1'b1), .S3(1'b1),
        .O0(), .O1(), .O2(c_o2), .O3(), .CO0(c_co0), .CO1(), .CO2(), .CO3(c_co3));

    integer eh = 0, e2 = 0, e3 = 0, ec3 = 0, ec0 = 0, eo2 = 0;
    time th0 = 0, th1 = 0, t2a = 0, t2b = 0, t3 = 0, tc3a = 0, tc3b = 0, tc3c = 0, tc0 = 0, to2 = 0;
    always @(h_o1) if ($time > 500) begin
        eh = eh + 1; if (eh == 1) th0 = $time; if (eh == 2) th1 = $time;
        $display("  h_o1  t=%0d %b", $time, h_o1); end
    always @(p_o2) if ($time > 500) begin
        e2 = e2 + 1; if (e2 == 1) t2a = $time; if (e2 == 2) t2b = $time;
        $display("  p_o2  t=%0d %b", $time, p_o2); end
    always @(p_o3) if ($time > 500) begin
        e3 = e3 + 1; t3 = $time; $display("  p_o3  t=%0d %b", $time, p_o3); end
    always @(c_co3) if ($time > 500) begin
        ec3 = ec3 + 1; if (ec3 == 1) tc3a = $time; if (ec3 == 2) tc3b = $time; if (ec3 == 3) tc3c = $time;
        $display("  c_co3 t=%0d %b", $time, c_co3); end
    always @(c_co0) if ($time > 500 && $time < 4900) begin ec0 = ec0 + 1; tc0 = $time; end
    always @(c_o2)  if ($time > 500 && $time < 4900) begin eo2 = eo2 + 1; to2 = $time; end

    initial begin #1000 hs0 = 1; hs1 = 1; end
    initial begin #2000 ps2 = 1; #50 ps2 = 0; end
    initial begin #3000 ps3 = 1; #120 ps3 = 0; #10 ps3 = 1; end
    initial begin #4000 cin = 1; #600 cin = 0; #400 cin = 1; #40 cin = 0; end  // 4000 rise, 4600 fall, 5000-5040 pulse

    integer fail = 0;
    task chk(input c, input [8*72-1:0] what);
        begin if (!c) begin fail = fail + 1; $display("  FAIL %0s", what); end
              else $display("  ok   %0s", what); end
    endtask
    initial begin
        #8000;
        $display("C1 hazard: %0d edges at %0d, %0d (transport: 2, 1205 and 1400)", eh, th0, th1);
        chk(eh == 2 && th0 == 1000 + 205 && th1 == 1000 + 400, "C1 S0/S1 together: O1 hazard 1205-1400");
        $display("C2 pulse: %0d edges at %0d, %0d (transport: 2, 2228 and 2278)", e2, t2a, t2b);
        chk(e2 == 2 && t2a == 2000 + 228 && t2b == 2050 + 228, "C2 50 ps S2 pulse reaches O2");
        $display("C3 close edges: %0d edges, last %0d (transport: 3, 3363)", e3, t3);
        chk(e3 == 3 && t3 == 3130 + 233, "C3 S3 edge after 3130 lands at 3363, not early");
        $display("C4 CO3: %0d edges at %0d %0d %0d.. (transport: 4, 4114 4714 5114 5154)", ec3, tc3a, tc3b, tc3c);
        chk(ec3 == 4 && tc3a == 4000 + 114 && tc3b == 4600 + 114 && tc3c == 5000 + 114,
            "C4 CIN edges and a 40 ps CIN pulse reach CO3");
        chk(ec0 == 2 && tc0 == 4600 + 271 && eo2 == 2 && to2 == 4600 + 239,
            "C5 CIN reaches CO0 / O2 each by its own arc");
        if (fail) $display("tb_f3_carry FAIL (%0d)", fail); else $display("tb_f3_carry PASS");
        $finish;
    end
endmodule
