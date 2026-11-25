// tb_c2_saf.v -- the GLS's sample-at-fire module path lets a 6 ps a/b overlap
// latch bd_c2 if any function change happened within the last 124 ps.
// Lean: bd_c2_two_change_hazard (Kleene X); an inertial channel (Core/Delay/
// Inertial) would filter both the 5 ps glitch and the 6 ps overlap.
`timescale 1ps/1ps
module tb_c2_saf;
    reg a = 0, b = 0, rst = 1;
    wire q;
    SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8))
        c (.A1(a), .A2(b), .A3(q), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(q), .O5());
    always @(q) $display("%0t q=%b", $time, q);
    integer pre;
    initial begin
        #2000 rst = 0; b = 1; #2000;
        for (pre = 0; pre < 2; pre = pre + 1) begin
            $display("--- trial %0d: %s", pre, pre ? "5 ps glitch on a at T, then a up at T+120, b down at T+126"
                                                : "no glitch: a up at T+120, b down at T+126");
            if (pre) begin a = 1; #5 a = 0; #115; end else #120;
            a = 1; #6 b = 0; #2000;
            $display("final q=%b", q);
            rst = 1; a = 0; b = 0; #1000 rst = 0; b = 1; #2000;
        end
        $finish;
    end
endmodule
