`timescale 1ps/1ps
// r22 passive monitor: prints the delivered result bus at every rig lap (rise) and checks it
// is unchanged at the lap's fall. Reads only; drives nothing.
module r22mon;
`include "r22sig.vh"
    wire [31:0] d = {`R22D31, `R22D30, `R22D29, `R22D28, `R22D27, `R22D26, `R22D25, `R22D24, `R22D23, `R22D22, `R22D21, `R22D20, `R22D19, `R22D18, `R22D17, `R22D16, `R22D15, `R22D14, `R22D13, `R22D12, `R22D11, `R22D10, `R22D9, `R22D8, `R22D7, `R22D6, `R22D5, `R22D4, `R22D3, `R22D2, `R22D1, `R22D0};
    integer n; reg [31:0] dr; initial n = 0;
    always @(posedge tb_run.`RIG_LAP) begin n = n + 1; dr = d; $display("R22LAP vec=%0d n=%0d t=%0t data=%h", tb_run.vec, n, $time, d); end
    always @(negedge tb_run.`RIG_LAP) if (n > 0 && d !== dr) $display("R22UNSTABLE vec=%0d n=%0d t=%0t rise=%h fall=%h", tb_run.vec, n, $time, dr, d);
endmodule
