`timescale 1ns/1ps
// Compare the SYNTHESISED netlist against Verilog's own `*`.  Both run in the
// same simulator on the same vectors, so a mismatch is the mapping and
// nothing else -- no board, no bitstream, no place and route involved.
module tb_mult32;
  reg [31:0] a, b;
  wire [31:0] p;
  reg [31:0] want;
  integer i, bad = 0, n = 0;
  mult32 dut (.a(a), .b(b), .p(p));

  task check;
    begin
      #1;
      want = a * b;
      n = n + 1;
      if (p !== want) begin
        bad = bad + 1;
        if (bad <= 12)
          $display("  MISMATCH a=%0d b=%0d got=%0d want=%0d", a, b, p, want);
      end
    end
  endtask

  initial begin
    // the exact operands the board disagreed on, first
    a = 4;          b = 4;          check;
    a = 5;          b = 5;          check;
    a = 7;          b = 7;          check;
    a = 3;          b = 3;          check;
    a = 65537;      b = 65537;      check;
    a = 1000000;    b = 1000000;    check;
    a = 32'hAAAAAAAA; b = 32'hAAAAAAAA; check;
    $display("directed: %0d of %0d wrong", bad, n);

    bad = 0; n = 0;
    for (i = 0; i < 4000; i = i + 1) begin
      a = $random; b = $random; check;
    end
    $display("random:   %0d of %0d wrong", bad, n);
    $finish;
  end
endmodule
