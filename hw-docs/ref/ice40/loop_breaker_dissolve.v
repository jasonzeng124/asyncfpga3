// Non-blackbox pass-through implementation of loop_breaker, used ONLY as a
// `techmap -map` template at the very end of synthesis (see synth.ys).
//
// rtl/common/loop_breaker.sv declares loop_breaker as (* blackbox, keep *) so
// that yosys treats every pin of every library LUT as an opaque boundary and
// cannot "optimize" the deliberate combinational feedback loops. nextpnr,
// however, cannot place a blackbox, so right before write_json each
// loop_breaker cell is techmapped to this trivial implementation, which
// dissolves it into a plain wire (a net alias). No opt pass may run after
// that point.
module loop_breaker (input A, output Y);
  assign Y = A;
endmodule
