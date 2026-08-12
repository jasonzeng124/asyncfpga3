// ---------------------------------------------------------------------------
// bd_arb.v -- the arbitration cell, and the arbiter built on it.
//
// HIGHEST RISK CELL IN THE LIBRARY.  Read the risk note before using it.
// ---------------------------------------------------------------------------
//
// One state node, read straight and complemented:
//
//     q  = C(r1, ~r2)
//     g1 = r1 .  q
//     g2 = r2 . ~q
//
// A C-element is exactly an SR latch whose set is r1.~r2 and whose reset is
// ~r1.r2 -- the two conditions under which one channel is unambiguously
// asking alone.  On a tie both are false, so q holds and the previous winner
// is asked to give way first.
//
// The complement costs nothing: ~q is a bubble on the pin that reads it, and
// an inverter is never a cell on this fabric.  So there is one feedback wire
// in the whole element and one logic level in its loop.  The textbook NAND
// mutex has two of each, and loop delay is what sets the resolution time
// constant.
//
// Exclusion is structural FOR A SETTLED q.  Exactly one of q and ~q is high,
// so at most one grant can be; the two grant LUTs read the same net, and no
// amount of routing skew changes which value it holds.
//
// Exclusion DURING HANDOVER is a different claim and a weaker one.  The two
// grants reach the same net through different arcs, so the ordering has to be
// checked rather than asserted -- and in one of the two directions it holds by
// a small margin that only routing supplies.  See the finding at the bottom of
// this header, and tb_arb, which counts the overlap in both timing regimes.
//
// Because q only ever moves while exactly one request is up, sustained
// contention forces alternation.
//
// -- THIS IS NOT A MUTEX ----------------------------------------------------
//
// It is the decision element of a mutex and nothing else.  A Seitz mutex is
// that element plus an analog metastability filter, and the filter is the
// part that makes the name mean something.
//
// A LUT is a digital mux tree: it will propagate whatever voltage its input
// reaches, including a metastable intermediate.  The decision element is
// buildable in one LUT; the filter is not buildable at all.  So on
// near-simultaneous requests this cell can not only go metastable, it can
// hand a metastable level straight to its grant outputs -- the one failure
// mode the analog filter exists to prevent.
//
// A plain tie (both requests rising together from idle) is resolved
// deterministically, since set and reset are both false and q simply holds.
// What remains is a runt on the set or reset condition: r1 and r2 moving in
// opposite senses within one loop delay of each other, driving the loop for
// less time than it needs to commit.
//
// What is available instead is resolution time -- metastability decays
// exponentially, so added stages buy MTBF without a true filter.  That turns
// "is this correct" into "what is the failure rate", and the failure rate
// MUST BE MEASURED ON HARDWARE.  verify/MTBF.md is the procedure.  Nothing
// in this tree discharges the obligation -- not one gate, not all of them.
//
// -- placement --------------------------------------------------------------
//
// Both grants must sit in ONE fractured site.  Two separate LUTs have
// identical intrinsic delay but land in different sites with different
// routing, and routing on this part moves about a nanosecond between builds.
// One fractured site has a fixed O5-versus-O6 delta of tens of picoseconds,
// identical every time.  A constant asymmetry only biases tie-breaking; an
// asymmetry that moves between builds means a measured MTBF does not transfer
// to the next bitstream, which would make the whole characterisation
// worthless.
// ---------------------------------------------------------------------------

`default_nettype none

// -- the decision element alone ------------------------------------ 2 LUTs -
// q may come up either way -- it only decides who wins the first tie -- but
// it must come up DEFINED, because an intermediate q is exactly the failure
// the risk note above is about.  Here rst drives it to 1.
module bd_arbcell
    (input  wire  r1,
     input  wire  r2,
     input  wire  rst,
     output wire  g1,
     output wire  g2);

    wire q;
    bd_c2n_set ustate (.a(r1), .b(r2), .rst(rst), .q(q));

    // Both grants from one fractured site, reading the routed-back q.
    LUT6_2 #(.INIT(64'h0C0C_0C0C_A0A0_A0A0)) ugrant (
        .I0(r1), .I1(r2), .I2(q), .I3(1'b0), .I4(1'b0), .I5(1'b1),
        .O5(g1), .O6(g2));
endmodule

// ---------------------------------------------------------------------------
// bd_arbiter -- the arbitration cell in front of a plain merge, with nothing
// between them.
//
//     q, R0   one fractured LUT: q = C(r1,~r2) and R0 = g1 + g2
//     g1, g2  one fractured LUT: r1.q and r2.~q
//     A1, A2  C(g1, A0) and C(g2, A0)
//
// R0 pairs with the state node rather than with the grants because
// r1.q + r2.~q is a function of the same three wires, and adding rst still
// only makes four.  It reads the routed-back copy of q -- the same net the
// grants read -- so the three outputs stay consistent with each other.
//
// Four LUTs for a two-way arbiter.  That number is derived from the packing
// rule; verify/lutcost.py is what confirms it against a routed netlist.
//
// The separate exclusion stage an earlier draft carried is gone.  It was a
// patch on a broken cell: the cross-coupled element it protected could reach
// a stable both-granted state, so something downstream had to catch it.  With
// one state node there is nothing to catch, and an exclusion stage built from
// LUTs would not help with a metastable q either -- it would be fed the same
// intermediate level.  What is still worth buying with an extra stage is
// resolution time, which is a different thing from exclusion.
//
// Control only, matching the schematic.  A data-carrying arbitrated merge
// adds bd_merge's select LUT, data mux and matched delay on R0.
//
// ---------------------------------------------------------------------------
// THE ARBITER AS SPECIFIED DOES NOT MEET THE MERGE'S PRECONDITION, so this
// cell is NOT the arbiter as specified.  It holds q on ack, unconditionally,
// and there is no way to ask for the unheld node.
//
// That is a deliberate departure from "report, do not silently patch", and
// the reason is that this cell has one consumer that cannot read a note: a
// compiler backend emits it once per contended resource, thousands of times,
// and nobody reads a parameter default.  A defect that is opt-out in a
// library is a defect that ships.  The finding below is the report; the
// constant is the patch; the two are not in tension because both are here.
//
// bd_merge's own header states the obligation, and it is stronger than
// exclusivity: the second input may not assert until the first transaction
// has FULLY COMPLETED, "otherwise C(y_req, z_ack) fires into a still-high
// z_ack and acknowledges a token the merge never carried".  Exclusive grants
// do not give that.  An arbiter under sustained contention gives precisely
// the opposite.
//
// Traced on this library (verify/probes/arb_handover.v), both clients
// asking, r1 winning:
//
//     4055   g1 rises,  R0 rises
//     6000   server acknowledges: A0 high
//     6056   A1 = C(g1, A0) rises -- client 1 is served
//     8000   client 1 enters return-to-zero: r1 falls
//     8124   q flips
//     8152   g1 falls
//     8180   g2 rises -- WITH A0 STILL HIGH
//     8236   A2 = C(g2, A0) rises
//
// Client 2 is acknowledged at 8236 for a transaction the server never began.
// R0 = g1 + g2 never returned to zero either: the OR bridges straight across
// the handover, so the server sees one long request where two clients were
// served.  A run of tb_arb on the unfixed cell shows exactly that -- eighty
// client completions against forty server transactions.
//
// The mechanism is that q is allowed to flip during the OTHER client's
// return-to-zero phase.  That is what makes the handover fast, and it is also
// what makes it early.
//
// Holding q while A0 is high fixes it.  Then g1 falls when r1 falls, R0
// falls with it, the server drops A0, A1 falls, client 1 completes -- and only
// then does q flip and g2 rise.  A0 is one more pin on the state node, and
// because R0 is a function of the pins that node already has, the pair is
// still five distinct inputs: the fix is a different constant, not a different
// cost.  Still four LUTs.  (INIT 64'hFFF0_FFB2_ACAC_ACAC, derived and proved
// as ARB_STATE_R0_HOLD in verify/inits.py.)
//
// It also removes a second, narrower problem.  Grant exclusion during handover
// is not quite structural in the unfixed cell: on the r2-to-r1 direction the
// falling grant travels one fall arc (O6, 124 ps) while the rising grant
// travels two rise arcs (q at 56, then O5 at 52), so with zero routing the
// rising grant wins by 16 ps and both grants are briefly high.  Real routing
// puts a full hop in the q feedback and the ordering is restored with about
// twenty times the margin -- so this is a post-route check, not a defect, but
// it is a timing dependency and the review presents exclusion as structural.
// With q frozen on A0 the two grants are separated by an entire server
// round-trip and the question stops arising.
//
// -- WHAT THE HOLD DOES NOT DO ----------------------------------------------
//
// It does not make fairness unconditional.  q re-evaluates at A0-fall; the
// losing client's request is already up, and the winning client cannot
// re-raise its own until A1 has fallen, which is strictly later.  So
// alternation holds by one arc of margin, not by construction.  tb_arb
// measures the alternation count rather than assuming it.
//
// IT DOES NOT MAKE THE MUTEX UNRACEABLE, and nothing here can.  The two
// problems above are a protocol violation and an arc ordering; both are
// digital races with digital fixes.  The third failure mode is not: r1 and r2
// moving in OPPOSITE SENSES within one loop delay drive the decision loop for
// less time than it needs to commit, and q can then sit at an intermediate
// level and hand that level straight to the grants.  No arrangement of LUTs
// removes it, because the analog filter that would is not buildable on this
// fabric.
//
// The hold does not even relocate that race to a safe place.  q is frozen
// while A0 is high, so the evaluation window opens at A0-fall -- and a request
// arriving coincident with that edge is exactly the runt condition.  What the
// hold plausibly buys is APERTURE: q is live only between A0-fall and the next
// grant, instead of continuously, so there are fewer instants at which a race
// can land.  That is a rate argument, not a structural one, and it is not
// measured.
//
// So exclusion has three tiers and they must not be quoted as one:
//
//   settled q      structural.  Exactly one of q and ~q is high and both
//                  grants read the same net.  No timing argument.
//   during handover  structural WITH THE HOLD.  The grants are separated by a
//                  server round-trip rather than racing within ~100 ps.
//   metastable q   NOT EXCLUDED, at a rate that must be measured.  This is
//                  what verify/MTBF.md exists for, and it is a property of
//                  arbitration itself, not a defect of this cell.
//
// On the one lever that sets the third tier's rate, this construction is
// already at the optimum: resolution time is governed by loop delay, and there
// is one logic level and one feedback wire in this loop where the textbook
// NAND mutex has two of each.  The remaining lever belongs to the consumer --
// metastability decays exponentially, so a grant read N hops downstream has
// had N hops to resolve.  Four-phase bundled data puts a full handshake
// between the decision and its use, which is many hops.  A CONSUMER MUST NOT
// READ A GRANT WITHIN ONE LOOP DELAY OF THE DECISION; that is the cell's
// obligation on its user, and it is the only one.
// ---------------------------------------------------------------------------
module bd_arbiter
    (input  wire  rst,
     input  wire  r1,
     output wire  A1,
     input  wire  r2,
     output wire  A2,
     output wire  R0,
     input  wire  A0,
     output wire  g1,
     output wire  g2);

    wire q;

    // q = rst + C(r1,~r2)   on O6;   R0 = r1.q + r2.~q   on O5.
    // I4 carries A0, so q additionally freezes while the resource is
    // acknowledging.  Same site, same cost as the unheld node -- the hold is
    // a different constant, not a different price.
    (* keep *) LUT6_2 #(.INIT(64'hFFF0_FFB2_ACAC_ACAC)) ustate (
        .I0(r1), .I1(r2), .I2(q), .I3(rst), .I4(A0), .I5(1'b1),
        .O5(R0), .O6(q));

    LUT6_2 #(.INIT(64'h0C0C_0C0C_A0A0_A0A0)) ugrant (
        .I0(r1), .I1(r2), .I2(q), .I3(1'b0), .I4(1'b0), .I5(1'b1),
        .O5(g1), .O6(g2));

    // From here down this is the plain merge, unchanged.  Safe for the same
    // reason: the grants are exclusive, so a plain OR of them is a legal
    // request and C(g, A0) per input is a legal acknowledge.
    bd_c2 ua1 (.a(g1), .b(A0), .rst(rst), .q(A1));
    bd_c2 ua2 (.a(g2), .b(A0), .rst(rst), .q(A2));
endmodule

`default_nettype wire
