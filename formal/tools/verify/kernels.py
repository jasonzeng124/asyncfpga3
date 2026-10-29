"""Per-kernel configuration of formal/tools/verify (probe C-vk).

Everything a new kernel needs is one entry here (see formal/notes/C-vk-verify.md):

  mlir     fixture name: build/frontend/<mlir>/comp/handshake_transformed.mlir if present,
           else cloud/fixtures/frontend/<mlir>/comp/handshake_transformed.mlir
  c        C reference, repo-relative (its directory must hold the .h it includes)
  func     the C function's name; its arguments are the MLIR function's data arguments,
           in order, each an `in_int_t` (int) and the result an int
  vectors  input vectors, as signed C ints (chosen to avoid degenerate answers)
  domain   python predicate on a vector: where the C reference is the specification
  K        Lean base name (Formal/Net/<K>Hw.lean ...); ns: the Lean namespace dfimport
           writes; dfargs: dfimport's naming options (None = its gcd defaults)
  proof    hand-written token-level proof files under formal/lean (optional), the main
           theorem, and `lean_ref`, a Lean term evaluating the hand transcription on a
           vector ({0}, {1} = the inputs as i32 bit patterns) -> Option Nat
  capstone the circuit-level main module and theorem (optional; only kernels capnet.py
           has a PROFILE for can be regenerated)
  autoc    the C file stage 2e (formal/tools/autoproof) transcribes, if not `c` (optional;
           gcd: `c` is Euclid, a different algorithm, so 2e uses the binary gcd)
"""

KERNELS = {
    "gcd": dict(
        mlir="gcd", c="formal/tools/verify/ref/gcd.c", func="gcd",
        autoc="formal/tools/autoproof/ref/gcd_binary.c",
        vectors=[(12, 18), (35, 14), (48, 180), (0, 7), (9, 0), (1071, 462), (17, 5),
                 (64, 24), (100000007, 30000001)],
        domain=lambda v: all(0 <= x < 2 ** 31 for x in v),
        K="GcdHw", ns="Formal.Net.GcdHw.Gcd", dfargs=None,
        proof=["Formal/Net/GcdHwProof.lean"],
        theorem="Formal.Net.GcdHw.Gcd.gcd_hw_graph_computes_gcdC",
        lean_ref="Formal.Net.GcdHw.Gcd.gcdC 100000 {0} {1}",
        capstone=dict(profile="gcd", module="Formal.Net.CapstoneWalk",
                      theorem="Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe3", compat=True,
                      gen=[("links", "CapstoneLinks.lean"), ("net", "CapstoneNet.lean")]),
    ),
    "ipow": dict(
        mlir="ipow", c="kernels/ipow/ipow.c", func="ipow",
        vectors=[(3, 7), (2, 10), (-3, 5), (5, 0), (7, -2), (0, 3), (1, 31), (3, 33), (-1, 6)],
        domain=lambda v: True,
        K="IpowHw", ns="Formal.Net.IpowHw",
        dfargs=["--ns", "Formal.Net.IpowHw", "--graph-module", "Formal.Net.IpowHw",
                "--label", "ipow_ps", "--short", "ipow"],
        proof=["Formal/Net/IpowHwProof.lean"],
        theorem="Formal.Net.IpowHw.ipow_hw_graph_computes_ipowC",
        lean_ref="Formal.Net.IpowHw.ipowC 100 {0} {1}",
        capstone=dict(profile="ipow", module="Formal.Net.IpowCapMain",
                      theorem="Formal.Net.IpowCap.ipow_circuit_safe3", compat=False,
                      gen=[("links", "IpowCapLinks.lean"), ("ring", "IpowCapRing.lean"),
                           ("net", "IpowCapNet.lean")]),
    ),
    "collatz": dict(
        mlir="collatz", c="kernels/collatz/collatz.c", func="collatz",
        vectors=[(6,), (7,), (1,), (27,), (97,)],
        domain=lambda v: v[0] >= 1,      # C loops forever on 0 and some negatives
        K="CollatzHw", ns="Formal.Net.CollatzHw",
        dfargs=["--ns", "Formal.Net.CollatzHw", "--graph-module", "Formal.Net.CollatzHw",
                "--label", "collatz", "--short", "collatz"],
        proof=["Formal/Net/CollatzHwProof.lean"],
        theorem="Formal.Net.CollatzHw.collatz_hw_graph_computes_collatzC",
        lean_ref="Formal.Net.CollatzHw.collatzC 1000 {0}",
        capstone=None,
    ),
    "xorshift": dict(
        mlir="xorshift", c="kernels/xorshift/xorshift.c", func="xorshift",
        vectors=[(-1831433054, 4), (1, 1), (123456789, 3), (5, 0), (-7, 2)],
        domain=lambda v: True,
        K="XorshiftHw", ns="Formal.Net.XorshiftHw",
        dfargs=["--ns", "Formal.Net.XorshiftHw", "--graph-module", "Formal.Net.XorshiftHw",
                "--label", "xorshift", "--short", "xorshift"],
        proof=None, theorem=None, lean_ref=None, capstone=None,
    ),
    # added by C-vk2: a kernel with no hand proof, nested loops and early returns; its all-inputs
    # theorem comes only from stage 2e (generated)
    "isprime": dict(
        mlir="isprime", c="kernels/isprime/isprime.c", func="isprime",
        vectors=[(97,), (91,), (2,), (1,), (7919,), (-5,), (49,)],
        domain=lambda v: True,
        K="IsprimeHw", ns="Formal.Net.IsprimeHw",
        dfargs=["--ns", "Formal.Net.IsprimeHw", "--graph-module", "Formal.Net.IsprimeHw",
                "--label", "isprime", "--short", "isprime"],
        proof=None, theorem=None, lean_ref=None, capstone=None,
    ),
}
