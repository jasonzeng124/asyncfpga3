# C-12a: C-element and arbiter checks in a SAT/SMT model checker

Status: IN PROGRESS (notes kept current as work proceeds).

Tools installed (pip, python3.13): z3-solver 5.3.2 (BMC, k-induction, Spacer/IC3
via CHC), cvc5 1.4.2 (python), python-sat 1.9.dev17. apt: nusmv / yices2 not
in the archive; cvc5/boolector are (not needed). yosys-smtbmc exists in the
openXC7 toolchain but has no delay model for combinational loops (not used).
