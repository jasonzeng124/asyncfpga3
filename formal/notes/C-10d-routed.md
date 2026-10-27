# C-10d: the verified timing checker on a REAL routed netlist (tracks 10+11)

(Work in progress; scaling section pending.)

## Verdict
Works for ce_pair seed 1 (38-50 arcs per launch): kernel `decide` (`decide +kernel`) checks
the routed instance in seconds. Scaling: see below.

## What checks
    formal/tools/routed2lean/run.sh        # regenerate + compile + axiom audit -> "routed2lean PASS"
