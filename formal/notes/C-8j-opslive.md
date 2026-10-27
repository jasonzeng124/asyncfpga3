# C-8j: finishing operator composition (track 8, Phase 3)

Status: IN PROGRESS (notes kept current as I go).

## Verdict (so far)

1. **Non-vacuity of `gcd_circuit`: done, and it exposed that the 8b graph is
   only live at `a = 0`.** `gcd_witness` (explicit run, every hypothesis of
   `gcd_circuit` checked, `out` latches `gcd 0 b = b` at t = 23, for every b).
   `gcd_stuck` / `gcd_no_token`: for every `a ≠ 0` (entry condition) NO run
   satisfying the hypotheses ever requests `out`. So `gcd_circuit` is true for
   `a ≠ 0` only because the circuit deadlocks: the hand-drawn graph has no
   storage on its data loop, and the loop's acknowledge cycle
   `hA.ack ← hA2.ack ← jA.ack ← aT.ack ← a1.ack ← backA.ack ← hA.ack` can never
   fire.

## Files

- `formal/lean/Formal/Net/OpsWitness.lean`: `GcdHyps` (all hypotheses of
  `gcd_circuit` bundled), `gcd_circuit_hyps`, the run table, `gcd_witness`,
  `gcd_witness_value`.
- `formal/lean/Formal/Net/OpsLive.lean`: `gcd_loop_stuck`, `gcd_stuck`,
  `gcd_no_token`.
- `formal/lean/Wip/C8j/gcd_run.py`: unit-delay simulator of the network;
  `-lean` prints the table (proves nothing; Lean re-checks every step).

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    # needs 8f's oleans (Ops, OpsFork, OpsJoin, OpsSteer, OpsMux, OpsGcd) and KahnGcd
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/OpsWitness.olean Formal/Net/OpsWitness.lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/OpsLive.olean Formal/Net/OpsLive.lean
