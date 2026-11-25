# Negative controls for plain_pass.py (shard A, 2026-11-18)

Each script runs plain_pass.py on research's countloop fixture (copied to /tmp/claude-0/pp/countloop.mlir) with one
defect injected. Each must exit 2 with OUT = IN. Results, 2026-11-18 21:57 UTC:

| script | defect injected | refused by |
|---|---|---|
| (command line) countloop with `cmpi sgt` -> `cmpi ne` in the guard | a real bug: n = INT_MIN enters the loop | the certificate search (untrusted); `PassInst.control_guard_ne` shows Lean's `check` is false too |
| plain_pass_badcert.py | certificate without the NotMin class | LEAN (`decide` proves check = false) |
| plain_pass_bad_ringdec.py | ring_dec's output corrupted: the decrement constant -1 -> -2 | rules_iso (untrusted) |
| plain_pass_bad_ringdec_forced_iso.py | the same, with rules_iso forced to "accept" using the correct maps | LEAN (`decide` proves renCheck = false) |

So the two untrusted searches can be wrong in either direction, and the acceptance still rests on Lean.
Paths inside the scripts are this session's; adjust them to rerun.
