# C-8y2: the circuit-safety capstone, generic in the kernel

**Status: IN PROGRESS (draft saved 08:30 UTC).** Shard C, probe 8y2, 2026-10-29.

## Verdict (draft)

- One theorem, `Formal.Net.KCap.kernel_circuit_safe`, proved once over a kernel given as two
  type classes `[KD]` (data) and `[KP]` (obligations). It is C-8s's `gcd_hw_circuit_safe3`
  with every gcd constant made a field; the proof is the gcd proof transcribed once
  (`KernelCap{Defs,Hist,Sound,Safe,CutSpine,Cut,WalkRun,Walk}.lean`, 2900 lines).
- collatz (one data argument, the shape C-8y's text-copy pipeline refused) goes through it:
  `collatz_circuit_safe` (third kernel at circuit level; token level was C-8v's).
- gcd_hw and ipow instances: see below (pending the lead's build of their chains).
