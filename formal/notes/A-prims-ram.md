# A-prims-ram: digital semantics of RAMB18E1 as bd_mem instantiates it

Probe PrimsRam, shard A. Started 2026-10-29 08:39 UTC. North-star goal 1 ("RAMB18E1 if a
design uses them"). Builds on PrimsSeq (`Formal/Core/Prims/SeqFlop.lean`: `ap`, `winVal`,
`EqOn`, `NoRise`, `lastRise`, `kmux`).

STATUS: in progress (plan + data written; Lean being written).

## Plan
1. Read bd_mem.v and its users (bdc/mem.py, bdc/emit.py), the prjxray BRAM SDF, the iverilog
   stand-in (cells/sim/bd_prims_sim.v), B's LibEndMemMlink MemPort.
2. `Formal/Core/Prims/Ram.lean`: Kleene word/address algebra (decoder, read, write, three
   write modes), the timed relation `RamRel`, theorems, non-vacuity witness.
3. `Formal/Core/Prims/RamXray.lean`: the prjxray numbers as data (integer ps).
4. `Formal/Core/Prims/RamBd.lean`: the bundled-data obligation of bd_mem, derived.
