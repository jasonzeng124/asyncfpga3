/-!
# Formal.Core.Prims.Xray — prjxray-db delay bands for the combinational primitives

Shard A, probe PrimsComb. Core Lean only (no Mathlib).
Notes: `formal/notes/A-prims-comb.md`.

## Source (transcribed by hand, every number checked against the file)

`$TC/openxc7/share/nextpnr/prjxray-db/zynq7/timings/slicel.sdf` (the prjxray-db
copy shipped with the toolchain that builds every design here; `TIMESCALE 1ns`,
transcribed in integer ps). Cells used:

* `SELMUX2_1` instances `SLICEL/F7AMUX`, `SLICEL/F7BMUX`, `SLICEL/F8MUX`
  (IOPATH `0`, `1`, `S0` -> `OUT`): MUXF7 (A/B halves) and MUXF8.
* `CARRY4` (IOPATH `CIN`, `CYINIT`, `S0..S3` -> `O0..O3`, `CO0..CO3`), and
  `CARRY4_O5` (IOPATH `DI0..DI3` -> ..., the DI variant where DI is driven by the
  LUT's O5, the one yosys/nextpnr use for an adder whose DI comes from a LUT).
  prjxray also has `CARRY4_AX/BX/CX/DX` and `_LBOTH`/`_LFF` variants with slightly
  different DI and CIN numbers; they are not transcribed here.
* `LUT6` `SLICEL/A6LUT` (A1..A6 -> O6) and `LUT5` `SLICEL/A5LUT` (A1..A5 -> O5).

`slicem.sdf` has the same arcs with numbers that differ by a few ps; only SLICEL
is transcribed.

## Meaning of the four numbers (the corner rule)

A prjxray SDF triple is `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`
(`prjxray/utils/makesdf.py`; `prjxray/prjxray/timing.py`). These are the
**fast and slow process corners**, each with a min and a max. They are **not**
rise and fall: prjxray-db has no rise/fall split at all, so every model here uses
ONE band per arc for both edges (PROGRAM.md "per-edge windows where the data
distinguishes them, otherwise one shared band": the data does not distinguish
them). A delay at a fixed corner lies in `[min, max]` of that corner, and an
analysis never takes one arc from the fast corner and another from the slow one
(`Band.lo`/`Band.hi` take ONE `Corner`).
-/

namespace Formal.Core.Prims

/-- Process corner of a prjxray-db timing triple. -/
inductive Corner where
  | fast
  | slow
  deriving DecidableEq, Repr

/-- One prjxray-db arc, in integer ps: `(fmin::fmax)(smin::smax)`. -/
structure Band where
  fmin : Int
  fmax : Int
  smin : Int
  smax : Int
  deriving DecidableEq, Repr

namespace Band

/-- Lower bound of the arc at corner `c`. -/
def lo (b : Band) : Corner → Int
  | .fast => b.fmin
  | .slow => b.smin

/-- Upper bound of the arc at corner `c`. -/
def hi (b : Band) : Corner → Int
  | .fast => b.fmax
  | .slow => b.smax

/-- `d` is an admissible delay for this arc at corner `c`. -/
def In (b : Band) (c : Corner) (d : Int) : Prop := b.lo c ≤ d ∧ d ≤ b.hi c

instance (b : Band) (c : Corner) (d : Int) : Decidable (b.In c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Well-formed: positive, min ≤ max at each corner, fast below slow. -/
def ok (b : Band) : Bool :=
  decide (0 < b.fmin) && decide (b.fmin ≤ b.fmax) && decide (b.smin ≤ b.smax) &&
  decide (b.fmin ≤ b.smin) && decide (b.fmax ≤ b.smax)

end Band

/-! ## MUXF7 / MUXF8 (`SELMUX2_1`): arcs `I0 -> O`, `I1 -> O`, `S -> O` -/

/-- Arcs of one 2:1 slice mux: data `I0`, data `I1`, select `S`. -/
structure MuxArcs where
  i0 : Band
  i1 : Band
  s : Band
  deriving DecidableEq, Repr

/-- `SLICEL/F7AMUX`: `0 OUT (0.053::0.067)(0.153::0.19)`, `1 OUT (0.055::0.069)(0.156::0.193)`,
`S0 OUT (0.085::0.106)(0.222::0.276)`. -/
def f7amux : MuxArcs := ⟨⟨53, 67, 153, 190⟩, ⟨55, 69, 156, 193⟩, ⟨85, 106, 222, 276⟩⟩

/-- `SLICEL/F7BMUX`: `(0.062::0.077)(0.175::0.217)`, `(0.065::0.081)(0.18::0.223)`,
`(0.093::0.115)(0.239::0.296)`. -/
def f7bmux : MuxArcs := ⟨⟨62, 77, 175, 217⟩, ⟨65, 81, 180, 223⟩, ⟨93, 115, 239, 296⟩⟩

/-- `SLICEL/F8MUX`: `(0.023::0.028)(0.083::0.104)`, `(0.019::0.024)(0.076::0.094)`,
`(0.08::0.1)(0.22::0.273)`. -/
def f8mux : MuxArcs := ⟨⟨23, 28, 83, 104⟩, ⟨19, 24, 76, 94⟩, ⟨80, 100, 220, 273⟩⟩

theorem muxArcs_ok :
    (f7amux.i0.ok && f7amux.i1.ok && f7amux.s.ok && f7bmux.i0.ok && f7bmux.i1.ok &&
      f7bmux.s.ok && f8mux.i0.ok && f8mux.i1.ok && f8mux.s.ok) = true := by decide

/-- In every slice mux, at both corners, the select arc is the slowest arc:
its minimum exceeds both data arcs' maxima. (This is what makes the
"select-first" glitch of `Muxf.lean` impossible and the "data-first" one possible
for these cells.) -/
theorem sel_slowest (m : MuxArcs) (hm : m = f7amux ∨ m = f7bmux ∨ m = f8mux) (c : Corner) :
    m.i0.hi c < m.s.lo c ∧ m.i1.hi c < m.s.lo c := by
  rcases hm with h | h | h <;> subst h <;> cases c <;> decide

/-! ## CARRY4 -/

/-- CARRY4 input pins (DI pins: the `CARRY4_O5` variant). -/
inductive CPin where
  | cin | cyinit | s0 | s1 | s2 | s3 | di0 | di1 | di2 | di3
  deriving DecidableEq, Repr

/-- CARRY4 output pins. -/
inductive COut where
  | o0 | o1 | o2 | o3 | co0 | co1 | co2 | co3
  deriving DecidableEq, Repr

/-- The prjxray arc `p -> o` of SLICEL `CARRY4` / `CARRY4_O5`, or `none` where
prjxray lists no arc (then `o` does not depend on `p`: see
`Carry4.support_matches_xray`). -/
def carry4Arc : CPin → COut → Option Band
  -- CARRY4: CIN
  | .cin, .co0 => some ⟨76, 100, 206, 271⟩
  | .cin, .co1 => some ⟨45, 56, 127, 157⟩
  | .cin, .co2 => some ⟨65, 81, 184, 228⟩
  | .cin, .co3 => some ⟨39, 49, 92, 114⟩
  | .cin, .o0 => some ⟨54, 80, 150, 222⟩
  | .cin, .o1 => some ⟨91, 113, 269, 334⟩
  | .cin, .o2 => some ⟨65, 81, 192, 239⟩
  | .cin, .o3 => some ⟨90, 112, 252, 313⟩
  -- CARRY4: CYINIT
  | .cyinit, .co0 => some ⟨165, 206, 432, 536⟩
  | .cyinit, .co1 => some ⟨144, 180, 398, 494⟩
  | .cyinit, .co2 => some ⟨169, 210, 477, 592⟩
  | .cyinit, .co3 => some ⟨173, 215, 467, 580⟩
  | .cyinit, .o0 => some ⟨147, 183, 388, 482⟩
  | .cyinit, .o1 => some ⟨176, 219, 482, 598⟩
  | .cyinit, .o2 => some ⟨167, 208, 471, 584⟩
  | .cyinit, .o3 => some ⟨190, 236, 518, 642⟩
  -- CARRY4: S0..S3
  | .s0, .co0 => some ⟨89, 118, 258, 340⟩
  | .s0, .co1 => some ⟨118, 156, 329, 433⟩
  | .s0, .co2 => some ⟨144, 190, 389, 512⟩
  | .s0, .co3 => some ⟨142, 187, 386, 508⟩
  | .s0, .o0 => some ⟨60, 79, 170, 223⟩
  | .s0, .o1 => some ⟨96, 127, 304, 400⟩
  | .s0, .o2 => some ⟨136, 180, 398, 523⟩
  | .s0, .o3 => some ⟨156, 206, 442, 582⟩
  | .s1, .co1 => some ⟨126, 166, 356, 469⟩
  | .s1, .co2 => some ⟨153, 202, 417, 548⟩
  | .s1, .co3 => some ⟨146, 192, 401, 528⟩
  | .s1, .o1 => some ⟨56, 74, 156, 205⟩
  | .s1, .o2 => some ⟨143, 189, 424, 558⟩
  | .s1, .o3 => some ⟨163, 215, 470, 618⟩
  | .s2, .co2 => some ⟨72, 95, 222, 292⟩
  | .s2, .co3 => some ⟨106, 140, 286, 376⟩
  | .s2, .o2 => some ⟨57, 75, 171, 226⟩
  | .s2, .o3 => some ⟨90, 119, 251, 330⟩
  | .s3, .co3 => some ⟨106, 140, 289, 380⟩
  | .s3, .o3 => some ⟨54, 71, 172, 227⟩
  -- CARRY4_O5: DI0..DI3
  | .di0, .co0 => some ⟨85, 112, 250, 329⟩
  | .di0, .co1 => some ⟨103, 136, 301, 396⟩
  | .di0, .co2 => some ⟨129, 171, 360, 474⟩
  | .di0, .co3 => some ⟨129, 171, 346, 456⟩
  | .di0, .o1 => some ⟨94, 124, 256, 337⟩
  | .di0, .o2 => some ⟨122, 161, 369, 486⟩
  | .di0, .o3 => some ⟨143, 189, 414, 545⟩
  | .di1, .co1 => some ⟨92, 122, 286, 376⟩
  | .di1, .co2 => some ⟨118, 156, 349, 459⟩
  | .di1, .co3 => some ⟨115, 152, 336, 443⟩
  | .di1, .o2 => some ⟨110, 146, 358, 471⟩
  | .di1, .o3 => some ⟨131, 174, 404, 532⟩
  | .di2, .co2 => some ⟨71, 94, 219, 289⟩
  | .di2, .co3 => some ⟨88, 116, 246, 324⟩
  | .di2, .o3 => some ⟨98, 129, 282, 372⟩
  | .di3, .co3 => some ⟨88, 116, 248, 327⟩
  | _, _ => none

def CPin.all : List CPin := [.cin, .cyinit, .s0, .s1, .s2, .s3, .di0, .di1, .di2, .di3]
def COut.all : List COut := [.o0, .o1, .o2, .o3, .co0, .co1, .co2, .co3]

/-- Every transcribed CARRY4 band is well formed. -/
theorem carry4Arc_ok :
    (CPin.all.all fun p => COut.all.all fun o =>
      match carry4Arc p o with | some b => b.ok | none => true) = true := by decide

/-- Number of transcribed arcs: 36 (CARRY4) + 16 (CARRY4_O5). -/
theorem carry4Arc_count :
    ((CPin.all.flatMap fun p => COut.all.filterMap fun o => carry4Arc p o).length) = 52 := by
  decide

/-- The smallest CARRY4 arc at any corner is 39 ps (CIN -> CO3, fast min); the
`S0 -> O0` arc is at least 60 ps (fast min). -/
theorem carry4_min_arc :
    (CPin.all.all fun p => COut.all.all fun o =>
      match carry4Arc p o with | some b => decide (39 ≤ b.fmin) | none => true) = true ∧
    carry4Arc .s0 .o0 = some ⟨60, 79, 170, 223⟩ := by
  decide

/-! ## LUT6 (O6) and LUT5 (O5) of `SLICEL/A6LUT`, `SLICEL/A5LUT` -/

/-- `A1..A6 -> O6`: all six identical, `(0.045::0.056)(0.1::0.124)`. -/
def lutO6Arc (_k : Fin 6) : Band := ⟨45, 56, 100, 124⟩

/-- `A_k -> O5` (k = 1..5, index `k-1`). -/
def lutO5Arc : Fin 5 → Band
  | ⟨0, _⟩ => ⟨44, 55, 122, 152⟩
  | ⟨1, _⟩ => ⟨44, 55, 122, 152⟩
  | ⟨2, _⟩ => ⟨42, 52, 121, 150⟩
  | ⟨3, _⟩ => ⟨46, 57, 121, 150⟩
  | ⟨4, _⟩ => ⟨48, 60, 95, 118⟩

end Formal.Core.Prims
