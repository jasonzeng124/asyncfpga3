/-!
# Formal.Core.Prims.Xray — types for prjxray-db delay bands of the slice primitives

Shard A, probe PrimsComb (north star 1). Core Lean only (no Mathlib).
Notes: `formal/notes/A-prims-comb.md`. The numbers are in the GENERATED
`Formal.Core.Prims.XrayData` (from prjxray-db `zynq7/timings/slicel.sdf`,
`slicem.sdf`; generator `Wip/PrimsComb/xray2lean.py`, sha256 of the inputs in
that file's header). Nothing here is transcribed by hand.

## Meaning of the four numbers (the corner rule)

A prjxray SDF triple is `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`
(`prjxray/utils/makesdf.py`, the `IOPATH` template). These are the **fast and
slow process corners**, each with a min and a max. They are **not** rise and
fall: prjxray-db has no rise/fall split, so every arc here has ONE band per
corner for both edges (PROGRAM.md: "per-edge windows where the data distinguishes
them, otherwise one shared band" — the data does not distinguish them). A delay
at corner `c` lies in `[lo c, hi c]`; `Band.lo`/`Band.hi` take ONE `Corner`, so a
statement quantifying over arcs at one `c` never mixes corners.
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

/-- Well-formed: non-negative, min ≤ max at each corner, fast below slow. -/
def ok (b : Band) : Bool :=
  decide (0 ≤ b.fmin) && decide (b.fmin ≤ b.fmax) && decide (b.smin ≤ b.smax) &&
  decide (b.fmin ≤ b.smin) && decide (b.fmax ≤ b.smax)

/-- Sum of two arcs in series (corner by corner: never mixes corners). -/
def add (a b : Band) : Band := ⟨a.fmin + b.fmin, a.fmax + b.fmax, a.smin + b.smin, a.smax + b.smax⟩

/-- Hull of two bands (corner by corner). -/
def hull (a b : Band) : Band :=
  ⟨min a.fmin b.fmin, max a.fmax b.fmax, min a.smin b.smin, max a.smax b.smax⟩

theorem add_lo (a b : Band) (c : Corner) : (a.add b).lo c = a.lo c + b.lo c := by
  cases c <;> rfl
theorem add_hi (a b : Band) (c : Corner) : (a.add b).hi c = a.hi c + b.hi c := by
  cases c <;> rfl

/-- Series composition: delays admissible for two arcs at one corner add to a
delay admissible for their sum at that corner. -/
theorem In.add {a b : Band} {c : Corner} {d e : Int} (ha : a.In c d) (hb : b.In c e) :
    (a.add b).In c (d + e) := by
  unfold In at *; rw [add_lo, add_hi]; omega

theorem In.hull_left {a b : Band} {c : Corner} {d : Int} (h : a.In c d) : (a.hull b).In c d := by
  cases c <;> simp only [In, lo, hi, hull] at * <;> omega

theorem In.hull_right {a b : Band} {c : Corner} {d : Int} (h : b.In c d) : (a.hull b).In c d := by
  cases c <;> simp only [In, lo, hi, hull] at * <;> omega

end Band

/-- Slice site type (prjxray keeps one SDF per site type). -/
inductive SiteType where
  | slicel
  | slicem
  deriving DecidableEq, Repr

/-- LUT / column letter inside a slice. -/
inductive Letter where
  | A | B | C | D
  deriving DecidableEq, Repr

/-- The three wide-function muxes of a slice: F7AMUX (A6/B6), F7BMUX (C6/D6),
F8MUX (over the two F7 outputs). -/
inductive FMux where
  | f7a | f7b | f8
  deriving DecidableEq, Repr

/-- Arcs of one 2:1 slice mux: data `0`, data `1`, select `S0` -> `OUT`. -/
structure MuxArcs where
  i0 : Band
  i1 : Band
  s : Band
  deriving DecidableEq, Repr

/-- CARRY4 input pins. -/
inductive CPin where
  | cin | cyinit | s0 | s1 | s2 | s3 | di0 | di1 | di2 | di3
  deriving DecidableEq, Repr

/-- CARRY4 output pins. -/
inductive COut where
  | o0 | o1 | o2 | o3 | co0 | co1 | co2 | co3
  deriving DecidableEq, Repr

/-- prjxray's CARRY4 cell variants (`CARRY4`, `CARRY4_O5`, `CARRY4_AX`, ...,
`_LBOTH`, `_LFF`). The base variant holds the CIN/CYINIT/S arcs; the `O5`/`?X`
variants the DI arcs by DI source (LUT O5 or the bypass pin); `LBOTH`/`LFF` are
output-load variants (the fuzzer does not document them further). -/
inductive C4Var where
  | base | o5 | ax | axLboth | axLff | bx | bxLboth | bxLff | cx | cxLboth | cxLff | dx
  | lboth | lff
  deriving DecidableEq, Repr

/-- Sources of a slice OUTMUX (`ROUTING_BEL <x>MUX`), in prjxray's names:
`x5lut`, `x6lut`, `o5`, `o6` (the two name pairs are NOT reconciled by the
database, see the notes), `x5ff`, `carry4_o<i>`, `carry4_co<i>`, and the
wide mux of that column (`f7amux` on A, `f8mux` on B, `f7bmux` on C), and
`a6lut` into SLICEM's DMUX (only there; the column-A LUT, e.g. for the SRL/RAM
cascade). -/
inductive OSrc where
  | lut5 | lut6 | o5 | o6 | ff5 | cyO | cyCO | fmux | a6lut
  deriving DecidableEq, Repr

/-- Sources of the carry-input hops (`ROUTING_BEL <SITE>/CARRY4` and `<x>CY0`). -/
inductive CHop where
  | lut5 (l : Letter)
  | lut6 (l : Letter)
  | x (l : Letter)
  | cy0 (l : Letter)
  deriving DecidableEq, Repr

def Letter.all : List Letter := [.A, .B, .C, .D]
def CPin.all : List CPin := [.cin, .cyinit, .s0, .s1, .s2, .s3, .di0, .di1, .di2, .di3]
def COut.all : List COut := [.o0, .o1, .o2, .o3, .co0, .co1, .co2, .co3]
def C4Var.all : List C4Var :=
  [.base, .o5, .ax, .axLboth, .axLff, .bx, .bxLboth, .bxLff, .cx, .cxLboth, .cxLff, .dx, .lboth, .lff]
def OSrc.all : List OSrc := [.lut5, .lut6, .o5, .o6, .ff5, .cyO, .cyCO, .fmux, .a6lut]
def SiteType.all : List SiteType := [.slicel, .slicem]
def FMux.all : List FMux := [.f7a, .f7b, .f8]

end Formal.Core.Prims
