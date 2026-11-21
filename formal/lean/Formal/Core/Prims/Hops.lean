import Formal.Core.Prims.XrayData

/-!
# Formal.Core.Prims.Hops — site-internal delay arcs (OUTMUX, LUT -> F7/CARRY4 hops)

Shard A, probe PrimsComb (north star 1). Core Lean only (no Mathlib).
Notes: `formal/notes/A-prims-comb.md`.

A primitive's output reaches the general routing through a site pin. On a
7-series slice the LUT `O6` has a dedicated pin (`A`..`D`; prjxray
`ROUTING_BEL <SITE>/A: a6lut -> a` is 0 ps), and everything else (`O5`, the F7/F8
outputs, `CARRY4 O/CO`, the 5FF) leaves through the column's **OUTMUX**
(`<x>MUX` pin), which prjxray charges as a `ROUTING_BEL <SITE>/<x>MUX` arc
(`XrayData.outMux`). These are delay arcs in series with the primitive's own
IOPATH (`Band.add`, corner by corner, `Band.In.add`).

## Results
* `amux_a5lut` : the `a5lut -> AMUX` hop is (62::78)(163::202) ps on SLICEL —
  the hop the 2026-10-29 audit found missing on every O5-driven arc of the
  xevents8 bands (E8Mux). `o5_path_includes_outmux` : an `A_j -> O5 -> AMUX`
  path is the LUT5 arc PLUS that hop; it is never below the arc alone plus 62 ps
  (fast) / 163 ps (slow).
* `outmux_names_disagree` : prjxray has both `a5lut` and `o5` (and `a6lut`/`o6`)
  entries for the same mux with DIFFERENT numbers; the database does not say
  which is the LUT output (xray_delay.py uses the `x5lut`/`x6lut` ones). `outMuxHull`
  takes the hull of each pair; `outMuxHull_sound` says a delay admissible for
  either entry is admissible for the hull.
* `carry4Hull` / `carry4Hull_sound` : the hull of a CARRY4 arc over prjxray's
  cell variants (DI source, output load), sound for whichever variant is
  physically right.
* `all_ok` : every generated band (LUT5/LUT6 arcs, OUTMUX, OUTMUXL, carry
  hops, all CARRY4 variants, both site types) is well formed: min ≤ max at each
  corner and fast ≤ slow.
* `cy0_flat` : the `<x>CY0` (`ax -> di0` etc.) entries have the same number at
  all four positions (e.g. 96 ps): prjxray-db's fuzzer reports no corner spread
  for them. Recorded as a data oddity, not interpreted.

## Not covered
Which `...L` instance (`AMUXL`) applies (the fuzzer does not record it;
transcribed as `outMuxL`, not used); wires and pips outside the site.
-/

namespace Formal.Core.Prims

/-! ## Optional-band helpers -/

/-- Hull of two optional bands (`none` = no arc). -/
def hullOpt : Option Band → Option Band → Option Band
  | some a, some b => some (a.hull b)
  | some a, none => some a
  | none, b => b

/-- `b` is admissible at `c` for `d`, as an optional band. -/
def InOpt (b : Option Band) (c : Corner) (d : Int) : Prop :=
  match b with
  | some b => b.In c d
  | none => False

theorem InOpt.hull_left {a b : Option Band} {c : Corner} {d : Int} (h : InOpt a c d) :
    InOpt (hullOpt a b) c d := by
  cases a with
  | none => exact h.elim
  | some a => cases b with
    | none => exact h
    | some b => exact Band.In.hull_left h

theorem InOpt.hull_right {a b : Option Band} {c : Corner} {d : Int} (h : InOpt b c d) :
    InOpt (hullOpt a b) c d := by
  cases a with
  | none => exact h
  | some a => cases b with
    | none => exact h.elim
    | some b => exact Band.In.hull_right h

/-- Hull over a list. -/
def hullList (l : List (Option Band)) : Option Band := l.foldr hullOpt none

theorem hullList_sound : ∀ (l : List (Option Band)) (b : Option Band) (c : Corner) (d : Int),
    b ∈ l → InOpt b c d → InOpt (hullList l) c d
  | [], _, _, _, h, _ => absurd h List.not_mem_nil
  | x :: xs, b, c, d, h, hb => by
      simp only [hullList, List.foldr_cons]
      rcases List.mem_cons.mp h with e | e
      · subst e; exact InOpt.hull_left hb
      · exact InOpt.hull_right (hullList_sound xs b c d e hb)

/-! ## CARRY4: hull over prjxray's cell variants -/

def carry4Hull (st : SiteType) (p : CPin) (o : COut) : Option Band :=
  hullList (C4Var.all.map fun v => carry4Arc st v p o)

theorem C4Var.mem_all (v : C4Var) : v ∈ C4Var.all := by cases v <;> decide

theorem carry4Hull_sound (st : SiteType) (v : C4Var) (p : CPin) (o : COut) (c : Corner) (d : Int)
    (h : InOpt (carry4Arc st v p o) c d) : InOpt (carry4Hull st p o) c d :=
  hullList_sound _ _ c d (List.mem_map.mpr ⟨v, C4Var.mem_all v, rfl⟩) h

/-! ## OUTMUX -/

/-- The two names prjxray gives a LUT output into the OUTMUX, hulled. -/
def outMuxHull (st : SiteType) (l : Letter) : Bool → Option Band
  | false => hullOpt (outMux st l .lut5) (outMux st l .o5)
  | true => hullOpt (outMux st l .lut6) (outMux st l .o6)

theorem outMuxHull_sound (st : SiteType) (l : Letter) (c : Corner) (d : Int) :
    (InOpt (outMux st l .lut5) c d → InOpt (outMuxHull st l false) c d) ∧
    (InOpt (outMux st l .o5) c d → InOpt (outMuxHull st l false) c d) ∧
    (InOpt (outMux st l .lut6) c d → InOpt (outMuxHull st l true) c d) ∧
    (InOpt (outMux st l .o6) c d → InOpt (outMuxHull st l true) c d) :=
  ⟨InOpt.hull_left, InOpt.hull_right, InOpt.hull_left, InOpt.hull_right⟩

theorem amux_a5lut :
    outMux .slicel .A .lut5 = some ⟨62, 78, 163, 202⟩ ∧
    outMux .slicel .A .o5 = some ⟨59, 74, 141, 175⟩ ∧
    outMux .slicel .A .lut6 = some ⟨71, 88, 168, 209⟩ := by decide

theorem outmux_names_disagree :
    ∀ st l, outMux st l .lut5 ≠ outMux st l .o5 ∧ outMux st l .lut6 ≠ outMux st l .o6 := by
  intro st l; cases st <;> cases l <;> decide

/-- `A_j -> O5 -> <x>MUX` as one series band. -/
def o5MuxPath (st : SiteType) (l : Letter) (j : Nat) : Option Band :=
  match lut5Arc st l j, outMux st l .lut5 with
  | some a, some b => some (a.add b)
  | _, _ => none

/-- Series composition: a LUT5 delay and an OUTMUX delay add to an admissible
path delay at the same corner. -/
theorem o5MuxPath_In {st : SiteType} {l : Letter} {j : Nat} {a b : Band} {c : Corner} {d e : Int}
    (ha : lut5Arc st l j = some a) (hb : outMux st l .lut5 = some b)
    (hd : a.In c d) (he : b.In c e) : InOpt (o5MuxPath st l j) c (d + e) := by
  simp only [o5MuxPath, ha, hb, InOpt]; exact Band.In.add hd he

/-- Every O5 path through the OUTMUX exceeds the bare LUT5 arc by at least the
smallest `x5lut -> <x>MUX` hop: 62 ps fast, 163 ps slow (over both site types,
all columns, all pins). -/
theorem o5_path_includes_outmux : ∀ st l, ∀ j, j < 5 →
    ∃ a b, lut5Arc st l j = some a ∧ outMux st l .lut5 = some b ∧
      62 ≤ b.lo .fast ∧ 163 ≤ b.lo .slow := by
  intro st l j hj
  cases st <;> cases l <;>
    (match j, hj with
     | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => exact ⟨_, _, rfl, rfl, by decide⟩)

/-! ## Well-formedness of all generated data -/

def okOpt : Option Band → Bool
  | some b => b.ok
  | none => true

theorem all_ok :
    (SiteType.all.all fun st =>
      (Letter.all.all fun l =>
        ((List.range 6).all fun j => okOpt (lut6Arc st l j)) &&
        ((List.range 5).all fun j => okOpt (lut5Arc st l j)) &&
        (OSrc.all.all fun s => okOpt (outMux st l s) && okOpt (outMuxL st l s)) &&
        (f7Hop st l).ok &&
        okOpt (carryHop st (.lut5 l)) && okOpt (carryHop st (.lut6 l)) &&
        okOpt (carryHop st (.x l)) && okOpt (carryHop st (.cy0 l))) &&
      (f8SelHop st).ok &&
      (C4Var.all.all fun v => CPin.all.all fun p => COut.all.all fun o =>
        okOpt (carry4Arc st v p o))) = true := by
  decide

theorem cy0_flat :
    carryHop .slicel (.cy0 .A) = some ⟨96, 96, 96, 96⟩ ∧
    carryHop .slicem (.cy0 .A) = some ⟨111, 111, 111, 111⟩ := by decide

/-- The number of generated CARRY4 arcs (both site types, all variants). -/
theorem carry4_rows : carry4ArcRows = 240 := rfl

end Formal.Core.Prims
