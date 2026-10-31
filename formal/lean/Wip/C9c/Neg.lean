import Formal.Net.MullerAll
/-! Negative controls for the window checker (scratch, `#eval` only). -/
namespace Formal.Net.MullerAll
open Formal.Net.Muller

/-- `chkMid` with the table and the semantics given separately. -/
def chkMidT (tab : Nat → List Nat) (m : Mode) : Bool :=
  dom.all fun a => (tab a).all fun b => (tab b).all fun c => types.all fun t =>
    !lenabled m a b c t ||
      ((tab a).contains (flip b t) && (tab (flip b t)).contains c && followL a b c t &&
        types.all fun u => u == t || !valid b u || persist m a b (flip b t) c u)

-- the physical network (free feedback, no RT restriction) with the rt table: fails
#eval chkMidT adjRt .free
-- the iso table under the rt semantics: fails (rt reaches f ≠ c)
#eval chkMidT adjIso .rt
-- drop one admissible pair (stage value 0 followed by 2) from the rt table: closure fails
#eval chkMidT (fun v => if v = 0 then (adjRt 0).erase 2 else adjRt v) .rt
-- sanity: the real ones pass
#eval (chkMidT adjRt .rt, chkMidT adjIso .iso)
end Formal.Net.MullerAll
