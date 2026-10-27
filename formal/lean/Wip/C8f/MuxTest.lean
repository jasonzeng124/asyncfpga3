import Formal.Net.Ops

namespace Formal.Net.Ops.Mux

/-- One reachable state of the bd_mux model plus three counter differences
(`dc = #c↑ - #z↑`, `dxo = 1 + #x↑ - #c↑(s=0)`, `dyo = 1 + #y↑ - #c↑(s=1)`). -/
structure MS where
  xr : Bool
  xa : Bool
  yr : Bool
  ya : Bool
  cr : Bool
  ca : Bool
  s : Bool
  zr : Bool
  za : Bool
  j0 : Bool
  j1 : Bool
  dc : Nat
  dxo : Nat
  dyo : Nat
  deriving DecidableEq

def tbl : List MS := [
  ⟨false, false, false, false, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, false, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, false, false, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, false, false, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, false, false, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, false, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, false, false, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨true, false, false, false, true, false, false, false, false, false, false, 1, 1, 1⟩,
  ⟨false, true, false, false, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨false, false, true, false, true, false, false, false, false, false, false, 1, 0, 2⟩,
  ⟨true, false, true, false, true, false, false, false, false, false, false, 1, 1, 2⟩,
  ⟨false, true, true, false, true, false, false, false, false, false, false, 1, 0, 2⟩,
  ⟨false, false, false, true, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨true, false, false, true, true, false, false, false, false, false, false, 1, 1, 1⟩,
  ⟨false, true, false, true, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨false, false, false, false, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, true, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, true, false, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, true, false, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, true, false, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, false, false, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, false, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, false, true, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, false, true, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, false, true, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, false, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, false, false, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨true, false, false, false, true, false, true, false, false, false, false, 1, 2, 0⟩,
  ⟨false, true, false, false, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨false, false, true, false, true, false, true, false, false, false, false, 1, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, false, false, false, false, 1, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, false, false, false, false, 1, 1, 1⟩,
  ⟨false, false, false, true, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨true, false, false, true, true, false, true, false, false, false, false, 1, 2, 0⟩,
  ⟨false, true, false, true, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨false, false, false, false, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, true, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, true, true, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, true, true, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, true, true, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, true, false, false, false, true, false, false, true, false, false, 0, 1, 1⟩,
  ⟨false, true, true, false, false, true, false, false, true, false, false, 0, 1, 2⟩,
  ⟨false, true, false, true, false, true, false, false, true, false, false, 0, 1, 1⟩,
  ⟨false, false, false, true, false, true, true, false, true, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, false, true, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, false, true, false, false, 0, 1, 1⟩,
  ⟨false, true, false, false, false, true, false, true, true, false, false, 0, 1, 1⟩,
  ⟨false, true, true, false, false, true, false, true, true, false, false, 0, 1, 2⟩,
  ⟨false, true, false, true, false, true, false, true, true, false, false, 0, 1, 1⟩,
  ⟨false, false, false, true, false, true, true, true, true, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, true, true, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, true, true, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, true, false, false, false, false, true, false, 1, 1, 1⟩,
  ⟨true, false, true, false, true, false, false, false, false, true, false, 1, 1, 2⟩,
  ⟨true, false, false, true, true, false, false, false, false, true, false, 1, 1, 1⟩,
  ⟨true, false, false, false, true, false, false, true, false, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, false, true, false, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, true, false, false, true, false, true, false, 0, 1, 1⟩,
  ⟨true, false, false, false, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, false, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, false, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, false, true, true, true, false, 0, 1, 2⟩,
  ⟨false, true, true, false, true, false, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, true, true, false, true, false, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, true, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, true, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, false, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, false, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, false, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨false, true, true, false, false, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, true, true, false, false, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, true, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, true, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, false, false, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, false, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, false, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, true, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨false, true, true, false, true, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, true, true, false, true, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, true, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, true, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, false, true, false, true, false, true, false, false, false, true, 1, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, false, false, false, true, 1, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, false, false, false, true, 1, 1, 1⟩,
  ⟨false, false, true, false, true, false, true, true, false, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, true, false, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, true, false, false, true, 0, 1, 1⟩,
  ⟨false, false, true, false, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, false, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, false, true, true, false, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, false, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, true, true, false, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, false, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, false, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, false, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, true, false, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, false, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, true, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, false, true, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, false, true, true, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, false, true, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, true, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, true, true, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, true, true, true, true, true, true, false, true, 0, 1, 1⟩]

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Successor entry for given next signal values. -/
def nxt (e : MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) : MS :=
  ⟨xr, xa, yr, ya, cr, ca, s, zr, za, j0, j1,
   e.dc + b2n (!e.cr && cr) - b2n (!e.zr && zr),
   e.dxo + b2n (!e.xr && xr) - b2n (!e.cr && cr && !s),
   e.dyo + b2n (!e.yr && yr) - b2n (!e.cr && cr && s)⟩

/-- What the closure check concludes about one allowed step. -/
def Concl (e : MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) : Prop :=
  let n := nxt e xr xa yr ya cr ca s zr za j0 j1
  tbl.contains n = true ∧
  n.dc + b2n (!e.zr && zr) = e.dc + b2n (!e.cr && cr) ∧
  n.dxo + b2n (!e.cr && cr && !s) = e.dxo + b2n (!e.xr && xr) ∧
  n.dyo + b2n (!e.cr && cr && s) = e.dyo + b2n (!e.yr && yr) ∧
  (xa ≠ e.xa → e.xa ≠ e.xr) ∧ (ya ≠ e.ya → e.ya ≠ e.yr) ∧ (ca ≠ e.ca → e.ca ≠ e.cr) ∧
  (zr ≠ e.zr → e.zr = e.za) ∧
  ((!e.zr && zr) = true → e.cr = true ∧ e.ca = false ∧ e.za = false ∧ e.dc = 1 ∧
     (if e.s then e.yr = true ∧ e.ya = false ∧ e.dyo = 1
      else e.xr = true ∧ e.xa = false ∧ e.dxo = 1))

instance (e : MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) :
    Decidable (Concl e xr xa yr ya cr ca s zr za j0 j1) := by
  unfold Concl; exact inferInstance

/-- Closure of the reachable set under every step the gate model and the
environment allow (interleaved so that `decide` prunes early). -/
theorem mux_closed : ∀ e ∈ tbl,
    ∀ xr : Bool, (xr ≠ e.xr → e.xr = e.xa) →
    ∀ yr : Bool, (yr ≠ e.yr → e.yr = e.ya) →
    ∀ cr : Bool, (cr ≠ e.cr → e.cr = e.ca) →
    ∀ za : Bool, (za ≠ e.za → e.za ≠ e.zr) →
    ∀ j0 : Bool, (j0 ≠ e.j0 → e.xr = j0 ∧ (e.cr && !e.s) = j0) →
    ∀ j1 : Bool, (j1 ≠ e.j1 → e.yr = j1 ∧ (e.cr && e.s) = j1) →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.j0 || e.j1)) →
    ∀ xa : Bool, (xa ≠ e.xa → e.j0 = xa ∧ e.za = xa) →
    ∀ ya : Bool, (ya ≠ e.ya → e.j1 = ya ∧ e.za = ya) →
    ∀ ca : Bool, (ca ≠ e.ca → ca = e.za) →
    ∀ s : Bool, (s ≠ e.s → ¬ ((e.cr || e.ca) = true ∧ (cr || ca) = true)) →
    Concl e xr xa yr ya cr ca s zr za j0 j1 := by
  decide +kernel

end Formal.Net.Ops.Mux
