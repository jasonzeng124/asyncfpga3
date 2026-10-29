import Formal.Net.CapstoneLiveNd3Loc

/-!
# Probe C-8z3 (5): the unweakened mux persistence claim is false (kernel)

`MPersFull` is `MPers` without the acknowledge exception (all six gates of the 2-way mux
persistent). Over the mux's reachable table and its allowed steps it FAILS: `mux_full_pers_false`
(kernel `decide`). So local persistence of the mux input acknowledges cannot be proved, and
`mux_pers_tbl`'s exception is necessary.
-/

namespace Formal.Net.CapNet.Live.Nd3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

def MPersFull (e : Mux.MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) : Prop :=
  MPers e xr xa yr ya cr ca s zr za j0 j1 ∧
  (AllB fun v : Bool => e.j0 = v → e.za = v → e.xa ≠ v → (j0 = v ∧ za = v) ∨ xa = v) ∧
  (AllB fun v : Bool => e.j1 = v → e.za = v → e.ya ≠ v → (j1 = v ∧ za = v) ∨ ya = v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : Mux.MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) :
    Decidable (MPersFull e xr xa yr ya cr ca s zr za j0 j1) := by
  unfold MPersFull; exact inferInstance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem mux_full_pers_false : ¬ ∀ e ∈ Mux.tbl,
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
    MPersFull e xr xa yr ya cr ca s zr za j0 j1 := by
  decide +kernel

end Formal.Net.CapNet.Live.Nd3
