import Formal.Net.OpsMuxNOp
import Formal.Net.CapstoneLiveNd3Loc

/-!
# Probe C-8z3 (3): local persistence of the 3-way mux (`bd_muxn3`)

Over the 648-state reachable table `MuxN.TB` (8l), by kernel `decide` split by the clipped
select (as `MuxN.closed0..3`; selects 0, 1 here, 2, 3 and the trace lemma in `CapstoneLiveNd3MuxN2`): every gate of the 3-way mux is persistent, except that the
falling excitation of an input acknowledge `in_k_ack = C(j_k, z_ack)` may be withdrawn by
`z_ack` rising in the same step (the same exception as the 2-way mux).
-/

namespace Formal.Net.CapNet.Live.Nd3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

/-- Persistence of the 3-way mux's gates for one step, with the acknowledge exception. -/
def NPers (e : MuxN.MS) (r0 r1 r2 a0 a1 a2 cr ca zr za j0 j1 j2 : Bool) (s : Nat) : Prop :=
  (AllB fun v : Bool => e.r0 = v → (e.cr && e.s == 0) = v → e.j0 ≠ v →
    (r0 = v ∧ (cr && s == 0) = v) ∨ j0 = v) ∧
  (AllB fun v : Bool => e.r1 = v → (e.cr && e.s == 1) = v → e.j1 ≠ v →
    (r1 = v ∧ (cr && s == 1) = v) ∨ j1 = v) ∧
  (AllB fun v : Bool => e.r2 = v → (e.cr && e.s == 2) = v → e.j2 ≠ v →
    (r2 = v ∧ (cr && s == 2) = v) ∨ j2 = v) ∧
  (AllB fun v : Bool => (e.j0 || e.j1 || e.j2) = v → e.zr ≠ v → (j0 || j1 || j2) = v ∨ zr = v) ∧
  (AllB fun v : Bool => e.j0 = v → e.za = v → e.a0 ≠ v →
    (j0 = v ∧ za = v) ∨ a0 = v ∨ (v = false ∧ za = true)) ∧
  (AllB fun v : Bool => e.j1 = v → e.za = v → e.a1 ≠ v →
    (j1 = v ∧ za = v) ∨ a1 = v ∨ (v = false ∧ za = true)) ∧
  (AllB fun v : Bool => e.j2 = v → e.za = v → e.a2 ≠ v →
    (j2 = v ∧ za = v) ∨ a2 = v ∨ (v = false ∧ za = true)) ∧
  (AllB fun v : Bool => e.za = v → e.ca ≠ v → za = v ∨ ca = v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : MuxN.MS) (r0 r1 r2 a0 a1 a2 cr ca zr za j0 j1 j2 : Bool) (s : Nat) :
    Decidable (NPers e r0 r1 r2 a0 a1 a2 cr ca zr za j0 j1 j2 s) := by
  unfold NPers; exact inferInstance

def NPersAt (e : MuxN.MS) : Prop :=
    MuxN.mem e = true →
    ∀ r0 : Bool, (r0 ≠ e.r0 → e.r0 = e.a0) →
    ∀ r1 : Bool, (r1 ≠ e.r1 → e.r1 = e.a1) →
    ∀ r2 : Bool, (r2 ≠ e.r2 → e.r2 = e.a2) →
    ∀ cr : Bool, (cr ≠ e.cr → e.cr = e.ca) →
    ∀ za : Bool, (za ≠ e.za → e.za ≠ e.zr) →
    ∀ j0 : Bool, (j0 ≠ e.j0 → e.r0 = j0 ∧ (e.cr && e.s == 0) = j0) →
    ∀ j1 : Bool, (j1 ≠ e.j1 → e.r1 = j1 ∧ (e.cr && e.s == 1) = j1) →
    ∀ j2 : Bool, (j2 ≠ e.j2 → e.r2 = j2 ∧ (e.cr && e.s == 2) = j2) →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.j0 || e.j1 || e.j2)) →
    ∀ a0 : Bool, (a0 ≠ e.a0 → e.j0 = a0 ∧ e.za = a0) →
    ∀ a1 : Bool, (a1 ≠ e.a1 → e.j1 = a1 ∧ e.za = a1) →
    ∀ a2 : Bool, (a2 ≠ e.a2 → e.j2 = a2 ∧ e.za = a2) →
    ∀ ca : Bool, (ca ≠ e.ca → ca = e.za) →
    ∀ s : Nat, s < 4 → (s ≠ e.s → ¬ ((e.cr || e.ca) = true ∧ (cr || ca) = true)) →
    NPers e r0 r1 r2 a0 a1 a2 cr ca zr za j0 j1 j2 s

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : MuxN.MS) : Decidable (NPersAt e) := by unfold NPersAt; exact inferInstance

def NPersS (s0 : Nat) : Prop :=
  ∀ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Bool,
    NPersAt ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩

instance (s0 : Nat) : Decidable (NPersS s0) := by unfold NPersS; exact inferInstance

set_option maxRecDepth 100000 in
theorem npers0 : NPersS 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem npers1 : NPersS 1 := by decide +kernel
end Formal.Net.CapNet.Live.Nd3
