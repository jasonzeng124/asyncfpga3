import Formal.Net.OpsSteer
import Formal.Net.OpsJoin
import Formal.Net.OpsCM
import Formal.Net.OpsLink

/-!
# Probe C-8z3 (1): local persistence of every gcd_hw cell kind

**Persistence** of a gate along a trace: if at `t` the gate is excited toward `v` and its
output is not `v`, then at `t + 1` it is still excited toward `v` or its output is `v`. An
excited gate is never disabled without firing (no hazard). It is the semi-modularity half of
the Keller/confluence route to H_NO_DEADLOCK'' (C-8z2's note).

Here it is proved per cell kind from the cell's gate model and the four-phase protocol of
its channels only (plus `Held` on the select channel of a steer / mux), using the cells'
own inductive invariants (8f/8j/8l: `FInv`, `JInv`, `SInv`, the reachable tables `tbl`,
`atbl`, `ltbl`):

* fork: branch request wires, acknowledge C-element (`fork_req_pers`, `fork_ack_pers`);
* join (also the branch `bjoin`): request C-element, acknowledge wires;
* steer: both output request LUTs, acknowledge OR;
* 2-way mux: `j0`, `j1`, `z_req`, `x_ack`, `y_ack`, `c_ack` (kernel `decide` over `tbl`);
* arbiter stage: `z_req`, `x_ack`, `y_ack`; the two grants only in states that are not
  contested (both requests high, no grant) -- a contested arbiter is the one place where a
  gate may be disabled without firing (`amerge_pers`, `amerge_grant_pers`);
* link: controller node `c`, `i_ack`, `o_req` (kernel `decide` over `ltbl`);
* source LUT and sink wire: from the protocol alone.

Not covered here: the 3-way mux (one instance in gcd_hw; its 648-state table is a bitmask,
see the note).
-/

namespace Formal.Net.CapNet.Live.Nd3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

/-- `∀ v : Bool`, in a form `decide` can evaluate. -/
def AllB (p : Bool → Prop) : Prop := p true ∧ p false

instance (p : Bool → Prop) [Decidable (p true)] [Decidable (p false)] : Decidable (AllB p) :=
  instDecidableAnd

theorem AllB.app {p : Bool → Prop} (h : AllB p) : ∀ v, p v
  | true => h.1
  | false => h.2

/-! ## Protocol consequences -/

theorem send_stay {c : Chan} (hp : Protocol c) {t : Nat} (h : c.req t ≠ c.ack t) :
    c.req (t + 1) = c.req t := by
  exact Classical.byContradiction fun hn => h ((hp.2 t).1 hn)

theorem recv_stay {c : Chan} (hp : Protocol c) {t : Nat} (h : c.ack t = c.req t) :
    c.ack (t + 1) = c.ack t := by
  exact Classical.byContradiction fun hn => ((hp.2 t).2 hn) h

/-- Source LUT `req := ¬ack` is persistent. -/
theorem src_pers {z : Chan} (hp : Protocol z) (v : Bool) (t : Nat) (he : (!z.ack t) = v)
    (hn : z.req t ≠ v) : (!z.ack (t + 1)) = v ∨ z.req (t + 1) = v := by
  left
  have : z.ack t = z.req t := by
    cases h1 : z.ack t <;> cases h2 : z.req t <;> simp_all
  rw [recv_stay hp this]; exact he

/-- Sink wire `ack := req` is persistent. -/
theorem sink_pers {i : Chan} (hp : Protocol i) (v : Bool) (t : Nat) (he : i.req t = v)
    (hn : i.ack t ≠ v) : i.req (t + 1) = v ∨ i.ack (t + 1) = v := by
  left
  have : i.req t ≠ i.ack t := by rw [he]; exact fun h => hn h.symm
  rw [send_stay hp this]; exact he

/-! ## Fork -/

theorem f1 : ∀ ar aa r k ar' r' v : Bool, Fork.FInv ar aa r k = true → (ar' ≠ ar → ar = aa) →
    (r' ≠ r → r' = ar) → ar = v → r ≠ v → ar' = v ∨ r' = v := by decide

theorem f2 : ∀ ar aa r k k' v : Bool, Fork.FInv ar aa r k = true → k = v → aa ≠ v →
    (k' ≠ k → k ≠ r) → k' = v := by decide

section fork
variable {a : Chan} {os : List Chan}

theorem fork_finv (F : Fork.Fork a os) (hpa : Protocol a) (hpo : ∀ o ∈ os, Protocol o) :
    ∀ t, ∀ o ∈ os, Fork.FInv (a.req t) (a.ack t) (o.req t) (o.ack t) = true := fun t =>
  Fork.fork_inv F hpa.1.1 (fun o ho => (hpo o ho).1.2) t
    (fun s _ => ⟨hpa.2 s, fun o ho => (hpo o ho).2 s⟩)

theorem fork_req_pers (F : Fork.Fork a os) (hpa : Protocol a) (hpo : ∀ o ∈ os, Protocol o)
    {o : Chan} (ho : o ∈ os) (v : Bool) (t : Nat) (he : a.req t = v) (hn : o.req t ≠ v) :
    a.req (t + 1) = v ∨ o.req (t + 1) = v :=
  f1 _ _ _ _ _ _ v (fork_finv F hpa hpo t o ho) (hpa.2 t).1 (F.wire o ho t) he hn

theorem fork_ack_pers (F : Fork.Fork a os) (hpa : Protocol a) (hpo : ∀ o ∈ os, Protocol o)
    (v : Bool) (t : Nat) (he : ∀ o ∈ os, o.ack t = v) (hn : a.ack t ≠ v) :
    (∀ o ∈ os, o.ack (t + 1) = v) ∨ a.ack (t + 1) = v :=
  Or.inl fun o ho => f2 _ _ _ _ _ v (fork_finv F hpa hpo t o ho) (he o ho) hn ((hpo o ho).2 t).2

end fork

/-! ## Join -/

theorem j1 : ∀ or oa r k r' v : Bool, Join.JInv or oa r k = true → r = v → or ≠ v →
    (r' ≠ r → r = k) → r' = v := by decide

theorem j2 : ∀ or oa r k oa' v : Bool, Join.JInv or oa r k = true → oa = v → k ≠ v →
    (oa' ≠ oa → oa ≠ or) → oa' = v := by decide

section join
variable {g : List Nat → Nat} {is : List Chan} {o : Chan}

theorem join_jinv (J : Join.Join g is o) (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) :
    ∀ t, ∀ i ∈ is, Join.JInv (o.req t) (o.ack t) (i.req t) (i.ack t) = true := fun t =>
  Join.join_inv J hpo.1.2 (fun i hi => (hpi i hi).1.1) t
    (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩)

theorem join_req_pers (J : Join.Join g is o) (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i)
    (v : Bool) (t : Nat) (he : ∀ i ∈ is, i.req t = v) (hn : o.req t ≠ v) :
    (∀ i ∈ is, i.req (t + 1) = v) ∨ o.req (t + 1) = v :=
  Or.inl fun i hi => j1 _ _ _ _ _ v (join_jinv J hpo hpi t i hi) (he i hi) hn ((hpi i hi).2 t).1

theorem join_ack_pers (J : Join.Join g is o) (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i)
    {i : Chan} (hi : i ∈ is) (v : Bool) (t : Nat) (he : o.ack t = v) (hn : i.ack t ≠ v) :
    o.ack (t + 1) = v ∨ i.ack (t + 1) = v :=
  Or.inl (j2 _ _ _ _ _ v (join_jinv J hpo hpi t i hi) he hn (hpo.2 t).2)

end join

/-! ## Steer -/

theorem st1 : ∀ jr ja s rT kT rF kF jr' ja' s' rT' v : Bool, Steer.SInv jr ja s rT kT rF kF = true →
    (jr' ≠ jr → jr = ja) → ((jr || ja) = true → (jr' || ja') = true → s' = s) →
    (jr && (s == true)) = v → rT ≠ v →
    (jr' && (s' == true)) = v ∨ rT' = v := by decide

theorem st2 : ∀ jr ja s rT kT rF kF jr' ja' s' rF' v : Bool, Steer.SInv jr ja s rT kT rF kF = true →
    (jr' ≠ jr → jr = ja) → ((jr || ja) = true → (jr' || ja') = true → s' = s) →
    (jr && (s == false)) = v → rF ≠ v →
    (jr' && (s' == false)) = v ∨ rF' = v := by decide

theorem st3 : ∀ jr ja s rT kT rF kF kT' kF' v : Bool, Steer.SInv jr ja s rT kT rF kF = true →
    (kT' ≠ kT → kT ≠ rT) → (kF' ≠ kF → kF ≠ rF) → (kT || kF) = v → ja ≠ v →
    (kT' || kF') = v := by decide

section steer
variable {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}

theorem steer_sinv (S : Steer.Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b))
    (hh : Held j) : ∀ t, Steer.SInv (j.req t) (j.ack t) (sel (j.dat t)) ((out true).req t)
      ((out true).ack t) ((out false).req t) ((out false).ack t) = true := fun t =>
  Steer.steer_inv S hpj.1.1 (fun b => (hpo b).1.2) hh t (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)

theorem held_sel (hh : Held j) (t : Nat) :
    (j.req t || j.ack t) = true → (j.req (t + 1) || j.ack (t + 1)) = true →
      sel (j.dat (t + 1)) = sel (j.dat t) := fun h1 h2 => by
  rw [hh t h1 h2]

theorem steer_t_pers (S : Steer.Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b))
    (hh : Held j) (v : Bool) (t : Nat) (he : (j.req t && (sel (j.dat t) == true)) = v)
    (hn : (out true).req t ≠ v) :
    (j.req (t + 1) && (sel (j.dat (t + 1)) == true)) = v ∨ (out true).req (t + 1) = v :=
  st1 _ _ _ _ _ _ _ _ _ _ ((out true).req (t + 1)) v (steer_sinv S hpj hpo hh t) (hpj.2 t).1
    (held_sel hh t) he hn

theorem steer_f_pers (S : Steer.Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b))
    (hh : Held j) (v : Bool) (t : Nat) (he : (j.req t && (sel (j.dat t) == false)) = v)
    (hn : (out false).req t ≠ v) :
    (j.req (t + 1) && (sel (j.dat (t + 1)) == false)) = v ∨ (out false).req (t + 1) = v :=
  st2 _ _ _ _ _ _ _ _ _ _ ((out false).req (t + 1)) v (steer_sinv S hpj hpo hh t) (hpj.2 t).1
    (held_sel hh t) he hn

theorem steer_a_pers (S : Steer.Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b))
    (hh : Held j) (v : Bool) (t : Nat) (he : ((out true).ack t || (out false).ack t) = v)
    (hn : j.ack t ≠ v) :
    ((out true).ack (t + 1) || (out false).ack (t + 1)) = v ∨ j.ack (t + 1) = v :=
  Or.inl (st3 _ _ _ _ _ _ _ _ _ v (steer_sinv S hpj hpo hh t) ((hpo true).2 t).2
    ((hpo false).2 t).2 he hn)

end steer

/-! ## 2-way mux (over the reachable table `Mux.tbl`) -/

/-- Persistence of the six mux gates for one step `e → next`, EXCEPT the falling excitation of
the input acknowledges `x_ack = C(j0, z_ack)`, `y_ack = C(j1, z_ack)`, which may be withdrawn by
`z_ack` rising again (the next token through the mux) before the acknowledge has fallen
(`mux_ack_not_pers`: this really happens in the reachable table). -/
def MPers (e : Mux.MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) : Prop :=
  (AllB fun v : Bool => e.xr = v → (e.cr && !e.s) = v → e.j0 ≠ v → (xr = v ∧ (cr && !s) = v) ∨ j0 = v) ∧
  (AllB fun v : Bool => e.yr = v → (e.cr && e.s) = v → e.j1 ≠ v → (yr = v ∧ (cr && s) = v) ∨ j1 = v) ∧
  (AllB fun v : Bool => (e.j0 || e.j1) = v → e.zr ≠ v → (j0 || j1) = v ∨ zr = v) ∧
  (AllB fun v : Bool => e.j0 = v → e.za = v → e.xa ≠ v →
    (j0 = v ∧ za = v) ∨ xa = v ∨ (v = false ∧ za = true)) ∧
  (AllB fun v : Bool => e.j1 = v → e.za = v → e.ya ≠ v →
    (j1 = v ∧ za = v) ∨ ya = v ∨ (v = false ∧ za = true)) ∧
  (AllB fun v : Bool => e.za = v → e.ca ≠ v → za = v ∨ ca = v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : Mux.MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) :
    Decidable (MPers e xr xa yr ya cr ca s zr za j0 j1) := by
  unfold MPers; exact inferInstance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem mux_pers_tbl : ∀ e ∈ Mux.tbl,
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
    MPers e xr xa yr ya cr ca s zr za j0 j1 := by
  decide +kernel

section mux
variable {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}

theorem mux_step_pers (M : Mux.Mux sel x y c z j0 j1) (hx : Protocol x) (hy : Protocol y)
    (hc : Protocol c) (hz : Protocol z) (hh : Held c) (t : Nat) :
    MPers ⟨x.req t, x.ack t, y.req t, y.ack t, c.req t, c.ack t, sel (c.dat t), z.req t, z.ack t,
      j0 t, j1 t, 0, 0, 0⟩ (x.req (t + 1)) (x.ack (t + 1)) (y.req (t + 1)) (y.ack (t + 1))
      (c.req (t + 1)) (c.ack (t + 1)) (sel (c.dat (t + 1))) (z.req (t + 1)) (z.ack (t + 1))
      (j0 (t + 1)) (j1 (t + 1)) := by
  obtain ⟨dc, dxo, dyo, hm, -⟩ := Mux.mux_inv M hx.1.1 hy.1.1 hc.1.1 hz.1.2 hh t
    (fun s _ => ⟨(hx.2 s).1, (hy.2 s).1, (hc.2 s).1, (hz.2 s).2⟩)
  have hm' : (⟨x.req t, x.ack t, y.req t, y.ack t, c.req t, c.ack t, sel (c.dat t), z.req t,
      z.ack t, j0 t, j1 t, dc, dxo, dyo⟩ : Mux.MS) ∈ Mux.tbl := by
    have := List.contains_iff_mem.mp hm; exact this
  have K := mux_pers_tbl _ hm' (x.req (t + 1)) (hx.2 t).1 (y.req (t + 1)) (hy.2 t).1
    (c.req (t + 1)) (hc.2 t).1 (z.ack (t + 1)) (hz.2 t).2 (j0 (t + 1)) (M.cj0 t) (j1 (t + 1)) (M.cj1 t)
    (z.req (t + 1)) (M.zr t) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t) (c.ack (t + 1)) (M.ca t)
    (sel (c.dat (t + 1))) (fun hs ⟨h1, h2⟩ => hs (by rw [hh t h1 h2]))
  exact K

/-- **The mux's input acknowledges are not persistent** (local table): from the reachable
state "x's previous token returning (`x_req` low, `x_ack` high, `j0` low), `z` idle with
`z_ack` low, the back-edge token `y` already through `j1` and `z_req`", `x_ack` is excited to
fall; an allowed step raises `z_ack` (the consumer takes the `y` token) and leaves `x_ack`
high, and then `x_ack` is no longer excited (`j0 = 0`, `z_ack = 1`). -/
theorem mux_ack_not_pers :
    let e : Mux.MS := ⟨false, true, true, false, true, false, true, true, false, false, true, 0, 1, 1⟩
    e ∈ Mux.tbl ∧
    -- the step: only `z_ack` rises; it is allowed (receiver rule: `z_ack ≠ z_req` before)
    (true ≠ e.za → e.za ≠ e.zr) ∧
    -- before: `x_ack = C(j0, z_ack)` is high and excited to fall
    (e.j0 = false ∧ e.za = false ∧ e.xa = true) ∧
    -- after (`j0 = 0`, `z_ack = 1`, `x_ack = 1`): no longer excited, not fired
    ¬ (false = false ∧ true = false) := by
  decide

end mux

/-! ## Arbiter stage (over `CM.atbl`) -/

def APers (e : CM.AS) (xa ya g1 g2 zr za : Bool) : Prop :=
  (AllB fun v : Bool => (e.g1 || e.g2) = v → (v = true → e.xa = false ∧ e.ya = false) → e.zr ≠ v →
    ((g1 || g2) = v ∧ (v = true → xa = false ∧ ya = false)) ∨ zr = v) ∧
  (AllB fun v : Bool => e.g1 = v → e.za = v → e.xa ≠ v → (g1 = v ∧ za = v) ∨ xa = v) ∧
  (AllB fun v : Bool => e.g2 = v → e.za = v → e.ya ≠ v → (g2 = v ∧ za = v) ∨ ya = v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : CM.AS) (xa ya g1 g2 zr za : Bool) : Decidable (APers e xa ya g1 g2 zr za) := by
  unfold APers; exact inferInstance

/-- Grant persistence (rise guard: own request, other grant low, `A0` low; fall guard: own
request low). -/
def GPers (e : CM.AS) (xr yr g1 g2 za : Bool) : Prop :=
  (AllB fun v : Bool => (v = true → (e.xr && !e.g2 && !e.za) = true) → (v = false → e.xr = false) →
    e.g1 ≠ v → ((v = true → (xr && !g2 && !za) = true) ∧ (v = false → xr = false)) ∨ g1 = v) ∧
  (AllB fun v : Bool => (v = true → (e.yr && !e.g1 && !e.za) = true) → (v = false → e.yr = false) →
    e.g2 ≠ v → ((v = true → (yr && !g1 && !za) = true) ∧ (v = false → yr = false)) ∨ g2 = v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : CM.AS) (xr yr g1 g2 za : Bool) : Decidable (GPers e xr yr g1 g2 za) := by
  unfold GPers; exact inferInstance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem amerge_pers_tbl : ∀ e ∈ CM.atbl,
    ∀ xr : Bool, (xr ≠ e.xr → e.xr = e.xa) →
    ∀ yr : Bool, (yr ≠ e.yr → e.yr = e.ya) →
    ∀ za : Bool, (za ≠ e.za → e.za ≠ e.zr) →
    ∀ g1 : Bool, (g1 ≠ e.g1 → g1 = e.xr ∧ (g1 = true → e.g2 = false ∧ e.za = false)) →
    ∀ g2 : Bool, (g2 ≠ e.g2 → g2 = e.yr ∧ (g2 = true → e.g1 = false ∧ e.za = false)) →
    (g1 && g2) = false →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.g1 || e.g2)) →
    (e.zr = false → zr = true → e.xa = false ∧ e.ya = false) →
    ∀ xa : Bool, (xa ≠ e.xa → e.g1 = xa ∧ e.za = xa) →
    ∀ ya : Bool, (ya ≠ e.ya → e.g2 = ya ∧ e.za = ya) →
    APers e xa ya g1 g2 zr za := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem grant_pers_tbl : ∀ e ∈ CM.atbl,
    ¬ (e.xr = true ∧ e.yr = true ∧ e.g1 = false ∧ e.g2 = false) →
    ∀ xr : Bool, (xr ≠ e.xr → e.xr = e.xa) →
    ∀ yr : Bool, (yr ≠ e.yr → e.yr = e.ya) →
    ∀ za : Bool, (za ≠ e.za → e.za ≠ e.zr) →
    ∀ g1 : Bool, (g1 ≠ e.g1 → g1 = e.xr ∧ (g1 = true → e.g2 = false ∧ e.za = false)) →
    ∀ g2 : Bool, (g2 ≠ e.g2 → g2 = e.yr ∧ (g2 = true → e.g1 = false ∧ e.za = false)) →
    (g1 && g2) = false →
    GPers e xr yr g1 g2 za := by
  decide +kernel

section amerge
variable {x y z : Chan} {g1 g2 : Trace}

theorem amerge_in_tbl (M : CM.AMerge x y z g1 g2) (hx : Protocol x) (hy : Protocol y)
    (hz : Protocol z) (t : Nat) :
    ∃ dx dy, (⟨x.req t, x.ack t, y.req t, y.ack t, g1 t, g2 t, z.req t, z.ack t, dx, dy⟩ : CM.AS)
      ∈ CM.atbl := by
  obtain ⟨dx, dy, hm, -⟩ := CM.amerge_inv M hx.1.1 hy.1.1 hz.1.2 t
    (fun s _ => ⟨(hx.2 s).1, (hy.2 s).1, (hz.2 s).2⟩)
  exact ⟨dx, dy, CM.amem hm⟩

theorem amerge_step_pers (M : CM.AMerge x y z g1 g2) (hx : Protocol x) (hy : Protocol y)
    (hz : Protocol z) (t : Nat) :
    APers ⟨x.req t, x.ack t, y.req t, y.ack t, g1 t, g2 t, z.req t, z.ack t, 0, 0⟩
      (x.ack (t + 1)) (y.ack (t + 1)) (g1 (t + 1)) (g2 (t + 1)) (z.req (t + 1)) (z.ack (t + 1)) := by
  obtain ⟨dx, dy, hm⟩ := amerge_in_tbl M hx hy hz t
  exact amerge_pers_tbl _ hm (x.req (t + 1)) (hx.2 t).1 (y.req (t + 1)) (hy.2 t).1
    (z.ack (t + 1)) (hz.2 t).2 (g1 (t + 1)) (M.H_ARB1 t) (g2 (t + 1)) (M.H_ARB2 t)
    (M.H_ARB_EXCL (t + 1)) (z.req (t + 1)) (M.zr t) (M.H_AMERGE_RTZ t) (x.ack (t + 1)) (M.xa t)
    (y.ack (t + 1)) (M.ya t)

theorem grant_step_pers (M : CM.AMerge x y z g1 g2) (hx : Protocol x) (hy : Protocol y)
    (hz : Protocol z) (t : Nat)
    (hnc : ¬ (x.req t = true ∧ y.req t = true ∧ g1 t = false ∧ g2 t = false)) :
    GPers ⟨x.req t, x.ack t, y.req t, y.ack t, g1 t, g2 t, z.req t, z.ack t, 0, 0⟩
      (x.req (t + 1)) (y.req (t + 1)) (g1 (t + 1)) (g2 (t + 1)) (z.ack (t + 1)) := by
  obtain ⟨dx, dy, hm⟩ := amerge_in_tbl M hx hy hz t
  exact grant_pers_tbl _ hm hnc (x.req (t + 1)) (hx.2 t).1 (y.req (t + 1)) (hy.2 t).1
    (z.ack (t + 1)) (hz.2 t).2 (g1 (t + 1)) (M.H_ARB1 t) (g2 (t + 1)) (M.H_ARB2 t)
    (M.H_ARB_EXCL (t + 1))

end amerge

/-! ## Link (over `ltbl`) -/

def LPers (e : Link.LS) (ir ia c orq oa : Bool) : Prop :=
  (AllB fun v : Bool => Formal.Cells.LinkHandshake.ctlB e.ir e.oa e.c false = v → e.c ≠ v →
    Formal.Cells.LinkHandshake.ctlB ir oa c false = v ∨ c = v) ∧
  (AllB fun v : Bool => e.c = v → e.ia ≠ v → c = v ∨ ia = v) ∧
  (AllB fun v : Bool => e.c = v → e.orq ≠ v → c = v ∨ orq = v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (e : Link.LS) (ir ia c orq oa : Bool) : Decidable (LPers e ir ia c orq oa) := by
  unfold LPers; exact inferInstance

set_option maxRecDepth 100000 in
theorem link_pers_tbl : ∀ e ∈ Link.ltbl,
    ∀ ir : Bool, (ir ≠ e.ir → e.ir = e.ia) →
    ∀ oa : Bool, (oa ≠ e.oa → e.oa ≠ e.orq) →
    ∀ c : Bool, (c ≠ e.c → c = Formal.Cells.LinkHandshake.ctlB e.ir e.oa e.c false) →
    ∀ ia : Bool, (ia ≠ e.ia → ia = e.c) →
    ∀ orq : Bool, (orq ≠ e.orq → orq = e.c) →
    LPers e ir ia c orq oa := by
  decide +kernel

section link
variable {i o : Chan} {c : Trace}

theorem link_step_pers (L : Link.Link i o c) (hi : Protocol i) (ho : Protocol o) (t : Nat) :
    LPers ⟨i.req t, i.ack t, c t, o.req t, o.ack t, 0, 0⟩ (i.req (t + 1)) (i.ack (t + 1)) (c (t + 1))
      (o.req (t + 1)) (o.ack (t + 1)) := by
  obtain ⟨d, q, hm, -⟩ := Link.link_inv L hi.1.1 ho.1.2 t (fun s _ => ⟨(hi.2 s).1, (ho.2 s).2⟩)
  exact link_pers_tbl _ (Link.lmem hm) (i.req (t + 1)) (hi.2 t).1 (o.ack (t + 1)) (ho.2 t).2
    (c (t + 1)) (L.H_CEL_SI t) (i.ack (t + 1)) (L.H_ACK_DI t) (o.req (t + 1)) (L.H_REQ_DI t)

end link

end Formal.Net.CapNet.Live.Nd3
