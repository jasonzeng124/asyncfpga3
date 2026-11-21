import Formal.Net.OpsMux

/-!
# Probe C-8j (2): `control_merge` / `merge` as bdc lowers it (`bdc_amerge2`)

`bdc/emit.py` (`emit_amerge`, n = 2, `_op_merge`, `_op_control_merge`):

    bd_arbiter   r1 = in0_req, A1 = in0_ack, r2 = in1_req, A2 = in1_ack, A0 = z_ack
                 g1 = r1.q, g2 = r2.~q, R0 = g1 + g2, A1 = C(g1, A0), A2 = C(g2, A0)
    won    = g2 | in1_ack                (the index, "rises with the grant, falls with the ack")
    z_data = won ? in1_data : in0_data
    z_req  = delta(uor(R0))

`control_merge` forks this cell's output into the result and the index
channel (`bd_fork`, 8f's `Fork`); the projections are wires. Here the output
bus carries both: `z.dat = 2 * data + won`.

Gate model `AMerge x y z g1 g2` (SI, binary). The arbiter's choice is FREE:
`g1`, `g2` are arbitrary traces subject only to
* H_ARB: a grant moves only to its request's previous value, and rises only
  while the other grant and `A0` are low (q is frozen while `A0` is high:
  B's `stA_eq`, `A0 ? q : stF`);
* H_ARB_EXCL: never both grants high. This is the cell-level obligation that
  B discharges: `ArbBinary.settled_exclusion` (structural, settled q) and, in
  time, `exclusion_transport` / `rt1_exclusion` (B-obligations R1, R2, A2);
* H_CEL_SI on `A1`, `A2`; H_DELAY_LUMPED for `uor` + `udly` (one unbounded
  inertial node from `g1 ∨ g2` to `z_req`);
* H_AMERGE_RTZ: `z_req` rises only while both input acknowledges are low.
  NEW obligation found here. `won = g2 | A2` and `A2 = C(g2, A0)` falls only
  after `A0↓`; in an SI model the next winner's grant and `z_req` can
  overtake that fall, and then the next token is offered with a stale index
  (`Wip/C8j/amerge_reach.py` without the rule: the counters diverge, i.e. a
  wrong-input offer). In the fabric it is the race `A0↓ → ua2 → A2↓` (one
  C-element LUT) against `A0↓ → ustate (q) → ugrant → uor → udly → z_req`
  (the matched delay), so it holds with a large margin, but it is a timing
  fact and must be checked like B's H_MUX_RTZ.
* H_DATA_COMB: `z.dat t = 2 * (won ? y.dat : x.dat) + won` at every tick.

The reachable set `atbl` (38 states, counters included) is found by
`Wip/C8j/amerge_reach.py`; `amerge_closed` re-checks its closure by kernel
`decide`.

Proved:
* `amerge_proto`, `amerge_op`: the network-level `OpProto` + `OpData` with the
  token equation relative to an ORACLE, the winner stream `ω`:
  `σ z k = 2 * (if ω k then σ y (#ω before k) else σ x (#¬ω before k)) + [ω k]`,
  where `ω = winner (ch z)` is read off the circuit (the index bit of the k-th
  offer). So `Ops.net_refines` / `net_determinate` apply unchanged: the
  network is determinate MODULO the winner stream.
* `amerge_forced`: if the two requests are never high together
  (H_EXCL_REQ; what one invocation in flight gives the loop header: the entry
  token and the back-edge token are never pending together) then the winner of
  every token is the input that is requesting at its offer: the arbiter's free
  choice is never exercised.
-/

namespace Formal.Net.Ops.CM
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.Ops.Mux (b2n)

structure AS where
  xr : Bool
  xa : Bool
  yr : Bool
  ya : Bool
  g1 : Bool
  g2 : Bool
  zr : Bool
  za : Bool
  dx : Nat
  dy : Nat
  deriving DecidableEq

def atbl : List AS := [
  ⟨false, false, false, false, false, false, false, false, 1, 1⟩,
  ⟨true, false, false, false, false, false, false, false, 2, 1⟩,
  ⟨false, true, false, false, false, false, false, false, 1, 1⟩,
  ⟨false, false, true, false, false, false, false, false, 1, 2⟩,
  ⟨true, false, true, false, false, false, false, false, 2, 2⟩,
  ⟨false, true, true, false, false, false, false, false, 1, 2⟩,
  ⟨false, false, false, true, false, false, false, false, 1, 1⟩,
  ⟨true, false, false, true, false, false, false, false, 2, 1⟩,
  ⟨true, false, false, false, true, false, false, false, 2, 1⟩,
  ⟨true, false, true, false, true, false, false, false, 2, 2⟩,
  ⟨true, false, false, true, true, false, false, false, 2, 1⟩,
  ⟨false, false, true, false, false, true, false, false, 1, 2⟩,
  ⟨true, false, true, false, false, true, false, false, 2, 2⟩,
  ⟨false, true, true, false, false, true, false, false, 1, 2⟩,
  ⟨true, false, false, false, true, false, true, false, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, false, 1, 2⟩,
  ⟨false, false, true, false, false, true, true, false, 1, 1⟩,
  ⟨true, false, true, false, false, true, true, false, 2, 1⟩,
  ⟨false, true, false, false, false, false, false, true, 1, 1⟩,
  ⟨false, true, true, false, false, false, false, true, 1, 2⟩,
  ⟨false, false, false, true, false, false, false, true, 1, 1⟩,
  ⟨true, false, false, true, false, false, false, true, 2, 1⟩,
  ⟨false, true, false, false, false, false, true, true, 1, 1⟩,
  ⟨false, true, true, false, false, false, true, true, 1, 2⟩,
  ⟨false, false, false, true, false, false, true, true, 1, 1⟩,
  ⟨true, false, false, true, false, false, true, true, 2, 1⟩,
  ⟨true, false, false, false, true, false, true, true, 1, 1⟩,
  ⟨false, true, false, false, true, false, true, true, 1, 1⟩,
  ⟨true, true, false, false, true, false, true, true, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, true, 1, 2⟩,
  ⟨false, true, true, false, true, false, true, true, 1, 2⟩,
  ⟨true, true, true, false, true, false, true, true, 1, 2⟩,
  ⟨false, false, true, false, false, true, true, true, 1, 1⟩,
  ⟨true, false, true, false, false, true, true, true, 2, 1⟩,
  ⟨false, false, false, true, false, true, true, true, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, true, 2, 1⟩,
  ⟨false, false, true, true, false, true, true, true, 1, 1⟩,
  ⟨true, false, true, true, false, true, true, true, 2, 1⟩]

def anxt (e : AS) (xr xa yr ya g1 g2 zr za : Bool) : AS :=
  ⟨xr, xa, yr, ya, g1, g2, zr, za,
   e.dx + b2n (!e.xr && xr) - b2n (!e.zr && zr && !(g2 || ya)),
   e.dy + b2n (!e.yr && yr) - b2n (!e.zr && zr && (g2 || ya))⟩

def AConcl (e : AS) (xr xa yr ya g1 g2 zr za : Bool) : Prop :=
  let n := anxt e xr xa yr ya g1 g2 zr za
  atbl.contains n = true ∧
  n.dx + b2n (!e.zr && zr && !(g2 || ya)) = e.dx + b2n (!e.xr && xr) ∧
  n.dy + b2n (!e.zr && zr && (g2 || ya)) = e.dy + b2n (!e.yr && yr) ∧
  (xa ≠ e.xa → e.xa ≠ e.xr) ∧ (ya ≠ e.ya → e.ya ≠ e.yr) ∧ (zr ≠ e.zr → e.zr = e.za) ∧
  ((!e.zr && zr) = true → e.za = false ∧
     (if (g2 || ya) then e.yr = true ∧ e.ya = false ∧ e.dy = 2 ∧ e.xr = e.xr
      else e.xr = true ∧ e.xa = false ∧ e.dx = 2))

instance (e : AS) (xr xa yr ya g1 g2 zr za : Bool) : Decidable (AConcl e xr xa yr ya g1 g2 zr za) := by
  unfold AConcl; exact inferInstance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem amerge_closed : ∀ e ∈ atbl,
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
    AConcl e xr xa yr ya g1 g2 zr za := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem amerge_guar : ∀ e ∈ atbl,
    ∀ xa : Bool, (xa ≠ e.xa → e.g1 = xa ∧ e.za = xa) →
    ∀ ya : Bool, (ya ≠ e.ya → e.g2 = ya ∧ e.za = ya) →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.g1 || e.g2)) →
    (xa ≠ e.xa → e.xa ≠ e.xr) ∧ (ya ≠ e.ya → e.ya ≠ e.yr) ∧ (zr ≠ e.zr → e.zr = e.za) := by
  decide +kernel

theorem amerge_init :
    atbl.contains ⟨false, false, false, false, false, false, false, false, 1, 1⟩ = true := by decide

/-- The gate model of `bdc_amerge2`, the arbiter's grants free (see the header). -/
structure AMerge (x y z : Chan) (g1 g2 : Trace) : Prop where
  H_ARB1 : ∀ t, g1 (t + 1) ≠ g1 t → g1 (t + 1) = x.req t ∧ (g1 (t + 1) = true → g2 t = false ∧ z.ack t = false)
  H_ARB2 : ∀ t, g2 (t + 1) ≠ g2 t → g2 (t + 1) = y.req t ∧ (g2 (t + 1) = true → g1 t = false ∧ z.ack t = false)
  H_ARB_EXCL : ∀ t, (g1 t && g2 t) = false
  zr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (g1 t || g2 t)
  H_AMERGE_RTZ : ∀ t, z.req t = false → z.req (t + 1) = true → x.ack t = false ∧ y.ack t = false
  xa : ∀ t, x.ack (t + 1) ≠ x.ack t → g1 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)
  ya : ∀ t, y.ack (t + 1) ≠ y.ack t → g2 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)
  dat : ∀ t, z.dat t = 2 * (if (g2 t || y.ack t) then y.dat t else x.dat t) + b2n (g2 t || y.ack t)
  i1 : g1 0 = false
  i2 : g2 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false

variable {x y z : Chan} {g1 g2 : Trace}

def ast (x y z : Chan) (g1 g2 : Trace) (t dx dy : Nat) : AS :=
  ⟨x.req t, x.ack t, y.req t, y.ack t, g1 t, g2 t, z.req t, z.ack t, dx, dy⟩

/-- The index bit `won` of the output. -/
def won (y : Chan) (g2 : Trace) (t : Nat) : Bool := g2 t || y.ack t

/-- #z offers (before `t`) whose index is 0 / 1. -/
def zc0 (y z : Chan) (g2 : Trace) : Nat → Nat := cnt (fun u => riseB z.req u && !won y g2 (u + 1))
def zc1 (y z : Chan) (g2 : Trace) : Nat → Nat := cnt (fun u => riseB z.req u && won y g2 (u + 1))

theorem amem {e : AS} (h : atbl.contains e = true) : e ∈ atbl := by simpa using h

theorem amerge_inv (M : AMerge x y z g1 g2) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hz : z.ack 0 = false) : ∀ t,
    (∀ s, s < t → SendStep x s ∧ SendStep y s ∧ RecvStep z s) →
    ∃ dx dy, atbl.contains (ast x y z g1 g2 t dx dy) = true ∧
      cnt (riseB x.req) t + 1 = zc0 y z g2 t + dx ∧
      cnt (riseB y.req) t + 1 = zc1 y z g2 t + dy := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨1, 1, ?_, rfl, rfl⟩
    simp only [ast, hx, hy, hz, M.i1, M.i2, M.iz, M.ix, M.iy]
    exact amerge_init
  | succ t ih =>
    intro hp
    obtain ⟨dx, dy, hm, h1, h2⟩ := ih (fun s hs => hp s (by omega))
    obtain ⟨sx, sy, rz⟩ := hp t (by omega)
    have K := amerge_closed _ (amem hm) (x.req (t + 1)) sx (y.req (t + 1)) sy (z.ack (t + 1)) rz
      (g1 (t + 1)) (M.H_ARB1 t) (g2 (t + 1)) (M.H_ARB2 t) (M.H_ARB_EXCL (t + 1))
      (z.req (t + 1)) (M.zr t) (M.H_AMERGE_RTZ t) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
    obtain ⟨Km, Kx, Ky, _⟩ := K
    refine ⟨_, _, Km, ?_, ?_⟩
    · have e1 : cnt (riseB x.req) (t + 1) = cnt (riseB x.req) t + b2n (!x.req t && x.req (t + 1)) := rfl
      have e2 : zc0 y z g2 (t + 1) = zc0 y z g2 t +
          b2n (!z.req t && z.req (t + 1) && !(g2 (t + 1) || y.ack (t + 1))) := rfl
      simp only [ast, anxt] at Kx ⊢
      omega
    · have e1 : cnt (riseB y.req) (t + 1) = cnt (riseB y.req) t + b2n (!y.req t && y.req (t + 1)) := rfl
      have e2 : zc1 y z g2 (t + 1) = zc1 y z g2 t +
          b2n (!z.req t && z.req (t + 1) && (g2 (t + 1) || y.ack (t + 1))) := rfl
      simp only [ast, anxt] at Ky ⊢
      omega

theorem amerge_proto (M : AMerge x y z g1 g2) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hz : z.ack 0 = false) : ∀ t,
    (∀ s, s < t → SendStep x s ∧ SendStep y s ∧ RecvStep z s) →
    RecvStep x t ∧ RecvStep y t ∧ SendStep z t := by
  intro t hp
  obtain ⟨dx, dy, hm, _⟩ := amerge_inv M hx hy hz t hp
  exact amerge_guar _ (amem hm) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
    (z.req (t + 1)) (M.zr t)

/-! ## Network level: the winner stream as an oracle -/

variable {C : Type}

/-- The winner stream read off a channel: the index bit of its `k`-th offer. -/
noncomputable def winner (c : Chan) (k : Nat) : Bool :=
  @decide (∃ r, OffAt c k r ∧ c.dat (r + 1) % 2 = 1) (Classical.propDecidable _)

theorem winner_at {c : Chan} {k r : Nat} (h : OffAt c k r) :
    winner c k = (c.dat (r + 1) % 2 == 1) := by
  unfold winner
  by_cases hb : c.dat (r + 1) % 2 = 1
  · have : ∃ r, OffAt c k r ∧ c.dat (r + 1) % 2 = 1 := ⟨r, h, hb⟩
    simp [this, hb]
  · have : ¬ ∃ r, OffAt c k r ∧ c.dat (r + 1) % 2 = 1 := by
      rintro ⟨r', h', hb'⟩; rw [off_unique h h'] at hb; exact hb hb'
    simp [this, hb]

/-- The merge's token equation relative to the winner stream `ω`. -/
def amergeEq (ω : Nat → Bool) (cx cy cz : C) (σ : C → Nat → Nat) : Prop :=
  ∀ k, σ cz k = 2 * (if ω k then σ cy (cnt ω k) else σ cx (cnt (fun i => !ω i) k)) + b2n (ω k)

theorem cnt_congr_lt {f g : Nat → Bool} : ∀ k, (∀ i, i < k → f i = g i) → cnt f k = cnt g k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih => intro h; simp only [cnt, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem cnt_ge_aux (f : Nat → Bool) : ∀ r k, k + 1 ≤ cnt f r → ∃ e, e < r ∧ f e = true ∧ cnt f e = k := by
  intro r
  induction r with
  | zero => intro k h; simp [cnt] at h
  | succ r ih =>
    intro k h
    by_cases h1 : k + 1 ≤ cnt f r
    · obtain ⟨e, he, h2, h3⟩ := ih k h1; exact ⟨e, by omega, h2, h3⟩
    · simp only [cnt] at h
      cases hf : f r
      · simp [hf] at h; omega
      · simp [hf] at h; exact ⟨r, by omega, hf, by omega⟩

theorem b2n_mod (w : Bool) (v : Nat) : (2 * v + b2n w) % 2 = b2n w := by
  cases w <;> simp [b2n] <;> omega

theorem amerge_op (ch : C → Chan) (cx cy cz : C) (g1 g2 : Trace)
    (M : AMerge (ch cx) (ch cy) (ch cz) g1 g2) :
    OpProto ch [cx, cy] [cz] ∧ OpData ch [cx, cy] [cz] (amergeEq (winner (ch cz)) cx cy cz) := by
  have mx : cx ∈ [cx, cy] := by simp
  have my : cy ∈ [cx, cy] := by simp
  have mz : cz ∈ [cz] := List.mem_singleton_self _
  refine ⟨⟨fun t hi ho _ hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := amerge_proto M (hi cx mx).1 (hi cy my).1 (ho cz mz).2 t
      (fun s hs => ⟨((hp s hs).1 cx mx).1, ((hp s hs).1 cy my).1, ((hp s hs).2 cz mz).2⟩)
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · simp at hc'
      rcases hc' with rfl | rfl
      · exact h.1
      · exact h.2.1
    · rw [List.mem_singleton.1 hc']; exact h.2.2
  · intro c' hc'; simp at hc'
    rcases hc' with rfl | rfl
    · exact M.ix
    · exact M.iy
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact M.iz
  · intro hin hout c' hc' k r' hoff σ hag hE
    rw [List.mem_singleton.1 hc'] at hoff ⊢
    obtain ⟨hpx, hhx⟩ := hin cx mx
    obtain ⟨hpy, hhy⟩ := hin cy my
    have hpz := (hout cz mz).1
    obtain ⟨dx, dy, hm, h1, h2⟩ := amerge_inv M hpx.1.1 hpy.1.1 hpz.1.2 r'
      (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpz.2 s).2⟩)
    have hr0 : (ch cz).req r' = false := by have := hoff.1; simp [riseB] at this; exact this.1
    have hr1 : (ch cz).req (r' + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
    have K := amerge_closed _ (amem hm) _ (hpx.2 r').1 _ (hpy.2 r').1 _ (hpz.2 r').2
      _ (M.H_ARB1 r') _ (M.H_ARB2 r') (M.H_ARB_EXCL (r' + 1)) _ (M.zr r') (M.H_AMERGE_RTZ r')
      _ (M.xa r') _ (M.ya r')
    have Ko := K.2.2.2.2.2.2
    simp only [ast, hr0, hr1] at Ko
    obtain ⟨_, hsel⟩ := Ko rfl
    -- the winner of this token and the counts of earlier winners
    have hw : winner (ch cz) k = won (ch cy) g2 (r' + 1) := by
      rw [winner_at hoff, M.dat, b2n_mod]; unfold won
      cases g2 (r' + 1) || (ch cy).ack (r' + 1) <;> rfl
    have hagz : ∀ i u, u < r' → OffAt (ch cz) i u → σ cz i = (ch cz).dat (u + 1) :=
      fun i u hu ho => hag cz i u hu ho
    have hwi : ∀ i, i < k → (σ cz i % 2 == 1) = winner (ch cz) i := by
      intro i hi
      have : cnt (riseB (ch cz).req) r' = k := hoff.2
      obtain ⟨u, hu, hf, hc⟩ := cnt_ge_aux (riseB (ch cz).req) r' i (by omega)
      rw [hagz i u hu ⟨hf, hc⟩, winner_at ⟨hf, hc⟩]
    have hwon : ∀ u, ((ch cz).dat (u + 1) % 2 == 1) = won (ch cy) g2 (u + 1) := by
      intro u; rw [M.dat, b2n_mod]; unfold won; cases g2 (u + 1) || (ch cy).ack (u + 1) <;> rfl
    have c1 : zc1 (ch cy) (ch cz) g2 r' = cnt (winner (ch cz)) k := by
      have := cnt_offers (σ := σ cz) (fun v => v % 2 == 1) hagz r' (Nat.le_refl _)
      rw [show cnt (riseB (ch cz).req) r' = k from hoff.2] at this
      rw [cnt_congr_lt k hwi] at this
      rw [← this]; unfold zc1; congr 1; funext u; rw [hwon]
    have c0 : zc0 (ch cy) (ch cz) g2 r' = cnt (fun i => !winner (ch cz) i) k := by
      have := cnt_offers (σ := σ cz) (fun v => !(v % 2 == 1)) hagz r' (Nat.le_refl _)
      rw [show cnt (riseB (ch cz).req) r' = k from hoff.2] at this
      rw [cnt_congr_lt k (fun i hi => by rw [hwi i hi])] at this
      rw [← this]; unfold zc0; congr 1; funext u; rw [hwon]
    rw [hE k, M.dat, hw]
    unfold won
    cases hs : (g2 (r' + 1) || (ch cy).ack (r' + 1))
    · rw [hs] at hsel
      simp only [Bool.false_eq_true, ite_false] at hsel ⊢
      obtain ⟨hxr, hxa, hdx⟩ := hsel
      obtain ⟨rx, ix, hrx, hoffx, hcrx, hcfx, _⟩ := open_offer hpx hxr
      have hcfx' : cnt (fallB (ch cx).ack) (r' + 1) = ix := by simp [cnt, fallB, hxa, hcfx]
      have hix : cnt (fun i => !winner (ch cz) i) k = ix := by
        omega
      rw [hix, hag cx ix rx hrx hoffx, held_at hpx hhx hoffx (by omega) hcfx']
    · rw [hs] at hsel
      simp only [ite_true] at hsel ⊢
      obtain ⟨hyr, hya, hdy, _⟩ := hsel
      obtain ⟨ry, iy, hry, hoffy, hcry, hcfy, _⟩ := open_offer hpy hyr
      have hcfy' : cnt (fallB (ch cy).ack) (r' + 1) = iy := by simp [cnt, fallB, hya, hcfy]
      have hiy : cnt (winner (ch cz)) k = iy := by
        omega
      rw [hiy, hag cy iy ry hry hoffy, held_at hpy hhy hoffy (by omega) hcfy']

/-- H_EXCL_REQ forces the winner: if the two requests are never high
together, the winner of the `k`-th output token is the input requesting at its
offer; the arbiter's free choice is never used. -/
theorem amerge_forced (M : AMerge x y z g1 g2) (hpx : Protocol x) (hpy : Protocol y)
    (hpz : Protocol z) (H_EXCL_REQ : ∀ t, (x.req t && y.req t) = false)
    {k r : Nat} (hoff : OffAt z k r) : winner z k = y.req r := by
  obtain ⟨dx, dy, hm, _⟩ := amerge_inv M hpx.1.1 hpy.1.1 hpz.1.2 r
    (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpz.2 s).2⟩)
  have hr0 : z.req r = false := by have := hoff.1; simp [riseB] at this; exact this.1
  have hr1 : z.req (r + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
  have K := amerge_closed _ (amem hm) _ (hpx.2 r).1 _ (hpy.2 r).1 _ (hpz.2 r).2
    _ (M.H_ARB1 r) _ (M.H_ARB2 r) (M.H_ARB_EXCL (r + 1)) _ (M.zr r) (M.H_AMERGE_RTZ r)
    _ (M.xa r) _ (M.ya r)
  have Ko := K.2.2.2.2.2.2
  simp only [ast, hr0, hr1] at Ko
  obtain ⟨_, hsel⟩ := Ko rfl
  have hw : winner z k = (g2 (r + 1) || y.ack (r + 1)) := by
    rw [winner_at hoff, M.dat, b2n_mod]; cases g2 (r + 1) || y.ack (r + 1) <;> rfl
  rw [hw]
  have he := H_EXCL_REQ r
  cases hs : (g2 (r + 1) || y.ack (r + 1))
  · rw [hs] at hsel; simp at hsel
    rw [hsel.1] at he; simpa using he
  · rw [hs] at hsel; simp at hsel; exact hsel.1.symm

end Formal.Net.Ops.CM
