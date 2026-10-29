import Formal.Cells.RigSrc
import Formal.Cells.RigSrcWitnessData

/-!
# Probe Bjw (shard B): a joint non-vacuity witness for `RigSrc.gcd_rig_first_env`

Notes: `formal/notes/B-rig-src-witness.md`. Builds on `RigSrc` (probe Bsrc) and on shard C's
`CapstoneWitnessLib` (event-list runs and the kernel checker `kChk`, used, never edited).

`gcd_rig_first_env` (RigSrc §4) assumes the kernel's cell models on the run (H_KER), H_BUNDLE,
the environment wiring (H_FORK_WIRE, H_DAT), the release state (H_REL, H_REL0), out0's
acknowledge = uenv0 (H_OUT0_ACK), the env cells' step forms through monotone causal read maps
(H_UENV1_B, H_C3, M1, M0). Probe Bsa3 (`SelfAuditB6.rig_env_feeds`) already gave a joint
witness with every read map the identity and no urdly delay. This file gives one with LAGGED
reads everywhere the theorem allows them.

## Results

* §1 `cell_sh1`: shifting a C-convention run (every request and acknowledge low at tick 0) one
  tick to the left keeps EVERY non-source cell model, reset fields included. (A reset field at
  the new tick 0 is the old tick 1; a cell's driven wire could only have moved at step 0 to a
  function of tick-0 values, which are all low.) This is how a run whose source requests are
  HIGH at tick 0 (the rig's release state) is obtained from event lists, which start low.
* §2 the run `chR` (a = 12, b = 18, `RigSrcWitnessData`): C's gcd_hw network, kernel gates with
  delay 1, closed by the rig's env: fork wires; the c3 reading `a`/`b`/`start` acks 2/3/5 ticks
  late; uenv1 = C(q, ¬k) reading `k` 3 and `q` 5 ticks late; uenv0 = C(res_req, ¬e) with
  urdly = 7 ticks on `out0.req` and `e` read 4 ticks late; every env gate fires 1 tick after its
  reads.
* §3 `gcd_rig_first_env_joint`: ONE run, ONE choice of env traces and of read maps
  `β t = t - 3`, `φ1 t = t - 5`, `φ0 t = t - 4`, `γ z t = t - 2|3|5` (strictly lagging from
  tick 5) meet ALL hypotheses of `gcd_rig_first_env` jointly; out0 offers its first token at rig
  tick 438 and latches it (ack falls) at 489, carrying 6. `w_nondegenerate` (decided): the c3
  holds low while two (then all three) acks are high; uenv1 holds while excited (stale reads)
  and holds `e` low while `q = 0` (the hold H_ENV rests on); uenv0 holds `q` low for 7 ticks
  with `out0.req` high (urdly). `gcd_rig_witness_consistent`: the theorem on the run gives 6.

Assumed: nothing beyond the run (everything is decided by kernel `decide`).
NOT covered: other inputs, other schedules (one schedule, fixed lags; kernel gate delays all 1),
per-pin skew INSIDE kernel cells (C's models have none), the silicon. After uenv1's second rise
the env is stopped (an inertial hold, allowed by every env hypothesis, all of which are guarded
step forms); the kernel runs to quiescence.
-/

namespace Formal.Cells.RigSrcWitness
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
  Formal.Net.CapNet.Wit

set_option maxRecDepth 100000

/-! ## 1. Shifting a C-convention run by one tick -/

/-- Request and acknowledge low at tick 0. -/
def Low0 (c : Chan) : Prop := c.req 0 = false ∧ c.ack 0 = false

theorem r1 {x : Nat → Bool} (h0 : x 0 = false) (g : x 1 ≠ x 0 → x 1 = false) : x 1 = false := by
  by_cases h : x 1 = x 0
  · rw [h, h0]
  · exact g h

theorem ex_mem {α : Type} {l : List α} (h : l ≠ []) : ∃ x, x ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x _ => exact ⟨x, List.mem_cons_self ..⟩

section sh

theorem fork_sh {a : Chan} {os : List Chan} (F : Fork.Fork a os) (ha : Low0 a)
    (ho : ∀ o ∈ os, Low0 o) : Fork.Fork (rtC (shf 1) a) (os.map (rtC (shf 1))) := by
  have hs := shf_mono 1
  refine ⟨by simpa using F.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro o hm'; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 hm'
    exact rt_guard hs o.req (fun s s' => o.req s' = a.req s) (F.wire o hm)
  · intro t hne o hm'; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 hm'
    exact rt_guard hs a.ack (fun s s' => o.ack s = a.ack s') (fun t h => F.cel t h o hm) t hne
  · intro o hm' t; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 hm'; exact F.dat o hm _
  · show a.ack 1 = false
    refine r1 F.initA (fun h => ?_)
    obtain ⟨o, hm⟩ := ex_mem F.ne
    rw [← F.cel 0 h o hm]; exact (ho o hm).2
  · intro o hm'; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 hm'
    show o.req 1 = false
    exact r1 (F.initO o hm) (fun h => (F.wire o hm 0 h).trans ha.1)

theorem join_sh {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : Join.Join g is o)
    (hi : ∀ i ∈ is, Low0 i) (ho : Low0 o) :
    Join.Join g (is.map (rtC (shf 1))) (rtC (shf 1) o) := by
  have hs := shf_mono 1
  refine ⟨by simpa using J.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hne i hm'; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hm'
    exact rt_guard hs o.req (fun s s' => i.req s = o.req s') (fun t h => J.cel t h i hm) t hne
  · intro i hm'; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hm'
    exact rt_guard hs i.ack (fun s s' => i.ack s' = o.ack s) (J.wire i hm)
  · intro t; simp only [List.map_map]; exact J.dat _
  · show o.req 1 = false
    refine r1 J.initO (fun h => ?_)
    obtain ⟨i, hm⟩ := ex_mem J.ne
    rw [← J.cel 0 h i hm]; exact (hi i hm).1
  · intro i hm'; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hm'
    show i.ack 1 = false
    exact r1 (J.initI i hm) (fun h => (J.wire i hm 0 h).trans ho.2)

theorem steer_sh {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer.Steer sel f j out) (hj : Low0 j) (ho : ∀ b, Low0 (out b)) :
    Steer.Steer sel f (rtC (shf 1) j) (fun b => rtC (shf 1) (out b)) := by
  have hs := shf_mono 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact rt_guard hs (out b).req (fun s s' => (out b).req s' = (j.req s && (sel (j.dat s) == b)))
      (S.lut b)
  · exact rt_guard hs j.ack (fun s s' => j.ack s' = ((out true).ack s || (out false).ack s)) S.orr
  · intro b t; exact S.dat b _
  · show j.ack 1 = false
    exact r1 S.initJ (fun h => by rw [S.orr 0 h, (ho true).2, (ho false).2]; rfl)
  · intro b; show (out b).req 1 = false
    exact r1 (S.initO b) (fun h => by rw [S.lut b 0 h, hj.1]; rfl)

theorem mux_sh {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}
    (M : Mux.Mux sel x y c z j0 j1) (hx : Low0 x) (hy : Low0 y) (hz : Low0 z) :
    Mux.Mux sel (rtC (shf 1) x) (rtC (shf 1) y) (rtC (shf 1) c) (rtC (shf 1) z)
      (rtT (shf 1) j0) (rtT (shf 1) j1) := by
  have hs := shf_mono 1
  have e0 : j0 1 = false := r1 M.i0 (fun h => (M.cj0 0 h).1.symm.trans hx.1)
  have e1 : j1 1 = false := r1 M.i1 (fun h => (M.cj1 0 h).1.symm.trans hy.1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rt_guard hs j0 (fun s s' => x.req s = j0 s' ∧ (c.req s && !sel (c.dat s)) = j0 s') M.cj0
  · exact rt_guard hs j1 (fun s s' => y.req s = j1 s' ∧ (c.req s && sel (c.dat s)) = j1 s') M.cj1
  · exact rt_guard hs z.req (fun s s' => z.req s' = (j0 s || j1 s)) M.zr
  · exact rt_guard hs x.ack (fun s s' => j0 s = x.ack s' ∧ z.ack s = x.ack s') M.xa
  · exact rt_guard hs y.ack (fun s s' => j1 s = y.ack s' ∧ z.ack s = y.ack s') M.ya
  · exact rt_guard hs c.ack (fun s s' => c.ack s' = z.ack s) M.ca
  · intro t; exact M.dat _
  · exact e0
  · exact e1
  · show z.req 1 = false
    exact r1 M.iz (fun h => by rw [M.zr 0 h, M.i0, M.i1]; rfl)
  · show x.ack 1 = false
    exact r1 M.ix (fun h => (M.xa 0 h).2.symm.trans hz.2)
  · show y.ack 1 = false
    exact r1 M.iy (fun h => (M.ya 0 h).2.symm.trans hz.2)
  · show c.ack 1 = false
    exact r1 M.ic (fun h => (M.ca 0 h).trans hz.2)

theorem muxn_sh {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}
    (M : MuxN.MuxN sel xs c z j) (hx : ∀ k, Low0 (xs k)) (hz : Low0 z) :
    MuxN.MuxN sel (fun k => rtC (shf 1) (xs k)) (rtC (shf 1) c) (rtC (shf 1) z)
      (fun k => rtT (shf 1) (j k)) := by
  have hs := shf_mono 1
  have ej : ∀ k, k < 3 → j k 1 = false := fun k hk =>
    r1 (M.ij k hk) (fun h => (M.cj k hk 0 h).1.symm.trans (hx k).1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact rt_guard hs (j k)
      (fun s s' => (xs k).req s = j k s' ∧ (c.req s && (sel (c.dat s) == k)) = j k s') (M.cj k hk)
  · exact rt_guard hs z.req (fun s s' => z.req s' = (j 0 s || j 1 s || j 2 s)) M.zr
  · intro k hk
    exact rt_guard hs (xs k).ack (fun s s' => j k s = (xs k).ack s' ∧ z.ack s = (xs k).ack s')
      (M.xa k hk)
  · exact rt_guard hs c.ack (fun s s' => c.ack s' = z.ack s) M.ca
  · intro t; exact M.dat _
  · intro k hk; exact ej k hk
  · show z.req 1 = false
    exact r1 M.iz (fun h => by
      rw [M.zr 0 h, M.ij 0 (by decide), M.ij 1 (by decide), M.ij 2 (by decide)]; rfl)
  · intro k hk; show (xs k).ack 1 = false
    exact r1 (M.ix k hk) (fun h => (M.xa k hk 0 h).2.symm.trans hz.2)
  · show c.ack 1 = false
    exact r1 M.ic (fun h => (M.ca 0 h).trans hz.2)

theorem amerge_sh {x y z : Chan} {g1 g2 : Trace} (M : CM.AMerge x y z g1 g2)
    (hx : Low0 x) (hy : Low0 y) (hz : Low0 z) :
    CM.AMerge (rtC (shf 1) x) (rtC (shf 1) y) (rtC (shf 1) z) (rtT (shf 1) g1) (rtT (shf 1) g2) := by
  have hs := shf_mono 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rt_guard hs g1
      (fun s s' => g1 s' = x.req s ∧ (g1 s' = true → g2 s = false ∧ z.ack s = false)) M.H_ARB1
  · exact rt_guard hs g2
      (fun s s' => g2 s' = y.req s ∧ (g2 s' = true → g1 s = false ∧ z.ack s = false)) M.H_ARB2
  · intro t; exact M.H_ARB_EXCL _
  · exact rt_guard hs z.req (fun s s' => z.req s' = (g1 s || g2 s)) M.zr
  · intro t h1 h2
    simp only [rtC] at h1 h2 ⊢
    rcases hs t with e | e
    · rw [e, h1] at h2; exact absurd h2 (by decide)
    · rw [e] at h2; exact M.H_AMERGE_RTZ _ h1 h2
  · exact rt_guard hs x.ack (fun s s' => g1 s = x.ack s' ∧ z.ack s = x.ack s') M.xa
  · exact rt_guard hs y.ack (fun s s' => g2 s = y.ack s' ∧ z.ack s = y.ack s') M.ya
  · intro t; exact M.dat _
  · show g1 1 = false
    exact r1 M.i1 (fun h => (M.H_ARB1 0 h).1.trans hx.1)
  · show g2 1 = false
    exact r1 M.i2 (fun h => (M.H_ARB2 0 h).1.trans hy.1)
  · show z.req 1 = false
    exact r1 M.iz (fun h => by rw [M.zr 0 h, M.i1, M.i2]; rfl)
  · show x.ack 1 = false
    exact r1 M.ix (fun h => (M.xa 0 h).2.symm.trans hz.2)
  · show y.ack 1 = false
    exact r1 M.iy (fun h => (M.ya 0 h).2.symm.trans hz.2)

theorem link_sh {i o : Chan} {c : Trace} (L : Link.Link i o c) (hi : Low0 i) (ho : Low0 o) :
    Link.Link (rtC (shf 1) i) (rtC (shf 1) o) (rtT (shf 1) c) := by
  have hs := shf_mono 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rt_guard hs c
      (fun s s' => c s' = Formal.Cells.LinkHandshake.ctlB (i.req s) (o.ack s) (c s) false)
      L.H_CEL_SI
  · exact rt_guard hs i.ack (fun s s' => i.ack s' = c s) L.H_ACK_DI
  · exact rt_guard hs o.req (fun s s' => o.req s' = c s) L.H_REQ_DI
  · intro t; exact L.H_LATCH_OPEN _
  · intro t h
    simp only [rtC, rtT] at h ⊢
    rcases hs t with e | e
    · rw [e]
    · rw [e] at h ⊢; exact L.H_LATCH_HOLD _ h
  · show c 1 = false
    exact r1 L.ic (fun h => by rw [L.H_CEL_SI 0 h, hi.1, ho.2, L.ic]; decide)
  · show i.ack 1 = false
    exact r1 L.ii (fun h => (L.H_ACK_DI 0 h).trans L.ic)
  · show o.req 1 = false
    exact r1 L.io (fun h => (L.H_REQ_DI 0 h).trans L.ic)

theorem sink_sh {c : Chan} (S : Gcd.Sink c) (hc : Low0 c) : Gcd.Sink (rtC (shf 1) c) := by
  have hs := shf_mono 1
  refine ⟨?_, ?_⟩
  · exact rt_guard hs c.ack (fun s s' => c.ack s' = c.req s) S.wire
  · show c.ack 1 = false
    exact r1 S.init (fun h => (S.wire 0 h).trans hc.1)

end sh

/-- **Shifting a C-convention run one tick to the left keeps every non-source cell model**,
provided every request and acknowledge is low at tick 0 (reset fields included: the new tick
0 is the old tick 1, and a driven wire can only have moved at step 0 to a function of tick-0
values). Sources are excluded: their `Src.iz` fails exactly when a source request rose at
step 0, which is the point (the rig's release state). -/
theorem cell_sh1 {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} (k : K n)
    (hk : isSrcK k = false) (hc : Cell ch sv k) (hz : ∀ c, Low0 (ch c)) :
    Cell (fun c => rtC (shf 1) (ch c)) sv k := by
  cases k with
  | forkG i os =>
    show Fork.Fork _ (os.map (fun c => rtC (shf 1) (ch c)))
    rw [show os.map (fun c => rtC (shf 1) (ch c)) = (os.map ch).map (rtC (shf 1)) by
      simp [List.map_map]]
    exact fork_sh hc (hz i) (fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hz c)
  | forkH i os l h d hs' =>
    show Fork.Fork _ ((os.map Prod.fst).map (fun c => rtC (shf 1) (ch c)))
    rw [show (os.map Prod.fst).map (fun c => rtC (shf 1) (ch c)) =
      ((os.map Prod.fst).map ch).map (rtC (shf 1)) by simp [List.map_map]]
    exact fork_sh hc (hz i) (fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hz c)
  | join ins o e js jw =>
    show Join.Join _ (ins.map (fun c => rtC (shf 1) (ch c))) _
    rw [show ins.map (fun c => rtC (shf 1) (ch c)) = (ins.map ch).map (rtC (shf 1)) by
      simp [List.map_map]]
    exact join_sh hc (fun i hi => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi; exact hz c) (hz o)
  | bjoin ins o ec ed =>
    show Join.Join _ (ins.map (fun c => rtC (shf 1) (ch c))) _
    rw [show ins.map (fun c => rtC (shf 1) (ch c)) = (ins.map ch).map (rtC (shf 1)) by
      simp [List.map_map]]
    exact join_sh hc (fun i hi => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi; exact hz c) (hz o)
  | steerC j t f => exact steer_sh hc (hz j) (fun b => hz _)
  | steerD j t f fd sw => exact steer_sh hc (hz j) (fun b => hz _)
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := hc
    exact ⟨rtT (shf 1) j0, rtT (shf 1) j1, mux_sh M (hz x) (hz y) (hz z)⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := hc
    exact ⟨fun k => rtT (shf 1) (j k), muxn_sh M (fun k => hz _) (hz z)⟩
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact ⟨rtT (shf 1) g1, rtT (shf 1) g2, amerge_sh M (hz x) (hz y) (hz z)⟩
  | link i o =>
    obtain ⟨c, L⟩ := hc
    exact ⟨rtT (shf 1) c, link_sh L (hz i) (hz o)⟩
  | src z which d => simp [isSrcK] at hk
  | sink i => exact sink_sh hc (hz i)

/-! ## 2. The run -/

def cdR (c : Fin NC) : CD := cdsR.getD c.val ⟨[], [], 0, [], []⟩

/-- The run in C's convention (tick 0 idle, every request low). -/
def chC : Fin NC → Chan := wch cdR

/-- **The run in rig time** (tick 0 = reset release, the source requests already high). -/
def chR : Fin NC → Chan := fun c => rtC (shf 1) (chC c)

/-- env_c (uenv1's output), in_ack (the fork's c3), env_c0 (uenv0's output = out0.ack). -/
def eR : Trace := (chR start).req
def kR : Trace := fun t => bv kLst (t + 1)
def qR : Trace := (chR out0).ack

/-- One step of a signal `x t = bv L (t + 1)` (rig time) is a listed toggle `t + 1`. -/
theorem sh_step {L : List Nat} {Q : Nat → Bool} (h : L.all (fun s => s == 0 || Q s) = true)
    {t : Nat} (hne : bv L (t + 1 + 1) ≠ bv L (t + 1)) : Q (t + 1) = true := by
  have hm : t + 1 ∈ L := mem_of_ne hne
  have := List.all_eq_true.mp h _ hm
  simpa using this

/-! ### H_KER -/

def kerChk (k : K NC) : Bool := isSrcK k || kChk cdR (srcV 12 18) k

theorem ker1 : (ops.take 90).all kerChk = true := by decide +kernel
theorem ker2 : ((ops.drop 90).take 90).all kerChk = true := by decide +kernel
theorem ker3 : (((ops.drop 90).drop 90).take 90).all kerChk = true := by decide +kernel
theorem ker4 : (((ops.drop 90).drop 90).drop 90).all kerChk = true := by decide +kernel

theorem ker_all : ops.all kerChk = true := by
  rw [← List.take_append_drop 90 ops, List.all_append, ker1, ← List.take_append_drop 90 (ops.drop 90),
    List.all_append, ker2, ← List.take_append_drop 90 ((ops.drop 90).drop 90), List.all_append, ker3,
    ker4]; rfl

theorem w_ker : ∀ o : Fin NO, isSrcK (opAt o) = false → Cell chR (srcV 12 18) (opAt o) := by
  intro o hk
  have h := List.all_eq_true.mp ker_all _ (getD_mem (o := o))
  simp only [kerChk, hk, Bool.false_or] at h
  exact cell_sh1 _ hk (kChk_sound (srcV 12 18) (opAt o) h) (fun c => ⟨bv_zero _, bv_zero _⟩)

/-! ### H_BUNDLE -/

theorem cdsR_len : cdsR.length = NC := by decide +kernel

theorem heldR_all : cdsR.all heldChk = true := by decide +kernel

theorem w_held : ∀ c : Fin NC, Held (chR c) := by
  intro c
  apply held_rt (shf_mono 1)
  apply held_of
  apply List.all_eq_true.mp heldR_all
  unfold cdR
  have h : c.val < cdsR.length := by rw [cdsR_len]; exact c.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-! ### The env's read maps (NOT the identity) -/

/-- uenv1 reads `in_ack` 3 ticks late (`β`) and `env_c0` 5 ticks late (`φ1`); uenv0 reads `env_c`
4 ticks late (`φ0`); the fork's c3 reads the `a`, `b`, `start` acknowledges 2, 3, 5 ticks late
(`γ`). (uenv0 also reads `out0.req` through urdly, 7 ticks; that is inside C's `Sink.wire`, which
H_KER checks for `out0`'s sink.) -/
def β : Nat → Nat := fun t => t - 3
def φ1 : Nat → Nat := fun t => t - 5
def φ0 : Nat → Nat := fun t => t - 4
def gz (z : Fin NC) : Nat := if z.val = 0 then 2 else if z.val = 1 then 3 else 5
def γ : Fin NC → Nat → Nat := fun z t => t - gz z

theorem sub_mono (d : Nat) : ∀ t t', t ≤ t' → t - d ≤ t' - d := fun _ _ h => by omega
theorem sub_le' (d : Nat) : ∀ t, t - d ≤ t := fun _ => by omega

/-! ### The env: sources, c3, uenv1, uenv0 -/

/-- Per source operator: its request list is `start`'s (one fork wire `env_c`), its bus is
constant `srcV 12 18 w`, and at every move of `k` (C-time step `s`, rig step `s - 1`) the pin read
`ack (γ z (s - 1))` has `k`'s new value. -/
def srcChkR : K NC → Bool
  | .src z w _ => decide ((cdR z).rq = (cdR start).rq) && decide ((cdR z).dt = []) &&
      decide ((cdR z).d0 = srcV 12 18 w) &&
      kLst.all (fun s => s == 0 || ((chR z).ack (γ z (s - 1)) == kR s))
  | _ => true

theorem src_all : ops.all srcChkR = true := by decide +kernel

theorem src_facts {o : Fin NO} {z : Fin NC} {w d : Nat} (h : opAt o = .src z w d) :
    (cdR z).rq = (cdR start).rq ∧ (cdR z).dt = [] ∧ (cdR z).d0 = srcV 12 18 w ∧
      kLst.all (fun s => s == 0 || ((chR z).ack (γ z (s - 1)) == kR s)) = true := by
  have := List.all_eq_true.mp src_all _ (getD_mem (o := o))
  rw [h] at this
  simp only [srcChkR, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem w_fork_wire : ∀ o z w d, opAt o = .src z w d → ∀ t, (chR z).req t = eR t := by
  intro o z w d h t
  show bv (cdR z).rq (t + 1) = bv (cdR start).rq (t + 1)
  rw [(src_facts h).1]

theorem w_dat : ∀ o z w d, opAt o = .src z w d → ∀ t, (chR z).dat t = srcV 12 18 w := by
  intro o z w d h t
  show nv (cdR z).d0 (cdR z).dt (t + 1) = _
  rw [(src_facts h).2.1, (src_facts h).2.2.1]; rfl

theorem w_rel : eR 0 = true ∧ kR 0 = false := by decide +kernel

theorem w_rel0 : qR 0 = false := by decide +kernel

theorem uenv1_chk : (cdR start).rq.all (fun s => s == 0 || (kR (β (s - 1)) == !eR s)) = true := by
  decide +kernel

theorem w_uenv1_b : ∀ t, eR (t + 1) ≠ eR t → kR (β t) = !eR (t + 1) := by
  intro t hne
  have := sh_step uenv1_chk hne
  rw [Nat.add_sub_cancel] at this
  exact eq_of_beq this

theorem w_c3 : ∀ o z w d, opAt o = .src z w d → ∀ t, kR (t + 1) ≠ kR t →
    (chR z).ack (γ z t) = kR (t + 1) := by
  intro o z w d h t hne
  have := sh_step (src_facts h).2.2.2 hne
  rw [Nat.add_sub_cancel] at this
  exact eq_of_beq this

theorem m1_chk : (cdR start).rq.all (fun s => s == 0 || (qR (φ1 (s - 1)) == eR s)) = true := by
  decide +kernel

theorem w_m1 : ∀ t, eR (t + 1) ≠ eR t → qR (φ1 t) = eR (t + 1) := by
  intro t hne
  have := sh_step m1_chk hne
  rw [Nat.add_sub_cancel] at this
  exact eq_of_beq this

theorem m0_chk : (cdR out0).ak.all (fun s => s == 0 || (eR (φ0 (s - 1)) == !qR s)) = true := by
  decide +kernel

theorem w_m0 : ∀ t, qR (t + 1) ≠ qR t → eR (φ0 t) = !qR (t + 1) := by
  intro t hne
  have := sh_step m0_chk hne
  rw [Nat.add_sub_cancel] at this
  exact eq_of_beq this

/-! ### What the run delivers, and why it is not degenerate -/

/-- out0's first token: offered at rig tick 438 (request rises), latched at 489 (ack falls,
which in the rig needs `e` to have re-risen: lap 2 offered at 452), value 6. -/
theorem w_out0 : OffAt (chR out0) 0 438 ∧ (chR out0).dat 439 = 6 ∧
    TokAt (chR out0) 0 489 ∧ (chR out0).dat 489 = 6 := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

/-- Non-degeneracy, decided on the run (rig ticks):
* the fork's c3 HOLDS: at 50 the `a`, `b` acks are high, `start`'s is low, `k` stays low;
  from 98 to 103 all three acks are high but `k` is still low (its `start` pin reads 5 ticks
  late), `k` rises at 104;
* uenv1 holds `e` high at 104..107 although it is excited (`k = 1`, `q = 0`; it reads `k` 3
  ticks late), `e` falls at 108; it holds `e` low at 300 (`q = 0`, `k = 0`: the hold H_ENV rests
  on) and at 447..452 (`q = 1` already, read 5 ticks late), `e` re-rises at 453;
* uenv0 (behind urdly) holds `q` low at 446 although `out0.req` is high since 439, `q` rises at
  447; it holds `q` low at 300 (`out0.req = 0`, `e = 0`);
* start is offered twice by 489 (reset level + lap 2). -/
theorem w_nondegenerate :
    ((chR ⟨0, by decide⟩).ack 50 = true ∧ (chR ⟨1, by decide⟩).ack 50 = true ∧
      (chR start).ack 50 = false ∧ kR 50 = false ∧ kR 51 = false ∧
      (chR ⟨0, by decide⟩).ack 98 = true ∧ (chR ⟨1, by decide⟩).ack 98 = true ∧
      (chR start).ack 98 = true ∧ kR 103 = false ∧ kR 104 = true) ∧
    (eR 104 = true ∧ kR 104 = true ∧ qR 104 = false ∧ eR 107 = true ∧ eR 108 = false ∧
      eR 300 = false ∧ qR 300 = false ∧ kR 300 = false ∧ eR 301 = false ∧
      qR 447 = true ∧ kR 447 = false ∧ eR 452 = false ∧ eR 453 = true) ∧
    ((chR out0).req 439 = true ∧ qR 446 = false ∧ qR 447 = true ∧
      (chR out0).req 300 = false ∧ qR 301 = false) ∧
    cnt (riseB eR) 489 = 1 ∧ eR 0 = true := by
  decide +kernel

/-! ## 3. Joint non-vacuity of `gcd_rig_first_env` -/

/-- **Joint non-vacuity of `RigSrc.gcd_rig_first_env` with non-identity read maps** (a = 12,
b = 18): one run `ch` with env traces `e k q` and read maps `β φ1 φ0 γ` meets EVERY hypothesis of
the theorem, in the order of its binders; every read map lags (`β t = t - 3`, `φ1 t = t - 5`,
`φ0 t = t - 4`, `γ z t = t - 2, 3, 5`), and out0 offers its first token and latches it,
carrying 6. -/
theorem gcd_rig_first_env_joint :
    ∃ (ch : Fin NC → Chan) (e k q : Trace) (β φ1 φ0 : Nat → Nat) (γ : Fin NC → Nat → Nat),
      (∀ o : Fin NO, isSrcK (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).req t = e t) ∧
      (∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).dat t = srcV 12 18 w) ∧
      (e 0 = true ∧ k 0 = false) ∧ q 0 = false ∧
      (∀ t, (ch out0).ack t = q t) ∧
      (∀ t t', t ≤ t' → β t ≤ β t') ∧ (∀ t, β t ≤ t) ∧
      (∀ z t t', t ≤ t' → γ z t ≤ γ z t') ∧ (∀ z t, γ z t ≤ t) ∧
      (∀ t t', t ≤ t' → φ1 t ≤ φ1 t') ∧ (∀ t, φ1 t ≤ t) ∧
      (∀ t t', t ≤ t' → φ0 t ≤ φ0 t') ∧ (∀ t, φ0 t ≤ t) ∧
      (∀ t, e (t + 1) ≠ e t → k (β t) = !e (t + 1)) ∧
      (∀ o z w d, opAt o = .src z w d → ∀ t, k (t + 1) ≠ k t → (ch z).ack (γ z t) = k (t + 1)) ∧
      (∀ t, e (t + 1) ≠ e t → q (φ1 t) = e (t + 1)) ∧
      (∀ t, q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)) ∧
      -- the maps are not the identity: each lags from tick 5 on
      (∀ t, 5 ≤ t → β t < t ∧ φ1 t < t ∧ φ0 t < t ∧ ∀ z, γ z t < t) ∧
      (OffAt (ch out0) 0 438 ∧ (ch out0).dat 439 = 6 ∧ TokAt (ch out0) 0 489 ∧
        (ch out0).dat 489 = 6) :=
  ⟨chR, eR, kR, qR, β, φ1, φ0, γ, w_ker, w_held, w_fork_wire, w_dat, w_rel, w_rel0,
    fun _ => rfl, sub_mono 3, sub_le' 3, fun z => sub_mono (gz z), fun z => sub_le' (gz z),
    sub_mono 5, sub_le' 5, sub_mono 4, sub_le' 4, w_uenv1_b, w_c3, w_m1, w_m0,
    fun t ht => ⟨by simp only [β]; omega, by simp only [φ1]; omega, by simp only [φ0]; omega,
      fun z => by simp only [γ, gz]; split <;> (try split) <;> omega⟩,
    w_out0⟩

/-- Sanity: `gcd_rig_first_env` applied to the witness gives the run's own values. -/
theorem gcd_rig_witness_consistent :
    (∀ r, OffAt (chR out0) 0 r → (chR out0).dat (r + 1) = 6) ∧
    (∀ e', TokAt (chR out0) 0 e' → (chR out0).dat e' = 6) := by
  have h := RigSrc.gcd_rig_first_env 12 18 (by decide) (by decide) chR eR kR qR β φ1 φ0 γ
    w_ker w_held w_fork_wire w_dat w_rel w_rel0 (fun _ => rfl)
    (sub_mono 3) (sub_le' 3) (fun z => sub_mono (gz z)) (fun z => sub_le' (gz z))
    (sub_mono 5) (sub_le' 5) (sub_mono 4) (sub_le' 4)
    w_uenv1_b w_c3 w_m1 w_m0
  rw [show Nat.gcd 12 18 = 6 by decide] at h
  exact h

end Formal.Cells.RigSrcWitness
