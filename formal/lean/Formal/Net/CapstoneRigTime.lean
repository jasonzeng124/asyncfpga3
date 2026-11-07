import Formal.Net.CapstoneNetDef

/-!
# Probe C-8s2: re-timing a circuit run (freezing, prepending an idle tick, shifting)

Every field of every gate model in `Cell` (Fork, Join, Steer, Mux, MuxN, AMerge, Link, Src,
Sink) and `Held` is one of:
* a guarded step property `x (t+1) ≠ x t → P (t, t+1)`, where `x` is a wire the cell drives
  (an output request, an input acknowledge, or an internal C-element trace);
* an unguarded step property that holds trivially on a stutter step (`H_AMERGE_RTZ`:
  `z.req t = false → z.req (t+1) = true → …`; `H_LATCH_HOLD`: `c (t+1) = false →
  o.dat (t+1) = o.dat t`; `Held`: `… → dat (t+1) = dat t`);
* a pointwise property at one tick (the `dat` fields, `H_ARB_EXCL`, `H_LATCH_OPEN`);
* a reset value at tick 0.
There is no liveness, fairness or look-ahead field. So:

* `rtC φ`: re-timing every wire through a "stutter-or-advance" map `φ` (`φ (t+1) = φ t` or
  `φ t + 1`) with `φ 0 = 0` preserves every cell model (`cell_rt`) and `Held` (`held_rt`,
  which does not need `φ 0 = 0`). Freezing at `T` is `φ t = min t T` (`frz`).
* `pc`: prepending one tick on which every request is low (acknowledges and buses copied from
  tick 0) preserves every cell model except the sources' reset clause `Src.iz`, which it
  establishes: `cell_pc` takes `CellR` (= `Cell` with `Src.iz` dropped) and the source's
  acknowledge being low at tick 0.

Ghost traces (Mux `j0 j1`, MuxN `j`, AMerge `g1 g2`, Link `c`) are re-timed the same way.
-/

namespace Formal.Net.CapNet
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

/-! ## Re-timing -/

def rtC (φ : Nat → Nat) (c : Chan) : Chan :=
  ⟨fun t => c.req (φ t), fun t => c.ack (φ t), fun t => c.dat (φ t)⟩

def rtT (φ : Nat → Nat) (g : Trace) : Trace := fun t => g (φ t)

/-- A stutter-or-advance time map. -/
def StepMono (φ : Nat → Nat) : Prop := ∀ t, φ (t + 1) = φ t ∨ φ (t + 1) = φ t + 1

/-- Freezing at `T`. -/
def frz (T : Nat) : Nat → Nat := fun t => min t T

theorem frz_mono (T : Nat) : StepMono (frz T) := by intro t; simp only [frz]; omega
theorem frz_zero (T : Nat) : frz T 0 = 0 := by simp [frz]

/-- Shifting the origin to `T`. -/
def shf (T : Nat) : Nat → Nat := fun t => t + T

theorem shf_mono (T : Nat) : StepMono (shf T) := by intro t; simp only [shf]; omega

section rt
variable {φ : Nat → Nat} (hs : StepMono φ)
include hs

/-- The generic guarded-step lemma. -/
theorem rt_guard {α : Type} (x : Nat → α) (P : Nat → Nat → Prop)
    (h : ∀ t, x (t + 1) ≠ x t → P t (t + 1)) :
    ∀ t, x (φ (t + 1)) ≠ x (φ t) → P (φ t) (φ (t + 1)) := by
  intro t hne
  rcases hs t with e | e
  · rw [e] at hne; exact absurd rfl hne
  · rw [e] at hne ⊢; exact h _ hne

theorem held_rt {c : Chan} (H : Held c) : Held (rtC φ c) := by
  intro t h1 h2
  simp only [rtC, inTx] at h1 h2 ⊢
  rcases hs t with e | e
  · rw [e]
  · rw [e] at h2 ⊢; exact H _ h1 h2

variable (h0 : φ 0 = 0)
include h0

theorem fork_rt {a : Chan} {os : List Chan} (F : Fork.Fork a os) :
    Fork.Fork (rtC φ a) (os.map (rtC φ)) := by
  refine ⟨by simpa using F.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho
    exact rt_guard hs o.req (fun s s' => o.req s' = a.req s) (F.wire o hm)
  · intro t hne o ho; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho
    exact rt_guard hs a.ack (fun s s' => o.ack s = a.ack s') (fun t h => F.cel t h o hm) t hne
  · intro o ho t; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho; exact F.dat o hm _
  · show a.ack (φ 0) = false; rw [h0]; exact F.initA
  · intro o ho; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho
    show o.req (φ 0) = false; rw [h0]; exact F.initO o hm

theorem join_rt {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : Join.Join g is o) :
    Join.Join g (is.map (rtC φ)) (rtC φ o) := by
  refine ⟨by simpa using J.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hne i hi; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hi
    exact rt_guard hs o.req (fun s s' => i.req s = o.req s') (fun t h => J.cel t h i hm) t hne
  · intro i hi; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hi
    exact rt_guard hs i.ack (fun s s' => i.ack s' = o.ack s) (J.wire i hm)
  · intro t; simp only [List.map_map]; exact J.dat _
  · show o.req (φ 0) = false; rw [h0]; exact J.initO
  · intro i hi; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hi
    show i.ack (φ 0) = false; rw [h0]; exact J.initI i hm

theorem steer_rt {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer.Steer sel f j out) : Steer.Steer sel f (rtC φ j) (fun b => rtC φ (out b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact rt_guard hs (out b).req (fun s s' => (out b).req s' = (j.req s && (sel (j.dat s) == b)))
      (S.lut b)
  · exact rt_guard hs j.ack (fun s s' => j.ack s' = ((out true).ack s || (out false).ack s)) S.orr
  · intro b t; exact S.dat b _
  · show j.ack (φ 0) = false; rw [h0]; exact S.initJ
  · intro b; show (out b).req (φ 0) = false; rw [h0]; exact S.initO b

theorem mux_rt {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}
    (M : Mux.Mux sel x y c z j0 j1) :
    Mux.Mux sel (rtC φ x) (rtC φ y) (rtC φ c) (rtC φ z) (rtT φ j0) (rtT φ j1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rt_guard hs j0 (fun s s' => x.req s = j0 s' ∧ (c.req s && !sel (c.dat s)) = j0 s') M.cj0
  · exact rt_guard hs j1 (fun s s' => y.req s = j1 s' ∧ (c.req s && sel (c.dat s)) = j1 s') M.cj1
  · exact rt_guard hs z.req (fun s s' => z.req s' = (j0 s || j1 s)) M.zr
  · exact rt_guard hs x.ack (fun s s' => j0 s = x.ack s' ∧ z.ack s = x.ack s') M.xa
  · exact rt_guard hs y.ack (fun s s' => j1 s = y.ack s' ∧ z.ack s = y.ack s') M.ya
  · exact rt_guard hs c.ack (fun s s' => c.ack s' = z.ack s) M.ca
  · intro t; exact M.dat _
  · show j0 (φ 0) = false; rw [h0]; exact M.i0
  · show j1 (φ 0) = false; rw [h0]; exact M.i1
  · show z.req (φ 0) = false; rw [h0]; exact M.iz
  · show x.ack (φ 0) = false; rw [h0]; exact M.ix
  · show y.ack (φ 0) = false; rw [h0]; exact M.iy
  · show c.ack (φ 0) = false; rw [h0]; exact M.ic

theorem muxn_rt {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}
    (M : MuxN.MuxN sel xs c z j) :
    MuxN.MuxN sel (fun k => rtC φ (xs k)) (rtC φ c) (rtC φ z) (fun k => rtT φ (j k)) := by
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
  · intro k hk; show j k (φ 0) = false; rw [h0]; exact M.ij k hk
  · show z.req (φ 0) = false; rw [h0]; exact M.iz
  · intro k hk; show (xs k).ack (φ 0) = false; rw [h0]; exact M.ix k hk
  · show c.ack (φ 0) = false; rw [h0]; exact M.ic

theorem amerge_rt {x y z : Chan} {g1 g2 : Trace} (M : CM.AMerge x y z g1 g2) :
    CM.AMerge (rtC φ x) (rtC φ y) (rtC φ z) (rtT φ g1) (rtT φ g2) := by
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
  · show g1 (φ 0) = false; rw [h0]; exact M.i1
  · show g2 (φ 0) = false; rw [h0]; exact M.i2
  · show z.req (φ 0) = false; rw [h0]; exact M.iz
  · show x.ack (φ 0) = false; rw [h0]; exact M.ix
  · show y.ack (φ 0) = false; rw [h0]; exact M.iy

theorem link_rt {i o : Chan} {c : Trace} (L : Link.Link i o c) :
    Link.Link (rtC φ i) (rtC φ o) (rtT φ c) := by
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
  · show c (φ 0) = false; rw [h0]; exact L.ic
  · show i.ack (φ 0) = false; rw [h0]; exact L.ii
  · show o.req (φ 0) = false; rw [h0]; exact L.io

theorem src_rt {z : Chan} {v : Nat} (S : Capstone.Src z v) : Capstone.Src (rtC φ z) v := by
  refine ⟨?_, ?_, ?_⟩
  · exact rt_guard hs z.req (fun s s' => z.req s' = !z.ack s) S.H_LUT_SI
  · intro t; exact S.dat _
  · show z.req (φ 0) = false; rw [h0]; exact S.iz

theorem sink_rt {c : Chan} (S : Gcd.Sink c) : Gcd.Sink (rtC φ c) := by
  refine ⟨?_, ?_⟩
  · exact rt_guard hs c.ack (fun s s' => c.ack s' = c.req s) S.wire
  · show c.ack (φ 0) = false; rw [h0]; exact S.init

/-- **Every cell model is preserved by re-timing** through a stutter-or-advance map. -/
theorem cell_rt {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} (k : K n) (hc : Cell ch sv k) :
    Cell (fun c => rtC φ (ch c)) sv k := by
  cases k with
  | forkG i os =>
    show Fork.Fork _ (os.map (fun c => rtC φ (ch c)))
    rw [show os.map (fun c => rtC φ (ch c)) = (os.map ch).map (rtC φ) by simp [List.map_map]]
    exact fork_rt hs h0 hc
  | forkH i os l h d hs' =>
    show Fork.Fork _ ((os.map Prod.fst).map (fun c => rtC φ (ch c)))
    rw [show (os.map Prod.fst).map (fun c => rtC φ (ch c)) =
      ((os.map Prod.fst).map ch).map (rtC φ) by simp [List.map_map]]
    exact fork_rt hs h0 hc
  | join ins o e js jw =>
    show Join.Join _ (ins.map (fun c => rtC φ (ch c))) _
    rw [show ins.map (fun c => rtC φ (ch c)) = (ins.map ch).map (rtC φ) by simp [List.map_map]]
    exact join_rt hs h0 hc
  | bjoin ins o ec ed =>
    show Join.Join _ (ins.map (fun c => rtC φ (ch c))) _
    rw [show ins.map (fun c => rtC φ (ch c)) = (ins.map ch).map (rtC φ) by simp [List.map_map]]
    exact join_rt hs h0 hc
  | steerC j t f => exact steer_rt hs h0 hc
  | steerD j t f fd sw => exact steer_rt hs h0 hc
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := hc
    exact ⟨rtT φ j0, rtT φ j1, mux_rt hs h0 M⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := hc
    refine ⟨fun k => rtT φ (j k), ?_⟩
    have := muxn_rt hs h0 M
    exact this
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact ⟨rtT φ g1, rtT φ g2, amerge_rt hs h0 M⟩
  | link i o =>
    obtain ⟨c, L⟩ := hc
    exact ⟨rtT φ c, link_rt hs h0 L⟩
  | src z which d => exact src_rt hs h0 hc
  | sink i => exact sink_rt hs h0 hc

end rt

/-! ## Prepending an idle tick -/

/-- Delay a trace by one tick, repeating tick 0. -/
def pd {α : Type} (x : Nat → α) : Nat → α
  | 0 => x 0
  | t + 1 => x t

/-- Prepend one tick to a channel: request low, acknowledge and bus as at tick 0. -/
def pc (c : Chan) : Chan :=
  ⟨fun t => match t with | 0 => false | t + 1 => c.req t, pd c.ack, pd c.dat⟩

@[simp] theorem pd_zero {α : Type} (x : Nat → α) : pd x 0 = x 0 := rfl
@[simp] theorem pd_succ {α : Type} (x : Nat → α) (t : Nat) : pd x (t + 1) = x t := rfl
@[simp] theorem pc_req0 (c : Chan) : (pc c).req 0 = false := rfl
@[simp] theorem pc_reqS (c : Chan) (t : Nat) : (pc c).req (t + 1) = c.req t := rfl
@[simp] theorem pc_ack (c : Chan) (t : Nat) : (pc c).ack t = pd c.ack t := rfl
@[simp] theorem pc_dat (c : Chan) (t : Nat) : (pc c).dat t = pd c.dat t := rfl

theorem held_pc {c : Chan} (H : Held c) : Held (pc c) := by
  intro t h1 h2
  cases t with
  | zero => rfl
  | succ t =>
    simp only [inTx, pc_reqS, pc_ack, pd_succ] at h1 h2
    exact H t h1 h2

/-- Tactic-free helper for a guarded field on a prepended request whose tick-0 value is low. -/
theorem req_pc_guard {c : Chan} (h0 : c.req 0 = false) {Q : Nat → Prop}
    (h : ∀ t, c.req (t + 1) ≠ c.req t → Q (t + 1)) :
    ∀ t, (pc c).req (t + 1) ≠ (pc c).req t → Q t := by
  intro t hne
  cases t with
  | zero => simp [h0] at hne
  | succ t => exact h t hne

theorem pd_guard' {α : Type} (x : Nat → α) {Q : Nat → Prop}
    (h : ∀ t, x (t + 1) ≠ x t → Q (t + 1)) :
    ∀ t, pd x (t + 1) ≠ pd x t → Q t := by
  intro t hne
  cases t with
  | zero => exact absurd rfl hne
  | succ t => exact h t hne

theorem fork_pc {a : Chan} {os : List Chan} (F : Fork.Fork a os) :
    Fork.Fork (pc a) (os.map pc) := by
  refine ⟨by simpa using F.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho
    exact req_pc_guard (F.initO o hm) (fun t h => F.wire o hm t h)
  · intro t hne o ho; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho
    exact pd_guard' a.ack (Q := fun t => (pc o).ack t = (pc a).ack (t + 1))
      (fun t h => F.cel t h o hm) t hne
  · intro o ho t; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho
    cases t <;> exact F.dat o hm _
  · exact F.initA
  · intro o ho; obtain ⟨o, hm, rfl⟩ := List.mem_map.1 ho; rfl

theorem join_pc {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : Join.Join g is o) :
    Join.Join g (is.map pc) (pc o) := by
  refine ⟨by simpa using J.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hne i hi; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hi
    exact req_pc_guard J.initO (Q := fun t => (pc i).req t = (pc o).req (t + 1))
      (fun t h => J.cel t h i hm) t hne
  · intro i hi; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hi
    exact pd_guard' i.ack (Q := fun t => (pc i).ack (t + 1) = (pc o).ack t) (J.wire i hm)
  · intro t; simp only [List.map_map]
    cases t
    · exact J.dat 0
    · exact J.dat _
  · rfl
  · intro i hi; obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hi; exact J.initI i hm

theorem steer_pc {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer.Steer sel f j out) : Steer.Steer sel f (pc j) (fun b => pc (out b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact req_pc_guard (S.initO b)
      (Q := fun t => (pc (out b)).req (t + 1) = ((pc j).req t && (sel ((pc j).dat t) == b)))
      (S.lut b)
  · exact pd_guard' j.ack
      (Q := fun t => (pc j).ack (t + 1) = ((pc (out true)).ack t || (pc (out false)).ack t)) S.orr
  · intro b t; cases t <;> exact S.dat b _
  · exact S.initJ
  · intro b; rfl

theorem mux_pc {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}
    (M : Mux.Mux sel x y c z j0 j1) :
    Mux.Mux sel (pc x) (pc y) (pc c) (pc z) (pd j0) (pd j1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pd_guard' j0
      (Q := fun t => (pc x).req t = pd j0 (t + 1) ∧
        ((pc c).req t && !sel ((pc c).dat t)) = pd j0 (t + 1)) M.cj0
  · exact pd_guard' j1
      (Q := fun t => (pc y).req t = pd j1 (t + 1) ∧
        ((pc c).req t && sel ((pc c).dat t)) = pd j1 (t + 1)) M.cj1
  · exact req_pc_guard M.iz (Q := fun t => (pc z).req (t + 1) = (pd j0 t || pd j1 t)) M.zr
  · exact pd_guard' x.ack
      (Q := fun t => pd j0 t = (pc x).ack (t + 1) ∧ (pc z).ack t = (pc x).ack (t + 1)) M.xa
  · exact pd_guard' y.ack
      (Q := fun t => pd j1 t = (pc y).ack (t + 1) ∧ (pc z).ack t = (pc y).ack (t + 1)) M.ya
  · exact pd_guard' c.ack (Q := fun t => (pc c).ack (t + 1) = (pc z).ack t) M.ca
  · intro t; cases t <;> exact M.dat _
  · exact M.i0
  · exact M.i1
  · rfl
  · exact M.ix
  · exact M.iy
  · exact M.ic

theorem muxn_pc {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}
    (M : MuxN.MuxN sel xs c z j) :
    MuxN.MuxN sel (fun k => pc (xs k)) (pc c) (pc z) (fun k => pd (j k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact pd_guard' (j k)
      (Q := fun t => (pc (xs k)).req t = pd (j k) (t + 1) ∧
        ((pc c).req t && (sel ((pc c).dat t) == k)) = pd (j k) (t + 1)) (M.cj k hk)
  · exact req_pc_guard M.iz
      (Q := fun t => (pc z).req (t + 1) = (pd (j 0) t || pd (j 1) t || pd (j 2) t)) M.zr
  · intro k hk
    exact pd_guard' (xs k).ack
      (Q := fun t => pd (j k) t = (pc (xs k)).ack (t + 1) ∧ (pc z).ack t = (pc (xs k)).ack (t + 1))
      (M.xa k hk)
  · exact pd_guard' c.ack (Q := fun t => (pc c).ack (t + 1) = (pc z).ack t) M.ca
  · intro t; cases t <;> exact M.dat _
  · intro k hk; exact M.ij k hk
  · rfl
  · intro k hk; exact M.ix k hk
  · exact M.ic

theorem amerge_pc {x y z : Chan} {g1 g2 : Trace} (M : CM.AMerge x y z g1 g2) :
    CM.AMerge (pc x) (pc y) (pc z) (pd g1) (pd g2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pd_guard' g1
      (Q := fun t => pd g1 (t + 1) = (pc x).req t ∧
        (pd g1 (t + 1) = true → pd g2 t = false ∧ (pc z).ack t = false)) M.H_ARB1
  · exact pd_guard' g2
      (Q := fun t => pd g2 (t + 1) = (pc y).req t ∧
        (pd g2 (t + 1) = true → pd g1 t = false ∧ (pc z).ack t = false)) M.H_ARB2
  · intro t; cases t <;> exact M.H_ARB_EXCL _
  · exact req_pc_guard M.iz (Q := fun t => (pc z).req (t + 1) = (pd g1 t || pd g2 t)) M.zr
  · intro t h1 h2
    cases t with
    | zero => simp [M.iz] at h2
    | succ t => exact M.H_AMERGE_RTZ t h1 h2
  · exact pd_guard' x.ack
      (Q := fun t => pd g1 t = (pc x).ack (t + 1) ∧ (pc z).ack t = (pc x).ack (t + 1)) M.xa
  · exact pd_guard' y.ack
      (Q := fun t => pd g2 t = (pc y).ack (t + 1) ∧ (pc z).ack t = (pc y).ack (t + 1)) M.ya
  · intro t; cases t <;> exact M.dat _
  · exact M.i1
  · exact M.i2
  · rfl
  · exact M.ix
  · exact M.iy

theorem link_pc {i o : Chan} {c : Trace} (L : Link.Link i o c) :
    Link.Link (pc i) (pc o) (pd c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pd_guard' c
      (Q := fun t => pd c (t + 1) =
        Formal.Cells.LinkHandshake.ctlB ((pc i).req t) ((pc o).ack t) (pd c t) false) L.H_CEL_SI
  · exact pd_guard' i.ack (Q := fun t => (pc i).ack (t + 1) = pd c t) L.H_ACK_DI
  · exact req_pc_guard L.io (Q := fun t => (pc o).req (t + 1) = pd c t) L.H_REQ_DI
  · intro t h; cases t <;> exact L.H_LATCH_OPEN _ h
  · intro t h
    cases t with
    | zero => rfl
    | succ t => exact L.H_LATCH_HOLD t h
  · exact L.ic
  · exact L.ii
  · rfl

/-- The source model without its reset clause `iz`. -/
structure SrcR (z : Chan) (v : Nat) : Prop where
  H_LUT_SI : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = !z.ack t
  dat : ∀ t, z.dat t = v

theorem src_pc {z : Chan} {v : Nat} (S : SrcR z v) (ha : z.ack 0 = false) :
    Capstone.Src (pc z) v := by
  refine ⟨?_, ?_, rfl⟩
  · intro t hne
    cases t with
    | zero =>
      show z.req 0 = !pd z.ack 0
      simp only [pd_zero, ha, Bool.not_false]
      cases h : z.req 0
      · simp [h] at hne
      · rfl
    | succ t => exact S.H_LUT_SI t hne
  · intro t; cases t <;> exact S.dat _

theorem sink_pc {c : Chan} (S : Gcd.Sink c) : Gcd.Sink (pc c) := by
  refine ⟨?_, S.init⟩
  exact pd_guard' c.ack (Q := fun t => (pc c).ack (t + 1) = (pc c).req t) S.wire

/-- `Cell` with the sources' reset clause `Src.iz` dropped: the hypothesis for a run whose
tick 0 is the first tick after reset release of a rig that holds the source requests HIGH
through reset (gcd_rig's `uenv1` is a `bd_c2n_set`). -/
def CellR {n : Nat} (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .src z which _ => SrcR (ch z) (sv which)
  | k => Cell ch sv k

theorem cellR_of {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} (k : K n) (h : Cell ch sv k) :
    CellR ch sv k := by
  cases k with
  | src z which d => exact ⟨h.H_LUT_SI, h.dat⟩
  | _ => exact h

/-- **Prepending an idle tick turns `CellR` into `Cell`** (given that a source's acknowledge
is low at tick 0; for a non-source cell nothing is needed). -/
theorem cell_pc {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} (k : K n) (hc : CellR ch sv k)
    (hsa : ∀ z which d, k = .src z which d → (ch z).ack 0 = false) :
    Cell (fun c => pc (ch c)) sv k := by
  cases k with
  | forkG i os =>
    show Fork.Fork _ (os.map (fun c => pc (ch c)))
    rw [show os.map (fun c => pc (ch c)) = (os.map ch).map pc by simp [List.map_map]]
    exact fork_pc hc
  | forkH i os l h d hs' =>
    show Fork.Fork _ ((os.map Prod.fst).map (fun c => pc (ch c)))
    rw [show (os.map Prod.fst).map (fun c => pc (ch c)) =
      ((os.map Prod.fst).map ch).map pc by simp [List.map_map]]
    exact fork_pc hc
  | join ins o e js jw =>
    show Join.Join _ (ins.map (fun c => pc (ch c))) _
    rw [show ins.map (fun c => pc (ch c)) = (ins.map ch).map pc by simp [List.map_map]]
    exact join_pc hc
  | bjoin ins o ec ed =>
    show Join.Join _ (ins.map (fun c => pc (ch c))) _
    rw [show ins.map (fun c => pc (ch c)) = (ins.map ch).map pc by simp [List.map_map]]
    exact join_pc hc
  | steerC j t f => exact steer_pc hc
  | steerD j t f fd sw => exact steer_pc hc
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := hc
    exact ⟨pd j0, pd j1, mux_pc M⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := hc
    exact ⟨fun k => pd (j k), muxn_pc M⟩
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact ⟨pd g1, pd g2, amerge_pc M⟩
  | link i o =>
    obtain ⟨c, L⟩ := hc
    exact ⟨pd c, link_pc L⟩
  | src z which d => exact src_pc hc (hsa z which d rfl)
  | sink i => exact sink_pc hc

end Formal.Net.CapNet
