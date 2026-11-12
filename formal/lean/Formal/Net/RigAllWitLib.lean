import Formal.Net.CapstoneWitnessLib
import Formal.Net.CapstoneRigAll

/-!
# Probe C-wit: event-list runs whose requests may start HIGH, and a checker for `CellR`

C-8t's `CapstoneWitnessLib` represents every binary signal by its toggle list, low at tick 0.
gcd_rig holds the source requests HIGH through reset (`uenv1` is a `bd_c2n_set`), and
`gcd_rig_all` assumes `CellR` (H_CELLS without `Src.iz`) for that reason. This module is a
copy of C-8t's channel layer with one change: a channel record `CDR` carries the initial level
`r0` of its request (`rb x t` = `r0` xor the toggle parity). Everything else (acknowledges,
buses, internal traces) is as in C-8t.

`kChkR cd sv k` checks `CellR (wchR cd) sv k`: the per-kind checkers of C-8t, plus "every
output request of a non-source operator starts low" (the reset field of those models); a
source's request may start high (`SrcR` has no reset field). `kChkR_sound` proves it sound.
-/

namespace Formal.Net.CapNet.RigWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw
open Formal.Net.CapNet.Wit

/-! ## Channels -/

structure CD where
  r0 : Bool
  rq : List Nat
  ak : List Nat
  d0 : Nat
  dt : List (Nat × Nat)
  ax : List (List Nat)
  deriving Repr

/-- The request: initial level `r0`, toggling at the steps of `rq`. -/
def rb (x : CD) (t : Nat) : Bool := bif x.r0 then !bv x.rq t else bv x.rq t

theorem rb_ne {x : CD} {t : Nat} (h : rb x (t + 1) ≠ rb x t) : bv x.rq (t + 1) ≠ bv x.rq t := by
  intro e; apply h; simp only [rb, e]

theorem rb_zero {x : CD} (h : x.r0 = false) : rb x 0 = false := by
  simp [rb, h, bv_zero]

theorem step_ofR {x : CD} {P : Nat → Bool} (h : x.rq.all P = true) {t : Nat}
    (hne : rb x (t + 1) ≠ rb x t) : P t = true := step_of h (rb_ne hne)

def CD.ch (x : CD) : Chan := ⟨rb x, bv x.ak, nv x.d0 x.dt⟩
def CD.dts (x : CD) : List Nat := x.dt.map Prod.fst
def CD.aux (x : CD) (k : Nat) : List Nat := x.ax.getD k []

variable {n : Nat} (cd : Fin n → CD)

def wch (c : Fin n) : Chan := (cd c).ch

/-- `Held` checker. -/
def heldChk (x : CD) : Bool :=
  x.dt.all fun p => !((rb x p.1 || bv x.ak p.1) && (rb x (p.1 + 1) || bv x.ak (p.1 + 1))) ||
    nv x.d0 x.dt (p.1 + 1) == nv x.d0 x.dt p.1

theorem held_of {x : CD} (h : heldChk x = true) : Held x.ch := by
  intro t h1 h2
  show nv x.d0 x.dt (t + 1) = nv x.d0 x.dt t
  by_cases ht : t ∈ x.dts
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    have := List.all_eq_true.mp h p hp
    simp only [inTx, CD.ch] at h1 h2
    simp [h1, h2] at this
    exact this
  · exact nv_st ht

/-! ## Per-kind checkers -/

abbrev rqv (c : Fin n) (t : Nat) : Bool := rb (cd c) t
abbrev akv (c : Fin n) (t : Nat) : Bool := bv (cd c).ak t
abbrev dv (c : Fin n) (t : Nat) : Nat := nv (cd c).d0 (cd c).dt t
abbrev xv (c : Fin n) (k t : Nat) : Bool := bv ((cd c).aux k) t

def forkChk (i : Fin n) (os : List (Fin n)) : Bool :=
  !os.isEmpty &&
  os.all (fun c => (cd c).rq.all fun e => rqv cd c (e + 1) == rqv cd i e) &&
  (cd i).ak.all (fun e => os.all fun c => akv cd c e == akv cd i (e + 1)) &&
  os.all (fun c => pwChk ((cd c).dts ++ (cd i).dts) fun t => dv cd c t == dv cd i t)

def joinChk (g : List Nat → Nat) (ins : List (Fin n)) (o : Fin n) : Bool :=
  !ins.isEmpty &&
  (cd o).rq.all (fun e => ins.all fun i => rqv cd i e == rqv cd o (e + 1)) &&
  ins.all (fun i => (cd i).ak.all fun e => akv cd i (e + 1) == akv cd o e) &&
  pwChk ((cd o).dts ++ ins.flatMap (fun i => (cd i).dts)) (fun t => dv cd o t == g (ins.map fun i => dv cd i t))

def steerChk (f : Nat → Nat) (j tc fc : Fin n) : Bool :=
  (cd tc).rq.all (fun e => rqv cd tc (e + 1) == (rqv cd j e && (sel2 (dv cd j e) == true))) &&
  (cd fc).rq.all (fun e => rqv cd fc (e + 1) == (rqv cd j e && (sel2 (dv cd j e) == false))) &&
  (cd j).ak.all (fun e => akv cd j (e + 1) == (akv cd tc e || akv cd fc e)) &&
  pwChk ((cd tc).dts ++ (cd j).dts) (fun t => dv cd tc t == f (dv cd j t)) &&
  pwChk ((cd fc).dts ++ (cd j).dts) (fun t => dv cd fc t == f (dv cd j t))

def muxChk (c x y z : Fin n) : Bool :=
  ((cd z).aux 0).all (fun e => rqv cd x e == xv cd z 0 (e + 1) &&
      (rqv cd c e && !sel2 (dv cd c e)) == xv cd z 0 (e + 1)) &&
  ((cd z).aux 1).all (fun e => rqv cd y e == xv cd z 1 (e + 1) &&
      (rqv cd c e && sel2 (dv cd c e)) == xv cd z 1 (e + 1)) &&
  (cd z).rq.all (fun e => rqv cd z (e + 1) == (xv cd z 0 e || xv cd z 1 e)) &&
  (cd x).ak.all (fun e => xv cd z 0 e == akv cd x (e + 1) && akv cd z e == akv cd x (e + 1)) &&
  (cd y).ak.all (fun e => xv cd z 1 e == akv cd y (e + 1) && akv cd z e == akv cd y (e + 1)) &&
  (cd c).ak.all (fun e => akv cd c (e + 1) == akv cd z e) &&
  pwChk ((cd z).dts ++ (cd c).dts ++ (cd x).dts ++ (cd y).dts)
    (fun t => dv cd z t == if sel2 (dv cd c t) then dv cd y t else dv cd x t)

def muxnChk (c x0 x1 x2 z : Fin n) : Bool :=
  [0, 1, 2].all (fun k => ((cd z).aux k).all fun e => rqv cd (cx3 x0 x1 x2 k) e == xv cd z k (e + 1) &&
      (rqv cd c e && (selD (dv cd c e) == k)) == xv cd z k (e + 1)) &&
  (cd z).rq.all (fun e => rqv cd z (e + 1) == (xv cd z 0 e || xv cd z 1 e || xv cd z 2 e)) &&
  [0, 1, 2].all (fun k => (cd (cx3 x0 x1 x2 k)).ak.all fun e =>
      xv cd z k e == akv cd (cx3 x0 x1 x2 k) (e + 1) && akv cd z e == akv cd (cx3 x0 x1 x2 k) (e + 1)) &&
  (cd c).ak.all (fun e => akv cd c (e + 1) == akv cd z e) &&
  pwChk ((cd z).dts ++ (cd c).dts ++ (cd x0).dts ++ (cd x1).dts ++ (cd x2).dts)
    (fun t => !decide (selD (dv cd c t) < 3) || dv cd z t == dv cd (cx3 x0 x1 x2 (selD (dv cd c t))) t)

def amChk (x y z : Fin n) : Bool :=
  ((cd z).aux 0).all (fun e => xv cd z 0 (e + 1) == rqv cd x e &&
      (!xv cd z 0 (e + 1) || (!xv cd z 1 e && !akv cd z e))) &&
  ((cd z).aux 1).all (fun e => xv cd z 1 (e + 1) == rqv cd y e &&
      (!xv cd z 1 (e + 1) || (!xv cd z 0 e && !akv cd z e))) &&
  pwChk ((cd z).aux 0 ++ (cd z).aux 1) (fun t => !(xv cd z 0 t && xv cd z 1 t)) &&
  (cd z).rq.all (fun e => rqv cd z (e + 1) == (xv cd z 0 e || xv cd z 1 e)) &&
  (cd z).rq.all (fun e => !(!rqv cd z e && rqv cd z (e + 1)) || (!akv cd x e && !akv cd y e)) &&
  (cd x).ak.all (fun e => xv cd z 0 e == akv cd x (e + 1) && akv cd z e == akv cd x (e + 1)) &&
  (cd y).ak.all (fun e => xv cd z 1 e == akv cd y (e + 1) && akv cd z e == akv cd y (e + 1)) &&
  pwChk ((cd z).dts ++ (cd z).aux 1 ++ (cd y).ak ++ (cd y).dts ++ (cd x).dts)
    (fun t => dv cd z t == 2 * (if (xv cd z 1 t || akv cd y t) then dv cd y t else dv cd x t) +
      Mux.b2n (xv cd z 1 t || akv cd y t))

def linkChk (i o : Fin n) : Bool :=
  ((cd o).aux 0).all (fun e => xv cd o 0 (e + 1) ==
      Formal.Cells.LinkHandshake.ctlB (rqv cd i e) (akv cd o e) (xv cd o 0 e) false) &&
  (cd i).ak.all (fun e => akv cd i (e + 1) == xv cd o 0 e) &&
  (cd o).rq.all (fun e => rqv cd o (e + 1) == xv cd o 0 e) &&
  pwChk ((cd o).aux 0 ++ (cd o).dts ++ (cd i).dts) (fun t => !xv cd o 0 t || dv cd o t == dv cd i t) &&
  (cd o).dts.all (fun e => xv cd o 0 (e + 1) || dv cd o (e + 1) == dv cd o e)

def srcChk (z : Fin n) (v : Nat) : Bool :=
  (cd z).rq.all (fun e => rqv cd z (e + 1) == !akv cd z e) &&
  pwChk (cd z).dts (fun t => dv cd z t == v)

def sinkChk (i : Fin n) : Bool :=
  (cd i).ak.all (fun e => akv cd i (e + 1) == rqv cd i e)

def kChk (sv : Nat → Nat) : K n → Bool
  | .forkG i os => forkChk cd i os
  | .forkH i os _ _ _ _ => forkChk cd i (os.map Prod.fst)
  | .join ins o e js _ => joinChk cd (jg e js) ins o
  | .bjoin ins o ec ed => joinChk cd (bg ec ed) ins o
  | .steerC j t f => steerChk cd (fun _ => 0) j t f
  | .steerD j t f fd _ => steerChk cd (fun v => fd.eval [v / 2]) j t f
  | .mux c x y z _ => muxChk cd c x y z
  | .muxn c x0 x1 x2 z _ => muxnChk cd c x0 x1 x2 z
  | .amerge x y z _ => amChk cd x y z
  | .link i o => linkChk cd i o
  | .src z which _ => srcChk cd z (sv which)
  | .sink i => sinkChk cd i

/-- Every output request of a non-source operator starts low. -/
def r0Chk (k : K n) : Bool := match k with
  | .src _ _ _ => true
  | k => k.outsC.all fun c => !(cd c).r0

def kChkR (sv : Nat → Nat) (k : K n) : Bool := r0Chk cd k && kChk cd sv k

/-! ## Soundness -/

variable {cd}

theorem nm {L L' : List Nat} {t : Nat} (h : t ∉ L ++ L') : t ∉ L ∧ t ∉ L' := by
  simp only [List.mem_append, not_or] at h; exact h

theorem fork_sound {i : Fin n} {os : List (Fin n)} (h : forkChk cd i os = true)
    (hr : ∀ c ∈ os, (cd c).r0 = false) :
    Fork.Fork (wch cd i) (os.map (wch cd)) := by
  simp only [forkChk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨hne, hw⟩, hc⟩, hd⟩ := h
  refine ⟨by simpa using hne, ?_, ?_, ?_, bv_zero _, ?_⟩
  · intro o ho t hmv
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ho
    have := step_ofR (List.all_eq_true.mp hw c hc') hmv
    simpa [wch, CD.ch] using this
  · intro t hmv o ho
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ho
    have := List.all_eq_true.mp (step_of hc hmv) c hc'
    simpa [wch, CD.ch] using this
  · intro o ho t
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ho
    have := pw_of (List.all_eq_true.mp hd c hc') (fun t ht => by
      obtain ⟨h1, h2⟩ := nm ht; simp only [nv_st h1, nv_st h2]) t
    simpa [wch, CD.ch] using this
  · intro o ho
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ho
    exact rb_zero (hr c hc')

theorem map_dv_st {ins : List (Fin n)} {t : Nat} (h : t ∉ ins.flatMap (fun i => (cd i).dts)) :
    ins.map (fun i => dv cd i (t + 1)) = ins.map (fun i => dv cd i t) := by
  apply List.map_congr_left
  intro i hi
  exact nv_st (fun h' => h (List.mem_flatMap.2 ⟨i, hi, h'⟩))

theorem join_sound {g : List Nat → Nat} {ins : List (Fin n)} {o : Fin n} (h : joinChk cd g ins o = true)
    (hr : (cd o).r0 = false) :
    Join.Join g (ins.map (wch cd)) (wch cd o) := by
  simp only [joinChk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨hne, hc⟩, hw⟩, hd⟩ := h
  refine ⟨by simpa using hne, ?_, ?_, ?_, rb_zero hr, ?_⟩
  · intro t hmv i hi
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hi
    have := List.all_eq_true.mp (step_ofR hc hmv) c hc'
    simpa [wch, CD.ch] using this
  · intro i hi t hmv
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hi
    have := step_of (List.all_eq_true.mp hw c hc') hmv
    simpa [wch, CD.ch] using this
  · intro t
    have := pw_of hd (fun t ht => by
      obtain ⟨h1, h2⟩ := nm ht; simp only [nv_st h1, map_dv_st h2]) t
    simp only [beq_iff_eq] at this
    simp only [wch, CD.ch, List.map_map, Function.comp_def]
    exact this
  · intro i hi
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi
    exact bv_zero _

theorem steer_sound {f : Nat → Nat} {j tc fc : Fin n} (h : steerChk cd f j tc fc = true)
    (hrt : (cd tc).r0 = false) (hrf : (cd fc).r0 = false) :
    Steer.Steer sel2 f (wch cd j) (fun b => wch cd (bif b then tc else fc)) := by
  simp only [steerChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ht, hf⟩, ho⟩, hdt⟩, hdf⟩ := h
  refine ⟨?_, ?_, ?_, bv_zero _, fun b => by cases b <;> first | exact rb_zero hrf | exact rb_zero hrt⟩
  · intro b t hmv
    cases b
    · have := step_ofR hf hmv; simpa [wch, CD.ch] using this
    · have := step_ofR ht hmv; simpa [wch, CD.ch] using this
  · intro t hmv
    have := step_of ho hmv; simpa [wch, CD.ch] using this
  · intro b t
    cases b
    · have := pw_of hdf (fun t ht => by
        obtain ⟨h1, h2⟩ := nm ht; simp only [nv_st h1, nv_st h2]) t
      simpa [wch, CD.ch] using this
    · have := pw_of hdt (fun t ht => by
        obtain ⟨h1, h2⟩ := nm ht; simp only [nv_st h1, nv_st h2]) t
      simpa [wch, CD.ch] using this

theorem mux_sound {c x y z : Fin n} (h : muxChk cd c x y z = true) (hr : (cd z).r0 = false) :
    Mux.Mux sel2 (wch cd x) (wch cd y) (wch cd c) (wch cd z) (bv ((cd z).aux 0)) (bv ((cd z).aux 1)) := by
  simp only [muxChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, hz⟩, hx⟩, hy⟩, hc⟩, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, bv_zero _, bv_zero _, rb_zero hr, bv_zero _, bv_zero _, bv_zero _⟩
  · intro t hmv; have := step_of h0 hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of h1 hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_ofR hz hmv; simpa [wch, CD.ch] using this
  · intro t hmv; have := step_of hx hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of hy hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of hc hmv; simpa [wch, CD.ch] using this
  · intro t
    have := pw_of hd (fun t ht => by
      obtain ⟨h1, h2⟩ := nm ht; obtain ⟨h1, h3⟩ := nm h1; obtain ⟨h1, h4⟩ := nm h1
      simp only [nv_st h1, nv_st h2, nv_st h3, nv_st h4]) t
    simp only [beq_iff_eq] at this
    exact this

theorem cx3_cases (x0 x1 x2 : Fin n) (k : Nat) : cx3 x0 x1 x2 k = x0 ∨ cx3 x0 x1 x2 k = x1 ∨ cx3 x0 x1 x2 k = x2 := by
  rcases k with _ | _ | k <;> simp [cx3]

theorem muxn_sound {c x0 x1 x2 z : Fin n} (h : muxnChk cd c x0 x1 x2 z = true) (hr : (cd z).r0 = false) :
    MuxN.MuxN selD (fun k => wch cd (cx3 x0 x1 x2 k)) (wch cd c) (wch cd z) (fun k => bv ((cd z).aux k)) := by
  simp only [muxnChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hj, hz⟩, hx⟩, hc⟩, hd⟩ := h
  have hj' : ∀ k, k < 3 → ((cd z).aux k).all (fun e => rqv cd (cx3 x0 x1 x2 k) e == xv cd z k (e + 1) &&
      (rqv cd c e && (selD (dv cd c e) == k)) == xv cd z k (e + 1)) = true := by
    intro k hk
    have := List.all_eq_true.mp hj k
    rcases k with _ | _ | _ | k
    · exact this (by simp)
    · exact this (by simp)
    · exact this (by simp)
    · omega
  have hx' : ∀ k, k < 3 → (cd (cx3 x0 x1 x2 k)).ak.all (fun e =>
      xv cd z k e == akv cd (cx3 x0 x1 x2 k) (e + 1) && akv cd z e == akv cd (cx3 x0 x1 x2 k) (e + 1)) = true := by
    intro k hk
    have := List.all_eq_true.mp hx k
    rcases k with _ | _ | _ | k
    · exact this (by simp)
    · exact this (by simp)
    · exact this (by simp)
    · omega
  refine ⟨?_, ?_, ?_, ?_, ?_, fun k _ => bv_zero _, rb_zero hr, fun k _ => bv_zero _, bv_zero _⟩
  · intro k hk t hmv; have := step_of (hj' k hk) hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_ofR hz hmv; simpa [wch, CD.ch] using this
  · intro k hk t hmv; have := step_of (hx' k hk) hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of hc hmv; simpa [wch, CD.ch] using this
  · intro t hs
    have := pw_of hd (fun t ht => by
      obtain ⟨h1, h5⟩ := nm ht; obtain ⟨h1, h4⟩ := nm h1; obtain ⟨h1, h3⟩ := nm h1
      obtain ⟨h1, h2⟩ := nm h1
      have e := cx3_cases x0 x1 x2 (selD (dv cd c t))
      simp only [nv_st h1, nv_st h2]
      rcases e with e | e | e <;> rw [e] <;> simp only [nv_st h3, nv_st h4, nv_st h5]) t
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at this
    rcases this with h' | h'
    · exact absurd hs h'
    · exact h'

theorem arb_bool : ∀ g' xr g2 za : Bool, (g' == xr && (!g' || (!g2 && !za))) = true →
    g' = xr ∧ (g' = true → g2 = false ∧ za = false) := by decide

theorem excl_bool : ∀ a b : Bool, (!(a && b)) = true → (a && b) = false := by decide

theorem am_sound {x y z : Fin n} (h : amChk cd x y z = true) (hr : (cd z).r0 = false) :
    CM.AMerge (wch cd x) (wch cd y) (wch cd z) (bv ((cd z).aux 0)) (bv ((cd z).aux 1)) := by
  simp only [amChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hex⟩, hz⟩, hrtz⟩, hx⟩, hy⟩, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, bv_zero _, bv_zero _, rb_zero hr, bv_zero _, bv_zero _⟩
  · intro t hmv; exact arb_bool _ _ _ _ (step_of h1 hmv)
  · intro t hmv; exact arb_bool _ _ _ _ (step_of h2 hmv)
  · intro t
    exact excl_bool _ _ (pw_of hex (fun t ht => by
      obtain ⟨h1, h2⟩ := nm ht; simp only [bv_st h1, bv_st h2]) t)
  · intro t hmv; have := step_ofR hz hmv; simpa [wch, CD.ch] using this
  · intro t h0 h1'
    have hmv : rb (cd z) (t + 1) ≠ rb (cd z) t := by
      simp only [wch, CD.ch] at h0 h1'; rw [h0, h1']; decide
    have := step_ofR hrtz hmv
    simp only [wch, CD.ch] at h0 h1' ⊢
    simpa [h0, h1'] using this
  · intro t hmv; have := step_of hx hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of hy hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t
    have := pw_of hd (fun t ht => by
      obtain ⟨h1, h5⟩ := nm ht; obtain ⟨h1, h4⟩ := nm h1; obtain ⟨h1, h3⟩ := nm h1
      obtain ⟨h1, h2⟩ := nm h1
      simp only [nv_st h1, bv_st h2, bv_st h3, nv_st h4, nv_st h5]) t
    simp only [beq_iff_eq] at this
    exact this

theorem link_sound {i o : Fin n} (h : linkChk cd i o = true) (hr : (cd o).r0 = false) :
    Link.Link (wch cd i) (wch cd o) (bv ((cd o).aux 0)) := by
  simp only [linkChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hc, ha⟩, hr'⟩, hop⟩, hho⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, bv_zero _, bv_zero _, rb_zero hr⟩
  · intro t hmv; have := step_of hc hmv; simpa [wch, CD.ch] using this
  · intro t hmv; have := step_of ha hmv; simpa [wch, CD.ch] using this
  · intro t hmv; have := step_ofR hr' hmv; simpa [wch, CD.ch] using this
  · intro t hct
    have := pw_of hop (fun t ht => by
      obtain ⟨h1, h3⟩ := nm ht; obtain ⟨h1, h2⟩ := nm h1
      simp only [bv_st h1, nv_st h2, nv_st h3]) t
    simp only [hct, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this
  · intro t hc0
    show nv (cd o).d0 (cd o).dt (t + 1) = nv (cd o).d0 (cd o).dt t
    by_cases ht : t ∈ (cd o).dts
    · have := List.all_eq_true.mp hho t ht
      simp only [hc0, Bool.false_or, beq_iff_eq] at this
      exact this
    · exact nv_st ht

theorem src_sound {z : Fin n} {v : Nat} (h : srcChk cd z v = true) : SrcR (wch cd z) v := by
  simp only [srcChk, Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro t hmv; have := step_ofR h.1 hmv; simpa [wch, CD.ch] using this
  · intro t
    have := pw_of h.2 (fun t ht => by simp only [nv_st ht]) t
    simpa [wch, CD.ch] using this

theorem sink_sound {i : Fin n} (h : sinkChk cd i = true) : Ops.Gcd.Sink (wch cd i) := by
  refine ⟨?_, bv_zero _⟩
  intro t hmv; have := step_of h hmv; simpa [wch, CD.ch] using this

theorem kChkR_sound (sv : Nat → Nat) (k : K n) (h : kChkR cd sv k = true) : CellR (wch cd) sv k := by
  simp only [kChkR, Bool.and_eq_true] at h
  obtain ⟨hr, h⟩ := h
  cases k with
  | forkG i os =>
    simp [r0Chk, K.outsC] at hr
    exact fork_sound h hr
  | forkH i os l hh d hs =>
    simp [r0Chk, K.outsC] at hr
    exact fork_sound h (fun c hc => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc; exact hr p.1 p.2 hp)
  | join ins o e js _ => simp [r0Chk, K.outsC] at hr; exact join_sound h hr
  | bjoin ins o ec ed => simp [r0Chk, K.outsC] at hr; exact join_sound h hr
  | steerC j t f => simp [r0Chk, K.outsC] at hr; exact steer_sound h hr.1 hr.2
  | steerD j t f fd _ => simp [r0Chk, K.outsC] at hr; exact steer_sound h hr.1 hr.2
  | mux c x y z _ => simp [r0Chk, K.outsC] at hr; exact ⟨_, _, mux_sound h hr⟩
  | muxn c x0 x1 x2 z _ => simp [r0Chk, K.outsC] at hr; exact ⟨_, muxn_sound h hr⟩
  | amerge x y z _ => simp [r0Chk, K.outsC] at hr; exact ⟨_, _, am_sound h hr⟩
  | link i o => simp [r0Chk, K.outsC] at hr; exact ⟨_, link_sound h hr⟩
  | src z which _ => exact src_sound h
  | sink i => exact sink_sound h

/-! ## The rig's environment gates (`RigEnv`) -/

/-- `RigEnv (rb x) (bv kL)` checked at the toggle steps of each signal. -/
def envChk (x : CD) (kL : List Nat) : Bool :=
  x.rq.all (fun e => (!riseB (rb x) e || bv kL e) && (!fallB (rb x) e || !bv kL e)) &&
  kL.all (fun e => (!riseB (bv kL) e || !rb x e) && (!fallB (bv kL) e || rb x e))

theorem mv_of_rise {s : Trace} {t : Nat} (h : riseB s t = true) : s (t + 1) ≠ s t := by
  simp only [riseB, Bool.and_eq_true, Bool.not_eq_true'] at h; rw [h.1, h.2]; decide

theorem mv_of_fall {s : Trace} {t : Nat} (h : fallB s t = true) : s (t + 1) ≠ s t := by
  simp only [fallB, Bool.and_eq_true, Bool.not_eq_true'] at h; rw [h.1, h.2]; decide

theorem env_of {x : CD} {kL : List Nat} (h : envChk x kL = true) : Gcd.RigEnv (rb x) (bv kL) := by
  simp only [envChk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun t hr => ?_, fun t hf => ?_, fun t hr => ?_, fun t hf => ?_⟩
  · have := step_ofR h1 (mv_of_rise hr); simp [hr] at this; exact this.1
  · have := step_ofR h1 (mv_of_fall hf); simp [hf] at this; exact this.2
  · have := step_of h2 (mv_of_rise hr); simp [hr] at this; exact this.1
  · have := step_of h2 (mv_of_fall hf); simp [hf] at this; exact this.2

end Formal.Net.CapNet.RigWit
