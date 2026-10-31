import Formal.Net.CapstoneNetDef

/-!
# Probe C-8t: event-list circuit runs and a kernel checker for the gate models

A circuit run of a `CapNet` network is given by finite event lists:
* a binary signal by the list of its toggle steps `L` (`bv L t` = parity of the number of
  `e ∈ L` with `e < t`; low at 0, as every reset field of the cell models asks);
* a bus by an initial value and a list of change points `(e, v)` (`nv d L t` = the value of
  the last listed `e < t`, else `d`).

`CD` collects one channel's request, acknowledge and bus, plus the internal traces of its
producer (the link's `c`, the mux's `j0 j1`, the 3-way mux's `j0 j1 j2`, the arbiter's
`g1 g2`), so every existential witness of `Cell` is keyed by the producer's output channel.

`kChk cd sv k` is a Boolean checker of `Cell (wch cd) sv k`, and `kChk_sound` proves it sound.
The checker evaluates each "a signal moves only to f(previous tick)" field at the toggle steps
of that signal only (`step_of`), and each pointwise field ("bus = g(buses)") at time 0 and
right after every change point of the signals involved (`pw_ind`). Signals are constant off
their event lists (`bv_st`, `nv_st`), which is what makes those finite checks cover all `t`.
`heldChk` is the same for `Held` (H_BUNDLE).

Nothing here is about gcd_hw; the data and the kernel checks are in `CapstoneWitnessData`
and `CapstoneWitnessCells`.
-/

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw

/-! ## Event-list signals -/

def cntLt : List Nat → Nat → Nat
  | [], _ => 0
  | e :: L, t => cntLt L t + (if e < t then 1 else 0)

def bv (L : List Nat) (t : Nat) : Bool := cntLt L t % 2 == 1

def nvA : List (Nat × Nat) → Nat → Nat → Nat
  | [], _, acc => acc
  | p :: L, t, acc => nvA L t (if p.1 < t then p.2 else acc)

def nv (d : Nat) (L : List (Nat × Nat)) (t : Nat) : Nat := nvA L t d

theorem cntLt_zero : ∀ L : List Nat, cntLt L 0 = 0
  | [] => rfl
  | e :: L => by simp [cntLt, cntLt_zero L]

theorem bv_zero (L : List Nat) : bv L 0 = false := by simp [bv, cntLt_zero]

theorem cntLt_st {t : Nat} : ∀ {L : List Nat}, t ∉ L → cntLt L (t + 1) = cntLt L t
  | [], _ => rfl
  | e :: L, h => by
    have he : e ≠ t := fun h' => h (h' ▸ List.mem_cons_self ..)
    have hL : t ∉ L := fun h' => h (List.mem_cons_of_mem _ h')
    simp only [cntLt, cntLt_st hL]
    have : (e < t + 1) ↔ (e < t) := by omega
    simp only [this]

theorem bv_st {L : List Nat} {t : Nat} (h : t ∉ L) : bv L (t + 1) = bv L t := by
  simp [bv, cntLt_st h]

theorem mem_of_ne {L : List Nat} {t : Nat} (h : bv L (t + 1) ≠ bv L t) : t ∈ L :=
  Classical.byContradiction fun hn => h (bv_st hn)

theorem nvA_st {t : Nat} : ∀ {L : List (Nat × Nat)} (acc : Nat), t ∉ L.map Prod.fst →
    nvA L (t + 1) acc = nvA L t acc
  | [], _, _ => rfl
  | p :: L, acc, h => by
    have he : p.1 ≠ t := fun h' => h (by simp [h'])
    have hL : t ∉ L.map Prod.fst := fun h' => h (List.mem_cons_of_mem _ h')
    simp only [nvA]
    have : (p.1 < t + 1) ↔ (p.1 < t) := by omega
    simp only [this]
    exact nvA_st _ hL

theorem nv_st {d : Nat} {L : List (Nat × Nat)} {t : Nat} (h : t ∉ L.map Prod.fst) :
    nv d L (t + 1) = nv d L t := nvA_st d h

/-- Pointwise induction over the change points `S`. -/
theorem pw_ind (S : List Nat) (Q : Nat → Bool) (h0 : Q 0 = true) (hS : ∀ e ∈ S, Q (e + 1) = true)
    (hst : ∀ t, t ∉ S → Q (t + 1) = Q t) : ∀ t, Q t = true := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    by_cases h : t ∈ S
    · exact hS t h
    · rw [hst t h, ih]

def pwChk (S : List Nat) (Q : Nat → Bool) : Bool := Q 0 && S.all (fun e => Q (e + 1))

theorem pw_of {S : List Nat} {Q : Nat → Bool} (h : pwChk S Q = true)
    (hst : ∀ t, t ∉ S → Q (t + 1) = Q t) : ∀ t, Q t = true := by
  simp only [pwChk, Bool.and_eq_true, List.all_eq_true] at h
  exact pw_ind S Q h.1 h.2 hst

theorem step_of {L : List Nat} {P : Nat → Bool} (h : L.all P = true) {t : Nat}
    (hne : bv L (t + 1) ≠ bv L t) : P t = true :=
  List.all_eq_true.mp h t (mem_of_ne hne)

/-! ## Channels -/

structure CD where
  rq : List Nat
  ak : List Nat
  d0 : Nat
  dt : List (Nat × Nat)
  ax : List (List Nat)
  deriving Repr

def CD.ch (x : CD) : Chan := ⟨bv x.rq, bv x.ak, nv x.d0 x.dt⟩
def CD.dts (x : CD) : List Nat := x.dt.map Prod.fst
def CD.aux (x : CD) (k : Nat) : List Nat := x.ax.getD k []

variable {n : Nat} (cd : Fin n → CD)

def wch (c : Fin n) : Chan := (cd c).ch

/-- `Held` checker. -/
def heldChk (x : CD) : Bool :=
  x.dt.all fun p => !((bv x.rq p.1 || bv x.ak p.1) && (bv x.rq (p.1 + 1) || bv x.ak (p.1 + 1))) ||
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

abbrev rqv (c : Fin n) (t : Nat) : Bool := bv (cd c).rq t
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

/-! ## Soundness -/

variable {cd}

theorem nm {L L' : List Nat} {t : Nat} (h : t ∉ L ++ L') : t ∉ L ∧ t ∉ L' := by
  simp only [List.mem_append, not_or] at h; exact h

theorem fork_sound {i : Fin n} {os : List (Fin n)} (h : forkChk cd i os = true) :
    Fork.Fork (wch cd i) (os.map (wch cd)) := by
  simp only [forkChk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨hne, hw⟩, hc⟩, hd⟩ := h
  refine ⟨by simpa using hne, ?_, ?_, ?_, bv_zero _, ?_⟩
  · intro o ho t hmv
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ho
    have := step_of (List.all_eq_true.mp hw c hc') hmv
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
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho
    exact bv_zero _

theorem map_dv_st {ins : List (Fin n)} {t : Nat} (h : t ∉ ins.flatMap (fun i => (cd i).dts)) :
    ins.map (fun i => dv cd i (t + 1)) = ins.map (fun i => dv cd i t) := by
  apply List.map_congr_left
  intro i hi
  exact nv_st (fun h' => h (List.mem_flatMap.2 ⟨i, hi, h'⟩))

theorem join_sound {g : List Nat → Nat} {ins : List (Fin n)} {o : Fin n} (h : joinChk cd g ins o = true) :
    Join.Join g (ins.map (wch cd)) (wch cd o) := by
  simp only [joinChk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨hne, hc⟩, hw⟩, hd⟩ := h
  refine ⟨by simpa using hne, ?_, ?_, ?_, bv_zero _, ?_⟩
  · intro t hmv i hi
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hi
    have := List.all_eq_true.mp (step_of hc hmv) c hc'
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

theorem steer_sound {f : Nat → Nat} {j tc fc : Fin n} (h : steerChk cd f j tc fc = true) :
    Steer.Steer sel2 f (wch cd j) (fun b => wch cd (bif b then tc else fc)) := by
  simp only [steerChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ht, hf⟩, ho⟩, hdt⟩, hdf⟩ := h
  refine ⟨?_, ?_, ?_, bv_zero _, fun b => by cases b <;> exact bv_zero _⟩
  · intro b t hmv
    cases b
    · have := step_of hf hmv; simpa [wch, CD.ch] using this
    · have := step_of ht hmv; simpa [wch, CD.ch] using this
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

theorem mux_sound {c x y z : Fin n} (h : muxChk cd c x y z = true) :
    Mux.Mux sel2 (wch cd x) (wch cd y) (wch cd c) (wch cd z) (bv ((cd z).aux 0)) (bv ((cd z).aux 1)) := by
  simp only [muxChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, hz⟩, hx⟩, hy⟩, hc⟩, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, bv_zero _, bv_zero _, bv_zero _, bv_zero _, bv_zero _, bv_zero _⟩
  · intro t hmv; have := step_of h0 hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of h1 hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of hz hmv; simpa [wch, CD.ch] using this
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

theorem muxn_sound {c x0 x1 x2 z : Fin n} (h : muxnChk cd c x0 x1 x2 z = true) :
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
  refine ⟨?_, ?_, ?_, ?_, ?_, fun k _ => bv_zero _, bv_zero _, fun k _ => bv_zero _, bv_zero _⟩
  · intro k hk t hmv; have := step_of (hj' k hk) hmv
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this
  · intro t hmv; have := step_of hz hmv; simpa [wch, CD.ch] using this
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

theorem am_sound {x y z : Fin n} (h : amChk cd x y z = true) :
    CM.AMerge (wch cd x) (wch cd y) (wch cd z) (bv ((cd z).aux 0)) (bv ((cd z).aux 1)) := by
  simp only [amChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hex⟩, hz⟩, hrtz⟩, hx⟩, hy⟩, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, bv_zero _, bv_zero _, bv_zero _, bv_zero _, bv_zero _⟩
  · intro t hmv; exact arb_bool _ _ _ _ (step_of h1 hmv)
  · intro t hmv; exact arb_bool _ _ _ _ (step_of h2 hmv)
  · intro t
    exact excl_bool _ _ (pw_of hex (fun t ht => by
      obtain ⟨h1, h2⟩ := nm ht; simp only [bv_st h1, bv_st h2]) t)
  · intro t hmv; have := step_of hz hmv; simpa [wch, CD.ch] using this
  · intro t h0 h1'
    have hmv : bv (cd z).rq (t + 1) ≠ bv (cd z).rq t := by
      simp only [wch, CD.ch] at h0 h1'; rw [h0, h1']; decide
    have := step_of hrtz hmv
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

theorem link_sound {i o : Fin n} (h : linkChk cd i o = true) :
    Link.Link (wch cd i) (wch cd o) (bv ((cd o).aux 0)) := by
  simp only [linkChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hc, ha⟩, hr⟩, hop⟩, hho⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, bv_zero _, bv_zero _, bv_zero _⟩
  · intro t hmv; have := step_of hc hmv; simpa [wch, CD.ch] using this
  · intro t hmv; have := step_of ha hmv; simpa [wch, CD.ch] using this
  · intro t hmv; have := step_of hr hmv; simpa [wch, CD.ch] using this
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

theorem src_sound {z : Fin n} {v : Nat} (h : srcChk cd z v = true) : Capstone.Src (wch cd z) v := by
  simp only [srcChk, Bool.and_eq_true] at h
  refine ⟨?_, ?_, bv_zero _⟩
  · intro t hmv; have := step_of h.1 hmv; simpa [wch, CD.ch] using this
  · intro t
    have := pw_of h.2 (fun t ht => by simp only [nv_st ht]) t
    simpa [wch, CD.ch] using this

theorem sink_sound {i : Fin n} (h : sinkChk cd i = true) : Ops.Gcd.Sink (wch cd i) := by
  refine ⟨?_, bv_zero _⟩
  intro t hmv; have := step_of h hmv; simpa [wch, CD.ch] using this

theorem kChk_sound (sv : Nat → Nat) (k : K n) (h : kChk cd sv k = true) : Cell (wch cd) sv k := by
  cases k with
  | forkG i os => exact fork_sound h
  | forkH i os l hh d hs => exact fork_sound h
  | join ins o e js _ => exact join_sound h
  | bjoin ins o ec ed => exact join_sound h
  | steerC j t f => exact steer_sound h
  | steerD j t f fd _ => exact steer_sound h
  | mux c x y z _ => exact ⟨_, _, mux_sound h⟩
  | muxn c x0 x1 x2 z _ => exact ⟨_, muxn_sound h⟩
  | amerge x y z _ => exact ⟨_, _, am_sound h⟩
  | link i o => exact ⟨_, link_sound h⟩
  | src z which _ => exact src_sound h
  | sink i => exact sink_sound h

/-! ## One-shot request, and a close -/

theorem cnt_le_ite {f : Nat → Bool} {t1 : Nat} (h : ∀ e, f e = true → e = t1) :
    ∀ t, Handshake.cnt f t ≤ (if t1 < t then 1 else 0) := by
  intro t
  induction t with
  | zero => simp [Handshake.cnt]
  | succ t ih =>
    simp only [Handshake.cnt]
    by_cases hf : f t = true
    · have ht := h t hf
      subst ht
      have h0 : Handshake.cnt f t = 0 := by simp at ih; omega
      simp [hf, h0]
    · simp only [Bool.not_eq_true] at hf
      simp only [hf, Bool.false_eq_true, if_false, Nat.add_zero]
      by_cases h1 : t1 < t
      · have h2 : t1 < t + 1 := by omega
        simp only [h1, h2, if_true] at ih ⊢; omega
      · simp only [h1, if_false] at ih
        have : Handshake.cnt f t = 0 := by omega
        rw [this]; split <;> omega

theorem cnt_le_one {f : Nat → Bool} {t1 : Nat} (h : ∀ e, f e = true → e = t1) : ∀ t, Handshake.cnt f t ≤ 1 := by
  intro t; have := cnt_le_ite h t; split at this <;> omega

/-- A request whose toggle list is `[r, f]` with `r < f` rises at most once. -/
theorem once_of {L : List Nat} {r f : Nat} (hL : L = [r, f]) (hrf : r < f) :
    ∀ t, Handshake.cnt (riseB (bv L)) t ≤ 1 := by
  apply cnt_le_one (t1 := r)
  intro e he
  have hmv : bv L (e + 1) ≠ bv L e := by
    simp only [riseB, Bool.and_eq_true, Bool.not_eq_true'] at he; rw [he.1, he.2]; decide
  have hm := mem_of_ne hmv
  subst hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm
  · exact hm
  · subst hm
    simp only [riseB, Bool.and_eq_true, Bool.not_eq_true'] at he
    have h2 := he.2
    simp [bv, cntLt] at h2
    split at h2 <;> simp_all <;> omega

end Formal.Net.CapNet.Wit
