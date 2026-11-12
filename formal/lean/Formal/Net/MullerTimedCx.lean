import Formal.Net.MullerTimed
import Formal.Net.MullerTimedInst

/-!
# Probe 8g: the converse. When the inequality fails, a timed trace glitches

`MullerTimed` proves: `FbBound` (feedback route max < lower-bound sum of
each neighbour loop) implies every timed trace is an rt run (no glitch,
protocol). Here: when the inequality fails, there is a concrete timed trace,
every node inside its delay interval, that glitches and breaks the protocol.
This lifts 8c's `free_hazard_n1` (the sink-side race, n = 1) to time.

## A deterministic witness: fixed-delay inertial simulation
`sim d` runs the chain with one fixed inertial delay `d i` per node: node `i`
takes the value of its gate function once that value has been stable for
`d i` ps (an age counter per node). `sim_timed`: this trace is a `Timed`
trace with bounds `[d i, d i]`, hence (`Inertial.widen`) with any bounds
`lo i ≤ d i ≤ hi i`. Generic in `n` and `d`.

## The instance (n = 1), numbers from probe 11b
Intervals (ps): `c 0` LUT6 `[45, 124]` and feedback route `f 0` `[213, 709]`
(11b, seed 1, routed `bd_c2` O -> B1); ack route `w 0` `[71, 709]`; req path
`b 0` = route + LUT1 + route `[187, 1542]`; sink response `snk` `[45, 124]`
(a LUT); source response `src` `[800, 2000]`. Route lower bound 71 ps = the
smallest LUT-to-LUT route lower bound in 11b's four seeds (`pinDelay`). The
sink-side loop violates the inequality (`709 ≥ 187 + 45`), the source-side one
holds (`709 < 71 + 800`). Delays chosen: `src 800, snk 45, c0 45, b0 187,
w0 71, f0 709`.

Events (ps): src↑ 800, c0↑ 845, w0↑ 916, b0↑ 1032, snk↑ 1077. At 1077 the
LUT sees `I0 = 1, I1 = 1` (hold) with `I2` still 0 (feedback not arrived,
due at 1554): it recomputes 0, c0 falls at 1122 (the token is retracted),
the feedback pulse is swallowed, w0 falls at 1193 while req is still high.
`cx_protocol_broken`: the input link (`src`, `w 0`) breaks `RecvStep` at 1192
(ack falls before req). `cx_glitch`: the source's excitation (to drop req,
since 916) is withdrawn at 1193 without it firing: a runt on `ack_in`.
-/

namespace Formal.Net.MullerTimed
open Formal.Net Formal.Net.Muller Formal.Net.CoreLut
open Formal.Net.Bridge (Inertial)

/-- Bitmask with bit `i` = `g i` for `i < N`. -/
def ofBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | N + 1, g => ofBits N g ||| (if g N then 2 ^ N else 0)

theorem testBit_ofBits (g : Nat → Bool) (i : Nat) :
    ∀ N, (ofBits N g).testBit i = (decide (i < N) && g i) := by
  intro N
  induction N with
  | zero => simp [ofBits]
  | succ N ih =>
    simp only [ofBits, Nat.testBit_or, ih]
    by_cases h : g N
    · simp only [h, ite_true, Nat.testBit_two_pow]
      by_cases e : i = N
      · subst e; simp [h]
      · have : ¬ N = i := fun h => e h.symm
        simp only [this, decide_false, Bool.or_false]
        by_cases hl : i < N
        · simp [hl, show i < N + 1 by omega]
        · simp [hl, show ¬ i < N + 1 by omega]
    · simp only [h, Bool.false_eq_true, ite_false, Nat.zero_testBit, Bool.or_false]
      by_cases e : i = N
      · subst e; simp [h]
      · by_cases hl : i < N
        · simp [hl, show i < N + 1 by omega]
        · simp [hl, show ¬ i < N + 1 by omega]

/-- Simulator state at `t`: node values `x t`, the gate values `e (t-1)`
(bitmask) and, per node, the length of the current run of its gate value
ending at `t - 1`. -/
structure Sim where
  x   : Nat
  ev  : Nat
  age : List Nat

def simStep (n : Nat) (d : Nat → Nat) (st : Sim) : Sim :=
  let N := numNodes n
  let e := ofBits N (fun i => nextVal .free n st.x i)
  let a := (List.range N).map (fun i =>
    if e.testBit i = st.ev.testBit i then st.age.getD i 0 + 1 else 1)
  ⟨ofBits N (fun i => if d i ≤ a.getD i 0 then e.testBit i else get st.x i), e, a⟩

def sim (n : Nat) (d : Nat → Nat) : Nat → Sim
  | 0 => ⟨0, 0, []⟩
  | t + 1 => simStep n d (sim n d t)

section
variable {n : Nat} {d : Nat → Nat}

/-- Gate value of node `i` along the simulated trace. -/
abbrev eS (n : Nat) (d : Nat → Nat) (t i : Nat) : Bool := nextVal .free n (sim n d t).x i

theorem getD_age (st : Sim) {i : Nat} (hi : i < numNodes n) :
    (simStep n d st).age.getD i 0 =
      (if (nextVal .free n st.x i) = st.ev.testBit i then st.age.getD i 0 + 1 else 1) := by
  simp only [simStep, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, testBit_ofBits, hi, decide_true, Bool.true_and]

theorem ev_succ (t : Nat) {i : Nat} (hi : i < numNodes n) :
    (sim n d (t + 1)).ev.testBit i = eS n d t i := by
  simp [sim, simStep, testBit_ofBits, hi]

theorem age_zero {i : Nat} : (sim n d 0).age.getD i 0 = 0 := by simp [sim]

theorem age_rec (t : Nat) {i : Nat} (hi : i < numNodes n) :
    (sim n d (t + 1)).age.getD i 0 =
      (if eS n d t i = (sim n d t).ev.testBit i then (sim n d t).age.getD i 0 + 1 else 1) :=
  getD_age (d := d) (sim n d t) hi

/-- The age counter is the length of the run of the gate value ending at `t`. -/
theorem age_spec {i : Nat} (hi : i < numNodes n) : ∀ t,
    1 ≤ (sim n d (t + 1)).age.getD i 0 ∧ (sim n d (t + 1)).age.getD i 0 ≤ t + 1 ∧
    (∀ u, t + 1 - (sim n d (t + 1)).age.getD i 0 ≤ u → u ≤ t → eS n d u i = eS n d t i) ∧
      (t + 1 - (sim n d (t + 1)).age.getD i 0 = 0 ∨
        eS n d (t - (sim n d (t + 1)).age.getD i 0) i ≠ eS n d t i) := by
  intro t
  induction t with
  | zero =>
    have ha : (sim n d (0 + 1)).age.getD i 0 = 1 := by
      rw [age_rec 0 hi, age_zero]; split <;> rfl
    rw [ha]
    refine ⟨by omega, by omega, fun u h1 h2 => by
      have : u = 0 := by omega
      rw [this], Or.inl (by omega)⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hr := age_rec (d := d) (t + 1) hi
    rw [ev_succ t hi] at hr
    by_cases he : eS n d (t + 1) i = eS n d t i
    · rw [if_pos he] at hr
      rw [hr]
      refine ⟨by omega, by omega, fun u hu1 hu2 => ?_, ?_⟩
      · by_cases e : u = t + 1
        · rw [e]
        · have := h3 u (by omega) (by omega)
          rw [this]; exact he.symm
      · rcases h4 with h | h
        · left; omega
        · right
          have e1 : t + 1 - ((sim n d (t + 1)).age.getD i 0 + 1) =
              t - (sim n d (t + 1)).age.getD i 0 := by omega
          rw [e1, he]; exact h
    · rw [if_neg he] at hr
      rw [hr]
      refine ⟨by omega, by omega, fun u hu1 hu2 => ?_, Or.inr ?_⟩
      · have : u = t + 1 := by omega
        rw [this]
      · simp only [Nat.add_sub_cancel]; exact fun h => he h.symm

theorem x_succ (t : Nat) {i : Nat} (hi : i < numNodes n) :
    get (sim n d (t + 1)).x i =
      (if d i ≤ (sim n d (t + 1)).age.getD i 0 then eS n d t i else get (sim n d t).x i) := by
  show get (simStep n d (sim n d t)).x i = (if d i ≤ (simStep n d (sim n d t)).age.getD i 0 then _ else _)
  simp only [simStep, Muller.get, testBit_ofBits, hi, decide_true, Bool.true_and]

theorem x_frame (t : Nat) {j : Nat} (hj : numNodes n ≤ j) : get (sim n d t).x j = false := by
  cases t with
  | zero => exact get_zero j
  | succ t =>
    show get (simStep n d (sim n d t)).x j = false
    simp only [simStep, Muller.get, testBit_ofBits]
    simp [show ¬ j < numNodes n by omega]

/-- Stable on the window `[t+1-D, t]` iff the age reached `D`. -/
theorem stable_iff {i : Nat} (hi : i < numNodes n) (t D : Nat) :
    (D ≤ t + 1 ∧ ∀ u, t + 1 - D ≤ u → u ≤ t → eS n d u i = eS n d t i) ↔
      D ≤ (sim n d (t + 1)).age.getD i 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := age_spec (d := d) hi t
  constructor
  · rintro ⟨hD, hw⟩
    apply Classical.byContradiction; intro hlt
    rcases h4 with h | h
    · omega
    · exact h (hw _ (by omega) (by omega))
  · intro hD
    exact ⟨by omega, fun u hu1 hu2 => h3 u (by omega) hu2⟩

/-- **The simulated trace is a timed trace** with fixed delays `[d i, d i]`. -/
theorem sim_timed (hd : ∀ i, 1 ≤ d i) : Timed n d d (fun t => (sim n d t).x) where
  init := rfl
  frame := fun t j hj => x_frame t hj
  gate i hi := {
    lo_pos := hd i
    cause := by
      intro t hc
      have hc' : get (sim n d t).x i ≠ get (sim n d (t + 1)).x i := hc
      clear hc
      show d i ≤ t + 1 ∧ ∀ u, t + 1 - d i ≤ u → u ≤ t →
        nextVal .free n (sim n d u).x i = get (sim n d (t + 1)).x i
      rw [x_succ t hi] at hc' ⊢
      by_cases hD : d i ≤ (sim n d (t + 1)).age.getD i 0
      · simp only [hD, ite_true] at hc' ⊢
        obtain ⟨h1, h2⟩ := (stable_iff hi t (d i)).2 hD
        exact ⟨h1, fun u hu1 hu2 => h2 u hu1 hu2⟩
      · simp only [hD, ite_false] at hc'; exact absurd rfl hc'
    settle := by
      intro t ht hs
      have hd1 := hd i
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := hd i; omega⟩
      rw [x_succ t' hi]
      have hst : d i ≤ t' + 1 ∧ ∀ u, t' + 1 - d i ≤ u → u ≤ t' → eS n d u i = eS n d t' i := by
        refine ⟨by omega, fun u hu1 hu2 => ?_⟩
        have a1 := hs u (by omega) (by omega)
        have a2 := hs t' (by omega) (by omega)
        simp only at a1 a2
        show nextVal .free n (sim n d u).x i = nextVal .free n (sim n d t').x i
        rw [a1, a2]
      have hD := (stable_iff hi t' (d i)).1 hst
      simp only [hD, ite_true]
      have a1 := hs (t' + 1) (by omega) (Nat.le_refl _)
      have a2 := hs t' (by omega) (by omega)
      simp only at a1 a2
      show nextVal .free n (sim n d t').x i = nextVal .free n (sim n d (t' + 1)).x i
      rw [a1, a2] }
end

/-- Widening an inertial channel's bounds. -/
theorem inertial_widen {d lo hi : Nat} {e o : Trace} (h : Inertial d d e o)
    (h1 : 1 ≤ lo) (h2 : lo ≤ d) (h3 : d ≤ hi) : Inertial lo hi e o where
  lo_pos := h1
  cause t hc := by
    obtain ⟨a, b⟩ := h.cause t hc
    exact ⟨by omega, fun u hu1 hu2 => b u (by omega) hu2⟩
  settle t ht hs := h.settle t (by omega) (fun u hu1 hu2 => by
    rw [hs u (by omega) hu2, hs (t - d) (by omega) (by omega)])

theorem Timed.widen {n : Nat} {d lo hi : Nat → Nat} {x : Nat → Nat} (h : Timed n d d x)
    (hb : ∀ i, i < numNodes n → 1 ≤ lo i ∧ lo i ≤ d i ∧ d i ≤ hi i) : Timed n lo hi x where
  init := h.init
  frame := h.frame
  gate i hi' := inertial_widen (h.gate i hi') (hb i hi').1 (hb i hi').2.1 (hb i hi').2.2

/-! ## The instance: n = 1, 11b numbers -/

/-- Node order: `src 0, snk 1, c0 2, b0 3, w0 4, f0 5`. -/
def cxD (i : Nat) : Nat := [800, 45, 45, 187, 71, 709].getD i 1
def cxLo (i : Nat) : Nat := [800, 45, 45, 187, 71, 213].getD i 1
def cxHi (i : Nat) : Nat := [2000, 124, 124, 1542, 709, 709].getD i 1

def cxX (t : Nat) : Nat := (sim 1 cxD t).x

theorem cx_timed : Timed 1 cxLo cxHi cxX := by
  have h := sim_timed (n := 1) (d := cxD) (fun i => by
    unfold cxD
    rcases i with _ | _ | _ | _ | _ | _ | i <;> simp)
  exact h.widen (fun i hi => by
    simp only [numNodes] at hi
    unfold cxLo cxD cxHi
    rcases i with _ | _ | _ | _ | _ | _ | i <;> simp <;> omega)

/-- The 11b intervals violate the sink-side inequality (only that one). -/
theorem cx_violates : ¬ FbBound 1 cxLo cxHi ∧
    cxHi (f 0) ≥ cxLo (b 0) + cxLo snk ∧ cxHi (f 0) < cxLo (w 0) + cxLo src := by
  refine ⟨fun h => ?_, by decide, by decide⟩
  have := h.succL
  revert this; decide

set_option maxRecDepth 100000 in
/-- The states the witness passes through (checked by kernel evaluation). -/
theorem cx_events :
    get (cxX 1077) snk = true ∧ get (cxX 1077) (c 0) = true ∧ get (cxX 1077) (f 0) = false ∧
    get (cxX 1192) src = true ∧ get (cxX 1192) (w 0) = true ∧
    get (cxX 1193) src = true ∧ get (cxX 1193) (w 0) = false := by
  decide +kernel

/-- **The protocol breaks** on the input link: the ack (`w 0`, at the
source) falls while req (`src`) is still high. -/
theorem cx_protocol_broken :
    ¬ Handshake.Protocol ⟨fun t => get (cxX t) src, fun t => get (cxX t) (w 0), fun _ => 0⟩ := by
  intro h
  have := (h.2 1192).2
  simp only [Handshake.RecvStep] at this
  obtain ⟨_, _, _, h1, h2, _, h3⟩ := cx_events
  rw [h1, h2, h3] at this
  exact this (by decide) rfl

set_option maxRecDepth 100000 in
/-- **The glitch**: the source is excited at 1192 (its gate value `!w0` is 0,
its output 1), does not fire, and at 1193 its excitation is gone: a runt on
`ack_in`, which 8c's `HazardFree` forbids. -/
theorem cx_glitch :
    nextVal .free 1 (cxX 1192) src ≠ get (cxX 1192) src ∧
    get (cxX 1193) src = get (cxX 1192) src ∧
    nextVal .free 1 (cxX 1193) src = get (cxX 1193) src := by
  decide +kernel

/-- The same race at the boundary `hi (f k) = Σ lo`: the feedback (I2) and the
ack (I1) arrive in the same ps. The atomic LUT of the timed model sees no
glitch, but the transition `(I0, I1, I2) = (1, 0, 0) → (1, 1, 1)` crosses the
function hazard `(1, 1, 0) ↦ 0` of the real INIT: a LUT whose I1 switches
before I2 inside the mux tree can glitch. So the strict inequality is the
right condition for a mux-tree LUT. -/
theorem boundary_function_hazard :
    evalL INIT_bd_c2n [true, false, false, false, false, false] = true ∧
    evalL INIT_bd_c2n [true, true, true, false, false, false] = true ∧
    evalL INIT_bd_c2n [true, true, false, false, false, false] = false := by decide

/-! ## Non-vacuity of the positive theorem

The same simulator with the feedback route at 76 ps (11b, seed 1, `bd_c2n`
O -> A5, the short in-slice route) meets `FbBound`, so `timed1_protocol` and
`timed1_hazard_free` apply to a real (non-empty) timed trace. -/

def okD (i : Nat) : Nat := [800, 45, 45, 187, 71, 76].getD i 1

theorem ok_timed : Timed 1 okD okD (fun t => (sim 1 okD t).x) :=
  sim_timed (fun i => by unfold okD; rcases i with _ | _ | _ | _ | _ | _ | i <;> simp)

theorem ok_bound : FbBound 1 okD okD :=
  ⟨by decide, fun _ h1 h2 => absurd h2 (by omega), by decide, fun _ h => absurd h (by omega)⟩

theorem ok_protocol {X Y : Nat} (hp : (X, Y) ∈ pairs 1) :
    Handshake.Protocol ⟨fun t => get (sim 1 okD t).x X, fun t => get (sim 1 okD t).x Y, fun _ => 0⟩ :=
  timed1_protocol ok_timed ok_bound hp

end Formal.Net.MullerTimed
