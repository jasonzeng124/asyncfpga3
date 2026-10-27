import Formal.Cells.Prelim

/-!
# Track 6c: matched delay lines (`bd_delay`) and the bundling condition (`bd_link`)

Sources: cells/rtl/bd_latch.v (`bd_delay`, `bd_latch`), cells/rtl/bd_link.v
(`bd_link`, header sections "req_out LEADS data_out" and "ack_in FALLS BEFORE
THE LATCH HAS CLOSED"), cells/verify/tighten.py (rules A, H, I, F).

## Time and gate model (gate fidelity)

* Time is `Nat` (one tick = any fixed quantum, e.g. 1 ps). A signal is
  `Sig := Nat → Bool`; before time 0 a signal is taken to hold its time-0
  value (truncated subtraction `t - s`).
* **Pin window.** Every LUT input pin is given as `(x, lo, hi)`: `x` is the
  DRIVING net, and `[lo, hi]` bounds the delay from that net to the LUT
  output through the routed wire AND the LUT's own pin-to-output arc (SDF
  INTERCONNECT + IOPATH for that pin). The output at time `t` may depend on
  `x` at any instant of the window `[t - hi, t - lo]`.
* **Gate relation (`Gate`).** `y t = b` whenever the Kleene closure of the
  LUT's real INIT (`lutK`, Prelim, hypothesis H_KLEENE_LUT) over the
  per-pin window readings (`winK`: `t`/`f` if the net was constant over the
  window, else `x`) is the definite value `b`. When the closure is `x` the
  output is unconstrained (glitches, runts, metastable levels are all
  allowed). This is a RELATION, not a function: every theorem below holds
  for every trace that satisfies it.
* **Soundness of the relation (`transport_gate`).** A transport-delay LUT
  `y t = lutB INIT [x_i (t - d_i)]` with each fixed `d_i ∈ [lo_i, hi_i]`
  satisfies `Gate`. The relation also covers delays that differ per edge or
  drift in time (anything that only ever reads the net inside its window),
  so a theorem about `Gate` is a theorem about all of those. It does NOT
  cover an inertial channel whose rejection width exceeds the window width
  (such a channel can hold an old value while the input is stable inside
  the window) -- noted, not used.
* **Feedback.** A latch is a LUT whose output net is also one of its own
  input pins, with its own window `[flo, fhi]` (the routed loop wire plus
  the I2-pin arc); H_LOOP_POS: `1 ≤ flo`.

The INIT constants are the cells' real ones, evaluated with `lutK`:
LUT1 `2'h2` (buffer), LUT2 `4'h8` (FASTFALL side stage, AND), LUT2 `4'hE`
(FASTRISE side stage, OR), latch LUT6 `64'hB8B8...B8` and LUT6_2
`64'hFF33_CC00_B8B8_B8B8`.
-/

namespace Formal.Cells.Bundling
open Formal.Cells

/-- A binary trace over discrete time. -/
abbrev Sig := Nat → Bool

/-- Decidability of `∀ k : K3, P k`, so `decide` can enumerate Kleene values. -/
instance decForallK3 (P : K3 → Prop) [DecidablePred P] : Decidable (∀ k, P k) :=
  decidable_of_iff (P .f ∧ P .t ∧ P .x)
    ⟨fun ⟨a, b, c⟩ k => by cases k <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-! ## 1. Windows, the gate relation, and its soundness for transport delay -/

/-- The values a net takes over the window `[t - hi, t - lo]`. -/
def winVals (x : Sig) (lo hi t : Nat) : List Bool :=
  (List.range (hi + 1 - lo)).map (fun k => x (t - (lo + k)))

/-- Kleene reading of a pin whose delay lies in `[lo, hi]`. -/
def winK (x : Sig) (lo hi t : Nat) : K3 :=
  if (winVals x lo hi t).all id then .t
  else if (winVals x lo hi t).all (!·) then .f else .x

theorem mem_winVals {x : Sig} {lo hi t : Nat} {b : Bool} :
    b ∈ winVals x lo hi t ↔ ∃ s, lo ≤ s ∧ s ≤ hi ∧ x (t - s) = b := by
  unfold winVals
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    exact ⟨lo + k, by omega, by omega, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩
    refine ⟨s - lo, List.mem_range.2 (by omega), ?_⟩
    have : lo + (s - lo) = s := by omega
    rw [this]

/-- A net constant over the window reads as that constant. -/
theorem win_const {x : Sig} {lo hi t : Nat} {b : Bool} (hlh : lo ≤ hi)
    (h : ∀ s, lo ≤ s → s ≤ hi → x (t - s) = b) : winK x lo hi t = K3.ofBool b := by
  have hall : ∀ y ∈ winVals x lo hi t, y = b := fun y hy => by
    obtain ⟨s, h1, h2, rfl⟩ := mem_winVals.1 hy
    exact h s h1 h2
  have hmem : b ∈ winVals x lo hi t :=
    mem_winVals.2 ⟨lo, Nat.le_refl _, hlh, h lo (Nat.le_refl _) hlh⟩
  cases b with
  | false =>
    have h1 : (winVals x lo hi t).all id = false := by
      rw [Bool.eq_false_iff]; intro hc
      have := List.all_eq_true.1 hc false hmem; simp at this
    have h2 : (winVals x lo hi t).all (!·) = true :=
      List.all_eq_true.2 (fun y hy => by rw [hall y hy]; rfl)
    unfold winK; rw [h1, h2]; rfl
  | true =>
    have h1 : (winVals x lo hi t).all id = true :=
      List.all_eq_true.2 (fun y hy => by rw [hall y hy]; rfl)
    unfold winK; rw [h1]; rfl

/-- Same, stated on absolute times: constant on `[t - hi, t - lo]`. -/
theorem win_eq {x : Sig} {lo hi t : Nat} {b : Bool} (hlh : lo ≤ hi)
    (h : ∀ u, t - hi ≤ u → u ≤ t - lo → x u = b) : winK x lo hi t = K3.ofBool b :=
  win_const hlh (fun s h1 h2 => h _ (by omega) (by omega))

/-- Every instant of the window is consistent with the window's reading. -/
theorem win_consistent {x : Sig} {lo hi t d : Nat} (h1 : lo ≤ d) (h2 : d ≤ hi) :
    K3.admits (winK x lo hi t) (x (t - d)) = true := by
  have hm : x (t - d) ∈ winVals x lo hi t := mem_winVals.2 ⟨d, h1, h2, rfl⟩
  unfold winK
  by_cases ha : (winVals x lo hi t).all id = true
  · simp only [ha, ↓reduceIte]
    have := List.all_eq_true.1 ha _ hm
    simp only [id] at this
    simp [K3.admits, this]
  · simp only [ha]
    by_cases hb : (winVals x lo hi t).all (!·) = true
    · simp only [hb, ↓reduceIte]
      have := List.all_eq_true.1 hb _ hm
      simp [K3.admits] at this ⊢; exact this
    · simp only [hb]; rfl

/-- Pointwise admissibility of a Boolean vector by a Kleene vector. -/
def AllConsistent : List K3 → List Bool → Prop
  | [], [] => True
  | k :: ks, v :: vs => K3.admits k v = true ∧ AllConsistent ks vs
  | _, _ => False

theorem mem_completions : ∀ (ks : List K3) (vs : List Bool),
    AllConsistent ks vs → vs ∈ completions ks
  | [], [], _ => by simp [completions]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | k :: ks, v :: vs, ⟨h, hs⟩ => by
    have ih := mem_completions ks vs hs
    cases v <;> simp [completions, h, ih]

/-- Soundness of the Kleene closure: a definite closure value is the value
of every consistent Boolean evaluation. -/
theorem lutK_sound {init : Nat} {ks : List K3} {vs : List Bool} {b : Bool}
    (h : lutK init ks = K3.ofBool b) (hv : vs ∈ completions ks) : lutB init vs = b := by
  have hm : lutB init vs ∈ (completions ks).map (lutB init) := List.mem_map.2 ⟨vs, hv, rfl⟩
  unfold lutK at h
  by_cases h1 : ((completions ks).map (lutB init)).all id = true
  · simp only [h1, ↓reduceIte] at h
    have := List.all_eq_true.1 h1 _ hm
    cases b
    · simp [K3.ofBool] at h
    · simpa using this
  · simp only [h1] at h
    by_cases h2 : ((completions ks).map (lutB init)).all (!·) = true
    · simp only [h2, ↓reduceIte] at h
      have := List.all_eq_true.1 h2 _ hm
      cases b
      · simpa using this
      · simp [K3.ofBool] at h
    · simp only [h2] at h
      cases b <;> simp [K3.ofBool] at h

/-- The gate relation: Kleene closure of the real INIT over the pin windows.
`pins` lists `(net, lo, hi)` in pin order I0, I1, ... -/
def Gate (init : Nat) (pins : List (Sig × Nat × Nat)) (y : Sig) : Prop :=
  ∀ t b, lutK init (pins.map (fun p => winK p.1 p.2.1 p.2.2 t)) = K3.ofBool b → y t = b

/-- A transport-delay LUT: every pin `(net, d)` read exactly `d` ticks ago. -/
def Transport (init : Nat) (pins : List (Sig × Nat)) (y : Sig) : Prop :=
  ∀ t, y t = lutB init (pins.map (fun p => p.1 (t - p.2)))

theorem allConsistent_map (t : Nat) : ∀ (ps : List (Sig × Nat × Nat × Nat)),
    (∀ p ∈ ps, p.2.2.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2.2) →
    AllConsistent (ps.map (fun p => winK p.1 p.2.2.1 p.2.2.2 t)) (ps.map (fun p => p.1 (t - p.2.1)))
  | [], _ => trivial
  | p :: ps, h => by
    refine ⟨?_, allConsistent_map t ps (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩
    have hp := h p List.mem_cons_self
    exact win_consistent hp.1 hp.2

/-- **Soundness of the window relation for transport delay.** A LUT with a
fixed transport delay `d_i ∈ [lo_i, hi_i]` on each pin satisfies `Gate`.
Pins are given as `(net, d, lo, hi)`. -/
theorem transport_gate (init : Nat) (ps : List (Sig × Nat × Nat × Nat)) (y : Sig)
    (hok : ∀ p ∈ ps, p.2.2.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2.2)
    (hy : Transport init (ps.map (fun p => (p.1, p.2.1))) y) :
    Gate init (ps.map (fun p => (p.1, p.2.2.1, p.2.2.2))) y := by
  intro t b h
  rw [hy t]
  rw [List.map_map] at h
  rw [List.map_map]
  exact lutK_sound h (mem_completions _ _ (allConsistent_map t ps hok))

/-! ## 2. The real INIT constants (cells/rtl/bd_latch.v), Kleene semantics -/

/-- `LUT1 #(.INIT(2'h2))`: the symmetric chain element and FAST stage 0. -/
def BUF : Nat := 0x2
/-- `LUT2 #(.INIT(4'h8))`, I0 = previous stage, I1 = `a`: FASTFALL side stage. -/
def FF_SIDE : Nat := 0x8
/-- `LUT2 #(.INIT(4'hE))`: FASTRISE side stage. -/
def FR_SIDE : Nat := 0xE
/-- `bd_latch` odd bit, LUT6, pins `d en q 0 0 0`. -/
def ODD : Nat := 0xB8B8B8B8B8B8B8B8
/-- `bd_latch` pair, LUT6_2, pins `d0 en q0 d1 q1 1`, O5 = q0, O6 = q1. -/
def PAIR : Nat := 0xFF33CC00B8B8B8B8

theorem buf_k : ∀ k : K3, lutK BUF [k] = k := by decide

/-- A side stage's fast value `c` (false for AND/FASTFALL, true for
OR/FASTRISE) on the TAP pin forces the output whatever the chain pin is. -/
def AbsorbTap (init : Nat) (c : Bool) : Prop := ∀ k, lutK init [k, K3.ofBool c] = K3.ofBool c
/-- The fast value on the CHAIN pin forces the output whatever the tap is. -/
def AbsorbChain (init : Nat) (c : Bool) : Prop := ∀ k, lutK init [K3.ofBool c, k] = K3.ofBool c
/-- With the tap at the slow value, the stage passes the chain pin. -/
def Pass (init : Nat) (c : Bool) : Prop :=
  ∀ v : Bool, lutK init [K3.ofBool v, K3.ofBool (!c)] = K3.ofBool v

theorem ff_absorbTap : AbsorbTap FF_SIDE false := by unfold AbsorbTap; decide
theorem ff_absorbChain : AbsorbChain FF_SIDE false := by unfold AbsorbChain; decide
theorem ff_pass : Pass FF_SIDE false := by unfold Pass; decide
theorem fr_absorbTap : AbsorbTap FR_SIDE true := by unfold AbsorbTap; decide
theorem fr_absorbChain : AbsorbChain FR_SIDE true := by unfold AbsorbChain; decide
theorem fr_pass : Pass FR_SIDE true := by unfold Pass; decide

/-- The latch LUTs ARE the Kleene mux `en ? d : q`, for all 3^k inputs
(the other bit's pins of the pair never reach this bit). -/
theorem odd_kleene : ∀ d en q : K3, lutK ODD [d, en, q, .f, .f, .f] = K3.mux en q d := by
  decide
theorem pair_o5_kleene : ∀ d0 en q0 d1 q1 : K3,
    lutK (PAIR % 2 ^ 32) [d0, en, q0, d1, q1] = K3.mux en q0 d0 := by decide
theorem pair_o6_kleene : ∀ d0 en q0 d1 q1 : K3,
    lutK PAIR [d0, en, q0, d1, q1, .t] = K3.mux en q1 d1 := by decide

theorem odd_bin : ∀ d en q : Bool,
    lutB ODD [d, en, q, false, false, false] = (if en then d else q) := by decide
theorem buf_bin : ∀ a : Bool, lutB BUF [a] = a := by decide
theorem ff_bin : ∀ a b : Bool, lutB FF_SIDE [a, b] = (a && b) := by decide

/-! ## 3. Gate helpers -/

/-- A net constant on a closed interval. -/
def StableOn (x : Sig) (v : Bool) (A B : Nat) : Prop := ∀ t, A ≤ t → t ≤ B → x t = v

theorem win_of_stable {x : Sig} {v : Bool} {lo hi A B t : Nat} (hlh : lo ≤ hi)
    (hx : StableOn x v A B) (h1 : A + hi ≤ t) (h2 : t ≤ B + lo) :
    winK x lo hi t = K3.ofBool v :=
  win_eq hlh (fun u hu1 hu2 => hx u (by omega) (by omega))

theorem gate_buf {x y : Sig} {lo hi t : Nat} {b : Bool} (hg : Gate BUF [(x, lo, hi)] y)
    (h : winK x lo hi t = K3.ofBool b) : y t = b :=
  hg t b (by show lutK BUF [winK x lo hi t] = _; rw [buf_k, h])

theorem gate_side_tap {init : Nat} {c : Bool} {x a y : Sig} {lo hi tlo thi t : Nat}
    (hg : Gate init [(x, lo, hi), (a, tlo, thi)] y) (hA : AbsorbTap init c)
    (h : winK a tlo thi t = K3.ofBool c) : y t = c :=
  hg t c (by show lutK init [winK x lo hi t, winK a tlo thi t] = _; rw [h, hA])

theorem gate_side_chain {init : Nat} {c : Bool} {x a y : Sig} {lo hi tlo thi t : Nat}
    (hg : Gate init [(x, lo, hi), (a, tlo, thi)] y) (hA : AbsorbChain init c)
    (h : winK x lo hi t = K3.ofBool c) : y t = c :=
  hg t c (by show lutK init [winK x lo hi t, winK a tlo thi t] = _; rw [h, hA])

theorem gate_side_pass {init : Nat} {c v : Bool} {x a y : Sig} {lo hi tlo thi t : Nat}
    (hg : Gate init [(x, lo, hi), (a, tlo, thi)] y) (hP : Pass init c)
    (h1 : winK x lo hi t = K3.ofBool v) (h2 : winK a tlo thi t = K3.ofBool (!c)) : y t = v :=
  hg t v (by show lutK init [winK x lo hi t, winK a tlo thi t] = _; rw [h1, h2, hP])

/-! ## 4. The symmetric chain (`bd_delay`, FASTFALL = FASTRISE = 0)

`s 0 = a`, `s N = z`, stage `i` is `LUT1 #(2'h2)` reading `s i` through a hop
(wire + LUT arc) whose delay lies in `[lo, hi]` (H_HOP_BOUNDS: per-hop SDF
min/max at the fast/slow corners, guardbanded; testable by ring oscillators
as in hw/README.md). -/

/-- A value held by `a` on `[T, T']` is held by stage `i` on
`[T + i*hi, T' + i*lo]`. Both edges, any polarity. -/
theorem sym_chain (s : Nat → Sig) (N lo hi : Nat) (hlh : lo ≤ hi)
    (hg : ∀ i, i < N → Gate BUF [(s i, lo, hi)] (s (i + 1)))
    (v : Bool) (T T' : Nat) (ha : StableOn (s 0) v T T') :
    ∀ i, i ≤ N → StableOn (s i) v (T + i * hi) (T' + i * lo) := by
  intro i
  induction i with
  | zero => intro _; simpa using ha
  | succ i ih =>
    intro hi' t h1 h2
    have e1 : (i + 1) * hi = i * hi + hi := by rw [Nat.add_mul, Nat.one_mul]
    have e2 : (i + 1) * lo = i * lo + lo := by rw [Nat.add_mul, Nat.one_mul]
    exact gate_buf (hg i (by omega)) (win_of_stable hlh (ih (by omega)) (by omega) (by omega))

/-- **Symmetric chain, edge form.** If `a` holds `u` on `[T0, T-1]` and `v`
on `[T, T1]` (an edge at `T`), then `z` holds `u` until `T - 1 + N*lo` and
`v` from `T + N*hi` to `T1 + N*lo`: the edge reaches `z` no earlier than
`N*lo` and no later than `N*hi` after `a`'s, for both polarities.
The `v` interval is non-empty iff `T1 - T ≥ N*(hi - lo)`: the minimum
pulse width for the pulse to be guaranteed at `z` (see `buf_pulse_lost`). -/
theorem sym_edge (s : Nat → Sig) (N lo hi : Nat) (hlh : lo ≤ hi)
    (hg : ∀ i, i < N → Gate BUF [(s i, lo, hi)] (s (i + 1)))
    (u v : Bool) (T0 T T1 : Nat)
    (h1 : StableOn (s 0) u T0 (T - 1)) (h2 : StableOn (s 0) v T T1) :
    StableOn (s N) u (T0 + N * hi) (T - 1 + N * lo) ∧
    StableOn (s N) v (T + N * hi) (T1 + N * lo) :=
  ⟨sym_chain s N lo hi hlh hg u T0 (T - 1) h1 N (Nat.le_refl _),
   sym_chain s N lo hi hlh hg v T T1 h2 N (Nat.le_refl _)⟩

/-- **Counter-trace: a short pulse can be lost.** One buffer stage with
window `[lo, hi]`, input `a` at `u` except on a pulse `[T, T + w - 1]`
with `w ≤ hi - lo` (and `0 < T`): the constant output `u` satisfies the gate relation.
(Physically: a buffer whose edge for the pulse's leading polarity is
slower than the trailing one by more than `w` -- e.g. distinct rise and
fall arcs, 56..152 ps in sim/bd_prims_sim.v -- swallows it.) -/
theorem buf_pulse_lost (a : Sig) (u : Bool) (lo hi T w : Nat) (hlh : lo ≤ hi)
    (hw : w ≤ hi - lo) (hT : 0 < T) (ha : ∀ t, (t < T ∨ T + w ≤ t) → a t = u) :
    Gate BUF [(a, lo, hi)] (fun _ => u) := by
  intro t b h
  show u = b
  have hb : winK a lo hi t = K3.ofBool b := by
    have : lutK BUF [winK a lo hi t] = K3.ofBool b := h
    rwa [buf_k] at this
  have hs : ∃ s, lo ≤ s ∧ s ≤ hi ∧ a (t - s) = u := by
    by_cases hc : t - hi < T
    · exact ⟨hi, hlh, Nat.le_refl _, ha _ (Or.inl hc)⟩
    · exact ⟨lo, Nat.le_refl _, hlh, ha _ (Or.inr (by omega))⟩
  obtain ⟨s, h1, h2, h3⟩ := hs
  have hadm := @win_consistent a lo hi t s h1 h2
  rw [hb, h3] at hadm
  cases u <;> cases b <;> simp_all [K3.admits, K3.ofBool]

/-! ## 5. FASTFALL / FASTRISE lines

`s 0 = a`; stage 0 is `LUT1 #(2'h2)` on `s 0` (window `[lo, hi]`); stage
`i ∈ [1, N)` is `LUT2 #(INIT)` with I0 = `s i` (window `[lo, hi]`) and
I1 = `a` (the side tap, its own window `[tlo, thi]`). INIT = 8 (AND) is
FASTFALL with fast value `c = false`; INIT = E (OR) is FASTRISE with
`c = true`. Everything is proved once for a generic side INIT with the
three Kleene properties, instantiated below. -/

section Fast
variable (s : Nat → Sig) (N lo hi tlo thi : Nat) (init : Nat) (c : Bool)

/-- The structural hypotheses of a FAST line. -/
structure FastLine : Prop where
  hlh : lo ≤ hi
  htlh : tlo ≤ thi
  g0 : Gate BUF [(s 0, lo, hi)] (s 1)
  gi : ∀ i, 1 ≤ i → i < N → Gate init [(s i, lo, hi), (s 0, tlo, thi)] (s (i + 1))
  absorbTap : AbsorbTap init c
  absorbChain : AbsorbChain init c
  pass : Pass init c

/-- **Fast edge.** `N ≥ 2`: `a` at the fast value on `[T, T']` puts `z` at
it on `[T + thi, T' + tlo]` -- one tap hop, whatever the chain is doing. -/
theorem fast_edge (L : FastLine s N lo hi tlo thi init c) (hN : 2 ≤ N)
    (T T' : Nat) (ha : StableOn (s 0) c T T') :
    StableOn (s N) c (T + thi) (T' + tlo) := by
  intro t h1 h2
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact gate_side_tap (L.gi M (by omega) (by omega)) L.absorbTap
    (win_of_stable L.htlh ha (by omega) (by omega))

/-- **Slow edge is not early (the matched direction).** `a` at the fast
value on `[F, T-1]` (it leaves at `T`), and the fast phase long enough to
flush the chain (H_FLUSH: `2*hi + thi ≤ (T - F) + tlo`): every stage
`i ≥ 1` holds the fast value on `[F + hi + thi, T + i*lo - 1]`, so `z`
cannot take the slow value before `T + N*lo`. -/
theorem slow_not_early (L : FastLine s N lo hi tlo thi init c)
    (F T : Nat) (hFT : F < T) (ha : StableOn (s 0) c F (T - 1))
    (H_FLUSH : 2 * hi + thi ≤ (T - F) + tlo) :
    ∀ i, 1 ≤ i → i ≤ N → StableOn (s i) c (F + hi + thi) (T + i * lo - 1) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hiN t h1 h2
    have e2 : (i + 1) * lo = i * lo + lo := by rw [Nat.add_mul, Nat.one_mul]
    by_cases hi0 : i = 0
    · subst hi0
      exact gate_buf L.g0 (win_of_stable L.hlh ha (by omega) (by omega))
    · by_cases ht : t ≤ T - 1 + tlo
      · exact gate_side_tap (L.gi i (by omega) (by omega)) L.absorbTap
          (win_of_stable L.htlh ha (by omega) ht)
      · exact gate_side_chain (L.gi i (by omega) (by omega)) L.absorbChain
          (win_of_stable L.hlh (ih (by omega) (by omega)) (by omega) (by omega))

/-- **Slow edge arrives.** `a` at the slow value on `[T, T']`: stage `i ≥ 1`
holds it on `[T + i*hi + thi, T' + min lo tlo]`. With `slow_not_early`:
the slow edge reaches `z` between `N*lo` and `N*hi + thi` after `a`'s. -/
theorem slow_arrives (L : FastLine s N lo hi tlo thi init c)
    (T T' : Nat) (ha : StableOn (s 0) (!c) T T') :
    ∀ i, 1 ≤ i → i ≤ N → StableOn (s i) (!c) (T + i * hi + thi) (T' + min lo tlo) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hiN t h1 h2
    have e1 : (i + 1) * hi = i * hi + hi := by rw [Nat.add_mul, Nat.one_mul]
    by_cases hi0 : i = 0
    · subst hi0
      exact gate_buf L.g0 (win_of_stable L.hlh ha (by omega) (by omega))
    · exact gate_side_pass (L.gi i (by omega) (by omega)) L.pass
        (win_of_stable L.hlh (ih (by omega) (by omega)) (by omega) (by omega))
        (win_of_stable L.htlh ha (by omega) (by omega))

end Fast

/-- FASTFALL instance: the real `4'h8` side stage has the three properties. -/
theorem fastfall_line (s : Nat → Sig) (N lo hi tlo thi : Nat) (hlh : lo ≤ hi) (htlh : tlo ≤ thi)
    (g0 : Gate BUF [(s 0, lo, hi)] (s 1))
    (gi : ∀ i, 1 ≤ i → i < N → Gate FF_SIDE [(s i, lo, hi), (s 0, tlo, thi)] (s (i + 1))) :
    FastLine s N lo hi tlo thi FF_SIDE false :=
  ⟨hlh, htlh, g0, gi, ff_absorbTap, ff_absorbChain, ff_pass⟩

/-- FASTRISE instance: the real `4'hE` side stage. -/
theorem fastrise_line (s : Nat → Sig) (N lo hi tlo thi : Nat) (hlh : lo ≤ hi) (htlh : tlo ≤ thi)
    (g0 : Gate BUF [(s 0, lo, hi)] (s 1))
    (gi : ∀ i, 1 ≤ i → i < N → Gate FR_SIDE [(s i, lo, hi), (s 0, tlo, thi)] (s (i + 1))) :
    FastLine s N lo hi tlo thi FR_SIDE true :=
  ⟨hlh, htlh, g0, gi, fr_absorbTap, fr_absorbChain, fr_pass⟩

/-! ### Counter-trace: FASTFALL with a short low phase (rule F)

N = 3, every hop `[lo, hi] = [1, 2]`, taps `[tlo, thi] = [1, 2]`. A transport
instance with chain hops of 2 and taps of 1 (both inside the bounds), and
`a` low for ONE tick at 10. Then z = a(t-6) ∧ a(t-3) ∧ a(t-1): it falls at
11 and RISES AGAIN AT 12, one tick after `a` rose at 11 -- the rise skipped
the chain (matched minimum: 11 + 3*1 = 14), and z pulses again later (a
glitch train on a request). H_FLUSH fails (2*2 + 2 ≤ 1 + 1 is false). -/

def ffA : Sig := fun t => decide (t ≠ 10)
def ffS1 : Sig := fun t => ffA (t - 2)
def ffS2 : Sig := fun t => ffS1 (t - 2) && ffA (t - 1)
def ffS3 : Sig := fun t => ffS2 (t - 2) && ffA (t - 1)
def ffS : Nat → Sig
  | 0 => ffA
  | 1 => ffS1
  | 2 => ffS2
  | _ => ffS3

theorem ff_counter :
    FastLine ffS 3 1 2 1 2 FF_SIDE false ∧
    StableOn (ffS 0) false 10 10 ∧ StableOn (ffS 0) true 11 1000 ∧
    ffS 3 12 = true ∧ 12 < 11 + 3 * 1 ∧ ffS 3 13 = false ∧
    ¬ (2 * 2 + 2 ≤ (11 - 10) + 1) := by
  refine ⟨fastfall_line ffS 3 1 2 1 2 (by decide) (by decide) ?_ ?_, ?_, ?_, by decide,
    by decide, by decide, by decide⟩
  · have := transport_gate BUF [(ffA, 2, 1, 2)] ffS1 (by simp)
      (fun t => by show ffA (t - 2) = lutB BUF [ffA (t - 2)]; rw [buf_bin])
    exact this
  · intro i h1 h2
    have hi : i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl
    · exact transport_gate FF_SIDE [(ffS1, 2, 1, 2), (ffA, 1, 1, 2)] ffS2 (by simp)
        (fun t => by
          show (ffS1 (t - 2) && ffA (t - 1)) = lutB FF_SIDE [ffS1 (t - 2), ffA (t - 1)]
          rw [ff_bin])
    · exact transport_gate FF_SIDE [(ffS2, 2, 1, 2), (ffA, 1, 1, 2)] ffS3 (by simp)
        (fun t => by
          show (ffS2 (t - 2) && ffA (t - 1)) = lutB FF_SIDE [ffS2 (t - 2), ffA (t - 1)]
          rw [ff_bin])
  · intro t h1 h2
    have : t = 10 := by omega
    subst this; decide
  · intro t h1 _
    show decide (t ≠ 10) = true
    simp; omega

/-! ### Counter-trace: every stage has fallen before the input rises, and the rise still skips

This is the shape of rule F's check (tighten.py `audit_fastfall`): each
stage's latest fall AT ITS OUTPUT against the earliest time the input can
rise again. Here every stage output is low at `T - 1 = 11` and at `T = 12`
(rule F's premise holds, guard aside), yet `z` rises at 13. The `1` that
stage 1 drove before it fell is still in flight on the 3-tick wire into
stage 2 when the fast tap (1 tick) re-enables stage 2. What the rise needs
is the fall to have reached the NEXT stage's chain pin before the tap's
rise does -- per stage, `fall_i + hop_hi(i → i+1) ≤ T + tap_lo(i+1)`;
H_FLUSH is a uniform sufficient form of it. Bounds: chain `[1, 3]`
(stage 0 hop 1, chain hops 3), taps `[1, 1]`. -/

def fgA : Sig := fun t => decide (t ≠ 10 ∧ t ≠ 11)
def fgS1 : Sig := fun t => fgA (t - 1)
def fgS2 : Sig := fun t => fgS1 (t - 3) && fgA (t - 1)
def fgS3 : Sig := fun t => fgS2 (t - 3) && fgA (t - 1)
def fgS : Nat → Sig
  | 0 => fgA
  | 1 => fgS1
  | 2 => fgS2
  | _ => fgS3

theorem ff_counter_ruleF :
    FastLine fgS 3 1 3 1 1 FF_SIDE false ∧
    StableOn (fgS 0) false 10 11 ∧ StableOn (fgS 0) true 12 1000 ∧
    -- rule F's premise: every stage output already low at 11 and 12
    (∀ i, 1 ≤ i → i ≤ 3 → fgS i 11 = false ∧ fgS i 12 = false) ∧
    -- the rise reaches z one tap hop after a's rise, not N*lo = 3 later
    fgS 3 13 = true ∧ 13 < 12 + 3 * 1 ∧
    ¬ (2 * 3 + 1 ≤ (12 - 10) + 1) := by
  refine ⟨fastfall_line fgS 3 1 3 1 1 (by decide) (by decide) ?_ ?_, ?_, ?_, ?_,
    by decide, by decide, by decide⟩
  · exact transport_gate BUF [(fgA, 1, 1, 3)] fgS1 (by simp)
      (fun t => by show fgA (t - 1) = lutB BUF [fgA (t - 1)]; rw [buf_bin])
  · intro i h1 h2
    have hi : i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl
    · exact transport_gate FF_SIDE [(fgS1, 3, 1, 3), (fgA, 1, 1, 1)] fgS2 (by simp)
        (fun t => by
          show (fgS1 (t - 3) && fgA (t - 1)) = lutB FF_SIDE [fgS1 (t - 3), fgA (t - 1)]
          rw [ff_bin])
    · exact transport_gate FF_SIDE [(fgS2, 3, 1, 3), (fgA, 1, 1, 1)] fgS3 (by simp)
        (fun t => by
          show (fgS2 (t - 3) && fgA (t - 1)) = lutB FF_SIDE [fgS2 (t - 3), fgA (t - 1)]
          rw [ff_bin])
  · intro t h1 h2
    have : t = 10 ∨ t = 11 := by omega
    rcases this with rfl | rfl <;> decide
  · intro t h1 _
    show decide (t ≠ 10 ∧ t ≠ 11) = true
    simp; omega
  · intro i h1 h2
    have : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl <;> decide

/-! ## 6. The latch and the bundling condition (`bd_link`, Muller controller)

One `bd_link` stage: node `c` (the C-element output) drives the latch
enable `en = c`. `d` is the data net as driven by the sender (its latch
output, or a pin), `q` the latch output. Each bit's latch LUT reads
`d` through `[dlo, dhi]`, `en` through `[elo, ehi]` (the enable net's
routed fanout to THIS bit plus the I1 arc), and its own `q` through
`[flo, fhi]` (loop wire plus I2 arc).

The C-element is not modelled here (track 5); its output is taken as a
clean pulse (H_EN_CLEAN): `en` true on `[Ton, Toff)`, false on
`[Toff, Tnext)`. -/

/-- The latch bit relation: the Kleene mux `en ? d : q` over the windows. -/
def LatchRel (d en q : Sig) (dlo dhi elo ehi flo fhi : Nat) : Prop :=
  ∀ t b, K3.mux (winK en elo ehi t) (winK q flo fhi t) (winK d dlo dhi t) = K3.ofBool b → q t = b

def zero : Sig := fun _ => false
def one : Sig := fun _ => true

theorem winK_zero (t : Nat) : winK zero 0 0 t = .f := win_const (b := false) (Nat.le_refl _) (fun _ _ _ => rfl)
theorem winK_one (t : Nat) : winK one 0 0 t = .t := win_const (b := true) (Nat.le_refl _) (fun _ _ _ => rfl)

/-- The odd-bit LUT6 (INIT B8B8..., I3..I5 tied 0) is a `LatchRel`. -/
theorem odd_latch {d en q : Sig} {dlo dhi elo ehi flo fhi : Nat}
    (hg : Gate ODD [(d, dlo, dhi), (en, elo, ehi), (q, flo, fhi),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] q) :
    LatchRel d en q dlo dhi elo ehi flo fhi := by
  intro t b h
  apply hg t b
  show lutK ODD [winK d dlo dhi t, winK en elo ehi t, winK q flo fhi t,
    winK zero 0 0 t, winK zero 0 0 t, winK zero 0 0 t] = _
  rw [winK_zero, odd_kleene, h]

/-- The pair's O5 (bit i; O5 reads the low 32 INIT bits over I0..I4) is a
`LatchRel` for bit i, whatever bit i+1's pins do. -/
theorem pair_o5_latch {d0 en q0 d1 q1 : Sig} {dlo dhi elo ehi flo fhi l3 h3 l4 h4 : Nat}
    (hg : Gate (PAIR % 2 ^ 32) [(d0, dlo, dhi), (en, elo, ehi), (q0, flo, fhi),
      (d1, l3, h3), (q1, l4, h4)] q0) :
    LatchRel d0 en q0 dlo dhi elo ehi flo fhi := by
  intro t b h
  apply hg t b
  show lutK (PAIR % 2 ^ 32) [winK d0 dlo dhi t, winK en elo ehi t, winK q0 flo fhi t,
    winK d1 l3 h3 t, winK q1 l4 h4 t] = _
  rw [pair_o5_kleene, h]

/-- The pair's O6 (bit i+1, I5 tied 1) is a `LatchRel` for bit i+1. -/
theorem pair_o6_latch {d0 en q0 d1 q1 : Sig} {dlo dhi elo ehi flo fhi l0 h0 l2 h2 : Nat}
    (hg : Gate PAIR [(d0, l0, h0), (en, elo, ehi), (q0, l2, h2),
      (d1, dlo, dhi), (q1, flo, fhi), (one, 0, 0)] q1) :
    LatchRel d1 en q1 dlo dhi elo ehi flo fhi := by
  intro t b h
  apply hg t b
  show lutK PAIR [winK d0 l0 h0 t, winK en elo ehi t, winK q0 l2 h2 t,
    winK d1 dlo dhi t, winK q1 flo fhi t, winK one 0 0 t] = _
  rw [winK_one, pair_o6_kleene, h]

theorem mux_same (e : K3) (v : Bool) : K3.mux e (K3.ofBool v) (K3.ofBool v) = K3.ofBool v := by
  cases e <;> cases v <;> rfl

/-- **Capture theorem (the derived bundling condition).**

Hypotheses, all named:
* H_LOOP_POS `1 ≤ flo`: the feedback loop has positive delay.
* `h_on`/`h_off` (H_EN_CLEAN): the node is a clean pulse `[Ton, Toff)`
  followed by low until `Tnext`.
* `h_d`: the sender's data net holds `v` on `[Td, Tnew)`.
* **H_SETUP** `max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo`: the latest
  time the bit's output can still be settling from the enable rise or the
  data change, plus one full loop window, is no later than the EARLIEST
  arrival of the enable FALL. This is the setup side, and it is a condition
  on the enable's fall, not its rise.
* **H_HOLD** `Toff + ehi ≤ Tnew + dlo`: the next value's earliest arrival
  through the data pin is no earlier than the LATEST arrival of the enable
  fall (rule H).

Conclusion: `q = v` from `max (Ton + ehi) (Td + dhi)` until the next
enable rise can reach the bit (`Tnext + elo`). -/
theorem capture (d en q : Sig) (dlo dhi elo ehi flo fhi : Nat)
    (hL : LatchRel d en q dlo dhi elo ehi flo fhi)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff Tnext Td Tnew : Nat) (v : Bool)
    (h_on : ∀ t, Ton ≤ t → t < Toff → en t = true)
    (h_off : ∀ t, Toff ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_SETUP : max (Ton + ehi) (Td + dhi) ≤ Toff + elo)
    (H_HOLD : Toff + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v := by
  -- induction on a bound, so the loop window can use every earlier instant
  suffices H : ∀ n, ∀ t, t < n → max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v
    from fun t h1 h2 => H (t + 1) t (Nat.lt_succ_self t) h1 h2
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t htn h1 h2
    by_cases hA : t < Toff + elo
    · -- transparent, data settled
      have he : winK en elo ehi t = .t :=
        win_eq (b := true) hew (fun u hu1 hu2 => h_on u (by omega) (by omega))
      have hd : winK d dlo dhi t = K3.ofBool v :=
        win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
      exact hL t v (by rw [he, hd]; rfl)
    · -- closing or closed: the loop carries v
      have hq : winK q flo fhi t = K3.ofBool v :=
        win_eq hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      by_cases hB : t < Toff + ehi
      · have hd : winK d dlo dhi t = K3.ofBool v :=
          win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
        exact hL t v (by rw [hq, hd, mux_same])
      · have he : winK en elo ehi t = .f :=
          win_eq (b := false) hew (fun u hu1 hu2 => h_off u (by omega) (by omega))
        exact hL t v (by rw [he, hq]; rfl)

/-- **Request-side form.** Let the sender's node rise at `Tr`; its request
reaches this node through a symmetric `rdly` line and the C-element, so
the node cannot rise before `Tr + Rlo` (H_REQ_LO, e.g. `Rlo = N*lo + clo`
from `sym_edge` and the C-element's req pin) and then stays high at
least `W` (H_EN_WIDTH: the handshake round trip, track 8). Then
* data side: `Td + dhi + fhi ≤ Tr + Rlo + W + elo`, and
* pulse side: `ehi + fhi ≤ W + elo`
together imply H_SETUP. The request is compared with the data only
through the enable FALL, a whole handshake (`W`) after the rise. -/
theorem setup_from_request (Ton Toff Td Tr Rlo W dhi ehi elo fhi : Nat)
    (H_REQ_LO : Tr + Rlo ≤ Ton) (H_EN_WIDTH : Ton + W ≤ Toff)
    (hdata : Td + dhi + fhi ≤ Tr + Rlo + W + elo) (hpulse : ehi + fhi ≤ W + elo) :
    max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo := by
  omega

/-- The classic "data before request" bundling (data out of the LUT no
later than the latest enable-rise arrival, rule A / `input_lead`'s premise)
plus the enable pulse condition implies H_SETUP ... -/
theorem classic_implies_setup (Ton Toff Td dhi ehi elo fhi : Nat)
    (hclassic : Td + dhi ≤ Ton + ehi) (hpulse : Ton + ehi + fhi ≤ Toff + elo) :
    max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo := by
  omega

/-- ... but not conversely: data may arrive after the enable rose. -/
theorem setup_not_classic :
    ∃ Ton Toff Td dhi ehi elo fhi : Nat,
      max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo ∧ ¬ (Td + dhi ≤ Ton + ehi) :=
  ⟨0, 100, 50, 1, 1, 1, 3, by decide, by decide⟩

/-! ### Counter-trace A: the I2-pin arc belongs in the setup side (rule I)

Transport latch (odd LUT6), d-pin arc 1, en-pin arc 1, loop = wire 2 +
I2 arc 1 = 3. Enable high on `[0, 10)`, data rises to 1 at 8 and stays.
Rule I's inequality (no guard): data at D pin + D arc + loop WIRE ≤ enable
fall at pin + en arc, i.e. 8 + 1 + 2 ≤ 10 + 1 -- holds with margin 0.
H_SETUP: 8 + 1 + 3 ≤ 10 + 1 -- fails. The latch closes with `0` still in
the I2 leg and the loop circulates 1,1,0: `q 11 = false`. -/

def caEn : Sig := fun t => decide (t < 10)
def caD : Sig := fun t => decide (8 ≤ t)
def caQ : Sig := fun t =>
  if t ≤ 8 then false else if t ≤ 10 then true else decide ((t - 8) % 3 ≠ 0)

theorem caQ_transport : Transport ODD [(caD, 1), (caEn, 1), (caQ, 3),
    (zero, 0), (zero, 0), (zero, 0)] caQ := by
  intro t
  show caQ t = lutB ODD [caD (t - 1), caEn (t - 1), caQ (t - 3), false, false, false]
  rw [odd_bin]
  by_cases ht : t < 14
  · revert t; decide
  · have hen : caEn (t - 1) = false := by simp [caEn]; omega
    rw [hen]
    have a1 : ¬ t ≤ 8 := by omega
    have a2 : ¬ t ≤ 10 := by omega
    have a3 : ¬ t - 3 ≤ 8 := by omega
    have a4 : ¬ t - 3 ≤ 10 := by omega
    simp only [caQ, Bool.false_eq_true, a1, a2, a3, a4, ↓reduceIte]
    have : t - 8 = (t - 3 - 8) + 3 := by omega
    rw [this, Nat.add_mod_right]

theorem counter_rule_I :
    LatchRel caD caEn caQ 1 1 1 1 3 3 ∧
    (∀ t, 0 ≤ t → t < 10 → caEn t = true) ∧ (∀ t, 10 ≤ t → t < 1000 → caEn t = false) ∧
    (∀ t, 8 ≤ t → t < 1000 → caD t = true) ∧
    -- rule I's form holds (margin 0), H_SETUP fails, H_HOLD holds
    (8 + 1 + 2 ≤ 10 + 1) ∧ ¬ (max (0 + 1) (8 + 1) + 3 ≤ 10 + 1) ∧ (10 + 1 ≤ 1000 + 1) ∧
    caQ 11 = false := by
  refine ⟨odd_latch (transport_gate ODD [(caD, 1, 1, 1), (caEn, 1, 1, 1), (caQ, 3, 3, 3),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] caQ (by simp) caQ_transport),
    ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · intro t _ h; simp [caEn]; omega
  · intro t h _; simp [caEn]; omega
  · intro t h _; simp [caD]; omega

/-! ### Counter-trace B: hold violation (rule H)

Data pin arc 0, enable arc 2, loop 1. Enable high on `[0, 10)`, data `1`
on `[5, 10)` and released (0) at 10 -- the moment the node falls, which
the protocol allows of a sender that sees ack fall with the node.
H_HOLD: 10 + 2 ≤ 10 + 0 fails; the latch still transparent at 11 takes
the released value: `q` is 0 from 10 on, the token is lost. -/

def cbEn : Sig := fun t => decide (t < 10)
def cbD : Sig := fun t => decide (5 ≤ t ∧ t < 10)
def cbQ : Sig := fun t => decide (5 ≤ t ∧ t < 10)

theorem cbQ_transport : Transport ODD [(cbD, 0), (cbEn, 2), (cbQ, 1),
    (zero, 0), (zero, 0), (zero, 0)] cbQ := by
  intro t
  show cbQ t = lutB ODD [cbD (t - 0), cbEn (t - 2), cbQ (t - 1), false, false, false]
  rw [odd_bin]
  by_cases ht : t < 14
  · revert t; decide
  · have hen : cbEn (t - 2) = false := by simp [cbEn]; omega
    rw [hen]
    have b1 : ¬ t < 10 := by omega
    have b2 : ¬ t - 1 < 10 := by omega
    simp only [cbQ, Bool.false_eq_true, ↓reduceIte, b1, b2, and_false]

theorem counter_rule_H :
    LatchRel cbD cbEn cbQ 0 0 2 2 1 1 ∧
    (∀ t, 5 ≤ t → t < 10 → cbD t = true) ∧
    max (0 + 2) (5 + 0) + 1 ≤ 10 + 2 ∧ ¬ (10 + 2 ≤ 10 + 0) ∧
    cbQ 12 = false := by
  refine ⟨odd_latch (transport_gate ODD [(cbD, 0, 0, 0), (cbEn, 2, 2, 2), (cbQ, 1, 1, 1),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] cbQ (by simp) cbQ_transport),
    ?_, by decide, by decide, by decide⟩
  intro t h1 h2; simp [cbD]; omega

end Formal.Cells.Bundling
