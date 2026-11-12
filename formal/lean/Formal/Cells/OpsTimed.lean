import Formal.Cells.PipeTimed
import Formal.Cells.LibCtlMergeMux

/-!
# Shard B Phase 2, probe Lt: timed handshake proofs for the dataflow operators (part 1)

Part 1: the token-trace vocabulary shared by `bd_steer`, `bd_mux` and
`bd_merge`, and the timed theorem for **`bd_steer`** (Dynamatic's branch).
Part 2 (`OpsTimedMux.lean`) does `bd_mux` and `bd_merge`.

Style: probe 6e/6f (`PipeTimed`, `PipeTimedN`). Every LUT and every wire is a
FIFO bounded-delay channel (`PipeTimed.Ret`, hypothesis **H_LUT_FIFO** /
**H_WIRE_FIFO**: the output at `t` shows the input at a read time
`σ t ∈ [t - hi, t - lo]`, `σ` nondecreasing). The LUT's input is the Boolean
function of its pins given by its REAL INIT through `Prelim.lutB` (here
`LibCtlMergeMux.req0B/req1B/or2B`, i.e. `o5B/o6B/lutB` of the RTL constants).
The environment's event times are free parameters; the cell's event times are
DEFINED from them through the channels' `Ret.fst` (first instant an edge
reaches the far end); the environment's causality is stated against those
derived times, as in 6e's `Env2`.

## `Tok`: a token-indexed four-phase trace

`Tok T x e g` says: from time `T` on, `x` is low before `e 0`; on
`[e (2k), e (2k+1))` it shows the gate `g k`; on `[e (2k+1), e (2k+2))` it is
low. A clean four-phase request is `Tok T x e (fun _ => true)`. A branch
request of a steer is `Tok T x e g` with `g k` = "token `k` is routed here":
in a token not routed here the wire stays low for the whole slot. Nothing in
`Tok` forces `e` to be monotone; the cell theorems carry the monotonicity
they need as named hypotheses or derive it.
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace lfind lfind_le lfind_spec lfind_min Vph)
open Formal.Cells.LibCtlMergeMux (req0B req1B or2B steer_req0 steer_req1 or2_spec)

/-! ## 1. Token traces -/

/-- A token-indexed four-phase trace with gates (see the module doc). -/
structure Tok (T : Nat) (x : Trace) (e : Nat → Nat) (g : Nat → Bool) : Prop where
  pre : ∀ t, T ≤ t → t < e 0 → x t = false
  hi : ∀ k t, T ≤ t → e (2 * k) ≤ t → t < e (2 * k + 1) → x t = g k
  lo : ∀ k t, T ≤ t → e (2 * k + 1) ≤ t → t < e (2 * k + 2) → x t = false

namespace Tok
variable {T : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool}

theorem mono (h : Tok T x e g) {T' : Nat} (hT : T ≤ T') : Tok T' x e g :=
  ⟨fun t h1 => h.pre t (by omega), fun k t h1 => h.hi k t (by omega),
    fun k t h1 => h.lo k t (by omega)⟩

theorem congr (h : Tok T x e g) {e' : Nat → Nat} (he : ∀ j, e j = e' j) : Tok T x e' g :=
  ⟨fun t h1 h2 => h.pre t h1 (by rw [he]; exact h2),
    fun k t h1 h2 h3 => h.hi k t h1 (by rw [he]; exact h2) (by rw [he]; exact h3),
    fun k t h1 h2 h3 => h.lo k t h1 (by rw [he]; exact h2) (by rw [he]; exact h3)⟩

theorem trace_congr (h : Tok T x e g) {y : Trace} (hy : ∀ t, T ≤ t → y t = x t) : Tok T y e g :=
  ⟨fun t h1 h2 => by rw [hy t h1]; exact h.pre t h1 h2,
    fun k t h1 h2 h3 => by rw [hy t h1]; exact h.hi k t h1 h2 h3,
    fun k t h1 h2 h3 => by rw [hy t h1]; exact h.lo k t h1 h2 h3⟩

/-- **FIFO transfer.** Through a FIFO channel a token trace stays a token
trace, with every edge moved to `r.fst` of itself; gates are unchanged. -/
theorem fifo (r : Ret) {y : Trace} (hy : ∀ t, r.hi ≤ t → y t = x (r.σ t)) (h : Tok T x e g) :
    Tok (T + r.hi) y (fun j => r.fst (e j)) g := by
  refine ⟨fun t h1 h2 => ?_, fun k t h1 h2 h3 => ?_, fun k t h1 h2 h3 => ?_⟩
  · have := r.ge t
    rw [hy t (by omega)]; exact h.pre _ (by omega) (r.fst_before h2)
  · have := r.ge t
    rw [hy t (by omega)]; exact h.hi k _ (by omega) (r.fst_after h2) (r.fst_before h3)
  · have := r.ge t
    rw [hy t (by omega)]; exact h.lo k _ (by omega) (r.fst_after h2) (r.fst_before h3)

/-- **A gated function of a token trace and a bundled bit.** If `f false _ =
false` and the bit `s` holds the token's value `sv k` while the request is
high, then `f (x t) (s t)` is a token trace with gate `f true (sv k)`. This is
the steer's two AND outputs and the mux's control decode. -/
theorem gate (h : Tok T x e (fun _ => true)) (f : Bool → Bool → Bool)
    (hf : ∀ b, f false b = false) {s : Trace} {sv : Nat → Bool}
    (hs : ∀ k t, T ≤ t → e (2 * k) ≤ t → t < e (2 * k + 1) → s t = sv k) :
    Tok T (fun t => f (x t) (s t)) e (fun k => f true (sv k)) := by
  refine ⟨fun t h1 h2 => ?_, fun k t h1 h2 h3 => ?_, fun k t h1 h2 h3 => ?_⟩
  · show f (x t) (s t) = false; rw [h.pre t h1 h2, hf]
  · show f (x t) (s t) = f true (sv k); rw [h.hi k t h1 h2 h3, hs k t h1 h2 h3]
  · show f (x t) (s t) = false; rw [h.lo k t h1 h2 h3, hf]

/-- Value of a token trace in phase `j` (even = high slot, odd = low slot). -/
theorem at_phase (h : Tok T x e g) (j t : Nat) (hT : T ≤ t) (h1 : e j ≤ t) (h2 : t < e (j + 1)) :
    x t = (Vph j && g (j / 2)) := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have ej : j = 2 * (j / 2) := by omega
    have hv : Vph j = true := by show decide (j % 2 = 0) = true; simp [hj]
    rw [hv, Bool.true_and]
    exact h.hi (j / 2) t hT (by rw [← ej]; exact h1) (by rw [show 2 * (j / 2) + 1 = j + 1 by omega]; exact h2)
  · have hv : Vph j = false := by show decide (j % 2 = 0) = false; simp [hj]
    rw [hv, Bool.false_and]
    exact h.lo (j / 2) t hT (by rw [show 2 * (j / 2) + 1 = j by omega]; exact h1)
      (by rw [show 2 * (j / 2) + 2 = j + 1 by omega]; exact h2)

/-- A slot is low if it is an odd (return-to-zero) slot or its gate is off. -/
def SlotLow (g : Nat → Bool) (j : Nat) : Prop := j % 2 = 1 ∨ g (j / 2) = false

theorem slotLow_odd (g : Nat → Bool) (k : Nat) : SlotLow g (2 * k + 1) := Or.inl (by omega)
theorem slotLow_even {g : Nat → Bool} {k : Nat} (h : g k = false) : SlotLow g (2 * k) :=
  Or.inr (by rw [show 2 * k / 2 = k by omega]; exact h)
theorem slotLow_even2 {g : Nat → Bool} {k : Nat} (h : g (k + 1) = false) : SlotLow g (2 * k + 2) :=
  Or.inr (by rw [show (2 * k + 2) / 2 = k + 1 by omega]; exact h)

theorem low_slot (h : Tok T x e g) (j t : Nat) (hj : SlotLow g j) (hT : T ≤ t) (h1 : e j ≤ t)
    (h2 : t < e (j + 1)) : x t = false := by
  rw [h.at_phase j t hT h1 h2]
  rcases hj with hj | hj
  · have : Vph j = false := by show decide (j % 2 = 0) = false; simp [hj]
    rw [this]; rfl
  · rw [hj]; cases Vph j <;> rfl

/-- Low across a run of low slots `[e a, e b)`. -/
theorem low_range (h : Tok T x e g) : ∀ b a t, a ≤ b → (∀ j, a ≤ j → j < b → SlotLow g j) →
    T ≤ t → e a ≤ t → t < e b → x t = false := by
  intro b
  induction b with
  | zero => intro a t hab _ _ h1 h2; have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    intro a t hab hs hT h1 h2
    by_cases hb : t < e b
    · by_cases ha : a ≤ b
      · exact ih a t ha (fun j h3 h4 => hs j h3 (by omega)) hT h1 hb
      · have : a = b + 1 := by omega
        subst this; omega
    · exact h.low_slot b t (hs b (by
        by_cases ha : a ≤ b
        · exact ha
        · have : a = b + 1 := by omega
          subst this; omega) (by omega)) hT (by omega) h2

/-- Low from `T` up to `e b` when every slot below `b` is low. -/
theorem low_pre (h : Tok T x e g) : ∀ b t, (∀ j, j < b → SlotLow g j) →
    T ≤ t → t < e b → x t = false := by
  intro b
  induction b with
  | zero => intro t _ hT h2; exact h.pre t hT h2
  | succ b ih =>
    intro t hs hT h2
    by_cases hb : t < e b
    · exact ih t (fun j hj => hs j (by omega)) hT hb
    · exact h.low_slot b t (hs b (by omega)) hT (by omega) h2

end Tok

/-! ## 2. OR of two exclusive token traces (`LUT2 E`: the steer's `uack`,
the mux's and merge's `uor`) -/

/-- Edges of the OR: the selected input's. -/
def orEdges (g : Nat → Bool) (e e' : Nat → Nat) (j : Nat) : Nat := if g (j / 2) then e j else e' j

/-- **OR of exclusive token traces.** `x` carries the tokens with `g k`, `y`
the others, over their own edge sequences `e`, `e'`. If each sequence's edge
precedes the other's next edge (`hs1`, `hs2`, the skew condition between the
two OR pins: **H_OR_SKEW**), the OR is a clean four-phase trace with one
pulse per token, on the selected input's edges. -/
theorem or_tok {T : Nat} {x y : Trace} {e e' : Nat → Nat} {g : Nat → Bool}
    (hx : Tok T x e g) (hy : Tok T y e' (fun k => !g k))
    (hs1 : ∀ j, e j ≤ e' (j + 1)) (hs2 : ∀ j, e' j ≤ e (j + 1)) :
    Tok T (fun t => x t || y t) (orEdges g e e') (fun _ => true) := by
  have d0 : (0 : Nat) / 2 = 0 := rfl
  have dk : ∀ k, 2 * k / 2 = k := fun k => by omega
  have dk1 : ∀ k, (2 * k + 1) / 2 = k := fun k => by omega
  have dk2 : ∀ k, (2 * k + 2) / 2 = k + 1 := fun k => by omega
  refine ⟨fun t hT h2 => ?_, fun k t hT h1 h2 => ?_, fun k t hT h1 h2 => ?_⟩
  · cases hg : g 0
    · have h2' : t < e' 0 := by simpa [orEdges, hg] using h2
      have h3 : e' 0 ≤ e 1 := hs2 0
      have a1 : x t = false := hx.low_pre 1 t (fun j hj => by
        have : j = 0 := by omega
        subst this; exact Tok.slotLow_even (k := 0) hg) hT (by omega)
      have a2 : y t = false := hy.pre t hT h2'
      simp [a1, a2]
    · have h2' : t < e 0 := by simpa [orEdges, hg] using h2
      have h3 : e 0 ≤ e' 1 := hs1 0
      have a1 : x t = false := hx.pre t hT h2'
      have a2 : y t = false := hy.low_pre 1 t (fun j hj => by
        have : j = 0 := by omega
        subst this; exact Tok.slotLow_even (k := 0) (g := fun k => !g k) (by simp [hg])) hT
        (by omega)
      simp [a1, a2]
  · cases hg : g k
    · have h1' : e' (2 * k) ≤ t := by simpa [orEdges, dk, hg] using h1
      have h2' : t < e' (2 * k + 1) := by simpa [orEdges, dk1, hg] using h2
      have := hy.hi k t hT h1' h2'; simp [hg] at this; simp [this]
    · have h1' : e (2 * k) ≤ t := by simpa [orEdges, dk, hg] using h1
      have h2' : t < e (2 * k + 1) := by simpa [orEdges, dk1, hg] using h2
      have := hx.hi k t hT h1' h2'; simp [hg] at this; simp [this]
  · have s1 : e (2 * k) ≤ e' (2 * k + 1) := hs1 (2 * k)
    have s2 : e' (2 * k) ≤ e (2 * k + 1) := hs2 (2 * k)
    have s3 : e (2 * k + 2) ≤ e' (2 * k + 3) := hs1 (2 * k + 2)
    have s4 : e' (2 * k + 2) ≤ e (2 * k + 3) := hs2 (2 * k + 2)
    have s5 : e (2 * k + 1) ≤ e' (2 * k + 2) := hs1 (2 * k + 1)
    have s6 : e' (2 * k + 1) ≤ e (2 * k + 2) := hs2 (2 * k + 1)
    cases hg : g k <;> cases hg' : g (k + 1)
    · have h1 : e' (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e' (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      -- y, y
      have a2 := hy.lo k t hT h1 h2
      have a1 := hx.low_range (2 * k + 3) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r | r <;> subst r
        · exact Tok.slotLow_even hg
        · exact Tok.slotLow_odd _ k
        · exact Tok.slotLow_even2 hg') hT (by omega) (by omega)
      simp [a1, a2]
    · have h1 : e' (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      -- y, then x
      have a1 := hx.low_range (2 * k + 2) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 by omega) with r | r <;> subst r
        · exact Tok.slotLow_even hg
        · exact Tok.slotLow_odd _ k) hT (by omega) h2
      have a2 := hy.low_range (2 * k + 3) (2 * k + 1) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r <;> subst r
        · exact Tok.slotLow_odd _ k
        · exact Tok.slotLow_even2 (g := fun k => !g k) (by simp [hg'])) hT h1 (by omega)
      simp [a1, a2]
    · have h1 : e (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e' (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      -- x, then y
      have a1 := hx.low_range (2 * k + 3) (2 * k + 1) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r <;> subst r
        · exact Tok.slotLow_odd _ k
        · exact Tok.slotLow_even2 hg') hT h1 (by omega)
      have a2 := hy.low_range (2 * k + 2) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 by omega) with r | r <;> subst r
        · exact Tok.slotLow_even (g := fun k => !g k) (by simp [hg])
        · exact Tok.slotLow_odd _ k) hT (by omega) h2
      simp [a1, a2]
    · have h1 : e (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      -- x, x
      have a1 := hx.lo k t hT h1 h2
      have a2 := hy.low_range (2 * k + 3) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r | r <;> subst r
        · exact Tok.slotLow_even (g := fun k => !g k) (by simp [hg])
        · exact Tok.slotLow_odd _ k
        · exact Tok.slotLow_even2 (g := fun k => !g k) (by simp [hg'])) hT (by omega) (by omega)
      simp [a1, a2]

/-! ## 3. Small facts about `Ret.fst` -/

theorem fst_mono (r : Ret) {a b : Nat} (h : a ≤ b) : r.fst a ≤ r.fst b := by
  apply Classical.byContradiction; intro hn
  have h1 := r.fst_before (c := a) (t := r.fst b) (by omega)
  have h2 := r.fst_spec b
  omega

/-- A sufficient static form of an edge-order condition between two channels
fed by one edge sequence: `e j + r.hi ≤ e (j+1) + r'.lo` gives
`r.fst (e j) ≤ r'.fst (e (j+1))`. -/
theorem fst_order (r r' : Ret) {a b : Nat} (hb : 1 ≤ b) (h : a + r.hi ≤ b + r'.lo) :
    r.fst a ≤ r'.fst b := by
  have := r.fst_le a; have := r'.fst_lo hb; omega

/-! ## 4. `bd_steer` (Dynamatic's branch)

`cells/rtl/bd_ctl.v`:

    LUT6_2 #(.INIT(64'h8888_8888_2222_2222)) u (.I0(req), .I1(s), .I2(0), .I3(0), .I4(0), .I5(1),
                                                  .O5(req0), .O6(req1));
    LUT2   #(.INIT(4'hE))                    uack (.I0(ack0), .I1(ack1), .O(ack));

Signals (all `Trace`s): `req` at the sender's port; `rqu`, `su` at `u.I0`,
`u.I1`; `o5`, `o6` at `u.O5`, `u.O6`; `r0`, `r1` at the two receivers' request
pins; `a0`, `a1` at the receivers' acknowledge ports; `a0u`, `a1u` at
`uack.I0/I1`; `ao` at `uack.O`; `ack` at the sender's acknowledge pin.

Branch 0 is the `s = 0` branch (`req0 = req·~s`), branch 1 the `s = 1` branch;
token `k`'s condition is `sv k`. -/

/-- Delay realisation of one run of a steer, plus the environment's event
times. -/
structure SteerRun where
  /-- wire `req` → `u.I0` -/
  Wq : Ret
  /-- `u` LUT arc to `O5` (req0) and to `O6` (req1): one LUT6_2, two outputs -/
  L5 : Ret
  L6 : Ret
  /-- wires `u.O5` → receiver 0, `u.O6` → receiver 1 -/
  W0 : Ret
  W1 : Ret
  /-- wires receiver acks → `uack.I0`, `uack.I1` -/
  Wa0 : Ret
  Wa1 : Ret
  /-- `uack` LUT2 arc -/
  La : Ret
  /-- wire `uack.O` → sender -/
  Wk : Ret
  /-- sender's request edges at its port (`ρ (2k)` rise, `ρ (2k+1)` fall of token `k`) -/
  ρ : Nat → Nat
  /-- the routed branch's acknowledge edges at its port (common sequence: the
  unrouted branch's acknowledge is low for the whole slot) -/
  A : Nat → Nat
  /-- token `k`'s condition (`s`) -/
  sv : Nat → Bool

namespace SteerRun
variable (P : SteerRun)

/-- `req` at `u.I0`. -/
def qr (j : Nat) : Nat := P.Wq.fst (P.ρ j)
/-- `req0` / `req1` at the receivers' pins. -/
def R0 (j : Nat) : Nat := P.W0.fst (P.L5.fst (P.qr j))
def R1 (j : Nat) : Nat := P.W1.fst (P.L6.fst (P.qr j))
/-- The routed branch's request edges. -/
def Rsel (j : Nat) : Nat := if P.sv (j / 2) then P.R1 j else P.R0 j
/-- The acknowledges at `uack`'s pins (the routed one's). -/
def au (j : Nat) : Nat := orEdges (fun k => !P.sv k) (fun j => P.Wa0.fst (P.A j)) (fun j => P.Wa1.fst (P.A j)) j
/-- `ack` at the sender's pin. -/
def K (j : Nat) : Nat := P.Wk.fst (P.La.fst (P.au j))

/-- Start of the clean window of the forward paths and of the back path. -/
def T1 (Tr : Nat) : Nat := Tr + P.Wq.hi + (P.L5.hi + P.L6.hi) + (P.W0.hi + P.W1.hi)
def T2 (Ta : Nat) : Nat := Ta + (P.Wa0.hi + P.Wa1.hi) + P.La.hi + P.Wk.hi

end SteerRun

/-- **The steer's gate relations.** One field per primitive; each is a
named fabric hypothesis. -/
structure SteerGates (P : SteerRun) (req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack : Trace) : Prop where
  /-- **H_WIRE_FIFO** (req → u.I0). -/
  H_WQ : ∀ t, P.Wq.hi ≤ t → rqu t = req (P.Wq.σ t)
  /-- **H_LUT_FIFO** for `u.O5`: the lower LUT5 of the REAL INIT
  `0x8888888822222222`, pins `[req, s, 0, 0, 0, 1]` (`req0B`), read through a
  FIFO arc. -/
  H_U5 : ∀ t, P.L5.hi ≤ t → o5 t = req0B (rqu (P.L5.σ t)) (su (P.L5.σ t))
  /-- **H_LUT_FIFO** for `u.O6` (`req1B`, full INIT, I5 = 1). -/
  H_U6 : ∀ t, P.L6.hi ≤ t → o6 t = req1B (rqu (P.L6.σ t)) (su (P.L6.σ t))
  /-- **H_WIRE_FIFO** (`u.O5` → receiver 0, `u.O6` → receiver 1). -/
  H_W0 : ∀ t, P.W0.hi ≤ t → r0 t = o5 (P.W0.σ t)
  H_W1 : ∀ t, P.W1.hi ≤ t → r1 t = o6 (P.W1.σ t)
  /-- **H_WIRE_FIFO** (receiver acks → `uack`). -/
  H_WA0 : ∀ t, P.Wa0.hi ≤ t → a0u t = a0 (P.Wa0.σ t)
  H_WA1 : ∀ t, P.Wa1.hi ≤ t → a1u t = a1 (P.Wa1.σ t)
  /-- **H_LUT_FIFO** for `uack` (REAL INIT `4'hE`, `or2B`). -/
  H_UA : ∀ t, P.La.hi ≤ t → ao t = or2B (a0u (P.La.σ t)) (a1u (P.La.σ t))
  /-- **H_WIRE_FIFO** (`uack.O` → sender). -/
  H_WK : ∀ t, P.Wk.hi ≤ t → ack t = ao (P.Wk.σ t)

/-- **The steer's environment and its timing obligations.** -/
structure SteerEnv (P : SteerRun) (req su a0 a1 : Trace) (Tr Ta Er Es : Nat) : Prop where
  /-- **H_SND_CLEAN**: the sender's request is a clean four-phase trace from `Tr`. -/
  H_REQ : Tok Tr req P.ρ (fun _ => true)
  /-- **H_BUNDLED_S_PIN** (steer form): at `u.I1`, `s` shows token `k`'s
  condition for as long as `req` is high at `u.I0`. Static sufficient form:
  `steer_s_pin_of_wire`. JSON: no `bd_steer` entry (reported missing); the
  mux's `bd_mux.bundled_s_setup` / `bundled_s_hold` are the analogue. -/
  H_S_PIN : ∀ k t, P.qr (2 * k) ≤ t → t < P.qr (2 * k + 1) → su t = P.sv k
  /-- **H_RCV_QUIET**: each receiver acknowledges only tokens routed to it;
  the routed one's acknowledge is a four-phase trace on the common edges
  `A`, clean from `Ta`. (A four-phase receiver whose request stays low does
  not move its acknowledge: this is the receiver's own protocol.) -/
  H_A0 : Tok Ta a0 P.A (fun k => !P.sv k)
  H_A1 : Tok Ta a1 P.A P.sv
  /-- **H_RCV_CAUSAL**: the routed receiver's acknowledge edge comes at least
  `Er` after it saw the matching request edge. -/
  H_RCV : ∀ j, P.Rsel j + Er ≤ P.A j
  /-- **H_SND_CAUSAL**: the sender's next request edge comes at least `Es`
  after it saw the acknowledge edge. -/
  H_SND : ∀ j, P.K j + Es ≤ P.ρ (j + 1)
  /-- **H_ACK_SKEW** (event form): at `uack`, each acknowledge pin's edge
  precedes the other pin's next edge. Static sufficient form:
  `A j + Wa0.hi ≤ A (j+1) + Wa1.lo` and symmetrically (`fst_order`); the gap
  `A (j+1) - A j` is a whole round trip through the sender
  (`steer_gap`). JSON: no entry (reported missing). -/
  H_ACK_SKEW : ∀ j, P.Wa0.fst (P.A j) ≤ P.Wa1.fst (P.A (j + 1)) ∧
    P.Wa1.fst (P.A j) ≤ P.Wa0.fst (P.A (j + 1))

section steer
variable {P : SteerRun} {req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack : Trace}
  {Tr Ta Er Es : Nat}

/-- **`bd_steer`, forward half: each token goes to the branch its condition
names, and only there.** Receiver 0's request pin shows a pulse exactly for
the tokens with `sv k = false`, receiver 1's exactly for `sv k = true`; in
every other slot the pin is low for the whole slot. Only the request path
and the `s` bundling are used. -/
theorem steer_fwd (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hreq : Tok Tr req P.ρ (fun _ => true))
    (hs : ∀ k t, P.qr (2 * k) ≤ t → t < P.qr (2 * k + 1) → su t = P.sv k) :
    Tok (P.T1 Tr) r0 P.R0 (fun k => !P.sv k) ∧ Tok (P.T1 Tr) r1 P.R1 P.sv := by
  have hq := hreq.fifo P.Wq G.H_WQ
  have g0 := hq.gate (fun a b => a && !b) (fun _ => rfl) (s := su) (sv := P.sv)
    (fun k t _ h1 h2 => hs k t h1 h2)
  have g1 := hq.gate (fun a b => a && b) (fun _ => rfl) (s := su) (sv := P.sv)
    (fun k t _ h1 h2 => hs k t h1 h2)
  have o5t := g0.fifo P.L5 (y := o5) (fun t ht => by rw [G.H_U5 t ht, steer_req0])
  have o6t := g1.fifo P.L6 (y := o6) (fun t ht => by rw [G.H_U6 t ht, steer_req1])
  have r0t := o5t.fifo P.W0 G.H_W0
  have r1t := o6t.fifo P.W1 G.H_W1
  constructor
  · exact r0t.mono (T' := P.T1 Tr) (by unfold SteerRun.T1; omega)
  · exact r1t.mono (T' := P.T1 Tr) (by unfold SteerRun.T1; omega)

/-- **`bd_steer`, backward half: one acknowledge per token.** The sender's
acknowledge pin is a clean four-phase trace on `K`, the routed receiver's
acknowledge edges moved through `uack`. -/
theorem steer_back (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (h0 : Tok Ta a0 P.A (fun k => !P.sv k)) (h1 : Tok Ta a1 P.A P.sv)
    (hsk : ∀ j, P.Wa0.fst (P.A j) ≤ P.Wa1.fst (P.A (j + 1)) ∧
      P.Wa1.fst (P.A j) ≤ P.Wa0.fst (P.A (j + 1))) :
    Tok (P.T2 Ta) ack P.K (fun _ => true) := by
  have p0 := (h0.fifo P.Wa0 G.H_WA0).mono (T' := Ta + (P.Wa0.hi + P.Wa1.hi)) (by omega)
  have p1 := (h1.fifo P.Wa1 G.H_WA1).mono (T' := Ta + (P.Wa0.hi + P.Wa1.hi)) (by omega)
  have p1' : Tok (Ta + (P.Wa0.hi + P.Wa1.hi)) a1u (fun j => P.Wa1.fst (P.A j))
      (fun k => !(!P.sv k)) := by simpa using p1
  have o := or_tok p0 p1' (fun j => (hsk j).1) (fun j => (hsk j).2)
  have ot := o.fifo P.La (y := ao) (fun t ht => by rw [G.H_UA t ht, or2_spec])
  exact (ot.fifo P.Wk G.H_WK).congr (fun j => rfl)

/-- **`steer_ok`: the steer meets its handshake spec for every token.**
(1) token `k` reaches exactly the branch named by `sv k` (one pulse there,
none on the other branch for that whole slot); (2) the sender sees exactly
one acknowledge pulse per token; (3) the order of a four-phase cell: each
request edge at the routed receiver follows the sender's edge, and each
acknowledge edge at the sender follows the routed receiver's acknowledge
edge, which follows its request edge by `Er`. -/
theorem steer_ok (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (E : SteerEnv P req su a0 a1 Tr Ta Er Es) :
    Tok (P.T1 Tr) r0 P.R0 (fun k => !P.sv k) ∧ Tok (P.T1 Tr) r1 P.R1 P.sv ∧
    Tok (P.T2 Ta) ack P.K (fun _ => true) ∧
    (∀ j, P.ρ j ≤ P.Rsel j ∧ P.Rsel j + Er ≤ P.A j ∧ P.A j ≤ P.K j ∧ P.K j + Es ≤ P.ρ (j + 1)) := by
  obtain ⟨f0, f1⟩ := steer_fwd G E.H_REQ E.H_S_PIN
  refine ⟨f0, f1, steer_back G E.H_A0 E.H_A1 E.H_ACK_SKEW, fun j => ⟨?_, E.H_RCV j, ?_, E.H_SND j⟩⟩
  · have a := P.Wq.fst_ge (P.ρ j)
    unfold SteerRun.Rsel SteerRun.R0 SteerRun.R1 SteerRun.qr
    have b5 := P.L5.fst_ge (P.Wq.fst (P.ρ j)); have b6 := P.L6.fst_ge (P.Wq.fst (P.ρ j))
    have c0 := P.W0.fst_ge (P.L5.fst (P.Wq.fst (P.ρ j)))
    have c1 := P.W1.fst_ge (P.L6.fst (P.Wq.fst (P.ρ j)))
    split <;> omega
  · unfold SteerRun.K SteerRun.au orEdges
    dsimp only
    have := P.Wa0.fst_ge (P.A j); have := P.Wa1.fst_ge (P.A j)
    split
    · have := P.La.fst_ge (P.Wa0.fst (P.A j)); have := P.Wk.fst_ge (P.La.fst (P.Wa0.fst (P.A j)))
      omega
    · have := P.La.fst_ge (P.Wa1.fst (P.A j)); have := P.Wk.fst_ge (P.La.fst (P.Wa1.fst (P.A j)))
      omega

/-- **Static form of H_BUNDLED_S_PIN.** If the sender holds `s = sv k` at its
port on `[sS k, sE k)`, the `s` wire is FIFO `Ws`, and
`sS k + Ws.hi ≤ ρ (2k) + Wq.lo` (setup: `s` launched no later than `req`,
less the wire skew) and `ρ (2k+1) + Wq.hi ≤ sE k + Ws.lo` (hold: `s` held
until `req`'s fall has crossed its wire, plus the skew), then the pin
hypothesis holds. (`ρ (2k) ≥ 1` only avoids the truncated-subtraction corner
at time 0.) -/
theorem steer_s_pin_of_wire (Ws : Ret) {s : Trace} (sS sE : Nat → Nat)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hhold : ∀ k t, sS k ≤ t → t < sE k → s t = P.sv k)
    (hpos : ∀ k, 1 ≤ P.ρ (2 * k))
    (hsu : ∀ k, sS k + Ws.hi ≤ P.ρ (2 * k) + P.Wq.lo)
    (hhd : ∀ k, P.ρ (2 * k + 1) + P.Wq.hi ≤ sE k + Ws.lo) :
    ∀ k t, P.qr (2 * k) ≤ t → t < P.qr (2 * k + 1) → su t = P.sv k := by
  intro k t h1 h2
  unfold SteerRun.qr at h1 h2
  have a1 := P.Wq.fst_lo (hpos k); have a2 := P.Wq.fst_le (P.ρ (2 * k + 1))
  have b1 := Ws.ge t; have b2 := Ws.le t; have b3 := Ws.lo_le_hi
  have := hsu k; have := hhd k
  rw [hw t (by omega)]
  exact hhold k _ (by omega) (by omega)

/-- **The round trip behind H_ACK_SKEW.** Under the causality hypotheses,
consecutive acknowledge edges are a whole sender round trip apart, so the
skew obligation reduces to the static
`Wa_b.hi ≤ Wa_b'.lo + Loop` with
`Loop = min(Wa0.lo, Wa1.lo) + La.lo + Wk.lo + Es + Wq.lo + min(L5.lo + W0.lo, L6.lo + W1.lo) + Er`. -/
theorem steer_gap (E : SteerEnv P req su a0 a1 Tr Ta Er Es) (Lm Wm : Nat)
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (hA : ∀ j, 1 ≤ P.A j) (hρ : ∀ j, 1 ≤ P.ρ j) :
    ∀ j, P.A j + (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) ≤ P.A (j + 1) := by
  intro j
  have hK : P.A j + Wm + P.La.lo + P.Wk.lo ≤ P.K j := by
    unfold SteerRun.K SteerRun.au orEdges
    dsimp only
    split
    · have hAj := hA j
      have a := P.Wa0.fst_lo (hA j)
      have b := P.La.fst_lo (c := P.Wa0.fst (P.A j)) (by omega)
      have c := P.Wk.fst_lo (c := P.La.fst (P.Wa0.fst (P.A j))) (by omega)
      omega
    · have hAj := hA j
      have a := P.Wa1.fst_lo (hA j)
      have b := P.La.fst_lo (c := P.Wa1.fst (P.A j)) (by omega)
      have c := P.Wk.fst_lo (c := P.La.fst (P.Wa1.fst (P.A j))) (by omega)
      omega
  have hS := E.H_SND j
  have hR : P.ρ (j + 1) + P.Wq.lo + Lm ≤ P.Rsel (j + 1) := by
    unfold SteerRun.Rsel SteerRun.R0 SteerRun.R1 SteerRun.qr
    have a := P.Wq.fst_lo (hρ (j + 1))
    have hρj := hρ (j + 1)
    split
    · have b := P.L6.fst_lo (c := P.Wq.fst (P.ρ (j + 1))) (by omega)
      have c := P.W1.fst_lo (c := P.L6.fst (P.Wq.fst (P.ρ (j + 1)))) (by omega)
      omega
    · have b := P.L5.fst_lo (c := P.Wq.fst (P.ρ (j + 1))) (by omega)
      have c := P.W0.fst_lo (c := P.L5.fst (P.Wq.fst (P.ρ (j + 1)))) (by omega)
      omega
  have := E.H_RCV (j + 1)
  omega

end steer

/-! ## 5. Non-vacuity of the steer theorem (unit delays)

Every channel is a unit transport delay (`Ret.shift 1`), the receivers and
the sender respond after one tick (`Er = Es = 1`). Token `k`'s condition
alternates (`sv k = (k odd)`), and `s` changes in the middle of every idle
phase. Every trace is the gate relation applied to its input, so the gate
relations hold by definition; the environment's hypotheses are proved for
every token `k`. -/
namespace SteerWit

def u : Ret := Ret.shift 1
def sv (k : Nat) : Bool := decide (k % 2 = 1)
def run : SteerRun where
  Wq := u
  L5 := u
  L6 := u
  W0 := u
  W1 := u
  Wa0 := u
  Wa1 := u
  La := u
  Wk := u
  ρ j := 8 * j + 1
  A j := 8 * j + 5
  sv := sv

def req (t : Nat) : Bool := decide (1 ≤ t ∧ (t - 1) % 16 < 8)
def su (t : Nat) : Bool := sv ((t + 4) / 16)
def rqu (t : Nat) : Bool := req (t - 1)
def o5 (t : Nat) : Bool := req0B (rqu (t - 1)) (su (t - 1))
def o6 (t : Nat) : Bool := req1B (rqu (t - 1)) (su (t - 1))
def r0 (t : Nat) : Bool := o5 (t - 1)
def r1 (t : Nat) : Bool := o6 (t - 1)
def a0 (t : Nat) : Bool := r0 (t - 1)
def a1 (t : Nat) : Bool := r1 (t - 1)
def a0u (t : Nat) : Bool := a0 (t - 1)
def a1u (t : Nat) : Bool := a1 (t - 1)
def ao (t : Nat) : Bool := or2B (a0u (t - 1)) (a1u (t - 1))
def ack (t : Nat) : Bool := ao (t - 1)

theorem fu (c : Nat) (hc : 1 ≤ c) : u.fst c = c + 1 := Ret.fst_shift 1 c hc

theorem gates : SteerGates run req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack where
  H_WQ _ _ := rfl
  H_U5 _ _ := rfl
  H_U6 _ _ := rfl
  H_W0 _ _ := rfl
  H_W1 _ _ := rfl
  H_WA0 _ _ := rfl
  H_WA1 _ _ := rfl
  H_UA _ _ := rfl
  H_WK _ _ := rfl

theorem qr_eq (j : Nat) : run.qr j = 8 * j + 2 := by
  unfold SteerRun.qr; rw [show run.Wq = u from rfl, fu _ (by show 1 ≤ 8 * j + 1; omega)]; rfl
theorem R0_eq (j : Nat) : run.R0 j = 8 * j + 4 := by
  unfold SteerRun.R0; rw [qr_eq, show run.L5 = u from rfl, show run.W0 = u from rfl,
    fu (8 * j + 2) (by omega), fu (8 * j + 2 + 1) (by omega)]
theorem R1_eq (j : Nat) : run.R1 j = 8 * j + 4 := by
  unfold SteerRun.R1; rw [qr_eq, show run.L6 = u from rfl, show run.W1 = u from rfl,
    fu (8 * j + 2) (by omega), fu (8 * j + 2 + 1) (by omega)]
theorem K_eq (j : Nat) : run.K j = 8 * j + 8 := by
  unfold SteerRun.K SteerRun.au orEdges
  rw [show run.Wa0 = u from rfl, show run.Wa1 = u from rfl, show run.La = u from rfl,
    show run.Wk = u from rfl]
  dsimp only
  have hA : run.A j = 8 * j + 5 := rfl
  split <;> rw [hA, fu (8 * j + 5) (by omega), fu (8 * j + 5 + 1) (by omega),
    fu (8 * j + 5 + 1 + 1) (by omega)]

theorem req_tok : Tok 0 req run.ρ (fun _ => true) := by
  refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
  · have h2 : t < 8 * 0 + 1 := h2
    simp only [req, decide_eq_false_iff_not]; omega
  · have h1 : 8 * (2 * k) + 1 ≤ t := h1; have h2 : t < 8 * (2 * k + 1) + 1 := h2
    simp only [req, decide_eq_true_eq]; omega
  · have h1 : 8 * (2 * k + 1) + 1 ≤ t := h1; have h2 : t < 8 * (2 * k + 2) + 1 := h2
    simp only [req, decide_eq_false_iff_not]; omega

theorem s_pin : ∀ k t, run.qr (2 * k) ≤ t → t < run.qr (2 * k + 1) → su t = run.sv k := by
  intro k t h1 h2
  rw [qr_eq] at h1 h2
  show sv ((t + 4) / 16) = sv k
  rw [show (t + 4) / 16 = k by omega]

theorem fwd : Tok (run.T1 0) r0 run.R0 (fun k => !run.sv k) ∧ Tok (run.T1 0) r1 run.R1 run.sv :=
  steer_fwd gates req_tok s_pin

theorem a0_tok : Tok 6 a0 run.A (fun k => !run.sv k) :=
  ((fwd.1.fifo u (y := a0) (fun _ _ => rfl)).mono (T' := 6) (by decide)).congr
    (fun j => by show u.fst (run.R0 j) = 8 * j + 5; rw [R0_eq, fu (8 * j + 4) (by omega)])

theorem a1_tok : Tok 6 a1 run.A run.sv :=
  ((fwd.2.fifo u (y := a1) (fun _ _ => rfl)).mono (T' := 6) (by decide)).congr
    (fun j => by show u.fst (run.R1 j) = 8 * j + 5; rw [R1_eq, fu (8 * j + 4) (by omega)])

/-- **Non-vacuity**: the unit-delay run satisfies every hypothesis of
`steer_ok`. -/
theorem env : SteerEnv run req su a0 a1 0 6 1 1 where
  H_REQ := req_tok
  H_S_PIN := s_pin
  H_A0 := a0_tok
  H_A1 := a1_tok
  H_RCV j := by
    unfold SteerRun.Rsel; rw [R0_eq, R1_eq]; show _ ≤ 8 * j + 5; split <;> omega
  H_SND j := by rw [K_eq]; show _ ≤ 8 * (j + 1) + 1; omega
  H_ACK_SKEW j := by
    show u.fst (8 * j + 5) ≤ u.fst (8 * (j + 1) + 5) ∧ u.fst (8 * j + 5) ≤ u.fst (8 * (j + 1) + 5)
    rw [fu (8 * j + 5) (by omega), fu (8 * (j + 1) + 5) (by omega)]; omega

theorem witness :
    Tok (run.T1 0) r0 run.R0 (fun k => !run.sv k) ∧ Tok (run.T1 0) r1 run.R1 run.sv ∧
    Tok (run.T2 6) ack run.K (fun _ => true) ∧
    (∀ j, run.ρ j ≤ run.Rsel j ∧ run.Rsel j + 1 ≤ run.A j ∧ run.A j ≤ run.K j ∧
      run.K j + 1 ≤ run.ρ (j + 1)) :=
  steer_ok gates env

/-- And it is not degenerate: token 0 (`s = 0`) reaches only branch 0, token 1
(`s = 1`) only branch 1, and the sender is acknowledged for both. -/
theorem witness_routes :
    r0 4 = true ∧ r1 4 = false ∧ r0 20 = false ∧ r1 20 = true ∧ ack 8 = true ∧ ack 24 = true := by
  decide

/-! ### Scope of this witness (self-audit correction)

This run witnesses `steer_ok` (all of `SteerGates` and `SteerEnv`: `gates`,
`env`) and, through `OpsTimed2.SteerWit.static_witness`, `steer_ok_static`
(`SteerCausal`, `SteerStatic`). Neither theorem has a hypothesis `H_T1`.
`H_T1` and `H_T2` are hypotheses of `ContractsB.steer_contract` only, which
asks the FIFO model's clean windows to open before the first edges. They fail
here, for EVERY choice of the free window start `Tr` (resp. at the chosen
`Ta = 6`): the first branch request reaches receiver 0 at `R0 0 = 4`, one tick
before the forward window can open. `steer_contract`'s witness is
`SelfAuditB4.steer_contract_witness` (a run whose first request is at 9). -/

/-- `steer_contract`'s `H_T1.1` (`T1 Tr ≤ R0 (2 · κ false 0)`, with token 0 the
first `s = 0` token, so `κ false 0 = 0`) is false for every `Tr`. -/
theorem not_H_T1 (Tr : Nat) : ¬ run.T1 Tr ≤ run.R0 0 := by
  rw [R0_eq]; show ¬ Tr + 1 + (1 + 1) + (1 + 1) ≤ 8 * 0 + 4; omega

/-- `steer_contract`'s `H_T2` (`T2 Ta ≤ K 0`) is false at the `Ta = 6` used by `env`. -/
theorem not_H_T2 : ¬ run.T2 6 ≤ run.K 0 := by
  rw [K_eq]; show ¬ 6 + (1 + 1) + 1 + 1 ≤ 8 * 0 + 8; omega

end SteerWit

end Formal.Cells.OpsTimed
