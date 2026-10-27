import Formal.Cells.FifoFidelity

/-!
# Probe P3a: per-pin `H_SEL_ORDER` for `bd_c2`, `bd_c3`, `bd_c4` (cell_constraints entries
`bd_c2.sel_order`, `bd_c3.sel_order`, `bd_c4.sel_order`)

`FifoFidelity` proved the select-level phase theorem (`sel_phase`), its runt
(`sel_runt`), its arithmetic form (`sel_order_of_lat`) and the counterexample
(`ce_not_fifo`) for `bd_c2n` only (`INIT_c2n`, two inputs, one inverted). The
cell-constraint JSON extrapolated the same per-pin condition to the symmetric
C-elements. This file proves it, for the REAL INITs and pin maps of
`cells/rtl/bd_ce.v`:

* `bd_c2`  `64'h00E8_00E8_00E8_00E8`, `I0=a I1=b I2=q I3=rst`;
* `bd_c3`  `64'h0000_FE80_0000_FE80`, `I0=a I1=b I2=c I3=q I4=rst`;
* `bd_c4`  `64'h0000_0000_FFFE_8000`, `I0=a I1=b I2=c I3=d I4=q I5=rst`;
* (`bd_c2n` re-derived as a sanity instance, `isC_c2n`).

Method: one generic per-pin model `CPinLut` over `n` inputs (each input pin
read through its OWN FIFO site-pin map, as `FifoFidelity.PinLut`), and one
generic theorem per FifoFidelity result, stated for any next-state function
with the three C-element properties `IsCElem` (all inputs at target -> target;
feedback at target and SOME input at target -> target; feedback off target and
SOME input off target -> off target). Each cell's INIT is shown to have them by
evaluating `lutB` on the real constant (`isC_c2`, `isC_c3`, `isC_c4`).

Results (for each of the three cells, by instantiation):
* `sel_phase_gen`: H_SEL_ORDER + H_SEL_KEEP => the select-level excitation is
  the target from the LAST arrival to the LAST departure (input arrival order
  is free).
* `sel_runt_gen`: the excitation is the OLD value whenever one input has left
  at its select before the feedback arrived at its select: what H_SEL_ORDER
  excludes (necessity at the select level).
* `sel_order_of_lat_gen`: the JSON form `w_hi + SP[fb].hi <= E_tau +
  SP[departing].lo` for every departing pin implies H_SEL_ORDER.
* `ceG_*`: a closed-form run of the per-pin model for each cell (all other
  inputs held high, the real INIT reduces to `a || q`), feedback site pin 6
  ticks, departing pin 1 tick: H_SEL_ORDER fails (20 > 17), the node makes a
  runt and oscillates, and no FIFO read of the pin-level excitation reproduces
  it (`ceG_not_fifo`); with every pin at 1 tick the same environment is clean
  (`cjG_clean`).

Time is ℕ ticks as in `PipeTimed`. Core Lean only.
-/

namespace Formal.Cells.ConstraintsSel
open Formal.Cells
open Formal.Cells.PipeTimed

/-! ## 1. The INITs, verbatim from `cells/rtl/bd_ce.v` -/

/-- `bd_c3`. -/
def INIT_c3 : Nat := 0x0000FE800000FE80
/-- `bd_c4`. -/
def INIT_c4 : Nat := 0x00000000FFFE8000

/-- `bd_c2` next state over the pin map `I0=a I1=b I2=q I3=rst`. -/
def g2 (x : Fin 2 → Bool) (q r : Bool) : Bool :=
  lutB CElemTiming.INIT_c2 [x 0, x 1, q, r, false, false]
/-- `bd_c2n` (sanity instance). -/
def g2n (x : Fin 2 → Bool) (q r : Bool) : Bool :=
  lutB CElemTiming.INIT_c2n [x 0, x 1, q, r, false, false]
/-- `bd_c3` over `I0=a I1=b I2=c I3=q I4=rst I5=0`. -/
def g3 (x : Fin 3 → Bool) (q r : Bool) : Bool :=
  lutB INIT_c3 [x 0, x 1, x 2, q, r, false]
/-- `bd_c4` over `I0=a I1=b I2=c I3=d I4=q I5=rst`. -/
def g4 (x : Fin 4 → Bool) (q r : Bool) : Bool :=
  lutB INIT_c4 [x 0, x 1, x 2, x 3, q, r]

/-- `bd_c3`'s INIT is `~rst · (a·b·c + q·(a+b+c))` (32 rows, proved). -/
theorem c3_eq (a b c q r : Bool) :
    lutB INIT_c3 [a, b, c, q, r, false] = (!r && ((a && b && c) || (q && (a || b || c)))) := by
  cases a <;> cases b <;> cases c <;> cases q <;> cases r <;> decide

/-- `bd_c4`'s INIT is `~rst · (a·b·c·d + q·(a+b+c+d))` (64 rows, proved). -/
theorem c4_eq (a b c d q r : Bool) :
    lutB INIT_c4 [a, b, c, d, q, r] =
      (!r && ((a && b && c && d) || (q && (a || b || c || d)))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases q <;> cases r <;> decide

/-! ## 2. The C-element properties -/

/-- The three properties of a C-element next-state function `g x q rst`, phase
target `v`, input `i`'s target `tgt v i` (`v` for a plain pin, `!v` for a
bubble). -/
structure IsCElem (n : Nat) (g : (Fin n → Bool) → Bool → Bool → Bool)
    (tgt : Bool → Fin n → Bool) : Prop where
  all : ∀ v x q, (∀ i, x i = tgt v i) → g x q false = v
  hold : ∀ v x, (∃ i, x i = tgt v i) → g x v false = v
  stay : ∀ v x, (∃ i, x i ≠ tgt v i) → g x (!v) false = !v
  reset : ∀ x q, g x q true = false

theorem fin2 (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem bool_ne {a v : Bool} (h : a ≠ v) : a = !v := by
  cases a <;> cases v <;> simp_all

/-- `bd_c2` is a C-element (all pins plain). -/
theorem isC_c2 : IsCElem 2 g2 (fun v _ => v) where
  all v x q h := by
    show CElemTiming.exc CElemTiming.INIT_c2 _ _ _ _ = _; rw [CElemTiming.c2_eq, h 0, h 1]
    cases v <;> cases q <;> rfl
  hold v x h := by
    obtain ⟨i, hi⟩ := h
    show CElemTiming.exc CElemTiming.INIT_c2 _ _ _ _ = _; rw [CElemTiming.c2_eq]
    rcases fin2 i with rfl | rfl <;>
      (rw [hi]; cases v <;> simp)
  stay v x h := by
    obtain ⟨i, hi⟩ := h
    show CElemTiming.exc CElemTiming.INIT_c2 _ _ _ _ = _; rw [CElemTiming.c2_eq]
    rcases fin2 i with rfl | rfl <;>
      (rw [bool_ne hi]; cases v <;> simp)
  reset x q := by
    show CElemTiming.exc CElemTiming.INIT_c2 _ _ _ _ = _; rw [CElemTiming.c2_eq]; rfl

/-- `bd_c2n` is a C-element with a bubble on `b` (sanity: FifoFidelity's case). -/
theorem isC_c2n : IsCElem 2 g2n (fun v i => if i = 0 then v else !v) where
  all v x q h := by
    have h0 := h 0; have h1 := h 1
    show CElemTiming.exc CElemTiming.INIT_c2n _ _ _ _ = _; rw [CElemTiming.c2n_eq]
    simp at h0 h1; rw [h0, h1]; cases v <;> cases q <;> rfl
  hold v x h := by
    obtain ⟨i, hi⟩ := h
    show CElemTiming.exc CElemTiming.INIT_c2n _ _ _ _ = _; rw [CElemTiming.c2n_eq]
    rcases fin2 i with rfl | rfl <;> simp at hi <;>
      (rw [hi]; cases v <;> simp)
  stay v x h := by
    obtain ⟨i, hi⟩ := h
    show CElemTiming.exc CElemTiming.INIT_c2n _ _ _ _ = _; rw [CElemTiming.c2n_eq]
    rcases fin2 i with rfl | rfl <;> simp at hi
    · rw [bool_ne hi]; cases v <;> simp
    · have e : x 1 = v := by cases h' : x 1 <;> cases v <;> simp_all
      rw [e]; cases v <;> simp
  reset x q := by
    show CElemTiming.exc CElemTiming.INIT_c2n _ _ _ _ = _; rw [CElemTiming.c2n_eq]; rfl

/-- `bd_c3` is a C-element. -/
theorem isC_c3 : IsCElem 3 g3 (fun v _ => v) where
  all v x q h := by
    simp only [g3]; rw [c3_eq, h 0, h 1, h 2]; cases v <;> cases q <;> rfl
  hold v x h := by
    obtain ⟨i, hi⟩ := h
    simp only [g3]; rw [c3_eq]
    rcases fin3 i with rfl | rfl | rfl <;>
      (rw [hi]; cases v <;> simp)
  stay v x h := by
    obtain ⟨i, hi⟩ := h
    simp only [g3]; rw [c3_eq]
    rcases fin3 i with rfl | rfl | rfl <;>
      (rw [bool_ne hi]; cases v <;> simp)
  reset x q := by simp only [g3]; rw [c3_eq]; rfl

/-- `bd_c4` is a C-element. -/
theorem isC_c4 : IsCElem 4 g4 (fun v _ => v) where
  all v x q h := by
    simp only [g4]; rw [c4_eq, h 0, h 1, h 2, h 3]; cases v <;> cases q <;> rfl
  hold v x h := by
    obtain ⟨i, hi⟩ := h
    simp only [g4]; rw [c4_eq]
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      (rw [hi]; cases v <;> simp)
  stay v x h := by
    obtain ⟨i, hi⟩ := h
    simp only [g4]; rw [c4_eq]
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      (rw [bool_ne hi]; cases v <;> simp)
  reset x q := by simp only [g4]; rw [c4_eq]; rfl

/-! ## 3. The generic per-pin model -/

/-- The excitation at the mux-tree selects: input `i` read through `p i`, the
feedback through `pq`, rst through `ps`. -/
def exSelG {n : Nat} (g : (Fin n → Bool) → Bool → Bool → Bool) (p : Fin n → Ret) (pq ps : Ret)
    (x : Fin n → Trace) (qp rst : Trace) : Trace := fun t =>
  g (fun i => x i ((p i).σ t)) (qp (pq.σ t)) (rst (ps.σ t))

/-- The pin-level excitation (all pins read at one instant). -/
def exPinG {n : Nat} (g : (Fin n → Bool) → Bool → Bool → Bool)
    (x : Fin n → Trace) (qp rst : Trace) : Trace := fun t =>
  g (fun i => x i t) (qp t) (rst t)

/-- **The per-pin LUT model of an `n`-input C-element cell** (FifoFidelity's
`PinLut`, generalised).
* `p i`, `pq`, `ps`: **H_PIN_FIFO**, each pin's path from the LUT pin to its
  mux-tree select (site-pin buffer, a single-input CMOS chain, FIFO by A's
  `Pure` argument), band = the prjxray site-pin delay of the PHYSICAL pin the
  router chose. Test: GLS with per-pin site delays before the function;
  board: LOCK_PINS with the feedback on A1 and a departing input on A5/A6.
* `out`, **H_TREE_FIFO**: mux tree + output stage as ONE FIFO read of the
  Boolean function of the select vector (contains the residual static-hazard
  assumption, B-muxtree-fidelity). -/
structure CPinLut (n : Nat) (g : (Fin n → Bool) → Bool → Bool → Bool)
    (x : Fin n → Trace) (rst O qp : Trace) where
  p : Fin n → Ret
  pq : Ret
  ps : Ret
  out : Ret
  H_OUT : ∀ t, out.hi ≤ t → O t = exSelG g p pq ps x qp rst (out.σ t)

section gen
variable {n : Nat} {g : (Fin n → Bool) → Bool → Bool → Bool} {tgt : Bool → Fin n → Bool}
  {x : Fin n → Trace} {rst O qp : Trace}

/-- **Select-level phase theorem, any C-element cell.** Phase target `v`. At
the pins: input `i` at `tgt v i` on `[α i, α' i)`, feedback `v` on `[κ, κ')`,
rst low from `R`. Under **H_SEL_ORDER** (the feedback's new value reaches its
select no later than ANY departure reaches its select) and **H_SEL_KEEP**
(it stays until every departure has reached its select), the select-level
excitation is exactly `v` from the LAST arrival to the LAST departure. -/
theorem sel_phase_gen (hC : IsCElem n g tgt) (P : CPinLut n g x rst O qp) (v : Bool)
    (α α' : Fin n → Nat) (κ κ' R : Nat)
    (hx : ∀ i s, α i ≤ s → s < α' i → x i s = tgt v i)
    (hqp : ∀ s, κ ≤ s → s < κ' → qp s = v)
    (hrst : ∀ s, R ≤ s → rst s = false)
    (H_SEL_ORDER : ∀ i, P.pq.fst κ ≤ (P.p i).fst (α' i))
    (H_SEL_KEEP : ∀ i, (P.p i).fst (α' i) ≤ P.pq.fst κ') :
    ∀ t, (∀ i, (P.p i).fst (α i) ≤ t) → (∃ i, t < (P.p i).fst (α' i)) →
      P.ps.fst R ≤ t → exSelG g P.p P.pq P.ps x qp rst t = v := by
  intro t hA hD hR
  have er : rst (P.ps.σ t) = false := hrst _ (P.ps.fst_after hR)
  unfold exSelG; rw [er]
  by_cases hall : ∀ i, t < (P.p i).fst (α' i)
  · exact hC.all v _ _ (fun i => hx i _ ((P.p i).fst_after (hA i)) ((P.p i).fst_before (hall i)))
  · obtain ⟨j, hj⟩ := hD
    have hk : ∃ k, (P.p k).fst (α' k) ≤ t :=
      Classical.byContradiction fun h => hall fun i => Nat.lt_of_not_le fun h' => h ⟨i, h'⟩
    obtain ⟨k, hk⟩ := hk
    have hq : qp (P.pq.σ t) = v :=
      hqp _ (P.pq.fst_after (Nat.le_trans (H_SEL_ORDER k) hk))
        (P.pq.fst_before (Nat.lt_of_lt_of_le hj (H_SEL_KEEP j)))
    rw [hq]
    exact hC.hold v _ ⟨j, hx j _ ((P.p j).fst_after (hA j)) ((P.p j).fst_before hj)⟩

/-- **The runt (necessity at the select level).** If at instant `t` some input
has already left its target at its select while the feedback's new value has
not yet reached its select, the excitation is the OLD value `!v`: after
`sel_phase_gen`'s `v` this is a glitch no FIFO read of a single-edge
pin-level excitation produces. This is exactly the case H_SEL_ORDER excludes. -/
theorem sel_runt_gen (hC : IsCElem n g tgt) (P : CPinLut n g x rst O qp) (v : Bool) (t : Nat)
    (j : Fin n) (hxj : x j ((P.p j).σ t) ≠ tgt v j) (hq : qp (P.pq.σ t) = !v)
    (hs : rst (P.ps.σ t) = false) :
    exSelG g P.p P.pq P.ps x qp rst t = !v := by
  unfold exSelG; rw [hq, hs]; exact hC.stay v _ ⟨j, hxj⟩

/-- **H_SEL_ORDER in the JSON's arithmetic form.** Node edge at `τ`; the
feedback reaches its PIN by `K = τ + w_hi`; every departing input leaves its
PIN no earlier than `D = τ + E_τ ≥ 1`. If for every departing pin
`K + pq.hi ≤ D + (p i).lo` (feedback wire max + feedback site pin max ≤
earliest departure + that pin's site-pin min), H_SEL_ORDER holds. -/
theorem sel_order_of_lat_gen (P : CPinLut n g x rst O qp) {κ K D : Nat} {α' : Fin n → Nat}
    (hk : κ ≤ K) (hD : 1 ≤ D) (hdep : ∀ i, D ≤ α' i)
    (hlat : ∀ i, K + P.pq.hi ≤ D + (P.p i).lo) :
    ∀ i, P.pq.fst κ ≤ (P.p i).fst (α' i) := by
  intro i
  have e1 := P.pq.fst_le κ
  have e2 := (P.p i).fst_lo (c := α' i) (Nat.le_trans hD (hdep i))
  have := hdep i; have := hlat i
  omega

/-- The select-level edge band: no earlier than the last pin arrival plus the
fastest site pin, no later than plus the slowest. -/
theorem sel_edge_band_gen (P : CPinLut n g x rst O qp) (α : Fin n → Nat) (i : Fin n) :
    (1 ≤ α i → α i + (P.p i).lo ≤ (P.p i).fst (α i)) ∧ (P.p i).fst (α i) ≤ α i + (P.p i).hi :=
  ⟨fun h => (P.p i).fst_lo h, (P.p i).fst_le (α i)⟩

end gen

/-- Sanity: the generic model at `bd_c2n` is FifoFidelity's per-pin
excitation (`exSel`) with `x 0 = req`, `x 1 = ack`. -/
theorem exSelG_c2n (pr pa pq ps : Ret) (req ack qp rst : Trace) :
    exSelG g2n (fun i => if i = 0 then pr else pa) pq ps (fun i => if i = 0 then req else ack) qp rst =
      FifoFidelity.exSel pr pa pq ps req ack qp rst := by
  funext t; rfl

/-! ## 4. Counter-trace, every cell

The environment of FifoFidelity §4: input `a` (I0) high on `[10, 16)` at its
pin, every other input held high, rst low. With the other inputs high, every
cell's real INIT reduces to `a || q` (`g*_one`), the same buffer-or-feedback
loop as `bd_c2n` with `ack = 0`; so FifoFidelity's closed-form run `eI`, `OC`,
`qpC` is a run of each cell. Site pins: `a` 1 tick, others 1, feedback **6**,
rst 1; tree + output 2; feedback wire 1. -/

/-- Input traces: `a = reqC`, all others constantly high. -/
def xsC (n : Nat) : Fin n → Trace := fun i => if i.val = 0 then FifoFidelity.reqC else fun _ => true

theorem g2_one (a q : Bool) : g2 (fun i : Fin 2 => if i.val = 0 then a else true) q false = (a || q) := by
  show CElemTiming.exc CElemTiming.INIT_c2 _ _ _ _ = _; rw [CElemTiming.c2_eq]
  cases a <;> cases q <;> rfl
theorem g3_one (a q : Bool) : g3 (fun i : Fin 3 => if i.val = 0 then a else true) q false = (a || q) := by
  simp only [g3]; rw [c3_eq]; cases a <;> cases q <;> rfl
theorem g4_one (a q : Bool) : g4 (fun i : Fin 4 => if i.val = 0 then a else true) q false = (a || q) := by
  simp only [g4]; rw [c4_eq]; cases a <;> cases q <;> rfl

theorem xsC_at (n : Nat) (s : Nat) :
    (fun i : Fin n => xsC n i s) = (fun i : Fin n => if i.val = 0 then FifoFidelity.reqC s else true) := by
  funext i; unfold xsC; split <;> rfl

/-- The closed-form excitation of FifoFidelity's run is `a || loop`. -/
theorem eI_or (s : Nat) : FifoFidelity.eI s = (FifoFidelity.reqC (s - 1) || FifoFidelity.eI (s - 9)) := by
  rw [FifoFidelity.eI_loop, CElemTiming.c2n_eq]
  cases FifoFidelity.reqC (s - 1) <;> cases FifoFidelity.eI (s - 9) <;> rfl

theorem eJ_or (s : Nat) : FifoFidelity.eJ s = (FifoFidelity.reqC (s - 1) || FifoFidelity.eJ (s - 4)) := by
  rw [FifoFidelity.eJ_loop, CElemTiming.c2n_eq]
  cases FifoFidelity.reqC (s - 1) <;> cases FifoFidelity.eJ (s - 4) <;> rfl

section ce
variable {n : Nat} {g : (Fin n → Bool) → Bool → Bool → Bool}

/-- The run as a behaviour of the per-pin model, for any cell whose INIT is
`a || q` with the other inputs high. -/
def ceG (hg : ∀ a q, g (fun i : Fin n => if i.val = 0 then a else true) q false = (a || q)) :
    CPinLut n g (xsC n) FifoFidelity.zeroT FifoFidelity.OC FifoFidelity.qpC where
  p := fun _ => Ret.shift 1
  pq := Ret.shift 6
  ps := Ret.shift 1
  out := Ret.shift 2
  H_OUT := by
    intro t _
    show FifoFidelity.eI (t - 2) = exSelG g (fun _ => Ret.shift 1) (Ret.shift 6) (Ret.shift 1)
      (xsC n) FifoFidelity.qpC FifoFidelity.zeroT (t - 2)
    show FifoFidelity.eI (t - 2) = g (fun i : Fin n => xsC n i (t - 2 - 1))
      (FifoFidelity.OC (t - 2 - 6 - 1)) false
    rw [xsC_at n (t - 2 - 1), hg]
    have e : FifoFidelity.OC (t - 2 - 6 - 1) = FifoFidelity.eI (t - 2 - 9) := by
      simp only [FifoFidelity.OC]; congr 1
    rw [e]; exact eI_or _

/-- The same environment with every pin at 1 tick. -/
def cjG (hg : ∀ a q, g (fun i : Fin n => if i.val = 0 then a else true) q false = (a || q)) :
    CPinLut n g (xsC n) FifoFidelity.zeroT FifoFidelity.OJ FifoFidelity.qpJ where
  p := fun _ => Ret.shift 1
  pq := Ret.shift 1
  ps := Ret.shift 1
  out := Ret.shift 2
  H_OUT := by
    intro t _
    show FifoFidelity.eJ (t - 2) = exSelG g (fun _ => Ret.shift 1) (Ret.shift 1) (Ret.shift 1)
      (xsC n) FifoFidelity.qpJ FifoFidelity.zeroT (t - 2)
    show FifoFidelity.eJ (t - 2) = g (fun i : Fin n => xsC n i (t - 2 - 1))
      (FifoFidelity.OJ (t - 2 - 1 - 1)) false
    rw [xsC_at n (t - 2 - 1), hg]
    have e : FifoFidelity.OJ (t - 2 - 1 - 1) = FifoFidelity.eJ (t - 2 - 4) := by
      simp only [FifoFidelity.OJ]; congr 1
    rw [e]; exact eJ_or _

/-- **The counter-trace.** In the run `ceG`:
* every input is at the target 1 at its pin on `[10, 16)` (a legal phase:
  `a` departs at 16, three ticks after the node rose at 13);
* the feedback's rise (pin 14) reaches its select at 20, the departure of `a`
  (pin 16) reaches its select at 17: H_SEL_ORDER FAILS (20 > 17), while the
  arithmetic form with EQUAL pins would hold;
* the node rises at 13, drops at 19 (a runt) and rises again at 22. -/
theorem ceG_runt (hg : ∀ a q, g (fun i : Fin n => if i.val = 0 then a else true) q false = (a || q))
    (i0 : Fin n) (hi0 : i0.val = 0) :
    (∀ i s, 10 ≤ s → s < 16 → xsC n i s = true) ∧
    xsC n i0 16 = false ∧
    ((ceG hg).pq.fst 14 = 20 ∧ ((ceG hg).p i0).fst 16 = 17) ∧
    (FifoFidelity.OC 12 = false ∧ FifoFidelity.OC 13 = true ∧ FifoFidelity.OC 18 = true ∧
      FifoFidelity.OC 19 = false ∧ FifoFidelity.OC 22 = true) := by
  refine ⟨?_, ?_, ⟨Ret.fst_shift 6 14 (by omega), Ret.fst_shift 1 16 (by omega)⟩,
    FifoFidelity.ce_node⟩
  · intro i s h1 h2
    unfold xsC; split
    · simp only [FifoFidelity.reqC]; apply decide_eq_true; omega
    · rfl
  · unfold xsC; simp only [hi0, ↓reduceIte]; rfl

/-- **No FIFO read of the pin-level excitation reproduces the run** (for any
band with `hi ≤ 18`): the lumped `H_LUT_FIFO` is false for every one of these
cells once the feedback pin is 5 ticks slower than a departing pin. -/
theorem ceG_not_fifo (hg : ∀ a q, g (fun i : Fin n => if i.val = 0 then a else true) q false = (a || q))
    (L : Ret) (hL : L.hi ≤ 18) :
    ¬ (∀ t, L.hi ≤ t → FifoFidelity.OC t =
        exPinG g (xsC n) FifoFidelity.qpC FifoFidelity.zeroT (L.σ t)) := by
  have e : exPinG g (xsC n) FifoFidelity.qpC FifoFidelity.zeroT =
      ex FifoFidelity.reqC FifoFidelity.zeroT FifoFidelity.qpC FifoFidelity.zeroT := by
    funext t
    show g (fun i : Fin n => xsC n i t) (FifoFidelity.qpC t) false = _
    rw [xsC_at n t, hg]; unfold ex
    rw [CElemTiming.c2n_eq]
    cases FifoFidelity.reqC t <;> cases FifoFidelity.qpC t <;> rfl
  rw [e]; exact FifoFidelity.ce_not_fifo L hL

/-- With equal (1-tick) pins the same environment gives one clean edge, at 13. -/
theorem cjG_clean (hg : ∀ a q, g (fun i : Fin n => if i.val = 0 then a else true) q false = (a || q))
    (t : Nat) : FifoFidelity.OJ t = decide (13 ≤ t) ∧ (cjG hg).pq.hi = 1 :=
  ⟨FifoFidelity.cj_clean t, rfl⟩

end ce

/-! ### The counter-trace, instantiated for the three cells -/

theorem ce_c2_sel_order_fails :
    (ceG g2_one).pq.fst 14 = 20 ∧ ((ceG g2_one).p 0).fst 16 = 17 ∧
    FifoFidelity.OC 13 = true ∧ FifoFidelity.OC 19 = false ∧ FifoFidelity.OC 22 = true :=
  have h := ceG_runt g2_one 0 rfl
  ⟨h.2.2.1.1, h.2.2.1.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
theorem ce_c3_sel_order_fails :
    (ceG g3_one).pq.fst 14 = 20 ∧ ((ceG g3_one).p 0).fst 16 = 17 ∧
    FifoFidelity.OC 13 = true ∧ FifoFidelity.OC 19 = false ∧ FifoFidelity.OC 22 = true :=
  have h := ceG_runt g3_one 0 rfl
  ⟨h.2.2.1.1, h.2.2.1.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
theorem ce_c4_sel_order_fails :
    (ceG g4_one).pq.fst 14 = 20 ∧ ((ceG g4_one).p 0).fst 16 = 17 ∧
    FifoFidelity.OC 13 = true ∧ FifoFidelity.OC 19 = false ∧ FifoFidelity.OC 22 = true :=
  have h := ceG_runt g4_one 0 rfl
  ⟨h.2.2.1.1, h.2.2.1.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem ce_c2_not_fifo (L : Ret) (hL : L.hi ≤ 18) :
    ¬ (∀ t, L.hi ≤ t → FifoFidelity.OC t =
        exPinG g2 (xsC 2) FifoFidelity.qpC FifoFidelity.zeroT (L.σ t)) := ceG_not_fifo g2_one L hL
theorem ce_c3_not_fifo (L : Ret) (hL : L.hi ≤ 18) :
    ¬ (∀ t, L.hi ≤ t → FifoFidelity.OC t =
        exPinG g3 (xsC 3) FifoFidelity.qpC FifoFidelity.zeroT (L.σ t)) := ceG_not_fifo g3_one L hL
theorem ce_c4_not_fifo (L : Ret) (hL : L.hi ≤ 18) :
    ¬ (∀ t, L.hi ≤ t → FifoFidelity.OC t =
        exPinG g4 (xsC 4) FifoFidelity.qpC FifoFidelity.zeroT (L.σ t)) := ceG_not_fifo g4_one L hL

end Formal.Cells.ConstraintsSel
