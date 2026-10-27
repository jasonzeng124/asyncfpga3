import Formal.Core.Lut
import Formal.Core.Circuit
import Formal.Core.Trace.Discrete

/-!
# Formal.Core.XSim — timed ternary (X-window) simulation, sound and computable

Probe of shard A (track 4 x track 2). See `formal/notes/A-xsim.md`.

## Model

* Concrete: `Formal.Core.TraceDiscrete` (time `ℕ`, 1 step = 1 ps, a signal is
  `ℕ → Bool`). A **LUT gate** `LGate n` over wires `Fin n` is a Core `Lut k`
  (real INIT, `Lut.eval`), its pins wired to `ins : Fin k → Fin n`, its output
  to `out`, and a delay band `[lo, hi]`. Its relation (`LGate.rel`) is the
  Discrete transport channel: the zero-delay Boolean LUT function of the pin
  values, through a monotone warp with delay in `[lo, hi]`
  (`TraceDiscrete.Transport`). A routed wire is a `Lut 1` buffer gate
  (`Init.delay_buf`) with its own band. A network is a `List (LGate n)`; its
  circuit is `Circuit (Fin n) Sig` (`toCircuit`), so `Circuit.Sat` of
  `Formal.Core.Circuit` is the set of concrete behaviours. Cycles are allowed.
* Weaker channel: `WinCh lo hi e o` says each output sample is SOME input
  sample from the window `[t-hi, t-lo]` (non-FIFO, delay may vary per step —
  the channel of shard B's `CElemTiming.WinDelay`). `transport_winCh`:
  every transport channel is a window channel. Soundness is proved for
  window-channel networks, so it holds for both.
* Abstract: a signal is `ℕ → K3`. The output of a gate at `t` is
  `win lo hi (fun s => keval (pins at s)) t`: the `K3.merge` (glb in `⊑`,
  "X unless all agree") of the Kleene LUT value over the window
  `[t-hi, t-lo]`. Primary inputs are given abstract signals `u`; the driven
  wires start (time 0) from a given row `a0` (usually all `X`).
* The simulator (`hist`) is a `def` by structural recursion on time: it builds
  the list of rows `[row t, row (t-1), ..., row 0]`, rows are `List K3`.
  It is kernel-reducible, so `decide` evaluates it (no `native_decide`).

## Results

* `sound` (window channels) and `sound_circuit` (Transport circuits,
  `Circuit.Sat`): if every gate has `1 ≤ lo` (causality: no zero-delay
  loop), the abstract inputs cover the concrete inputs and `a0` covers the
  time-0 values of driven wires, then `val t w ⊑ ofBool (x w t)` for every
  wire and time, in every concrete behaviour. `defined_eq`: a binary
  abstract value is therefore a theorem about every delay assignment.
* `stationary`: if the inputs are constant from `t0` and the last `H ≥ hi`
  rows are equal, every later row is equal (the simulation has reached a
  fixed point). This turns a finite `decide` into an all-time statement.
* Demo on `Init.bd_c2` with routed input pins and the routed feedback wire
  (all bands `[1,3]`): four-phase protocol settles with bounded X windows
  (`c2_fourphase_*`), and the opposite-sense simultaneous change
  `a↑ b↓` latches X in the loop forever (`c2_hazard_*`).
-/

namespace Formal.Core.XSim

open K3
open Formal.Core.TraceDiscrete (Sig Warp delay delay_transport transport_mono)

/-! ## 1. Windows of `K3` values -/

/-- `merge` of `g a, g (a+1), ..., g (a+n)`. -/
def wmerge (g : Nat → K3) (a : Nat) : Nat → K3
  | 0 => g a
  | n + 1 => merge (wmerge g a n) (g (a + n + 1))

theorem wmerge_le (g : Nat → K3) (a : Nat) :
    ∀ n s, a ≤ s → s ≤ a + n → wmerge g a n ⊑ g s
  | 0, s, h1, h2 => by
      have : s = a := by omega
      subst this; exact le_refl _
  | n + 1, s, h1, h2 => by
      by_cases h : s ≤ a + n
      · exact le_trans (merge_le_left _ _) (wmerge_le g a n s h1 h)
      · have : s = a + n + 1 := by omega
        subst this; exact merge_le_right _ _

theorem wmerge_const (g : Nat → K3) (a : Nat) (c : K3) :
    ∀ n, (∀ j, j ≤ n → g (a + j) = c) → wmerge g a n = c
  | 0, h => by simpa [wmerge] using h 0 (Nat.le_refl 0)
  | n + 1, h => by
      simp only [wmerge]
      rw [wmerge_const g a c n (fun j hj => h j (by omega))]
      have := h (n + 1) (Nat.le_refl _)
      rw [← Nat.add_assoc] at this
      rw [this]
      exact merge_self c

/-- The X-window: `merge` of `g` over `[t - hi, t - lo]` (truncated at 0). -/
def win (lo hi : Nat) (g : Nat → K3) (t : Nat) : K3 :=
  wmerge g (t - hi) ((t - lo) - (t - hi))

theorem win_le {lo hi : Nat} {g : Nat → K3} {t s : Nat}
    (h1 : t - hi ≤ s) (h2 : s ≤ t - lo) : win lo hi g t ⊑ g s :=
  wmerge_le _ _ _ _ h1 (by omega)

theorem win_const {lo hi : Nat} {g : Nat → K3} {t : Nat} {c : K3} (hlh : lo ≤ hi)
    (h : ∀ s, t - hi ≤ s → s ≤ t - lo → g s = c) : win lo hi g t = c :=
  wmerge_const _ _ _ _ (fun j hj => h _ (by omega) (by omega))

/-! ## 2. Channels and gates -/

/-- Window channel (non-FIFO bounded delay): each output sample equals some
input sample between `lo` and `hi` steps earlier (truncated at 0). -/
def WinCh (lo hi : Nat) (e o : Sig) : Prop :=
  ∀ t, ∃ s, t - hi ≤ s ∧ s ≤ t - lo ∧ o t = e s

/-- Every Discrete transport channel (monotone warp) is a window channel. -/
theorem transport_winCh {lo hi : Nat} {e o : Sig}
    (h : TraceDiscrete.Transport lo hi e o) : WinCh lo hi e o := by
  obtain ⟨f, F, hf⟩ := h
  exact fun t => ⟨f t, F.early_le t, F.le_late t, hf t⟩

/-! ### Per-gate exactness of the window -/

theorem wmerge_eq_of_ne_X (g : Nat → K3) (a n : Nat) (h : wmerge g a n ≠ X) :
    wmerge g a n = g a := by
  have := wmerge_le g a n a (Nat.le_refl _) (by omega)
  rcases this with h' | h'
  · exact absurd h' h
  · exact h'

theorem wmerge_X (g : Nat → K3) (a : Nat) :
    ∀ n, wmerge g a n = X → (∀ s, g s ≠ X) →
      ∃ s1 s2, a ≤ s1 ∧ s1 ≤ a + n ∧ a ≤ s2 ∧ s2 ≤ a + n ∧ g s1 ≠ g s2
  | 0, h, hg => absurd h (hg a)
  | n + 1, h, hg => by
      by_cases hn : wmerge g a n = X
      · obtain ⟨s1, s2, h1, h2, h3, h4, h5⟩ := wmerge_X g a n hn hg
        exact ⟨s1, s2, h1, by omega, h3, by omega, h5⟩
      · refine ⟨a, a + n + 1, Nat.le_refl _, by omega, by omega, by omega, fun he => ?_⟩
        simp only [wmerge] at h
        rw [wmerge_eq_of_ne_X g a n hn, he] at h
        exact hg _ ((merge_self _).symm.trans h)

/-- **The X-window is exact for one gate.** If a window channel's abstract
output (from exactly known input `e`) is `X` at `t`, two legal outputs differ
at `t`. So all imprecision of `XSim` comes from composing gates (lost
correlations), never from the single-gate abstraction. -/
theorem win_exact (lo hi : Nat) (hlh : lo ≤ hi) (e : Sig) (t : Nat)
    (h : win lo hi (fun s => ofBool (e s)) t = X) :
    ∃ o o' : Sig, WinCh lo hi e o ∧ WinCh lo hi e o' ∧ o t ≠ o' t := by
  obtain ⟨s1, s2, h1, h2, h3, h4, h5⟩ :=
    wmerge_X _ _ _ h (fun s => ofBool_ne_X (e s))
  have mk : ∀ s, t - hi ≤ s → s ≤ t - lo →
      WinCh lo hi e (fun t' => if t' = t then e s else e (t' - lo)) := by
    intro s hs1 hs2 t'
    by_cases ht : t' = t
    · subst ht; exact ⟨s, hs1, hs2, by simp⟩
    · exact ⟨t' - lo, by omega, Nat.le_refl _, by simp [ht]⟩
  refine ⟨_, _, mk s1 h1 (by omega), mk s2 h3 (by omega), ?_⟩
  simp only [ite_true]
  exact fun he => h5 (by rw [he])

/-- A LUT gate on wires `Fin n`: Core LUT, pin wiring, output wire, delay band. -/
structure LGate (n : Nat) where
  k : Nat
  lut : Lut k
  ins : Fin k → Fin n
  out : Fin n
  lo : Nat
  hi : Nat

namespace LGate
variable {n : Nat} (g : LGate n)

/-- Zero-delay Boolean LUT function of the pin values. -/
def exc (x : Fin n → Sig) : Sig := fun t => g.lut.eval (fun i => x (g.ins i) t)

/-- Gate relation: LUT function through a `[lo, hi]` transport channel. -/
def rel : Gate (Fin n) Sig := fun x => TraceDiscrete.Transport g.lo g.hi (g.exc x) (x g.out)

/-- Gate relation with the weaker (non-FIFO) window channel. -/
def relW : Gate (Fin n) Sig := fun x => WinCh g.lo g.hi (g.exc x) (x g.out)

theorem relW_of_rel {x : Fin n → Sig} (h : g.rel x) : g.relW x := transport_winCh h

end LGate

/-- The concrete circuit of a gate list (shared Circuit layer). -/
def toCircuit {n : Nat} (gs : List (LGate n)) : Circuit (Fin n) Sig := gs.map LGate.rel

/-! ## 3. The simulator -/

section Sim
variable {n : Nat}

/-- Build a row (wire `i` at position `i`) by structural recursion. -/
def mkRow : (m : Nat) → (Fin m → K3) → List K3
  | 0, _ => []
  | m + 1, f => f 0 :: mkRow m (fun i => f i.succ)

theorem mkRow_getD : ∀ (m : Nat) (f : Fin m → K3) (w : Fin m), (mkRow m f).getD w.val X = f w
  | 0, _, w => w.elim0
  | m + 1, f, w => by
      refine Fin.cases ?_ (fun j => ?_) w
      · rfl
      · simp only [mkRow, Fin.val_succ, List.getD_cons_succ]
        exact mkRow_getD m (fun i => f i.succ) j

/-- The (first) gate driving wire `w`, if any. -/
def driver (gs : List (LGate n)) (w : Fin n) : Option (LGate n) :=
  gs.find? (fun g => decide (g.out = w))

/-- No gate drives `w`: it is a primary input. -/
def Undriven (gs : List (LGate n)) (w : Fin n) : Prop := ∀ g ∈ gs, g.out ≠ w

instance (gs : List (LGate n)) (w : Fin n) : Decidable (Undriven gs w) :=
  inferInstanceAs (Decidable (∀ g ∈ gs, g.out ≠ w))

theorem driver_some {gs : List (LGate n)} {w : Fin n} {g : LGate n}
    (h : driver gs w = some g) : g ∈ gs ∧ g.out = w := by
  unfold driver at h
  have h2 := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using h2⟩

theorem driver_none {gs : List (LGate n)} {w : Fin n} (h : driver gs w = none) :
    Undriven gs w := by
  intro g hg he
  have := List.find?_eq_none.mp h g hg
  simp [he] at this

/-- Abstract value of wire `w` at time `t`, from earlier rows `R s`. -/
def cell (gs : List (LGate n)) (u : Fin n → Nat → K3) (R : Nat → List K3) (t : Nat)
    (w : Fin n) : K3 :=
  match driver gs w with
  | none => u w t
  | some g => win g.lo g.hi (fun s => g.lut.keval (fun i => (R s).getD (g.ins i).val X)) t

/-- Row 0: inputs from `u`, driven wires from the power-up row `a0`. -/
def row0 (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3) : List K3 :=
  mkRow n (fun w => match driver gs w with
    | none => u w 0
    | some _ => a0 w)

/-- **The simulator.** `hist t = [row t, row (t-1), ..., row 0]`. -/
def hist (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3) : Nat → List (List K3)
  | 0 => [row0 gs u a0]
  | t + 1 =>
      let h := hist gs u a0 t
      mkRow n (cell gs u (fun s => h.getD (t - s) []) (t + 1)) :: h

/-- Row `t` of the simulation. -/
def arow (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3) (t : Nat) : List K3 :=
  (hist gs u a0 t).headD []

/-- Abstract value of wire `w` at time `t`. -/
def val (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3) (t : Nat)
    (w : Fin n) : K3 :=
  (arow gs u a0 t).getD w.val X

variable (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3)

theorem hist_getD : ∀ T s, s ≤ T → (hist gs u a0 T).getD (T - s) [] = arow gs u a0 s
  | 0, s, h => by
      have : s = 0 := by omega
      subst this; rfl
  | T + 1, s, h => by
      by_cases hs : s = T + 1
      · subst hs; simp only [Nat.sub_self]; rfl
      · have : T + 1 - s = (T - s) + 1 := by omega
        rw [this]
        simp only [hist, List.getD_cons_succ]
        exact hist_getD T s (by omega)

theorem arow_succ (t : Nat) :
    arow gs u a0 (t + 1) = mkRow n (cell gs u (fun s => (hist gs u a0 t).getD (t - s) []) (t + 1)) :=
  rfl

theorem val_zero (w : Fin n) :
    val gs u a0 0 w = match driver gs w with | none => u w 0 | some _ => a0 w :=
  mkRow_getD _ _ w

theorem val_succ (t : Nat) (w : Fin n) :
    val gs u a0 (t + 1) w = cell gs u (fun s => (hist gs u a0 t).getD (t - s) []) (t + 1) w :=
  mkRow_getD _ _ w

end Sim

/-! ## 4. Soundness -/

section Sound
variable {n : Nat} (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3)

/-- `x` is covered by the abstract simulation up to time `T`. -/
def CoveredUpTo (x : Fin n → Sig) (T : Nat) : Prop :=
  ∀ s, s ≤ T → ∀ w, val gs u a0 s w ⊑ ofBool (x w s)

/-- **Soundness** (window channels; cyclic networks allowed). -/
theorem sound (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (x : Fin n → Sig)
    (hsat : ∀ g ∈ gs, g.relW x)
    (hin : ∀ w, Undriven gs w → ∀ t, u w t ⊑ ofBool (x w t))
    (h0 : ∀ g ∈ gs, a0 g.out ⊑ ofBool (x g.out 0)) :
    ∀ t w, val gs u a0 t w ⊑ ofBool (x w t) := by
  suffices H : ∀ T, CoveredUpTo gs u a0 x T from fun t w => H t t (Nat.le_refl t) w
  intro T
  induction T with
  | zero =>
      intro s hs w
      have : s = 0 := by omega
      subst this
      rw [val_zero]
      cases hd : driver gs w with
      | none => exact hin w (driver_none hd) 0
      | some g =>
          obtain ⟨hg, rfl⟩ := driver_some hd
          exact h0 g hg
  | succ t ih =>
      intro s hs w
      by_cases hst : s ≤ t
      · exact ih s hst w
      have : s = t + 1 := by omega
      subst this
      rw [val_succ]
      unfold cell
      cases hd : driver gs w with
      | none => exact hin w (driver_none hd) (t + 1)
      | some g =>
          obtain ⟨hg, rfl⟩ := driver_some hd
          simp only
          obtain ⟨s, h1, h2, hx⟩ := hsat g hg (t + 1)
          have hlo1 := hlo g hg
          have hs : s ≤ t := by omega
          refine le_trans (win_le h1 h2) ?_
          rw [hist_getD gs u a0 t s hs, hx]
          simp only [LGate.exc]
          rw [← Lut.keval_ofBoolVec]
          exact Lut.keval_mono _ (fun i => ih s hs (g.ins i))

/-- **Soundness for the Discrete transport circuit** (`Circuit.Sat`). -/
theorem sound_circuit (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (x : Fin n → Sig)
    (hsat : Circuit.Sat (toCircuit gs) x)
    (hin : ∀ w, Undriven gs w → ∀ t, u w t ⊑ ofBool (x w t))
    (h0 : ∀ g ∈ gs, a0 g.out ⊑ ofBool (x g.out 0)) :
    ∀ t w, val gs u a0 t w ⊑ ofBool (x w t) :=
  sound gs u a0 hlo x (fun g hg => g.relW_of_rel (hsat _ (List.mem_map_of_mem hg))) hin h0

/-- A binary abstract value is the concrete value, for every behaviour. -/
theorem defined_eq {a : K3} {b c : Bool} (hc : a ⊑ ofBool c) (ha : a = ofBool b) : c = b :=
  ofBool_inj.mp (ofBool_le_iff.mp (ha ▸ hc))

end Sound

/-! ## 5. Stationarity: a finite check gives an all-time statement -/

section Stat
variable {n : Nat} (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3)

/-- If the inputs are constant from `t0 ≥ 1` and rows `t0 - H .. t0` are equal
(`H` bounds every `hi`), the simulation stays at that row forever. -/
theorem stationary (H t0 : Nat) (ht0 : 1 ≤ t0)
    (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (hlh : ∀ g ∈ gs, g.lo ≤ g.hi) (hhi : ∀ g ∈ gs, g.hi ≤ H)
    (hu : ∀ w, Undriven gs w → ∀ t, t0 ≤ t → u w t = u w t0)
    (hr : ∀ s, t0 - H ≤ s → s ≤ t0 → arow gs u a0 s = arow gs u a0 t0) :
    ∀ t, t0 ≤ t → arow gs u a0 t = arow gs u a0 t0 := by
  obtain ⟨t1, rfl⟩ : ∃ t1, t0 = t1 + 1 := ⟨t0 - 1, by omega⟩
  -- the cell function of row t0, in closed form
  have key : ∀ t, t1 ≤ t → (∀ s, t1 + 1 - H ≤ s → s ≤ t → arow gs u a0 s = arow gs u a0 (t1 + 1)) →
      arow gs u a0 (t + 1) = arow gs u a0 (t1 + 1) := by
    intro t ht hR
    rw [arow_succ, arow_succ]
    congr 1
    funext w
    unfold cell
    cases hd : driver gs w with
    | none => exact hu w (driver_none hd) (t + 1) (by omega)
    | some g =>
        obtain ⟨hg, rfl⟩ := driver_some hd
        simp only
        have := hlo g hg; have := hlh g hg; have := hhi g hg
        let c := g.lut.keval (fun i => (arow gs u a0 (t1 + 1)).getD (g.ins i).val X)
        have e1 : ∀ T, t1 ≤ T → T ≤ t →
            win g.lo g.hi (fun s => g.lut.keval
              (fun i => ((hist gs u a0 T).getD (T - s) []).getD (g.ins i).val X)) (T + 1) = c := by
          intro T hT1 hT2
          refine win_const (hlh g hg) (fun s h1 h2 => ?_)
          rw [hist_getD gs u a0 T s (by omega), hR s (by omega) (by omega)]
        rw [e1 t ht (Nat.le_refl _), e1 t1 (Nat.le_refl _) ht]
  have : ∀ m s, t1 + 1 - H ≤ s → s ≤ t1 + 1 + m → arow gs u a0 s = arow gs u a0 (t1 + 1) := by
    intro m
    induction m with
    | zero => intro s h1 h2; exact hr s h1 (by omega)
    | succ m ih =>
        intro s h1 h2
        by_cases hs : s ≤ t1 + 1 + m
        · exact ih s h1 hs
        have : s = (t1 + 1 + m) + 1 := by omega
        subst this
        exact key _ (by omega) ih
  intro t ht
  exact this (t - (t1 + 1)) t (by omega) (by omega)

theorem val_stationary (H t0 : Nat) (ht0 : 1 ≤ t0)
    (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (hlh : ∀ g ∈ gs, g.lo ≤ g.hi) (hhi : ∀ g ∈ gs, g.hi ≤ H)
    (hu : ∀ w, Undriven gs w → ∀ t, t0 ≤ t → u w t = u w t0)
    (hr : ∀ s, t0 - H ≤ s → s ≤ t0 → arow gs u a0 s = arow gs u a0 t0) :
    ∀ t w, t0 ≤ t → val gs u a0 t w = val gs u a0 t0 w := by
  intro t w ht
  simp only [val, stationary gs u a0 H t0 ht0 hlo hlh hhi hu hr t ht]

end Stat


/-! ## 6. Demo: the C-element `bd_c2` (cells/rtl/bd_ce.v) with routed pins and feedback

Wires (`Fin 8`): 0 `a_in`, 1 `b_in`, 2 `rst`, 3 `gnd` (primary inputs);
4 `a_pin`, 5 `b_pin` (the routed input nets as seen at LUT pins I0, I1);
6 `q` (LUT output O); 7 `qp` (routed feedback O -> I2).
Gates: two input routes `[ip, ip']`, the LUT `Init.bd_c2` (real INIT,
I0=a_pin I1=b_pin I2=qp I3=rst I4=I5=gnd) with band `[ll, lh]`, the feedback
route `[wl, wh]`. The demo bands are `[1,3]` everywhere (1 step = 1 ps scaled:
the shape matters, not the magnitude; see notes). -/

namespace Demo

/-- A routed wire `i -> o` (a `Lut 1` buffer) with band `[lo, hi]`. -/
def buf (i o : Fin 8) (lo hi : Nat) : LGate 8 :=
  { k := 1, lut := Init.delay_buf, ins := fun _ => i, out := o, lo := lo, hi := hi }

/-- The `bd_c2` LUT6, pins `[a_pin, b_pin, qp, rst, gnd, gnd]`. -/
def c2lut (lo hi : Nat) : LGate 8 :=
  { k := 6, lut := Init.bd_c2, ins := ofList (3 : Fin 8) [4, 5, 7, 2, 3, 3] 6, out := 6,
    lo := lo, hi := hi }

def c2net (ip ip' ll lh wl wh : Nat) : List (LGate 8) :=
  [buf 0 4 ip ip', buf 1 5 ip ip', c2lut ll lh, buf 6 7 wl wh]

/-- The demo network: every band `[1, 3]`. -/
def net : List (LGate 8) := c2net 1 3 1 3 1 3

/-- Concrete port stimuli as functions of time. -/
def stim (a b : Nat → Bool) (w : Fin 8) (t : Nat) : Bool :=
  match w.val with
  | 0 => a t
  | 1 => b t
  | 2 => decide (t < 4)
  | _ => false

/-- Four-phase: reset for 4 steps; `a↑` at 10, `b↑` at 16, `a↓` at 26, `b↓` at 32. -/
def stimFP : Fin 8 → Nat → Bool :=
  stim (fun t => decide (10 ≤ t ∧ t < 26)) (fun t => decide (16 ≤ t ∧ t < 32))

/-- Hazard: `b↑` at 6 (state stays 0), then `a↑` and `b↓` in the same step 16. -/
def stimHZ : Fin 8 → Nat → Bool :=
  stim (fun t => decide (16 ≤ t)) (fun t => decide (6 ≤ t ∧ t < 16))

/-- Exactly known inputs: abstract input = `ofBool` of the stimulus. -/
def absIn (st : Fin 8 → Nat → Bool) : Fin 8 → Nat → K3 := fun w t => ofBool (st w t)

/-- Power-up: everything unknown. -/
def a0 : Fin 8 → K3 := fun _ => X

/-- Expected abstract `q` under the four-phase stimulus, derived from the bands
(not pasted from a run): `b_pin` is X on `[17,18]` (b_in↑ at 16 through
`[1,3]`), so the LUT window `[t-3, t-1]` sees an X excitation for
`t ∈ [18, 21]`; `a↓` is a single-input change with `b = q = 1` (masked);
`b↓` at 32 gives X on `[34, 37]`. `t = 0` is the X power-up row. -/
def specFPq (t : Nat) : K3 :=
  if t = 0 then X else if t ≤ 17 then zero else if t ≤ 20 then X
  else if t ≤ 33 then one else if t ≤ 37 then X else zero

/-- Horizon of the finite checks. -/
def T : Nat := 45

theorem fp_q_trace :
    (List.range (T + 1)).all (fun t => decide (val net (absIn stimFP) a0 t 6 = specFPq t))
      = true := by decide

set_option maxRecDepth 10000 in
/-- Rows `T-3 .. T` coincide (the simulation reached its fixed point). -/
theorem fp_rows_fixed :
    (List.range' (T - 3) 4).all (fun s => decide (arow net (absIn stimFP) a0 s =
      arow net (absIn stimFP) a0 T)) = true := by decide

theorem hz_q_trace :
    (List.range (T + 1)).all (fun t => decide (val net (absIn stimHZ) a0 t 6 =
      if t = 0 then X else if t ≤ 17 then zero else X)) = true := by decide

set_option maxRecDepth 10000 in
theorem hz_rows_fixed :
    (List.range' (T - 3) 4).all (fun s => decide (arow net (absIn stimHZ) a0 s =
      arow net (absIn stimHZ) a0 T)) = true := by decide

theorem net_lo : ∀ g ∈ net, 1 ≤ g.lo := by decide
theorem net_lohi : ∀ g ∈ net, g.lo ≤ g.hi := by decide
theorem net_hi : ∀ g ∈ net, g.hi ≤ 3 := by decide

/-- The undriven wires of `net` are exactly the ports 0..3. -/
theorem net_undriven (w : Fin 8) : Undriven net w → w.val < 4 := by
  revert w; decide

theorem stimFP_const (w : Fin 8) (t : Nat) (ht : T ≤ t) : stimFP w t = stimFP w T := by
  simp only [stimFP, stim, T] at *
  split <;> simp <;> omega

theorem stimHZ_const (w : Fin 8) (t : Nat) (ht : T ≤ t) : stimHZ w t = stimHZ w T := by
  simp only [stimHZ, stim, T] at *
  split <;> simp <;> omega

theorem specFPq_1 {t : Nat} (h : 1 ≤ t ∧ t ≤ 17) : specFPq t = zero := by
  unfold specFPq; simp only [show t ≠ 0 by omega, show t ≤ 17 by omega, ↓reduceIte]
theorem specFPq_2 {t : Nat} (h : 22 ≤ t ∧ t ≤ 33) : specFPq t = one := by
  unfold specFPq
  simp only [show t ≠ 0 by omega, show ¬ t ≤ 17 by omega, show ¬ t ≤ 21 by omega,
    show t ≤ 33 by omega, ↓reduceIte]
theorem specFPq_3 {t : Nat} (h : 38 ≤ t) : specFPq t = zero := by
  unfold specFPq
  simp only [show t ≠ 0 by omega, show ¬ t ≤ 17 by omega, show ¬ t ≤ 21 by omega,
    show ¬ t ≤ 33 by omega, show ¬ t ≤ 37 by omega, ↓reduceIte]

/-- The abstract `q` under four-phase, for ALL time. -/
theorem fp_q_abs (t : Nat) : val net (absIn stimFP) a0 t 6 = specFPq t := by
  by_cases ht : t ≤ T
  · have h := fp_q_trace
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h t (by omega)
  · have hs := val_stationary net (absIn stimFP) a0 3 T (by decide) net_lo net_lohi net_hi
      (fun w _ t ht => by simp only [absIn, stimFP_const w t ht])
      (fun s h1 h2 => by
        have h := fp_rows_fixed
        simp only [List.all_eq_true, List.mem_range'_1, decide_eq_true_eq] at h
        exact h s ⟨h1, by simp only [T] at h2 ⊢; omega⟩) t 6 (by omega)
    rw [hs]
    have h := fp_q_trace
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    rw [h T (by decide), specFPq_3 (by decide), specFPq_3 (by simp only [T] at ht; omega)]

/-- The abstract `q` after the simultaneous `a↑ b↓`: X from step 18, for ALL
later time. The feedback latches the hazard: X never self-resolves. -/
theorem hz_q_abs (t : Nat) (ht : 18 ≤ t) : val net (absIn stimHZ) a0 t 6 = X := by
  by_cases ht' : t ≤ T
  · have h := hz_q_trace
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    rw [h t (by omega)]
    simp only [T] at ht'
    split <;> first | omega | (split <;> first | omega | rfl)
  · have hs := val_stationary net (absIn stimHZ) a0 3 T (by decide) net_lo net_lohi net_hi
      (fun w _ t ht => by simp only [absIn, stimHZ_const w t ht])
      (fun s h1 h2 => by
        have h := hz_rows_fixed
        simp only [List.all_eq_true, List.mem_range'_1, decide_eq_true_eq] at h
        exact h s ⟨h1, by simp only [T] at h2 ⊢; omega⟩) t 6 (by omega)
    rw [hs]
    have h := hz_q_trace
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    rw [h T (by decide)]
    decide

/-- **Concrete theorem, all delay assignments.** Every behaviour of the
`bd_c2` network (every pair of input-route delays, LUT delay and feedback
delay in `[1,3]`, each a monotone warp, from any power-up state) driven by the
four-phase stimulus has `q = 0` on `[1,17]`, `q = 1` on `[22,33]` and
`q = 0` from 38 on, forever. -/
theorem fp_q_concrete (x : Fin 8 → Sig) (hsat : Circuit.Sat (toCircuit net) x)
    (hin : ∀ w, Undriven net w → x w = stimFP w) (t : Nat) :
    (1 ≤ t ∧ t ≤ 17 → x 6 t = false) ∧ (22 ≤ t ∧ t ≤ 33 → x 6 t = true) ∧
    (38 ≤ t → x 6 t = false) := by
  have hc := sound_circuit net (absIn stimFP) a0 net_lo x hsat
    (fun w hw t => by rw [hin w hw]; exact le_refl _) (fun _ _ => X_le _) t 6
  rw [fp_q_abs t] at hc
  exact ⟨fun h => defined_eq hc (specFPq_1 h), fun h => defined_eq hc (specFPq_2 h),
    fun h => defined_eq hc (specFPq_3 h)⟩

theorem c2lut_exc (x : Fin 8 → Sig) (lo hi s : Nat) (hg : x 3 s = false) :
    (c2lut lo hi).exc x s = (!x 2 s && maj (x 4 s) (x 5 s) (x 7 s)) := by
  have hv : (fun i => x ((c2lut lo hi).ins i) s) =
      bvec [x 4 s, x 5 s, x 7 s, x 2 s, false, false] 6 := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => exact hg
    | ⟨5, _⟩ => exact hg
  simp only [LGate.exc, hv]
  exact Init.bd_c2_eval _ _ _ _

theorem buf_exc (x : Fin 8 → Sig) (i o : Fin 8) (lo hi s : Nat) :
    (buf i o lo hi).exc x s = x i s := by
  simp only [LGate.exc, buf]; cases x i s <;> rfl

/-- A concrete behaviour of `net` under `stimHZ` with fixed delays: input
routes `da`, `db`, LUT 1, feedback 1, and a closed form for `q`. -/
def hzBeh (da db : Nat) (q : Sig) : Fin 8 → Sig := fun w =>
  match w.val with
  | 4 => delay da (stimHZ 0)
  | 5 => delay db (stimHZ 1)
  | 6 => q
  | 7 => delay 1 q
  | _ => stimHZ w

theorem hzBeh_sat (da db : Nat) (q : Sig) (hda : 1 ≤ da ∧ da ≤ 3) (hdb : 1 ≤ db ∧ db ≤ 3)
    (hq : ∀ t, q t = (!stimHZ 2 (t - 1) && maj (delay da (stimHZ 0) (t - 1))
      (delay db (stimHZ 1) (t - 1)) (q (t - 1 - 1)))) :
    Circuit.Sat (toCircuit net) (hzBeh da db q) := by
  intro g hg
  simp only [toCircuit, net, c2net, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · refine transport_mono (by simp only [buf]; omega) (by simp only [buf]; omega) (?_ : TraceDiscrete.Transport da da _ _)
    have : hzBeh da db q 4 = delay da ((buf 0 4 1 3).exc (hzBeh da db q)) := by
      funext t; simp only [delay, buf_exc]; rfl
    show TraceDiscrete.Transport da da _ (hzBeh da db q 4)
    rw [this]; exact delay_transport _ _
  · refine transport_mono (by simp only [buf]; omega) (by simp only [buf]; omega) (?_ : TraceDiscrete.Transport db db _ _)
    have : hzBeh da db q 5 = delay db ((buf 1 5 1 3).exc (hzBeh da db q)) := by
      funext t; simp only [delay, buf_exc]; rfl
    show TraceDiscrete.Transport db db _ (hzBeh da db q 5)
    rw [this]; exact delay_transport _ _
  · refine transport_mono (by simp only [c2lut]; omega) (by simp only [c2lut]; omega) (?_ : TraceDiscrete.Transport 1 1 _ _)
    have : hzBeh da db q 6 = delay 1 ((c2lut 1 3).exc (hzBeh da db q)) := by
      funext t; simp only [delay]; rw [c2lut_exc _ _ _ _ rfl]; exact hq t
    show TraceDiscrete.Transport 1 1 _ (hzBeh da db q 6)
    rw [this]; exact delay_transport _ _
  · refine transport_mono (by simp only [buf]; omega) (by simp only [buf]; omega) (?_ : TraceDiscrete.Transport 1 1 _ _)
    have : hzBeh da db q 7 = delay 1 ((buf 6 7 1 3).exc (hzBeh da db q)) := by
      funext t; simp only [delay, buf_exc]; rfl
    show TraceDiscrete.Transport 1 1 _ (hzBeh da db q 7)
    rw [this]; exact delay_transport _ _

/-- Fast `a` route, slow `b` route: the pins see `11` for two steps; `q` latches 1. -/
theorem hz_latch_one : Circuit.Sat (toCircuit net) (hzBeh 1 3 (fun t => decide (18 ≤ t))) := by
  refine hzBeh_sat 1 3 _ (by omega) (by omega) (fun t => ?_)
  simp only [stimHZ, stim, delay, maj]
  by_cases h : 18 ≤ t <;> simp [h] <;> omega

/-- Slow `a` route, fast `b` route: the pins see `00`; `q` stays 0. -/
theorem hz_latch_zero : Circuit.Sat (toCircuit net) (hzBeh 3 1 (fun _ => false)) := by
  refine hzBeh_sat 3 1 _ (by omega) (by omega) (fun t => ?_)
  simp only [stimHZ, stim, delay, maj]
  simp; omega
/-- **The X is real.** Under the simultaneous `a↑ b↓`, two legal behaviours
of the same network (same stimulus, delays inside the bands) latch DIFFERENT
values of `q` forever after step 18. So no sound simulator can give a binary
`q` there, and `hz_q_abs` (X from 18 on, forever) is the exact answer. -/
theorem hz_nondeterministic : ∃ x y : Fin 8 → Sig,
    Circuit.Sat (toCircuit net) x ∧ Circuit.Sat (toCircuit net) y ∧
    (∀ w, Undriven net w → x w = stimHZ w ∧ y w = stimHZ w) ∧
    ∀ t, 18 ≤ t → x 6 t = true ∧ y 6 t = false := by
  refine ⟨_, _, hz_latch_one, hz_latch_zero, fun w hw => ?_, fun t ht => ?_⟩
  · have h4 := net_undriven w hw
    constructor <;> (simp only [hzBeh]; split <;> first | omega | rfl)
  · exact ⟨by simp only [hzBeh]; exact decide_eq_true ht, rfl⟩

end Demo

end Formal.Core.XSim
