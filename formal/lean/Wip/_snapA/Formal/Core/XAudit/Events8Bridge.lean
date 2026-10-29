import Formal.Core.XAudit.Events8Beh
import Formal.Net.Fasm.Basic
import Formal.Cells.LibGapSteer

/-!
# Formal.Core.XAudit.Events8Bridge — `design_verdict8`'s hypotheses against shards B and C

Probe E8Hyp (shard A). Notes: `formal/notes/A-e8hyp.md` (with the hypothesis-by-hypothesis
mapping table). Every theorem here is a bridge (A's hypothesis derived from another shard's
statement), a gap (a concrete trace showing the other shard's statement does not give A's),
or a non-vacuity result.

* §1 **SatPin vs B/C's window channel** (`CElemTiming.WinDelay`, the channel of C's
  `Fasm.Behaves`): A's per-pin transport is a `WinDelay` (`transport_win`), not conversely:
  `win_origin_gap` (WinDelay leaves `[0, hi)` free; A's warp reads the input's time-0 value
  there) and `win_overtake_gap` (WinDelay may read out of order: a clean input step gives a
  runt that NO monotone warp produces, with a quiet origin).
* §2 **Time origin.** `satPin_origin`: under `SatPin` time 0 is a combinational fixpoint of
  the whole netlist. `satPin_shift`: a physical trace that obeys the per-pin relation from
  `t0` on (monotone reads) and is quiet on `[t0 - H, t0]` is, shifted to `t0`, a `SatPin`
  behaviour. This is exactly what a reset theorem must deliver.
* §3 **Non-vacuity of SatPin + constants + reset.** `satPin_exists` / `satPin_exists_iff`:
  on a well-formed singly-driven netlist, `SatPin d plG` behaviours with time-0 state `σ0`
  exist iff `σ0` is a fixpoint; `core_hyps_exist`: with constant wires and reset as well.
  Negative control `ringD_unsat`: an unreset inverter loop has no `SatPin` behaviour.
* §4 **SelOK from B's steer theorem.** `sel_read_of_steer` derives one select read from
  `LibGapSteer.steer_pin_ok` (B's H_S_STABLE, H_SETUP_PIN, H_HOLD_PIN) through an embedding
  of A's ℕ warps as B's ℤ read maps (`rdOf`, `extZ`); `selOK_of_steer` lifts it to
  `Beh7.SelOK` for multi-bit selects.
* §5 **SelPart by construction.** `selPart_of_value`: groups that are indicators of distinct
  patterns of ONE value sequence per partition satisfy `SelPart`.

NOT here: H_ARB (no shard-B/C statement implies `HARB7`; see the notes), HDsub (probe HDsub),
a joint witness of HARB7/SelOK/HDsub on gcd_hw (the gcd_hw netlist is not a Lean term).
-/

namespace Formal.Core.XAudit.Events8Bridge

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2Pin (SatPin PinRel PinTab shift_warp)
open Formal.Core.XAudit.Events6 (plG)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7

/-! ## §1 SatPin's channel against B / C's window channel -/

theorem warp_lo_le_hi {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : lo ≤ hi := by
  have a := w.le_late (lo + hi); have b := w.early_le (lo + hi); omega

/-- A's per-pin transport channel (monotone warp, `[lo, hi]`) is B / C's window channel. -/
theorem transport_win {lo hi : Nat} {i o : Sig} (h : TraceDiscrete.Transport lo hi i o) :
    Formal.Cells.CElemTiming.WinDelay lo hi i o := by
  obtain ⟨f, w, hf⟩ := h
  have hlh := warp_lo_le_hi w
  intro t ht
  refine ⟨f t, ?_, ?_, hf t⟩
  · have := w.early_le t; omega
  · have := w.le_late t; omega

/-- **Gap 1 (time origin).** A window channel leaves its output free before `hi`;
A's transport forces it to the input's time-0 value. -/
theorem win_origin_gap :
    Formal.Cells.CElemTiming.WinDelay 1 1 (fun _ => false) (fun t => decide (t = 0)) ∧
      ¬ TraceDiscrete.Transport 1 1 (fun _ => false) (fun t => decide (t = 0)) := by
  refine ⟨fun t ht => ⟨t - 1, by omega, by omega, ?_⟩, fun ⟨f, _, hf⟩ => ?_⟩
  · simp only [decide_eq_false_iff_not]; omega
  · have := hf 0; simp at this

/-- A clean step at 2. -/
def ovI : Sig := fun t => decide (2 ≤ t)
/-- A window-channel output of `ovI` that overtakes: high at 3, low at 4, high from 5. -/
def ovO : Sig := fun t => decide (t = 3 ∨ 5 ≤ t)

/-- **Gap 2 (overtaking).** In `[1, 3]` the window channel can read the step's new value
at 3 and its old value at 4: a runt that no monotone warp produces. The output is quiet
(the input's time-0 value) before 3, so this is not the origin gap. -/
theorem win_overtake_gap :
    (∀ t, t < 3 → ovO t = ovI 0) ∧ Formal.Cells.CElemTiming.WinDelay 1 3 ovI ovO ∧
      ¬ TraceDiscrete.Transport 1 3 ovI ovO := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun ⟨f, w, hf⟩ => ?_⟩
  · simp only [ovO, ovI]; rw [decide_eq_false (by omega), decide_eq_false (by omega)]
  · by_cases h3 : t = 3
    · subst h3; exact ⟨2, by omega, by omega, by decide⟩
    · by_cases h4 : t = 4
      · subst h4; exact ⟨1, by omega, by omega, by decide⟩
      · refine ⟨t - 1, by omega, by omega, ?_⟩
        simp only [ovO, ovI]
        rw [decide_eq_true (by omega), decide_eq_true (by omega)]
  · have m := w.mono 3 4 (by omega)
    have a3 : ovI (f 3) = true := by rw [← hf 3]; decide
    have a4 : ovI (f 4) = false := by rw [← hf 4]; decide
    simp only [ovI, decide_eq_true_eq, decide_eq_false_iff_not] at a3 a4
    omega


/-! ## §2 Time origin -/






/-- **The time origin of `SatPin`.** At time 0 every gate output is its INIT at the
inputs' time-0 values: time 0 is a combinational fixpoint of the whole netlist. -/
theorem satPin_origin {d : Design} {pl : PinTab} {x : Fin d.n → Sig} (hs : SatPin d pl x) :
    ∀ g ∈ d.gates, x (d.wire g.out) 0 =
      g.init.testBit (addr (fun p : Fin g.k => x (d.wire (g.ins.getD p.val 0)) 0)) := by
  intro g hg
  obtain ⟨f, hw, he⟩ := hs g hg
  rw [he 0]
  congr 2
  funext p
  have h := (hw p.val p.isLt).le_late 0
  have : f p.val 0 = 0 := by omega
  rw [this]

/-- A physical per-pin relation valid from `t0` on (monotone reads, band `pl g i`). -/
def PhysPin (d : Design) (pl : PinTab) (g : GSpec) (y : Fin d.n → Sig) (t0 : Nat) : Prop :=
  ∃ f : Nat → Nat → Nat, (∀ i, i < g.k → Mono (f i) ∧
      ∀ t, t0 ≤ t → f i t + (pl g i).1 ≤ t ∧ t ≤ f i t + (pl g i).2) ∧
    ∀ t, t0 ≤ t → y (d.wire g.out) t =
      g.init.testBit (addr (fun p : Fin g.k => y (d.wire (g.ins.getD p.val 0)) (f p.val t)))

/-- **Shift bridge.** A physical trace that obeys the per-pin relation from `t0` on and
is QUIET (every wire constant) on `[t0 - H, t0]`, `H` at least every pin band's upper
end, is, shifted to start at `t0`, a `SatPin` behaviour. -/
theorem satPin_shift {d : Design} {pl : PinTab} {y : Fin d.n → Sig} {t0 H : Nat}
    (hp : ∀ g ∈ d.gates, PhysPin d pl g y t0)
    (hH : ∀ g ∈ d.gates, ∀ i, i < g.k → (pl g i).2 ≤ H)
    (hq : ∀ w u, t0 - H ≤ u → u ≤ t0 → y w u = y w t0) :
    SatPin d pl (fun w t => y w (t0 + t)) := by
  intro g hg
  obtain ⟨f, hw, he⟩ := hp g hg
  refine ⟨fun i t => f i (t0 + t) - t0, fun i hi => ⟨?_, ?_, ?_⟩, fun t => ?_⟩
  · intro a c hac; have := (hw i hi).1 (t0 + a) (t0 + c) (by omega); dsimp only; omega
  · intro t; have := ((hw i hi).2 (t0 + t) (by omega)).1; dsimp only; omega
  · intro t; have := ((hw i hi).2 (t0 + t) (by omega)).2; dsimp only; omega
  · show y (d.wire g.out) (t0 + t) = _
    rw [he (t0 + t) (by omega)]
    congr 2
    funext p
    have h1 := ((hw p.val p.isLt).2 (t0 + t) (by omega)).2
    have h2 := hH g hg p.val p.isLt
    by_cases hc : t0 ≤ f p.val (t0 + t)
    · show _ = y _ (t0 + (f p.val (t0 + t) - t0))
      congr 1; omega
    · show _ = y _ (t0 + (f p.val (t0 + t) - t0))
      have e : t0 + (f p.val (t0 + t) - t0) = t0 := by omega
      rw [e]; exact hq _ _ (by omega) (by omega)


/-! ## §3 Existence -/



/-- The trace built by recursion in time: time 0 is `σ0`, a driven wire is its gate's
INIT of the inputs `lo` steps earlier, an undriven wire is `inp`. -/
def xs (d : Design) (σ0 : Fin d.n → Bool) (inp : Fin d.n → Sig) : Nat → Fin d.n → Bool
  | 0, w => σ0 w
  | t + 1, w =>
    match d.gates.find? (fun g => decide (d.wire g.out = w)) with
    | some g => g.init.testBit (addr (fun p : Fin g.k =>
        xs d σ0 inp (t - (g.lo - 1)) (d.wire (g.ins.getD p.val 0))))
    | none => inp w (t + 1)
termination_by t => t
decreasing_by omega

theorem inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (List.mem_map.mpr ⟨b, hb', he.symm⟩) h.1
    · subst hb'; exact absurd (List.mem_map.mpr ⟨a, ha', he⟩) h.1
    · exact inj_of_nodup_map f h.2 ha' hb' he

theorem find_drv {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup) {g : GSpec}
    (hg : g ∈ d.gates) : d.gates.find? (fun g' => decide (d.wire g'.out = d.wire g.out)) = some g := by
  cases h : d.gates.find? (fun g' => decide (d.wire g'.out = d.wire g.out)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h g hg)
  | some g' =>
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    have e1 := Design.wire_val d (hwf g' hm).2.2.1
    have e2 := Design.wire_val d (hwf g hg).2.2.1
    have ho : g'.out = g.out := by rw [← e1, ← e2, hp]
    rw [inj_of_nodup_map GSpec.out hnd hm hg ho]

/-- **Existence (non-vacuity of SatPin, constants and reset).** On a well-formed netlist
with one driver per wire, every time-0 fixpoint `σ0` extends, for any undriven-wire
inputs agreeing with it at time 0, to a `SatPin d plG` behaviour (each pin read with
the fixed shift `t - lo`). -/
theorem satPin_exists {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup)
    (σ0 : Fin d.n → Bool)
    (hfix : ∀ g ∈ d.gates, σ0 (d.wire g.out) =
      g.init.testBit (addr (fun p : Fin g.k => σ0 (d.wire (g.ins.getD p.val 0)))))
    (inp : Fin d.n → Sig) (hi0 : ∀ w, inp w 0 = σ0 w) :
    ∃ x : Fin d.n → Sig, SatPin d plG x ∧ (∀ w, x w 0 = σ0 w) ∧
      ∀ w, (∀ g ∈ d.gates, d.wire g.out ≠ w) → ∀ t, x w t = inp w t := by
  refine ⟨fun w t => xs d σ0 inp t w, ?_, fun w => by simp [xs], ?_⟩
  · intro g hg
    have hw := hwf g hg
    refine ⟨fun _ t => t - g.lo, fun i _ => shift_warp _ _ hw.2.2.2.2.1, fun t => ?_⟩
    cases t with
    | zero =>
      show xs d σ0 inp 0 _ = _
      rw [show xs d σ0 inp 0 (d.wire g.out) = σ0 (d.wire g.out) by simp [xs], hfix g hg]
      congr 2
      funext p
      simp [xs]
    | succ t =>
      show xs d σ0 inp (t + 1) _ = _
      rw [xs, find_drv hwf hnd hg]
      simp only
      congr 2
      funext p
      have : t + 1 - g.lo = t - (g.lo - 1) := by have := hw.2.2.2.1; omega
      rw [this]
  · intro w hw t
    cases t with
    | zero => simp [xs, hi0]
    | succ t =>
      show xs d σ0 inp (t + 1) w = _
      have hn : d.gates.find? (fun g => decide (d.wire g.out = w)) = none := by
        rw [List.find?_eq_none]; intro g hg; simpa using hw g hg
      rw [xs, hn]

/-- **Necessity**: the time-0 values of a `SatPin` behaviour are a fixpoint (any band
table). Together with `satPin_exists`: `SatPin` behaviours with time-0 state `σ0` exist
iff `σ0` is a fixpoint. -/
theorem satPin_exists_iff {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup)
    (σ0 : Fin d.n → Bool) :
    (∃ x : Fin d.n → Sig, SatPin d plG x ∧ ∀ w, x w 0 = σ0 w) ↔
      ∀ g ∈ d.gates, σ0 (d.wire g.out) =
        g.init.testBit (addr (fun p : Fin g.k => σ0 (d.wire (g.ins.getD p.val 0)))) := by
  constructor
  · rintro ⟨x, hs, h0⟩ g hg
    have := satPin_origin hs g hg
    rw [h0] at this
    simp only [h0] at this
    exact this
  · intro hfix
    obtain ⟨x, hs, h0, _⟩ := satPin_exists hwf hnd σ0 hfix (fun w _ => σ0 w) (fun _ => rfl)
    exact ⟨x, hs, h0⟩

/-- **The outer hypotheses of `design_verdict8` that concern `x` alone** (SatPin, the
constant wires 0 / 1, reset high until `T`) are jointly satisfiable on every well-formed,
singly-driven netlist whose constant and reset wires are undriven, as soon as there is a
time-0 fixpoint with wire 0 low, wire 1 high and reset high. -/
theorem core_hyps_exist {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup)
    {rw T : Nat} (hT : 1 ≤ T) (h1rw : d.wire rw ≠ d.wire 1)
    (hu : ∀ g ∈ d.gates, d.wire g.out ≠ d.wire 0 ∧ d.wire g.out ≠ d.wire 1 ∧ d.wire g.out ≠ d.wire rw)
    (σ0 : Fin d.n → Bool)
    (hfix : ∀ g ∈ d.gates, σ0 (d.wire g.out) =
      g.init.testBit (addr (fun p : Fin g.k => σ0 (d.wire (g.ins.getD p.val 0)))))
    (s0 : σ0 (d.wire 0) = false) (s1 : σ0 (d.wire 1) = true) (sr : σ0 (d.wire rw) = true) :
    ∃ x : Fin d.n → Sig, SatPin d plG x ∧ (∀ t, x (d.wire 0) t = false) ∧
      (∀ t, x (d.wire 1) t = true) ∧ (∀ t, x (d.wire rw) t = decide (t < T)) := by
  have n01 : d.wire 1 ≠ d.wire 0 := fun h => by rw [h, s0] at s1; exact absurd s1 (by decide)
  have nr0 : d.wire rw ≠ d.wire 0 := fun h => by rw [h, s0] at sr; exact absurd sr (by decide)
  let inp : Fin d.n → Sig := fun w t =>
    if w = d.wire 0 then false else if w = d.wire 1 then true
    else if w = d.wire rw then decide (t < T) else σ0 w
  have hi0 : ∀ w, inp w 0 = σ0 w := by
    intro w
    by_cases a : w = d.wire 0
    · simp [inp, a, s0]
    · by_cases b : w = d.wire 1
      · simp [inp, b, s1, n01]
      · by_cases c : w = d.wire rw
        · simp [inp, c, sr, nr0, h1rw]; omega
        · simp [inp, a, b, c]
  obtain ⟨x, hs, _, hund⟩ := satPin_exists hwf hnd σ0 hfix inp hi0
  refine ⟨x, hs, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [hund _ (fun g hg => (hu g hg).1) t]; simp [inp]
  · rw [hund _ (fun g hg => (hu g hg).2.1) t]; simp [inp, n01]
  · rw [hund _ (fun g hg => (hu g hg).2.2) t]; simp [inp, nr0, h1rw]

/-! ### Negative control: SatPin can be unsatisfiable -/

/-- One inverter feeding itself (no reset): wire 2 = NOT wire 2. -/
def ringD : Design where
  m := 2
  gates := [{ name := "inv", k := 1, init := 1, ins := [2], out := 2, lo := 1, hi := 1 }]

/-- **`SatPin` has NO behaviour on an unreset inverter loop**: the time-0 fixpoint
`b = ¬b` does not exist. So the existence of a time-0 fixpoint (a reset state) is a
real condition, not a formality. -/
theorem ringD_unsat : ¬ ∃ x : Fin ringD.n → Sig, SatPin ringD plG x := by
  rintro ⟨x, hs⟩
  have h : x (ringD.wire 2) 0 = (1 : Nat).testBit (addr (fun _ : Fin 1 => x (ringD.wire 2) 0)) :=
    satPin_origin hs _ (List.mem_singleton_self _)
  have ha : ∀ y : Fin 1 → Bool, addr y = (y 0).toNat := by intro y; simp [addr]
  rw [ha] at h
  revert h
  generalize x (ringD.wire 2) 0 = c
  cases c <;> decide


/-! ## §4, §5 SelOK and SelPart -/




/-- A (ℕ-time, truncated-at-0) warp as one of B's ℤ-time read maps `LibGapSteer.Rd`:
before `lo` the pin reads the driver at a negative time (where the driver is extended
by its time-0 value), from `lo` on it reads at the warp. -/
def rdOf {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : Formal.Cells.LibGapSteer.Rd where
  σ := fun t => if t < (lo : Int) then t - lo else (f t.toNat : Int)
  lo := lo
  hi := hi
  ge := fun t => by
    have hlh := warp_lo_le_hi w
    by_cases h : t < (lo : Int)
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]
      have := w.early_le t.toNat; omega
  le := fun t => by
    by_cases h : t < (lo : Int)
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]
      have := w.le_late t.toNat; omega

/-- The ℤ-time extension of a trace: its time-0 value before 0. -/
def extZ (x : Sig) : Int → Bool := fun t => x t.toNat

theorem rdOf_read {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) (x : Sig) (s : Nat) :
    extZ x ((rdOf w).σ s) = x (f s) := by
  by_cases h : (s : Int) < (lo : Int)
  · have h1 : f s = 0 := by have := w.le_late s; omega
    simp only [extZ, rdOf, h, ↓reduceIte]
    rw [h1]; congr 1; omega
  · simp only [extZ, rdOf, h, ↓reduceIte, Int.toNat_natCast]

/-- **One select read, from B's steer theorem.** The request source's count `M`
(0 at time 0) is `2k+1` only inside `[R k, F k)`; the select driver `xs` shows `v k`
on `[S0 k, S1 k)` (B's H_S_STABLE); the request is read through a warp in
`[Rlo, Rhi]` and the select through one in `[Slo, Shi]`, both at the same sample
time; and B's per-pin H_SETUP_PIN / H_HOLD_PIN hold for every transaction. Then
whenever the request read shows transaction `k`, the select read shows `v k`.
The proof is `LibGapSteer.steer_pin_ok` (branch `true`) on the ℤ embedding. -/
theorem sel_read_of_steer {Rlo Rhi Slo Shi : Nat} {gR gS : Nat → Nat}
    (wR : Warp Rlo Rhi gR) (wS : Warp Slo Shi gS) (M : Nat → Nat) (hM0 : M 0 = 0)
    (xs : Sig) (v : Nat → Bool) (R F S0 S1 : Nat → Nat)
    (hwin : ∀ u k, M u = 2 * k + 1 → R k ≤ u ∧ u < F k)
    (hstab : ∀ k t, S0 k ≤ t → t < S1 k → xs t = v k)
    (hsetup : ∀ k, S0 k + Shi ≤ R k + Rlo) (hhold : ∀ k, F k + Rhi ≤ S1 k + Slo) :
    ∀ s k, M (gR s) = 2 * k + 1 → xs (gS s) = v k := by
  intro s k hm
  have hspec := Formal.Cells.LibGapSteer.steer_pin_ok true (v k) (rdOf wR) (rdOf wS)
    (R k) (F k) (S0 k) (S1 k) (extZ xs)
    (fun t h1 h2 => by unfold extZ; exact hstab k t.toNat (by omega) (by omega))
    (by show ((S0 k : Nat) : Int) + Shi ≤ (R k : Int) + Rlo; have := hsetup k; omega)
    (by show ((F k : Nat) : Int) + Rhi ≤ (S1 k : Int) + Slo; have := hhold k; omega) (s : Int)
  have hlo : Rlo ≤ s := by
    rcases Nat.lt_or_ge s Rlo with hc | hc
    · have : gR s = 0 := by have := wR.le_late s; omega
      rw [this, hM0] at hm; omega
    · exact hc
  have hσ : (rdOf wR).σ s = (gR s : Int) := by
    have hn : ¬ ((s : Int) < (Rlo : Int)) := by omega
    simp only [rdOf, hn, ↓reduceIte, Int.toNat_natCast]
  have hw := hwin (gR s) k hm
  have hp : Formal.Cells.LibGapSteer.pulse (R k) (F k) ((rdOf wR).σ s) = true := by
    rw [hσ]; unfold Formal.Cells.LibGapSteer.pulse; simp only [decide_eq_true_eq]; omega
  rw [hp, Formal.Cells.LibGapSteer.outB_eq, rdOf_read] at hspec
  cases h1 : xs (gS s) <;> cases h2 : v k <;> simp_all

/-- **SelOK from B's steer conditions** (multi-bit select). For every filtered pin
`(j, p)`, the select it sees is a function `φ j p` of `nb j p` select bits, bit `q`
being the driver `xs j p q` read through its own warp `gS j p q` in
`[Slo j p q, Shi j p q]`; transaction `k` of the pin's source lies in `[R j p k, F j p k)`;
bit `q` is stable at `vb j p q k` on `[S0 j p q k, S1 j p q k)`, with B's setup / hold
against every copy's band; and `sel` is `φ` of the stable bits. Then `SelOK`. -/
theorem selOK_of_steer {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}
    (bh : Beh7 net b sel)
    (nb : (j : Fin N) → Fin (net.ar j) → Nat)
    (φ : (j : Fin N) → (p : Fin (net.ar j)) → (Fin (nb j p) → Bool) → Bool)
    (xs : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Sig)
    (gS : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat → Nat)
    (Slo Shi : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat)
    (wS : ∀ j p q, Warp (Slo j p q) (Shi j p q) (gS j p q))
    (hsv : ∀ j p s, net.pk j p = PK.filt → bh.sv j p s = φ j p (fun q => xs j p q (gS j p q s)))
    (R F : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (S0 S1 : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat → Nat)
    (vb : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat → Bool)
    (hwin : ∀ j p u k, net.pk j p = PK.filt → bh.M u (net.src j p) = 2 * k + 1 →
      R j p k ≤ u ∧ u < F j p k)
    (hstab : ∀ j p q k t, net.pk j p = PK.filt → S0 j p q k ≤ t → t < S1 j p q k →
      xs j p q t = vb j p q k)
    (hsetup : ∀ j p q (i : Fin (net.nc j p)) k, net.pk j p = PK.filt →
      S0 j p q k + Shi j p q ≤ R j p k + b.loC j p i)
    (hhold : ∀ j p q (i : Fin (net.nc j p)) k, net.pk j p = PK.filt →
      F j p k + b.hiC j p i ≤ S1 j p q k + Slo j p q)
    (hsel : ∀ j p k, net.pk j p = PK.filt → sel (net.grp j p) k = φ j p (fun q => vb j p q k)) :
    bh.SelOK := by
  intro j p s i hk hodd
  have hk2 : bh.M (bh.G j p i s) (net.src j p) = 2 * (bh.M (bh.G j p i s) (net.src j p) / 2) + 1 := by
    omega
  rw [hsv j p s hk, hsel j p _ hk]
  congr 1
  funext q
  exact sel_read_of_steer (bh.wG j p i) (wS j p q) (fun u => bh.M u (net.src j p))
    (bh.M_zero _) (xs j p q) (vb j p q) (R j p) (F j p) (S0 j p q) (S1 j p q)
    (fun u k h => hwin j p u k hk h) (fun k t h1 h2 => hstab j p q k t hk h1 h2)
    (fun k => hsetup j p q i k hk) (fun k => hhold j p q i k hk) s _ hk2

/-! ## SelPart by construction -/

/-- **SelPart from one select value per partition.** If every group of a partition is
the indicator of its own pattern of ONE value sequence `val P` (distinct patterns within
a partition), then `SelPart` holds. -/
theorem selPart_of_value (sel : Nat → Nat → Bool) (parts : List (List Nat))
    (pat : Nat → Nat) (val : List Nat → Nat → Nat)
    (hinj : ∀ P ∈ parts, ∀ g1 ∈ P, ∀ g2 ∈ P, g1 ≠ g2 → pat g1 ≠ pat g2)
    (hsel : ∀ P ∈ parts, ∀ g ∈ P, ∀ k, sel g k = decide (pat g = val P k)) :
    Formal.Core.XAudit.Events7.SelPart sel parts := by
  intro P hP g1 h1 g2 h2 hne k ⟨a, c⟩
  rw [hsel P hP g1 h1, decide_eq_true_eq] at a
  rw [hsel P hP g2 h2, decide_eq_true_eq] at c
  exact hinj P hP g1 h1 g2 h2 hne (by rw [a, c])


end Formal.Core.XAudit.Events8Bridge
