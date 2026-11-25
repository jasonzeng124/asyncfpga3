import Formal.Core.Ternary
import Formal.Core.XAudit.Design

/-!
# Formal.Core.XAudit.Untimed — Eichelberger A/B over a parsed design, computed fast, proved equal

Probe A-xaudit. The untimed half of `xaudit`: for an input transition
`a → b`, algorithm A (`Ternary.iterA`) and algorithm B (`Ternary.iterB`) over
the `Ternary.LutNet` of the parsed design.

* `toLutNet d D`: node `w` of the net is wire `w`. A driven wire is the LUT of
  its driver (arity `k`, INIT bit at `addr` of the pins; a pin on an undriven
  wire reads the input `inl`, a pin on a driven wire reads the node `inr`). An
  undriven wire is a follower of its own input (never read by any node).
  `D` is the driver table (`drvTable d`), computed once by the executable.
* `fb_driven`: the Boolean gate function of node `w` is INIT bit
  `addr(pin values)` of the parsed driver of `w` (the connection lemma).
* The ternary rows are `Array`s. `iterRF_eq`/`iterBF_eq`: the array iteration
  that the executable runs (with an early stop at a fixed point) equals
  `Ternary.iterA`/`iterB` after `n` steps, pointwise.
* `soundA0`, `settleB0`: `Ternary.soundA`/`settleB` generalised to a TERNARY
  start state `t0` (used to chain transitions and to start from power-up all
  `X`). Proved from Ternary's `sound_postfix`, `iterA_fix`, `Net.cover`.
* `untimed_noGlitch`, `untimed_settles`: the verdicts the executable prints,
  as theorems about every `Ternary.Causal` behaviour (any gate and wire delays,
  unbounded) and, for settling, every behaviour with bounded staleness `D`.
-/

namespace Formal.Core.XAudit.Untimed

open Formal.Core.Ternary
open Formal.Core.Ternary.K3
open Formal.Core.XAudit (GSpec Design)

/-- Ternary's (local) three-valued type. -/
local notation "TK" => Formal.Core.Ternary.K3

/-! ## Generalised A/B soundness (ternary start state) -/

section Gen
variable {ι ν : Type} (N : Net ι ν) (l : List ν) (hl : ∀ i, i ∈ l)

theorem iterA_le_start (u : ι → TK) (t0 : ν → TK) : ∀ k, VLe (iterA N u t0 k) t0
  | 0 => vle_refl _
  | k + 1 => vle_trans (iterA_antitone N u t0 k) (iterA_le_start u t0 k)

include hl in
theorem iterA_postfix (u : ι → TK) (t0 : ν → TK) :
    VLe (iterA N u t0 l.length) (N.F u (iterA N u t0 l.length)) := by
  intro i
  have h := congrFun (iterA_fix N l hl u t0) i
  rw [← h]
  exact meet_le_right _ _

include hl in
/-- Algorithm A from a ternary start `t0` covering the initial state. -/
theorem soundA0 (a b : ι → Bool) (t0 : ν → TK)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (hσ : Causal N c σ) (h0 : VLe t0 (vb (σ 0))) :
    ∀ t, VLe (iterA N (uA a b) t0 l.length) (vb (σ t)) :=
  sound_postfix N (iterA_postfix N l hl _ t0) (fun t => hull_le (hc t)) hσ
    (vle_trans (iterA_le_start N _ t0 _) h0)

include hl in
/-- Algorithm B from the A result of a ternary start. -/
theorem settleB0 (a b : ι → Bool) (t0 : ν → TK)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (T0 : Nat) (hb : ∀ t, T0 ≤ t → c t = b)
    (hσ : Causal N c σ) (D : Nat) (hD : Stale N c σ D) (h0 : VLe t0 (vb (σ 0))) :
    ∀ k t, T0 + k * D ≤ t →
      VLe (iterB N b (iterA N (uA a b) t0 l.length) k) (vb (σ t)) := by
  intro k
  induction k with
  | zero => intro t _; exact soundA0 N l hl a b t0 c σ hc hσ h0 t
  | succ k IH =>
    intro t ht i
    have hDt : D ≤ t := by rw [Nat.succ_mul] at ht; omega
    obtain ⟨τi, τn, hτi, hτn, h⟩ := hD t i hDt
    show N.F (vb b) (iterB N b (iterA N (uA a b) t0 l.length) k) i ⊑ ofBool (σ t i)
    rw [h]
    apply N.cover
    · intro x
      have : c (τi x) = b := hb _ (by have := hτi x; rw [Nat.succ_mul] at ht; omega)
      show vb b x ⊑ ofBool (c (τi x) x)
      rw [this]; exact le_refl _
    · intro j
      exact IH (τn j) (by have := hτn j; rw [Nat.succ_mul] at ht; omega) j

end Gen

/-! ## The LUT net of a design -/

/-- A node: arity, INIT, pin wires. -/
structure Node where
  k : Nat
  init : Nat
  ins : List Nat

/-- Driver table: entry `w` is the first parsed gate with output `w`. -/
def drvTable (d : Design) : Array (Option GSpec) :=
  Array.ofFn (fun w : Fin d.n => d.gates.find? (fun g => g.out == w.val))

/-- Node of wire `w`: its driver, or (undriven) a follower of input `w`. -/
def nodeOf (D : Array (Option GSpec)) (w : Nat) : Node :=
  match D[w]?.join with
  | some g => ⟨g.k, g.init, g.ins⟩
  | none => ⟨1, 2, [w]⟩

def isDriven (D : Array (Option GSpec)) (v : Nat) : Bool := (D[v]?.join).isSome

/-- The `Ternary.LutNet` of a design (inputs and nodes both indexed by wires). -/
def toLutNet (d : Design) (D : Array (Option GSpec)) : LutNet (Fin d.n) (Fin d.n) where
  arity i := (nodeOf D i.val).k
  pin i p :=
    let v := (nodeOf D i.val).ins.getD p.val 0
    if isDriven D v then .inr (d.wire v) else .inl (d.wire v)
  tbl i x := (nodeOf D i.val).init.testBit (Ternary.addr x)

/-- The ternary network. -/
def net (d : Design) (D : Array (Option GSpec)) : Net (Fin d.n) (Fin d.n) := (toLutNet d D).toNet

theorem drvTable_get (d : Design) (w : Fin d.n) :
    (drvTable d)[w.val]?.join = d.gates.find? (fun g => g.out == w.val) := by
  simp [drvTable, w.isLt]

/-- **Connection lemma.** If `g` is the (first) parsed gate driving `w`, the
Boolean gate function of node `w` is INIT bit `addr` of its pin values, each
pin reading the input (undriven wire) or the node (driven wire) it is
connected to. -/
theorem fb_driven (d : Design) (w : Fin d.n) (g : GSpec)
    (hg : d.gates.find? (fun g => g.out == w.val) = some g)
    (a s : Fin d.n → Bool) :
    (net d (drvTable d)).fb a s w =
      Nat.testBit g.init (Ternary.addr (k := (nodeOf (drvTable d) w.val).k) (fun p =>
        let v := (nodeOf (drvTable d) w.val).ins.getD p.val 0
        if isDriven (drvTable d) v then s (d.wire v) else a (d.wire v))) ∧
      (nodeOf (drvTable d) w.val) = ⟨g.k, g.init, g.ins⟩ := by
  have hn : nodeOf (drvTable d) w.val = ⟨g.k, g.init, g.ins⟩ := by
    simp only [nodeOf, drvTable_get, hg]
  refine ⟨?_, hn⟩
  simp only [net, LutNet.toNet, toLutNet]
  rw [hn]
  congr 2
  funext p
  split <;> rfl

theorem find?_some_spec (d : Design) (w : Nat) (g : GSpec)
    (hg : d.gates.find? (fun g => g.out == w) = some g) : g ∈ d.gates ∧ g.out = w := by
  refine ⟨List.mem_of_find?_eq_some hg, ?_⟩
  have := List.find?_some hg
  simpa using this

/-! ## Array rows and the fast iteration -/

variable {n : Nat}

/-- Read entry `i` of a row (`X` out of range). -/
def rget (r : Array TK) (i : Fin n) : TK := if h : i.val < r.size then r[i.val] else Formal.Core.Ternary.K3.X

def rowOf (f : Fin n → TK) : Array TK := Array.ofFn f

theorem rget_rowOf (f : Fin n → TK) (i : Fin n) : rget (rowOf f) i = f i := by
  simp [rget, rowOf]

/-- One A step on a row. -/
def stepAR (N : Net (Fin n) (Fin n)) (u : Fin n → TK) (r : Array TK) : Array TK :=
  rowOf (fun i => meet (rget r i) (N.F u (rget r) i))

/-- One B step on a row. -/
def stepBR (N : Net (Fin n) (Fin n)) (b : Fin n → Bool) (r : Array TK) : Array TK :=
  rowOf (fun i => N.F (vb b) (rget r) i)

theorem rget_stepAR (N : Net (Fin n) (Fin n)) (u : Fin n → TK) (r : Array TK) :
    rget (stepAR N u r) = stepA N u (rget r) := by
  funext i; exact rget_rowOf _ i

theorem rget_stepBR (N : Net (Fin n) (Fin n)) (b : Fin n → Bool) (r : Array TK) :
    rget (stepBR N b r) = N.F (vb b) (rget r) := by
  funext i; exact rget_rowOf _ i

/-- Iterate a row step `k` times, stopping early at a fixed point. -/
def iterF (step : Array TK → Array TK) : Nat → Array TK → Array TK
  | 0, r => r
  | k + 1, r => let r' := step r; if r' = r then r else iterF step k r'

/-- Plain `k`-fold iteration. -/
def iterP (step : Array TK → Array TK) (r : Array TK) : Nat → Array TK
  | 0 => r
  | k + 1 => step (iterP step r k)

theorem iterP_fix (step : Array TK → Array TK) (r : Array TK) (h : step r = r) :
    ∀ k, iterP step r k = r
  | 0 => rfl
  | k + 1 => by simp only [iterP, iterP_fix step r h k, h]

theorem iterP_succ' (step : Array TK → Array TK) (r : Array TK) :
    ∀ k, iterP step r (k + 1) = iterP step (step r) k
  | 0 => rfl
  | k + 1 => by
      show step (iterP step r (k + 1)) = step (iterP step (step r) k)
      rw [iterP_succ' step r k]

theorem iterF_eq (step : Array TK → Array TK) : ∀ k r, iterF step k r = iterP step r k
  | 0, _ => rfl
  | k + 1, r => by
      simp only [iterF]
      split
      · rename_i h; exact (iterP_fix step r h (k + 1)).symm
      · rw [iterF_eq step k (step r), iterP_succ']

theorem iterP_A (N : Net (Fin n) (Fin n)) (u : Fin n → TK) (r : Array TK) :
    ∀ k, rget (iterP (stepAR N u) r k) = iterA N u (rget r) k
  | 0 => rfl
  | k + 1 => by
      simp only [iterP, iterA]
      rw [rget_stepAR, iterP_A N u r k]

theorem iterP_B (N : Net (Fin n) (Fin n)) (b : Fin n → Bool) (r : Array TK) :
    ∀ k, rget (iterP (stepBR N b) r k) = iterB N b (rget r) k
  | 0 => rfl
  | k + 1 => by
      simp only [iterP, iterB]
      rw [rget_stepBR, iterP_B N b r k]

/-- **Algorithm A as the executable runs it.** -/
def runA (N : Net (Fin n) (Fin n)) (a b : Fin n → Bool) (r0 : Array TK) : Array TK :=
  iterF (stepAR N (uA a b)) n r0

/-- **Algorithm B as the executable runs it** (from the A row). -/
def runB (N : Net (Fin n) (Fin n)) (a b : Fin n → Bool) (r0 : Array TK) : Array TK :=
  iterF (stepBR N b) n (runA N a b r0)

theorem runA_eq (N : Net (Fin n) (Fin n)) (a b : Fin n → Bool) (r0 : Array TK) :
    rget (runA N a b r0) = iterA N (uA a b) (rget r0) (List.finRange n).length := by
  rw [List.length_finRange, runA, iterF_eq, iterP_A]

theorem runB_eq (N : Net (Fin n) (Fin n)) (a b : Fin n → Bool) (r0 : Array TK) :
    rget (runB N a b r0) = iterB N b (iterA N (uA a b) (rget r0) (List.finRange n).length)
      (List.finRange n).length := by
  rw [runB, iterF_eq, iterP_B, runA_eq, List.length_finRange]

/-! ## The untimed verdicts -/

/-- **No glitch.** For every causal behaviour of the design's LUT net (any gate
and any wire delay, unbounded, per-wire sample times), whose inputs move, input
by input, between `a` and `b`, and whose initial state is covered by the row
`r0`: a wire that the executable's algorithm A reports binary `v` is `v` at
every time. -/
theorem untimed_noGlitch (N : Net (Fin n) (Fin n)) (a b : Fin n → Bool) (r0 : Array TK)
    (c : Nat → Fin n → Bool) (σ : Nat → Fin n → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (hσ : Causal N c σ) (h0 : VLe (rget r0) (vb (σ 0)))
    (w : Fin n) (v : Bool) (hv : rget (runA N a b r0) w = ofBool v) : ∀ t, σ t w = v := by
  intro t
  have h := soundA0 N (List.finRange n) (List.mem_finRange) a b (rget r0) c σ hc hσ h0 t w
  rw [← runA_eq, hv] at h
  exact ofBool_inj.mp (ofBool_le_iff.mp h)

/-- **Settles.** With in addition: inputs at `b` from `T0` and bounded
staleness `D`, a wire that algorithm B reports binary `v` equals `v` from
`T0 + n·D` on. -/
theorem untimed_settles (N : Net (Fin n) (Fin n)) (a b : Fin n → Bool) (r0 : Array TK)
    (c : Nat → Fin n → Bool) (σ : Nat → Fin n → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (T0 : Nat) (hb : ∀ t, T0 ≤ t → c t = b)
    (hσ : Causal N c σ) (D : Nat) (hD : Stale N c σ D) (h0 : VLe (rget r0) (vb (σ 0)))
    (w : Fin n) (v : Bool) (hv : rget (runB N a b r0) w = ofBool v) :
    ∀ t, T0 + n * D ≤ t → σ t w = v := by
  intro t ht
  have h := settleB0 N (List.finRange n) (List.mem_finRange) a b (rget r0) c σ hc T0 hb hσ D hD
    h0 (List.finRange n).length t (by rw [List.length_finRange]; exact ht) w
  rw [← runB_eq, hv] at h
  exact ofBool_inj.mp (ofBool_le_iff.mp h)

/-- The all-`X` row (power-up): covers every initial state. -/
def rowX (n : Nat) : Array TK := rowOf (n := n) (fun _ => Formal.Core.Ternary.K3.X)

theorem rowX_covers (s : Fin n → Bool) : VLe (rget (rowX n)) (vb s) := by
  intro i; rw [rowX, rget_rowOf]; exact X_le _

end Formal.Core.XAudit.Untimed
