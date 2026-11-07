import Formal.Cells.PipeTimed
open Formal.Core.LutList

/-!
# Track 6, probe 6f: a timed `bd_pipe` with any number of stages `N ≥ 1`

Probe 6e (`PipeTimed`) proved the two-stage pipe under FIFO bounded-delay
LUTs and lines. This file proves the same three statements for every
`N ≥ 1`, reusing 6e's step lemmas unchanged (`fifo_hold`, `or_hold_*`,
`exc_phase`, `exc_pre`, `node_phase`), which do not depend on `N`:

* **Control** (`pipe_ctl`, `nodes_clean`, `pins_clean`): every controller's
  excitation, every node and every internal pin is a clean step signal, one
  edge per phase, at event times DEFINED from the delay realisation (`PN.cc`).
* **Data** (`token`, `pipe_forward`): every stage latches every token's
  value, and the last stage delivers it to the receiver.
* **Liveness** (`live`): every node's edges strictly increase.
* **Non-vacuity** (`Wit.witness`, `Wit.witness_data`): for EVERY `N ≥ 1`, a
  unit-delay run satisfies all hypotheses at every instant, with closed-form
  event times `τ i j = 5 + 2i + 4j`, and delivers alternating tokens.

Event times: phase `j` of stage `i` starts at `c i j = max (Rin i j) (Ain i j)`
where the request arrives from stage `i-1`'s phase `j` and the acknowledge
from stage `i+1`'s phase `j-1`; the recursion is well founded on `2j + i` and
is written as an outer recursion on `j` with an inner (ascending) recursion
on `i` (`PN.row`, `PN.cc`). The induction of `pipe_ctl` follows the same
order.

Boundary `b = i + 1` (between stages `i` and `i + 1`) carries the request
line `Rq b` and the DACK line, the OR of `m b + 1` FIFO copies `Ap b k` of
stage `b`'s node; all per-boundary obligations are indexed by `b`.

**DACK, gate by gate** (section 0, `fastrise_or`): 6e's two-path
abstraction of the FASTRISE line is replaced by an `m + 1`-path OR, and the
real chain (`LUT1` buffer, then `LUT2 #(.INIT(4'hE))` side stages, each a
FIFO LUT of its real INIT) is PROVED to be such an OR, one path per tap plus
the full ripple. `Wit.chain_w` instantiates it: a rise crosses in one hop,
a fall through the whole chain.

Core Lean only.
-/

namespace Formal.Cells.PipeTimedN
open Formal.Cells Formal.Cells.PipeTimed

/-! ## 0. The DACK line, gate by gate: an OR of `m + 1` FIFO copies

6e modelled the DACK FASTRISE line as the OR of two FIFO copies of the node
(a fast tap and a slow ripple). Here it is the OR of `m + 1` FIFO copies,
and `fastrise_or` proves that the real gate-level chain is exactly that:
`bd_delay #(.N(DACK), .FASTRISE(1))` (`cells/rtl/bd_latch.v`) is a `LUT1`
buffer `s1 = s0` followed by `LUT2 #(.INIT(4'hE))` side stages
`s(i+1) = s i ∨ s0` (I0 = chain, I1 = tap), each LUT with FIFO arcs. Each
copy is one path from the node to the pin: the ripple through the buffer and
every side stage, or the tap into side stage `i` and the ripple after it. -/

/-- Minimum of `f 0, ..., f m`. -/
def fmin (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | m + 1 => min (fmin f m) (f (m + 1))

/-- Maximum of `f 0, ..., f m`. -/
def fmax (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | m + 1 => max (fmax f m) (f (m + 1))

/-- `g 0 ∨ ... ∨ g m`. -/
def orAll (g : Nat → Bool) : Nat → Bool
  | 0 => g 0
  | m + 1 => orAll g m || g (m + 1)

theorem fmin_le_of (f : Nat → Nat) (c : Nat) : ∀ m k, k ≤ m → f k ≤ c → fmin f m ≤ c := by
  intro m; induction m with
  | zero => intro k hk h; have : k = 0 := by omega
            subst this; exact h
  | succ m ih =>
    intro k hk h; show min (fmin f m) (f (m + 1)) ≤ c
    by_cases e : k = m + 1
    · subst e; omega
    · have := ih k (by omega) h; omega

theorem le_fmin (f : Nat → Nat) (c : Nat) : ∀ m, (∀ k, k ≤ m → c ≤ f k) → c ≤ fmin f m := by
  intro m; induction m with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ m ih =>
    intro h; show c ≤ min (fmin f m) (f (m + 1))
    have := ih (fun k hk => h k (by omega)); have := h (m + 1) (Nat.le_refl _); omega

theorem le_fmax_of (f : Nat → Nat) (c : Nat) : ∀ m k, k ≤ m → c ≤ f k → c ≤ fmax f m := by
  intro m; induction m with
  | zero => intro k hk h; have : k = 0 := by omega
            subst this; exact h
  | succ m ih =>
    intro k hk h; show c ≤ max (fmax f m) (f (m + 1))
    by_cases e : k = m + 1
    · subst e; omega
    · have := ih k (by omega) h; omega

theorem fmax_le (f : Nat → Nat) (c : Nat) : ∀ m, (∀ k, k ≤ m → f k ≤ c) → fmax f m ≤ c := by
  intro m; induction m with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ m ih =>
    intro h; show max (fmax f m) (f (m + 1)) ≤ c
    have := ih (fun k hk => h k (by omega)); have := h (m + 1) (Nat.le_refl _); omega

theorem fmin_eq (f : Nat → Nat) : ∀ m, ∃ k, k ≤ m ∧ fmin f m = f k := by
  intro m; induction m with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk, e⟩ := ih
    show ∃ k, k ≤ m + 1 ∧ min (fmin f m) (f (m + 1)) = f k
    by_cases h : fmin f m ≤ f (m + 1)
    · exact ⟨k, by omega, by omega⟩
    · exact ⟨m + 1, Nat.le_refl _, by omega⟩

theorem fmax_eq (f : Nat → Nat) : ∀ m, ∃ k, k ≤ m ∧ fmax f m = f k := by
  intro m; induction m with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk, e⟩ := ih
    show ∃ k, k ≤ m + 1 ∧ max (fmax f m) (f (m + 1)) = f k
    by_cases h : f (m + 1) ≤ fmax f m
    · exact ⟨k, by omega, by omega⟩
    · exact ⟨m + 1, Nat.le_refl _, by omega⟩

theorem orAll_true (g : Nat → Bool) : ∀ m k, k ≤ m → g k = true → orAll g m = true := by
  intro m; induction m with
  | zero => intro k hk h; have : k = 0 := by omega
            subst this; exact h
  | succ m ih =>
    intro k hk h; show (orAll g m || g (m + 1)) = true
    by_cases e : k = m + 1
    · subst e; rw [h]; cases orAll g m <;> rfl
    · rw [ih k (by omega) h]; rfl

theorem orAll_false (g : Nat → Bool) : ∀ m, (∀ k, k ≤ m → g k = false) → orAll g m = false := by
  intro m; induction m with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ m ih =>
    intro h; show (orAll g m || g (m + 1)) = false
    rw [ih (fun k hk => h k (by omega)), h (m + 1) (Nat.le_refl _)]; rfl

theorem orAll_congr (g g' : Nat → Bool) : ∀ m, (∀ k, k ≤ m → g k = g' k) → orAll g m = orAll g' m := by
  intro m; induction m with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ m ih =>
    intro h; show (orAll g m || g (m + 1)) = (orAll g' m || g' (m + 1))
    rw [ih (fun k hk => h k (by omega)), h (m + 1) (Nat.le_refl _)]

/-- **OR of `m + 1` FIFO copies, low stretch.** The input low on `[a, b)`
gives the output low on the intersection of the copies' low stretches. -/
theorem orn_hold_false (p : Nat → Ret) (m g : Nat) {x y : Trace}
    (hy : ∀ t, g ≤ t → y t = orAll (fun k => x ((p k).σ t)) m)
    {a b : Nat} (hx : ∀ s, a ≤ s → s < b → x s = false) :
    ∀ t, fmax (fun k => (p k).fst a) m ≤ t → t < fmin (fun k => (p k).fst b) m → g ≤ t →
      y t = false := by
  intro t h1 h2 h3
  rw [hy t h3]
  apply orAll_false
  intro k hk
  have e1 := le_fmax_of (fun k => (p k).fst a) ((p k).fst a) m k hk (Nat.le_refl _)
  have e2 := fmin_le_of (fun k => (p k).fst b) ((p k).fst b) m k hk (Nat.le_refl _)
  exact hx _ ((p k).fst_after (by omega)) ((p k).fst_before (by omega))

/-- **OR of `m + 1` FIFO copies, high stretch.** The input high on `[a, b)`
gives the output high from the first copy's rise to the last copy's fall,
provided every copy takes the rise before any copy takes the fall
(`hov`: the line is flushed). -/
theorem orn_hold_true (p : Nat → Ret) (m g : Nat) {x y : Trace}
    (hy : ∀ t, g ≤ t → y t = orAll (fun k => x ((p k).σ t)) m)
    {a b : Nat} (hx : ∀ s, a ≤ s → s < b → x s = true)
    (hov : fmax (fun k => (p k).fst a) m ≤ fmin (fun k => (p k).fst b) m) :
    ∀ t, fmin (fun k => (p k).fst a) m ≤ t → t < fmax (fun k => (p k).fst b) m → g ≤ t →
      y t = true := by
  intro t h1 h2 h3
  rw [hy t h3]
  by_cases hc : fmax (fun k => (p k).fst a) m ≤ t
  · obtain ⟨k, hk, e⟩ := fmax_eq (fun k => (p k).fst b) m
    have e1 := le_fmax_of (fun k => (p k).fst a) ((p k).fst a) m k hk (Nat.le_refl _)
    exact orAll_true _ m k hk (hx _ ((p k).fst_after (by omega)) ((p k).fst_before (by omega)))
  · obtain ⟨k, hk, e⟩ := fmin_eq (fun k => (p k).fst a) m
    have e2 := fmin_le_of (fun k => (p k).fst b) ((p k).fst b) m k hk (Nat.le_refl _)
    exact orAll_true _ m k hk (hx _ ((p k).fst_after (by omega)) ((p k).fst_before (by omega)))

/-- The real FASTRISE side INIT `4'hE`, pins `[I0 = chain, I1 = tap]`, is OR. -/
theorem fr_bin : ∀ a b : Bool, lutB Bundling.FR_SIDE [a, b] = (a || b) := by decide

/-- The FIFO copies of a FASTRISE chain: `cpath B C U n k` (`k ≤ n`) is the
`k`-th path from the input `s 0` to `s (n+1)`. `B`: the buffer's arc
(wire + LUT1); `C i`, `U i`: side stage `i`'s chain-pin and tap-pin arcs
(wire + LUT2 arc, composed by `Ret.comp`). Path 0 is the full ripple;
path `k ≥ 1` enters by side stage `k`'s tap. -/
def cpath (B : Ret) (C U : Nat → Ret) : Nat → Nat → Ret
  | 0, _ => B
  | n + 1, k => if k ≤ n then Ret.comp (cpath B C U n k) (C (n + 1)) else U (n + 1)

/-- Power-up guard of the chain: from this instant every stage relation has
been in force long enough. -/
def cguard (B : Ret) (C U : Nat → Ret) : Nat → Nat
  | 0 => B.hi
  | n + 1 => cguard B C U n + (C (n + 1)).hi + (U (n + 1)).hi

/-- **The gate-level FIFO FASTRISE chain IS an OR of FIFO copies.**
`s 0` is the node, `s (n+1)` the `n`-th side stage's output. Each LUT is
its REAL INIT (`BUF = 2'h2`, `FR_SIDE = 4'hE`, `lutB`) of its pins read
through FIFO maps (`H_LUT_FIFO` of 6e applied to every DACK element). Then
`s (n+1)` is the OR of the `n + 1` copies `cpath n k` of `s 0`. With
`n + 1 = DACK` this discharges the DACK line hypothesis of the pipe
(`GatesN.H_ACK_LINE`) with `m = DACK - 1`, paths `cpath (DACK-1)` and
guard `cguard (DACK-1)`; `DACK = 0` (bypass) is the single identity path. -/
theorem fastrise_or (s : Nat → Trace) (B : Ret) (C U : Nat → Ret) (Nd : Nat)
    (hB : ∀ t, B.hi ≤ t → s 1 t = lutB Bundling.BUF [s 0 (B.σ t)])
    (hS : ∀ i, 1 ≤ i → i < Nd → ∀ t, (C i).hi + (U i).hi ≤ t →
      s (i + 1) t = lutB Bundling.FR_SIDE [s i ((C i).σ t), s 0 ((U i).σ t)]) :
    ∀ n, n + 1 ≤ Nd → ∀ t, cguard B C U n ≤ t →
      s (n + 1) t = orAll (fun k => s 0 ((cpath B C U n k).σ t)) n := by
  intro n
  induction n with
  | zero => intro _ t ht; rw [hB t ht, Bundling.buf_bin]; rfl
  | succ n ih =>
    intro hn t ht
    have hg : cguard B C U (n + 1) = cguard B C U n + (C (n + 1)).hi + (U (n + 1)).hi := rfl
    rw [hS (n + 1) (by omega) (by omega) t (by omega), fr_bin]
    have g := (C (n + 1)).ge t
    rw [ih (by omega) _ (by omega)]
    show _ = (orAll (fun k => s 0 ((cpath B C U (n + 1) k).σ t)) n ||
      s 0 ((cpath B C U (n + 1) (n + 1)).σ t))
    have e : cpath B C U (n + 1) (n + 1) = U (n + 1) := by
      simp only [cpath, show ¬ (n + 1 ≤ n) by omega, ite_false]
    rw [e]
    congr 1
    apply orAll_congr
    intro k hk
    simp only [cpath, hk, ite_true]; rfl

/-! ## 1. Delay realisation and derived event times -/

/-- Delay realisation of one run of an `N`-stage pipe plus the
environment's event times. Stage `i < N`; boundary `b ∈ [1, N)` sits
between stages `b - 1` and `b`. -/
structure PN where
  /-- number of stages (`bd_pipe #(.N(N))`) -/
  N : Nat
  /-- reset is released at `R` -/
  R : Nat
  /-- stage `i`'s controller LUT read-time map -/
  L : Nat → Ret
  /-- boundary `b`'s request line (wire + SDELAY chain + wire), `O (b-1) → I0` of stage `b` -/
  Rq : Nat → Ret
  /-- boundary `b`'s acknowledge line `O b → I1` of stage `b-1` (DACK
  FASTRISE chain + wires) is the OR of `m b + 1` FIFO copies of the node
  (`fastrise_or`) -/
  m : Nat → Nat
  /-- the `k`-th copy's read-time map at boundary `b` (`cpath` for the real chain) -/
  Ap : Nat → Nat → Ret
  /-- power-up guard of boundary `b`'s acknowledge line (`cguard`) -/
  Ag : Nat → Nat
  /-- the environment's request `r[0]` makes its `j`-th edge at `ρ j` -/
  ρ : Nat → Nat
  /-- the environment's acknowledge `a[N]` makes its `j`-th edge at `γ j` -/
  γ : Nat → Nat

namespace PN

/-- Edge time at boundary `b`'s acknowledge output for the node's `j`-th
edge at `τ` (rise by the earlier path, fall by the later). -/
def ackT (P : PN) (b j τ : Nat) : Nat :=
  if j % 2 = 0 then fmin (fun k => (P.Ap b k).fst τ) (P.m b)
  else fmax (fun k => (P.Ap b k).fst τ) (P.m b)

/-- Phase starts of all stages in phase `j`, given each stage's acknowledge
arrival `α i`: ascending recursion on the stage index. -/
def row (P : PN) (j : Nat) (α : Nat → Nat) : Nat → Nat
  | 0 => max (P.ρ j) (α 0)
  | i + 1 => max ((P.Rq (i + 1)).fst ((P.L i).fst (row P j α i))) (α (i + 1))

/-- Acknowledge arrival at stage `i` for phase `j + 1`, from the node edges
`τn` of phase `j`. -/
def ackIn (P : PN) (j : Nat) (τn : Nat → Nat) (i : Nat) : Nat :=
  if i + 1 < P.N then P.ackT (i + 1) j (τn (i + 1)) else P.γ j

/-- All phase starts: outer recursion on the phase `j`. -/
def cc (P : PN) : Nat → Nat → Nat
  | 0 => P.row 0 (fun _ => P.R)
  | j + 1 => P.row (j + 1) (P.ackIn j (fun i => (P.L i).fst (cc P j i)))

/-- Phase `j` of stage `i` starts (both its pins at the target). -/
def c (P : PN) (i j : Nat) : Nat := P.cc j i
/-- Stage `i`'s node makes its `j`-th edge. -/
def τ (P : PN) (i j : Nat) : Nat := (P.L i).fst (P.c i j)
/-- Stage `i`'s request pin I0 makes its `j`-th edge. -/
def Rin (P : PN) : Nat → Nat → Nat
  | 0, j => P.ρ j
  | i + 1, j => (P.Rq (i + 1)).fst (P.τ i j)
/-- Stage `i`'s acknowledge pin I1 reaches phase `j`'s level. -/
def Ain (P : PN) (i : Nat) : Nat → Nat
  | 0 => P.R
  | j + 1 => P.ackIn j (fun k => P.τ k j) i

/-- Fastest path's minimum delay of boundary `b`'s DACK line (a rise). -/
def alo (P : PN) (b : Nat) : Nat := fmin (fun k => (P.Ap b k).lo) (P.m b)
/-- Slowest path's maximum delay. -/
def ahi (P : PN) (b : Nat) : Nat := fmax (fun k => (P.Ap b k).hi) (P.m b)
/-- Largest path minimum: a fall leaves no earlier than this (DACK's
credit, `N*lo` of the ripple for the real chain). -/
def aslow (P : PN) (b : Nat) : Nat := fmax (fun k => (P.Ap b k).lo) (P.m b)

/-- Minimum latency from stage `i`'s node edge to its request pin's next edge:
the sender's `Es` at stage 0; the round trip through stage `i - 1`
(DACK fast side, LUT, request line) inside. -/
def ER (P : PN) (Es : Nat) : Nat → Nat
  | 0 => Es
  | i + 1 => P.alo (i + 1) + (P.L i).lo + (P.Rq (i + 1)).lo

/-- Minimum latency from stage `i`'s node edge to its acknowledge pin's next
edge: the round trip through stage `i + 1` inside, the receiver's `Er` at the
last stage. -/
def EA (P : PN) (Er : Nat) (i : Nat) : Nat :=
  if i + 1 < P.N then (P.Rq (i + 1)).lo + (P.L (i + 1)).lo + P.alo (i + 1) else Er

/-- Minimum spacing of stage `i`'s consecutive node edges, minus nothing:
`τ i j + Won i ≤ τ i (j+1)` (`gap`). -/
def Won (P : PN) (Es Er i : Nat) : Nat := (P.L i).lo + max (P.ER Es i) (P.EA Er i)

theorem c_eq (P : PN) (i j : Nat) : P.c i j = max (P.Rin i j) (P.Ain i j) := by
  cases i <;> cases j <;> rfl

/-- Every copy's edge is at least its `lo` after the node's. -/
theorem fst_lo_all (P : PN) (b τ : Nat) (h : 1 ≤ τ) :
    ∀ k, k ≤ P.m b → τ + P.alo b ≤ (P.Ap b k).fst τ := by
  intro k hk
  have := (P.Ap b k).fst_lo h
  have := fmin_le_of (fun k => (P.Ap b k).lo) _ (P.m b) k hk (Nat.le_refl _)
  unfold alo; omega

theorem fst_hi_all (P : PN) (b τ : Nat) :
    ∀ k, k ≤ P.m b → (P.Ap b k).fst τ ≤ τ + P.ahi b := by
  intro k hk
  have := (P.Ap b k).fst_le τ
  have := le_fmax_of (fun k => (P.Ap b k).hi) _ (P.m b) k hk (Nat.le_refl _)
  unfold ahi; omega

theorem ackT_ge (P : PN) (b j τ : Nat) (h : 1 ≤ τ) : τ + P.alo b ≤ P.ackT b j τ := by
  unfold ackT; split
  · exact le_fmin _ _ _ (P.fst_lo_all b τ h)
  · exact le_fmax_of _ _ _ 0 (Nat.zero_le _) (P.fst_lo_all b τ h 0 (Nat.zero_le _))

theorem ackT_ge' (P : PN) (b j τ : Nat) : τ ≤ P.ackT b j τ := by
  unfold ackT; split
  · exact le_fmin _ _ _ (fun k _ => (P.Ap b k).fst_ge τ)
  · exact le_fmax_of _ _ _ 0 (Nat.zero_le _) ((P.Ap b 0).fst_ge τ)

theorem ackT_le (P : PN) (b j τ : Nat) : P.ackT b j τ ≤ τ + P.ahi b := by
  unfold ackT; split
  · exact fmin_le_of _ _ _ 0 (Nat.zero_le _) (P.fst_hi_all b τ 0 (Nat.zero_le _))
  · exact fmax_le _ _ _ (P.fst_hi_all b τ)

/-- A fall leaves the acknowledge line by the SLOWEST path: the DACK credit. -/
theorem ackT_odd (P : PN) (b j τ : Nat) (hj : j % 2 = 1) (h : 1 ≤ τ) :
    τ + P.aslow b ≤ P.ackT b j τ := by
  unfold ackT; simp only [show ¬ (j % 2 = 0) by omega, ite_false]
  obtain ⟨k, hk, e⟩ := fmax_eq (fun k => (P.Ap b k).lo) (P.m b)
  have := (P.Ap b k).fst_lo h
  have := le_fmax_of (fun k => (P.Ap b k).fst τ) ((P.Ap b k).fst τ) (P.m b) k hk (Nat.le_refl _)
  unfold aslow; omega

theorem Ain_in (P : PN) (i j : Nat) (h : i + 1 < P.N) :
    P.Ain i (j + 1) = P.ackT (i + 1) j (P.τ (i + 1) j) := by
  simp only [Ain, ackIn, h, ite_true]

theorem Ain_last (P : PN) (i j : Nat) (h : ¬ i + 1 < P.N) : P.Ain i (j + 1) = P.γ j := by
  simp only [Ain, ackIn, h, ite_false]

theorem EA_in (P : PN) (Er i : Nat) (h : i + 1 < P.N) :
    P.EA Er i = (P.Rq (i + 1)).lo + (P.L (i + 1)).lo + P.alo (i + 1) := by
  simp only [EA, h, ite_true]

theorem EA_last (P : PN) (Er i : Nat) (h : ¬ i + 1 < P.N) : P.EA Er i = Er := by
  simp only [EA, h, ite_false]

end PN

/-! ## 2. Gate relations, environment, control-side obligations -/

/-- **Gate relations of the `N`-stage pipe.** `r i`, `a i`: stage `i`'s
request (I0) and acknowledge (I1) pins; `O i`: its node; `q i`: its
feedback pin. `r 0` and `a (N-1)` are driven by the environment. -/
structure GatesN (P : PN) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) : Prop where
  /-- **H_RST**: `rst` high on `[0, R)` (from power-up), low after. -/
  H_RST : ∀ t, rst t = decide (t < P.R)
  /-- **H_CTL i**: each controller (real `bd_c2n` INIT, FIFO LUT
  `H_LUT_FIFO`, feedback window `H_FB`, 6e's `Ctl`). -/
  H_CTL : ∀ i, i < P.N → Ctl (r i) (a i) rst (O i) (q i) (P.L i) (wl i) (wh i)
  /-- **H_REQ_LINE b** (FIFO, `b = i + 1`): stage `b`'s I0 reads stage
  `b - 1`'s node through the request line `Rq b` (6e row 3). -/
  H_REQ_LINE : ∀ i, i + 1 < P.N → ∀ t, (P.Rq (i + 1)).hi ≤ t →
    r (i + 1) t = O i ((P.Rq (i + 1)).σ t)
  /-- **H_ACK_LINE b** (`b = i + 1`): stage `b - 1`'s I1 is the OR of the
  `m b + 1` FIFO copies of stage `b`'s node. For the real gate-level DACK
  FASTRISE chain with FIFO LUTs this is a THEOREM (`fastrise_or`), not an
  abstraction; 6e's two-path OR is the case `m b = 1`. -/
  H_ACK_LINE : ∀ i, i + 1 < P.N → ∀ t, P.Ag (i + 1) ≤ t →
    a i t = orAll (fun k => O (i + 1) ((P.Ap (i + 1) k).σ t)) (P.m (i + 1))

/-- **The environment**: the sender at `r[0]` (stage 0's I0) and the
receiver at `a[N]` (stage `N-1`'s I1), as in 6e's `Env2`. -/
structure EnvN (P : PN) (r0 aN : Trace) (Es Er : Nat) : Prop where
  H_REQ_LOW0 : ∀ t, P.R ≤ t → t < P.ρ 0 → r0 t = false
  H_REQ : ∀ j t, P.ρ j ≤ t → t < P.ρ (j + 1) → r0 t = Vph j
  H_ACK_LOW0 : ∀ t, P.R ≤ t → t < P.γ 0 → aN t = false
  H_ACK : ∀ j t, P.γ j ≤ t → t < P.γ (j + 1) → aN t = Vph j
  /-- **H_SND**: the sender's next request edge comes at least `Es` after
  stage 0's node edge it answers. -/
  H_SND : ∀ j, P.τ 0 j + Es ≤ P.ρ (j + 1)
  /-- **H_RCV**: the receiver's acknowledge edge comes at least `Er` after
  the last stage's node edge. -/
  H_RCV : ∀ j, P.τ (P.N - 1) j + Er ≤ P.γ j
  H_RST_EARLY : P.R ≤ P.ρ 0

/-- **Control-side obligations**, per stage `i` and per boundary `b = i+1`. -/
structure TimingN (P : PN) (wh : Nat → Nat) (Es Er : Nat) : Prop where
  H_N_POS : 1 ≤ P.N
  H_R_POS : 1 ≤ P.R
  /-- **H_RST_LONG i**: reset outlasts each controller loop. -/
  H_RST_LONG : ∀ i, i < P.N → (P.L i).hi + wh i ≤ P.R
  /-- **H_RST_LINES b**: both lines of boundary `b` have flushed the
  power-up values by release. -/
  H_RST_LINES : ∀ i, i + 1 < P.N →
    (P.L i).hi + (P.Rq (i + 1)).hi ≤ P.R ∧ (P.L (i + 1)).hi + P.ahi (i + 1) ≤ P.R ∧
    P.Ag (i + 1) ≤ P.R
  /-- **H_LAT i** (5b `H_ENV_LATENCY` at stage `i`): both neighbours answer
  slower than the feedback wire plus the LUT spread. The internal
  neighbours' latency is the DERIVED round trip (`ER`, `EA`). -/
  H_LAT : ∀ i, i < P.N → (P.L i).hi + wh i ≤ (P.L i).lo + min (P.ER Es i) (P.EA Er i)
  /-- **H_ACK_FLUSH b**: stage `b`'s high phase outlasts boundary `b`'s
  DACK path spread (6e row 11). -/
  H_ACK_FLUSH : ∀ i, i + 1 < P.N →
    P.ahi (i + 1) ≤ (P.L (i + 1)).lo + max (P.ER Es (i + 1)) (P.EA Er (i + 1)) + P.alo (i + 1)

/-! ## 3. Derived timing: causality across every boundary -/

section chain
variable {P : PN} {r0 aN : Trace} {wh : Nat → Nat} {Es Er : Nat}

/-- Every phase of every stage starts after reset release. -/
theorem ge_R (E : EnvN P r0 aN Es Er) : ∀ j i, P.R ≤ P.c i j := by
  intro j
  induction j with
  | zero => intro i; rw [P.c_eq]; simp only [PN.Ain]; omega
  | succ j ih =>
    intro i; rw [P.c_eq]
    by_cases h : i + 1 < P.N
    · rw [P.Ain_in i j h]
      have := P.ackT_ge' (i + 1) j (P.τ (i + 1) j)
      have := (P.L (i + 1)).fst_ge (P.c (i + 1) j); have := ih (i + 1)
      unfold PN.τ at *; omega
    · rw [P.Ain_last i j h]
      have := E.H_RCV j; have := (P.L (P.N - 1)).fst_ge (P.c (P.N - 1) j)
      have := ih (P.N - 1); unfold PN.τ at *; omega

variable (E : EnvN P r0 aN Es Er) (T : TimingN P wh Es Er)
include E T

theorem c_pos (i j : Nat) : 1 ≤ P.c i j := by have := ge_R E j i; have := T.H_R_POS; omega

theorem tau_lo (i j : Nat) : P.c i j + (P.L i).lo ≤ P.τ i j :=
  (P.L i).fst_lo (c_pos E T i j)

theorem tau_pos (i j : Nat) : 1 ≤ P.τ i j := by
  have := tau_lo E T i j; have := c_pos E T i j; omega

theorem Rin_lo (i j : Nat) : P.τ i j + (P.Rq (i + 1)).lo ≤ P.Rin (i + 1) j :=
  (P.Rq (i + 1)).fst_lo (tau_pos E T i j)

theorem Ain_lo (i j : Nat) (h : i + 1 < P.N) : P.τ (i + 1) j + P.alo (i + 1) ≤ P.Ain i (j + 1) := by
  rw [P.Ain_in i j h]; exact P.ackT_ge _ _ _ (tau_pos E T _ _)

/-- **Request-side departure, DERIVED** inside the pipe: stage `i`'s request
pin's next edge comes at least `ER i` after stage `i`'s node edge. -/
theorem depR (i j : Nat) (hi : i < P.N) : P.τ i j + P.ER Es i ≤ P.Rin i (j + 1) := by
  cases i with
  | zero => exact E.H_SND j
  | succ i =>
    have h1 := Rin_lo E T i (j + 1); have h2 := tau_lo E T i (j + 1)
    have h3 := P.c_eq i (j + 1); have h4 := Ain_lo E T i j hi
    simp only [PN.ER]; omega

/-- **Acknowledge-side departure, DERIVED** inside the pipe. -/
theorem depA (i j : Nat) (hi : i < P.N) : P.τ i j + P.EA Er i ≤ P.Ain i (j + 1) := by
  by_cases h : i + 1 < P.N
  · rw [P.EA_in Er i h]
    have h1 := Ain_lo E T i j h; have h2 := tau_lo E T (i + 1) j
    have h3 := P.c_eq (i + 1) j; have h4 := Rin_lo E T i j
    omega
  · rw [P.EA_last Er i h, P.Ain_last i j h]
    have e : i = P.N - 1 := by omega
    subst e; exact E.H_RCV j

theorem dep_c (i j : Nat) (hi : i < P.N) :
    P.c i j + (P.L i).lo + P.ER Es i ≤ P.Rin i (j + 1) ∧
    P.c i j + (P.L i).lo + P.EA Er i ≤ P.Ain i (j + 1) := by
  have := depR E T i j hi; have := depA E T i j hi; have := tau_lo E T i j; omega

/-- Stage `i`'s consecutive node edges are at least `Won i` apart. -/
theorem gap (i j : Nat) (hi : i < P.N) : P.τ i j + P.Won Es Er i ≤ P.τ i (j + 1) := by
  have := depR E T i j hi; have := depA E T i j hi; have := tau_lo E T i (j + 1)
  have := P.c_eq i (j + 1); unfold PN.Won; omega

/-- Stage `i+1`'s `j`-th edge follows stage `i`'s through the request line. -/
theorem fwd (i j : Nat) : P.τ i j + (P.Rq (i + 1)).lo + (P.L (i + 1)).lo ≤ P.τ (i + 1) j := by
  have := Rin_lo E T i j; have := tau_lo E T (i + 1) j; have := P.c_eq (i + 1) j; omega

/-- Stage `i`'s rise after stage `i+1`'s fall comes through the SLOW DACK
path of boundary `i+1`. -/
theorem back_odd (i j : Nat) (h : i + 1 < P.N) (hj : j % 2 = 1) :
    P.τ (i + 1) j + P.aslow (i + 1) + (P.L i).lo ≤ P.τ i (j + 1) := by
  have h1 := tau_lo E T i (j + 1); have h2 := P.c_eq i (j + 1)
  have h3 := P.ackT_odd (i + 1) j (P.τ (i + 1) j) hj (tau_pos E T _ _)
  rw [P.Ain_in i j h] at h2; omega

theorem rho_le (j : Nat) : P.ρ j + (P.L 0).lo ≤ P.τ 0 j := by
  have := tau_lo E T 0 j; have := P.c_eq 0 j; simp only [PN.Rin] at this; omega

theorem gam_le (j : Nat) : P.γ j + (P.L (P.N - 1)).lo ≤ P.τ (P.N - 1) (j + 1) := by
  have := tau_lo E T (P.N - 1) (j + 1); have := P.c_eq (P.N - 1) (j + 1)
  have hn := T.H_N_POS
  rw [P.Ain_last _ j (by omega)] at this; omega

/-- **Liveness, given the environment's.** Every stage's node edges strictly
increase, so every phase interval is non-empty. -/
theorem live (i j : Nat) (hi : i < P.N) (hp : 1 ≤ (P.L i).lo + wh i) :
    P.τ i j < P.τ i (j + 1) := by
  have g := gap E T i j hi; have l := T.H_LAT i hi
  have := (P.L i).lo_le_hi
  have e : P.Won Es Er i = (P.L i).lo + max (P.ER Es i) (P.EA Er i) := rfl
  omega

end chain

/-! ## 4. Every node and internal pin of the pipe is a clean step signal -/

section ctl
variable {P : PN} {rst : Trace} {r a O q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesN P rst r a O q wl wh) (E : EnvN P (r 0) (a (P.N - 1)) Es Er)
  (T : TimingN P wh Es Er)
include G E T

omit E T in
theorem rst_hi : ∀ t, t < P.R → rst t = true := by
  intro t h; rw [G.H_RST]; simp [h]

omit E T in
theorem rst_lo : ∀ t, P.R ≤ t → rst t = false := by
  intro t h; rw [G.H_RST]; simp; omega

/-- **Before the first phase, every stage.** Each excitation is 0 before its
first phase start, and each node is low from `L.hi` to its first edge.
Induction on the stage index: stage `i+1`'s request is stage `i`'s node,
still low, through the flushed request line. -/
theorem pre : ∀ i, i < P.N →
    (∀ s, s < P.c i 0 → ex (r i) (a i) (q i) rst s = false) ∧
    (∀ t, (P.L i).hi ≤ t → t < P.τ i 0 → O i t = false) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc : P.c 0 0 = P.ρ 0 := by
      rw [P.c_eq]; simp only [PN.Rin, PN.Ain]; have := E.H_RST_EARLY; omega
    have h1 : ∀ s, s < P.c 0 0 → ex (r 0) (a 0) (q 0) rst s = false := by
      rw [hc]
      exact exc_pre (G.H_CTL 0 hi) P.R (P.ρ 0) (rst_hi G) E.H_REQ_LOW0 (T.H_RST_LONG 0 hi)
    refine ⟨h1, fun t t1 t2 => ?_⟩
    rw [(G.H_CTL 0 hi).H_LUT_FIFO t t1]; exact h1 _ ((P.L 0).fst_before t2)
  | succ i ih =>
    intro hi
    have hprev := (ih (by omega)).2
    have h1 : ∀ s, s < P.c (i + 1) 0 → ex (r (i + 1)) (a (i + 1)) (q (i + 1)) rst s = false := by
      apply exc_pre (G.H_CTL (i + 1) hi) P.R (P.c (i + 1) 0) (rst_hi G) _ (T.H_RST_LONG (i + 1) hi)
      intro t t1 t2
      have hc := P.c_eq (i + 1) 0; simp only [PN.Rin, PN.Ain] at hc
      have hr := (T.H_RST_LINES i hi).1; have hl := (P.Rq (i + 1)).lo_le_hi
      have g := (P.Rq (i + 1)).ge t
      rw [G.H_REQ_LINE i hi t (by omega)]
      exact hprev _ (by omega) ((P.Rq (i + 1)).fst_before (by omega))
    refine ⟨h1, fun t t1 t2 => ?_⟩
    rw [(G.H_CTL (i + 1) hi).H_LUT_FIFO t t1]; exact h1 _ ((P.L (i + 1)).fst_before t2)

/-- Stage `i`, phase `j`, given clean request and acknowledge pins for the
phase: 6e's `exc_phase` with the DERIVED departures. -/
theorem phase_of (i j : Nat) (hi : i < P.N)
    (hreq : ∀ t, P.Rin i j ≤ t → t < P.Rin i (j + 1) → r i t = Vph j)
    (hack : ∀ t, P.Ain i j ≤ t → t < P.Ain i (j + 1) → a i t = !Vph j) :
    ∀ s, P.c i j ≤ s → s < P.c i (j + 1) → ex (r i) (a i) (q i) rst s = Vph j := by
  have hR := ge_R E j i
  have hlat := T.H_LAT i hi
  have ⟨d1, d2⟩ := dep_c E T i j hi
  have hc := P.c_eq i j
  have hb := T.H_RST_LONG i hi
  have res := exc_phase (G.H_CTL i hi) (Vph j) (P.Rin i j) (P.Rin i (j + 1)) (P.Ain i j)
    (P.Ain i (j + 1)) (min (P.ER Es i) (P.EA Er i)) hreq hack
    (fun t ht => rst_lo G t (by omega)) (by omega) (by omega) hlat (by omega)
  intro s h1 h2
  rw [P.c_eq] at h1 h2; exact res s h1 h2

/-- A stage's node is `Vph j` between its `j`-th and `(j+1)`-th edges, given
its excitation's phase `j`. -/
theorem node_of (i j : Nat) (hi : i < P.N)
    (h : ∀ s, P.c i j ≤ s → s < P.c i (j + 1) → ex (r i) (a i) (q i) rst s = Vph j) :
    ∀ t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j := by
  intro t t1 t2
  have := tau_lo E T i j; have := ge_R E j i; have := T.H_RST_LONG i hi
  exact node_phase (G.H_CTL i hi) h t t1 t2 (by omega)

/-- Stage `i+1`'s request pin, phase `j`, from stage `i`'s phase `j`
through the request line of boundary `i+1`. -/
theorem req_of (i j : Nat) (hi : i + 1 < P.N)
    (h : ∀ s, P.c i j ≤ s → s < P.c i (j + 1) → ex (r i) (a i) (q i) rst s = Vph j) :
    ∀ t, P.Rin (i + 1) j ≤ t → t < P.Rin (i + 1) (j + 1) → r (i + 1) t = Vph j := by
  have hO := node_of G E T i j (by omega) h
  intro t t1 t2
  have := Rin_lo E T i j; have := tau_lo E T i j; have := ge_R E j i
  have := (T.H_RST_LINES i hi).1
  exact fifo_hold (P.Rq (i + 1)) (G.H_REQ_LINE i hi) hO t t1 t2 (by omega)

omit G in
/-- The last stage's acknowledge pin is the receiver's. -/
theorem ack_last (j : Nat) :
    ∀ t, P.Ain (P.N - 1) j ≤ t → t < P.Ain (P.N - 1) (j + 1) → a (P.N - 1) t = !Vph j := by
  have hn := T.H_N_POS
  intro t t1 t2
  rw [P.Ain_last _ j (by omega)] at t2
  cases j with
  | zero => simp only [PN.Ain] at t1; rw [E.H_ACK_LOW0 t t1 t2]; rfl
  | succ j =>
    rw [P.Ain_last _ j (by omega)] at t1
    rw [E.H_ACK j t t1 t2, Vph_succ, Bool.not_not]

/-- Stage `i`'s acknowledge pin for phase 0 (boundary `i+1`'s DACK line
carries stage `i+1`'s still-low node). -/
theorem ack_zero (i : Nat) (hi : i + 1 < P.N) :
    ∀ t, P.Ain i 0 ≤ t → t < P.Ain i 1 → a i t = !Vph 0 := by
  intro t t1 t2
  rw [P.Ain_in i 0 hi] at t2
  simp only [PN.Ain] at t1
  simp only [PN.ackT, show (0 : Nat) % 2 = 0 from rfl, ite_true] at t2
  have hl := T.H_RST_LINES i hi
  have f1 := fmax_le (fun k => (P.Ap (i + 1) k).fst (P.L (i + 1)).hi) ((P.L (i + 1)).hi + P.ahi (i + 1))
    (P.m (i + 1)) (P.fst_hi_all (i + 1) _)
  have := orn_hold_false (P.Ap (i + 1)) (P.m (i + 1)) (P.Ag (i + 1)) (G.H_ACK_LINE i hi)
    (a := (P.L (i + 1)).hi) (b := P.τ (i + 1) 0)
    (fun s h1 h2 => (pre G E T (i + 1) hi).2 s h1 h2) t (by omega) t2 (by omega)
  rw [this]; rfl

/-- Stage `i`'s acknowledge pin for phase `j+1`, from stage `i+1`'s phase
`j` through boundary `i+1`'s DACK line. -/
theorem ack_succ (i j : Nat) (hi : i + 1 < P.N)
    (h : ∀ s, P.c (i + 1) j ≤ s → s < P.c (i + 1) (j + 1) →
      ex (r (i + 1)) (a (i + 1)) (q (i + 1)) rst s = Vph j) :
    ∀ t, P.Ain i (j + 1) ≤ t → t < P.Ain i (j + 1 + 1) → a i t = !Vph (j + 1) := by
  have hO := node_of G E T (i + 1) j hi h
  have hR := ge_R E j (i + 1)
  have hl := T.H_RST_LINES i hi
  have ht := tau_lo E T (i + 1) j; have hRp := T.H_R_POS
  have hge := P.ackT_ge' (i + 1) j (P.τ (i + 1) j)
  rw [Vph_succ, Bool.not_not]
  intro t t1 t2
  rw [P.Ain_in i j hi] at t1; rw [P.Ain_in i (j + 1) hi] at t2
  have hgd : P.Ag (i + 1) ≤ t := by omega
  simp only [PN.ackT] at t1 t2
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hv : Vph j = true := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [hj, ite_true] at t1
    simp only [show ¬ ((j + 1) % 2 = 0) by omega, ite_false] at t2
    have g := gap E T (i + 1) j hi; have fl := T.H_ACK_FLUSH i hi
    have ew : P.Won Es Er (i + 1) =
      (P.L (i + 1)).lo + max (P.ER Es (i + 1)) (P.EA Er (i + 1)) := rfl
    have a1 := fmax_le (fun k => (P.Ap (i + 1) k).fst (P.τ (i + 1) j)) (P.τ (i + 1) j + P.ahi (i + 1))
      (P.m (i + 1)) (P.fst_hi_all (i + 1) _)
    have a2 := le_fmin (fun k => (P.Ap (i + 1) k).fst (P.τ (i + 1) (j + 1)))
      (P.τ (i + 1) (j + 1) + P.alo (i + 1)) (P.m (i + 1))
      (P.fst_lo_all (i + 1) _ (tau_pos E T (i + 1) (j + 1)))
    exact orn_hold_true (P.Ap (i + 1)) (P.m (i + 1)) (P.Ag (i + 1)) (G.H_ACK_LINE i hi) hO
      (by omega) t t1 t2 hgd
  · have hv : Vph j = false := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [show ¬ (j % 2 = 0) by omega, ite_false] at t1
    simp only [show (j + 1) % 2 = 0 by omega, ite_true] at t2
    exact orn_hold_false (P.Ap (i + 1)) (P.m (i + 1)) (P.Ag (i + 1)) (G.H_ACK_LINE i hi) hO
      t t1 t2 hgd

/-- The excitation of stage `i` in phase `j` is `Vph j` over the phase. -/
def PhaseOK (i j : Nat) : Prop :=
  ∀ s, P.c i j ≤ s → s < P.c i (j + 1) → ex (r i) (a i) (q i) rst s = Vph j

/-- **(1) The `N`-stage pipe's control is clean, phase by phase.** For every
phase `j` and every stage `i < N`, the excitation equals `Vph j` from the
phase start to the next. Outer induction on `j`, inner induction on `i`
ascending: phase `(i, j)` uses `(i-1, j)` through the request line and
`(i+1, j-1)` through the DACK line, i.e. well-founded on `2j + i`. -/
theorem pipe_ctl : ∀ j i, i < P.N → PhaseOK (P := P) (r := r) (a := a) (q := q) (rst := rst) i j := by
  intro j
  induction j with
  | zero =>
    intro i
    induction i with
    | zero =>
      intro hi
      apply phase_of G E T 0 0 hi (E.H_REQ 0)
      by_cases hl : 0 + 1 < P.N
      · exact ack_zero G E T 0 hl
      · have e : P.N - 1 = 0 := by omega
        have := ack_last E T 0; rw [e] at this; exact this
    | succ i ih =>
      intro hi
      apply phase_of G E T (i + 1) 0 hi (req_of G E T i 0 hi (ih (by omega)))
      by_cases hl : i + 1 + 1 < P.N
      · exact ack_zero G E T (i + 1) hl
      · have e : P.N - 1 = i + 1 := by omega
        have := ack_last E T 0; rw [e] at this; exact this
  | succ j ihj =>
    intro i
    induction i with
    | zero =>
      intro hi
      apply phase_of G E T 0 (j + 1) hi (E.H_REQ (j + 1))
      by_cases hl : 0 + 1 < P.N
      · exact ack_succ G E T 0 j hl (ihj 1 hl)
      · have e : P.N - 1 = 0 := by omega
        have := ack_last E T (j + 1); rw [e] at this; exact this
    | succ i ih =>
      intro hi
      apply phase_of G E T (i + 1) (j + 1) hi (req_of G E T i (j + 1) hi (ih (by omega)))
      by_cases hl : i + 1 + 1 < P.N
      · exact ack_succ G E T (i + 1) j hl (ihj (i + 1 + 1) hl)
      · have e : P.N - 1 = i + 1 := by omega
        have := ack_last E T (j + 1); rw [e] at this; exact this

/-- **(1') Every node is a clean step signal**: low from `L.hi` to its first
edge, then `Vph j` between its `j`-th and `(j+1)`-th edges. -/
theorem nodes_clean (i : Nat) (hi : i < P.N) :
    (∀ t, (P.L i).hi ≤ t → t < P.τ i 0 → O i t = false) ∧
    (∀ j t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j) :=
  ⟨(pre G E T i hi).2, fun j => node_of G E T i j hi (pipe_ctl G E T j i hi)⟩

/-- **(1'') Every internal pin is a clean four-phase signal**: at every
boundary `b = i + 1`, stage `b`'s request pin makes one edge per phase at
`Rin b j`, and stage `b-1`'s acknowledge pin is `!Vph j` on
`[Ain (b-1) j, Ain (b-1) (j+1))`. -/
theorem pins_clean (i : Nat) (hi : i + 1 < P.N) :
    (∀ j t, P.Rin (i + 1) j ≤ t → t < P.Rin (i + 1) (j + 1) → r (i + 1) t = Vph j) ∧
    (∀ j t, P.Ain i j ≤ t → t < P.Ain i (j + 1) → a i t = !Vph j) := by
  refine ⟨fun j => req_of G E T i j hi (pipe_ctl G E T j i (by omega)), fun j => ?_⟩
  cases j with
  | zero => exact ack_zero G E T i hi
  | succ j => exact ack_succ G E T i j hi (pipe_ctl G E T j (i + 1) hi)

end ctl

/-! ## 5. The data path: every token through every stage

Stage `i`'s latch bit `b` (`x i b`) reads `din d x i b`: the environment's
data `d b` at stage 0, stage `i-1`'s latch output `x (i-1) b` after. -/

/-- The data input of stage `i`. -/
def din (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig) : Nat → Nat → Bundling.Sig
  | 0 => d
  | i + 1 => x i

/-- **The data lateness bound** `Dl i b`, relative to stage `i`'s own rise
`τ i (2k)`: token `k`'s value is valid at `x i b` no later than
`τ i (2k) + Dl i b` (`Sx_le`). It is the larger of the enable branch and the
data that rippled through the transparent stages before; the request line
and LUT of each boundary (`Rq.lo + L.lo`) are credited against each data arc
`dhi`. This is the recursion over depth in which the request's lead over the
data grows (`bd_link.v` header; 441 ps measured at N = 4). Integer valued:
the credit may exceed the arcs. -/
def Dl (P : PN) (V : Nat → Win) (Sdr Lag : Nat) : Nat → Nat → Int
  | 0, b => max ((V 0).ehi b : Int) ((Lag : Int) - Sdr - (P.L 0).lo + (V 0).dhi b)
  | i + 1, b => max ((V (i + 1)).ehi b : Int)
      (Dl P V Sdr Lag i b - (P.Rq (i + 1)).lo - (P.L (i + 1)).lo + (V (i + 1)).dhi b)

/-- Start of token `k`'s validity at stage `i`'s latch bit `b` (6c's
`capture` window start, iterated down the pipe). -/
def PN.Sx (P : PN) (V : Nat → Win) (dS : Nat → Nat) (k b : Nat) : Nat → Nat
  | 0 => max (P.τ 0 (2 * k) + (V 0).ehi b) (dS k + (V 0).dhi b)
  | i + 1 => max (P.τ (i + 1) (2 * k) + (V (i + 1)).ehi b) (PN.Sx P V dS k b i + (V (i + 1)).dhi b)

/-- **Data-path hypotheses and per-stage / per-boundary obligations** of the
`N`-stage pipe. All windows `V i` are per stage and per bit. -/
structure DataN (P : PN) (O : Nat → Trace) (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig)
    (val : Nat → Nat → Bool) (dS dE : Nat → Nat) (V : Nat → Win)
    (W Es Er Erel Sdr Lag : Nat) : Prop where
  /-- **H_LATCH i**: each latch bit is 6c's Kleene mux over its pin windows
  (from the real INITs under H_KLEENE_LUT); the enable is the stage's node. -/
  H_LATCH : ∀ i b, i < P.N → b < W → Bundling.LatchRel (din d x i b) (O i) (x i b)
    ((V i).dlo b) ((V i).dhi b) ((V i).elo b) ((V i).ehi b) ((V i).flo b) ((V i).fhi b)
  H_WIN : ∀ i b, i < P.N → b < W → (V i).dlo b ≤ (V i).dhi b ∧ (V i).elo b ≤ (V i).ehi b ∧
    (V i).flo b ≤ (V i).fhi b ∧ 1 ≤ (V i).flo b
  /-- **H_DATA_VALID**: the sender holds token `k` on `[dS k, dE k)`. -/
  H_DATA_VALID : ∀ k b t, b < W → dS k ≤ t → t < dE k → d b t = val k b
  /-- **H_DATA_LEAD** (rule A at the pipe input). -/
  H_DATA_LEAD : ∀ k, dS k + Sdr ≤ P.ρ (2 * k) + Lag
  /-- **H_DATA_REL**: the sender releases token `k` at least `Erel` after
  stage 0's node falls. -/
  H_DATA_REL : ∀ k, P.τ 0 (2 * k + 1) + Erel ≤ dE k
  /-- **H_HOLD0** (rule H at the input boundary). -/
  H_HOLD0 : ∀ b, b < W → (V 0).ehi b ≤ Erel + (V 0).dlo b
  /-- **H_PW i**: stage `i`'s enable high time covers its spread plus one
  latch loop (no rule). -/
  H_PW : ∀ i b, i < P.N → b < W → (V i).ehi b + (V i).fhi b ≤ P.Won Es Er i + (V i).elo b
  /-- **H_SETUP0** (rule I at the input boundary; "not audited" for data
  from a pin). -/
  H_SETUP0 : ∀ b, b < W →
    (V 0).dhi b + (V 0).fhi b + Lag ≤ Sdr + (P.L 0).lo + P.Won Es Er 0 + (V 0).elo b
  /-- **H_I b** (rule I at boundary `b = i + 1`, the SDELAY knob): stage `b`
  closes on the path stage-`(b-1)` rise → its fall (`Won`) → request line
  → stage-`b` LUT → enable branch, no earlier than stage `b-1`'s value
  (lateness `Dl`, which includes the ripple from upstream) has gone through
  stage `b`'s D arc and latch loop. For `b = 1`, `Dl 0` unfolds to 6e's
  `H_I1` and `H_I1_SRC` exactly. -/
  H_I : ∀ i b, i + 1 < P.N → b < W →
    Dl P V Sdr Lag i b + (V (i + 1)).dhi b + (V (i + 1)).fhi b ≤
      ((P.Won Es Er i + (P.Rq (i + 1)).lo + (P.L (i + 1)).lo + (V (i + 1)).elo b : Nat) : Int)
  /-- **H_H b** (rule H at boundary `b = i + 1`, with stage `b`'s DACK slow
  path credit). -/
  H_H : ∀ i b, i + 1 < P.N → b < W →
    (V (i + 1)).ehi b ≤ P.aslow (i + 1) + (P.L i).lo + (V i).elo b +
      (V (i + 1)).dlo b

section data
variable {P : PN} {rst : Trace} {r a O q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
  {d : Nat → Bundling.Sig} {x : Nat → Nat → Bundling.Sig} {val : Nat → Nat → Bool}
  {dS dE : Nat → Nat} {V : Nat → Win} {W Erel Sdr Lag : Nat}

/-- Token `k`'s validity at stage `i` starts no later than
`τ i (2k) + Dl i b`. -/
theorem Sx_le (E : EnvN P (r 0) (a (P.N - 1)) Es Er) (T : TimingN P wh Es Er)
    (hlead : ∀ k, dS k + Sdr ≤ P.ρ (2 * k) + Lag) (k b : Nat) :
    ∀ i, (P.Sx V dS k b i : Int) ≤ (P.τ i (2 * k) : Int) + Dl P V Sdr Lag i b := by
  intro i
  induction i with
  | zero =>
    have := rho_le E T (2 * k); have := hlead k
    simp only [PN.Sx, Dl]; omega
  | succ i ih =>
    have := fwd E T i (2 * k)
    simp only [PN.Sx, Dl] at ih ⊢; omega

variable (G : GatesN P rst r a O q wl wh) (E : EnvN P (r 0) (a (P.N - 1)) Es Er)
  (T : TimingN P wh Es Er) (D : DataN P O d x val dS dE V W Es Er Erel Sdr Lag)
include G E T D

/-- **(2) Every stage latches every token, every bit.** Induction on the
stage: stage `i+1` reads stage `i`'s latched value, valid on
`[Sx i, τ i (2k+2) + elo)`. 6c's `Bundling.capture` unchanged, with the
enable times DERIVED from `nodes_clean`. -/
theorem token (k b : Nat) (hb : b < W) : ∀ i, i < P.N →
    ∀ t, P.Sx V dS k b i ≤ t → t < P.τ i (2 * k + 1 + 1) + (V i).elo b → x i b t = val k b := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hn := (nodes_clean G E T 0 hi).2
    have hon : ∀ t, P.τ 0 (2 * k) ≤ t → t < P.τ 0 (2 * k + 1) → O 0 t = true := by
      intro t u v; have := hn (2 * k) t u v; rwa [Vph_even] at this
    have hoff : ∀ t, P.τ 0 (2 * k + 1) ≤ t → t < P.τ 0 (2 * k + 1 + 1) → O 0 t = false := by
      intro t u v; have := hn (2 * k + 1) t u v; rwa [Vph_odd] at this
    have ⟨hdw, hew, hfw, hpos⟩ := D.H_WIN 0 b hi hb
    have g := gap E T 0 (2 * k) hi; have rl := rho_le E T (2 * k); have l := D.H_DATA_LEAD k
    have pw := D.H_PW 0 b hi hb; have su := D.H_SETUP0 b hb
    have rel := D.H_DATA_REL k; have ho := D.H_HOLD0 b hb
    exact Bundling.capture (d b) (O 0) (x 0 b) _ _ _ _ _ _ (D.H_LATCH 0 b hi hb) hdw hew hfw hpos
      (P.τ 0 (2 * k)) (P.τ 0 (2 * k + 1)) (P.τ 0 (2 * k + 1 + 1)) (dS k) (dE k) (val k b)
      hon hoff (fun t h1 h2 => D.H_DATA_VALID k b t hb h1 h2) (by omega) (by omega)
  | succ i ih =>
    intro hi
    have hn := (nodes_clean G E T (i + 1) hi).2
    have hon : ∀ t, P.τ (i + 1) (2 * k) ≤ t → t < P.τ (i + 1) (2 * k + 1) → O (i + 1) t = true := by
      intro t u v; have := hn (2 * k) t u v; rwa [Vph_even] at this
    have hoff : ∀ t, P.τ (i + 1) (2 * k + 1) ≤ t → t < P.τ (i + 1) (2 * k + 1 + 1) →
        O (i + 1) t = false := by
      intro t u v; have := hn (2 * k + 1) t u v; rwa [Vph_odd] at this
    have ⟨hdw, hew, hfw, hpos⟩ := D.H_WIN (i + 1) b hi hb
    have g1 := gap E T (i + 1) (2 * k) hi; have g0 := gap E T i (2 * k) (by omega)
    have f := fwd E T i (2 * k + 1)
    have sl := Sx_le (V := V) E T D.H_DATA_LEAD k b i
    have bo := back_odd E T i (2 * k + 1) hi (by omega)
    have pw := D.H_PW (i + 1) b hi hb; have iI := D.H_I i b hi hb
    have hH := D.H_H i b hi hb
    exact Bundling.capture (x i b) (O (i + 1)) (x (i + 1) b) _ _ _ _ _ _
      (D.H_LATCH (i + 1) b hi hb) hdw hew hfw hpos
      (P.τ (i + 1) (2 * k)) (P.τ (i + 1) (2 * k + 1)) (P.τ (i + 1) (2 * k + 1 + 1))
      (P.Sx V dS k b i) (P.τ i (2 * k + 1 + 1) + (V i).elo b) (val k b)
      hon hoff (ih (by omega)) (by omega) (by omega)

/-- **(3) The pipe delivers every token.** The last stage's latch bit
carries token `k`'s value from its validity start until the receiver's
acknowledge falls (`γ (2k+1)`); and, under the output-bundling inequality
`Dl (N-1) b ≤ Er` (the consumer's rule), from the receiver's acknowledge
rise `γ (2k)` on. -/
theorem pipe_forward (k b : Nat) (hb : b < W) :
    (∀ t, P.Sx V dS k b (P.N - 1) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b) ∧
    (Dl P V Sdr Lag (P.N - 1) b ≤ (Er : Int) →
      ∀ t, P.γ (2 * k) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b) := by
  have hn := T.H_N_POS
  have g := gam_le E T (2 * k + 1)
  have rc := E.H_RCV (2 * k)
  have sl := Sx_le (V := V) E T D.H_DATA_LEAD k b (P.N - 1)
  refine ⟨fun t h1 h2 => token G E T D k b hb (P.N - 1) (by omega) t h1 (by omega),
    fun o t h1 h2 => token G E T D k b hb (P.N - 1) (by omega) t (by omega) (by omega)⟩

end data

/-! ## 6. Non-vacuity for EVERY `N ≥ 1`: a unit-delay run

All read-time maps are a fixed delay of 1 tick, feedback wires 1, reset
released at 4, sender and receiver latency 3. Stage `i`'s request pin is the
square wave `sq (4 + 2i)` (low before the offset, then 4 high, 4 low, ...),
its node `sq (5 + 2i)`, its feedback `sq (6 + 2i)`, its acknowledge pin
`sq (8 + 2i)`. The derived event times come out of the recursion in closed
form: `c i j = 4 + 2i + 4j`, `τ i j = 5 + 2i + 4j` (`cc_w`, `τ_w`). -/

namespace Wit
open PipeTimed.Wit

/-- The witness run with `N` stages. -/
def Pw (N : Nat) : PN where
  N := N
  R := 4
  L _ := Ret.shift 1
  Rq _ := Ret.shift 1
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ j := 4 + 4 * j
  γ j := 6 + 2 * N + 4 * j

theorem ackT_w (N b j τ : Nat) (h : 1 ≤ τ) : (Pw N).ackT b j τ = τ + 1 := by
  show (if j % 2 = 0 then (Ret.shift 1).fst τ else (Ret.shift 1).fst τ) = _
  rw [fst1 τ h]; split <;> rfl

theorem row_w (N j : Nat) (α : Nat → Nat) (hα : ∀ i, α i ≤ 4 + 2 * i + 4 * j) :
    ∀ i, (Pw N).row j α i = 4 + 2 * i + 4 * j := by
  intro i
  induction i with
  | zero => show max (4 + 4 * j) (α 0) = _; have := hα 0; omega
  | succ i ih =>
    show max ((Ret.shift 1).fst ((Ret.shift 1).fst ((Pw N).row j α i))) (α (i + 1)) = _
    rw [ih, fst1 (4 + 2 * i + 4 * j) (by omega), fst1 (4 + 2 * i + 4 * j + 1) (by omega)]
    have := hα (i + 1); omega

/-- The event-time recursion, solved: `c i j = 4 + 2i + 4j` for every stage
and phase. -/
theorem cc_w (N : Nat) : ∀ j i, (Pw N).cc j i = 4 + 2 * i + 4 * j := by
  intro j
  induction j with
  | zero => exact row_w N 0 (fun _ => 4) (fun i => by omega)
  | succ j ih =>
    apply row_w
    intro i
    show (if i + 1 < N then (Pw N).ackT (i + 1) j ((Ret.shift 1).fst ((Pw N).cc j (i + 1)))
      else 6 + 2 * N + 4 * j) ≤ _
    split
    · rw [ih, fst1 _ (by omega), ackT_w N _ _ _ (by omega)]; omega
    · omega

theorem τ_w (N i j : Nat) : (Pw N).τ i j = 5 + 2 * i + 4 * j := by
  show (Ret.shift 1).fst ((Pw N).cc j i) = _
  rw [cc_w, fst1 (4 + 2 * i + 4 * j) (by omega)]; omega

def rW (i : Nat) : Trace := sq (4 + 2 * i)
def aW (i : Nat) : Trace := sq (8 + 2 * i)
def OW (i : Nat) : Trace := sq (5 + 2 * i)
def qW (i : Nat) : Trace := sq (6 + 2 * i)

theorem sq1 (o t : Nat) (ht : 1 ≤ t) : sq (o + 1) t = sq o (t - 1) := by
  have := sq_shift o 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this

/-- One unit-delay controller with the real `bd_c2n` INIT. -/
theorem ctl_w (o : Nat) (ho : 4 ≤ o) :
    Ctl (sq o) (sq (o + 4)) rstW (sq (o + 1)) (sq (o + 2)) (Ret.shift 1) 1 1 where
  H_LUT_FIFO t ht := by
    show sq (o + 1) t = ex (sq o) (sq (o + 4)) (sq (o + 2)) rstW (t - 1)
    rw [key o (t - 1) ho]; exact sq1 o t ht
  H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
    (fun t => sq_shift (o + 1) 1 t)
  H_LOOP_POS := by decide

theorem gates_w (N : Nat) : GatesN (Pw N) rstW rW aW OW qW (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i _ := by
    have h := ctl_w (4 + 2 * i) (by omega)
    rw [show 4 + 2 * i + 4 = 8 + 2 * i by omega, show 4 + 2 * i + 1 = 5 + 2 * i by omega,
      show 4 + 2 * i + 2 = 6 + 2 * i by omega] at h
    exact h
  H_REQ_LINE i _ t ht := by
    show sq (4 + 2 * (i + 1)) t = sq (5 + 2 * i) (t - 1)
    rw [show 4 + 2 * (i + 1) = 5 + 2 * i + 1 by omega]; exact sq1 _ t ht
  H_ACK_LINE i _ t ht := by
    show sq (8 + 2 * i) t = sq (5 + 2 * (i + 1)) (t - 1)
    rw [show 8 + 2 * i = 5 + 2 * (i + 1) + 1 by omega]
    exact sq1 _ t ht

theorem env_w (N : Nat) (hN : 1 ≤ N) : EnvN (Pw N) (rW 0) (aW ((Pw N).N - 1)) 3 3 where
  H_REQ_LOW0 t h1 h2 := by simp only [Pw] at h1 h2; omega
  H_REQ j t h1 h2 := sq_phase 4 j t h1 (by simp only [Pw] at h2; omega)
  H_ACK_LOW0 t h1 h2 := by
    show sq (8 + 2 * (N - 1)) t = false
    exact sq_pre _ t (by simp only [Pw] at h2; omega)
  H_ACK j t h1 h2 := by
    show sq (8 + 2 * (N - 1)) t = Vph j
    rw [show 8 + 2 * (N - 1) = 6 + 2 * N by omega]
    exact sq_phase _ j t (by simp only [Pw] at h1; omega) (by simp only [Pw] at h2; omega)
  H_SND j := by rw [τ_w]; show 5 + 2 * 0 + 4 * j + 3 ≤ 4 + 4 * (j + 1); omega
  H_RCV j := by rw [τ_w]; show 5 + 2 * (N - 1) + 4 * j + 3 ≤ 6 + 2 * N + 4 * j; omega
  H_RST_EARLY := by show 4 ≤ 4 + 4 * 0; omega

theorem ER_w (N i : Nat) : (Pw N).ER 3 i = 3 := by cases i <;> rfl

theorem EA_w (N i : Nat) : (Pw N).EA 3 i = 3 := by
  unfold PN.EA; split <;> rfl

theorem Won_w (N i : Nat) : (Pw N).Won 3 3 i = 4 := by
  unfold PN.Won; rw [ER_w, EA_w]; rfl

theorem timing_w (N : Nat) (hN : 1 ≤ N) : TimingN (Pw N) (fun _ => 1) 3 3 where
  H_N_POS := hN
  H_R_POS := by show 1 ≤ 4; decide
  H_RST_LONG _ _ := by show 1 + 1 ≤ 4; decide
  H_RST_LINES _ _ := by show 1 + 1 ≤ 4 ∧ 1 + 1 ≤ 4 ∧ 1 ≤ 4; decide
  H_LAT i _ := by rw [ER_w, EA_w]; show 1 + 1 ≤ 1 + min 3 3; decide
  H_ACK_FLUSH i _ := by rw [ER_w, EA_w]; show 1 ≤ 1 + max 3 3 + 1; decide

/-- **Non-vacuity of the control contract, every `N ≥ 1`.** The unit-delay
run satisfies every field of `GatesN`, `EnvN` and `TimingN` at every
instant; every node alternates every 4 ticks, so `pipe_ctl`, `nodes_clean`,
`pins_clean` and `live` speak about a real, live `N`-stage handshake. -/
theorem witness (N : Nat) (hN : 1 ≤ N) :
    GatesN (Pw N) rstW rW aW OW qW (fun _ => 1) (fun _ => 1) ∧
    EnvN (Pw N) (rW 0) (aW ((Pw N).N - 1)) 3 3 ∧ TimingN (Pw N) (fun _ => 1) 3 3 ∧
    (∀ i j, (Pw N).τ i j = 5 + 2 * i + 4 * j) ∧
    (∀ i, OW i (5 + 2 * i) = true ∧ OW i (9 + 2 * i) = false) := by
  refine ⟨gates_w N, env_w N hN, timing_w N hN, τ_w N, fun i => ⟨?_, ?_⟩⟩ <;>
    (unfold OW sq; simp <;> omega)

/-! ### The data path of the witness

One bit; token values alternate (`valW k = (k even)`); the sender as in 6e
(token `k` on `[2 + 8k, 10 + 8k)`). Every latch bit is the real `ODD` INIT as
a transport LUT with unit pin delays (6e's `latch_of`, through 6c's
`odd_latch`). Stage `i`'s output shows token `m` on
`[6 + 2i + 8m, 14 + 2i + 8m)`. -/

/-- Stage `i`'s latch output. -/
def xW (i t : Nat) : Bool := decide (6 + 2 * i ≤ t ∧ (t - (6 + 2 * i)) % 16 < 8)

def VWn : Nat → Win := fun _ => VW

theorem xW_rel0 (t : Nat) : xW 0 t = (if OW 0 (t - 1) then dW (t - 1) else xW 0 (t - 1)) := by
  have e : xW 0 = x0W := by funext u; unfold xW x0W; simp
  rw [e]; exact x0_rel t

theorem xW_rel (i t : Nat) :
    xW (i + 1) t = (if OW (i + 1) (t - 1) then xW i (t - 1) else xW (i + 1) (t - 1)) := by
  unfold OW
  split
  · next h =>
    unfold sq at h; simp at h
    unfold xW; simp only [decide_eq_decide]; omega
  · next h =>
    unfold sq at h; simp at h
    unfold xW; simp only [decide_eq_decide]; omega

theorem Dl_w (N : Nat) : ∀ i b, Dl (Pw N) VWn 2 0 i b = 1 := by
  intro i b
  induction i with
  | zero => show max ((1 : Nat) : Int) (((0 : Nat) : Int) - ((2 : Nat) : Int) - ((1 : Nat) : Int)
      + ((1 : Nat) : Int)) = 1; decide
  | succ i ih =>
    show max ((1 : Nat) : Int) (Dl (Pw N) VWn 2 0 i b - ((1 : Nat) : Int) - ((1 : Nat) : Int)
      + ((1 : Nat) : Int)) = 1
    rw [ih]; decide

set_option linter.unusedSimpArgs false in
theorem data_w (N : Nat) : DataN (Pw N) OW (fun _ => dW) (fun i _ => xW i)
    valW dSW dEW VWn 1 3 3 1 2 0 where
  H_LATCH i _ _ _ := by
    cases i with
    | zero => exact latch_of dW (OW 0) (xW 0) xW_rel0
    | succ i => exact latch_of (xW i) (OW (i + 1)) (xW (i + 1)) (xW_rel i)
  H_WIN _ _ _ _ := by simp [VWn, VW]
  H_DATA_VALID k i t _ h1 h2 := by
    unfold dSW at h1; unfold dEW at h2; unfold dW valW
    simp only [decide_eq_decide]; omega
  H_DATA_LEAD k := by show 2 + 8 * k + 2 ≤ 4 + 4 * (2 * k) + 0; omega
  H_DATA_REL k := by rw [τ_w]; show 5 + 2 * 0 + 4 * (2 * k + 1) + 1 ≤ 10 + 8 * k; omega
  H_HOLD0 _ _ := by simp [VWn, VW]
  H_PW i _ _ _ := by rw [Won_w]; simp [VWn, VW]
  H_SETUP0 _ _ := by rw [Won_w]; simp [VWn, VW, Pw, Ret.shift]
  H_I i b _ _ := by
    rw [Dl_w, Won_w]; simp [VWn, VW, Pw, Ret.shift]
  H_H _ _ _ _ := by simp [VWn, VW, Pw, Ret.shift]

/-- **Non-vacuity, data side, and the theorem at work, every `N ≥ 1`.** The
witness satisfies `DataN` too, so `pipe_forward` applies: the last stage's
output bit carries token `k`'s value from the receiver's acknowledge rise to
its fall, for EVERY token; the values alternate, so a stuck latch cannot
pass. -/
theorem witness_data (N : Nat) (hN : 1 ≤ N) :
    DataN (Pw N) OW (fun _ => dW) (fun i _ => xW i) valW dSW dEW VWn 1 3 3 1 2 0 ∧
    (∀ k t, (Pw N).γ (2 * k) ≤ t → t < (Pw N).γ (2 * k + 1) →
      xW (N - 1) t = decide (k % 2 = 0)) ∧
    xW (N - 1) ((Pw N).γ 0) = true ∧ xW (N - 1) ((Pw N).γ 2) = false := by
  refine ⟨data_w N, fun k t h1 h2 => ?_, ?_, ?_⟩
  · exact (pipe_forward (gates_w N) (env_w N hN) (timing_w N hN) (data_w N) k 0 (by omega)).2
      (by rw [Dl_w]; decide) t h1 h2
  · show decide (6 + 2 * (N - 1) ≤ 6 + 2 * N + 4 * 0 ∧
      (6 + 2 * N + 4 * 0 - (6 + 2 * (N - 1))) % 16 < 8) = true
    rw [decide_eq_true_iff]; omega
  · show decide (6 + 2 * (N - 1) ≤ 6 + 2 * N + 4 * 2 ∧
      (6 + 2 * N + 4 * 2 - (6 + 2 * (N - 1))) % 16 < 8) = false
    rw [decide_eq_false_iff_not]; omega

/-! ### The gate-level DACK chain, instantiated

A unit-delay FIFO FASTRISE chain of `n + 1` elements (`DACK = n + 1`):
`s1 = BUF(s0)`, `s(i+1) = FR_SIDE(s i, s0)`, every arc 1 tick. Its
hypotheses hold at every instant for ANY input trace, so `fastrise_or`
applies; the paths come out with `lo = n + 1` for the full ripple and
`lo = n + 1 - k` for the tap into side stage `k`. Hence a rise crosses in
one hop (`alo = 1`) and a fall takes the whole chain (`aslow = n + 1`):
6e's FASTRISE reading, now derived from the real INITs. -/

/-- The chain's nets for input `x`. -/
def chS (x : Trace) : Nat → Trace
  | 0 => x
  | 1 => fun t => x (t - 1)
  | i + 2 => fun t => chS x (i + 1) (t - 1) || x (t - 1)

/-- Unit arcs everywhere. -/
abbrev u1 : Ret := Ret.shift 1

theorem cpath_lo : ∀ n k, k ≤ n →
    (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo = (if k = 0 then n + 1 else n + 1 - k) := by
  intro n
  induction n with
  | zero => intro k hk; have : k = 0 := by omega
            subst this; rfl
  | succ n ih =>
    intro k hk
    by_cases h : k ≤ n
    · have e : cpath u1 (fun _ => u1) (fun _ => u1) (n + 1) k =
          Ret.comp (cpath u1 (fun _ => u1) (fun _ => u1) n k) u1 := by
        simp only [cpath, h, ite_true]
      rw [e]; show (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo + 1 = _
      rw [ih k h]; split <;> omega
    · have e : cpath u1 (fun _ => u1) (fun _ => u1) (n + 1) k = u1 := by
        simp only [cpath, h, ite_false]
      rw [e]; show 1 = _; split <;> omega

/-- **The real FASTRISE chain is an OR line, and its DACK credit is the
whole chain.** For every input trace `x` and every chain length `n + 1 ≥ 2`:
the output is the OR of `n + 1` FIFO copies of `x`; the fastest has `lo = 1`
(a rise crosses in one hop), the slowest `lo = n + 1` (a fall ripples
through every element). -/
theorem chain_w (x : Trace) (n : Nat) (hn : 1 ≤ n) :
    (∀ t, cguard u1 (fun _ => u1) (fun _ => u1) n ≤ t →
      chS x (n + 1) t = orAll (fun k => x ((cpath u1 (fun _ => u1) (fun _ => u1) n k).σ t)) n) ∧
    fmin (fun k => (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo) n = 1 ∧
    fmax (fun k => (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo) n = n + 1 := by
  refine ⟨fastrise_or (chS x) u1 (fun _ => u1) (fun _ => u1) (n + 1) ?_ ?_ n (Nat.le_refl _), ?_, ?_⟩
  · intro t _; rw [Bundling.buf_bin]; rfl
  · intro i h1 _ t _
    rw [fr_bin]
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rfl
  · have h1 := fmin_le_of (fun k => (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo) 1 n n
      (Nat.le_refl _) (by rw [cpath_lo n n (Nat.le_refl _)]; split <;> omega)
    have h2 := le_fmin (fun k => (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo) 1 n
      (fun k hk => by rw [cpath_lo n k hk]; split <;> omega)
    omega
  · have h1 := le_fmax_of (fun k => (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo) (n + 1) n 0
      (Nat.zero_le _) (by rw [cpath_lo n 0 (Nat.zero_le _)]; simp)
    have h2 := fmax_le (fun k => (cpath u1 (fun _ => u1) (fun _ => u1) n k).lo) (n + 1) n
      (fun k hk => by rw [cpath_lo n k hk]; split <;> omega)
    omega

/-- The witness's acknowledge lines ARE the real chain with `DACK = 1` (one
`LUT1` buffer, unit arc): its one path and guard are `fastrise_or`'s. -/
theorem witness_dack1 (N b : Nat) :
    (Pw N).m b = 0 ∧ (Pw N).Ap b 0 = cpath u1 (fun _ => u1) (fun _ => u1) 0 0 ∧
    (Pw N).Ag b = cguard u1 (fun _ => u1) (fun _ => u1) 0 :=
  ⟨rfl, rfl, rfl⟩

end Wit

end Formal.Cells.PipeTimedN
