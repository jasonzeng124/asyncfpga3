import Formal.Cells.PipeTimedN
import Formal.Cells.PipePerPin

/-!
# Track 6, probe 6h: non-degenerate joint witnesses for the timed pipe

Audit P3 row 3 (`audit/findings/P3.md`, `audit/lean/P3/PipeNWit.lean`)
showed that `PipeTimedN.Wit.witness` is a TIE run: in it the request and the
acknowledge reach every controller in the same tick, so `bd_c2n =
C(req, !ack)` never sees disagreeing inputs and never holds through its
feedback. The auditor built a non-degenerate CONTROL-side witness
(`Aud.witness_g`: LUT 2, request line 3, DACK 1, feedback 1). Still open:
a data-side witness with non-unit delays, and a joint witness with
`DACK ≥ 2`. This file builds, for EVERY `N ≥ 1`:

* **W1** (`W1.witness`): the auditor's control realisation, re-derived here
  (not imported), PLUS a non-unit data path (latch D arc 3 in window [2,4],
  enable arc 2 in [1,3], own loop 2 in [1,2]): `GatesN ∧ EnvN ∧ TimingN ∧
  DataN` jointly, `pipe_forward` applied, the C-element holds through its
  feedback in every phase of every stage (`W1.hold`), and every latch holds
  through its own loop while its data input already shows the next token
  (`W1.latch_hold`).
* **W2** (`W2.witness`): the same with `DACK = 2`, the acknowledge line
  BUILT from the real FASTRISE chain (`LUT1 2'h2`, arc 2; `LUT2 4'hE`,
  chain arc 2, tap arc 1) and discharged by `PipeTimedN.fastrise_or`: rise
  latency 1, fall latency 4 (`W2.ack_latency`). The C-element holds 4 ticks
  after each acknowledge rise and 1 tick after each fall (`W2.hold_rise`,
  `W2.hold_fall`).
* **W3** (`W3.witness`): the per-pin model of `PipePerPin`, request pin 1,
  acknowledge pin 2, **feedback pin 3 (slowest)**, reset pin 1, tree 2,
  request line 3, the same DACK = 2 chain, the same non-unit data path:
  `GatesP ∧ EnvP ∧ TimingP ∧ DataP`, `pipe_forward` applied, the select-level
  excitation holds through the feedback select 5 ticks per rise and 2 per
  fall (`W3.hold_rise`, `W3.hold_fall`).

Every gate relation is the real INIT (`bd_c2n` through `CElemTiming.exc`,
the latch `ODD` through `Bundling.transport_gate`, the DACK chain through
`fastrise_or`), evaluated with `lutB`. Core Lean only.
-/

namespace Formal.Cells.PipeWitness
open Formal.Cells Formal.Cells.PipeTimed Formal.Cells.PipeTimedN

/-! ## 0. Shared helpers -/

/-- Close a Boolean equation between `decide`-built wave expressions by
turning it into a Presburger formula. -/
macro "bw" : tactic => `(tactic| (rw [Bool.eq_iff_iff]; simp [decide_eq_false_iff_not] <;> omega))

/-- **A transport ODD latch with NON-UNIT, unequal pin delays is a 6c
`LatchRel`.** The real `bd_latch` odd-bit INIT `B8B8…` with the data pin read
`a` ticks ago, the enable `e`, its own output `f`, each inside its window. -/
theorem latchT (dd en q : Bundling.Sig) (a e f dlo dhi elo ehi flo fhi : Nat)
    (ha1 : dlo ≤ a) (ha2 : a ≤ dhi) (he1 : elo ≤ e) (he2 : e ≤ ehi)
    (hf1 : flo ≤ f) (hf2 : f ≤ fhi)
    (h : ∀ t, q t = (if en (t - e) then dd (t - a) else q (t - f))) :
    Bundling.LatchRel dd en q dlo dhi elo ehi flo fhi := by
  apply Bundling.odd_latch
  apply Bundling.transport_gate Bundling.ODD
    [(dd, a, dlo, dhi), (en, e, elo, ehi), (q, f, flo, fhi), (Bundling.zero, 0, 0, 0),
     (Bundling.zero, 0, 0, 0), (Bundling.zero, 0, 0, 0)] q
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ha1, ha2⟩
    · exact ⟨he1, he2⟩
    · exact ⟨hf1, hf2⟩
    all_goals exact ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  · intro t
    show q t = lutB Bundling.ODD [dd (t - a), en (t - e), q (t - f), false, false, false]
    rw [Bundling.odd_bin]; exact h t

theorem shσ (d t : Nat) : (Ret.shift d).σ t = t - d := rfl

theorem fst_shift (d c : Nat) (h : 1 ≤ c) : (Ret.shift d).fst c = c + d := Ret.fst_shift d c h

theorem fst_comp_shift (a b c : Nat) (h : 1 ≤ c) :
    (Ret.comp (Ret.shift a) (Ret.shift b)).fst c = c + (a + b) := by
  have h1 : c + (a + b) ≤ (Ret.comp (Ret.shift a) (Ret.shift b)).fst c := Ret.fst_lo (Ret.comp (Ret.shift a) (Ret.shift b)) h
  have h2 : (Ret.comp (Ret.shift a) (Ret.shift b)).fst c ≤ c + (a + b) := Ret.fst_le _ c
  omega

/-- Half-period-12 square wave: low before `o`, then 12 high, 12 low, … -/
def sq12 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 24 < 12)
/-- Reset high on `[0, 6)`. -/
def rst6 (t : Nat) : Bool := decide (t < 6)
/-- Token values alternate: never the reset value for every token, so a stuck
latch cannot pass. -/
def val (k _ : Nat) : Bool := decide (k % 2 = 0)

/-! ### The real FASTRISE chain with `DACK = 2`, non-unit arcs

`s1 = LUT1 #(.INIT(2'h2)) (s0)` through arc `B` (2 ticks), then
`s2 = LUT2 #(.INIT(4'hE)) (I0 = s1, I1 = s0)` with chain arc `C` (2 ticks)
and tap arc `U` (1 tick). A rise crosses by the tap (1 tick), a fall must
ripple (4 ticks). -/

abbrev cB : Ret := Ret.shift 2
abbrev cC : Nat → Ret := fun _ => Ret.shift 2
abbrev cU : Nat → Ret := fun _ => Ret.shift 1

/-- The chain's nets for input `x` (transport arcs). -/
def chs (x : Trace) : Nat → Trace
  | 0 => x
  | 1 => fun t => x (t - 2)
  | _ => fun t => x (t - 2 - 2) || x (t - 1)

/-- The two FIFO copies of the chain: the full ripple (4) and the tap (1). -/
theorem cp0 : cpath cB cC cU 1 0 = Ret.comp cB (Ret.shift 2) := rfl
theorem cp1 : cpath cB cC cU 1 1 = Ret.shift 1 := rfl
theorem cg : cguard cB cC cU 1 = 5 := rfl

/-- **The DACK = 2 chain, gate by gate, is the OR of its two copies**:
`PipeTimedN.fastrise_or` applied to the real INITs `BUF`, `FR_SIDE`. -/
theorem chain2 (x : Trace) :
    ∀ t, cguard cB cC cU 1 ≤ t → chs x 2 t = orAll (fun k => x ((cpath cB cC cU 1 k).σ t)) 1 :=
  fastrise_or (chs x) cB cC cU 2
    (fun t _ => by show x (t - 2) = lutB Bundling.BUF [x (t - 2)]; rw [Bundling.buf_bin])
    (fun i h1 h2 t _ => by
      have e : i = 1 := by omega
      subst e
      show (x (t - 2 - 2) || x (t - 1)) = lutB Bundling.FR_SIDE [x (t - 2 - 2), x (t - 1)]
      rw [fr_bin])
    1 (Nat.le_refl _)

/-! ## 1. W1: the auditor's control realisation, re-derived, plus a non-unit data path

LUT 2, request line 3, DACK 1, feedback wire 1, reset 6, half-period 12,
sender and receiver latency 6. Stage `i`: request pin `sq12 (6+5i)`, node
`sq12 (8+5i)`, feedback `sq12 (9+5i)`, acknowledge pin `sq12 (14+5i)`.
Inside the pipe the acknowledge arrives 4 ticks before the request. -/

namespace W1

def P (N : Nat) : PN where
  N := N
  R := 6
  L _ := Ret.shift 2
  Rq _ := Ret.shift 3
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ j := 6 + 12 * j
  γ j := 14 + 5 * (N - 1) + 12 * j

theorem ackT_e (N b j τ : Nat) (h : 1 ≤ τ) : (P N).ackT b j τ = τ + 1 := by
  show (if j % 2 = 0 then (Ret.shift 1).fst τ else (Ret.shift 1).fst τ) = _
  rw [fst_shift 1 τ h]; split <;> rfl

theorem row_e (N j : Nat) (α : Nat → Nat) (hα : ∀ i, α i ≤ 6 + 5 * i + 12 * j) :
    ∀ i, (P N).row j α i = 6 + 5 * i + 12 * j := by
  intro i
  induction i with
  | zero => show max (6 + 12 * j) (α 0) = _; have := hα 0; omega
  | succ i ih =>
    show max ((Ret.shift 3).fst ((Ret.shift 2).fst ((P N).row j α i))) (α (i + 1)) = _
    rw [ih, fst_shift 2 _ (by omega), fst_shift 3 _ (by omega)]
    have := hα (i + 1); omega

theorem cc_e (N : Nat) : ∀ j i, (P N).cc j i = 6 + 5 * i + 12 * j := by
  intro j
  induction j with
  | zero => exact row_e N 0 (fun _ => 6) (fun i => by omega)
  | succ j ih =>
    apply row_e
    intro i
    show (if i + 1 < N then (P N).ackT (i + 1) j ((Ret.shift 2).fst ((P N).cc j (i + 1)))
      else 14 + 5 * (N - 1) + 12 * j) ≤ _
    split
    · rw [ih, fst_shift 2 _ (by omega), ackT_e N _ _ _ (by omega)]; omega
    · omega

/-- The derived event times in closed form. -/
theorem τ_e (N i j : Nat) : (P N).τ i j = 8 + 5 * i + 12 * j := by
  show (Ret.shift 2).fst ((P N).cc j i) = _
  rw [cc_e, fst_shift 2 _ (by omega)]; omega

def r (i : Nat) : Trace := sq12 (6 + 5 * i)
def O (i : Nat) : Trace := sq12 (8 + 5 * i)
def q (i : Nat) : Trace := sq12 (9 + 5 * i)
def a (i : Nat) : Trace := sq12 (14 + 5 * i)

theorem gates (N : Nat) : GatesN (P N) rst6 r a O q (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i _ := {
    H_LUT_FIFO := fun t _ => by
      show sq12 (8 + 5 * i) t = ex (sq12 (6 + 5 * i)) (sq12 (14 + 5 * i)) (sq12 (9 + 5 * i)) rst6 (t - 2)
      unfold ex rst6; rw [CElemTiming.c2n_eq]; unfold sq12; bw
    H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
      (fun t => by show sq12 (9 + 5 * i) (t + 1) = sq12 (8 + 5 * i) t; unfold sq12; bw)
    H_LOOP_POS := by show 1 ≤ 2 + 1; decide }
  H_REQ_LINE i _ t _ := by
    show sq12 (6 + 5 * (i + 1)) t = sq12 (8 + 5 * i) (t - 3); unfold sq12; bw
  H_ACK_LINE i _ t _ := by
    show sq12 (14 + 5 * i) t = sq12 (8 + 5 * (i + 1)) (t - 1); unfold sq12; bw

theorem env (N : Nat) (_hN : 1 ≤ N) : EnvN (P N) (r 0) (a ((P N).N - 1)) 6 6 where
  H_REQ_LOW0 t h1 h2 := by
    simp only [P] at h1 h2; show sq12 (6 + 5 * 0) t = false; unfold sq12; bw
  H_REQ j t h1 h2 := by
    simp only [P] at h1 h2; show sq12 (6 + 5 * 0) t = Vph j
    unfold sq12 Vph LinkTimed.Vph; bw
  H_ACK_LOW0 t h1 h2 := by
    simp only [P] at h1 h2; show sq12 (14 + 5 * (N - 1)) t = false; unfold sq12; bw
  H_ACK j t h1 h2 := by
    simp only [P] at h1 h2; show sq12 (14 + 5 * (N - 1)) t = Vph j
    unfold sq12 Vph LinkTimed.Vph; bw
  H_SND j := by rw [τ_e]; show 8 + 5 * 0 + 12 * j + 6 ≤ 6 + 12 * (j + 1); omega
  H_RCV j := by rw [τ_e]; show 8 + 5 * (N - 1) + 12 * j + 6 ≤ 14 + 5 * (N - 1) + 12 * j; omega
  H_RST_EARLY := by show 6 ≤ 6 + 12 * 0; omega

theorem ER_e (N i : Nat) : (P N).ER 6 i = 6 := by cases i <;> rfl
theorem EA_e (N i : Nat) : (P N).EA 6 i = 6 := by unfold PN.EA; split <;> rfl
theorem Won_e (N i : Nat) : (P N).Won 6 6 i = 8 := by
  unfold PN.Won; rw [ER_e, EA_e]; rfl

theorem timing (N : Nat) (hN : 1 ≤ N) : TimingN (P N) (fun _ => 1) 6 6 where
  H_N_POS := hN
  H_R_POS := by show 1 ≤ 6; decide
  H_RST_LONG _ _ := by show 2 + 1 ≤ 6; decide
  H_RST_LINES _ _ := by show 2 + 3 ≤ 6 ∧ 2 + 1 ≤ 6 ∧ 1 ≤ 6; decide
  H_LAT i _ := by rw [ER_e, EA_e]; show 2 + 1 ≤ 2 + min 6 6; decide
  H_ACK_FLUSH i _ := by rw [ER_e, EA_e]; show 1 ≤ 2 + max 6 6 + 1; decide

/-- **Not a tie** (model times): inside the pipe, the acknowledge pin of
stage `i` reaches phase `j+1` at `14 + 5i + 12j`, the request at
`18 + 5i + 12j`: 4 ticks of hold. -/
theorem no_tie (N i j : Nat) (hi : i + 1 < N) :
    (P N).Ain i (j + 1) = 14 + 5 * i + 12 * j ∧ (P N).Rin i (j + 1) = 18 + 5 * i + 12 * j := by
  refine ⟨?_, ?_⟩
  · rw [PN.Ain_in _ _ _ hi, τ_e, ackT_e _ _ _ _ (by omega)]; omega
  · cases i with
    | zero => show 6 + 12 * (j + 1) = _; omega
    | succ i =>
      show (Ret.shift 3).fst ((P N).τ i (j + 1)) = _
      rw [τ_e, fst_shift 3 _ (by omega)]; omega

/-- **The C-element HOLDS through its feedback**, every stage, every phase:
at `s = 15 + 5i + 12j` (inside the window of `no_tie`) request, acknowledge
and feedback all read `Vph j`, so `C(req, !ack)` has disagreeing inputs; the
real INIT outputs `Vph j`, and with the feedback pin flipped it would output
`!Vph j`: the output is decided by the feedback pin alone. -/
theorem hold (i j : Nat) :
    r i (15 + 5 * i + 12 * j) = Vph j ∧ a i (15 + 5 * i + 12 * j) = Vph j ∧
    q i (15 + 5 * i + 12 * j) = Vph j ∧ ex (r i) (a i) (q i) rst6 (15 + 5 * i + 12 * j) = Vph j ∧
    CElemTiming.exc CElemTiming.INIT_c2n (r i (15 + 5 * i + 12 * j)) (a i (15 + 5 * i + 12 * j))
      (!q i (15 + 5 * i + 12 * j)) (rst6 (15 + 5 * i + 12 * j)) = !Vph j := by
  unfold r a q ex rst6 Vph LinkTimed.Vph
  rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq]
  unfold sq12
  refine ⟨by bw, by bw, by bw, by bw, by bw⟩

/-! ### W1 data path: one bit, non-unit, unequal latch arcs

Sender: token `k` on `[2 + 24k, 26 + 24k)`, values alternating. Each latch
bit is the real ODD INIT reading its data 3 ticks ago (window [2,4]), its
enable (the stage's node) 2 ticks ago (window [1,3]) and its own output 2
ticks ago (window [1,2]). Stage `i` shows token `k` on
`[10 + 5i + 24k, 34 + 5i + 24k)`. -/

def d (t : Nat) : Bool := decide (2 ≤ t ∧ (t - 2) % 48 < 24)
def x (i t : Nat) : Bool := decide (10 + 5 * i ≤ t ∧ (t - (10 + 5 * i)) % 48 < 24)
def dS (k : Nat) : Nat := 2 + 24 * k
def dE (k : Nat) : Nat := 26 + 24 * k
def V : Win := ⟨fun _ => 2, fun _ => 4, fun _ => 1, fun _ => 3, fun _ => 1, fun _ => 2⟩

theorem x_rel0 (t : Nat) : x 0 t = (if O 0 (t - 2) then d (t - 3) else x 0 (t - 2)) := by
  unfold O
  split
  · next h => unfold sq12 at h; simp at h; unfold x d; bw
  · next h => unfold sq12 at h; simp at h; unfold x; bw

theorem x_rel (i t : Nat) :
    x (i + 1) t = (if O (i + 1) (t - 2) then x i (t - 3) else x (i + 1) (t - 2)) := by
  unfold O
  split
  · next h => unfold sq12 at h; simp at h; unfold x; bw
  · next h => unfold sq12 at h; simp at h; unfold x; bw

theorem Dl_e (N : Nat) : ∀ i b, Dl (P N) (fun _ => V) 4 0 i b = 3 := by
  intro i b
  induction i with
  | zero => simp [Dl, V, P, Ret.shift]; decide
  | succ i ih => simp only [Dl, ih]; simp [V, P, Ret.shift]; decide

theorem data (N : Nat) : DataN (P N) O (fun _ => d) (fun i _ => x i) val dS dE (fun _ => V)
    1 6 6 6 4 0 where
  H_LATCH i _ _ _ := by
    cases i with
    | zero => exact latchT d (O 0) (x 0) 3 2 2 2 4 1 3 1 2 (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) x_rel0
    | succ i => exact latchT (x i) (O (i + 1)) (x (i + 1)) 3 2 2 2 4 1 3 1 2 (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (x_rel i)
  H_WIN _ _ _ _ := by simp [V]
  H_DATA_VALID k _ t _ h1 h2 := by
    unfold dS at h1; unfold dE at h2; unfold d val; bw
  H_DATA_LEAD k := by show 2 + 24 * k + 4 ≤ 6 + 12 * (2 * k) + 0; omega
  H_DATA_REL k := by rw [τ_e]; show 8 + 5 * 0 + 12 * (2 * k + 1) + 6 ≤ 26 + 24 * k; omega
  H_HOLD0 _ _ := by simp [V]
  H_PW i _ _ _ := by rw [Won_e]; simp [V]
  H_SETUP0 _ _ := by rw [Won_e]; simp [V, P, Ret.shift]
  H_I i b _ _ := by rw [Dl_e, Won_e]; simp [V, P, Ret.shift]
  H_H _ _ _ _ := by show 3 ≤ 1 + 2 + 1 + 2; decide

/-- **The latch HOLDS through its own loop**, every stage, every token: at
`t = 33 + 5i + 24k` the enable pin reads closed, the data pin already reads
token `k+1`, and the output still shows token `k`. -/
theorem latch_hold (i k : Nat) :
    O i (33 + 5 * i + 24 * k - 2) = false ∧
    din (fun _ => d) (fun i _ => x i) i 0 (33 + 5 * i + 24 * k - 3) = val (k + 1) 0 ∧
    x i (33 + 5 * i + 24 * k) = val k 0 ∧ val (k + 1) 0 = !val k 0 := by
  cases i with
  | zero => unfold O d x val sq12; refine ⟨by bw, ?_, by bw, by bw⟩; show d _ = _; unfold d; bw
  | succ i =>
    refine ⟨by unfold O sq12; bw, ?_, by unfold x val; bw, by unfold val; bw⟩
    show x i _ = _; unfold x val; bw

/-- **W1: joint non-vacuity, every `N ≥ 1`, non-unit unequal delays on both
the control and the data side, the C-element and the latches exercised in
their hold states, and `pipe_forward` at work.** -/
theorem witness (N : Nat) (hN : 1 ≤ N) :
    GatesN (P N) rst6 r a O q (fun _ => 1) (fun _ => 1) ∧
    EnvN (P N) (r 0) (a ((P N).N - 1)) 6 6 ∧ TimingN (P N) (fun _ => 1) 6 6 ∧
    DataN (P N) O (fun _ => d) (fun i _ => x i) val dS dE (fun _ => V) 1 6 6 6 4 0 ∧
    (∀ k t, (P N).γ (2 * k) ≤ t → t < (P N).γ (2 * k + 1) → x (N - 1) t = decide (k % 2 = 0)) ∧
    (∀ i j, i < N → ex (r i) (a i) (q i) rst6 (15 + 5 * i + 12 * j) = Vph j ∧
      CElemTiming.exc CElemTiming.INIT_c2n (r i (15 + 5 * i + 12 * j)) (a i (15 + 5 * i + 12 * j))
        (!q i (15 + 5 * i + 12 * j)) (rst6 (15 + 5 * i + 12 * j)) = !Vph j) ∧
    (∀ i k, i < N → x i (33 + 5 * i + 24 * k) = val k 0 ∧
      din (fun _ => d) (fun i _ => x i) i 0 (33 + 5 * i + 24 * k - 3) = !val k 0) := by
  refine ⟨gates N, env N hN, timing N hN, data N, fun k t h1 h2 => ?_,
    fun i j _ => ⟨(hold i j).2.2.2.1, (hold i j).2.2.2.2⟩, fun i k _ => ?_⟩
  · exact (pipe_forward (gates N) (env N hN) (timing N hN) (data N) k 0 (by omega)).2
      (by rw [Dl_e]; decide) t h1 h2
  · have h := latch_hold i k
    exact ⟨h.2.2.1, by rw [h.2.1, h.2.2.2]⟩

end W1

/-! ## 2. W2: `DACK = 2` (the real FASTRISE chain, rise 1, fall 4)

As W1, but each acknowledge line is the gate-level chain `chs` of the next
stage's node (`chain2`), so the acknowledge rises 1 tick and falls 4 ticks
after the node edge. The receiver behaves as a virtual stage `N` behind the
same chain. -/

namespace W2

def P (N : Nat) : PN where
  N := N
  R := 6
  L _ := Ret.shift 2
  Rq _ := Ret.shift 3
  m _ := 1
  Ap _ k := cpath cB cC cU 1 k
  Ag _ := cguard cB cC cU 1
  ρ j := 6 + 12 * j
  γ j := 9 + 5 * N + 12 * j + 3 * (j % 2)

theorem ackT_e (N b j τ : Nat) (h : 1 ≤ τ) :
    (P N).ackT b j τ = τ + (if j % 2 = 0 then 1 else 4) := by
  show (if j % 2 = 0 then min ((cpath cB cC cU 1 0).fst τ) ((cpath cB cC cU 1 1).fst τ)
    else max ((cpath cB cC cU 1 0).fst τ) ((cpath cB cC cU 1 1).fst τ)) = _
  rw [cp0, cp1, fst_comp_shift 2 2 τ h, fst_shift 1 τ h]
  split <;> omega

theorem alo_e (N b : Nat) : (P N).alo b = 1 := rfl
theorem ahi_e (N b : Nat) : (P N).ahi b = 4 := rfl
theorem aslow_e (N b : Nat) : (P N).aslow b = 4 := rfl

theorem row_e (N j : Nat) (α : Nat → Nat) (hα : ∀ i, α i ≤ 6 + 5 * i + 12 * j) :
    ∀ i, (P N).row j α i = 6 + 5 * i + 12 * j := by
  intro i
  induction i with
  | zero => show max (6 + 12 * j) (α 0) = _; have := hα 0; omega
  | succ i ih =>
    show max ((Ret.shift 3).fst ((Ret.shift 2).fst ((P N).row j α i))) (α (i + 1)) = _
    rw [ih, fst_shift 2 _ (by omega), fst_shift 3 _ (by omega)]
    have := hα (i + 1); omega

theorem cc_e (N : Nat) : ∀ j i, (P N).cc j i = 6 + 5 * i + 12 * j := by
  intro j
  induction j with
  | zero => exact row_e N 0 (fun _ => 6) (fun i => by omega)
  | succ j ih =>
    apply row_e
    intro i
    show (if i + 1 < N then (P N).ackT (i + 1) j ((Ret.shift 2).fst ((P N).cc j (i + 1)))
      else 9 + 5 * N + 12 * j + 3 * (j % 2)) ≤ _
    split
    · rw [ih, fst_shift 2 _ (by omega), ackT_e N _ _ _ (by omega)]; split <;> omega
    · omega

theorem τ_e (N i j : Nat) : (P N).τ i j = 8 + 5 * i + 12 * j := by
  show (Ret.shift 2).fst ((P N).cc j i) = _
  rw [cc_e, fst_shift 2 _ (by omega)]; omega

def r (i : Nat) : Trace := sq12 (6 + 5 * i)
def O (i : Nat) : Trace := sq12 (8 + 5 * i)
def q (i : Nat) : Trace := sq12 (9 + 5 * i)
/-- Stage `i`'s acknowledge pin: the DACK = 2 chain's output on stage
`i + 1`'s node (for `i = N - 1`, the receiver's virtual stage `N`). -/
def a (i : Nat) : Trace := chs (O (i + 1)) 2

theorem gates (N : Nat) : GatesN (P N) rst6 r a O q (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i _ := {
    H_LUT_FIFO := fun t _ => by
      show sq12 (8 + 5 * i) t = ex (sq12 (6 + 5 * i))
        (fun u => sq12 (8 + 5 * (i + 1)) (u - 2 - 2) || sq12 (8 + 5 * (i + 1)) (u - 1))
        (sq12 (9 + 5 * i)) rst6 (t - 2)
      unfold ex rst6; rw [CElemTiming.c2n_eq]; unfold sq12; bw
    H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
      (fun t => by show sq12 (9 + 5 * i) (t + 1) = sq12 (8 + 5 * i) t; unfold sq12; bw)
    H_LOOP_POS := by show 1 ≤ 2 + 1; decide }
  H_REQ_LINE i _ t _ := by
    show sq12 (6 + 5 * (i + 1)) t = sq12 (8 + 5 * i) (t - 3); unfold sq12; bw
  H_ACK_LINE i _ t ht := chain2 (O (i + 1)) t ht

theorem env (N : Nat) (hN : 1 ≤ N) : EnvN (P N) (r 0) (a ((P N).N - 1)) 6 6 where
  H_REQ_LOW0 t h1 h2 := by
    simp only [P] at h1 h2; show sq12 (6 + 5 * 0) t = false; unfold sq12; bw
  H_REQ j t h1 h2 := by
    simp only [P] at h1 h2; show sq12 (6 + 5 * 0) t = Vph j
    unfold sq12 Vph LinkTimed.Vph; bw
  H_ACK_LOW0 t h1 h2 := by
    simp only [P] at h1 h2
    show (sq12 (8 + 5 * (N - 1 + 1)) (t - 2 - 2) || sq12 (8 + 5 * (N - 1 + 1)) (t - 1)) = false
    unfold sq12; bw
  H_ACK j t h1 h2 := by
    simp only [P] at h1 h2
    show (sq12 (8 + 5 * (N - 1 + 1)) (t - 2 - 2) || sq12 (8 + 5 * (N - 1 + 1)) (t - 1)) = Vph j
    unfold sq12 Vph LinkTimed.Vph; bw
  H_SND j := by rw [τ_e]; show 8 + 5 * 0 + 12 * j + 6 ≤ 6 + 12 * (j + 1); omega
  H_RCV j := by
    rw [τ_e]; show 8 + 5 * (N - 1) + 12 * j + 6 ≤ 9 + 5 * N + 12 * j + 3 * (j % 2); omega
  H_RST_EARLY := by show 6 ≤ 6 + 12 * 0; omega

theorem ER_e (N i : Nat) : (P N).ER 6 i = 6 := by cases i <;> rfl
theorem EA_e (N i : Nat) : (P N).EA 6 i = 6 := by unfold PN.EA; split <;> rfl
theorem Won_e (N i : Nat) : (P N).Won 6 6 i = 8 := by
  unfold PN.Won; rw [ER_e, EA_e]; rfl

theorem timing (N : Nat) (hN : 1 ≤ N) : TimingN (P N) (fun _ => 1) 6 6 where
  H_N_POS := hN
  H_R_POS := by show 1 ≤ 6; decide
  H_RST_LONG _ _ := by show 2 + 1 ≤ 6; decide
  H_RST_LINES i _ := by rw [ahi_e]; show 2 + 3 ≤ 6 ∧ 2 + 4 ≤ 6 ∧ 5 ≤ 6; decide
  H_LAT i _ := by rw [ER_e, EA_e]; show 2 + 1 ≤ 2 + min 6 6; decide
  H_ACK_FLUSH i _ := by rw [ER_e, EA_e, ahi_e, alo_e]; show 4 ≤ 2 + max 6 6 + 1; decide

/-- **Rise and fall latencies differ** (model times, inside the pipe): the
acknowledge pin follows stage `i+1`'s rise 1 tick later (tap) and its fall
4 ticks later (ripple), and in both cases still arrives before the request
(4 ticks and 1 tick of hold). -/
theorem ack_latency (N i k : Nat) (hi : i + 1 < N) :
    (P N).Ain i (2 * k + 1) = (P N).τ (i + 1) (2 * k) + 1 ∧
    (P N).Ain i (2 * k + 2) = (P N).τ (i + 1) (2 * k + 1) + 4 ∧
    (P N).Ain i (2 * k + 1) + 4 = (P N).Rin i (2 * k + 1) ∧
    (P N).Ain i (2 * k + 2) + 1 = (P N).Rin i (2 * k + 2) := by
  have hR : ∀ j, (P N).Rin i (j + 1) = 18 + 5 * i + 12 * j := by
    intro j
    cases i with
    | zero => show 6 + 12 * (j + 1) = _; omega
    | succ i =>
      show (Ret.shift 3).fst ((P N).τ i (j + 1)) = _
      rw [τ_e, fst_shift 3 _ (by omega)]; omega
  have hA : ∀ j, (P N).Ain i (j + 1) = (P N).τ (i + 1) j + (if j % 2 = 0 then 1 else 4) := by
    intro j; rw [PN.Ain_in _ _ _ hi, ackT_e _ _ _ _ (by rw [τ_e]; omega)]
  rw [hR, show 2 * k + 2 = (2 * k + 1) + 1 by omega, hR, hA, hA, τ_e, τ_e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split <;> omega

/-- **The C-element holds after an acknowledge RISE** (4 ticks; here at
`15 + 5i + 24k`): all three inputs high, output high, feedback flipped would
give low. -/
theorem hold_rise (i k : Nat) :
    r i (15 + 5 * i + 24 * k) = true ∧ a i (15 + 5 * i + 24 * k) = true ∧
    q i (15 + 5 * i + 24 * k) = true ∧ ex (r i) (a i) (q i) rst6 (15 + 5 * i + 24 * k) = true ∧
    CElemTiming.exc CElemTiming.INIT_c2n (r i (15 + 5 * i + 24 * k)) (a i (15 + 5 * i + 24 * k))
      (!q i (15 + 5 * i + 24 * k)) (rst6 (15 + 5 * i + 24 * k)) = false := by
  unfold r q ex rst6
  show _ ∧ (sq12 (8 + 5 * (i + 1)) (15 + 5 * i + 24 * k - 2 - 2) ||
    sq12 (8 + 5 * (i + 1)) (15 + 5 * i + 24 * k - 1)) = true ∧ _ ∧
    CElemTiming.exc _ _ (sq12 (8 + 5 * (i + 1)) (15 + 5 * i + 24 * k - 2 - 2) ||
      sq12 (8 + 5 * (i + 1)) (15 + 5 * i + 24 * k - 1)) _ _ = true ∧
    CElemTiming.exc _ _ (sq12 (8 + 5 * (i + 1)) (15 + 5 * i + 24 * k - 2 - 2) ||
      sq12 (8 + 5 * (i + 1)) (15 + 5 * i + 24 * k - 1)) _ _ = false
  rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq]
  unfold sq12
  refine ⟨by bw, by bw, by bw, by bw, by bw⟩

/-- **The C-element holds after an acknowledge FALL** (1 tick, at
`29 + 5i + 24k`): all three inputs low, output low, feedback flipped would
give high. -/
theorem hold_fall (i k : Nat) :
    r i (29 + 5 * i + 24 * k) = false ∧ a i (29 + 5 * i + 24 * k) = false ∧
    q i (29 + 5 * i + 24 * k) = false ∧ ex (r i) (a i) (q i) rst6 (29 + 5 * i + 24 * k) = false ∧
    CElemTiming.exc CElemTiming.INIT_c2n (r i (29 + 5 * i + 24 * k)) (a i (29 + 5 * i + 24 * k))
      (!q i (29 + 5 * i + 24 * k)) (rst6 (29 + 5 * i + 24 * k)) = true := by
  unfold r q ex rst6
  show _ ∧ (sq12 (8 + 5 * (i + 1)) (29 + 5 * i + 24 * k - 2 - 2) ||
    sq12 (8 + 5 * (i + 1)) (29 + 5 * i + 24 * k - 1)) = false ∧ _ ∧
    CElemTiming.exc _ _ (sq12 (8 + 5 * (i + 1)) (29 + 5 * i + 24 * k - 2 - 2) ||
      sq12 (8 + 5 * (i + 1)) (29 + 5 * i + 24 * k - 1)) _ _ = false ∧
    CElemTiming.exc _ _ (sq12 (8 + 5 * (i + 1)) (29 + 5 * i + 24 * k - 2 - 2) ||
      sq12 (8 + 5 * (i + 1)) (29 + 5 * i + 24 * k - 1)) _ _ = true
  rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq]
  unfold sq12
  refine ⟨by bw, by bw, by bw, by bw, by bw⟩

/-! ### W2 data path: W1's (the nodes are the same waves) -/

abbrev d := W1.d
abbrev x := W1.x
abbrev dS := W1.dS
abbrev dE := W1.dE
abbrev V := W1.V

theorem Dl_e (N : Nat) : ∀ i b, Dl (P N) (fun _ => V) 4 0 i b = 3 := by
  intro i b
  induction i with
  | zero => simp [Dl, V, W1.V, P, Ret.shift]; decide
  | succ i ih => simp only [Dl, ih]; simp [V, W1.V, P, Ret.shift]; decide

theorem data (N : Nat) : DataN (P N) O (fun _ => d) (fun i _ => x i) val dS dE (fun _ => V)
    1 6 6 6 4 0 where
  H_LATCH i _ _ _ := by
    cases i with
    | zero => exact latchT W1.d (O 0) (W1.x 0) 3 2 2 2 4 1 3 1 2 (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) W1.x_rel0
    | succ i => exact latchT (W1.x i) (O (i + 1)) (W1.x (i + 1)) 3 2 2 2 4 1 3 1 2 (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (W1.x_rel i)
  H_WIN _ _ _ _ := by simp [V, W1.V]
  H_DATA_VALID k _ t _ h1 h2 := by
    unfold dS W1.dS at h1; unfold dE W1.dE at h2; unfold d W1.d val; bw
  H_DATA_LEAD k := by show 2 + 24 * k + 4 ≤ 6 + 12 * (2 * k) + 0; omega
  H_DATA_REL k := by rw [τ_e]; show 8 + 5 * 0 + 12 * (2 * k + 1) + 6 ≤ 26 + 24 * k; omega
  H_HOLD0 _ _ := by simp [V, W1.V]
  H_PW i _ _ _ := by rw [Won_e]; simp [V, W1.V]
  H_SETUP0 _ _ := by rw [Won_e]; simp [V, W1.V, P, Ret.shift]
  H_I i b _ _ := by rw [Dl_e, Won_e]; simp [V, W1.V, P, Ret.shift]
  H_H i _ _ _ := by rw [aslow_e]; show 3 ≤ 4 + 2 + 1 + 2; decide

/-- **W2: joint non-vacuity with `DACK = 2`, every `N ≥ 1`.** All four
contracts hold jointly; the acknowledge lines are the real FASTRISE chain;
rise/fall latencies 1/4; the C-element holds in both kinds of phase; the
latches hold through their loops; `pipe_forward` delivers every token. -/
theorem witness (N : Nat) (hN : 1 ≤ N) :
    GatesN (P N) rst6 r a O q (fun _ => 1) (fun _ => 1) ∧
    EnvN (P N) (r 0) (a ((P N).N - 1)) 6 6 ∧ TimingN (P N) (fun _ => 1) 6 6 ∧
    DataN (P N) O (fun _ => d) (fun i _ => x i) val dS dE (fun _ => V) 1 6 6 6 4 0 ∧
    (∀ b, (P N).m b = 1 ∧ (P N).alo b = 1 ∧ (P N).aslow b = 4) ∧
    (∀ k t, (P N).γ (2 * k) ≤ t → t < (P N).γ (2 * k + 1) → x (N - 1) t = decide (k % 2 = 0)) ∧
    (∀ i k, i < N →
      ex (r i) (a i) (q i) rst6 (15 + 5 * i + 24 * k) = true ∧
      CElemTiming.exc CElemTiming.INIT_c2n (r i (15 + 5 * i + 24 * k)) (a i (15 + 5 * i + 24 * k))
        (!q i (15 + 5 * i + 24 * k)) (rst6 (15 + 5 * i + 24 * k)) = false ∧
      ex (r i) (a i) (q i) rst6 (29 + 5 * i + 24 * k) = false ∧
      CElemTiming.exc CElemTiming.INIT_c2n (r i (29 + 5 * i + 24 * k)) (a i (29 + 5 * i + 24 * k))
        (!q i (29 + 5 * i + 24 * k)) (rst6 (29 + 5 * i + 24 * k)) = true) := by
  refine ⟨gates N, env N hN, timing N hN, data N, fun _ => ⟨rfl, rfl, rfl⟩,
    fun k t h1 h2 => ?_, fun i k _ => ⟨(hold_rise i k).2.2.2.1, (hold_rise i k).2.2.2.2,
      (hold_fall i k).2.2.2.1, (hold_fall i k).2.2.2.2⟩⟩
  exact (pipe_forward (gates N) (env N hN) (timing N hN) (data N) k 0 (by omega)).2
    (by rw [Dl_e]; decide) t h1 h2

end W2

/-! ## 3. W3: the per-pin model (`PipePerPin`), feedback on the SLOWEST pin, `DACK = 2`

Per stage: request site pin 1, acknowledge site pin 2, **feedback site pin 3
(the slowest)**, reset site pin 1, tree + output 2, feedback wire 1; request
line 3; the DACK = 2 chain of W2 (rise 1, fall 4). Reset released at its pin
at 8, every pin flushed from 6. Half-period 16, sender latency 8, receiver 7.
Stage `i`: request pin `sq16 (8+6i)`, node `sq16 (11+6i)`, feedback pin net
`sq16 (12+6i)`, acknowledge pin the chain of stage `i+1`'s node. At the
SELECTS the acknowledge arrives 5 ticks (after a rise) or 2 ticks (after a
fall) before the request, so the select-level excitation is decided by the
slowest pin, the feedback, for 5 resp. 2 ticks per phase. -/

namespace W3

/-- Half-period-16 square wave. -/
def sq16 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 32 < 16)
def rst8 (t : Nat) : Bool := decide (t < 8)

theorem rst8_lo (t : Nat) (h : 8 ≤ t) : rst8 t = false := by
  unfold rst8; simp; omega

def P (N : Nat) : PipePerPin.PP where
  N := N
  R := 8
  R0 := 6
  pr _ := Ret.shift 1
  pa _ := Ret.shift 2
  pq _ := Ret.shift 3
  ps _ := Ret.shift 1
  out _ := Ret.shift 2
  Rq _ := Ret.shift 3
  m _ := 1
  Ap _ k := cpath cB cC cU 1 k
  Ag _ := cguard cB cC cU 1
  ρ j := 8 + 16 * j
  γ j := 12 + 6 * N + 16 * j + 3 * (j % 2)

theorem ackT_e (N b j τ : Nat) (h : 1 ≤ τ) :
    (P N).ackT b j τ = τ + (if j % 2 = 0 then 1 else 4) := by
  show (if j % 2 = 0 then min ((cpath cB cC cU 1 0).fst τ) ((cpath cB cC cU 1 1).fst τ)
    else max ((cpath cB cC cU 1 0).fst τ) ((cpath cB cC cU 1 1).fst τ)) = _
  rw [cp0, cp1, fst_comp_shift 2 2 τ h, fst_shift 1 τ h]
  split <;> omega

theorem alo_e (N b : Nat) : (P N).alo b = 1 := rfl
theorem ahi_e (N b : Nat) : (P N).ahi b = 4 := rfl
theorem aslow_e (N b : Nat) : (P N).aslow b = 4 := rfl

theorem row_e (N j : Nat) (α : Nat → Nat) (hα : ∀ i, 1 ≤ α i ∧ α i + 2 ≤ 9 + 6 * i + 16 * j) :
    ∀ i, (P N).row j α i = 11 + 6 * i + 16 * j := by
  intro i
  induction i with
  | zero =>
    show (Ret.shift 2).fst (max ((Ret.shift 1).fst (8 + 16 * j)) ((Ret.shift 2).fst (α 0))) = _
    have := hα 0
    rw [fst_shift 1 _ (by omega), fst_shift 2 _ this.1, fst_shift 2 _ (by omega)]; omega
  | succ i ih =>
    show (Ret.shift 2).fst (max ((Ret.shift 1).fst ((Ret.shift 3).fst ((P N).row j α i)))
      ((Ret.shift 2).fst (α (i + 1)))) = _
    have := hα (i + 1)
    rw [ih, fst_shift 3 _ (by omega), fst_shift 1 _ (by omega), fst_shift 2 _ this.1,
      fst_shift 2 _ (by omega)]; omega

theorem tt_e (N : Nat) : ∀ j i, (P N).tt j i = 11 + 6 * i + 16 * j := by
  intro j
  induction j with
  | zero => exact row_e N 0 (fun _ => 6) (fun i => by omega)
  | succ j ih =>
    apply row_e
    intro i
    show 1 ≤ (if i + 1 < N then (P N).ackT (i + 1) j ((P N).tt j (i + 1))
      else 12 + 6 * N + 16 * j + 3 * (j % 2)) ∧
      (if i + 1 < N then (P N).ackT (i + 1) j ((P N).tt j (i + 1))
      else 12 + 6 * N + 16 * j + 3 * (j % 2)) + 2 ≤ _
    split
    · rw [ih, ackT_e N _ _ _ (by omega)]; split <;> omega
    · omega

/-- The derived node edges in closed form. -/
theorem τ_e (N i j : Nat) : (P N).τ i j = 11 + 6 * i + 16 * j := tt_e N j i

def r (i : Nat) : Trace := sq16 (8 + 6 * i)
def O (i : Nat) : Trace := sq16 (11 + 6 * i)
def q (i : Nat) : Trace := sq16 (12 + 6 * i)
/-- Stage `i`'s acknowledge pin: the DACK = 2 chain on stage `i+1`'s node. -/
def a (i : Nat) : Trace := chs (O (i + 1)) 2

/-- One per-pin controller: the real `bd_c2n` INIT at the selects, every
instant. -/
theorem ctl (i : Nat) :
    PipePerPin.CtlP (r i) (a i) rst8 (O i) (q i) (Ret.shift 1) (Ret.shift 2) (Ret.shift 3)
      (Ret.shift 1) (Ret.shift 2) 1 1 where
  H_OUT t _ := by
    show sq16 (11 + 6 * i) t = CElemTiming.exc CElemTiming.INIT_c2n (sq16 (8 + 6 * i) (t - 2 - 1))
      (sq16 (11 + 6 * (i + 1)) (t - 2 - 2 - 2 - 2) || sq16 (11 + 6 * (i + 1)) (t - 2 - 2 - 1))
      (sq16 (12 + 6 * i) (t - 2 - 3)) (rst8 (t - 2 - 1))
    rw [CElemTiming.c2n_eq]; unfold sq16 rst8; bw
  H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
    (fun t => by show sq16 (12 + 6 * i) (t + 1) = sq16 (11 + 6 * i) t; unfold sq16; bw)
  H_LOOP_POS := by show 1 ≤ 2 + 1 + 3; decide

theorem gates (N : Nat) : PipePerPin.GatesP (P N) rst8 r a O q (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i _ := ctl i
  H_REQ_LINE i _ t _ := by
    show sq16 (8 + 6 * (i + 1)) t = sq16 (11 + 6 * i) (t - 3); unfold sq16; bw
  H_ACK_LINE i _ t ht := chain2 (O (i + 1)) t ht

theorem env (N : Nat) (hN : 1 ≤ N) : PipePerPin.EnvP (P N) (r 0) (a ((P N).N - 1)) 8 7 where
  H_REQ_LOW0 t h1 h2 := by
    simp only [P] at h1 h2; show sq16 (8 + 6 * 0) t = false; unfold sq16; bw
  H_REQ j t h1 h2 := by
    simp only [P] at h1 h2; show sq16 (8 + 6 * 0) t = Vph j
    unfold sq16 Vph LinkTimed.Vph; bw
  H_ACK_LOW0 t h1 h2 := by
    simp only [P] at h1 h2
    show (sq16 (11 + 6 * (N - 1 + 1)) (t - 2 - 2) || sq16 (11 + 6 * (N - 1 + 1)) (t - 1)) = false
    unfold sq16; bw
  H_ACK j t h1 h2 := by
    simp only [P] at h1 h2
    show (sq16 (11 + 6 * (N - 1 + 1)) (t - 2 - 2) || sq16 (11 + 6 * (N - 1 + 1)) (t - 1)) = Vph j
    unfold sq16 Vph LinkTimed.Vph; bw
  H_SND j := by rw [τ_e]; show 11 + 6 * 0 + 16 * j + 8 ≤ 8 + 16 * (j + 1); omega
  H_RCV j := by
    rw [τ_e]; show 11 + 6 * (N - 1) + 16 * j + 7 ≤ 12 + 6 * N + 16 * j + 3 * (j % 2); omega
  H_RST_EARLY := by show 8 ≤ 8 + 16 * 0; omega

theorem ER_e (N i : Nat) : (P N).ER 8 i = 8 := by cases i <;> rfl
theorem EA_e (N i : Nat) : (P N).EA 7 i = 7 := by unfold PipePerPin.PP.EA; split <;> rfl
theorem Won_e (N i : Nat) : (P N).Won 8 7 i = 11 := by
  unfold PipePerPin.PP.Won; rw [ER_e, EA_e]; rfl

theorem timing (N : Nat) (hN : 1 ≤ N) : PipePerPin.TimingP (P N) (fun _ => 1) 8 7 where
  H_N_POS := hN
  H_R0_POS := by show 1 ≤ 6; decide
  H_R0_LE := by show 6 ≤ 8; decide
  H_RST_SEL _ _ := by
    show 6 + 1 ≤ 8 + 1 ∧ 2 + 1 + 3 ≤ 8 + 1 ∧ 8 + 1 ≤ 8 + 16 * 0 + 1 ∧ 6 + 2 ≤ 8 + 16 * 0 + 1
    decide
  H_FLUSH i _ := by rw [ahi_e]; show 2 + 3 ≤ 6 ∧ 2 + 4 ≤ 6 ∧ 5 ≤ 6; decide
  H_SELORD i _ := by rw [ER_e, EA_e]; show 1 + 3 ≤ 8 + 1 ∧ 1 + 3 ≤ 7 + 2; decide
  H_ACK_FLUSH i _ := by rw [Won_e, ahi_e, alo_e]; decide

/-- **Model times at the selects** (inside the pipe): the acknowledge follows
stage `i+1`'s rise by 1 and its fall by 4 at the pin; at the selects
(acknowledge site pin 2, request site pin 1) it leads the request by 5
ticks after a rise and by 2 after a fall. -/
theorem sel_lead (N i k : Nat) (hi : i + 1 < N) :
    (P N).Ain i (2 * k + 1) = (P N).τ (i + 1) (2 * k) + 1 ∧
    (P N).Ain i (2 * k + 2) = (P N).τ (i + 1) (2 * k + 1) + 4 ∧
    (Ret.shift 2).fst ((P N).Ain i (2 * k + 1)) + 5 = (Ret.shift 1).fst ((P N).Rin i (2 * k + 1)) ∧
    (Ret.shift 2).fst ((P N).Ain i (2 * k + 2)) + 2 = (Ret.shift 1).fst ((P N).Rin i (2 * k + 2)) ∧
    (Ret.shift 2).fst ((P N).Ain i (2 * k + 1)) = 20 + 6 * i + 32 * k ∧
    (Ret.shift 2).fst ((P N).Ain i (2 * k + 2)) = 39 + 6 * i + 32 * k := by
  have hR : ∀ j, (P N).Rin i (j + 1) = 24 + 6 * i + 16 * j := by
    intro j
    cases i with
    | zero => show 8 + 16 * (j + 1) = _; omega
    | succ i =>
      show (Ret.shift 3).fst ((P N).τ i (j + 1)) = _
      rw [τ_e, fst_shift 3 _ (by omega)]; omega
  have hA : ∀ j, (P N).Ain i (j + 1) = (P N).τ (i + 1) j + (if j % 2 = 0 then 1 else 4) := by
    intro j; rw [PipePerPin.PP.Ain_in _ _ _ hi, ackT_e _ _ _ _ (by rw [τ_e]; omega)]
  have hA1 : (P N).Ain i (2 * k + 1) = 18 + 6 * i + 32 * k := by
    rw [hA, τ_e]; split <;> omega
  have hA2 : (P N).Ain i (2 * k + 1 + 1) = 37 + 6 * i + 32 * k := by
    rw [hA, τ_e]; split <;> omega
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, hA1, hA2, hR, hR, τ_e, τ_e,
    fst_shift 2 (18 + 6 * i + 32 * k) (by omega), fst_shift 2 (37 + 6 * i + 32 * k) (by omega),
    fst_shift 1 _ (by omega), fst_shift 1 _ (by omega)]
  omega

/-- The select-level excitation of stage `i` at select instant `u`. -/
abbrev exS (i u : Nat) : Bool :=
  FifoFidelity.exSel (Ret.shift 1) (Ret.shift 2) (Ret.shift 3) (Ret.shift 1) (r i) (a i) (q i) rst8 u

/-- **Hold after an acknowledge RISE, at the selects** (`u = 21 + 6i + 32k`,
inside `[20 + 6i + 32k, 25 + 6i + 32k)` of `sel_lead`): request, acknowledge
and feedback selects all high, excitation high; with the feedback select
flipped it would be low. -/
theorem hold_rise (i k : Nat) :
    r i (21 + 6 * i + 32 * k - 1) = true ∧ a i (21 + 6 * i + 32 * k - 2) = true ∧
    q i (21 + 6 * i + 32 * k - 3) = true ∧ exS i (21 + 6 * i + 32 * k) = true ∧
    CElemTiming.exc CElemTiming.INIT_c2n (r i (21 + 6 * i + 32 * k - 1))
      (a i (21 + 6 * i + 32 * k - 2)) (!q i (21 + 6 * i + 32 * k - 3))
      (rst8 (21 + 6 * i + 32 * k - 1)) = false := by
  unfold exS FifoFidelity.exSel r q
  show _ ∧ (sq16 (11 + 6 * (i + 1)) (21 + 6 * i + 32 * k - 2 - 2 - 2) ||
    sq16 (11 + 6 * (i + 1)) (21 + 6 * i + 32 * k - 2 - 1)) = true ∧ _ ∧
    CElemTiming.exc _ _ (sq16 (11 + 6 * (i + 1)) (21 + 6 * i + 32 * k - 2 - 2 - 2) ||
      sq16 (11 + 6 * (i + 1)) (21 + 6 * i + 32 * k - 2 - 1)) _ _ = true ∧
    CElemTiming.exc _ _ (sq16 (11 + 6 * (i + 1)) (21 + 6 * i + 32 * k - 2 - 2 - 2) ||
      sq16 (11 + 6 * (i + 1)) (21 + 6 * i + 32 * k - 2 - 1)) _ _ = false
  rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq]
  simp only [shσ]
  rw [rst8_lo (21 + 6 * i + 32 * k - 1) (by omega)]
  unfold sq16
  refine ⟨by bw, by bw, by bw, by bw, by bw⟩

/-- **Hold after an acknowledge FALL, at the selects** (`u = 39 + 6i + 32k`,
inside `[39 + 6i + 32k, 41 + 6i + 32k)`): all three selects low, excitation
low; flipped feedback would give high. -/
theorem hold_fall (i k : Nat) :
    r i (39 + 6 * i + 32 * k - 1) = false ∧ a i (39 + 6 * i + 32 * k - 2) = false ∧
    q i (39 + 6 * i + 32 * k - 3) = false ∧ exS i (39 + 6 * i + 32 * k) = false ∧
    CElemTiming.exc CElemTiming.INIT_c2n (r i (39 + 6 * i + 32 * k - 1))
      (a i (39 + 6 * i + 32 * k - 2)) (!q i (39 + 6 * i + 32 * k - 3))
      (rst8 (39 + 6 * i + 32 * k - 1)) = true := by
  unfold exS FifoFidelity.exSel r q
  show _ ∧ (sq16 (11 + 6 * (i + 1)) (39 + 6 * i + 32 * k - 2 - 2 - 2) ||
    sq16 (11 + 6 * (i + 1)) (39 + 6 * i + 32 * k - 2 - 1)) = false ∧ _ ∧
    CElemTiming.exc _ _ (sq16 (11 + 6 * (i + 1)) (39 + 6 * i + 32 * k - 2 - 2 - 2) ||
      sq16 (11 + 6 * (i + 1)) (39 + 6 * i + 32 * k - 2 - 1)) _ _ = false ∧
    CElemTiming.exc _ _ (sq16 (11 + 6 * (i + 1)) (39 + 6 * i + 32 * k - 2 - 2 - 2) ||
      sq16 (11 + 6 * (i + 1)) (39 + 6 * i + 32 * k - 2 - 1)) _ _ = true
  rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq]
  simp only [shσ]
  rw [rst8_lo (39 + 6 * i + 32 * k - 1) (by omega)]
  unfold sq16
  refine ⟨by bw, by bw, by bw, by bw, by bw⟩

/-! ### W3 data path: non-unit latch arcs (W1's windows), half-period 16 -/

def d (t : Nat) : Bool := decide (2 ≤ t ∧ (t - 2) % 64 < 32)
def x (i t : Nat) : Bool := decide (13 + 6 * i ≤ t ∧ (t - (13 + 6 * i)) % 64 < 32)
def dS (k : Nat) : Nat := 2 + 32 * k
def dE (k : Nat) : Nat := 34 + 32 * k
abbrev V := W1.V

theorem x_rel0 (t : Nat) : x 0 t = (if O 0 (t - 2) then d (t - 3) else x 0 (t - 2)) := by
  unfold O
  split
  · next h => unfold sq16 at h; simp at h; unfold x d; bw
  · next h => unfold sq16 at h; simp at h; unfold x; bw

theorem x_rel (i t : Nat) :
    x (i + 1) t = (if O (i + 1) (t - 2) then x i (t - 3) else x (i + 1) (t - 2)) := by
  unfold O
  split
  · next h => unfold sq16 at h; simp at h; unfold x; bw
  · next h => unfold sq16 at h; simp at h; unfold x; bw

theorem Dl_e (N : Nat) : ∀ i b, PipePerPin.Dl (P N) (fun _ => V) 6 0 i b = 3 := by
  intro i b
  induction i with
  | zero => simp [PipePerPin.Dl, V, W1.V, P, Ret.shift]; decide
  | succ i ih => simp only [PipePerPin.Dl, ih]; simp [V, W1.V, P, Ret.shift]; decide

theorem data (N : Nat) : PipePerPin.DataP (P N) O (fun _ => d) (fun i _ => x i) val dS dE
    (fun _ => V) 1 8 7 7 6 0 where
  H_LATCH i _ _ _ := by
    cases i with
    | zero => exact latchT d (O 0) (x 0) 3 2 2 2 4 1 3 1 2 (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) x_rel0
    | succ i => exact latchT (x i) (O (i + 1)) (x (i + 1)) 3 2 2 2 4 1 3 1 2 (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (x_rel i)
  H_WIN _ _ _ _ := by simp [V, W1.V]
  H_DATA_VALID k _ t _ h1 h2 := by
    unfold dS at h1; unfold dE at h2; unfold d val; bw
  H_DATA_LEAD k := by show 2 + 32 * k + 6 ≤ 8 + 16 * (2 * k) + 0; omega
  H_DATA_REL k := by rw [τ_e]; show 11 + 6 * 0 + 16 * (2 * k + 1) + 7 ≤ 34 + 32 * k; omega
  H_HOLD0 _ _ := by simp [V, W1.V]
  H_PW i _ _ _ := by rw [Won_e]; simp [V, W1.V]
  H_SETUP0 _ _ := by rw [Won_e]; simp [V, W1.V, P, Ret.shift]
  H_I i b _ _ := by rw [Dl_e, Won_e]; simp [V, W1.V, P, Ret.shift]
  H_H i _ _ _ := by rw [aslow_e]; show 3 ≤ 4 + 2 + 2 + 1 + 2; decide

/-- **The latch holds through its own loop**, every stage, every token: at
`t = 44 + 6i + 32k` the enable pin reads closed, the data pin already reads
token `k+1`, the output still shows token `k`. -/
theorem latch_hold (i k : Nat) :
    O i (44 + 6 * i + 32 * k - 2) = false ∧
    din (fun _ => d) (fun i _ => x i) i 0 (44 + 6 * i + 32 * k - 3) = val (k + 1) 0 ∧
    x i (44 + 6 * i + 32 * k) = val k 0 ∧ val (k + 1) 0 = !val k 0 := by
  cases i with
  | zero => unfold O d x val sq16; refine ⟨by bw, ?_, by bw, by bw⟩; show d _ = _; unfold d; bw
  | succ i =>
    refine ⟨by unfold O sq16; bw, ?_, by unfold x val; bw, by unfold val; bw⟩
    show x i _ = _; unfold x val; bw

/-- **W3: joint non-vacuity of the PER-PIN contract, every `N ≥ 1`**: unequal
site pins with the feedback on the slowest, `DACK = 2` from the real chain,
non-unit data arcs; `GatesP ∧ EnvP ∧ TimingP ∧ DataP` jointly;
`PipePerPin.pipe_forward` delivers every token; the select-level C-element
is decided by the (slowest) feedback select after every acknowledge rise and
fall; the latches hold through their loops. -/
theorem witness (N : Nat) (hN : 1 ≤ N) :
    PipePerPin.GatesP (P N) rst8 r a O q (fun _ => 1) (fun _ => 1) ∧
    PipePerPin.EnvP (P N) (r 0) (a ((P N).N - 1)) 8 7 ∧
    PipePerPin.TimingP (P N) (fun _ => 1) 8 7 ∧
    PipePerPin.DataP (P N) O (fun _ => d) (fun i _ => x i) val dS dE (fun _ => V) 1 8 7 7 6 0 ∧
    (∀ i, ((P N).pr i).hi < ((P N).pa i).hi ∧ ((P N).pa i).hi < ((P N).pq i).hi ∧
      ((P N).ps i).hi < ((P N).pq i).hi) ∧
    (∀ b, (P N).m b = 1 ∧ (P N).alo b = 1 ∧ (P N).aslow b = 4) ∧
    (∀ k t, (P N).γ (2 * k) ≤ t → t < (P N).γ (2 * k + 1) → x (N - 1) t = decide (k % 2 = 0)) ∧
    (∀ i k, i < N →
      exS i (21 + 6 * i + 32 * k) = true ∧
      CElemTiming.exc CElemTiming.INIT_c2n (r i (21 + 6 * i + 32 * k - 1))
        (a i (21 + 6 * i + 32 * k - 2)) (!q i (21 + 6 * i + 32 * k - 3))
        (rst8 (21 + 6 * i + 32 * k - 1)) = false ∧
      exS i (39 + 6 * i + 32 * k) = false ∧
      CElemTiming.exc CElemTiming.INIT_c2n (r i (39 + 6 * i + 32 * k - 1))
        (a i (39 + 6 * i + 32 * k - 2)) (!q i (39 + 6 * i + 32 * k - 3))
        (rst8 (39 + 6 * i + 32 * k - 1)) = true) ∧
    (∀ i k, i < N → x i (44 + 6 * i + 32 * k) = val k 0 ∧
      din (fun _ => d) (fun i _ => x i) i 0 (44 + 6 * i + 32 * k - 3) = !val k 0) := by
  refine ⟨gates N, env N hN, timing N hN, data N, fun _ => by show 1 < 2 ∧ 2 < 3 ∧ 1 < 3; decide,
    fun _ => ⟨rfl, rfl, rfl⟩, fun k t h1 h2 => ?_,
    fun i k _ => ⟨(hold_rise i k).2.2.2.1, (hold_rise i k).2.2.2.2,
      (hold_fall i k).2.2.2.1, (hold_fall i k).2.2.2.2⟩, fun i k _ => ?_⟩
  · exact (PipePerPin.pipe_forward (gates N) (env N hN) (timing N hN) (data N) k 0 (by omega)).2
      (by rw [Dl_e]; decide) t h1 h2
  · have h := latch_hold i k
    exact ⟨h.2.2.1, by rw [h.2.1, h.2.2.2]⟩

end W3

end Formal.Cells.PipeWitness
