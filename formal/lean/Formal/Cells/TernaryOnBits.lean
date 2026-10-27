import Formal.Cells.TernarySound
import Formal.Cells.TernaryPhases
import Formal.Cells.TernaryExact
import Formal.Cells.OnNetlist

/-!
# Probe Bx: ternary hazard / settling checker on the whole routed netlist

7f/7i/7l proved two-phase ternary simulation (Algorithms A and B) SOUND and
EXACT for any LUT network (`TernarySound.Circ`) in the GMW model with a
per-pin wire read time (H_WIRE_CAUSAL, H_GMW_GATE) and, for settling, the
bounds H_WIRE_BOUND / H_GATE_BOUND (`Bounded D W`). Bn (`OnNetlist`) read
the 7 physical LUT6/LUT6_2 sites (10 used outputs) of `link_arb`
(`bd_link #(.W(3))` + `bd_arbiter`) back from four routed bitstreams
(seeds 1..4, nextpnr sha256 9c732bc6303458df; C-11c's `FasmLink.S1..S4`).

This file applies the generic theorems to the WHOLE physical netlist of each
seed, as ONE network over physical nodes:

* nodes 0..8 are the input ports (C-11c's common port order:
  A0, ack_out, data_in[0..2], r1, r2, req_in, rst);
* node `9 + 2i` is O6 of physical LUT `i`, node `10 + 2i` its O5, each a
  `Circ` gate with the PHYSICAL INIT on the PHYSICAL pin sources A1..A6
  (O5: `INIT % 2^32` on A1..A5), every routed pin an independent read
  (so per-pin routing skew, e.g. the A0 fork, is inside the model);
* ties are constants (11b's H_TIE).

`stepK_circ` proves that the generic ternary step of this network IS Bn's
physical Kleene excitation `OnNetlist.excK` (per LUT output).

Results (all by `decide +kernel` on list computations, per seed: kernel
evaluation only, no extra axiom; about 3.5-5.5 s per seed for the schedule,
under 1 s for the reset and contested checks):

1. **Reset** (`reset_s*`): with rst = 1 and EVERY other input arbitrary
   (all `x`), from any power-up state, every bounded run has c = 0,
   A1 = A2 = 0, q = 1, g2 = 0 from `F + 3(D+W+1)` on, for ever. The three
   latch bits are NOT reset (`x`): `bd_link` has no data reset.
2. **Transactions** (`txn_s*`): a 14-phase schedule from all-`x` power-up:
   reset, reset release, one four-phase link transaction (req_in up,
   ack_out up, req_in down, ack_out down with the data changing), one
   arbitrated transaction for client 1 (r1 up, A0 up, r1 down, A0 down) and
   one for client 2. Each phase puts `x` on its changing inputs for the
   whole window. Every bounded run following the schedule is covered on
   every logical node by the expected A table during the window (a node
   definite there never glitches: hazard-free) and by the expected B table
   from `F + 3(D+W+1)` until the next window (definite on every node at
   every phase end, except the three latch bits before the first
   transaction). The tables (`expTables`) are the same for all four seeds.
3. **Contested** (`contested_exact_s*`): from the idle state after the
   transactions, both requests rise in one window. Over EVERY physical gate
   node: some bounded run (inputs: one clean edge on r1 and r2) never
   settles at that node IFF the node is the physical q, g1 or g2. The `x`
   result there is exact by 7l; every other node settles in every bounded
   run. The FIFO witness of 7l (`B_exact_fifo`) is also instantiated
   (`contested_exact_fifo`, generic in the seed).

Model: `TernarySound.Run` / `Bounded` unchanged; the hypotheses are its
H_WIRE_CAUSAL, H_GMW_GATE, H_WIRE_BOUND, H_GATE_BOUND, plus H_KLEENE_LUT
(Prelim) and H_TIE (11b). O5 and O6 of one LUT6_2 are separate gate nodes
with independent pin reads (an over-approximation for soundness; for the
exactness witnesses it means the witness may let O5 and O6 see the shared
pin at different times, see the notes).
-/

namespace Formal.Cells.TernaryOnBits
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.TernaryPhases

abbrev PNet := Formal.Net.Fasm.PNet
abbrev LOut := Formal.Net.Fasm.LOut

/-! ## 1. The physical netlist as a `Circ` -/

/-- Physical node index of a LUT output. -/
def pidx (i : Nat) : LOut → Nat
  | .o6 => 9 + 2 * i
  | .o5 => 10 + 2 * i

def toSrc : Formal.Net.Fasm.Src → Src
  | .const b => .const b
  | .port i => .node i
  | .lut i o => .node (pidx i o)

/-- The whole routed netlist as one LUT network over physical nodes. -/
def circ (N : PNet) : Circ where
  size := 9 + 2 * N.luts.length
  node n :=
    if n < 9 then .input else
    match N.luts[(n - 9) / 2]? with
    | some L => if (n - 9) % 2 = 0 then .gate L.init (L.pins.map toSrc)
                else .gate (L.init % 2 ^ 32) ((L.pins.take 5).map toSrc)
    | none => .input

theorem circ_ge (N : PNet) (n : Nat) (h : (circ N).size ≤ n) : (circ N).node n = .input := by
  simp only [circ] at h ⊢
  simp only [show ¬ n < 9 by omega, ↓reduceIte]
  have : N.luts.length ≤ (n - 9) / 2 := by omega
  rw [List.getElem?_eq_none this]

theorem circ_lt9 (N : PNet) (n : Nat) (h : n < 9) : (circ N).node n = .input := by
  simp only [circ, h, ↓reduceIte]

theorem circ_gate (N : PNet) (n : Nat) (h9 : 9 ≤ n) (h : n < (circ N).size) :
    ∃ init pins, (circ N).node n = .gate init pins := by
  simp only [circ] at h ⊢
  simp only [show ¬ n < 9 by omega, ↓reduceIte]
  have hl : (n - 9) / 2 < N.luts.length := by omega
  rw [List.getElem?_eq_getElem hl]
  dsimp only
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem srcK_toSrc (s : Nat → K3) (x : Formal.Net.Fasm.Src) :
    srcK s (toSrc x) = OnNetlist.srcK s (fun i o => s (pidx i o)) x := by
  cases x <;> rfl

/-- **The generic ternary step on this network is Bn's physical Kleene
excitation**: node `pidx i o` steps to `OnNetlist.excK` of LUT `i`, output
`o`, with ports read from nodes 0..8 and LUT outputs from their nodes. -/
theorem stepK_circ (N : PNet) (u s : Nat → K3) (i : Nat) (o : LOut)
    (hi : i < N.luts.length) :
    stepK (circ N) u s (pidx i o) = OnNetlist.excK N s (fun i o => s (pidx i o)) i o := by
  have hL := List.getElem?_eq_getElem hi
  cases o with
  | o6 =>
    have e1 : ¬ (9 + 2 * i < 9) := by omega
    have e2 : (9 + 2 * i - 9) / 2 = i := by omega
    have e3 : (9 + 2 * i - 9) % 2 = 0 := by omega
    simp only [stepK, circ, pidx, OnNetlist.excK, e1, e2, e3, hL, ↓reduceIte,
      OnNetlist.fnK, o6K, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    exact srcK_toSrc s x
  | o5 =>
    have e1 : ¬ (10 + 2 * i < 9) := by omega
    have e2 : (10 + 2 * i - 9) / 2 = i := by omega
    have e3 : ¬ ((10 + 2 * i - 9) % 2 = 0) := by omega
    simp only [stepK, circ, pidx, OnNetlist.excK, e1, e2, e3, hL, ↓reduceIte,
      OnNetlist.fnK, o5K, List.map_map, ← List.map_take]
    congr 1
    apply List.map_congr_left
    intro x _
    exact srcK_toSrc s x

/-! ## 2. List-valued iteration (so that `decide` shares work) -/

/-- A ternary state given by a list; `x` beyond its end. -/
def V (l : List K3) : Nat → K3 := fun n => l.getD n .x

def stepL (N : Circ) (u : Nat → K3) (l : List K3) : List K3 :=
  (List.range N.size).map (fun n => stepK N u (V l) n)

def iterL (N : Circ) (u : Nat → K3) : Nat → List K3 → List K3
  | 0, l => l
  | m + 1, l => iterL N u m (stepL N u l)

/-- Every pin reads a node inside the network. -/
def WF (N : Circ) : Prop :=
  ∀ n, n < N.size → ∀ init pins, N.node n = .gate init pins → ∀ i, Src.node i ∈ pins → i < N.size

def pinOK (N : Circ) : Src → Bool
  | .node i => decide (i < N.size)
  | .const _ => true

def wfB (N : Circ) : Bool :=
  (List.range N.size).all (fun n => match N.node n with
    | .gate _ pins => pins.all (pinOK N)
    | .input => true)

theorem wf_of (N : Circ) (h : wfB N = true) : WF N := by
  intro n hn init pins hnode i hi
  simp only [wfB, List.all_eq_true, List.mem_range] at h
  have := h n hn
  rw [hnode] at this
  simp only [List.all_eq_true] at this
  have := this _ hi
  simpa [pinOK] using this

theorem V_ge {l : List K3} {n : Nat} (h : l.length ≤ n) : V l n = .x := by
  simp [V, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem V_replicate (k n : Nat) : V (List.replicate k .x) n = .x := by
  simp only [V, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_stepL (N : Circ) (u : Nat → K3) (l : List K3) {n : Nat} (hn : n < N.size) :
    V (stepL N u l) n = stepK N u (V l) n := by
  simp [V, stepL, List.getD_eq_getElem?_getD, hn]

theorem length_stepL (N : Circ) (u : Nat → K3) (l : List K3) : (stepL N u l).length = N.size := by
  simp [stepL]

theorem length_iterL (N : Circ) (u : Nat → K3) : ∀ m (l : List K3),
    (iterL N u (m + 1) l).length = N.size := by
  intro m
  induction m with
  | zero => intro l; exact length_stepL N u l
  | succ m ih => intro l; exact ih (stepL N u l)

theorem stepK_congr (N : Circ) (hwf : WF N) (u : Nat → K3) {s s' : Nat → K3}
    (h : ∀ n, n < N.size → s n = s' n) : ∀ n, n < N.size → stepK N u s n = stepK N u s' n := by
  intro n hn
  unfold stepK
  cases hnode : N.node n with
  | input => rfl
  | gate init pins =>
    simp only
    congr 1
    apply List.map_congr_left
    intro p hp
    cases p with
    | node i => exact h i (hwf n hn init pins hnode i hp)
    | const b => rfl

/-- The function iteration agrees with the list iteration inside the network. -/
theorem iter_lt (N : Circ) (hwf : WF N) (u : Nat → K3) :
    ∀ m (s : Nat → K3) (l : List K3), (∀ n, n < N.size → s n = V l n) →
      ∀ n, n < N.size → iter N u m s n = V (iterL N u m l) n := by
  intro m
  induction m with
  | zero => intro s l h n hn; exact h n hn
  | succ m ih =>
    intro s l h n hn
    show iter N u m (stepK N u s) n = V (iterL N u m (stepL N u l)) n
    apply ih
    · intro n' hn'
      rw [getD_stepL N u l hn']
      exact stepK_congr N hwf u h n' hn'
    · exact hn

theorem iter_ge (N : Circ) (hN : ∀ n, N.size ≤ n → N.node n = .input) (u : Nat → K3) (m : Nat)
    (s : Nat → K3) {n : Nat} (hn : N.size ≤ n) : iter N u (m + 1) s n = u n := by
  rw [iter_succ']
  unfold stepK
  rw [hN n hn]

theorem iterL_V (N : Circ) (hwf : WF N) (u : Nat → K3) (m : Nat) (l : List K3) :
    ∀ n, n < N.size → iter N u m (V l) n = V (iterL N u m l) n :=
  iter_lt N hwf u m (V l) l (fun _ _ => rfl)

/-- Boolean information order. -/
def leB (a b : K3) : Bool := decide (a = b) || decide (b = .x)

theorem le_of_leB {a b : K3} (h : leB a b = true) : le a b := by
  simp only [leB, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

def sleB (N : Circ) (l l' : List K3) : Bool :=
  (List.range N.size).all (fun n => leB (V l n) (V l' n))

theorem sleB_lt {N : Circ} {l l' : List K3} (h : sleB N l l' = true) {n : Nat} (hn : n < N.size) :
    le (V l n) (V l' n) := by
  simp only [sleB, List.all_eq_true, List.mem_range] at h
  exact le_of_leB (h n hn)

/-! ## 3. Phase schedules with a ternary certificate

A phase is a window vector `u` (`x` on the inputs that change), a final
vector `a`, and a CERTIFICATE `s`: a ternary state that must be closed under
the window step and lie above the previous phase's B result (checked by
`chk`). Algorithm A's result is the least such state; any closed state above
it is sound too, so the certificate is checked, not trusted. The B result is
always computed (`iterL (V a) M s`). -/

structure Spec where
  u : List K3
  a : List K3

/-- A certified phase: spec, A state `s`, claimed B result `r` (checked:
`r = iterL (V a) M s`). -/
abbrev CPh := Spec × (List K3 × List K3)

/-- 7i's phase list for a schedule `((spec, (s, r)), (S, F))`. -/
def build (N : Circ) (M : Nat) : List (CPh × (Nat × Nat)) → List Phase
  | [] => []
  | ((sp, (s, _)), (S, F)) :: rest => ⟨V sp.u, V sp.a, V s, M, S, F⟩ :: build N M rest

/-- The per-phase (A state, B result) lists, B computed. -/
def resL (N : Circ) (M : Nat) (c : List CPh) : List (List K3 × List K3) :=
  c.map (fun p => (p.2.1, iterL N (V p.1.a) M p.2.1))

/-- The decidable ternary certificate check: each A state is closed under its
window step, and each B result is below the next A state. -/
def chk (N : Circ) (M : Nat) : List CPh → Bool
  | [] => true
  | (sp, (s, r)) :: rest =>
    decide (sp.u.length ≤ N.size) && decide (s.length ≤ N.size) &&
    sleB N (stepL N (V sp.u) s) s && (iterL N (V sp.a) M s == r) &&
    (match rest with
      | [] => true
      | (_, (s', _)) :: _ => sleB N r s') &&
    chk N M rest

theorem resL_eq (N : Circ) (M : Nat) : ∀ c : List CPh, chk N M c = true →
    resL N M c = c.map (·.2) := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨sp, s, r⟩ := hd
    intro h
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [resL, List.map_cons] at ih ⊢
    rw [h.1.1.2, ih h.2]

theorem chk_len (N : Circ) (M : Nat) : ∀ c : List CPh, chk N M c = true →
    ∀ q ∈ c, q.2.1.length ≤ N.size := by
  intro c
  induction c with
  | nil => intro _ q hq; cases hq
  | cons hd tl ih =>
    intro h q hq
    obtain ⟨spq, sq, rq⟩ := hd
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1.1.1.1.2
    · exact ih h.2 q hq

/-- The timing side of the schedule: `S ≤ F` and each window opens only
after the previous phase has settled and every wire has flushed
(`F + M(D+W+1) + W ≤ S'`, 7i's spacing). -/
def TimesOK (D W M : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | [(S, F)] => S ≤ F
  | (S, F) :: (S', F') :: rest => S ≤ F ∧ F + M * (D + W + 1) + W ≤ S' ∧ TimesOK D W M ((S', F') :: rest)

theorem closed_one (N : Circ) (u s : List K3) (hus : s.length ≤ N.size)
    (h : sleB N (stepL N (V u) s) s = true) : sle (stepK N (V u) (V s)) (V s) := by
  intro n
  rcases Nat.lt_or_ge n N.size with hn | hn
  · have := sleB_lt h hn
    rwa [getD_stepL N _ _ hn] at this
  · rw [V_ge (by omega)]; exact Or.inr rfl

section generic
variable (N : Circ) (hwf : WF N)
include hwf

theorem res_le (a s s' : List K3) (M : Nat) (hs' : s'.length ≤ N.size)
    (h : sleB N (iterL N (V a) M s) s' = true) : sle (iter N (V a) M (V s)) (V s') := by
  intro n
  rcases Nat.lt_or_ge n N.size with hn | hn
  · rw [iterL_V N hwf _ M s n hn]; exact sleB_lt h hn
  · rw [V_ge (show s'.length ≤ n by omega)]; exact Or.inr rfl

theorem build_ok (D W M : Nat) :
    ∀ (phs : List (CPh × (Nat × Nat))),
      chk N M (phs.map (·.1)) = true → TimesOK D W M (phs.map (·.2)) →
      Closed N (build N M phs) ∧ Links N D W (build N M phs) := by
  intro phs
  induction phs with
  | nil =>
    intro _ _
    refine ⟨?_, ?_⟩
    · intro p hp; simp [build] at hp
    · simp [build, Links]
  | cons hd rest ih =>
    obtain ⟨⟨sp, s, r⟩, S, F⟩ := hd
    intro hc hT
    simp only [List.map_cons, chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨_, hsl⟩, hcl⟩, hr⟩, hnext⟩, hrest⟩ := hc
    subst hr
    have hp := closed_one N sp.u s hsl hcl
    cases rest with
    | nil =>
      refine ⟨?_, trivial⟩
      intro p hpm
      simp only [build, List.mem_singleton] at hpm
      subst hpm
      exact ⟨hp, hT⟩
    | cons hd2 rest2 =>
      obtain ⟨⟨sp', s', r'⟩, S', F'⟩ := hd2
      simp only [List.map_cons] at hT hnext hrest
      obtain ⟨hSF, hsp, hT'⟩ := hT
      have hs'l : s'.length ≤ N.size := by
        have := hrest
        simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1.1.1.2
      have ih' := ih (by simpa using hrest) (by simpa using hT')
      refine ⟨?_, ?_⟩
      · intro p hpm
        rcases List.mem_cons.1 hpm with rfl | hpm
        · exact ⟨hp, hSF⟩
        · exact ih'.1 p hpm
      · refine ⟨?_, ?_, ih'.2⟩
        · exact res_le N hwf sp.a s s' M hs'l hnext
        · simp only [Phase.ready]; omega

/-- **Generic multi-phase theorem on a certified list schedule.** The first
phase's A state is all-`x` (power-up: nothing is assumed about the initial
state); the ternary certificate is decided once (`chk`), the timing is
`TimesOK`. Every bounded run whose inputs follow the schedule satisfies 7i's
`Good`. -/
theorem build_good (D W M : Nat) {v : Nat → Nat → Bool} (R : Run N v)
    (hB : Bounded N v R D W) (sp : Spec) (s r : List K3) (S F : Nat)
    (rest : List (CPh × (Nat × Nat)))
    (h0 : s = List.replicate N.size .x)
    (hc : chk N M ((((sp, (s, r)), (S, F)) :: rest).map (·.1)) = true)
    (hT : TimesOK D W M ((((sp, (s, r)), (S, F)) :: rest).map (·.2)))
    (hF : Follows N v (build N M (((sp, (s, r)), (S, F)) :: rest))) :
    Good N D W v (build N M (((sp, (s, r)), (S, F)) :: rest)) := by
  have hok := build_ok N hwf D W M _ hc hT
  simp only [build] at hok hF ⊢
  apply phases_sound N R hB _ _ hok.1 hok.2 hF
  intro k _ _ n
  simp only [h0, V_replicate]
  rfl

/-- What `Good` says, read on the lists: per phase, the A state covers the
run from the window start to the next window start, and the B result from
`F + M(D+W+1)` to the next window start (for ever for the last phase). -/
def HoldsL (D W M : Nat) (v : Nat → Nat → Bool) :
    List (List K3 × List K3) → List (Nat × Nat) → Prop
  | (sl, rl) :: rest, (S, F) :: ts =>
    (∀ k, S ≤ k → (match ts with | [] => True | (S', _) :: _ => k ≤ S') →
      ∀ n, n < N.size → K3.admits (V sl n) (v k n) = true) ∧
    (∀ k, F + M * (D + W + 1) ≤ k → (match ts with | [] => True | (S', _) :: _ => k ≤ S') →
      ∀ n, n < N.size → K3.admits (V rl n) (v k n) = true) ∧
    HoldsL D W M v rest ts
  | _, _ => True

omit hwf in
theorem good_holds (D W M : Nat) {v : Nat → Nat → Bool} (hwf : WF N) :
    ∀ (phs : List (CPh × (Nat × Nat))),
      Good N D W v (build N M phs) →
      HoldsL N D W M v (resL N M (phs.map (·.1))) (phs.map (·.2)) := by
  intro phs
  induction phs with
  | nil => intro _; simp [resL, HoldsL]
  | cons hd rest ih =>
    obtain ⟨⟨sp, s, r⟩, S, F⟩ := hd
    intro hG
    cases rest with
    | nil =>
      simp only [build, Good] at hG
      simp only [List.map_cons, List.map_nil, resL, HoldsL]
      refine ⟨fun k hk _ n _ => hG.1 k hk n, fun k hk _ n hn => ?_, trivial⟩
      have := hG.2 k hk n
      simp only [Phase.res] at this
      rwa [iterL_V N hwf _ M _ n hn] at this
    | cons hd2 rest2 =>
      obtain ⟨⟨sp', s', r'⟩, S', F'⟩ := hd2
      simp only [build, Good] at hG
      obtain ⟨hA, hBr, hG'⟩ := hG
      simp only [List.map_cons, resL, HoldsL]
      refine ⟨fun k hk hk2 n _ => hA k hk hk2 n, fun k hk hk2 n hn => ?_, ?_⟩
      · have := hBr k hk hk2 n
        simp only [Phase.res] at this
        rwa [iterL_V N hwf _ M _ n hn] at this
      · have := ih (by simp only [build]; exact hG')
        simp only [List.map_cons, resL, HoldsL] at this
        exact this

end generic

/-! ## 4. The instance: `link_arb`, seeds 1..4 -/

/-- Physical node of a logical node of Bn's map (`OnNetlist.Seed.m`). -/
def phys (S : OnNetlist.Seed) (n : OnNetlist.Node) : Nat :=
  match S.m n with
  | .port i => i
  | .lut i o => pidx i o
  | .const _ => 0

/-- A physical list read on the 19 logical nodes (order `OnNetlist.allNodes`:
r1 r2 a0 rst req_in ack_out d0 d1 d2 | c q0 q1 q2 | A1 A2 q g1 g2 R0). -/
def logical (S : OnNetlist.Seed) (l : List K3) : List K3 :=
  OnNetlist.allNodes.map (fun n => V l (phys S n))

/-- Read a physical cover on the logical nodes. -/
theorem logical_cover (S : OnNetlist.Seed) (l : List K3) (c : Nat → Bool)
    (hl : l.length ≤ (circ S.net).size)
    (h : ∀ n, n < (circ S.net).size → K3.admits (V l n) (c n) = true) :
    ∀ p ∈ OnNetlist.allNodes.zip (logical S l), K3.admits p.2 (c (phys S p.1)) = true := by
  intro p hp
  have hz : OnNetlist.allNodes.zip (logical S l) =
      OnNetlist.allNodes.map (fun n => (n, V l (phys S n))) := by
    simp only [logical]
    generalize OnNetlist.allNodes = L
    induction L with
    | nil => rfl
    | cons a L ih => simp [ih]
  rw [hz] at hp
  obtain ⟨n, _, rfl⟩ := List.mem_map.1 hp
  rcases Nat.lt_or_ge (phys S n) (circ S.net).size with hlt | hge
  · exact h _ hlt
  · show K3.admits (V l (phys S n)) _ = true
    rw [V_ge (by omega)]
    rfl

/-- Input vector in port order (A0, ack_out, data_in[0..2], r1, r2, req_in, rst). -/
def P (a0 ack d0 d1 d2 r1 r2 req rst : K3) : List K3 := [a0, ack, d0, d1, d2, r1, r2, req, rst]

open K3 in
/-- The schedule. Data sent: 101 (d0 = 1, d1 = 0, d2 = 1), then 010.
In each phase `u` has `x` exactly on the inputs that change. -/
def specs : List Spec := [
  -- 0 reset from power-up: rst = 1, controls 0, data anything
  ⟨P x x x x x x x x x, P f f x x x f f f t⟩,
  -- 1 reset release; data becomes 101
  ⟨P f f x x x f f f x, P f f t f t f f f f⟩,
  -- 2..5 link: req_in up, ack_out up, req_in down, ack_out down with data 101 -> 010
  ⟨P f f t f t f f x f, P f f t f t f f t f⟩,
  ⟨P f x t f t f f t f, P f t t f t f f t f⟩,
  ⟨P f t t f t f f x f, P f t t f t f f f f⟩,
  ⟨P f x x x x f f f f, P f f f t f f f f f⟩,
  -- 6..9 arbiter, client 1: r1 up, A0 up, r1 down, A0 down
  ⟨P f f f t f x f f f, P f f f t f t f f f⟩,
  ⟨P x f f t f t f f f, P t f f t f t f f f⟩,
  ⟨P t f f t f x f f f, P t f f t f f f f f⟩,
  ⟨P x f f t f f f f f, P f f f t f f f f f⟩,
  -- 10..13 arbiter, client 2: r2 up, A0 up, r2 down, A0 down
  ⟨P f f f t f f x f f, P f f f t f f t f f⟩,
  ⟨P x f f t f f t f f, P t f f t f f t f f⟩,
  ⟨P t f f t f f x f f, P t f f t f f f f f⟩,
  ⟨P x f f t f f f f f, P f f f t f f f f f⟩]

open K3 in
/-- Expected (A table, B table) per phase on the logical nodes, written from
the cells' specifications (C-element `~rst . C(req_in, ~ack_out)`, latch
transparent while c = 1, arbiter states `idle1/own1/served1/done1` of 7b and
their client-2 mirror), not copied from a run. In an A table a node is `x`
iff it is meant to move in the window, or is still undefined. -/
def expTables : List (List K3 × List K3) := [
  -- r1 r2 a0 rst rq ak d0 d1 d2 | c q0 q1 q2 | A1 A2 q g1 g2 R0
  ([x, x, x, x, x, x, x, x, x,  x, x, x, x,  x, x, x, x, x, x],
   [f, f, f, t, f, f, x, x, x,  f, x, x, x,  f, f, t, f, f, f]),
  ([f, f, f, x, f, f, x, x, x,  f, x, x, x,  f, f, t, f, f, f],
   [f, f, f, f, f, f, t, f, t,  f, x, x, x,  f, f, t, f, f, f]),
  ([f, f, f, f, x, f, t, f, t,  x, x, x, x,  f, f, t, f, f, f],
   [f, f, f, f, t, f, t, f, t,  t, t, f, t,  f, f, t, f, f, f]),
  ([f, f, f, f, t, x, t, f, t,  t, t, f, t,  f, f, t, f, f, f],
   [f, f, f, f, t, t, t, f, t,  t, t, f, t,  f, f, t, f, f, f]),
  ([f, f, f, f, x, t, t, f, t,  x, t, f, t,  f, f, t, f, f, f],
   [f, f, f, f, f, t, t, f, t,  f, t, f, t,  f, f, t, f, f, f]),
  ([f, f, f, f, f, x, x, x, x,  f, t, f, t,  f, f, t, f, f, f],
   [f, f, f, f, f, f, f, t, f,  f, t, f, t,  f, f, t, f, f, f]),
  ([x, f, f, f, f, f, f, t, f,  f, t, f, t,  f, f, t, x, f, x],
   [t, f, f, f, f, f, f, t, f,  f, t, f, t,  f, f, t, t, f, t]),
  ([t, f, x, f, f, f, f, t, f,  f, t, f, t,  x, f, t, t, f, t],
   [t, f, t, f, f, f, f, t, f,  f, t, f, t,  t, f, t, t, f, t]),
  ([x, f, t, f, f, f, f, t, f,  f, t, f, t,  t, f, t, x, f, x],
   [f, f, t, f, f, f, f, t, f,  f, t, f, t,  t, f, t, f, f, f]),
  ([f, f, x, f, f, f, f, t, f,  f, t, f, t,  x, f, t, f, f, f],
   [f, f, f, f, f, f, f, t, f,  f, t, f, t,  f, f, t, f, f, f]),
  ([f, x, f, f, f, f, f, t, f,  f, t, f, t,  f, f, x, f, x, x],
   [f, t, f, f, f, f, f, t, f,  f, t, f, t,  f, f, f, f, t, t]),
  ([f, t, x, f, f, f, f, t, f,  f, t, f, t,  f, x, f, f, t, t],
   [f, t, t, f, f, f, f, t, f,  f, t, f, t,  f, t, f, f, t, t]),
  ([f, x, t, f, f, f, f, t, f,  f, t, f, t,  f, t, f, f, x, x],
   [f, f, t, f, f, f, f, t, f,  f, t, f, t,  f, t, f, f, f, f]),
  ([f, f, x, f, f, f, f, t, f,  f, t, f, t,  f, x, f, f, f, f],
   [f, f, f, f, f, f, f, t, f,  f, t, f, t,  f, f, f, f, f, f])]

/-- Number of B steps per phase (the B results are fixed points by then). -/
def M : Nat := 3

/-- Everything decided per seed, for a schedule `sp` with certificates `cs`
(A state, B result per phase) and expected logical tables `ex`. -/
def certB (S : OnNetlist.Seed) (sp : List Spec) (cs : List (List K3 × List K3))
    (ex : List (List K3 × List K3)) : Bool :=
  wfB (circ S.net) && decide (cs.length = sp.length) &&
  decide ((cs.head?.map (·.1)) = some (List.replicate (circ S.net).size .x)) &&
  chk (circ S.net) M (sp.zip cs) &&
  (cs.map (fun p => (logical S p.1, logical S p.2)) == ex)

/-- `HoldsL` read on the logical nodes with given tables. -/
def HoldsT (S : OnNetlist.Seed) (D W : Nat) (v : Nat → Nat → Bool) :
    List (List K3 × List K3) → List (Nat × Nat) → Prop
  | (aT, bT) :: rest, (S0, F) :: ts =>
    (∀ k, S0 ≤ k → (match ts with | [] => True | (S', _) :: _ => k ≤ S') →
      ∀ p ∈ OnNetlist.allNodes.zip aT, K3.admits p.2 (v k (phys S p.1)) = true) ∧
    (∀ k, F + M * (D + W + 1) ≤ k → (match ts with | [] => True | (S', _) :: _ => k ≤ S') →
      ∀ p ∈ OnNetlist.allNodes.zip bT, K3.admits p.2 (v k (phys S p.1)) = true) ∧
    HoldsT S D W v rest ts
  | _, _ => True

theorem holdsL_T (S : OnNetlist.Seed) (D W : Nat) (v : Nat → Nat → Bool) :
    ∀ (L : List (List K3 × List K3)) (ts : List (Nat × Nat)),
      (∀ p ∈ L, p.1.length ≤ (circ S.net).size ∧ p.2.length ≤ (circ S.net).size) →
      HoldsL (circ S.net) D W M v L ts →
      HoldsT S D W v (L.map (fun p => (logical S p.1, logical S p.2))) ts := by
  intro L
  induction L with
  | nil => intro ts _ _; simp [HoldsT]
  | cons hd rest ih =>
    intro ts hlen hH
    obtain ⟨sl, rl⟩ := hd
    cases ts with
    | nil => simp [HoldsT]
    | cons t ts =>
      obtain ⟨S0, F⟩ := t
      have hl := hlen _ (List.mem_cons_self ..)
      simp only [HoldsL] at hH
      simp only [List.map_cons, HoldsT]
      refine ⟨fun k h1 h2 => logical_cover S sl _ hl.1 (hH.1 k h1 h2),
        fun k h1 h2 => logical_cover S rl _ hl.2 (hH.2.1 k h1 h2), ?_⟩
      exact ih ts (fun p hp => hlen p (List.mem_cons_of_mem _ hp)) hH.2.2

/-- **Main theorem, generic in the seed.** If the per-seed certificate
checks, every bounded run (any `D`, `W`) of the whole physical netlist whose
inputs follow the schedule `sp` with times `ts` is covered on every logical
node by the expected A table during each window and by the expected B table
from `F + 3(D+W+1)` to the next window start (for ever after the last). -/
theorem schedule_holds (S : OnNetlist.Seed) (sp : List Spec) (cs : List (List K3 × List K3))
    (ex : List (List K3 × List K3)) (hc : certB S sp cs ex = true)
    {v : Nat → Nat → Bool} (R : Run (circ S.net) v) {D W : Nat}
    (hB : Bounded (circ S.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = sp.length)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ S.net) v (build (circ S.net) M ((sp.zip cs).zip ts))) :
    HoldsT S D W v ex ts := by
  simp only [certB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hwf, hcl⟩, hhd⟩, hchk⟩, hex⟩ := hc
  have hwf' := wf_of _ hwf
  have hz1 : ((sp.zip cs).zip ts).map (·.1) = sp.zip cs :=
    List.map_fst_zip (by simp [hcl, hlen])
  have hz2 : ((sp.zip cs).zip ts).map (·.2) = ts :=
    List.map_snd_zip (by simp [hcl, hlen])
  have hz3 : (sp.zip cs).map (·.2) = cs := List.map_snd_zip (by simp [hcl])
  have hG : Good (circ S.net) D W v (build (circ S.net) M ((sp.zip cs).zip ts)) := by
    cases hphs : (sp.zip cs).zip ts with
    | nil => simp [build, Good]
    | cons hd rest =>
      obtain ⟨⟨sp0, s0, r0⟩, S0, F0⟩ := hd
      have h0 : s0 = List.replicate (circ S.net).size .x := by
        cases sp with
        | nil => simp at hphs
        | cons a sp' =>
          cases cs with
          | nil => simp at hphs
          | cons c cs' =>
            cases ts with
            | nil => simp at hphs
            | cons t ts' =>
              simp only [List.zip_cons_cons, List.cons.injEq, Prod.mk.injEq] at hphs
              simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
              rw [hphs.1.1.2] at hhd; exact hhd
      rw [hphs] at hF hz1 hz2
      apply build_good (circ S.net) hwf' D W M R hB sp0 s0 r0 S0 F0 rest h0
      · rw [hz1]; exact hchk
      · rw [hz2]; exact hT
      · exact hF
  have hH := good_holds (circ S.net) D W M hwf' _ hG
  rw [hz1, hz2] at hH
  have hT' := holdsL_T S D W v _ ts (by
    intro p hp
    simp only [resL, List.mem_map] at hp
    obtain ⟨q, hmem, rfl⟩ := hp
    exact ⟨chk_len _ M _ hchk q hmem, by simp only [M]; rw [length_iterL]; exact Nat.le_refl _⟩) hH
  rw [resL_eq _ M _ hchk, hz3, hex] at hT'
  exact hT'

/-! ### Certificates ((A state, B result) per phase; generated by running the
same functions, then CHECKED by `chk`: nothing in them is trusted) -/

open K3 in
def cert1 : List (List K3 × List K3) :=
[([x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x],
    [f, f, x, x, x, f, f, f, t, f, f, x, x, x, x, t, f, f, f, f, f, f, f]),
   ([f, f, x, x, x, f, f, f, x, f, f, x, x, x, x, t, f, f, f, f, f, f, f],
    [f, f, t, f, t, f, f, f, f, f, f, x, x, x, x, t, f, f, f, f, f, f, f]),
   ([f, f, t, f, t, f, f, x, f, x, x, x, x, x, x, t, f, f, f, f, f, f, f],
    [f, f, t, f, t, f, f, t, f, t, t, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, x, t, f, t, f, f, t, f, t, t, f, t, t, t, t, f, f, f, f, f, f, f],
    [f, t, t, f, t, f, f, t, f, t, t, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, t, t, f, t, f, f, x, f, x, x, f, t, t, t, t, f, f, f, f, f, f, f],
    [f, t, t, f, t, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, x, x, x, x, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, f, f, t, f, x, f, f, f, f, f, f, t, t, t, t, x, f, f, f, x, f, f],
    [f, f, f, t, f, t, f, f, f, f, f, f, t, t, t, t, t, f, f, f, t, f, f]),
   ([x, f, f, t, f, t, f, f, f, f, f, f, t, t, t, t, t, x, x, f, t, f, f],
    [t, f, f, t, f, t, f, f, f, f, f, f, t, t, t, t, t, t, t, f, t, f, f]),
   ([t, f, f, t, f, x, f, f, f, f, f, f, t, t, t, t, x, t, t, f, x, f, f],
    [t, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, t, t, f, f, f, f]),
   ([x, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, x, x, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, f, f, t, f, f, x, f, f, f, f, f, t, t, t, x, x, f, f, x, f, f, f],
    [f, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, t, f, f, t, f, f, f]),
   ([x, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, t, f, f, t, f, x, x],
    [t, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, t, f, f, t, f, t, t]),
   ([t, f, f, t, f, f, x, f, f, f, f, f, t, t, t, f, x, f, f, x, f, t, t],
    [t, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, t, t]),
   ([x, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, x, x],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, f, f])]

open K3 in
def cert2 : List (List K3 × List K3) :=
[([x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x],
    [f, f, x, x, x, f, f, f, t, f, f, x, x, x, x, f, f, t, f, f, f, f, f]),
   ([f, f, x, x, x, f, f, f, x, f, f, x, x, x, x, f, f, t, f, f, f, f, f],
    [f, f, t, f, t, f, f, f, f, f, f, x, x, x, x, f, f, t, f, f, f, f, f]),
   ([f, f, t, f, t, f, f, x, f, x, x, x, x, x, x, f, f, t, f, f, f, f, f],
    [f, f, t, f, t, f, f, t, f, t, t, f, t, t, t, f, f, t, f, f, f, f, f]),
   ([f, x, t, f, t, f, f, t, f, t, t, f, t, t, t, f, f, t, f, f, f, f, f],
    [f, t, t, f, t, f, f, t, f, t, t, f, t, t, t, f, f, t, f, f, f, f, f]),
   ([f, t, t, f, t, f, f, x, f, x, x, f, t, t, t, f, f, t, f, f, f, f, f],
    [f, t, t, f, t, f, f, f, f, f, f, f, t, t, t, f, f, t, f, f, f, f, f]),
   ([f, x, x, x, x, f, f, f, f, f, f, f, t, t, t, f, f, t, f, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, t, f, f, f, f, f]),
   ([f, f, f, t, f, x, f, f, f, f, f, f, t, t, t, f, x, t, x, f, f, f, f],
    [f, f, f, t, f, t, f, f, f, f, f, f, t, t, t, f, t, t, t, f, f, f, f]),
   ([x, f, f, t, f, t, f, f, f, f, f, f, t, t, t, f, t, t, t, x, x, f, f],
    [t, f, f, t, f, t, f, f, f, f, f, f, t, t, t, f, t, t, t, t, t, f, f]),
   ([t, f, f, t, f, x, f, f, f, f, f, f, t, t, t, f, x, t, x, t, t, f, f],
    [t, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, t, f, t, t, f, f]),
   ([x, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, t, f, x, x, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, t, f, f, f, f, f]),
   ([f, f, f, t, f, f, x, f, f, f, f, f, t, t, t, x, f, x, x, f, f, f, f],
    [f, f, f, t, f, f, t, f, f, f, f, f, t, t, t, t, f, f, t, f, f, f, f]),
   ([x, f, f, t, f, f, t, f, f, f, f, f, t, t, t, t, f, f, t, f, f, x, x],
    [t, f, f, t, f, f, t, f, f, f, f, f, t, t, t, t, f, f, t, f, f, t, t]),
   ([t, f, f, t, f, f, x, f, f, f, f, f, t, t, t, x, f, f, x, f, f, t, t],
    [t, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, t, t]),
   ([x, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, x, x],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, f, f])]

open K3 in
def cert3 : List (List K3 × List K3) :=
[([x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x],
    [f, f, x, x, x, f, f, f, t, f, f, x, x, x, x, f, f, t, f, f, f, f, f]),
   ([f, f, x, x, x, f, f, f, x, f, f, x, x, x, x, f, f, t, f, f, f, f, f],
    [f, f, t, f, t, f, f, f, f, f, f, x, x, x, x, f, f, t, f, f, f, f, f]),
   ([f, f, t, f, t, f, f, x, f, x, x, x, x, x, x, f, f, t, f, f, f, f, f],
    [f, f, t, f, t, f, f, t, f, t, t, t, t, f, t, f, f, t, f, f, f, f, f]),
   ([f, x, t, f, t, f, f, t, f, t, t, t, t, f, t, f, f, t, f, f, f, f, f],
    [f, t, t, f, t, f, f, t, f, t, t, t, t, f, t, f, f, t, f, f, f, f, f]),
   ([f, t, t, f, t, f, f, x, f, x, x, t, t, f, t, f, f, t, f, f, f, f, f],
    [f, t, t, f, t, f, f, f, f, f, f, t, t, f, t, f, f, t, f, f, f, f, f]),
   ([f, x, x, x, x, f, f, f, f, f, f, t, t, f, t, f, f, t, f, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, t, t, f, t, f, f, t, f, f, f, f, f]),
   ([f, f, f, t, f, x, f, f, f, f, f, t, t, f, t, f, f, t, x, f, f, f, x],
    [f, f, f, t, f, t, f, f, f, f, f, t, t, f, t, f, f, t, t, f, f, f, t]),
   ([x, f, f, t, f, t, f, f, f, f, f, t, t, f, t, f, f, t, t, x, x, f, t],
    [t, f, f, t, f, t, f, f, f, f, f, t, t, f, t, f, f, t, t, t, t, f, t]),
   ([t, f, f, t, f, x, f, f, f, f, f, t, t, f, t, f, f, t, x, t, t, f, x],
    [t, f, f, t, f, f, f, f, f, f, f, t, t, f, t, f, f, t, f, t, t, f, f]),
   ([x, f, f, t, f, f, f, f, f, f, f, t, t, f, t, f, f, t, f, x, x, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, t, t, f, t, f, f, t, f, f, f, f, f]),
   ([f, f, f, t, f, f, x, f, f, f, f, t, t, f, t, f, f, x, x, f, f, x, f],
    [f, f, f, t, f, f, t, f, f, f, f, t, t, f, t, f, f, f, t, f, f, t, f]),
   ([x, f, f, t, f, f, t, f, f, f, f, t, t, f, t, x, x, f, t, f, f, t, f],
    [t, f, f, t, f, f, t, f, f, f, f, t, t, f, t, t, t, f, t, f, f, t, f]),
   ([t, f, f, t, f, f, x, f, f, f, f, t, t, f, t, t, t, f, x, f, f, x, f],
    [t, f, f, t, f, f, f, f, f, f, f, t, t, f, t, t, t, f, f, f, f, f, f]),
   ([x, f, f, t, f, f, f, f, f, f, f, t, t, f, t, x, x, f, f, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, t, t, f, t, f, f, f, f, f, f, f, f])]

open K3 in
def cert4 : List (List K3 × List K3) :=
[([x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x],
    [f, f, x, x, x, f, f, f, t, f, f, x, x, x, x, t, f, f, f, f, f, f, f]),
   ([f, f, x, x, x, f, f, f, x, f, f, x, x, x, x, t, f, f, f, f, f, f, f],
    [f, f, t, f, t, f, f, f, f, f, f, x, x, x, x, t, f, f, f, f, f, f, f]),
   ([f, f, t, f, t, f, f, x, f, x, x, x, x, x, x, t, f, f, f, f, f, f, f],
    [f, f, t, f, t, f, f, t, f, t, t, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, x, t, f, t, f, f, t, f, t, t, f, t, t, t, t, f, f, f, f, f, f, f],
    [f, t, t, f, t, f, f, t, f, t, t, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, t, t, f, t, f, f, x, f, x, x, f, t, t, t, t, f, f, f, f, f, f, f],
    [f, t, t, f, t, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, x, x, x, x, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, f, f, t, f, x, f, f, f, f, f, f, t, t, t, t, x, f, f, f, x, f, f],
    [f, f, f, t, f, t, f, f, f, f, f, f, t, t, t, t, t, f, f, f, t, f, f]),
   ([x, f, f, t, f, t, f, f, f, f, f, f, t, t, t, t, t, f, f, f, t, x, x],
    [t, f, f, t, f, t, f, f, f, f, f, f, t, t, t, t, t, f, f, f, t, t, t]),
   ([t, f, f, t, f, x, f, f, f, f, f, f, t, t, t, t, x, f, f, f, x, t, t],
    [t, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, t, t]),
   ([x, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, x, x],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f]),
   ([f, f, f, t, f, f, x, f, f, f, f, f, t, t, t, x, x, f, f, x, f, f, f],
    [f, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, t, f, f, t, f, f, f]),
   ([x, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, t, x, x, t, f, f, f],
    [t, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, t, t, t, t, f, f, f]),
   ([t, f, f, t, f, f, x, f, f, f, f, f, t, t, t, f, x, t, t, x, f, f, f],
    [t, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, t, t, f, f, f, f]),
   ([x, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, x, x, f, f, f, f],
    [f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, f, f, f, f, f, f])]

def seed1 := OnNetlist.seed1
def seed2 := OnNetlist.seed2
def seed3 := OnNetlist.seed3
def seed4 := OnNetlist.seed4

theorem cert_s1 : certB seed1 specs cert1 expTables = true := by decide +kernel
theorem cert_s2 : certB seed2 specs cert2 expTables = true := by decide +kernel
theorem cert_s3 : certB seed3 specs cert3 expTables = true := by decide +kernel
theorem cert_s4 : certB seed4 specs cert4 expTables = true := by decide +kernel

/-- **(1)+(2) on the bits, seed 1**: reset from all-`x` power-up, release,
one four-phase link transaction and two arbitrated transactions; every
bounded run of the whole physical netlist following the schedule is covered
by `expTables` (hazard-free where the A table is definite, settled to the B
table at every phase end). Seeds 2..4 below. -/
theorem txn_s1 {v : Nat → Nat → Bool} (R : Run (circ seed1.net) v) {D W : Nat}
    (hB : Bounded (circ seed1.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 14)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed1.net) v (build (circ seed1.net) M ((specs.zip cert1).zip ts))) :
    HoldsT seed1 D W v expTables ts :=
  schedule_holds seed1 specs cert1 expTables cert_s1 R hB ts hlen hT hF

theorem txn_s2 {v : Nat → Nat → Bool} (R : Run (circ seed2.net) v) {D W : Nat}
    (hB : Bounded (circ seed2.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 14)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed2.net) v (build (circ seed2.net) M ((specs.zip cert2).zip ts))) :
    HoldsT seed2 D W v expTables ts :=
  schedule_holds seed2 specs cert2 expTables cert_s2 R hB ts hlen hT hF

theorem txn_s3 {v : Nat → Nat → Bool} (R : Run (circ seed3.net) v) {D W : Nat}
    (hB : Bounded (circ seed3.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 14)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed3.net) v (build (circ seed3.net) M ((specs.zip cert3).zip ts))) :
    HoldsT seed3 D W v expTables ts :=
  schedule_holds seed3 specs cert3 expTables cert_s3 R hB ts hlen hT hF

theorem txn_s4 {v : Nat → Nat → Bool} (R : Run (circ seed4.net) v) {D W : Nat}
    (hB : Bounded (circ seed4.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 14)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed4.net) v (build (circ seed4.net) M ((specs.zip cert4).zip ts))) :
    HoldsT seed4 D W v expTables ts :=
  schedule_holds seed4 specs cert4 expTables cert_s4 R hB ts hlen hT hF

/-! ### (1) Reset alone: rst = 1, every other input arbitrary -/

open K3 in
def resetSpec : List Spec := [⟨P x x x x x x x x x, P x x x x x x x x t⟩]

open K3 in
/-- With rst = 1 and nothing else known: c = 0, A1 = A2 = 0, q = 1, g2 = 0;
g1 and R0 follow r1 (combinational), the latch is not reset. -/
def resetTable : List (List K3 × List K3) :=
  -- r1 r2 a0 rst rq ak d0 d1 d2 | c q0 q1 q2 | A1 A2 q g1 g2 R0
  [([x, x, x, x, x, x, x, x, x,  x, x, x, x,  x, x, x, x, x, x],
    [x, x, x, t, x, x, x, x, x,  f, x, x, x,  f, f, t, x, f, x])]

def rcert (N : Circ) : List (List K3 × List K3) :=
  [(List.replicate N.size .x, iterL N (V (P .x .x .x .x .x .x .x .x .t)) M (List.replicate N.size .x))]

theorem rcert_s1 : certB seed1 resetSpec (rcert (circ seed1.net)) resetTable = true := by decide +kernel
theorem rcert_s2 : certB seed2 resetSpec (rcert (circ seed2.net)) resetTable = true := by decide +kernel
theorem rcert_s3 : certB seed3 resetSpec (rcert (circ seed3.net)) resetTable = true := by decide +kernel
theorem rcert_s4 : certB seed4 resetSpec (rcert (circ seed4.net)) resetTable = true := by decide +kernel

/-- **(1) Reset, every seed.** From ANY power-up state, if rst = 1 from `F` on
(the other inputs doing anything at all, and rst anything before `F`), every
bounded run of the whole physical netlist has, from `F + 3(D+W+1)` on, for
ever: c = 0, A1 = A2 = 0, q = 1, g2 = 0 (and rst = 1). -/
theorem adm_f {b : Bool} (h : K3.admits .f b = true) : b = false := by
  cases b; rfl; exact absurd h (by decide)

theorem adm_t {b : Bool} (h : K3.admits .t b = true) : b = true := by
  cases b; exact absurd h (by decide); rfl

open K3 in
theorem V_P8 (z : K3) (n : Nat) (h : n ≠ 8) : V (P x x x x x x x x z) n = .x := by
  rcases n with _|_|_|_|_|_|_|_|_|n <;> simp_all [V, P]

theorem reset_settles (S : OnNetlist.Seed)
    (hc : certB S resetSpec (rcert (circ S.net)) resetTable = true)
    {v : Nat → Nat → Bool} (R : Run (circ S.net) v) {D W : Nat}
    (hB : Bounded (circ S.net) v R D W) (F : Nat)
    (hrst : ∀ k, F ≤ k → v k 8 = true) :
    ∀ k, F + M * (D + W + 1) ≤ k →
      v k (phys S .c) = false ∧ v k (phys S .a1) = false ∧ v k (phys S .a2) = false ∧
      v k (phys S .q) = true ∧ v k (phys S .g2) = false := by
  have hH := schedule_holds S resetSpec (rcert (circ S.net)) resetTable hc R hB [(0, F)] rfl
    (Nat.zero_le F) (by
      intro k _
      refine ⟨?_, fun hk => ?_⟩
      · intro n _
        show K3.admits (V (P .x .x .x .x .x .x .x .x .x) n) _ = true
        by_cases h8 : n = 8
        · subst h8; rfl
        · rw [V_P8 _ n h8]; rfl
      · intro n _
        show K3.admits (V (P .x .x .x .x .x .x .x .x .t) n) _ = true
        by_cases h8 : n = 8
        · subst h8; show K3.admits .t _ = true; rw [hrst k hk]; rfl
        · rw [V_P8 _ n h8]; rfl)
  intro k hk
  have h := hH.2.1 k hk trivial
  exact ⟨adm_f (h (.c, .f) (by decide)), adm_f (h (.a1, .f) (by decide)),
    adm_f (h (.a2, .f) (by decide)), adm_t (h (.q, .t) (by decide)),
    adm_f (h (.g2, .f) (by decide))⟩

theorem reset_s1 {v : Nat → Nat → Bool} (R : Run (circ seed1.net) v) {D W : Nat}
    (hB : Bounded (circ seed1.net) v R D W) (F : Nat) (hrst : ∀ k, F ≤ k → v k 8 = true) :
    ∀ k, F + M * (D + W + 1) ≤ k →
      v k (phys seed1 .c) = false ∧ v k (phys seed1 .a1) = false ∧ v k (phys seed1 .a2) = false ∧
      v k (phys seed1 .q) = true ∧ v k (phys seed1 .g2) = false :=
  reset_settles seed1 rcert_s1 R hB F hrst

theorem reset_s2 {v : Nat → Nat → Bool} (R : Run (circ seed2.net) v) {D W : Nat}
    (hB : Bounded (circ seed2.net) v R D W) (F : Nat) (hrst : ∀ k, F ≤ k → v k 8 = true) :
    ∀ k, F + M * (D + W + 1) ≤ k →
      v k (phys seed2 .c) = false ∧ v k (phys seed2 .a1) = false ∧ v k (phys seed2 .a2) = false ∧
      v k (phys seed2 .q) = true ∧ v k (phys seed2 .g2) = false :=
  reset_settles seed2 rcert_s2 R hB F hrst

theorem reset_s3 {v : Nat → Nat → Bool} (R : Run (circ seed3.net) v) {D W : Nat}
    (hB : Bounded (circ seed3.net) v R D W) (F : Nat) (hrst : ∀ k, F ≤ k → v k 8 = true) :
    ∀ k, F + M * (D + W + 1) ≤ k →
      v k (phys seed3 .c) = false ∧ v k (phys seed3 .a1) = false ∧ v k (phys seed3 .a2) = false ∧
      v k (phys seed3 .q) = true ∧ v k (phys seed3 .g2) = false :=
  reset_settles seed3 rcert_s3 R hB F hrst

theorem reset_s4 {v : Nat → Nat → Bool} (R : Run (circ seed4.net) v) {D W : Nat}
    (hB : Bounded (circ seed4.net) v R D W) (F : Nat) (hrst : ∀ k, F ≤ k → v k 8 = true) :
    ∀ k, F + M * (D + W + 1) ≤ k →
      v k (phys seed4 .c) = false ∧ v k (phys seed4 .a1) = false ∧ v k (phys seed4 .a2) = false ∧
      v k (phys seed4 .q) = true ∧ v k (phys seed4 .g2) = false :=
  reset_settles seed4 rcert_s4 R hB F hrst

/-! ### (3) The contested case: exact `x` on q, g1, g2 -/

open K3 in
def uC : List K3 := P f f f t f x x f f
def aC : List Bool := [false, false, false, true, false, true, true, false, false]
def aF (n : Nat) : Bool := aC.getD n false

def c0f (c : List Bool) (n : Nat) : Bool := c.getD n false
def c0K (c : List Bool) : List K3 := c.map K3.ofBool

def stabB (N : Circ) (c : Nat → Bool) : Bool :=
  (List.range N.size).all (fun j => match N.node j with
    | .gate init pins => lutB init (pinsB (fun _ i => c i) pins 0) == c j
    | .input => true)

/-- The decided facts of the contested case for seed `S` from idle state `c`:
`c` is the B result of phase 9 of the schedule (idle, client 1's turn), it is
binary stable, the A and B iterations are fixed at 3, the inputs are
admitted, and the A-then-B result is `x` at a gate node exactly at the
physical q, g1, g2. -/
def contestB (S : OnNetlist.Seed) (cs : List (List K3 × List K3)) (c : List Bool) : Bool :=
  let N := circ S.net
  let A := iterL N (V uC) 3 (c0K c)
  wfB N && decide (c.length = N.size) &&
  ((cs.getD 9 ([], [])).2 == c0K c) &&
  stabB N (c0f c) &&
  ((List.range 9).all (fun i => K3.admits (V uC i) (c0f c i) && K3.admits (V uC i) (aF i))) &&
  (iterL N (V uC) 4 (c0K c) == A) &&
  (iterL N (TernaryExact.fin aF) 4 A == iterL N (TernaryExact.fin aF) 3 A) &&
  ((List.range N.size).all (fun n => decide (n < 9) ||
    (decide (V (iterL N (TernaryExact.fin aF) 3 A) n = .x) ==
      decide (n = phys S .q ∨ n = phys S .g1 ∨ n = phys S .g2)))) &&
  (logical S (iterL N (TernaryExact.fin aF) 3 A) ==
    -- r1 r2 a0 rst rq ak d0 d1 d2 | c q0 q1 q2 | A1 A2 q g1 g2 R0
    [.t, .t, .f, .f, .f, .f, .f, .t, .f,  .f, .t, .f, .t,  .f, .f, .x, .x, .x, .t])

open K3 in
def idle1 : List Bool := ([f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f] : List K3).map (fun z => z == t)
open K3 in
def idle2 : List Bool := ([f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, f, f, t, f, f, f, f, f] : List K3).map (fun z => z == t)
open K3 in
def idle3 : List Bool := ([f, f, f, t, f, f, f, f, f, f, f, t, t, f, t, f, f, t, f, f, f, f, f] : List K3).map (fun z => z == t)
open K3 in
def idle4 : List Bool := ([f, f, f, t, f, f, f, f, f, f, f, f, t, t, t, t, f, f, f, f, f, f, f] : List K3).map (fun z => z == t)

theorem contest_s1 : contestB seed1 cert1 idle1 = true := by decide +kernel
theorem contest_s2 : contestB seed2 cert2 idle2 = true := by decide +kernel
theorem contest_s3 : contestB seed3 cert3 idle3 = true := by decide +kernel
theorem contest_s4 : contestB seed4 cert4 idle4 = true := by decide +kernel

theorem s0_V (c : List Bool) {n : Nat} (h : n < c.length) :
    TernaryExact.s0 (c0f c) n = V (c0K c) n := by
  simp [TernaryExact.s0, c0f, c0K, V, List.getD_eq_getElem?_getD, h]

theorem admits_x (b : Bool) : K3.admits .x b = true := by cases b <;> rfl

section contested
variable (S : OnNetlist.Seed) (cs : List (List K3 × List K3)) (c : List Bool)
  (hc : contestB S cs c = true)
include hc

theorem c_wf : WF (circ S.net) := by
  simp only [contestB, Bool.and_eq_true] at hc
  exact wf_of _ hc.1.1.1.1.1.1.1.1

theorem c_len : c.length = (circ S.net).size := by
  simp only [contestB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1.1.1.1.1.1.2

theorem c_inner : ∀ n, n < (circ S.net).size →
    iter (circ S.net) (V uC) 3 (TernaryExact.s0 (c0f c)) n =
      V (iterL (circ S.net) (V uC) 3 (c0K c)) n :=
  iter_lt _ (c_wf S cs c hc) _ 3 _ _ (fun n hn => s0_V c (by rw [c_len S cs c hc]; exact hn))

theorem c_outer : ∀ n, n < (circ S.net).size →
    iter (circ S.net) (TernaryExact.fin aF) 3
      (iter (circ S.net) (V uC) 3 (TernaryExact.s0 (c0f c))) n =
      V (iterL (circ S.net) (TernaryExact.fin aF) 3
        (iterL (circ S.net) (V uC) 3 (c0K c))) n :=
  iter_lt _ (c_wf S cs c hc) _ 3 _ _ (c_inner S cs c hc)

/-- The A-then-B result of the contested window is `x` at a gate node iff
the node is the physical q, g1 or g2. -/
theorem contested_x_iff (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ S.net).size) :
    iter (circ S.net) (TernaryExact.fin aF) 3
      (iter (circ S.net) (V uC) 3 (TernaryExact.s0 (c0f c))) n = .x ↔
      (n = phys S .q ∨ n = phys S .g1 ∨ n = phys S .g2) := by
  rw [c_outer S cs c hc n hn]
  have h := hc
  simp only [contestB, Bool.and_eq_true] at h
  have := h.1.2
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this n hn with h' | h'
  · omega
  · simp only [beq_iff_eq] at h'
    exact decide_eq_decide.1 h'

theorem c_stab : ∀ j init pins, (circ S.net).node j = .gate init pins →
    lutB init (pinsB (fun _ i => c0f c i) pins 0) = c0f c j := by
  intro j init pins hj
  have h := hc
  simp only [contestB, Bool.and_eq_true] at h
  have hs := h.1.1.1.1.1.2
  simp only [stabB, List.all_eq_true, List.mem_range] at hs
  rcases Nat.lt_or_ge j (circ S.net).size with hlt | hge
  · have := hs j hlt
    rw [hj] at this
    simpa using this
  · rw [circ_ge _ j hge] at hj; cases hj

theorem c_hu : ∀ i, (circ S.net).node i = .input →
    K3.admits (V uC i) (c0f c i) = true ∧ K3.admits (V uC i) (aF i) = true := by
  intro i _
  rcases Nat.lt_or_ge i 9 with hlt | hge
  · have h := hc
    simp only [contestB, Bool.and_eq_true] at h
    have := h.1.1.1.1.2
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at this
    exact this i hlt
  · rw [V_ge (by simp [uC, P]; omega)]
    exact ⟨admits_x _, admits_x _⟩

theorem c_fixA : ∀ n, iter (circ S.net) (V uC) (3 + 1) (TernaryExact.s0 (c0f c)) n =
    iter (circ S.net) (V uC) 3 (TernaryExact.s0 (c0f c)) n := by
  intro n
  rcases Nat.lt_or_ge n (circ S.net).size with hlt | hge
  · have h := hc
    simp only [contestB, Bool.and_eq_true, beq_iff_eq] at h
    rw [iter_lt _ (c_wf S cs c hc) _ 4 _ (c0K c)
        (fun n hn => s0_V c (by rw [c_len S cs c hc]; exact hn)) n hlt,
      c_inner S cs c hc n hlt, h.1.1.1.2]
  · rw [iter_ge _ (circ_ge _) _ 3 _ hge, iter_ge _ (circ_ge _) _ 2 _ hge]

theorem c_fixB : ∀ n, iter (circ S.net) (TernaryExact.fin aF) (3 + 1)
      (iter (circ S.net) (V uC) 3 (TernaryExact.s0 (c0f c))) n =
    iter (circ S.net) (TernaryExact.fin aF) 3
      (iter (circ S.net) (V uC) 3 (TernaryExact.s0 (c0f c))) n := by
  intro n
  rcases Nat.lt_or_ge n (circ S.net).size with hlt | hge
  · have h := hc
    simp only [contestB, Bool.and_eq_true, beq_iff_eq] at h
    rw [iter_lt _ (c_wf S cs c hc) _ 4 _ _ (c_inner S cs c hc) n hlt,
      c_outer S cs c hc n hlt, h.1.1.2]
  · rw [iter_ge _ (circ_ge _) _ 3 _ hge, iter_ge _ (circ_ge _) _ 2 _ hge]

/-- **(3) The contested case on the whole physical netlist, exactly.**
Start in the binary idle state `c0f c` (client 1's turn, link idle, latch
holding 010; checked to be phase 9's B result of the schedule). Over every
physical gate node `n`: some bounded run whose inputs stay inside `uC` (only
r1, r2 may move) and are final (r1 = r2 = 1) from step 2 NEVER SETTLES at `n`
iff `n` is the physical q, g1 or g2. Every other node settles in every
bounded run (7f), and by 7l's construction the witness run has unit gate
delay and one clean edge on both requests at step 1. -/
theorem contested_exact (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ S.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ S.net) v) (D W : Nat),
        Bounded (circ S.net) v R D W ∧ v 0 = c0f c ∧
        (∀ t i, (circ S.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ S.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys S .q ∨ n = phys S .g1 ∨ n = phys S .g2) := by
  obtain ⟨init, pins, hg⟩ := circ_gate S.net n h9 hn
  rw [← contested_x_iff S cs c hc n h9 hn]
  exact (TernaryExact.B_exact (circ S.net) (c0f c) aF (V uC) 3 (c_stab S cs c hc) (c_hu S cs c hc)
    (c_fixA S cs c hc) 3 (c_fixB S cs c hc) hg).symm

/-- The same with 7l's FIFO witness: unit gate delay, every wire 0 or 1
step and never reordering; the requests may glitch inside `uC` before `T0`. -/
theorem contested_exact_fifo (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ S.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ S.net) v) (T0 : Nat),
        Bounded (circ S.net) v R 0 1 ∧ (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ v 0 = c0f c ∧
        (∀ t i, (circ S.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ S.net).node i = .input → T0 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys S .q ∨ n = phys S .g1 ∨ n = phys S .g2) := by
  rw [← contested_x_iff S cs c hc n h9 hn]
  exact (TernaryExact.B_exact_fifo (circ S.net) (c0f c) aF (V uC) 3 (c_stab S cs c hc)
    (c_hu S cs c hc) (c_fixA S cs c hc) 3 (c_fixB S cs c hc) n).symm

end contested

theorem contested_exact_s1 (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed1.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ seed1.net) v) (D W : Nat),
        Bounded (circ seed1.net) v R D W ∧ v 0 = c0f idle1 ∧
        (∀ t i, (circ seed1.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ seed1.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys seed1 .q ∨ n = phys seed1 .g1 ∨ n = phys seed1 .g2) :=
  contested_exact seed1 cert1 idle1 contest_s1 n h9 hn

theorem contested_exact_s2 (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed2.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ seed2.net) v) (D W : Nat),
        Bounded (circ seed2.net) v R D W ∧ v 0 = c0f idle2 ∧
        (∀ t i, (circ seed2.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ seed2.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys seed2 .q ∨ n = phys seed2 .g1 ∨ n = phys seed2 .g2) :=
  contested_exact seed2 cert2 idle2 contest_s2 n h9 hn

theorem contested_exact_s3 (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed3.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ seed3.net) v) (D W : Nat),
        Bounded (circ seed3.net) v R D W ∧ v 0 = c0f idle3 ∧
        (∀ t i, (circ seed3.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ seed3.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys seed3 .q ∨ n = phys seed3 .g1 ∨ n = phys seed3 .g2) :=
  contested_exact seed3 cert3 idle3 contest_s3 n h9 hn

theorem contested_exact_s4 (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed4.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ seed4.net) v) (D W : Nat),
        Bounded (circ seed4.net) v R D W ∧ v 0 = c0f idle4 ∧
        (∀ t i, (circ seed4.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ seed4.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys seed4 .q ∨ n = phys seed4 .g1 ∨ n = phys seed4 .g2) :=
  contested_exact seed4 cert4 idle4 contest_s4 n h9 hn

/-- Non-vacuity of `contested_exact_s1`: q, g1, g2 are three distinct gate
nodes of the network, the other gate nodes number 11 (14 LUT outputs, of
which 4 unused O5s). -/
theorem contested_nodes_s1 :
    9 ≤ phys seed1 .q ∧ phys seed1 .q < (circ seed1.net).size ∧
    9 ≤ phys seed1 .g1 ∧ phys seed1 .g1 < (circ seed1.net).size ∧
    9 ≤ phys seed1 .g2 ∧ phys seed1 .g2 < (circ seed1.net).size ∧
    phys seed1 .q ≠ phys seed1 .g1 ∧ phys seed1 .q ≠ phys seed1 .g2 ∧
    phys seed1 .g1 ≠ phys seed1 .g2 ∧ (circ seed1.net).size = 23 := by decide

/-! ### Negative controls (the checks can fail) -/

/-- Bn's `MutInit` (seed 1, ugrant INIT bit 36 flipped: g2 = 1 when
r1 = r2 = q = 0) fails the certificate check. -/
theorem neg_mut_init : certB OnNetlist.mutSeed specs cert1 expTables = false := by decide +kernel

open K3 in
/-- A table that claims a hazard-free node where the network can glitch is
refuted: claiming c definite (0) during the req_in-rise window of phase 2. -/
theorem neg_table_hazard :
    certB seed1 specs cert1 (expTables.set 2
      ([f, f, f, f, x, f, t, f, t,  f, x, x, x,  f, f, t, f, f, f],
       [f, f, f, f, t, f, t, f, t,  t, t, f, t,  f, f, t, f, f, f])) = false := by decide +kernel

/-- Weakening the certificate's A state of phase 2 (c claimed 0 instead of
`x`) fails the closure check: the A state is checked, not trusted. -/
theorem neg_cert_closure :
    chk (circ seed1.net) M (specs.zip (cert1.set 2 ((cert1.getD 2 ([], [])).1.set (phys seed1 .c) .f,
      (cert1.getD 2 ([], [])).2))) = false := by decide +kernel

end Formal.Cells.TernaryOnBits
