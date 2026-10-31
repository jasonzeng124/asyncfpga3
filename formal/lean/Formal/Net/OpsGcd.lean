import Formal.Net.OpsFork
import Formal.Net.OpsJoin
import Formal.Net.OpsSteer
import Formal.Net.OpsMux
import Formal.Net.KahnGcd

/-!
# C-8f: the gcd-shaped loop (8b's `KahnGcd.G`) built from bdc's cells

The graph of 8b's `Formal.Net.Kahn.Gcd.G` (the C kernel's main loop: mux
header, `a ≠ 0` test, two `cond_br`s, forks, `|a-b|`-then-strip and `min`),
with each operator realised as bdc realises it:

* `mux` → `bd_mux` (`OpsMux.Mux`), the select is `tst v = (v ≠ 0)`;
* `fork` → `bd_fork` (`OpsFork.Fork`);
* the test, `sub` (`strip2 ∘ absdiff`), `min` → compute units (`OpsJoin.Join`);
* `cond_br` → `bd_join(cond, data)` (`Join gEnc`) + `bd_steer` (`Steer`), the
  joined bus carrying `2·data + [cond ≠ 0]`;
* the `aF` sink → `bd_snk` (`Sink`, proved here);
* the environment: two sources (`inA`, `inB`: every offered token is the
  argument), a consumer of `out`, and the two INITIAL-TOKEN buffers that put
  8b's initial select token `0` on `sA`, `sB`. These are hypotheses
  (H_SRC, H_ENV_OUT, H_INITBUF): not cells of this probe. (bdc gets the
  first select from an arbitrated `control_merge` instead, which is open.)

`gcd_circuit`: if every cell instance satisfies its gate model, the
environment its spec, and every channel `Held` (H_BUNDLE), then EVERY token
ever latched on `out` is `Nat.gcd a b`, for every `a`, `b` meeting the loop's
entry condition (`b` odd, `a` odd or zero; the C prologue establishes it,
8b's `gcdC_eq`). Proof: `net_refines_close` with an explicit solution `refS`
of the token equations (the loop's iterates, periodic in the invocation since
the sources repeat the arguments).
-/

namespace Formal.Net.Ops.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.Ops.Fork Formal.Net.Ops.Join Formal.Net.Ops.Steer Formal.Net.Ops.Mux

/-! ## `bd_snk` -/

/-- `bd_snk`: `ack = req`, a wire, modelled as a DI wire (≥ 1 tick). With zero
delay the two wires would move in the same step, which 8a's protocol forbids. -/
structure Sink (c : Chan) : Prop where
  wire : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = c.req t
  init : c.ack 0 = false

theorem sink_op {C : Type} (ch : C → Chan) (ca : C) (S : Sink (ch ca)) :
    OpProto ch [ca] [] ∧ OpData ch [ca] [] (fun _ => True) := by
  refine ⟨⟨fun t _ _ _ _ => ⟨fun c hc h => ?_, fun c hc => by cases hc⟩, ?_, ?_⟩, ?_⟩
  · rw [List.mem_singleton.1 hc] at h ⊢
    have := S.wire t h
    intro e; exact h (this.trans e.symm)
  · intro c hc; rw [List.mem_singleton.1 hc]; exact S.init
  · intro c hc; cases hc
  · intro _ _ c hc; cases hc

/-! ## The network -/

inductive GC
  | inA | inB | sA | sB | backA | backB | hA | hB | hA1 | hA2 | cnd | cA | cB | sA' | sB'
  | jA | jB | aT | aF | bT | out | a1 | a2 | b1 | b2
  deriving DecidableEq

inductive GO
  | srcA | srcB | muxA | muxB | forkA | isnz | forkC | ibA | ibB | joinA | brA | joinB | brB
  | snkA | forkAT | forkBT | sub | mn | envOut
  deriving DecidableEq

open GC GO

def ins : GO → List GC
  | srcA => [] | srcB => [] | muxA => [sA, inA, backA] | muxB => [sB, inB, backB]
  | forkA => [hA] | isnz => [hA1] | forkC => [cnd] | ibA => [sA'] | ibB => [sB']
  | joinA => [cA, hA2] | brA => [jA] | joinB => [cB, hB] | brB => [jB] | snkA => [aF]
  | forkAT => [aT] | forkBT => [bT] | sub => [a1, b1] | mn => [a2, b2] | envOut => [out]

def outs : GO → List GC
  | srcA => [inA] | srcB => [inB] | muxA => [hA] | muxB => [hB] | forkA => [hA1, hA2]
  | isnz => [cnd] | forkC => [cA, cB, sA', sB'] | ibA => [sA] | ibB => [sB] | joinA => [jA]
  | brA => [aT, aF] | joinB => [jB] | brB => [bT, out] | snkA => [] | forkAT => [a1, a2]
  | forkBT => [b1, b2] | sub => [backA] | mn => [backB] | envOut => []

def prod : GC → GO
  | inA => srcA | inB => srcB | sA => ibA | sB => ibB | backA => sub | backB => mn
  | hA => muxA | hB => muxB | hA1 => forkA | hA2 => forkA | cnd => isnz | cA => forkC
  | cB => forkC | sA' => forkC | sB' => forkC | jA => joinA | jB => joinB | aT => brA
  | aF => brA | bT => brB | out => brB | a1 => forkAT | a2 => forkAT | b1 => forkBT
  | b2 => forkBT

def cons : GC → GO
  | inA => muxA | inB => muxB | sA => muxA | sB => muxB | backA => muxA | backB => muxB
  | hA => forkA | hB => joinB | hA1 => isnz | hA2 => joinA | cnd => forkC | cA => joinA
  | cB => joinB | sA' => ibA | sB' => ibB | jA => brA | jB => brB | aT => forkAT
  | aF => snkA | bT => forkBT | out => envOut | a1 => sub | a2 => mn | b1 => sub
  | b2 => mn

def net : Net GC GO where
  ins := ins
  outs := outs
  prod := prod
  cons := cons
  prod_iff := by intro c o; cases c <;> cases o <;> simp [outs, prod]
  cons_iff := by intro c o; cases c <;> cases o <;> simp [ins, cons]

/-! ## Operator functions and token equations -/

def tst (v : Nat) : Bool := v != 0
/-- The test `a ≠ 0` as a 0/1 token. -/
def gNZ : List Nat → Nat := fun l => match l with | [x] => if x = 0 then 0 else 1 | _ => 0
/-- `cond_br`'s join: the bus carries `2·data + [cond ≠ 0]`. -/
def gEnc : List Nat → Nat := fun l => match l with
  | [c, d] => 2 * d + (if c = 0 then 0 else 1) | _ => 0
def selE (x : Nat) : Bool := x % 2 == 1
def gSub : List Nat → Nat := fun l => match l with
  | [x, y] => Kahn.Gcd.strip2 (Kahn.Gcd.absdiff x y) | _ => 0
def gMin : List Nat → Nat := fun l => match l with | [x, y] => min x y | _ => 0

def coutA (b : Bool) : GC := if b then aT else aF
def coutB (b : Bool) : GC := if b then bT else out

/-- Initial-token buffer: one token `0`, then the input stream. -/
def ibEq (i o : GC) (σ : GC → Nat → Nat) : Prop := σ o 0 = 0 ∧ ∀ k, σ o (k + 1) = σ i k

def E (a b : Nat) : GO → (GC → Nat → Nat) → Prop
  | srcA => fun σ => ∀ k, σ inA k = a
  | srcB => fun σ => ∀ k, σ inB k = b
  | muxA => muxEq tst sA inA backA hA
  | muxB => muxEq tst sB inB backB hB
  | forkA => forkEq hA [hA1, hA2]
  | isnz => joinEq gNZ [hA1] cnd
  | forkC => forkEq cnd [cA, cB, sA', sB']
  | ibA => ibEq sA' sA
  | ibB => ibEq sB' sB
  | joinA => joinEq gEnc [cA, hA2] jA
  | brA => steerEq selE (· / 2) jA coutA
  | joinB => joinEq gEnc [cB, hB] jB
  | brB => steerEq selE (· / 2) jB coutB
  | snkA => fun _ => True
  | forkAT => forkEq aT [a1, a2]
  | forkBT => forkEq bT [b1, b2]
  | sub => joinEq gSub [a1, b1] backA
  | mn => joinEq gMin [a2, b2] backB
  | envOut => fun _ => True

/-! ## An explicit solution of the token equations -/

/-- The C loop's iterates `(a_i, b_i)`. -/
def it : Nat → Nat → Nat → Nat × Nat
  | a, b, 0 => (a, b)
  | a, b, i + 1 => it (Kahn.Gcd.strip2 (Kahn.Gcd.absdiff a b)) (min a b) i

theorem it_succ : ∀ i a b, it a b (i + 1) =
    (Kahn.Gcd.strip2 (Kahn.Gcd.absdiff (it a b i).1 (it a b i).2), min (it a b i).1 (it a b i).2) := by
  intro i
  induction i with
  | zero => intro a b; rfl
  | succ i ih => intro a b; exact ih _ _

/-- Where the C loop stops: `a_N = 0`, `a_i ≠ 0` before, and `b_N` is its result. -/
theorem loop_N : ∀ f a b r, Kahn.Gcd.cLoop f a b = some r →
    ∃ N, (∀ i, i < N → (it a b i).1 ≠ 0) ∧ (it a b N).1 = 0 ∧ (it a b N).2 = r := by
  intro f
  induction f with
  | zero => intro a b r h; simp [Kahn.Gcd.cLoop] at h
  | succ f ih =>
    intro a b r h
    simp only [Kahn.Gcd.cLoop] at h
    by_cases h0 : a = 0
    · subst h0; simp at h; subst h
      exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), rfl, rfl⟩
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨N, h1, h2, h3⟩ := ih _ _ r h
      refine ⟨N + 1, fun i hi => ?_, h2, h3⟩
      cases i with
      | zero => exact h0
      | succ i => exact h1 i (by omega)

/-- Position inside the current invocation (`0 .. N`) and invocation number. -/
def ph (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if ph N k = N then 0 else ph N k + 1
def qq (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if ph N k = N then qq N k + 1 else qq N k

theorem ph_le (N : Nat) : ∀ k, ph N k ≤ N := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => simp only [ph]; split <;> omega

theorem cnt_congr {f g : Nat → Bool} (h : ∀ i, f i = g i) (k : Nat) : cnt f k = cnt g k := by
  have : f = g := funext h
  rw [this]

theorem cnt_shift (f : Nat → Bool) : ∀ k, cnt f (k + 1) =
    (if f 0 = true then 1 else 0) + cnt (fun i => f (i + 1)) k := by
  intro k
  induction k with
  | zero => simp [cnt]
  | succ k ih =>
    show cnt f (k + 1) + (if f (k + 1) = true then 1 else 0) = _
    rw [ih]; simp only [cnt]; omega

theorem cnt_ph (N : Nat) : ∀ k, cnt (fun i => decide (ph N i < N)) k = qq N k * N + ph N k := by
  intro k
  induction k with
  | zero => simp [cnt, qq, ph]
  | succ k ih =>
    show cnt (fun i => decide (ph N i < N)) k + (if decide (ph N k < N) = true then 1 else 0) = _
    rw [ih]
    have hle := ph_le N k
    simp only [ph, qq]
    by_cases h : ph N k = N
    · simp only [h, ↓reduceIte, Nat.lt_irrefl, decide_false, Bool.false_eq_true]
      rw [Nat.succ_mul]
      try omega
    · simp only [h, ↓reduceIte]
      have : ph N k < N := by omega
      simp [this] <;> omega

theorem mod_idx {N q r : Nat} (h : r < N) : (q * N + r) % N = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

section Sol
variable (a b N : Nat)

def A (i : Nat) : Nat := (it a b i).1
def B (i : Nat) : Nat := (it a b i).2
def cndS (k : Nat) : Nat := if A a b (ph N k) = 0 then 0 else 1

/-- The solution: every channel's value stream. -/
def refS : GC → Nat → Nat
  | inA => fun _ => a
  | inB => fun _ => b
  | hA => fun k => A a b (ph N k)
  | hA1 => fun k => A a b (ph N k)
  | hA2 => fun k => A a b (ph N k)
  | hB => fun k => B a b (ph N k)
  | cnd => cndS a b N
  | cA => cndS a b N
  | cB => cndS a b N
  | sA' => cndS a b N
  | sB' => cndS a b N
  | sA => fun k => match k with | 0 => 0 | k + 1 => cndS a b N k
  | sB => fun k => match k with | 0 => 0 | k + 1 => cndS a b N k
  | jA => fun k => gEnc [cndS a b N k, A a b (ph N k)]
  | jB => fun k => gEnc [cndS a b N k, B a b (ph N k)]
  | aT => fun j => A a b (j % N)
  | a1 => fun j => A a b (j % N)
  | a2 => fun j => A a b (j % N)
  | bT => fun j => B a b (j % N)
  | b1 => fun j => B a b (j % N)
  | b2 => fun j => B a b (j % N)
  | aF => fun _ => 0
  | out => fun _ => B a b N
  | backA => fun j => gSub [A a b (j % N), B a b (j % N)]
  | backB => fun j => gMin [A a b (j % N), B a b (j % N)]

end Sol

theorem refS_solves (a b N : Nat) (h1 : ∀ i, i < N → A a b i ≠ 0) (h2 : A a b N = 0) :
    ∀ o, E a b o (refS a b N) := by
  have hz : ∀ k, A a b (ph N k) = 0 ↔ ph N k = N := by
    intro k; have := ph_le N k
    constructor
    · intro h
      rcases Nat.lt_or_ge (ph N k) N with hl | hg
      · exact absurd h (h1 _ hl)
      · omega
    · intro h; rw [h]; exact h2
  have htst : ∀ k, tst (cndS a b N k) = decide (ph N k < N) := by
    intro k; have := ph_le N k
    unfold cndS tst
    by_cases h : ph N k = N
    · rw [h, h2]; simp
    · have hlt : ph N k < N := by omega
      have : A a b (ph N k) ≠ 0 := h1 _ hlt
      simp [this, hlt]
  have hsel : ∀ k x, selE (gEnc [cndS a b N k, x]) = decide (ph N k < N) := by
    intro k x; rw [← htst k]; unfold selE gEnc tst cndS
    by_cases hA : A a b (ph N k) = 0 <;> simp [hA] <;> omega
  have hdiv : ∀ k x, gEnc [cndS a b N k, x] / 2 = x := by
    intro k x; unfold gEnc cndS
    by_cases hA : A a b (ph N k) = 0 <;> simp [hA] <;> omega
  have hcntS : ∀ k, cnt (fun i => tst (refS a b N sA i)) (k + 1) = qq N k * N + ph N k := by
    intro k
    rw [cnt_shift]
    show (if tst 0 = true then 1 else 0) + cnt (fun i => tst (cndS a b N i)) k = _
    rw [cnt_congr htst, cnt_ph]; simp [tst]
  have hcntSB : ∀ k, cnt (fun i => tst (refS a b N sB i)) (k + 1) = qq N k * N + ph N k := hcntS
  have hmux : ∀ (F : Nat → Nat) (init : Nat) (back : Nat → Nat),
      F 0 = init →
      (∀ k, ph N k < N → F (ph N k + 1) = back (ph N k)) →
      ∀ k, F (ph N k) = if tst (refS a b N sA k) then back ((cnt (fun i => tst (refS a b N sA i)) k) % N)
        else init := by
    intro F init back hF0 hF k
    cases k with
    | zero => show F 0 = if tst 0 then _ else init; rw [hF0]; rfl
    | succ k =>
      rw [hcntS k]
      show F (ph N (k + 1)) = if tst (cndS a b N k) then back ((qq N k * N + ph N k) % N) else init
      rw [htst]
      have hle := ph_le N k
      by_cases h : ph N k = N
      · simp only [ph, h, ↓reduceIte, Nat.lt_irrefl, decide_false, Bool.false_eq_true]; exact hF0
      · have hlt : ph N k < N := by omega
        simp only [ph, h, ↓reduceIte, hlt, decide_true]
        rw [mod_idx hlt]; exact hF k hlt
  intro o
  cases o
  · intro k; rfl
  · intro k; rfl
  · -- muxA
    intro k
    have := hmux (A a b) a (fun j => gSub [A a b j, B a b j]) rfl
      (fun k _ => by unfold A; rw [it_succ]; rfl) k
    exact this
  · -- muxB
    intro k
    have := hmux (B a b) b (fun j => gMin [A a b j, B a b j]) rfl
      (fun k _ => by unfold B; rw [it_succ]; rfl) k
    show B a b (ph N k) = if tst (refS a b N sB k) then _ else _
    cases k with
    | zero => exact this
    | succ k => exact this
  · intro c hc k; simp at hc; rcases hc with rfl | rfl <;> rfl
  · intro k; rfl
  · intro c hc k; simp at hc; rcases hc with rfl | rfl | rfl | rfl <;> rfl
  · exact ⟨rfl, fun k => rfl⟩
  · exact ⟨rfl, fun k => rfl⟩
  · intro k; rfl
  · -- brA
    intro i bb hb
    show refS a b N (coutA bb) _ = gEnc [cndS a b N i, A a b (ph N i)] / 2
    rw [hdiv]
    have hs : selE (refS a b N jA i) = decide (ph N i < N) := hsel i _
    cases bb
    · show (0 : Nat) = _
      have : ph N i = N := by
        rw [hs] at hb; have := ph_le N i; simp at hb; omega
      rw [this, h2]
    · show A a b (_ % N) = _
      have hlt : ph N i < N := by rw [hs] at hb; simpa using hb
      have : cnt (fun i' => selE (refS a b N jA i') == true) i = qq N i * N + ph N i := by
        rw [← cnt_ph]; apply cnt_congr; intro i'
        show (selE (gEnc [cndS a b N i', A a b (ph N i')]) == true) = _
        rw [hsel]; simp
      rw [this, mod_idx hlt]
  · intro k; rfl
  · -- brB
    intro i bb hb
    show refS a b N (coutB bb) _ = gEnc [cndS a b N i, B a b (ph N i)] / 2
    rw [hdiv]
    have hs : selE (refS a b N jB i) = decide (ph N i < N) := hsel i _
    cases bb
    · show B a b N = _
      have : ph N i = N := by
        rw [hs] at hb; have := ph_le N i; simp at hb; omega
      rw [this]
    · show B a b (_ % N) = _
      have hlt : ph N i < N := by rw [hs] at hb; simpa using hb
      have : cnt (fun i' => selE (refS a b N jB i') == true) i = qq N i * N + ph N i := by
        rw [← cnt_ph]; apply cnt_congr; intro i'
        show (selE (gEnc [cndS a b N i', B a b (ph N i')]) == true) = _
        rw [hsel]; simp
      rw [this, mod_idx hlt]
  · trivial
  · intro c hc k; simp at hc; rcases hc with rfl | rfl <;> rfl
  · intro c hc k; simp at hc; rcases hc with rfl | rfl <;> rfl
  · intro k; rfl
  · intro k; rfl
  · trivial

/-! ## The circuit computes gcd -/

/-- The gcd-shaped loop built from bdc's cells: every token latched on `out`
is `Nat.gcd a b`.

Assumed (each a named hypothesis): the gate models of the 15 cell instances
(`H_MUX*`, `H_FORK*`, `H_ISNZ`, `H_JOIN*`, `H_BR*`, `H_SUB`, `H_MIN`,
`H_SNKA`: SI gates, DI fan-out wires, ideal data path; the internal C-element
traces `j0*`, `j1*` of the two muxes are existentially free), the environment
(`H_SRC*`: the sources follow the protocol and offer the arguments;
`H_ENV_OUT`: the result's consumer follows the protocol), the two initial-token
buffers (`H_INITBUF*`), and `H_BUNDLE` on every channel. -/
theorem gcd_circuit (a b : Nat) (hb : b % 2 = 1) (ha : a = 0 ∨ a % 2 = 1)
    (ch : GC → Chan) (j0A j1A j0B j1B : Trace)
    (H_MUXA : Mux tst (ch inA) (ch backA) (ch sA) (ch hA) j0A j1A)
    (H_MUXB : Mux tst (ch inB) (ch backB) (ch sB) (ch hB) j0B j1B)
    (H_FORKA : Fork (ch hA) [ch hA1, ch hA2])
    (H_ISNZ : Join gNZ [ch hA1] (ch cnd))
    (H_FORKC : Fork (ch cnd) [ch cA, ch cB, ch sA', ch sB'])
    (H_JOINA : Join gEnc [ch cA, ch hA2] (ch jA))
    (H_BRA : Steer selE (· / 2) (ch jA) (fun b => ch (coutA b)))
    (H_JOINB : Join gEnc [ch cB, ch hB] (ch jB))
    (H_BRB : Steer selE (· / 2) (ch jB) (fun b => ch (coutB b)))
    (H_SNKA : Sink (ch aF))
    (H_FORKAT : Fork (ch aT) [ch a1, ch a2])
    (H_FORKBT : Fork (ch bT) [ch b1, ch b2])
    (H_SUB : Join gSub [ch a1, ch b1] (ch backA))
    (H_MIN : Join gMin [ch a2, ch b2] (ch backB))
    (H_SRCA : OpProto ch [] [inA] ∧ OpData ch [] [inA] (fun σ => ∀ k, σ inA k = a))
    (H_SRCB : OpProto ch [] [inB] ∧ OpData ch [] [inB] (fun σ => ∀ k, σ inB k = b))
    (H_INITBUFA : OpProto ch [sA'] [sA] ∧ OpData ch [sA'] [sA] (ibEq sA' sA))
    (H_INITBUFB : OpProto ch [sB'] [sB] ∧ OpData ch [sB'] [sB] (ibEq sB' sB))
    (H_ENV_OUT : OpProto ch [out] [])
    (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ k e, TokAt (ch out) k e → (ch out).dat e = Nat.gcd a b := by
  have hops : ∀ o, OpProto ch (net.ins o) (net.outs o) ∧
      OpData ch (net.ins o) (net.outs o) (E a b o) := by
    intro o
    cases o
    · exact H_SRCA
    · exact H_SRCB
    · exact mux_op ch sA inA backA hA j0A j1A H_MUXA
    · exact mux_op ch sB inB backB hB j0B j1B H_MUXB
    · exact fork_op ch hA [hA1, hA2] H_FORKA
    · exact join_op ch [hA1] cnd H_ISNZ
    · exact fork_op ch cnd [cA, cB, sA', sB'] H_FORKC
    · exact H_INITBUFA
    · exact H_INITBUFB
    · exact join_op ch [cA, hA2] jA H_JOINA
    · exact steer_op ch jA coutA H_BRA
    · exact join_op ch [cB, hB] jB H_JOINB
    · exact steer_op ch jB coutB H_BRB
    · exact sink_op ch aF H_SNKA
    · exact fork_op ch aT [a1, a2] H_FORKAT
    · exact fork_op ch bT [b1, b2] H_FORKBT
    · exact join_op ch [a1, b1] backA H_SUB
    · exact join_op ch [a2, b2] backB H_MIN
    · exact ⟨H_ENV_OUT, fun _ _ c hc => by cases hc⟩
  obtain ⟨N, h1, h2, h3⟩ := loop_N _ _ _ _ (Kahn.Gcd.cLoop_gcd (a + b + 1) a b (by omega) hb ha)
  intro k e h
  rw [net_refines_close net ch (E a b) (fun o => (hops o).1) H_BUNDLE (fun o => (hops o).2)
    (refS a b N) (refS_solves a b N h1 h2) out k e h]
  exact h3

end Formal.Net.Ops.Gcd
