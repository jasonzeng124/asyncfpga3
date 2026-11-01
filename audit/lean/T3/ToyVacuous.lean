import Formal.Target.Spec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Audit T3: the frozen `NetCorrect` holds VACUOUSLY for a circuit that never answers

Against `Formal.Target.Spec` at formal 88c74e3c (frozen at 69c49057). Every Spec name used
here (`Net`, `Gate`, `Arc`, `Boundary`, `ArbNodes`, `GateOK`, `Behaves`, `circuit`, `ArbOK`,
`Env`, `SeqEnv`, `Correct`, `NetCorrect`, `NetCorrectSeq`) is the frozen definition; nothing
is copied.

## The toy netlist (parameter `L` = the "server wait", in ps)
nodes: 0 rst (env), 1 r1, 2 r2, 3 q, 4 A0, 5 input request (env, shared by a/b/start as in
the target), 6 input acknowledge, 7 out0/end request, 8 out0/end acknowledge (env).
gates: r1 := 0, r2 := 1 (constants), q := the held bd_arbiter's ustate O6 table
`0xFFF0FFB2` on pins (r1, r2, q, rst, A0) with 1 ps arcs (a feedback loop: q reads q),
A0 := rst through one arc of exactly `L` ps (a server that holds A0 for `L` ps),
input acknowledge := 0, out0 request := 0. The circuit NEVER acknowledges its input.
Arbiter list: `[⟨1, 2, 3⟩]`. Delay parameters `g = 1, κ = 0`.

## Results
* `toy_witness`: an explicit behaviour that satisfies `Behaves` and `Env` (one pair offered)
  and `SeqEnv`, and violates `Correct` (the input is never acknowledged).
* `toy_arbOK_big`: that behaviour satisfies `ArbOK T` for every `T > R + L`.
* `toy_vacuous`: for `1 ≤ T ≤ R + L` (and `1 ≤ L ≤ R`), `Behaves ∧ ArbOK T ∧ Env` has NO
  model at all, so `NetCorrect` (and `NetCorrectSeq`) hold for this broken circuit.
* `toy_iff`: `NetCorrect toy … T R su Δo ↔ T ≤ R + L` (same for `NetCorrectSeq`).
So the truth value of the frozen statement, for a circuit that never answers, is decided
by whether the arbiter's server holds A0 for longer than T, not by the circuit's behaviour
at the boundary. The mechanism is exactly shard B's (q must flip at A0's fall while both
requests are constant, and `ArbOK` forbids that).
-/

open Formal.Target

namespace Audit.T3.Toy

def a1 : Arc := ⟨1, 1, 1, 1⟩
def aL (L : Nat) : Arc := ⟨L, L, L, L⟩

def qInit : Nat := 0xFFF0FFB2

def gR1 : Gate := ⟨"r1 := 0", 0, 0, [], [], 1⟩
def gR2 : Gate := ⟨"r2 := 1", 0, 1, [], [], 2⟩
def gQ : Gate := ⟨"ustate.O6", 5, qInit, [1, 2, 3, 0, 4], [a1, a1, a1, a1, a1], 3⟩
def gA0 (L : Nat) : Gate := ⟨"A0 := rst after L", 1, 2, [0], [aL L], 4⟩
def gAck : Gate := ⟨"in ack := 0", 0, 0, [], [], 6⟩
def gOreq : Gate := ⟨"out0 req := 0", 0, 0, [], [], 7⟩

def toyNet (L : Nat) : Net := ⟨9, [], [gR1, gR2, gQ, gA0 L, gAck, gOreq]⟩

def inCh : InCh := ⟨5, 6, []⟩
def outCh : OutCh := ⟨7, 8, []⟩
def toyB : Boundary := ⟨0, inCh, inCh, inCh, outCh, outCh, [0, 5, 8]⟩
def toyA : List ArbNodes := [⟨1, 2, 3⟩]

def p1 : DelayPar := ⟨1, 0⟩

theorem circuit_gates (L : Nat) : (circuit (toyNet L) toyB).gates = (toyNet L).gates := by
  simp [circuit, toyNet, toyB, Boundary.envNodes, gR1, gR2, gQ, gA0, gAck, gOreq]

/-! ### small facts -/

theorem start_const (p : DelayPar) (g : Gate) (h : g.arcs = []) : g.start p = 0 := by
  simp [Gate.start, h]

theorem start_q : gQ.start p1 = 1 := by
  simp [Gate.start, gQ, a1, p1]
  rfl

theorem start_A0 (L : Nat) : (gA0 L).start p1 = L := by
  simp only [Gate.start, gA0, aL, p1, List.map, List.foldr]
  have e : ((L : ℕ) : ℚ) = ((L : ℤ) : ℚ) := (Int.cast_natCast L).symm
  rw [mul_one, e, Rat.ceil_intCast]
  simp

/-- With `g = 1, κ = 0` an arc whose four numbers are all `m` admits exactly delay `m`. -/
theorem adm_exact (c : ℚ) (m d : Nat) (h : Adm p1 c ⟨m, m, m, m⟩ d) : d = m := by
  obtain ⟨h1, h2, -, -⟩ := h
  simp only [p1, div_one, mul_one] at h1 h2
  have : (d : ℚ) = m := le_antisymm h2 h1
  exact_mod_cast this

theorem adm_of (c : ℚ) (m : Nat) : Adm p1 c ⟨m, m, m, m⟩ m := by
  have e : (1 - c) * (m : ℚ) + c * m = m := by ring
  simp [Adm, p1, lerp, e]

theorem qbit (v : Nat → Bool) (h0 : v 0 = false) (h1 : v 1 = true) :
    qInit.testBit (addr 5 v) = (v 3 || (v 4 && v 2)) := by
  simp only [addr, h0, h1]
  cases v 2 <;> cases v 3 <;> cases v 4 <;> decide

theorem bufbit (v : Nat → Bool) : (2 : Nat).testBit (addr 1 v) = v 0 := by
  simp only [addr]
  cases v 0 <;> decide

/-! ### the witness behaviour -/

def xw (L R : Nat) : Beh := fun n t =>
  if n = 0 then decide (t < R)
  else if n = 2 then true
  else if n = 3 then decide (t < R + L + 1)
  else if n = 4 then decide (t < R + L)
  else if n = 5 then decide (R < t)
  else false

theorem rises_req (L R t : Nat) : rises (xw L R 5) R t = if R < t then 1 else 0 := by
  induction t with
  | zero => simp [rises]
  | succ t ih =>
    simp only [rises, ih, xw]
    by_cases h1 : R < t
    · have : R < t + 1 := by omega
      simp [h1, this] <;> omega
    · by_cases h2 : t = R
      · subst h2; simp
      · have : ¬ R < t + 1 := by omega
        simp [h1, this] <;> omega

theorem rises_zero (s : Sig) (R t : Nat) (h : ∀ u, s u = false) : rises s R t = 0 := by
  induction t with
  | zero => simp [rises]
  | succ t ih => simp [rises, ih, h]

theorem constGate (c : ℚ) (g : Gate) (x : Beh) (hk : g.k = 0) (ha : g.arcs = [])
    (hv : ∀ t, x g.out t = g.init.testBit 0) : GateOK p1 c g x := by
  refine ⟨fun _ _ => 0, fun i hi => by omega, fun t _ => ⟨fun i hi => by omega, ?_⟩⟩
  rw [hk, hv t]; rfl

theorem toy_behaves (L R : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) : Behaves p1 (circuit (toyNet L) toyB) (xw L R) := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rw [circuit_gates]
  intro g hg
  simp only [toyNet, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gR1, xw])
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gR2, xw])
  · -- the arbiter's state gate, 1 ps reads
    refine ⟨fun _ t => t - 1, fun _ _ _ _ h => Nat.sub_le_sub_right h 1, ?_⟩
    intro t ht
    rw [start_q] at ht
    refine ⟨fun i hi => ⟨Nat.sub_le t 1, ?_⟩, ?_⟩
    · have hi' : gQ.arcs.getD i default = a1 := by
        simp only [gQ] at hi ⊢
        rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | (exfalso; omega)
      rw [hi']
      have e : t - (t - 1) = 1 := by omega
      rw [e]; exact adm_of 0 1
    · show xw L R 3 t = qInit.testBit (addr 5 fun i => xw L R ([1, 2, 3, 0, 4].getD i 0) (t - 1))
      rw [qbit _ (by simp [xw]) (by simp [xw])]
      simp only [xw, List.getD_cons_succ, List.getD_cons_zero]
      simp
      by_cases h : t < R + L + 1 <;> simp [h] <;> omega
  · -- A0 := rst after exactly L ps
    refine ⟨fun _ t => t - L, fun _ _ _ _ h => Nat.sub_le_sub_right h L, ?_⟩
    intro t ht
    rw [start_A0] at ht
    refine ⟨fun i hi => ⟨Nat.sub_le t L, ?_⟩, ?_⟩
    · have hi0 : i = 0 := by simp [gA0] at hi; omega
      subst hi0
      have e : t - (t - L) = L := by omega
      rw [e]; exact adm_of 0 L
    · show xw L R 4 t = (2 : Nat).testBit (addr 1 fun i => xw L R ([0].getD i 0) (t - L))
      rw [bufbit]
      simp [xw]
      omega
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gAck, xw])
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gOreq, xw])

theorem envIn_w (L R su : Nat) : EnvIn (xw L R) inCh R su (some 1) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; simp [inCh, xw]; omega
  · intro t ht hne
    simp only [inCh, xw] at hne ⊢
    simp at hne ⊢
    omega
  · intro t ht _ _
    exact ⟨t + 1, by omega, by simp [inCh, xw]; omega⟩
  · intro t ht _
    simp only [inCh, Offered, rises_req]
    split <;> omega
  · intro t _ _ _ s _ _; simp [busVal, inCh]
  · intro t _ _ _; simp [busVal, inCh]

theorem envOut_w (L R Δo : Nat) : EnvOut (xw L R) outCh R Δo := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _; simp [outCh, xw]
  · intro t _ h; simp [outCh, xw] at h
  · intro t _ h; simp [outCh, xw] at h
  · intro t _ _ h; simp [outCh, xw] at h

theorem toy_env (L R su Δo : Nat) :
    Env (xw L R) toyB R su Δo (some 1) (fun _ => 0) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, envIn_w L R su, envIn_w L R su, envIn_w L R su, envOut_w L R Δo, envOut_w L R Δo⟩
  · intro t ht; simp [toyB, xw, ht]
  · intro t ht; simp [toyB, xw]; omega
  · intro k _; show 0 < 2 ^ 31 ∧ 0 < 2 ^ 31; decide

theorem toy_seq (L R : Nat) : SeqEnv (xw L R) toyB R := by
  intro ch hch t ht h0 _
  simp only [toyB, List.mem_cons, List.not_mem_nil, or_false, or_self] at hch
  subst hch
  have e8 : rises (xw L R toyB.out0.ack) R t = 0 :=
    rises_zero _ R t (fun u => by show xw L R 8 u = false; simp [xw])
  refine ⟨?_, ?_, ?_⟩
  · rw [e8]
    show rises (xw L R 5) R t ≤ 0
    rw [rises_req]
    have : t ≤ R := by
      have h0' : xw L R 5 t = false := h0
      simp [xw] at h0'; omega
    split <;> omega
  · show xw L R 7 t = false; simp [xw]
  · show xw L R 8 t = false; simp [xw]

theorem toy_not_correct (L R Δo : Nat) :
    ¬ Correct (xw L R) toyB R Δo (some 1) (fun _ => 0) (fun _ => 0) := by
  intro hc
  obtain ⟨⟨_, _, hlive⟩, _⟩ := hc
  obtain ⟨s, hs, he⟩ := hlive (R + 1) (by omega) (by simp [toyB, inCh, xw])
  simp [toyB, inCh, xw] at he
  omega

theorem toy_arbOK_big (L R T : Nat) (hT : R + L + 1 ≤ T) : ArbOK T toyA (xw L R) := by
  intro a ha t1 t2 _ _ t h1 _
  simp only [toyA, List.mem_singleton] at ha
  subst ha
  simp [xw]
  omega

/-- The witness: Behaves ∧ Env ∧ SeqEnv ∧ ¬Correct (for every T) and ArbOK for T > R + L. -/
theorem toy_witness (L R su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) :
    Behaves p1 (circuit (toyNet L) toyB) (xw L R) ∧
    Env (xw L R) toyB R su Δo (some 1) (fun _ => 0) (fun _ => 0) ∧ SeqEnv (xw L R) toyB R ∧
    ¬ Correct (xw L R) toyB R Δo (some 1) (fun _ => 0) (fun _ => 0) :=
  ⟨toy_behaves L R hL hLR, toy_env L R su Δo, toy_seq L R, toy_not_correct L R Δo⟩

/-! ### vacuity: no model of Behaves ∧ ArbOK T ∧ Env when 1 ≤ T ≤ R + L -/

theorem toy_no_model (L R T su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) (hT1 : 1 ≤ T) (hT2 : T ≤ R + L)
    (x : Beh) (n : Option Nat) (va vb : Nat → Nat)
    (hB : Behaves p1 (circuit (toyNet L) toyB) x) (hA : ArbOK T toyA x)
    (hE : Env x toyB R su Δo n va vb) : False := by
  obtain ⟨c, -, -, hg⟩ := hB
  rw [circuit_gates] at hg
  have mem : ∀ g, g = gR1 ∨ g = gR2 ∨ g = gQ ∨ g = gA0 L → g ∈ (toyNet L).gates := by
    intro g hg'; rcases hg' with rfl | rfl | rfl | rfl <;> simp [toyNet]
  -- rst
  have hrst : ∀ t, x 0 t = decide (t < R) := by
    intro t
    by_cases h : t < R
    · simp [h]; exact hE.1 t h
    · simp [h]; exact hE.2.1 t (by omega)
  -- constants
  have hr1 : ∀ t, x 1 t = false := by
    intro t
    obtain ⟨f, -, h⟩ := hg gR1 (mem _ (Or.inl rfl))
    have := (h t (by rw [start_const p1 gR1 rfl]; omega)).2
    simpa [gR1, addr] using this
  have hr2 : ∀ t, x 2 t = true := by
    intro t
    obtain ⟨f, -, h⟩ := hg gR2 (mem _ (Or.inr (Or.inl rfl)))
    have := (h t (by rw [start_const p1 gR2 rfl]; omega)).2
    simpa [gR2, addr] using this
  -- A0
  have hA0 : ∀ t, L ≤ t → x 4 t = x 0 (t - L) := by
    intro t ht
    obtain ⟨f, -, h⟩ := hg (gA0 L) (mem _ (Or.inr (Or.inr (Or.inr rfl))))
    obtain ⟨hr, hv⟩ := h t (by rw [start_A0]; exact ht)
    obtain ⟨hle, hadm⟩ := hr 0 (by simp [gA0])
    have hd := adm_exact c L _ (by simpa [gA0, aL] using hadm)
    have hf : f 0 t = t - L := by omega
    have : x 4 t = (2 : Nat).testBit (addr 1 fun i => x ([0].getD i 0) (f i t)) := by
      simpa [gA0] using hv
    rw [this, bufbit]
    simp [hf]
  -- q
  have hq : ∀ t, 1 ≤ t → x 3 t = (x 0 (t - 1) || (x 4 (t - 1) && x 3 (t - 1))) := by
    intro t ht
    obtain ⟨f, -, h⟩ := hg gQ (mem _ (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨hr, hv⟩ := h t (by rw [start_q]; exact ht)
    have hf : ∀ i, i < 5 → f i t = t - 1 := by
      intro i hi
      obtain ⟨hle, hadm⟩ := hr i (by simpa [gQ] using hi)
      have harc : gQ.arcs.getD i default = ⟨1, 1, 1, 1⟩ := by
        simp only [gQ]
        rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | (exfalso; omega)
      rw [harc] at hadm
      have := adm_exact c 1 _ hadm
      omega
    have : x 3 t = qInit.testBit (addr 5 fun i => x ([1, 2, 3, 0, 4].getD i 0) (f i t)) := by
      simpa [gQ] using hv
    rw [this, qbit _ (by simp [hf 0 (by omega), hr1]) (by simp [hf 1 (by omega), hr2])]
    simp [hf 2 (by omega), hf 3 (by omega), hf 4 (by omega)]
  -- q stays high on [1, R + L]
  have hhigh : ∀ t, 1 ≤ t → t ≤ R + L → x 3 t = true := by
    intro t ht1 ht2
    induction t, ht1 using Nat.le_induction with
    | base => rw [hq 1 le_rfl, hrst]; simp; omega
    | succ t ht ih =>
      rw [hq (t + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      by_cases h : t < R
      · rw [hrst]; simp [h]
      · rw [hA0 t (by omega), hrst, hrst, ih (by omega)]
        simp; omega
  -- q low at R + L + 1
  have hlow : x 3 (R + L + 1) = false := by
    rw [hq _ (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [hrst, hA0 (R + L) (by omega), hrst]
    simp
  -- ArbOK on [0, R + L + 1]: requests constant, so q is constant on [T, R + L + 1]
  have hc := hA ⟨1, 2, 3⟩ (by simp [toyA]) 0 (R + L + 1)
    (fun t _ _ => by simp [hr1]) (fun t _ _ => by simp [hr2])
  have := hc (R + L + 1) (by omega) le_rfl
  rw [Nat.zero_add, hlow, hhigh T hT1 hT2] at this
  exact Bool.false_ne_true this

theorem toy_vacuous (L R T su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) (hT1 : 1 ≤ T) (hT2 : T ≤ R + L) :
    NetCorrect (toyNet L) toyB toyA p1 T R su Δo ∧ NetCorrectSeq (toyNet L) toyB toyA p1 T R su Δo :=
  ⟨fun x n va vb hB hA hE => (toy_no_model L R T su Δo hL hLR hT1 hT2 x n va vb hB hA hE).elim,
   fun x n va vb hB hA hE _ => (toy_no_model L R T su Δo hL hLR hT1 hT2 x n va vb hB hA hE).elim⟩

theorem toy_iff (L R T su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) (hT1 : 1 ≤ T) :
    (NetCorrect (toyNet L) toyB toyA p1 T R su Δo ↔ T ≤ R + L) ∧
    (NetCorrectSeq (toyNet L) toyB toyA p1 T R su Δo ↔ T ≤ R + L) := by
  refine ⟨⟨fun h => ?_, fun h => (toy_vacuous L R T su Δo hL hLR hT1 h).1⟩,
          ⟨fun h => ?_, fun h => (toy_vacuous L R T su Δo hL hLR hT1 h).2⟩⟩
  · by_contra hT
    exact toy_not_correct L R Δo (h (xw L R) (some 1) _ _ (toy_behaves L R hL hLR)
      (toy_arbOK_big L R T (by omega)) (toy_env L R su Δo))
  · by_contra hT
    exact toy_not_correct L R Δo (h (xw L R) (some 1) _ _ (toy_behaves L R hL hLR)
      (toy_arbOK_big L R T (by omega)) (toy_env L R su Δo) (toy_seq L R))

/-- For every T there is a netlist (server wait L = T) on which the frozen statement holds
only vacuously while the circuit never acknowledges. -/
theorem vacuous_every_T (T : Nat) (hT : 1 ≤ T) (su Δo : Nat) :
    ∃ L R, NetCorrect (toyNet L) toyB toyA p1 T R su Δo ∧
      ∃ x, Behaves p1 (circuit (toyNet L) toyB) x ∧
        Env x toyB R su Δo (some 1) (fun _ => 0) (fun _ => 0) ∧ SeqEnv x toyB R ∧
        ¬ Correct x toyB R Δo (some 1) (fun _ => 0) (fun _ => 0) :=
  ⟨T, T, (toy_vacuous T T T su Δo hT le_rfl hT (by omega)).1, xw T T,
    toy_witness T T su Δo hT le_rfl⟩

end Audit.T3.Toy

#print axioms Audit.T3.Toy.toy_iff
#print axioms Audit.T3.Toy.vacuous_every_T
#print axioms Audit.T3.Toy.toy_witness
