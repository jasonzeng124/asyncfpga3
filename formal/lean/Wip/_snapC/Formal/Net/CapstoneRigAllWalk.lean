import Formal.Net.CapstoneCut

/-!
# Probe C-8s3: the periodic walk, and the circuit induction for repeated invocations

8r's circuit induction (`CapstoneCut.main`) tracks the control-spine token along the walk
`walk σ`, which starts at `start` and ends at the sink of `g251.0` (channel 417). It uses
H_START_ONCE in exactly one place: a rise of `start` must be the walk's next step, and the
walk never re-enters `start`.

Here the walk is made periodic (`walkR`): when the token leaves `z251` (channel 464, the last
arbiter output, forked by `forkG 464 [417, 413]` to the function-end sink and to `out0`'s
select), it re-enters `start` instead of moving to 417. Channel 417 (a dead end into a sink)
is dropped from the invariant: the circuit may lag on it, which the gate models allow (a fork
output moves with unbounded delay).

H_START_ONCE is replaced by **H_START_GATE**: `start` is offered for the `(k+1)`-th time only
after `z251` has been offered `k` times. With the periodic H_WALK (`WalkOKR`, proved for gcd_hw
in `CapstoneRigAllPer`), the same induction gives H_CM_FORCED for every offer of the whole run
and therefore (8m's `gcd_hw_circuit_safe`) every value latched on `out0`, in every invocation,
is `gcd a b`.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw
open Formal.Net.CapSafe Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut

set_option maxRecDepth 100000

/-- `z251`: the last arbiter output; its spine successor is the end channel. -/
def zEnd : Fin NC := 464
/-- `g251.0`: the function-end control channel (into a sink). -/
def eEnd : Fin NC := 417

theorem zEnd_sp : sp zEnd = true := by decide
theorem eEnd_sp : sp eEnd = true := by decide
theorem zEnd_ne_start : zEnd ≠ start := by decide
theorem eEnd_ne_start : eEnd ≠ start := by decide
theorem eEnd_ne_zEnd : eEnd ≠ zEnd := by decide
theorem cons_eEnd : opAt (consOf eEnd) = .sink eEnd := rfl
theorem prod_eEnd : opAt (prodOf eEnd) = .forkG zEnd [eEnd, 413] := rfl
theorem cons_zEnd : opAt (consOf zEnd) = .forkG zEnd [eEnd, 413] := rfl

/-- Every spine channel except `eEnd` has a spine successor (no dead end but 417's sink). -/
def liveOK (c : Fin NC) : Bool :=
  match opAt (consOf c) with
  | .link _ o => sp o
  | .forkG _ os => (os.find? sp).isSome
  | .bjoin _ o _ _ => sp o
  | .steerC _ t _ => sp t
  | .amerge _ _ _ _ => true
  | _ => false

def liveOKn (n : Nat) : Bool := if h : n < NC then (n == 417 || liveOK ⟨n, h⟩) else true

theorem liveOK_chk : spN.all liveOKn = true := by decide +kernel

theorem liveOK_of {c : Fin NC} (hs : sp c = true) (he : c ≠ eEnd) : liveOK c = true := by
  have hm := sp_mem hs
  have := List.all_eq_true.mp liveOK_chk c.val hm
  simp only [liveOKn, c.isLt, dite_true] at this
  have hne : (c.val == 417) = false := by
    cases h : c.val == 417
    · rfl
    · exfalso; apply he; apply Fin.ext; simpa using h
  rw [hne, Bool.false_or] at this
  exact this

variable (σ : Fin NC → Nat → Nat)

theorem nxt_some_of_live {c : Fin NC} (hs : sp c = true) (he : c ≠ eEnd) (k : Nat) :
    ∃ e, nxt σ c k = some e := by
  have hl := liveOK_of hs he
  unfold liveOK at hl
  unfold nxt
  split at hl
  · rename_i heq; rw [heq]; simp [hl]
  · rename_i heq; rw [heq]
    cases h : List.find? sp _ with
    | none => rw [h] at hl; simp at hl
    | some e => exact ⟨e, rfl⟩
  · rename_i heq; rw [heq]; simp [hl]
  · rename_i heq; rw [heq]; simp [hl]
  · rename_i heq; rw [heq]; simp
  · simp at hl

theorem nxt_eEnd {d : Fin NC} {k : Nat} (h : nxt σ d k = some eEnd) : d = zEnd := by
  have := nxt_in σ h
  rw [prod_eEnd] at this
  simpa [K.insC] using this

theorem nxt_zEnd (k : Nat) : nxt σ zEnd k = some eEnd := by
  rw [nxt_forkG σ cons_zEnd]; decide

/-! ## The periodic walk -/

/-- The periodic walk's successor: `eEnd` and dead ends are replaced by `start`. -/
def nxtR (c : Fin NC) (k : Nat) : Fin NC :=
  match nxt σ c k with
  | some e => if e = eEnd then start else e
  | none => start

structure WR where
  cur : Fin NC
  W : Fin NC → Nat

def wstepR (s : WR) : WR :=
  ⟨nxtR σ s.cur (s.W s.cur), fun d => s.W d + if d = s.cur then 1 else 0⟩

def walkR : Nat → WR
  | 0 => ⟨start, fun _ => 0⟩
  | p + 1 => wstepR σ (walkR p)

/-- **Periodic H_WALK**: arriving at an arbiter stage, the periodic walk finds the oracle's next
label naming the input it arrives on. -/
def WalkOKR (om : Nat → Nat → Bool) : Prop :=
  ∀ p x y z w, opAt (consOf (walkR σ p).cur) = .amerge x y z w →
    om w ((walkR σ p).W z) = decide ((walkR σ p).cur = y)

theorem W_succR (p : Nat) (c : Fin NC) :
    (walkR σ (p + 1)).W c = (walkR σ p).W c + bn ((walkR σ p).cur == c) := by
  show (wstepR σ (walkR σ p)).W c = _
  simp only [wstepR, bn]
  by_cases h : c = (walkR σ p).cur
  · subst h; simp
  · have : ((walkR σ p).cur == c) = false := by simp [Ne.symm h]
    simp [h, this]

theorem cur_succR (p : Nat) :
    (walkR σ (p + 1)).cur = nxtR σ (walkR σ p).cur ((walkR σ p).W (walkR σ p).cur) := rfl

theorem nxtR_of {d c : Fin NC} {k : Nat} (h : nxtR σ d k = c) (hc : c ≠ start) :
    nxt σ d k = some c ∧ c ≠ eEnd := by
  unfold nxtR at h
  split at h
  · rename_i e he
    split at h
    · exact absurd h.symm hc
    · rename_i hee; subst h; exact ⟨he, hee⟩
  · exact absurd h.symm hc

theorem nxtR_eq {d c : Fin NC} {k : Nat} (h : nxt σ d k = some c) (hc : c ≠ eEnd) :
    nxtR σ d k = c := by
  unfold nxtR; rw [h]; simp [hc]

theorem nxtR_ne_eEnd (d : Fin NC) (k : Nat) : nxtR σ d k ≠ eEnd := by
  unfold nxtR
  split
  · split
    · exact Ne.symm eEnd_ne_start
    · assumption
  · exact Ne.symm eEnd_ne_start

theorem curR_ne_eEnd : ∀ p, (walkR σ p).cur ≠ eEnd
  | 0 => Ne.symm eEnd_ne_start
  | p + 1 => by rw [cur_succR]; exact nxtR_ne_eEnd σ _ _

theorem curR_sp : ∀ p, sp (walkR σ p).cur = true
  | 0 => sp_start
  | p + 1 => by
    rw [cur_succR]
    unfold nxtR
    split
    · split
      · exact sp_start
      · rename_i e he _; exact nxt_sp σ he
    · exact sp_start

/-- `nxtR` re-enters `start` exactly from `zEnd` (among spine channels other than `eEnd`). -/
theorem nxtR_start {d : Fin NC} (hs : sp d = true) (he : d ≠ eEnd) (k : Nat) :
    nxtR σ d k = start ↔ d = zEnd := by
  constructor
  · intro h
    obtain ⟨e, hn⟩ := nxt_some_of_live σ hs he k
    unfold nxtR at h; rw [hn] at h
    simp only at h
    split at h
    · rename_i hee; subst hee; exact nxt_eEnd σ hn
    · subst h
      have := nxt_in σ hn
      rw [prod_start] at this; simp [K.insC] at this
  · intro h; subst h; unfold nxtR; rw [nxt_zEnd]; simp

/-- Transitions of the periodic walk into `c`. -/
def trR (c : Fin NC) (q : Nat) : Bool :=
  nxtR σ (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) == c

def visR (c : Fin NC) (q : Nat) : Bool := (walkR σ q).cur == c

theorem W_eqR : ∀ p c, (walkR σ p).W c = cnt (visR σ c) p := by
  intro p
  induction p with
  | zero => intro c; rfl
  | succ p ih => intro c; rw [W_succR, ih, cnt_succ']; rfl

theorem flowR : ∀ p c, (walkR σ p).W c + bn ((walkR σ p).cur == c) =
    cnt (trR σ c) p + bn (c == start) := by
  intro p
  induction p with
  | zero =>
    intro c
    show 0 + bn (start == c) = 0 + bn (c == start)
    by_cases h : c = start
    · subst h; simp
    · have h1 : (start == c) = false := by simp [Ne.symm h]
      have h2 : (c == start) = false := by simp [h]
      rw [h1, h2]
  | succ p ih =>
    intro c
    rw [W_succR, cur_succR, cnt_succ']
    have hc := ih c
    show _ = cnt (trR σ c) p + bn (trR σ c p) + _
    unfold trR at *
    omega

theorem cnt_visitR (j : Fin NC) (f : Nat → Bool) : ∀ p,
    cnt (fun q => visR σ j q && f ((walkR σ q).W j)) p = cnt f ((walkR σ p).W j) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [cnt_succ', ih, W_succR]
    cases hv : visR σ j p
    · have : ((walkR σ p).cur == j) = false := hv
      simp [bn, this]
    · have : ((walkR σ p).cur == j) = true := hv
      simp only [Bool.true_and, bn, this, ite_true]; rw [cnt_succ']; rfl

theorem in_cpR {c i : Fin NC} (hin : ∀ d k, sp d = true → d ≠ eEnd → (nxtR σ d k = c ↔ d = i)) :
    ∀ p, cnt (trR σ c) p = (walkR σ p).W i := by
  intro p
  rw [W_eqR]
  apply CM.cnt_congr_lt
  intro q _
  unfold trR visR
  have hs := curR_sp σ q
  have he := curR_ne_eEnd σ q
  have := hin (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) hs he
  by_cases hdi : (walkR σ q).cur = i
  · rw [hdi] at this ⊢; simp [this.2 rfl]
  · have h1 : (nxtR σ (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) == c) = false := by
      cases hn : nxtR σ (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) == c
      · rfl
      · exact absurd (this.1 (by simpa using hn)) hdi
    have h2 : ((walkR σ q).cur == i) = false := by simp [hdi]
    rw [h1, h2]

theorem in_stR {c j : Fin NC} {b : Bool}
    (hin : ∀ d k, sp d = true → d ≠ eEnd → (nxtR σ d k = c ↔ d = j ∧ sel2 (σ j k) = b)) :
    ∀ p, cnt (trR σ c) p = cnt (fun k => sel2 (σ j k) == b) ((walkR σ p).W j) := by
  intro p
  rw [← cnt_visitR]
  apply CM.cnt_congr_lt
  intro q _
  unfold trR visR
  have hs := curR_sp σ q
  have he := curR_ne_eEnd σ q
  have := hin (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) hs he
  by_cases hdj : (walkR σ q).cur = j
  · rw [hdj] at this ⊢
    cases hb : (sel2 (σ j ((walkR σ q).W j)) == b)
    · have h1 : (nxtR σ j ((walkR σ q).W j) == c) = false := by
        cases hn : nxtR σ j ((walkR σ q).W j) == c
        · rfl
        · have := (this.1 (by simpa using hn)).2; simp [this] at hb
      rw [h1]; simp
    · have := this.2 ⟨rfl, by simpa using hb⟩
      simp [this]
  · have h1 : (nxtR σ (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) == c) = false := by
      cases hn : nxtR σ (walkR σ q).cur ((walkR σ q).W (walkR σ q).cur) == c
      · rfl
      · exact absurd (this.1 (by simpa using hn)).1 hdj
    have h2 : ((walkR σ q).cur == j) = false := by simp [hdj]
    rw [h1, h2]; simp

/-- The arbiter's input counts along the periodic walk. -/
theorem am_sideR (ω : Nat → Bool) {x y z : Fin NC} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hzs : z ≠ start)
    (hin : ∀ d k, sp d = true → d ≠ eEnd → (nxtR σ d k = z ↔ d = x ∨ d = y))
    (hw : ∀ p, ((walkR σ p).cur = x ∨ (walkR σ p).cur = y) →
      ω ((walkR σ p).W z) = decide ((walkR σ p).cur = y)) :
    ∀ p, (walkR σ p).W y = cnt ω ((walkR σ p).W z) +
        bn (((walkR σ p).cur == z) && ω ((walkR σ p).W z)) ∧
      (walkR σ p).W x = cnt (fun i => !ω i) ((walkR σ p).W z) +
        bn (((walkR σ p).cur == z) && !ω ((walkR σ p).W z)) := by
  intro p
  induction p with
  | zero =>
    have : (start == z) = false := by simp [Ne.symm hzs]
    show 0 = 0 + bn ((start == z) && _) ∧ 0 = 0 + bn ((start == z) && _)
    rw [this]; simp [bn]
  | succ p ih =>
    obtain ⟨iy, ix⟩ := ih
    rw [W_succR, W_succR, W_succR, cur_succR]
    generalize hd : (walkR σ p).cur = d at iy ix hw
    have hs : sp d = true := hd ▸ curR_sp σ p
    have he : d ≠ eEnd := hd ▸ curR_ne_eEnd σ p
    by_cases hdz : d = z
    · subst hdz
      have hn : (nxtR σ d ((walkR σ p).W d) == d) = false := by
        cases hq : nxtR σ d ((walkR σ p).W d) == d
        · rfl
        · exfalso
          have e1 : nxtR σ d ((walkR σ p).W d) = d := by simpa using hq
          have := (nxtR_of σ e1 hzs).1
          exact nxt_ne σ this rfl
      have h1 : (d == y) = false := by simp [hzy]
      have h2 : (d == x) = false := by simp [hzx]
      have h3 : (d == d) = true := by simp
      rw [hn, h1, h2, h3]
      simp only [h3, Bool.true_and] at iy ix
      simp only [Bool.false_and, bn, ite_true, Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [cnt_succ', cnt_succ']
      cases hω : ω ((walkR σ p).W d) <;> simp [hω, bn] at iy ix ⊢ <;> omega
    · have hzd : (d == z) = false := by simp [hdz]
      rw [hzd] at iy ix
      simp only [Bool.false_and, bn, Bool.false_eq_true, ite_false, Nat.add_zero] at iy ix
      rw [hzd]
      simp only [bn, Bool.false_eq_true, ite_false, Nat.add_zero]
      by_cases hdy : d = y
      · subst hdy
        have hn := (hin d ((walkR σ p).W d) hs he).2 (Or.inr rfl)
        have hω := hw p (Or.inr hd)
        rw [hd] at hω
        simp only [decide_true] at hω
        have h2 : (d == x) = false := by simp [Ne.symm hxy]
        rw [hn, h2]
        simp [hω, iy, ix]
      · by_cases hdx : d = x
        · subst hdx
          have hn := (hin d ((walkR σ p).W d) hs he).2 (Or.inl rfl)
          have hω := hw p (Or.inl hd)
          rw [hd] at hω
          simp only [hdy, decide_false] at hω
          have h1 : (d == y) = false := by simp [hdy]
          rw [hn, h1]
          simp [hω, iy, ix]
        · have hn : (nxtR σ d ((walkR σ p).W d) == z) = false := by
            cases hq : nxtR σ d ((walkR σ p).W d) == z
            · rfl
            · have := (hin d _ hs he).1 (by simpa using hq)
              rcases this with e | e <;> contradiction
          have h1 : (d == y) = false := by simp [hdy]
          have h2 : (d == x) = false := by simp [hdx]
          rw [h1, h2, hn]
          simp only [Bool.false_and, Bool.false_eq_true, ite_false, Nat.add_zero]
          exact ⟨iy, ix⟩

theorem cur_of_boundR {c : Fin NC} {p : Nat} (hcs : c ≠ start)
    (hb : (walkR σ p).W c + 1 ≤ cnt (trR σ c) p) : (walkR σ p).cur = c := by
  have hf := flowR σ p c
  have h0 : (c == start) = false := by simp [hcs]
  rw [h0] at hf
  cases h : ((walkR σ p).cur == c)
  · rw [h] at hf; simp [bn] at hf; omega
  · simpa using h

/-- Re-entries into `start` are the visits of `zEnd`. -/
theorem tr_startR (p : Nat) : cnt (trR σ start) p = (walkR σ p).W zEnd :=
  in_cpR σ (fun d k hs he => nxtR_start σ hs he k) p

/-- Transitions into a channel produced by a one-spine-input operator, for the periodic walk. -/
theorem hin_oneR {c i : Fin NC} (hcs : c ≠ start) (hce : c ≠ eEnd)
    (hins : ∀ d, sp d = true → d ∈ (opAt (prodOf c)).insC → d = i)
    (hn : ∀ k, nxt σ i k = some c) :
    ∀ d k, sp d = true → d ≠ eEnd → (nxtR σ d k = c ↔ d = i) := by
  intro d k hs _
  constructor
  · intro h; exact hins d hs (nxt_in σ (nxtR_of σ h hcs).1)
  · intro h; subst h; exact nxtR_eq σ (hn k) hce

end Formal.Net.CapNet.Gcd
