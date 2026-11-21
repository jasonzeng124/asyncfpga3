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

def liveOKn (n : Nat) : Bool :=
  if h : n < NC then (!(spL.getD n false) || n == 417 || liveOK ⟨n, h⟩) else true

theorem liveOK_chk : (List.range NC).all liveOKn = true := by decide +kernel

theorem liveOK_of {c : Fin NC} (hs : sp c = true) (he : c ≠ eEnd) : liveOK c = true := by
  have := List.all_eq_true.mp liveOK_chk c.val (List.mem_range.mpr c.isLt)
  simp only [liveOKn, c.isLt, dite_true] at this
  have hs' : spL.getD c.val false = true := hs
  have hne : (c.val == 417) = false := by
    cases h : c.val == 417
    · rfl
    · exfalso; apply he; apply Fin.ext; have := beq_iff_eq.mp h; exact this
  rw [hs', hne] at this
  simpa using this

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
    | some e => exact ⟨e, by simp [h]⟩
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

/-! ## The circuit induction for repeated invocations -/

theorem ne_eEnd_in {i : Fin NC} {o : Fin NO} (hi : i ∈ (opAt o).insC)
    (hk : ∀ j, opAt o ≠ .sink j) : i ≠ eEnd := by
  intro e; subst e
  have := cons_in o eEnd hi
  exact hk eEnd (by rw [← this]; rfl)

theorem ne_eEnd_out {c : Fin NC} {o : Fin NO} (hc : c ∈ (opAt o).outsC)
    (hk : ∀ i os, opAt o ≠ .forkG i os) : c ≠ eEnd := by
  intro e; subst e
  have := prod_out o eEnd hc
  exact hk zEnd [eEnd, 413] (by rw [← this]; rfl)

section
variable (a b : Nat) (ch : Fin NC → Chan) (y : TS)

/-- The circuit's offer counts on the spine (except the dead end `eEnd`) are the periodic
walk's visit counts after `p` steps. -/
def InvR (t : Nat) : Prop :=
  ∃ p, ∀ c, sp c = true → c ≠ eEnd → cnt (riseB (ch c).req) t = (walkR (σY a b y) p).W c

/-- **H_START_GATE** (environment): `start` is offered for the `(k+1)`-th time only after the
control token has left the last arbiter stage `k` times (`z251` offered `k` times). -/
def H_START_GATE : Prop :=
  ∀ t, riseB (ch start).req t = true → cnt (riseB (ch start).req) t ≤ cnt (riseB (ch zEnd).req) t

end

section mainR
variable {a b : Nat} {ch : Fin NC → Chan} {y : TS}
variable (hy : Good a b y)
variable (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
variable (H_BUNDLE : ∀ c, Held (ch c))
variable (H_GATE : H_START_GATE ch)
variable (H_WALKR : WalkOKR (σY a b y) (omOf a b y))

theorem am_ne {o : Fin NO} {x u z : Fin NC} {w : Nat} (ho : opAt o = .amerge x u z w) :
    x ≠ eEnd ∧ u ≠ eEnd ∧ z ≠ eEnd := by
  refine ⟨ne_eEnd_in (o := o) (by rw [ho]; simp [K.insC]) (by intro j; rw [ho]; simp),
    ne_eEnd_in (o := o) (by rw [ho]; simp [K.insC]) (by intro j; rw [ho]; simp),
    ne_eEnd_out (o := o) (by rw [ho]; simp [K.outsC]) (by intro i os; rw [ho]; simp)⟩

include H_WALKR in
theorem am_countsR {o : Fin NO} {x u z : Fin NC} {w : Nat} (ho : opAt o = .amerge x u z w) (p : Nat) :
    (walkR (σY a b y) p).W u = cnt (omOf a b y w) ((walkR (σY a b y) p).W z) +
        bn (((walkR (σY a b y) p).cur == z) && omOf a b y w ((walkR (σY a b y) p).W z)) ∧
      (walkR (σY a b y) p).W x = cnt (fun i => !omOf a b y w i) ((walkR (σY a b y) p).W z) +
        bn (((walkR (σY a b y) p).cur == z) && !omOf a b y w ((walkR (σY a b y) p).W z)) := by
  have hs := spok o
  rw [ho] at hs
  simp only [SpOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  have hd := ops_ok o
  rw [ho] at hd
  have hzo : prodOf z = o := prod_out o z (by rw [ho]; simp [K.outsC])
  have hxo : consOf x = o := cons_in o x (by rw [ho]; simp [K.insC])
  have huo : consOf u = o := cons_in o u (by rw [ho]; simp [K.insC])
  have hzs : z ≠ start := ne_start (by intro z' w' d'; rw [hzo, ho]; simp)
  have hze := (am_ne ho).2.2
  apply am_sideR (σY a b y) (omOf a b y w) hs.2 (Ne.symm hd.2.1) (Ne.symm hd.2.2) hzs
  · intro d k hsd _
    constructor
    · intro h
      have := nxt_in _ (nxtR_of _ h hzs).1
      rw [hzo, ho] at this; simpa [K.insC] using this
    · intro h
      rcases h with h | h <;> subst h
      · exact nxtR_eq _ (nxt_amerge _ (by rw [hxo, ho])) hze
      · exact nxtR_eq _ (nxt_amerge _ (by rw [huo, ho])) hze
  · intro p hd'
    rcases hd' with e | e
    · have := H_WALKR p x u z w (by rw [e, hxo, ho]); rw [this]
    · have := H_WALKR p x u z w (by rw [e, huo, ho]); rw [this]

include H_CELLS H_BUNDLE H_WALKR in
theorem forc_atR (t : Nat) (hinv : InvR a b ch y t) (hf : ForcB a b ch y t) : ForcB a b ch y (t + 1) := by
  intro o x u z w ho k r hr hoff
  rcases Nat.lt_or_ge r t with hlt | hge
  · exact hf o x u z w ho k r hlt hoff
  have hrt : r = t := by omega
  subst hrt
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  obtain ⟨p, hp'⟩ := hinv
  have hs := spok o
  rw [ho] at hs
  simp only [SpOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  obtain ⟨hxe, hue, hze⟩ := am_ne ho
  have hc := H_CELLS o
  rw [ho] at hc
  obtain ⟨g1, g2, M⟩ := hc
  obtain ⟨py, px⟩ := offer_pending M (hp x) (hp u) (hp z) hoff
  have hk : cnt (riseB (ch z).req) r = k := hoff.2
  have hpre : ∀ i, i < k → CM.winner (ch z) i = omOf a b y w i := by
    intro i hi
    obtain ⟨r', hr'⟩ := Capstone.offered_below hoff hi
    exact hf o x u z w ho i r' (off_before hoff hr' hi) hr'
  have c1 : cnt (CM.winner (ch z)) k = cnt (omOf a b y w) k := CM.cnt_congr_lt k hpre
  have c0 : cnt (fun i => !CM.winner (ch z) i) k = cnt (fun i => !omOf a b y w i) k :=
    CM.cnt_congr_lt k (fun i hi => by rw [hpre i hi])
  obtain ⟨ey, ex⟩ := am_countsR H_WALKR ho p
  have hzk : (walkR (σY a b y) p).W z = k := by rw [← hp' z hs.1.2 hze, hk]
  rw [hzk] at ey ex
  rw [← hp' u hs.1.1.2 hue] at ey
  rw [← hp' x hs.1.1.1 hxe] at ex
  cases hwk : CM.winner (ch z) k
  · have := px hwk; rw [c0] at this
    cases hω : omOf a b y w k
    · rfl
    · rw [hω] at ex; simp [bn] at ex; omega
  · have := py hwk; rw [c1] at this
    cases hω : omOf a b y w k
    · rw [hω] at ey; simp [bn] at ey; omega
    · rfl

include H_CELLS H_BUNDLE H_GATE H_WALKR in
/-- A spine channel other than `eEnd` can rise at `t` only if it is the periodic walk's next
channel. -/
theorem rise_curR (t p : Nat)
    (hinv : ∀ c, sp c = true → c ≠ eEnd → cnt (riseB (ch c).req) t = (walkR (σY a b y) p).W c)
    (hag : Agree ch (σY a b y) t) (hf : ForcB a b ch y (t + 1))
    (c : Fin NC) (hsc : sp c = true) (hce : c ≠ eEnd) (hr : riseB (ch c).req t = true) :
    (walkR (σY a b y) p).cur = c := by
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  have hct : cnt (riseB (ch c).req) (t + 1) = (walkR (σY a b y) p).W c + 1 := by
    rw [cnt_succ_of hr, hinv c hsc hce]
  let o := prodOf c
  have hco : c ∈ (opAt o).outsC := prod_mem c
  have hs := spok o
  have hc := H_CELLS o
  have hnes : ∀ (K' : K NC), opAt o = K' → (∀ z w d, K' ≠ .src z w d) → c ≠ start := by
    intro K' hK hK'; apply ne_start; intro z w d e; exact hK' z w d (hK ▸ e)
  cases hk : opAt o with
  | forkG i os =>
    rw [hk] at hco hs hc
    simp only [K.outsC] at hco
    have hsi : sp i = true := by
      cases hsi : sp i
      · simp only [SpOK, hsi, Bool.false_eq_true, ite_false, List.all_eq_true] at hs
        have := hs c hco; simp [hsc] at this
      · rfl
    simp only [SpOK, hsi, ite_true, beq_iff_eq] at hs
    have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
    have hie : i ≠ eEnd := ne_eEnd_in (o := o) (by rw [hk]; simp [K.insC]) (by intro j; rw [hk]; simp)
    have hb := fork_strict hc (hp i) (fun o' ho' => by
      obtain ⟨c', _, e⟩ := List.mem_map.mp ho'; rw [← e]; exact hp c') (List.mem_map_of_mem hco) hr
    rw [hct, hinv i hsi hie] at hb
    have hcs := hnes _ hk (by intros; simp)
    have hin := hin_oneR (σY a b y) (c := c) (i := i) hcs hce
      (by intro d _ hd; rw [show prodOf c = o from rfl, hk] at hd; simpa [K.insC] using hd)
      (fun k => by rw [nxt_forkG _ (by rw [hio, hk])]; exact find_one hs hco hsc)
    apply cur_of_boundR _ hcs
    rw [in_cpR _ hin]; exact hb
  | link i o' =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    simp only [SpOK, beq_iff_eq] at hs
    have hsi : sp i = true := by rw [hs]; exact hsc
    have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
    have hie : i ≠ eEnd := ne_eEnd_in (o := o) (by rw [hk]; simp [K.insC]) (by intro j; rw [hk]; simp)
    obtain ⟨cc, L⟩ := hc
    have hb := link_strict L (hp i) (hp c) hr
    rw [hct, hinv i hsi hie] at hb
    have hcs := hnes _ hk (by intros; simp)
    have hin := hin_oneR (σY a b y) (c := c) (i := i) hcs hce
      (by intro d _ hd; rw [show prodOf c = o from rfl, hk] at hd; simpa [K.insC] using hd)
      (fun k => nxt_link _ (by rw [hio, hk]) hsc)
    apply cur_of_boundR _ hcs
    rw [in_cpR _ hin]; exact hb
  | bjoin ins o' ec ed =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    simp only [SpOK, hsc, Bool.not_true, Bool.false_or] at hs
    match ins, hs, hc, hk with
    | [cd, i], hs, hc, hk =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
      have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
      have hie : i ≠ eEnd := ne_eEnd_in (o := o) (by rw [hk]; simp [K.insC]) (by intro j; rw [hk]; simp)
      have hb := join_strict hc (hp c) (fun i' hi' => by
        obtain ⟨c', _, e⟩ := List.mem_map.mp hi'; rw [← e]; exact hp c') (i := ch i) (by simp) hr
      rw [hct, hinv i hs.2 hie] at hb
      have hcs := hnes _ hk (by intros; simp)
      have hin := hin_oneR (σY a b y) (c := c) (i := i) hcs hce
        (by
          intro d hd hd'
          rw [show prodOf c = o from rfl, hk] at hd'
          simp only [K.insC, List.mem_cons, List.not_mem_nil, or_false] at hd'
          rcases hd' with e | e
          · subst e; rw [hs.1] at hd; exact absurd hd (by decide)
          · exact e)
        (fun k => nxt_bjoin _ (by rw [hio, hk]) hsc)
      apply cur_of_boundR _ hcs
      rw [in_cpR _ hin]; exact hb
  | steerC j tt ff =>
    rw [hk] at hco hs hc
    simp only [SpOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
    obtain ⟨⟨htj, hfj⟩, htf⟩ := hs
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hco
    have hjo : consOf j = o := cons_in o j (by rw [hk]; simp [K.insC])
    have hje : j ≠ eEnd := ne_eEnd_in (o := o) (by rw [hk]; simp [K.insC]) (by intro j; rw [hk]; simp)
    have hsj : sp j = true := by
      rcases hco with e | e
      · rw [← htj, ← e]; exact hsc
      · rw [← hfj, ← e]; exact hsc
    have hst : sp tt = true := by rw [htj]; exact hsj
    obtain ⟨bb, hbb⟩ : ∃ bb : Bool, c = (bif bb then tt else ff) := by
      rcases hco with e | e
      · exact ⟨true, e⟩
      · exact ⟨false, e⟩
    have hb := steer_strict hc (hp j) (fun b' => hp _) (H_BUNDLE j) bb (by rw [← hbb]; exact hr)
    rw [← hbb, hct] at hb
    have hsel : selOff sel2 (ch j) bb t =
        cnt (fun i => sel2 (σY a b y j i) == bb) (cnt (riseB (ch j).req) t) :=
      cnt_offers (σ := σY a b y j) (fun v => sel2 v == bb)
        (fun i u hu ho => hag j i u hu ho) t (Nat.le_refl _)
    rw [hsel, hinv j hsj hje] at hb
    have hcs := hnes _ hk (by intros; simp)
    have hin : ∀ d k, sp d = true → d ≠ eEnd →
        (nxtR (σY a b y) d k = c ↔ d = j ∧ sel2 (σY a b y j k) = bb) := by
      intro d k hsd _
      constructor
      · intro h
        have h' := (nxtR_of _ h hcs).1
        have hd := nxt_in _ h'
        rw [show prodOf c = o from rfl, hk] at hd
        simp only [K.insC, List.mem_singleton] at hd
        subst hd
        rw [nxt_steerC _ (by rw [hjo, hk]) hst] at h'
        simp only [Option.some.injEq] at h'
        refine ⟨rfl, ?_⟩
        rw [hbb] at h'
        cases hb1 : sel2 (σY a b y d k) <;> cases bb <;> simp [hb1] at h' ⊢ <;>
          exact htf (by first | exact h' | exact h'.symm)
      · rintro ⟨e, hsl⟩
        subst e
        apply nxtR_eq _ _ hce
        rw [nxt_steerC _ (by rw [hjo, hk]) hst]
        simp [hsl, hbb]
    apply cur_of_boundR _ hcs
    rw [in_stR _ hin]; exact hb
  | amerge x u z w =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    obtain ⟨g1, g2, M⟩ := hc
    obtain ⟨hxe, hue, -⟩ := am_ne hk
    have hsx : sp x = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.1
    have hsu : sp u = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.2
    have hoff : OffAt (ch c) (walkR (σY a b y) p |>.W c) t := ⟨hr, hinv c hsc hce⟩
    have hw := hf o x u c w hk _ t (Nat.lt_succ_self _) hoff
    obtain ⟨py, px⟩ := offer_pending M (hp x) (hp u) (hp c) hoff
    have hpre : ∀ i, i < (walkR (σY a b y) p).W c → CM.winner (ch c) i = omOf a b y w i := by
      intro i hi
      obtain ⟨r', hr'⟩ := Capstone.offered_below hoff hi
      exact hf o x u c w hk i r' (by have := off_before hoff hr' hi; omega) hr'
    have c1 := CM.cnt_congr_lt _ hpre
    have c0 : cnt (fun i => !CM.winner (ch c) i) ((walkR (σY a b y) p).W c) =
        cnt (fun i => !omOf a b y w i) ((walkR (σY a b y) p).W c) :=
      CM.cnt_congr_lt _ (fun i hi => by rw [hpre i hi])
    obtain ⟨ey, ex⟩ := am_countsR H_WALKR hk p
    rw [← hinv u hsu hue] at ey
    rw [← hinv x hsx hxe] at ex
    cases hω : omOf a b y w ((walkR (σY a b y) p).W c)
    · have := px (by rw [hw, hω]); rw [c0] at this
      rw [hω] at ex
      cases hq : ((walkR (σY a b y) p).cur == c)
      · rw [hq] at ex; simp [bn] at ex; omega
      · simpa using hq
    · have := py (by rw [hw, hω]); rw [c1] at this
      rw [hω] at ey
      cases hq : ((walkR (σY a b y) p).cur == c)
      · rw [hq] at ey; simp [bn] at ey; omega
      · simpa using hq
  | src z which d =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    have hcs : c = start := by
      by_cases hw2 : which = 2
      · subst hw2; simpa [SpOK, hsc] using hs
      · simp [SpOK, hsc, hw2] at hs
    subst hcs
    have hg := H_GATE t hr
    rw [hinv start hsc hce, hinv zEnd zEnd_sp (Ne.symm eEnd_ne_zEnd)] at hg
    have hf' := flowR (σY a b y) p start
    rw [tr_startR] at hf'
    cases hq : ((walkR (σY a b y) p).cur == start)
    · rw [hq] at hf'; simp [bn] at hf'; omega
    · simpa using hq
  | forkH i os l h d hs' =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_map] at hco
    obtain ⟨pr, hpr, e⟩ := hco
    simp only [SpOK, List.all_eq_true] at hs
    have := hs pr hpr; rw [e] at this; simp [hsc] at this
  | join ins o' e js jw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | steerD j tt ff fd sw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hco
    simp only [SpOK, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rcases hco with e | e <;> subst e
    · rw [hs.1] at hsc; exact absurd hsc (by decide)
    · rw [hs.2] at hsc; exact absurd hsc (by decide)
  | mux cc xx yy zz mw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | muxn cc x0 x1 x2 zz nw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | sink i =>
    rw [hk] at hco
    simp [K.outsC] at hco

include hy H_CELLS H_BUNDLE H_GATE H_WALKR in
/-- **The joint induction on time, for repeated invocations.** -/
theorem mainR : ∀ t, InvR a b ch y t ∧ ForcB a b ch y t ∧ Agree ch (σY a b y) t := by
  intro t
  induction t with
  | zero =>
    refine ⟨⟨0, fun c _ _ => rfl⟩, fun _ _ _ _ _ _ _ _ h _ => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h _ => absurd h (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨hinv, hf, hag⟩ := ih
    have hf' := forc_atR H_CELLS H_BUNDLE H_WALKR t hinv hf
    have hag' := agr_at hy H_CELLS H_BUNDLE t hag hf'
    refine ⟨?_, hf', hag'⟩
    obtain ⟨p, hp⟩ := hinv
    have hrc := rise_curR H_CELLS H_BUNDLE H_GATE H_WALKR t p hp hag hf'
    by_cases hex : ∃ c, sp c = true ∧ c ≠ eEnd ∧ riseB (ch c).req t = true
    · obtain ⟨c, hsc, hce, hr⟩ := hex
      have hcur := hrc c hsc hce hr
      refine ⟨p + 1, fun d hsd hde => ?_⟩
      rw [W_succR, cnt_succ', hp d hsd hde, hcur]
      by_cases hdc : d = c
      · subst hdc; simp [hr, bn]
      · have h1 : riseB (ch d).req t = false := by
          cases h : riseB (ch d).req t
          · rfl
          · have := hrc d hsd hde h; rw [hcur] at this; exact absurd this.symm hdc
        have h2 : (c == d) = false := by simp [Ne.symm hdc]
        rw [h1, h2]
    · refine ⟨p, fun d hsd hde => ?_⟩
      rw [cnt_succ', hp d hsd hde]
      have : riseB (ch d).req t = false := by
        cases h : riseB (ch d).req t
        · rfl
        · exact absurd ⟨d, hsd, hde, h⟩ hex
      rw [this]; rfl

end mainR

/-- **H_CM_FORCED for repeated invocations**: under H_CELLS, H_BUNDLE, H_START_GATE and the
periodic walk condition, every arbiter stage's winner of every offered token (in every
invocation) is the token run's label. -/
theorem gcd_hw_forcedR (a b : Nat) (ch : Fin NC → Chan) (y : TS) (hy : Good a b y)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_GATE : H_START_GATE ch)
    (H_WALKR : WalkOKR (σY a b y) (omOf a b y)) :
    ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o) := by
  intro o
  cases hk : opAt o with
  | amerge x u z w =>
    intro k r hoff
    exact (mainR hy H_CELLS H_BUNDLE H_GATE H_WALKR (r + 1)).2.1 o x u z w hk k r
      (Nat.lt_succ_self _) hoff
  | _ => trivial

/-- **Circuit safety for repeated invocations, given the periodic walk condition.** -/
theorem gcd_hw_circuit_safeR (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_GATE : H_START_GATE ch)
    (H_WALKR : ∃ y, Good a b y ∧ WalkOKR (σY a b y) (omOf a b y)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  obtain ⟨y, hy, hw⟩ := H_WALKR
  exact gcd_hw_circuit_safe a b ch H_CELLS H_BUNDLE
    ⟨y, hy, gcd_hw_forcedR a b ch y hy H_CELLS H_BUNDLE H_GATE hw⟩

end Formal.Net.CapNet.Gcd
