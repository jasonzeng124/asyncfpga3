import Formal.Cells.ZeroDelayRefine

/-!
# ZeroDelayNet: the network half of the physical ↦ zero-delay refinement (link chain)

Probe Bzd2 (shard B); note `formal/notes/B-zero-delay-net.md`. Builds on
`ZeroDelayRefine` (probe Bzd: the cell half, one token per cell, each cell with its own
retiming). C's definitions (`Handshake.Chan`, `Protocol`, `Ops.Held`, `Ops.Link.Link`) are
imported, never restated.

## What this file proves (abstract / parameter level)

* **One retiming for the whole chain** (`key`, `kS`): every physical event window `[lo, hi]`
  gets the abstract step `key T D lo d = (lo - T).toNat * D + d`, where `d < D` is the event's
  causal depth in the ideal four-phase order. Such a step function is AUTOMATICALLY monotone
  (`net_mono`: if `e.hi < e'.lo` then `e.lo < e'.lo`, so `e` gets the earlier step). The work is
  in C's gate fields, which need every cause to get a strictly earlier step than its effect.
* `chain_link` / `chain_proto` / `chain_held` (any schedule `S` meeting the order list
  `SchOK`): the abstract chain run `chA` (channels `0..N`, shared between neighbouring stages:
  channel `i+1` is stage `i`'s output AND stage `i+1`'s input) satisfies C's `Link` for every
  stage, `Protocol` and `Held` on every channel.
* `kS_ok`: the key schedule meets `SchOK` whenever the windows are **lo-causal** (`LoOrd`:
  each effect's window starts no earlier than its cause's).
* **H_CAUSAL from the closed loop** (`chain_loOrd`, `chain_causal`): in a chain whose
  inter-stage wires are exactly the neighbour's node windows read through nonnegative delays
  (`ChainPar.loop_a/loop_b`, `Wf.hA/hB`), `LoOrd` holds and Bzd's `Causal` holds for EVERY
  stage, given only the end environments' own causality (`H_SRC`, `H_SNK`: a source and a sink
  that answer through nonnegative delays).
* `stage_mono`: restricted to stage `i`'s own six events (Bzd's `linkEvs` windows, read off
  its own `Par`), the one global retiming is a monotone retiming of that stage; the shared
  wire gets ONE step (both stages read the same abstract `Chan`).
* Necessity of the causality hypothesis: `causal_iff_mono` (for Bzd's per-cell retiming,
  `Causal` is exactly its `Mono`); `negdelay_breaks_causal` (a two-stage loop with a negative
  read delay downstream violates `Causal` upstream).

The physical (trace-level) half, where every stage is a real `LinkExact` behaviour in the closed
loop, is `ZeroDelayNetPhys`; multi-token is `ZeroDelayNetTok`.

NOT covered here: fork/join, steer→mux diamond (only the general principle `net_mono` +
"order list" applies; their order lists are not written); rings (initial tokens).
Core Lean only.
-/

namespace Formal.Cells.ZeroDelayNet
open Formal.Cells
open Formal.Cells.LinkExact
open Formal.Cells.ZeroDelayRefine
open Formal.Net (Trace)
open Formal.Net.Handshake (Chan Protocol SendStep RecvStep)
open Formal.Net.Ops (Held inTx)
open Formal.Cells.LinkHandshake (ctlB ctlB_eq)

/-! ## 0. `tokA` facts -/

theorem tA_t {a b n : Nat} (h1 : a < n) (h2 : n ≤ b) : tokA a b n = true := by
  simp [tokA]; omega
theorem tA_f1 {a b n : Nat} (h : n ≤ a) : tokA a b n = false := by
  simp [tokA]; omega
theorem tA_f2 {a b n : Nat} (h : b < n) : tokA a b n = false := by
  simp [tokA]; omega
theorem tA_succ (a b n : Nat) : tokA (a + 1) (b + 1) (n + 1) = tokA a b n := by
  by_cases h : a < n ∧ n ≤ b
  · rw [tA_t (by omega) (by omega), tA_t h.1 h.2]
  · by_cases h' : n ≤ a
    · rw [tA_f1 (by omega), tA_f1 h']
    · rw [tA_f2 (by omega), tA_f2 (by omega)]
theorem tA_move {a b t : Nat} (h : tokA a b (t + 1) ≠ tokA a b t) : t = a ∨ t = b := by
  refine Classical.byContradiction fun hc => ?_
  apply h
  by_cases h1 : a < t ∧ t ≤ b
  · rw [tA_t h1.1 h1.2, tA_t (by omega) (by omega)]
  · by_cases h2 : t < a
    · rw [tA_f1 (by omega), tA_f1 (by omega)]
    · rw [tA_f2 (by omega), tA_f2 (by omega)]

/-- C's four-phase protocol for a one-token channel whose four edges are ordered. -/
theorem proto_tok {a b c d : Nat} (h1 : a < b) (h2 : b < c) (h3 : c < d) (dat : Nat → Nat) :
    Protocol ⟨tokA a c, tokA b d, dat⟩ := by
  refine ⟨⟨tA_f1 (Nat.zero_le _), tA_f1 (Nat.zero_le _)⟩, fun t => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · rcases tA_move hm with rfl | rfl
    · show tokA t c t = tokA b d t
      rw [tA_f1 (Nat.le_refl _), tA_f1 (by omega)]
    · show tokA a t t = tokA b d t
      rw [tA_t (by omega) (Nat.le_refl _), tA_t (by omega) (by omega)]
  · rcases tA_move hm with rfl | rfl
    · show tokA t d t ≠ tokA a c t
      rw [tA_f1 (Nat.le_refl _), tA_t (by omega) (by omega)]; decide
    · show tokA b t t ≠ tokA a c t
      rw [tA_t (by omega) (Nat.le_refl _), tA_f2 (by omega)]; decide

/-- `Held` for a one-token channel whose bus moves only across step `s ≤ a` (idle there). -/
theorem held_tok {a b c d s : Nat} (hs : s ≤ a) (hab : a ≤ b) (dat : Nat → Nat)
    (hd : ∀ t, t ≠ s → dat (t + 1) = dat t) : Held ⟨tokA a c, tokA b d, dat⟩ := by
  intro t h0 _
  by_cases ht : t = s
  · exfalso; subst ht
    simp only [inTx] at h0
    rw [tA_f1 hs, tA_f1 (by omega)] at h0; exact Bool.false_ne_true h0
  · exact hd t ht

/-! ## 1. The abstract chain run, for any schedule -/

/-- A schedule of one token through an `N`-stage link chain: source request rise/fall `sr/sf`,
sink acknowledge rise/fall `ku/kd`, node `i` rise/fall `cu i / cd i`. The inter-stage wires
(`(ch (i+1)).req`, `(ch i).ack`) are DI copies of node `i`, one step later. -/
structure Sch where
  sr : Nat
  sf : Nat
  ku : Nat
  kd : Nat
  cu : Nat → Nat
  cd : Nat → Nat

namespace Sch
variable (S : Sch) (N : Nat)
def rq (j : Nat) : Nat := if j = 0 then S.sr else S.cu (j - 1) + 1
def rqf (j : Nat) : Nat := if j = 0 then S.sf else S.cd (j - 1) + 1
def ak (j : Nat) : Nat := if j = N then S.ku else S.cu j + 1
def akf (j : Nat) : Nat := if j = N then S.kd else S.cd j + 1
end Sch

/-- Abstract channel `j` (`0 ≤ j ≤ N`): channel 0 is the source's, channel `N` the sink's.
Bus: the token value `V`; channel `j ≥ 1` carries the old latch content `u j` until node `j-1`
opens. -/
def chA (S : Sch) (N V : Nat) (u : Nat → Nat) (j : Nat) : Chan :=
  ⟨tokA (S.rq j) (S.rqf j), tokA (S.ak N j) (S.akf N j),
   fun n => if j = 0 then V else if n ≤ S.cu (j - 1) then u j else V⟩

/-- Abstract node `i`. -/
def ndA (S : Sch) (i : Nat) : Trace := tokA (S.cu i) (S.cd i)

/-- **The order list** a schedule must meet (each item a cause strictly before its effect, or
an effect not before its cause). -/
structure SchOK (S : Sch) (N : Nat) : Prop where
  o1 : ∀ i < N, S.rq i < S.cu i
  o2 : ∀ i < N, S.cu i ≤ S.rqf i
  o3 : ∀ i < N, S.cu i ≤ S.ak N (i + 1)
  o4 : ∀ i < N, S.rqf i < S.cd i
  o5 : ∀ i < N, S.ak N (i + 1) < S.cd i
  o6 : ∀ i < N, S.cd i ≤ S.akf N (i + 1)
  o7 : ∀ i < N, S.cu i < S.cd i
  pr : ∀ j ≤ N, S.rq j < S.ak N j ∧ S.ak N j < S.rqf j ∧ S.rqf j < S.akf N j

theorem ak_lt {S : Sch} {N i : Nat} (h : i < N) : S.ak N i = S.cu i + 1 := by
  simp [Sch.ak, Nat.ne_of_lt h]
theorem akf_lt {S : Sch} {N i : Nat} (h : i < N) : S.akf N i = S.cd i + 1 := by
  simp [Sch.akf, Nat.ne_of_lt h]
theorem rq_succ (S : Sch) (i : Nat) : S.rq (i + 1) = S.cu i + 1 := by simp [Sch.rq]
theorem rqf_succ (S : Sch) (i : Nat) : S.rqf (i + 1) = S.cd i + 1 := by simp [Sch.rqf]

open Formal.Net.Ops.Link (Link) in
/-- **Every stage of the abstract chain satisfies C's `Link`** (on the SHARED channels). -/
theorem chain_link {S : Sch} {N : Nat} (H : SchOK S N) (V : Nat) (u : Nat → Nat) :
    ∀ i < N, Link (chA S N V u i) (chA S N V u (i + 1)) (ndA S i) := by
  intro i hi
  have o1 := H.o1 i hi; have o2 := H.o2 i hi; have o3 := H.o3 i hi; have o4 := H.o4 i hi
  have o5 := H.o5 i hi; have o6 := H.o6 i hi; have o7 := H.o7 i hi
  refine ⟨fun t hm => ?_, fun t _ => ?_, fun t _ => ?_, fun t ht => ?_, fun t ht => ?_,
    tA_f1 (Nat.zero_le _), tA_f1 (Nat.zero_le _), tA_f1 (Nat.zero_le _)⟩
  · simp only [ndA] at hm ⊢
    simp only [chA]
    rcases tA_move hm with h | h <;> subst h
    · rw [tA_t (a := S.cu i) (b := S.cd i) (n := S.cu i + 1) (by omega) (by omega),
        tA_f1 (a := S.cu i) (b := S.cd i) (n := S.cu i) (Nat.le_refl _), tA_t o1 o2, tA_f1 o3,
        ctlB_eq]
      rfl
    · rw [tA_f2 (a := S.cu i) (b := S.cd i) (n := S.cd i + 1) (Nat.lt_succ_self _),
        tA_t (a := S.cu i) (b := S.cd i) (n := S.cd i) o7 (Nat.le_refl _), tA_f2 o4, tA_t o5 o6,
        ctlB_eq]
      rfl
  · show tokA (S.ak N i) (S.akf N i) (t + 1) = tokA (S.cu i) (S.cd i) t
    rw [ak_lt hi, akf_lt hi, tA_succ]
  · show tokA (S.rq (i + 1)) (S.rqf (i + 1)) (t + 1) = tokA (S.cu i) (S.cd i) t
    rw [rq_succ, rqf_succ, tA_succ]
  · simp only [ndA, tokA, decide_eq_true_eq] at ht
    simp only [chA, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [if_neg (by omega)]
    rcases i with _ | j
    · simp
    · have := H.o1 (j + 1) hi
      rw [rq_succ] at this
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [if_neg (by omega)]
  · simp only [chA, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h1 : t = S.cu i
    · subst h1; exfalso
      simp only [ndA] at ht
      rw [tA_t (by omega) (by omega)] at ht; exact Bool.noConfusion ht
    · by_cases h2 : t + 1 ≤ S.cu i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- **C's `Protocol` on every channel of the abstract chain.** -/
theorem chain_proto {S : Sch} {N : Nat} (H : SchOK S N) (V : Nat) (u : Nat → Nat) :
    ∀ j ≤ N, Protocol (chA S N V u j) := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := H.pr j hj
  exact proto_tok p1 p2 p3 _

/-- **C's `Held` (H_BUNDLE) on every channel of the abstract chain.** -/
theorem chain_held {S : Sch} {N : Nat} (H : SchOK S N) (V : Nat) (u : Nat → Nat) :
    ∀ j ≤ N, Held (chA S N V u j) := by
  intro j hj
  obtain ⟨p1, -, -⟩ := H.pr j hj
  rcases j with _ | k
  · exact fun _ _ _ => rfl
  · refine held_tok (s := S.cu k) (by rw [rq_succ]; omega) (by omega) _ fun t ht => ?_
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h2 : t + 1 ≤ S.cu k
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- The abstract latch of stage `i` holds the token from its opening on. -/
theorem chain_latched (S : Sch) (N V : Nat) (u : Nat → Nat) (i n : Nat) (h : S.cu i < n) :
    (chA S N V u (i + 1)).dat n = V := by
  simp only [chA, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  rw [if_neg (by omega)]

/-! ## 2. The key retiming -/

/-- Abstract step of an event whose window starts at `lo`, with causal depth `d` (`d < D`). -/
def key (T : Int) (D : Nat) (x : Int) (d : Nat) : Nat := (x - T).toNat * D + d

theorem key_le {T x y : Int} {D d d' : Nat} (h : x ≤ y) (hd : d ≤ d') : key T D x d ≤ key T D y d' := by
  unfold key
  have : (x - T).toNat ≤ (y - T).toNat := by omega
  have := Nat.mul_le_mul_right D this
  omega
theorem key_lt {T x y : Int} {D d d' : Nat} (h : x ≤ y) (hd : d < d') : key T D x d < key T D y d' := by
  unfold key
  have : (x - T).toNat ≤ (y - T).toNat := by omega
  have := Nat.mul_le_mul_right D this
  omega
theorem key_succ (T : Int) (D : Nat) (x : Int) (d : Nat) : key T D x (d + 1) = key T D x d + 1 := by
  unfold key; omega
theorem key_mono {T x y : Int} {D d d' : Nat} (hT : T ≤ x) (h : x < y) (hd : d < D) :
    key T D x d < key T D y d' := by
  unfold key
  have : (x - T).toNat + 1 ≤ (y - T).toNat := by omega
  have := Nat.mul_le_mul_right D this
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The key schedule of an `N`-stage chain with per-stage parameters `P i`. Base `T` = the
source's request window start; depths: source rise 0, node `i` rise `2i+2` (its wire copies
`2i+3`), sink rise `2N+2`, source fall `2N+4`, node `i` fall `2N+6+2i` (copies `+1`), sink fall
`4N+6`; `D = 4N+8`. -/
def kS (N : Nat) (P : Nat → Par) : Sch :=
  { sr := key (P 0).Ra (4 * N + 8) (P 0).Ra 0
    sf := key (P 0).Ra (4 * N + 8) (P 0).Fa (2 * N + 4)
    ku := key (P 0).Ra (4 * N + 8) (P (N - 1)).Rb (2 * N + 2)
    kd := key (P 0).Ra (4 * N + 8) (P (N - 1)).Fb (4 * N + 6)
    cu := fun i => key (P 0).Ra (4 * N + 8) (P i).U0 (2 * i + 2)
    cd := fun i => key (P 0).Ra (4 * N + 8) (P i).V0 (2 * N + 6 + 2 * i) }

/-- **Lo-causality**: each effect's window starts no earlier than each of its causes'
(source rise → node 0 rise → … → node `N-1` rise → sink rise; node `i+1` rise → node `i` fall;
node `i` fall → node `i+1` fall; source fall after node 0 rise; sink fall after node `N-1` fall). -/
structure LoOrd (N : Nat) (P : Nat → Par) : Prop where
  pos : 1 ≤ N
  l1 : (P 0).Ra ≤ (P 0).U0
  l2 : (P 0).U0 ≤ (P 0).Fa
  l3 : (P 0).Fa ≤ (P 0).V0
  l4 : ∀ i, i + 1 < N → (P i).U0 ≤ (P (i + 1)).U0 ∧ (P (i + 1)).U0 ≤ (P i).V0 ∧
    (P i).V0 ≤ (P (i + 1)).V0
  l5 : (P (N - 1)).U0 ≤ (P (N - 1)).Rb ∧ (P (N - 1)).Rb ≤ (P (N - 1)).V0 ∧
    (P (N - 1)).V0 ≤ (P (N - 1)).Fb
  l6 : ∀ i < N, (P i).U0 ≤ (P i).V0

/-- **The key schedule meets the order list** whenever the windows are lo-causal. -/
theorem kS_ok {N : Nat} {P : Nat → Par} (L : LoOrd N P) : SchOK (kS N P) N := by
  have l1 := L.l1; have l2 := L.l2; have l3 := L.l3; have l5 := L.l5; have pos := L.pos
  have tl : ∀ i, i + 1 = N → i = N - 1 := fun i h => by omega
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun j hj => ?_⟩ <;>
    simp only [Sch.rq, Sch.rqf, Sch.ak, Sch.akf, kS]
  · rcases i with _ | j
    · exact key_lt l1 (by omega)
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * j + 2 + 1) (d' := 2 * (j + 1) + 2)
        (L.l4 j hi).1 (by omega)
      simp only [key_succ] at *; omega
  · rcases i with _ | j
    · exact key_le l2 (by omega)
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      have := key_le (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * (j + 1) + 2)
        (d' := 2 * N + 6 + 2 * j) (L.l4 j hi).2.1 (by omega)
      omega
  · by_cases e : i + 1 = N
    · rw [if_pos e, ← tl i e]; exact key_le (tl i e ▸ l5.1) (by omega)
    · rw [if_neg e]
      have := key_le (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * i + 2) (d' := 2 * (i + 1) + 2)
        (L.l4 i (by omega)).1 (by omega)
      omega
  · rcases i with _ | j
    · exact key_lt l3 (by omega)
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * N + 6 + 2 * j + 1)
        (d' := 2 * N + 6 + 2 * (j + 1)) (L.l4 j hi).2.2 (by omega)
      simp only [key_succ] at *; omega
  · by_cases e : i + 1 = N
    · rw [if_pos e, ← tl i e]; exact key_lt (tl i e ▸ l5.2.1) (by omega)
    · rw [if_neg e]
      have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * (i + 1) + 2 + 1)
        (d' := 2 * N + 6 + 2 * i) (L.l4 i (by omega)).2.1 (by omega)
      simp only [key_succ] at *; omega
  · by_cases e : i + 1 = N
    · rw [if_pos e, ← tl i e]; exact key_le (tl i e ▸ l5.2.2) (by omega)
    · rw [if_neg e]
      have := key_le (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * N + 6 + 2 * i)
        (d' := 2 * N + 6 + 2 * (i + 1)) (L.l4 i (by omega)).2.2 (by omega)
      omega
  · exact key_lt (L.l6 i hi) (by omega)
  · rcases j with _ | k
    · have e : (0 = N) = False := by simp; omega
      simp only [e, if_true, if_false]
      refine ⟨?_, ?_, ?_⟩
      · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 0) (d' := 2 * 0 + 2 + 1) l1 (by omega)
        simp only [key_succ] at *; omega
      · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * 0 + 2 + 1) (d' := 2 * N + 4) l2
          (by omega)
        simp only [key_succ] at *; omega
      · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * N + 4) (d' := 2 * N + 6 + 2 * 0 + 1)
          l3 (by omega)
        simp only [key_succ] at *; omega
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      by_cases e : k + 1 = N
      · rw [if_pos e, if_pos e]
        have hk : k = N - 1 := by omega
        rw [← hk]
        rw [← hk] at l5
        refine ⟨?_, ?_, ?_⟩
        · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * k + 2 + 1) (d' := 2 * N + 2)
            l5.1 (by omega)
          simp only [key_succ] at *; omega
        · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * N + 2)
            (d' := 2 * N + 6 + 2 * k + 1) l5.2.1 (by omega)
          simp only [key_succ] at *; omega
        · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * N + 6 + 2 * k + 1)
            (d' := 4 * N + 6) l5.2.2 (by omega)
          simp only [key_succ] at *; omega
      · rw [if_neg e, if_neg e]
        have h4 := L.l4 k (by omega)
        refine ⟨?_, ?_, ?_⟩
        · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * k + 2 + 1)
            (d' := 2 * (k + 1) + 2 + 1) h4.1 (by omega)
          simp only [key_succ] at *; omega
        · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * (k + 1) + 2 + 1)
            (d' := 2 * N + 6 + 2 * k + 1) h4.2.1 (by omega)
          simp only [key_succ] at *; omega
        · have := key_lt (T := (P 0).Ra) (D := 4 * N + 8) (d := 2 * N + 6 + 2 * k + 1)
            (d' := 2 * N + 6 + 2 * (k + 1) + 1) h4.2.2 (by omega)
          simp only [key_succ] at *; omega

/-! ## 3. The closed loop (parameter level): lo-causality and `Causal` from nonnegative delays -/

/-- **The closed-loop chain, parameter level.** `N ≥ 1` stages, each `Wf` (nonnegative read
windows `Alo, Blo ≥ 0`: the wire delay is folded into the reading pin's window, as `bd_link`'s
`req_out` and `ack_in` ARE the node, `DELAY = DACK = 0`). **H_LOOP**: stage `i+1`'s request
pin's driver windows are stage `i`'s node windows (`loop_a`), stage `i`'s acknowledge pin's
driver windows are stage `i+1`'s node windows (`loop_b`). **H_SRC**, **H_SNK**: the source
does not start to drop its request before stage 0 could start to acknowledge, and the sink
neither starts to acknowledge before stage `N-1` could request nor starts to release before
it could release (any source/sink that reads those wires through a nonnegative delay). -/
structure ChainPar (N : Nat) (P : Nat → Par) : Prop where
  pos : 1 ≤ N
  wf : ∀ i < N, Wf (P i)
  loop_a : ∀ i, i + 1 < N → (P (i + 1)).Ra = (P i).U0 ∧ (P (i + 1)).Ra1 = (P i).U1 ∧
    (P (i + 1)).Fa = (P i).V0 ∧ (P (i + 1)).Fa1 = (P i).V1
  loop_b : ∀ i, i + 1 < N → (P i).Rb = (P (i + 1)).U0 ∧ (P i).Rb1 = (P (i + 1)).U1 ∧
    (P i).Fb = (P (i + 1)).V0 ∧ (P i).Fb1 = (P (i + 1)).V1
  H_SRC : (P 0).U0 ≤ (P 0).Fa
  H_SNK : (P (N - 1)).U0 ≤ (P (N - 1)).Rb ∧ (P (N - 1)).V0 ≤ (P (N - 1)).Fb

/-- **The closed loop is lo-causal.** -/
theorem chain_loOrd {N : Nat} {P : Nat → Par} (C : ChainPar N P) : LoOrd N P := by
  have pos := C.pos
  have w0 := C.wf 0 (by omega)
  have a0 := w0.hA; have h0 := w0.ha
  refine ⟨pos, ?_, C.H_SRC, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · simp only [Par.U0]; omega
  · simp only [Par.V0]; omega
  · have wi := C.wf i (by omega); have wj := C.wf (i + 1) hi
    have la := C.loop_a i hi; have lb := C.loop_b i hi
    have := wi.hA; have := wi.hB; have := wj.hA; have := wj.hB
    simp only [Par.U0, Par.V0] at *
    omega
  · have w := C.wf (N - 1) (by omega)
    have := w.hB; have := C.H_SNK
    simp only [Par.V0] at *
    omega
  · have w := C.wf i hi; have := w.ha
    simp only [Par.U0, Par.V0]; omega

/-- **H_CAUSAL from the closed loop (goal 1).** Every stage of a closed-loop chain with
nonnegative read delays meets Bzd's environment causality `Causal`. -/
theorem chain_causal {N : Nat} {P : Nat → Par} (C : ChainPar N P) : ∀ i < N, Causal (P i) := by
  intro i hi
  have w := C.wf i hi; have := w.ha; have := w.hb; have := w.hA; have := w.hB
  have sn := C.H_SNK; have sr := C.H_SRC
  refine ⟨?_, ?_, ?_⟩
  · by_cases e : i + 1 < N
    · have lb := C.loop_b i e; have la := C.loop_a i e; have wj := (C.wf (i + 1) e).hA
      simp only [Par.U0] at *; omega
    · have hi' : i = N - 1 := by omega
      subst hi'; omega
  · rcases i with _ | j
    · omega
    · have la := C.loop_a j hi; have lb := C.loop_b j hi; have wj := (C.wf j (by omega)).hB
      simp only [Par.U0, Par.V0] at *; omega
  · by_cases e : i + 1 < N
    · have lb := C.loop_b i e; have la := C.loop_a i e; have wj := (C.wf (i + 1) e).hA
      simp only [Par.V0] at *; omega
    · have hi' : i = N - 1 := by omega
      subst hi'; omega

/-- **`Causal` is exactly the monotonicity of Bzd's per-cell retiming** (so it cannot be
dropped from `link_refines` without changing the retiming). -/
theorem causal_iff_mono {P : Par} (S : Wf P) : Mono (linkEvs P (swOf P)) ↔ Causal P := by
  refine ⟨fun M => ⟨?_, ?_, ?_⟩, link_mono S⟩
  · refine Classical.byContradiction fun h => ?_
    have := M (⟨P.Rb, P.Rb1⟩, kB (swOf P)) (by simp [linkEvs]) (⟨P.U0, P.U1⟩, 1)
      (by simp [linkEvs]) (by simp only; omega)
    generalize swOf P = sw at this; cases sw <;> simp [kB] at this
  · refine Classical.byContradiction fun h => ?_
    have := M (⟨P.Fa, P.Fa1⟩, kA (swOf P)) (by simp [linkEvs]) (⟨P.U0, P.U1⟩, 1)
      (by simp [linkEvs]) (by simp only; omega)
    generalize swOf P = sw at this; cases sw <;> simp [kA] at this
  · refine Classical.byContradiction fun h => ?_
    have := M (⟨P.Fb, P.Fb1⟩, 7) (by simp [linkEvs]) (⟨P.V0, P.V1⟩, 5)
      (by simp [linkEvs]) (by simp only; omega)
    omega

/-- Upstream stage of the negative-delay counter-loop (LinkExact's `P0` numbers, a slow
acknowledge pin `[900, 1000]`, and the acknowledge windows the loop dictates). -/
def Pn0 : Par :=
  { W := 2000, W1 := 2001, Ra := 3000, Ra1 := 3001, Fa := 4500, Fa1 := 4501,
    Rb := 3100, Rb1 := 3221, Fb := 6380, Fb1 := 6501, Td := 2500, Tn := 7000,
    Alo := 400, Ahi := 520, Blo := 900, Bhi := 1000, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }
/-- Downstream stage: it reads its request pin with a NEGATIVE delay `-300` (`Alo = Ahi`). -/
def Pn1 : Par :=
  { W := 2000, W1 := 2001, Ra := 3400, Ra1 := 3521, Fa := 4900, Fa1 := 5021,
    Rb := 6000, Rb1 := 6001, Fb := 7500, Fb1 := 7501, Td := 2500, Tn := 7000,
    Alo := -300, Ahi := -300, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }
def Pn (i : Nat) : Par := if i = 0 then Pn0 else Pn1

/-- **Counter-loop: a negative wire delay breaks `Causal`.** A two-stage closed loop meeting
H_LOOP exactly, the upstream stage `Wf` and meeting every one of its six cell rows (`Conj`:
its slow acknowledge pin keeps the race), the downstream stage reading its request 300 ps
"early" (`Ahi = -300 < 0`): the upstream stage's acknowledge surely rises before its node can
start to rise, so `Causal` fails, and with it (`causal_iff_mono`) Bzd's retiming of that stage;
it is the loop's causality, not a cell row, that breaks. -/
theorem negdelay_breaks_causal :
    ((Pn 1).Ra = (Pn 0).U0 ∧ (Pn 1).Ra1 = (Pn 0).U1 ∧ (Pn 1).Fa = (Pn 0).V0 ∧
      (Pn 1).Fa1 = (Pn 0).V1) ∧
    ((Pn 0).Rb = (Pn 1).U0 ∧ (Pn 0).Rb1 = (Pn 1).U1 ∧ (Pn 0).Fb = (Pn 1).V0 ∧
      (Pn 0).Fb1 = (Pn 1).V1) ∧
    Wf (Pn 0) ∧ Conj (Pn 0) ∧ (Pn 1).Ahi < 0 ∧ ¬ Causal (Pn 0) ∧
    ¬ Mono (linkEvs (Pn 0) (swOf (Pn 0))) := by
  have hw : Wf (Pn 0) := wf_of _ (by decide)
  have hn : ¬ Causal (Pn 0) := fun h => by have := h.ack_up; revert this; decide
  exact ⟨by decide, by decide, hw, (conj_iff _).2 (by decide), by decide, hn,
    fun M => hn ((causal_iff_mono hw).1 M)⟩

/-! ## 4. One global retiming: monotone on the whole network, and per stage -/

/-- The physical events of the chain: source request rise/fall, sink acknowledge rise/fall,
node `i` rise/fall, and the abstract wire copies of node `i` (`(ch (i+1)).req`, `(ch i).ack`:
physically the node itself, read through the neighbours' pins, so the same window). -/
inductive NE where
  | sU | sD | kU | kD
  | nU (i : Nat) | nD (i : Nat) | wU (i : Nat) | wD (i : Nat)

def NE.ok (N : Nat) : NE → Prop
  | .nU i => i < N
  | .nD i => i < N
  | .wU i => i < N
  | .wD i => i < N
  | _ => True

/-- Window and abstract step of every network event (steps from `kS`). -/
def nev (N : Nat) (P : Nat → Par) : NE → Ev × Nat
  | .sU => (⟨(P 0).Ra, (P 0).Ra1⟩, (kS N P).sr)
  | .sD => (⟨(P 0).Fa, (P 0).Fa1⟩, (kS N P).sf)
  | .kU => (⟨(P (N - 1)).Rb, (P (N - 1)).Rb1⟩, (kS N P).ku)
  | .kD => (⟨(P (N - 1)).Fb, (P (N - 1)).Fb1⟩, (kS N P).kd)
  | .nU i => (⟨(P i).U0, (P i).U1⟩, (kS N P).cu i)
  | .nD i => (⟨(P i).V0, (P i).V1⟩, (kS N P).cd i)
  | .wU i => (⟨(P i).U0, (P i).U1⟩, (kS N P).cu i + 1)
  | .wD i => (⟨(P i).V0, (P i).V1⟩, (kS N P).cd i + 1)

/-- Monotone retiming of an indexed family of events (Bzd's `Mono`, family form). -/
def MonoF {ι : Type} (ok : ι → Prop) (f : ι → Ev × Nat) : Prop :=
  ∀ p q, ok p → ok q → (f p).1.hi < (f q).1.lo → (f p).2 < (f q).2

theorem lo_base {N : Nat} {P : Nat → Par} (L : LoOrd N P) : ∀ i < N, (P 0).Ra ≤ (P i).U0 := by
  intro i
  induction i with
  | zero => intro _; exact L.l1
  | succ j ih => intro h; have := (L.l4 j h).1; have := ih (by omega); omega

theorem nev_shape {N : Nat} {P : Nat → Par} (C : ChainPar N P) (p : NE) (hp : p.ok N) :
    ∃ lo hi d, nev N P p = (⟨lo, hi⟩, key (P 0).Ra (4 * N + 8) lo d) ∧ (P 0).Ra ≤ lo ∧
      lo ≤ hi ∧ d < 4 * N + 8 := by
  have L := chain_loOrd C
  have pos := C.pos
  have b := lo_base L
  have w0 := C.wf 0 (by omega); have wN := C.wf (N - 1) (by omega)
  have l5 := L.l5; have l1 := L.l1; have l2 := L.l2; have l3 := L.l3
  have uv : ∀ i < N, (P i).U0 ≤ (P i).U1 ∧ (P i).V0 ≤ (P i).V1 := fun i hi => by
    have w := C.wf i hi; have := w.ha; have := w.hb; have := w.hA; have := w.hB
    simp only [Par.U0, Par.U1, Par.V0, Par.V1]; omega
  have := w0.ha; have := wN.hb; have := b (N - 1) (by omega)
  cases p with
  | sU => exact ⟨_, _, 0, rfl, Int.le_refl _, by omega, by omega⟩
  | sD => exact ⟨_, _, 2 * N + 4, rfl, by omega, by omega, by omega⟩
  | kU => exact ⟨_, _, 2 * N + 2, rfl, by omega, by omega, by omega⟩
  | kD => exact ⟨_, _, 4 * N + 6, rfl, by omega, by omega, by omega⟩
  | nU i =>
    simp only [NE.ok] at hp
    exact ⟨_, _, 2 * i + 2, rfl, b i hp, (uv i hp).1, by omega⟩
  | nD i =>
    simp only [NE.ok] at hp
    have := b i hp; have := L.l6 i hp
    exact ⟨_, _, 2 * N + 6 + 2 * i, rfl, by omega, (uv i hp).2, by omega⟩
  | wU i =>
    simp only [NE.ok] at hp
    exact ⟨_, _, 2 * i + 2 + 1, by simp [nev, kS, key_succ], b i hp, (uv i hp).1, by omega⟩
  | wD i =>
    simp only [NE.ok] at hp
    have := b i hp; have := L.l6 i hp
    exact ⟨_, _, 2 * N + 6 + 2 * i + 1, by simp [nev, kS, key_succ], by omega, (uv i hp).2,
      by omega⟩

/-- **The one global retiming is monotone on the WHOLE network** (every pair of events of
every stage and both ends). -/
theorem net_mono {N : Nat} {P : Nat → Par} (C : ChainPar N P) : MonoF (NE.ok N) (nev N P) := by
  intro p q hp hq hlt
  obtain ⟨lo, hi, d, e, hT, hlh, hd⟩ := nev_shape C p hp
  obtain ⟨lo', hi', d', e', -, -, -⟩ := nev_shape C q hq
  rw [e, e'] at hlt ⊢
  simp only at hlt ⊢
  exact key_mono hT (by omega) hd

theorem mono_of_sub {ι : Type} {ok : ι → Prop} {f : ι → Ev × Nat} (M : MonoF ok f)
    {l : List (Ev × Nat)} (h : ∀ x ∈ l, ∃ p, ok p ∧ f p = x) : Mono l := by
  intro x hx y hy hlt
  obtain ⟨p, hp, rfl⟩ := h x hx
  obtain ⟨q, hq, rfl⟩ := h y hy
  exact M p q hp hq hlt

/-- Stage `i`'s six events (Bzd's `linkEvs` windows, from its OWN `Par`) with the steps the
global retiming gives them. -/
def stageEvs (N : Nat) (P : Nat → Par) (i : Nat) : List (Ev × Nat) :=
  let S := kS N P
  [(⟨(P i).Ra, (P i).Ra1⟩, S.rq i), (⟨(P i).U0, (P i).U1⟩, S.cu i),
   (⟨(P i).Fa, (P i).Fa1⟩, S.rqf i), (⟨(P i).Rb, (P i).Rb1⟩, S.ak N (i + 1)),
   (⟨(P i).V0, (P i).V1⟩, S.cd i), (⟨(P i).Fb, (P i).Fb1⟩, S.akf N (i + 1))]

/-- **Per-cell retimings agree on shared wires.** For every stage, the restriction of the one
global retiming to that stage's own six events is a monotone retiming in Bzd's sense; the
stage's request events are, by H_LOOP, the upstream node's events, and its acknowledge
events the downstream node's, with ONE step each (the same abstract channel). -/
theorem stage_mono {N : Nat} {P : Nat → Par} (C : ChainPar N P) :
    ∀ i < N, Mono (stageEvs N P i) := by
  intro i hi
  apply mono_of_sub (net_mono C)
  intro x hx
  simp only [stageEvs, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases i with _ | j
    · exact ⟨.sU, trivial, rfl⟩
    · have la := C.loop_a j hi
      refine ⟨.wU j, (by simp only [NE.ok]; omega), ?_⟩
      simp only [nev, la.1, la.2.1, rq_succ]
  · exact ⟨.nU i, hi, rfl⟩
  · rcases i with _ | j
    · exact ⟨.sD, trivial, rfl⟩
    · have la := C.loop_a j hi
      refine ⟨.wD j, (by simp only [NE.ok]; omega), ?_⟩
      simp only [nev, la.2.2.1, la.2.2.2, rqf_succ]
  · by_cases e : i + 1 = N
    · have hk : i = N - 1 := by omega
      refine ⟨.kU, trivial, ?_⟩
      simp only [nev, Sch.ak, if_pos e, ← hk]
    · have lb := C.loop_b i (by omega)
      refine ⟨.wU (i + 1), (by simp only [NE.ok]; omega), ?_⟩
      simp only [nev, lb.1, lb.2.1, ak_lt (show i + 1 < N by omega)]
  · exact ⟨.nD i, hi, rfl⟩
  · by_cases e : i + 1 = N
    · have hk : i = N - 1 := by omega
      refine ⟨.kD, trivial, ?_⟩
      simp only [nev, Sch.akf, if_pos e, ← hk]
    · have lb := C.loop_b i (by omega)
      refine ⟨.wD (i + 1), (by simp only [NE.ok]; omega), ?_⟩
      simp only [nev, lb.2.2.1, lb.2.2.2, akf_lt (show i + 1 < N by omega)]

open Formal.Net.Ops.Link (Link) in
/-- **Headline (abstract half of the chain).** For every closed-loop chain (`ChainPar`), the
ONE key retiming gives a zero-delay run of C's chain network: C's `Link` at every stage on the
shared channels, `Protocol` and `Held` on every channel `0..N`, the abstract latch holding the
token from its opening; the retiming is monotone on the whole network and on every stage. -/
theorem chain_abstract {N : Nat} {P : Nat → Par} (C : ChainPar N P) (V : Nat) (u : Nat → Nat) :
    (∀ i < N, Link (chA (kS N P) N V u i) (chA (kS N P) N V u (i + 1)) (ndA (kS N P) i)) ∧
    (∀ j ≤ N, Protocol (chA (kS N P) N V u j)) ∧ (∀ j ≤ N, Held (chA (kS N P) N V u j)) ∧
    (∀ i n, (kS N P).cu i < n → (chA (kS N P) N V u (i + 1)).dat n = V) ∧
    MonoF (NE.ok N) (nev N P) ∧ (∀ i < N, Mono (stageEvs N P i)) ∧ (∀ i < N, Causal (P i)) :=
  let H := kS_ok (chain_loOrd C)
  ⟨chain_link H V u, chain_proto H V u, chain_held H V u, chain_latched _ N V u, net_mono C,
    stage_mono C, chain_causal C⟩

end Formal.Cells.ZeroDelayNet
