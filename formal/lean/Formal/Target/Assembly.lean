import Formal.Target.Spec
import Mathlib.Data.Nat.Find

/-!
# Formal.Target.Assembly — THE statement from a per-pair step (the top-level assembly)

Shard A, 2026-11-06. An addition next to the frozen `Spec.lean` (no definition there changes).

**Problem, plainly.** `Spec.Correct` is a conjunction of seven clauses over all time (protocol, liveness, one
output per pair, the data, quiescence). A proof for the decoded target will not argue about all time at once: it
will show (i) after reset the circuit is idle, (ii) while nothing is offered it stays idle, and (iii) from an idle
state, one offered pair produces one correct output handshake and the circuit is idle again before the next
request can rise. This file proves, once and for every netlist, that (i)-(iii) give `Correct`, so the remaining
work on the target is exactly (i)-(iii), stated here as `Plan`.

**The shape assumed of the boundary** (`OneReq`): the three input requests and the end channel's request are ONE
node. That is how both targets are wired (the rig's `bd_fork` broadcasts one request; bdc's end token is the start
request passed through, `p_end_req = req`, and the kernel's start acknowledge is a C-element of that request and
the end acknowledge, shard A journal 2026-11-06).

**`Plan x B R Δo I`** (for one behaviour `x`, with an invariant `I` on time chosen by the prover. NOT "the storage
nodes hold their idle values": the environment may raise the next request in the very ps the last boundary
acknowledge falls, so `I` must include the settling states right after that fall and be closed under `quiet`):
* `base`: `I R` and the circuit's boundary outputs (input acks, `out0.req`) are low at `R`;
* `quiet`: if `I t` and every boundary node is low at `t` and the request is still low at `t + 1`, then the
  circuit's boundary outputs are low at `t + 1` and `I (t + 1)`;
* `step`: if `I t`, every boundary node is low at `t` and the request rises at `t`, then there is a `t2 > t`
  (`StepCore`): no further request rise before `t2`; on `[t, t2)` the input acks and the output requests move
  only as four-phase allows; `out0.req` rises exactly once, at some `t0`, and from `Δo` after that until its
  acknowledge the data bus shows `gcd` of the operand buses as they were at `t + 1`; every boundary node is low
  at `t2`, and `I t2`.

**Shown:** `correct_of_plan`: `OneReq B` and `Env x B R su Δo n va vb` and `Plan x B R Δo I` imply
`Correct x B R Δo n va vb`. Hence `netCorrectSeq_of_plan`: if every behaviour meeting THE statement's
hypotheses has some `I` with `Plan`, THE statement holds. SeqEnv and H_ARB are not used here; they are what a
proof of `step` for the target will need.

**Not shown:** `Plan` for any netlist (that is S4/S6 for the target). **How much this reduces** (independent review,
2026-11-06): `Plan` is about as strong as `Correct` plus "exactly one `out0` rise per request and no spontaneous
outputs" (e.g. `I t := Low x B t ∧ rises = rises` works when the circuit is correct); what the assembly removes is the
all-time bookkeeping (liveness, counting, indices, quiescence), not the circuit argument.
-/

namespace Formal.Target.Assembly
open Formal.Target

/-- A rising edge of `s` at `t` (between `t` and `t + 1`). -/
def edge (s : Sig) (t : Nat) : Prop := s t = false ∧ s (t + 1) = true

/-- The ten boundary nodes, in `Correct`'s order. -/
def bnodes (B : Boundary) : List Nat :=
  [B.a.req, B.a.ack, B.b.req, B.b.ack, B.start.req, B.start.ack, B.out0.req, B.out0.ack, B.pend.req, B.pend.ack]

/-- The boundary nodes the circuit drives (the end request is the env's request in `OneReq` boundaries). -/
def couts (B : Boundary) : List Nat := [B.a.ack, B.b.ack, B.start.ack, B.out0.req]

def Low (x : Beh) (B : Boundary) (t : Nat) : Prop := ∀ v ∈ bnodes B, x v t = false

/-- One request node for `a`, `b`, `start` and the end channel. -/
def OneReq (B : Boundary) : Prop := B.b.req = B.a.req ∧ B.start.req = B.a.req ∧ B.pend.req = B.a.req

/-- One pair's episode on `[t1, t2)`, with `out0`'s request rising at `t0`. -/
structure StepCore (x : Beh) (B : Boundary) (Δo : Nat) (I : Nat → Prop) (t1 t2 t0 : Nat) : Prop where
  lt : t1 < t2
  norise : ∀ t, t1 < t → t < t2 → ¬ edge (x B.a.req) t
  ack : ∀ ch ∈ [B.a, B.b, B.start], ∀ t, t1 ≤ t → t < t2 → x ch.ack (t + 1) ≠ x ch.ack t → x ch.ack t ≠ x ch.req t
  req : ∀ ch ∈ [B.out0, B.pend], ∀ t, t1 ≤ t → t < t2 → x ch.req (t + 1) ≠ x ch.req t → x ch.req t = x ch.ack t
  t0_ge : t1 ≤ t0
  t0_lt : t0 < t2
  o_edge : edge (x B.out0.req) t0
  o_once : ∀ t, t1 ≤ t → t < t2 → edge (x B.out0.req) t → t = t0
  data : ∀ t, t0 + 1 + Δo ≤ t → (∀ s, t0 + 1 ≤ s → s ≤ t → x B.out0.req s = true ∧ x B.out0.ack s = false) →
      busVal x B.out0.data t = Nat.gcd (busVal x B.a.data (t1 + 1)) (busVal x B.b.data (t1 + 1))
  low : Low x B t2
  inv : I t2

/-- **The plan**: base, quiet and step (see the module doc). -/
structure Plan (x : Beh) (B : Boundary) (R Δo : Nat) (I : Nat → Prop) : Prop where
  base_inv : I R
  base_low : ∀ v ∈ couts B, x v R = false
  quiet : ∀ t, R ≤ t → I t → Low x B t → x B.a.req (t + 1) = false →
      (∀ v ∈ couts B, x v (t + 1) = false) ∧ I (t + 1)
  step : ∀ t, R ≤ t → I t → Low x B t → edge (x B.a.req) t → ∃ t2 t0, StepCore x B Δo I t t2 t0

/-! ## Counting rises -/

theorem rises_self (s : Sig) (R : Nat) : ∀ t, t ≤ R → rises s R t = 0
  | 0, _ => rfl
  | t + 1, h => by
    simp only [rises]
    rw [rises_self s R t (by omega)]
    simp
    omega

theorem rises_noedge (s : Sig) (R t : Nat) (h : ¬ edge s t) : rises s R (t + 1) = rises s R t := by
  simp only [rises]
  have : ¬ (R ≤ t ∧ s t = false ∧ s (t + 1) = true) := fun h' => h ⟨h'.2.1, h'.2.2⟩
  simp [this]

theorem rises_edge (s : Sig) {R t : Nat} (hR : R ≤ t) (h : edge s t) : rises s R (t + 1) = rises s R t + 1 := by
  simp only [rises]
  have : R ≤ t ∧ s t = false ∧ s (t + 1) = true := ⟨hR, h.1, h.2⟩
  simp [this]

/-- No edge on `[a, b)`: the count does not change. -/
theorem rises_const (s : Sig) (R a : Nat) : ∀ b, a ≤ b → (∀ t, a ≤ t → t < b → ¬ edge s t) →
    rises s R b = rises s R a
  | 0, h, _ => by rw [show a = 0 by omega]
  | b + 1, h, hn => by
    rcases Nat.lt_or_ge a (b + 1) with hab | hab
    · rw [rises_noedge s R b (hn b (by omega) (by omega)),
        rises_const s R a b (by omega) (fun t h1 h2 => hn t h1 (by omega))]
    · rw [show a = b + 1 by omega]

theorem rises_mono (s : Sig) (R : Nat) : ∀ a b, a ≤ b → rises s R a ≤ rises s R b := by
  intro a b h
  induction b with
  | zero => rw [show a = 0 by omega]
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hab | hab
    · have := ih (by omega)
      simp only [rises]
      omega
    · rw [show a = b + 1 by omega]

/-- No edge on `[a, b)` and low at `a`: low on `[a, b]`. -/
theorem low_of_noedge (s : Sig) (a : Nat) (ha : s a = false) : ∀ b, a ≤ b →
    (∀ t, a ≤ t → t < b → ¬ edge s t) → s b = false
  | 0, h, _ => by rw [show (0 : Nat) = a by omega]; exact ha
  | b + 1, h, hn => by
    rcases Nat.lt_or_ge a (b + 1) with hab | hab
    · have hb := low_of_noedge s a ha b (by omega) (fun t h1 h2 => hn t h1 (by omega))
      by_contra hc
      exact hn b (by omega) (by omega) ⟨hb, by simpa using hc⟩
    · rw [show b + 1 = a by omega]; exact ha

/-- A signal low at `a` and high at `b > a` has an edge in `[a, b)`. -/
theorem exists_edge (s : Sig) (a : Nat) (ha : s a = false) (b : Nat) (hab : a ≤ b) (hb : s b = true) :
    ∃ t, a ≤ t ∧ t < b ∧ edge s t := by
  by_contra hc
  push Not at hc
  have := low_of_noedge s a ha b hab (fun t h1 h2 he => hc t h1 h2 he)
  rw [hb] at this
  exact Bool.noConfusion this

/-! ## The phase invariant -/

section
variable {x : Beh} {B : Boundary} {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat} {I : Nat → Prop}

/-- Quiet point: invariant, everything low, and as many `out0` rises as request rises. -/
def Q (x : Beh) (B : Boundary) (R : Nat) (I : Nat → Prop) (t : Nat) : Prop :=
  I t ∧ Low x B t ∧ rises (x B.a.req) R t = rises (x B.out0.req) R t

/-- Every time from `R` on is a quiet point or inside an episode started at a quiet point. -/
def Ph (x : Beh) (B : Boundary) (R Δo : Nat) (I : Nat → Prop) (t : Nat) : Prop :=
  Q x B R I t ∨ ∃ a t2 t0, R ≤ a ∧ a < t ∧ t < t2 ∧ Q x B R I a ∧ edge (x B.a.req) a ∧ StepCore x B Δo I a t2 t0

/-- The covering form: `t` is a quiet point with no request edge, or in an episode `[a, t2)`. -/
def Cov (x : Beh) (B : Boundary) (R Δo : Nat) (I : Nat → Prop) (t : Nat) : Prop :=
  (Q x B R I t ∧ ¬ edge (x B.a.req) t) ∨
    ∃ a t2 t0, R ≤ a ∧ a ≤ t ∧ t < t2 ∧ Q x B R I a ∧ edge (x B.a.req) a ∧ StepCore x B Δo I a t2 t0

theorem low_mem {t : Nat} (h : Low x B t) {v : Nat} (hv : v ∈ bnodes B) : x v t = false := h v hv

theorem cov_of_ph (hp : Plan x B R Δo I) {t : Nat} (hR : R ≤ t) (h : Ph x B R Δo I t) : Cov x B R Δo I t := by
  rcases h with hq | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
  · by_cases he : edge (x B.a.req) t
    · obtain ⟨t2, t0, hs⟩ := hp.step t hR hq.1 hq.2.1 he
      exact Or.inr ⟨t, t2, t0, hR, le_rfl, hs.lt, hq, he, hs⟩
    · exact Or.inl ⟨hq, he⟩
  · exact Or.inr ⟨a, t2, t0, ha, hat.le, ht2, hqa, hea, hs⟩

/-- The env's acknowledges stay low while their request is low. -/
theorem envack_stay {r k : Sig} {R t : Nat} (hm : AckMoves r k R) (hR : R ≤ t) (hk : k t = false)
    (hr : r t = false) : k (t + 1) = false := by
  by_contra hc
  have := hm t hR (by rw [hk]; simpa using hc)
  rw [hk, hr] at this
  exact this rfl

theorem quiet_next (hreq : OneReq B) (he : Env x B R su Δo n va vb) (hp : Plan x B R Δo I) {t : Nat}
    (hR : R ≤ t) (hq : Q x B R I t) (hne : ¬ edge (x B.a.req) t) : Q x B R I (t + 1) := by
  obtain ⟨hI, hL, hc⟩ := hq
  have hr0 : x B.a.req t = false := hL _ (by simp [bnodes])
  have hr1 : x B.a.req (t + 1) = false := by
    by_contra hc'
    exact hne ⟨hr0, by simpa using hc'⟩
  obtain ⟨hco, hI'⟩ := hp.quiet t hR hI hL hr1
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ := he
  have ho1 : x B.out0.req (t + 1) = false := hco _ (by simp [couts])
  have hoa : x B.out0.ack (t + 1) = false :=
    envack_stay hb7.2.1 hR (hL _ (by simp [bnodes])) (hL _ (by simp [bnodes]))
  have hpa : x B.pend.ack (t + 1) = false :=
    envack_stay hb8.2.1 hR (hL _ (by simp [bnodes])) (hL _ (by simp [bnodes]))
  obtain ⟨h1, h2, h3⟩ := hreq
  refine ⟨hI', ?_, ?_⟩
  · intro v hv
    simp only [bnodes, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr1
    · exact hco _ (by simp [couts])
    · rw [h1]; exact hr1
    · exact hco _ (by simp [couts])
    · rw [h2]; exact hr1
    · exact hco _ (by simp [couts])
    · exact ho1
    · exact hoa
    · rw [h3]; exact hr1
    · exact hpa
  · have hoe : ¬ edge (x B.out0.req) t := fun h => by have h' := h.2; rw [ho1] at h'; exact Bool.noConfusion h'
    rw [rises_noedge _ R t hne, rises_noedge _ R t hoe, hc]

/-- Counts across an episode. -/
theorem step_counts {a t2 t0 : Nat} (hRa : R ≤ a) (hea : edge (x B.a.req) a) (hs : StepCore x B Δo I a t2 t0) :
    rises (x B.a.req) R t2 = rises (x B.a.req) R a + 1 ∧ rises (x B.out0.req) R t2 = rises (x B.out0.req) R a + 1 := by
  constructor
  · rw [rises_const _ R (a + 1) t2 hs.lt (fun t h1 h2 => hs.norise t (by omega) h2), rises_edge _ hRa hea]
  · rw [rises_const _ R (t0 + 1) t2 hs.t0_lt (fun t h1 h2 he => by
        have := hs.o_once t (by have := hs.t0_ge; omega) h2 he; omega),
      rises_edge _ (by have := hs.t0_ge; omega) hs.o_edge,
      rises_const _ R a t0 hs.t0_ge (fun t h1 h2 he => by
        have := hs.o_once t h1 (by have := hs.t0_lt; omega) he; omega)]

theorem ph_all (hreq : OneReq B) (he : Env x B R su Δo n va vb) (hp : Plan x B R Δo I) :
    ∀ t, R ≤ t → Ph x B R Δo I t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    left
    refine ⟨hp.base_inv, ?_, by rw [rises_self _ R R le_rfl, rises_self _ R R le_rfl]⟩
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩ := he
    have hr : x B.a.req R = false := hb4.1 R le_rfl
    obtain ⟨h1, h2, h3⟩ := hreq
    intro v hv
    simp only [bnodes, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr
    · exact hp.base_low _ (by simp [couts])
    · rw [h1]; exact hr
    · exact hp.base_low _ (by simp [couts])
    · rw [h2]; exact hr
    · exact hp.base_low _ (by simp [couts])
    · exact hp.base_low _ (by simp [couts])
    · exact hb7.1 R le_rfl
    · rw [h3]; exact hr
    · exact hb8.1 R le_rfl
  | succ t hRt ih =>
    rcases cov_of_ph hp hRt ih with ⟨hq, hne⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
    · exact Or.inl (quiet_next hreq he hp hRt hq hne)
    · rcases Nat.lt_or_ge (t + 1) t2 with h | h
      · exact Or.inr ⟨a, t2, t0, ha, by omega, h, hqa, hea, hs⟩
      · have : t + 1 = t2 := by omega
        subst this
        left
        obtain ⟨c1, c2⟩ := step_counts ha hea hs
        exact ⟨hs.inv, hs.low, by rw [c1, c2, hqa.2.2]⟩

theorem cov_all (hreq : OneReq B) (he : Env x B R su Δo n va vb) (hp : Plan x B R Δo I) {t : Nat} (hR : R ≤ t) :
    Cov x B R Δo I t := cov_of_ph hp hR (ph_all hreq he hp t hR)

/-- At a quiet point, the circuit's outputs and the request are low one ps later unless the request rises. -/
theorem quiet_couts (hp : Plan x B R Δo I) {t : Nat} (hR : R ≤ t) (hq : Q x B R I t) (hne : ¬ edge (x B.a.req) t) :
    x B.a.req (t + 1) = false ∧ ∀ v ∈ couts B, x v (t + 1) = false := by
  have hr0 : x B.a.req t = false := hq.2.1 _ (by simp [bnodes])
  have hr1 : x B.a.req (t + 1) = false := by
    by_contra hc
    exact hne ⟨hr0, by simpa using hc⟩
  exact ⟨hr1, (hp.quiet t hR hq.1 hq.2.1 hr1).1⟩

/-- From a quiet point with more pairs owed, the request rises again at a quiet point. -/
theorem next_rise (hreq : OneReq B) (he : Env x B R su Δo n va vb) (hp : Plan x B R Δo I) {q : Nat} (hR : R ≤ q)
    (hq : Q x B R I q) (hmore : Offered n (rises (x B.a.req) R q)) :
    ∃ t1, q ≤ t1 ∧ Q x B R I t1 ∧ edge (x B.a.req) t1 := by
  classical
  by_cases hex : ∃ t1, q ≤ t1 ∧ edge (x B.a.req) t1
  · let P := fun t1 => q ≤ t1 ∧ edge (x B.a.req) t1
    have hP : ∃ t1, P t1 := hex
    let t1 := Nat.find hP
    have ht1 : P t1 := Nat.find_spec hP
    have hmin : ∀ s, s < t1 → ¬ P s := fun s hs => Nat.find_min hP hs
    -- quiet on [q, t1]
    have hall : ∀ s, q ≤ s → s ≤ t1 → Q x B R I s := by
      intro s hs1 hs2
      induction s, hs1 using Nat.le_induction with
      | base => exact hq
      | succ s hqs ih =>
        exact quiet_next hreq he hp (by omega) (ih (by omega)) (fun h => hmin s (by omega) ⟨hqs, h⟩)
    exact ⟨t1, ht1.1, hall t1 ht1.1 le_rfl, ht1.2⟩
  · exfalso
    push Not at hex
    have hall : ∀ s, q ≤ s → Q x B R I s := by
      intro s hs
      induction s, hs using Nat.le_induction with
      | base => exact hq
      | succ s hqs ih => exact quiet_next hreq he hp (by omega) ih (hex s hqs)
    obtain ⟨hb1, hb2, hb3, ha, hb, hst, ho, hpe⟩ := he
    have hrq : x B.a.req q = x B.a.ack q := by
      rw [hq.2.1 _ (by simp [bnodes]), hq.2.1 _ (by simp [bnodes])]
    obtain ⟨s, hs, hne⟩ := ha.2.2.1 q hR hrq (Or.inr hmore)
    have := hall s hs
    rw [this.2.1 B.a.req (by simp [bnodes]), this.2.1 B.a.ack (by simp [bnodes])] at hne
    exact hne rfl

/-- The `k`-th episode's `out0` count: inside an episode after its `out0` rise, the count is the episode's. -/
theorem out0_count_in {a t2 t0 t : Nat} (hRa : R ≤ a) (hs : StepCore x B Δo I a t2 t0) (h1 : t0 < t) (h2 : t ≤ t2) :
    rises (x B.out0.req) R t = rises (x B.out0.req) R a + 1 := by
  rw [rises_const _ R (t0 + 1) t (by omega) (fun u hu1 hu2 he => by
        have := hs.o_once u (by have := hs.t0_ge; omega) (by omega) he; omega),
      rises_edge _ (by have := hs.t0_ge; omega) hs.o_edge,
      rises_const _ R a t0 hs.t0_ge (fun u hu1 hu2 he => by
        have := hs.o_once u hu1 (by have := hs.t0_lt; omega) he; omega)]

/-- Inside an episode, before or at its `out0` rise, `out0.req` is low. -/
theorem out0_low_before {a t2 t0 t : Nat} (hs : StepCore x B Δo I a t2 t0) (hqa : Low x B a) (h1 : a ≤ t)
    (h2 : t ≤ t0) : x B.out0.req t = false :=
  low_of_noedge _ a (hqa _ (by simp [bnodes])) t h1 (fun u hu1 hu2 he => by
    have := hs.o_once u hu1 (by have := hs.t0_lt; omega) he; omega)

/-- The request count is constant inside an episode after its start. -/
theorem req_count_in {a t2 t0 t : Nat} (hRa : R ≤ a) (hea : edge (x B.a.req) a) (hs : StepCore x B Δo I a t2 t0)
    (h1 : a < t) (h2 : t ≤ t2) : rises (x B.a.req) R t = rises (x B.a.req) R a + 1 := by
  rw [rises_const _ R (a + 1) t (by omega) (fun u hu1 hu2 => hs.norise u (by omega) (by omega)),
    rises_edge _ hRa hea]

/-- A request that eventually falls back after being high together with an env acknowledge: liveness of the
"both high" case. `k` is an env acknowledge (moves only when different from `r`). -/
theorem live_hh {r k : Sig} {R t e : Nat} (hm : AckMoves r k R) (hR : R ≤ t) (hr : r t = true) (hk : k t = true)
    (hte : t ≤ e) (he : r e = false) : ∃ s, t ≤ s ∧ r s ≠ k s := by
  classical
  let P := fun s => t ≤ s ∧ ¬ (r s = true ∧ k s = true)
  have hP : ∃ s, P s := ⟨e, hte, fun h => by rw [he] at h; exact Bool.noConfusion h.1⟩
  let s := Nat.find hP
  have hs : P s := Nat.find_spec hP
  have hmin : ∀ u, u < s → ¬ P u := fun u hu => Nat.find_min hP hu
  have hst : t < s := by
    rcases Nat.lt_or_ge t s with h | h
    · exact h
    · exfalso; have : s = t := by have := hs.1; omega
      exact hs.2 (this ▸ ⟨hr, hk⟩)
  have hprev : r (s - 1) = true ∧ k (s - 1) = true := by
    by_contra hc
    exact hmin (s - 1) (by omega) ⟨by omega, hc⟩
  have hks : k s = true := by
    by_contra hc
    have := hm (s - 1) (by omega) (by rw [show s - 1 + 1 = s by omega, hprev.2]; simpa using hc)
    rw [hprev.1, hprev.2] at this
    exact this rfl
  refine ⟨s, hs.1, fun h => hs.2 ⟨?_, hks⟩⟩
  rw [h, hks]

/-- Liveness of the "both low, owed a rise" case: the request rises at some `t0 ≥ t` and the env acknowledge
cannot rise before it. -/
theorem live_ll {r k : Sig} {R t t0 : Nat} (hm : AckMoves r k R) (hR : R ≤ t) (hk : k t = false) (ht0 : t ≤ t0)
    (he : edge r t0) : ∃ s, t ≤ s ∧ r s ≠ k s := by
  by_cases hk1 : k (t0 + 1) = true
  · obtain ⟨u, hu1, hu2, hue⟩ := exists_edge k t hk (t0 + 1) (by omega) hk1
    have := hm u (by omega) (by rw [hue.1, hue.2]; simp)
    refine ⟨u, hu1, fun h => this h.symm⟩
  · refine ⟨t0 + 1, by omega, ?_⟩
    rw [he.2]
    simpa using hk1

theorem correct_of_plan (hreq : OneReq B) (he : Env x B R su Δo n va vb) (hp : Plan x B R Δo I) :
    Correct x B R Δo n va vb := by
  classical
  have hcov := fun {t : Nat} (h : R ≤ t) => cov_all hreq he hp h
  obtain ⟨h1, h2, h3⟩ := hreq
  have hE := he
  obtain ⟨hb1, hb2, hb3, hA, hB, hS, hO, hPe⟩ := he
  -- input channels
  have circIn : ∀ ch ∈ [B.a, B.b, B.start], CircIn x ch R := by
    intro ch hch
    have hchreq : ch.req = B.a.req := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
      rcases hch with rfl | rfl | rfl
      · rfl
      · exact h1
      · exact h2
    have hackR : x ch.ack R = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
      rcases hch with rfl | rfl | rfl <;> exact hp.base_low _ (by simp [couts])
    have hackc : ∀ t, ∀ hR : R ≤ t, (Q x B R I t ∧ ¬ edge (x B.a.req) t) → x ch.ack t = false ∧ x ch.ack (t + 1) = false := by
      intro t hR ⟨hq, hne⟩
      have hm : ch.ack ∈ bnodes B ∧ ch.ack ∈ couts B := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
        rcases hch with rfl | rfl | rfl <;> simp [bnodes, couts]
      exact ⟨hq.2.1 _ hm.1, (quiet_couts hp hR hq hne).2 _ hm.2⟩
    refine ⟨hackR, ?_, ?_⟩
    · intro t hR hne
      rcases hcov hR with hq | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · obtain ⟨c1, c2⟩ := hackc t hR hq
        exact absurd (by rw [c1, c2]) hne
      · exact hs.ack ch hch t hat ht2 hne
    · intro t hR hne
      rcases hcov hR with hq | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · exfalso
        apply hne
        rw [(hackc t hR hq).1, hchreq, hq.1.2.1 _ (by simp [bnodes])]
      · refine ⟨t2, ht2.le, ?_⟩
        have hm : ch.ack ∈ bnodes B := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl | rfl <;> simp [bnodes]
        rw [hs.low _ hm, hchreq, hs.low _ (by simp [bnodes])]
  -- the request is owed a rise from a quiet point: eventually an episode starts
  have future_ep : ∀ t, R ≤ t → x B.a.req t = false → Offered n (rises (x B.a.req) R t) →
      ∃ a t2 t0, t ≤ a ∧ R ≤ a ∧ Q x B R I a ∧ edge (x B.a.req) a ∧ StepCore x B Δo I a t2 t0 := by
    intro t hR hr hmore
    -- a quiet point q ≥ t with the same request count
    obtain ⟨q, hqt, hRq, hq, hcnt⟩ : ∃ q, t ≤ q ∧ R ≤ q ∧ Q x B R I q ∧ rises (x B.a.req) R q = rises (x B.a.req) R t := by
      rcases hcov hR with ⟨hq, _⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · exact ⟨t, le_rfl, hR, hq, rfl⟩
      · rcases Nat.eq_or_lt_of_le hat with h | h
        · subst h; exact ⟨a, le_rfl, ha, hqa, rfl⟩
        · obtain ⟨c1, _⟩ := step_counts ha hea hs
          refine ⟨t2, ht2.le, by omega, ⟨hs.inv, hs.low, ?_⟩, ?_⟩
          · rw [c1, step_counts ha hea hs |>.2, hqa.2.2]
          · rw [c1, req_count_in ha hea hs h ht2.le]
    obtain ⟨a, hqa', hQa, hea⟩ := next_rise ⟨h1, h2, h3⟩ hE hp hRq hq (hcnt ▸ hmore)
    obtain ⟨t2, t0, hs⟩ := hp.step a (by omega) hQa.1 hQa.2.1 hea
    exact ⟨a, t2, t0, by omega, by omega, hQa, hea, hs⟩
  refine ⟨circIn B.a (by simp), circIn B.b (by simp), circIn B.start (by simp), ?_, ?_, ?_, ?_⟩
  · -- out0
    refine ⟨hp.base_low _ (by simp [couts]), ?_, ?_, ?_⟩
    · intro t hR hne
      rcases hcov hR with ⟨hq, hn⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · exfalso; apply hne
        rw [hq.2.1 _ (by simp [bnodes]), (quiet_couts hp hR hq hn).2 _ (by simp [couts])]
      · exact hs.req B.out0 (by simp) t hat ht2 hne
    · intro t hR heq hor
      rcases hcov hR with ⟨hq, hn⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · -- quiet: out0.req low, so the owed rise
        have hol : x B.out0.req t = false := hq.2.1 _ (by simp [bnodes])
        have hmore : Offered n (rises (x B.a.req) R t) := by
          rcases hor with h | h
          · rw [hol] at h; exact Bool.noConfusion h
          · rw [hq.2.2]; exact h
        obtain ⟨a, t2, t0, hta, hRa, hQa, hea, hs⟩ := future_ep t hR (hq.2.1 _ (by simp [bnodes])) hmore
        have hk : x B.out0.ack t = false := by rw [← heq]; exact hol
        exact live_ll hO.2.1 hR hk (le_trans hta hs.t0_ge) hs.o_edge
      · rcases Nat.lt_or_ge t0 t with hlt | hge
        · -- after this episode's out0 rise
          rcases Bool.eq_false_or_eq_true (x B.out0.req t) with hot | hof
          · -- both high
            have hk : x B.out0.ack t = true := by rw [← heq]; exact hot
            exact live_hh hO.2.1 hR hot hk ht2.le (hs.low _ (by simp [bnodes]))
          · -- both low; owed: the count is the episode's, go to the next episode
            have hmore : Offered n (rises (x B.out0.req) R t) := by
              rcases hor with h | h
              · rw [hof] at h; exact Bool.noConfusion h
              · exact h
            have hc : rises (x B.a.req) R t2 = rises (x B.out0.req) R t := by
              rw [(step_counts ha hea hs).1, out0_count_in ha hs hlt ht2.le, hqa.2.2]
            obtain ⟨a', t2', t0', hta, hRa', hQa', hea', hs'⟩ :=
              future_ep t2 (by omega) (hs.low _ (by simp [bnodes])) (hc ▸ hmore)
            have hk : x B.out0.ack t = false := by rw [← heq]; exact hof
            exact live_ll hO.2.1 hR hk (by have := hs'.t0_ge; omega) hs'.o_edge
        · -- before or at this episode's out0 rise: out0.req low, its rise is ahead
          have hol := out0_low_before hs hqa.2.1 hat hge
          have hk : x B.out0.ack t = false := by rw [← heq]; exact hol
          exact live_ll hO.2.1 hR hk hge hs.o_edge
    · intro t hR hot
      rcases hcov hR with ⟨hq, hn⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · rw [hq.2.1 _ (by simp [bnodes])] at hot; exact Bool.noConfusion hot
      · have hlt : t0 < t := by
          by_contra hc
          rw [out0_low_before hs hqa.2.1 hat (by omega)] at hot
          exact Bool.noConfusion hot
        rw [out0_count_in ha hs hlt ht2.le, ← hqa.2.2, ← rises_edge _ ha hea]
        exact hA.2.2.2.1 (a + 1) (by omega) hea.2
  · -- pend (its request is the env's request)
    have hpr : B.pend.req = B.a.req := h3
    refine ⟨by rw [hpr]; exact hA.1 R le_rfl, ?_, ?_, ?_⟩
    · intro t hR hne
      rcases hcov hR with ⟨hq, hn⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · exfalso; apply hne
        rw [hpr, hq.2.1 _ (by simp [bnodes]), (quiet_couts hp hR hq hn).1]
      · exact hs.req B.pend (by simp) t hat ht2 hne
    · intro t hR heq hor
      rw [hpr] at heq hor ⊢
      rcases Bool.eq_false_or_eq_true (x B.a.req t) with hrt | hrf
      · have hk : x B.pend.ack t = true := by rw [← heq]; exact hrt
        -- inside an episode (a quiet point has the request low); it is low at the episode's end
        rcases hcov hR with ⟨hq, _⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
        · rw [hq.2.1 _ (by simp [bnodes])] at hrt; exact Bool.noConfusion hrt
        · have hm := hPe.2.1
          rw [hpr] at hm
          exact live_hh hm hR hrt hk ht2.le (hs.low _ (by simp [bnodes]))
      · have hmore : Offered n (rises (x B.a.req) R t) := by
          rcases hor with h | h
          · rw [hrf] at h; exact Bool.noConfusion h
          · exact h
        obtain ⟨a, t2, t0, hta, hRa, hQa, hea, hs⟩ := future_ep t hR hrf hmore
        have hk : x B.pend.ack t = false := by rw [← heq]; exact hrf
        have hm := hPe.2.1
        rw [hpr] at hm
        exact live_ll hm hR hk hta hea
    · intro t hR hrt
      rw [hpr] at hrt ⊢
      exact hA.2.2.2.1 t hR hrt
  · -- data
    intro t0 t hR ho0 ho1 hwin hhold
    have hedge : edge (x B.out0.req) t0 := ⟨ho0, ho1⟩
    rcases hcov hR with ⟨hq, hn⟩ | ⟨a, t2, t0', ha, hat, ht2, hqa, hea, hs⟩
    · rw [(quiet_couts hp hR hq hn).2 _ (by simp [couts])] at ho1; exact Bool.noConfusion ho1
    · have heq0 : t0 = t0' := hs.o_once t0 hat ht2 hedge
      subst heq0
      rw [hs.data t hwin hhold]
      have hcnt : rises (x B.out0.req) R (t0 + 1) = rises (x B.a.req) R (a + 1) := by
        rw [out0_count_in ha hs (by omega) (by have := hs.t0_lt; omega), ← hqa.2.2, rises_edge _ ha hea]
      rw [hcnt]
      have hva := hA.2.2.2.2.1 a ha hea.1 hea.2 (a + 1) (by omega) le_rfl
      have hbr : x B.b.req = x B.a.req := by rw [h1]
      have hvb := hB.2.2.2.2.1 a ha (by rw [hbr]; exact hea.1) (by rw [hbr]; exact hea.2) (a + 1) (by omega) le_rfl
      rw [hva, hvb, hbr]
  · -- finitely many pairs: eventually quiet for ever
    intro m hm
    subst hm
    -- the request count never exceeds m
    have hbound : ∀ t, rises (x B.a.req) R t ≤ m := by
      intro t
      induction t with
      | zero => simp [rises]
      | succ t ih =>
        by_cases he' : R ≤ t ∧ edge (x B.a.req) t
        · rw [rises_edge _ he'.1 he'.2]
          have := hA.2.2.2.1 (t + 1) (by omega) he'.2.2
          simp only [Offered] at this
          rw [rises_edge _ he'.1 he'.2] at this
          omega
        · have : rises (x B.a.req) R (t + 1) = rises (x B.a.req) R t := by
            simp only [rises]
            have : ¬ (R ≤ t ∧ x B.a.req t = false ∧ x B.a.req (t + 1) = true) :=
              fun h => he' ⟨h.1, h.2.1, h.2.2⟩
            simp [this]
          omega
    -- a time after which the count is maximal
    obtain ⟨tm, htm⟩ : ∃ tm, ∀ t, rises (x B.a.req) R t ≤ rises (x B.a.req) R tm := by
      by_contra hc
      push Not at hc
      -- then the count is unbounded
      have : ∀ k, ∃ t, k ≤ rises (x B.a.req) R t := by
        intro k
        induction k with
        | zero => exact ⟨0, Nat.zero_le _⟩
        | succ k ih =>
          obtain ⟨t, ht⟩ := ih
          obtain ⟨t', ht'⟩ := hc t
          exact ⟨t', by omega⟩
      obtain ⟨t, ht⟩ := this (m + 1)
      have := hbound t
      omega
    -- a quiet point q ≥ max R tm
    have hRtm : R ≤ max R tm := le_max_left _ _
    obtain ⟨q, hqge, hRq, hq⟩ : ∃ q, max R tm ≤ q ∧ R ≤ q ∧ Q x B R I q := by
      rcases hcov hRtm with ⟨hq, _⟩ | ⟨a, t2, t0, ha, hat, ht2, hqa, hea, hs⟩
      · exact ⟨max R tm, le_rfl, hRtm, hq⟩
      · obtain ⟨c1, c2⟩ := step_counts ha hea hs
        exact ⟨t2, ht2.le, by omega, hs.inv, hs.low, by rw [c1, c2, hqa.2.2]⟩
    -- no request edge from q on
    have hnoedge : ∀ t, q ≤ t → ¬ edge (x B.a.req) t := by
      intro t ht he'
      have h1' := rises_edge (x B.a.req) (show R ≤ t by omega) he'
      have h2' := htm (t + 1)
      have h3' := rises_mono (x B.a.req) R tm t (by omega)
      omega
    have hallQ : ∀ t, q ≤ t → Q x B R I t := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hq
      | succ t hqt ih => exact quiet_next ⟨h1, h2, h3⟩ hE hp (by omega) ih (hnoedge t hqt)
    -- the count at q is m (else the env still owes a request)
    have hcq : rises (x B.a.req) R q = m := by
      have := hbound q
      by_contra hne
      obtain ⟨t1, ht1, _, he'⟩ := next_rise ⟨h1, h2, h3⟩ hE hp hRq hq (by simp only [Offered]; omega)
      exact hnoedge t1 ht1 he'
    refine ⟨q, fun t ht => ⟨fun v hv => (hallQ t ht).2.1 v hv, ?_, ?_⟩⟩
    · rw [← (hallQ t ht).2.2, rises_const _ R q t ht (fun u hu _ => hnoedge u hu), hcq]
    · rw [h3, rises_const _ R q t ht (fun u hu _ => hnoedge u hu), hcq]

end

/-- **THE (sequential) statement from a plan.** If every behaviour meeting THE statement's hypotheses has an
invariant `I` with `Plan`, THE statement holds. -/
theorem netCorrectSeq_of_plan {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (hreq : OneReq B)
    (h : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit N B) x → ArbOK T A x →
      Env x B R su Δo n va vb → SeqEnv x B R → ∃ I, Plan x B R Δo I) :
    NetCorrectSeq N B A p T R su Δo := by
  intro x n va vb hb ha he hs
  obtain ⟨I, hp⟩ := h x n va vb hb ha he hs
  exact correct_of_plan hreq he hp

end Formal.Target.Assembly
