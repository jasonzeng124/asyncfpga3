import Formal.Target.SpecRunt

/-!
# A vacuity in the frozen statement, and its repair (shard A, 2026-11-16)

**Problem (shard C's finding, JOURNAL-C 2026-11-16 03:36).** In the target's boundary one request node can serve
several input channels (gcd_ps and research's bench builds drive `a`, `b` and `start` from one flop: "OneReq").
`Spec.Env` asks the environment, on EACH channel separately, for `ReqLive` (if `req = ack`, `req` eventually moves)
and `ReqMoves` (`req` moves only when `req = ack`). If the circuit raises `a`'s acknowledge but never `start`'s, the
shared request must fall for `a` and may not fall for `start`: no behaviour satisfies `Env`, so `NetCorrectSeq`
holds VACUOUSLY on every delay assignment that leads there, though the real harness simply hangs.
`env_unsat_partial_ack` below states this for any boundary with `B.a.req = B.start.req`.

**Repair, without touching the frozen `Spec.lean`.** `ReqLiveWF`: the environment must not keep a request still
FOREVER while the move stays allowed by every channel that shares the node (weak fairness). The old `ReqLive`
implies it (`reqLiveWF_of_reqLive`), so `Env` implies `EnvWF` (`envWF_of_env`): every behaviour the old statement
covered is still covered, and `NetCorrectSeqWF → NetCorrectSeq` (same for the H_RUNT forms). Hence every refutation
already proved (`¬ NetCorrectSeq…`) is a refutation of the WF form too (`not_wf_of_not`), with no new proof. The
WF form is strictly stronger where it matters: the partial-ack hang satisfies `EnvWF` (`envWF` asks nothing of a
request whose move some sharer forbids), and there `Correct`'s `CircIn` (start's `AckLive`) fails, so a hang is a
counterexample instead of a vacuous case.

**Status.** A proposal: `NetCorrectSeqRuntWF` should replace `NetCorrectSeqRunt` as THE statement. Changing the
frozen statement needs a journaled reason (JOURNAL.md 2026-11-16) and an audit row; until the audit has looked, the
frozen statement stands and this file only adds definitions and implications.
-/

namespace Formal.Target

/-- The acknowledges of the channels among `[B.a, B.b, B.start]` whose request is the node `r`. -/
def sharers (x : Beh) (B : Boundary) (r : Nat) : List Sig :=
  ([B.a, B.b, B.start].filter (fun c => c.req = r)).map (fun c => x c.ack)

/-- **Weak-fairness request liveness.** From `t0` on, if `r = a` and the driver may move (`r` high, or more to send),
the request is not kept equal to EVERY sharer's acknowledge for ever. With `a` among the sharers this is implied by
`ReqLive`; it asks nothing when some sharer keeps the move forbidden. -/
def ReqLiveWF (r a : Sig) (sh : List Sig) (t0 : Nat) (more : Nat → Prop) : Prop :=
  ∀ t, t0 ≤ t → r t = a t → (r t = true ∨ more (rises r t0 t)) → ¬ ∀ s, t ≤ s → ∀ o ∈ sh, r s = o s

theorem reqLiveWF_of_reqLive {r a : Sig} {sh : List Sig} {t0 : Nat} {more : Nat → Prop} (ha : a ∈ sh)
    (h : ReqLive r a t0 more) : ReqLiveWF r a sh t0 more := by
  intro t ht he hm hall
  obtain ⟨s, hs, hne⟩ := h t ht he hm
  exact hne (hall s hs a ha)

/-- `EnvIn` with `ReqLiveWF` (the sharers' acknowledges `sh`) in place of `ReqLive`; every other clause unchanged. -/
def EnvInWF (x : Beh) (ch : InCh) (sh : List Sig) (R su : Nat) (n : Option Nat) (vals : Nat → Nat) : Prop :=
  (∀ t, t ≤ R → x ch.req t = false) ∧
  ReqMoves (x ch.req) (x ch.ack) R ∧
  ReqLiveWF (x ch.req) (x ch.ack) sh R (Offered n) ∧
  (∀ t, R ≤ t → x ch.req t = true → Offered n (rises (x ch.req) R t - 1)) ∧
  (∀ t, R ≤ t → x ch.req t = false → x ch.req (t + 1) = true →
      ∀ s, t + 1 - su ≤ s → s ≤ t + 1 → busVal x ch.data s = vals (rises (x ch.req) R (t + 1) - 1)) ∧
  (∀ t, R ≤ t → (x ch.req t = true ∨ x ch.ack t = true) → 1 ≤ rises (x ch.req) R t →
      busVal x ch.data t = vals (rises (x ch.req) R t - 1))

/-- **H_ENV, weak-fairness form.** -/
def EnvWF (x : Beh) (B : Boundary) (R su Δo : Nat) (n : Option Nat) (va vb : Nat → Nat) : Prop :=
  (∀ t, t < R → x B.rst t = true) ∧ (∀ t, R ≤ t → x B.rst t = false) ∧
  (∀ k, Offered n k → va k < 2 ^ 31 ∧ vb k < 2 ^ 31) ∧
  EnvInWF x B.a (sharers x B B.a.req) R su n va ∧ EnvInWF x B.b (sharers x B B.b.req) R su n vb ∧
  EnvInWF x B.start (sharers x B B.start.req) R su n (fun _ => 0) ∧
  EnvOut x B.out0 R Δo ∧ EnvOut x B.pend R Δo

theorem mem_sharers_self (x : Beh) (B : Boundary) (c : InCh) (hc : c ∈ [B.a, B.b, B.start]) :
    x c.ack ∈ sharers x B c.req := by
  unfold sharers
  exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp⟩, rfl⟩

theorem envInWF_of_envIn {x : Beh} {ch : InCh} {sh : List Sig} {R su : Nat} {n : Option Nat} {vals : Nat → Nat}
    (ha : x ch.ack ∈ sh) (h : EnvIn x ch R su n vals) : EnvInWF x ch sh R su n vals := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, reqLiveWF_of_reqLive ha h3, h4, h5, h6⟩

/-- Every environment of the frozen statement is an environment of the WF form. -/
theorem envWF_of_env {x : Beh} {B : Boundary} {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat}
    (h : Env x B R su Δo n va vb) : EnvWF x B R su Δo n va vb := by
  obtain ⟨h1, h2, h3, ha, hb, hs, ho, hp⟩ := h
  exact ⟨h1, h2, h3,
    envInWF_of_envIn (mem_sharers_self x B B.a (by simp)) ha,
    envInWF_of_envIn (mem_sharers_self x B B.b (by simp)) hb,
    envInWF_of_envIn (mem_sharers_self x B B.start (by simp)) hs, ho, hp⟩

/-- The sequential statement with `EnvWF`. -/
def NetCorrectSeqWF (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    Behaves p (circuit N B) x → ArbOK T A x → EnvWF x B R su Δo n va vb → SeqEnv x B R →
      Correct x B R Δo n va vb

/-- The H_RUNT(w) statement (LUT-pin filter) with `EnvWF`: the proposed new THE statement. -/
def NetCorrectSeqRuntWF (w : Nat) (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) :
    Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    BehavesRuntOn lutGate w p (circuit N B) x → ArbOK T A x → EnvWF x B R su Δo n va vb → SeqEnv x B R →
      Correct x B R Δo n va vb

theorem netCorrectSeq_of_wf {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (h : NetCorrectSeqWF N B A p T R su Δo) : NetCorrectSeq N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb hb ha (envWF_of_env he) hs

theorem netCorrectSeqRunt_of_wf {w : Nat} {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar}
    {T R su Δo : Nat} (h : NetCorrectSeqRuntWF w N B A p T R su Δo) : NetCorrectSeqRunt w N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb hb ha (envWF_of_env he) hs

/-- Every refutation of the frozen statement refutes the WF form. -/
theorem not_wf_of_not {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (h : ¬ NetCorrectSeq N B A p T R su Δo) : ¬ NetCorrectSeqWF N B A p T R su Δo :=
  fun hw => h (netCorrectSeq_of_wf hw)

theorem not_runtWF_of_not {w : Nat} {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (h : ¬ NetCorrectSeqRunt w N B A p T R su Δo) : ¬ NetCorrectSeqRuntWF w N B A p T R su Δo :=
  fun hw => h (netCorrectSeqRunt_of_wf hw)

/-- **The vacuity, stated.** With `a` and `start` sharing one request node: if at some `t ≥ R` that request is high,
and from `t` on `a`'s acknowledge is high and `start`'s is low for ever (C's "partial-ack deadlock"), no behaviour
satisfies the frozen `Env`. So the frozen statement says nothing about such a hang, whatever the circuit does. -/
theorem env_unsat_partial_ack {x : Beh} {B : Boundary} {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat}
    (hsh : B.a.req = B.start.req) (t : Nat) (hR : R ≤ t) (hrt : x B.a.req t = true)
    (hA : ∀ s, t ≤ s → x B.a.ack s = true) (hS : ∀ s, t ≤ s → x B.start.ack s = false) :
    ¬ Env x B R su Δo n va vb := by
  rintro ⟨-, -, -, ⟨-, -, hlive, -⟩, -, ⟨-, hmovS, -⟩, -, -⟩
  -- once high, the request cannot fall: start's ReqMoves allows a move only when req = start's ack = false
  have hstay : ∀ u, t ≤ u → x B.a.req u = true := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact hrt
    | succ u hu ih =>
      by_contra hne
      have hmv : x B.start.req (u + 1) ≠ x B.start.req u := by
        rw [← hsh, ih]; exact hne
      have := hmovS u (le_trans hR hu) hmv
      rw [← hsh, ih, hS u hu] at this
      exact Bool.noConfusion this
  -- but a's ReqLive needs the request to differ from a's acknowledge (= true) at some later time
  obtain ⟨v, hv, hne⟩ := hlive t hR (by rw [hrt, hA t le_rfl]) (Or.inl hrt)
  exact hne (by rw [hstay v hv, hA v hv])

/-- **The repair is not vacuous there.** In the same situation `ReqLiveWF` asks nothing of the shared request: `start`'s
acknowledge, a sharer, stays different from it. -/
theorem reqLiveWF_partial_ack {x : Beh} {B : Boundary}
    (hsh : B.a.req = B.start.req) (t : Nat) (hrt : ∀ s, t ≤ s → x B.a.req s = true)
    (hS : ∀ s, t ≤ s → x B.start.ack s = false) (u : Nat) (hu : t ≤ u) :
    ¬ ∀ s, u ≤ s → ∀ o ∈ sharers x B B.a.req, x B.a.req s = o s := by
  intro hall
  have hmem : x B.start.ack ∈ sharers x B B.a.req := by
    rw [hsh]; exact mem_sharers_self x B B.start (by simp)
  have := hall u le_rfl _ hmem
  rw [hrt u hu, hS u hu] at this
  exact Bool.noConfusion this

end Formal.Target
