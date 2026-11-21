import Formal.Net.Handshake

/-!
# Probe C-8f: handshake networks of Dynamatic operators refine their token semantics

Core Lean only. Builds on 8a (`Formal.Net.Handshake`: `Chan`, `SendStep`,
`RecvStep`, `Protocol`, `cnt`, `riseB`, `fallB`, `TokAt`).

## Tokens are counted at the OFFER, not at the close

8a names a token by its close (the k-th `ack↓`). For a linear pipeline of
latches that is the natural choice. For Dynamatic's operators it is not: a
fork, join, steer or mux is combinational in the handshake, so its OUTPUT
token closes BEFORE its input token does (the input's ack waits for the
outputs' acks). Causality runs the other way at the offer: an output request
rises strictly after the input requests it is made of (every gate has a
positive delay). So here:

* `OffAt c k r`: the k-th `req↑` of `c` is the step `r → r+1`;
* the token's value is `c.dat (r+1)`, the bus right after the request rose;
* `Held c` (hypothesis H_BUNDLE on channel `c`): the bus does not move while
  the channel is mid-transaction, so it keeps the offer value from `r+1` until
  the close of the same transaction. This is LIBRARY.md's
  bundling with setup margin 0 and hold margin 0 at the channel's wires (the
  receiving latch's own setup/hold margins are 8a's `SetupHold` on top).
  `close_val` turns it into 8a's view: the k-th close carries the k-th offer's
  value.

## Networks

`Net C O`: channels `C`, operators `O`, each operator has an input list and
an output list; `prod c` / `cons c` is the unique operator sending / receiving
on `c` (the environment is operators too: sources, sinks). ANY graph: cycles
are allowed, nothing here is finite or acyclic.

* `OpProto`: causal assume-guarantee for one operator (8a's `StageSpec.ag`
  generalised to many channels): if every channel it touches started in reset
  (`Init`) and obeyed both protocol rules at all steps `< t`, and its inputs
  are bundled (`Held`, needed by the steer and the mux, whose select is data),
  it obeys its own rules at step `t`.
  `net_protocol`: every channel obeys the four-phase protocol. Strong
  induction on time; no acyclicity needed because the guarantees are strict.
* `Eqs o σ`: the token-level (Kahn) equations of operator `o` over value
  streams `σ : C → Nat → Nat` (`σ c k` = value of the k-th token of `c`).
* `OpData`: the operator's output token `k`, offered at `r`, has the value
  that ANY stream assignment `σ` must give it if `σ` agrees with the circuit
  on every token offered strictly before `r` and satisfies the operator's
  equations. This is the per-operator content (fork copies, join pairs,
  steer routes by the condition, mux selects by the select token).
* `net_refines`: if every operator meets `OpProto` and `OpData` and every
  channel meets `Held`, then for EVERY solution `ref` of all the equations,
  the value of every offered token on every channel equals `ref`; by
  `close_val`, so does every closed token (`net_refines_close`): at every
  time, each channel's sequence of values so far is a prefix of the token
  semantics' sequence. `net_determinate`: two solutions agree on everything
  the circuit offers.

Why no "every cycle passes through a link" here: the per-operator specs are
strictly causal in time (each output offer is strictly after the offers it
reads), so the time induction closes on any graph. The link condition (and 9's
three-stage rule) is about LIVENESS: a cycle without storage cannot hold a
token and deadlocks. Safety holds on it vacuously.
-/

namespace Formal.Net.Ops
open Formal.Net Formal.Net.Handshake

/-! ## Offers and the count invariant -/

/-- The `k`-th request rise of `c` is the step `r → r+1`. -/
def OffAt (c : Chan) (k r : Nat) : Prop := riseB c.req r = true ∧ cnt (riseB c.req) r = k

/-- The channel is mid-transaction (not in the idle phase `00`). -/
def inTx (c : Chan) (t : Nat) : Bool := c.req t || c.ack t

/-- H_BUNDLE (one channel): the bus does not move across a step that starts
and ends mid-transaction. So it holds the value it has right after `req↑`
until the step after the close (`ack↓`); it may change only across steps that
start or end in the idle phase. (LIBRARY.md: "data stable from req-rise to
ack-fall", with zero setup and hold margin at the channel's own wires.) -/
def Held (c : Chan) : Prop :=
  ∀ t, inTx c t = true → inTx c (t + 1) = true → c.dat (t + 1) = c.dat t

theorem rise_bool : ∀ (X Y : Nat) (r a r' a' : Bool),
    X = Y + (if (r || a) = true then 1 else 0) → (r' ≠ r → r = a) → (a' ≠ a → a ≠ r) →
    X + (if (!r && r') = true then 1 else 0) =
      Y + (if (a && !a') = true then 1 else 0) + (if (r' || a') = true then 1 else 0) := by
  intro X Y r a r' a'
  cases r <;> cases a <;> cases r' <;> cases a' <;> simp <;> omega

/-- Under the protocol, #req↑ = #ack↓ + [mid-transaction]. -/
theorem rise_inv {c : Chan} (hp : Protocol c) : ∀ t,
    cnt (riseB c.req) t = cnt (fallB c.ack) t + (if inTx c t = true then 1 else 0) := by
  intro t
  induction t with
  | zero => simp [cnt, inTx, hp.1.1, hp.1.2]
  | succ t ih =>
    simp only [cnt, fallB, riseB, inTx] at ih ⊢
    exact rise_bool _ _ _ _ _ _ ih (hp.2 t).1 (hp.2 t).2

theorem cnt_unique (f : Nat → Bool) {r r' k : Nat} (h1 : f r = true) (h2 : cnt f r = k)
    (h1' : f r' = true) (h2' : cnt f r' = k) : r = r' := by
  rcases Nat.lt_trichotomy r r' with h | h | h
  · have := cnt_mono f (show r + 1 ≤ r' by omega); rw [cnt_succ_of h1] at this; omega
  · exact h
  · have := cnt_mono f (show r' + 1 ≤ r by omega); rw [cnt_succ_of h1'] at this; omega

theorem off_unique {c : Chan} {k r r' : Nat} (h : OffAt c k r) (h' : OffAt c k r') : r = r' :=
  cnt_unique _ h.1 h.2 h'.1 h'.2

/-- At an offer step the channel is idle. -/
theorem off_idle {c : Chan} (hp : Protocol c) {r : Nat} (h : riseB c.req r = true) :
    c.req r = false ∧ c.ack r = false := by
  have h0 : c.req r = false := by simp [riseB] at h; exact h.1
  have h1 : c.req (r+1) = true := by simp [riseB] at h; exact h.2
  exact ⟨h0, req_rise_ack_low (hp.2 r).1 h0 h1⟩

/-- At the k-th offer, k closes have happened. -/
theorem off_falls {c : Chan} (hp : Protocol c) {k r : Nat} (h : OffAt c k r) :
    cnt (fallB c.ack) r = k := by
  have hi := rise_inv hp r
  have := off_idle hp h.1
  simp [inTx, this.1, this.2] at hi; rw [h.2] at hi; omega

/-- Every close is preceded by the offer with the same index. -/
theorem tok_off {c : Chan} (hp : Protocol c) {k e : Nat} (h : TokAt c k e) :
    ∃ r, r < e ∧ OffAt c k r := by
  have hae : c.ack e = true := by simp [TokAt, fallB] at h; exact h.1.1
  have hi := rise_inv hp e
  simp [inTx, hae, h.2] at hi
  obtain ⟨r, hr, hf, hc⟩ := cnt_witness _ e k hi
  exact ⟨r, hr, hf, hc⟩

/-- While a transaction is open, `Held` keeps the bus at the offer value.
Count form used by the operator proofs: if the `k`-th offer is at `r` and at
`s > r` there are still only `k` closes, the bus at `s` is the offer value. -/
theorem held_at {c : Chan} (hp : Protocol c) (hh : Held c) {k r s : Nat}
    (ho : OffAt c k r) (hs : r < s) (hc : cnt (fallB c.ack) s = k) :
    c.dat s = c.dat (r + 1) := by
  have hf0 := off_falls hp ho
  have hin : ∀ u, r + 1 ≤ u → u ≤ s → inTx c u = true := by
    intro u h1 h2
    have a1 := cnt_mono (fallB c.ack) h2
    have a2 := cnt_mono (fallB c.ack) (show r ≤ u by omega)
    have a3 := cnt_mono (riseB c.req) h1
    rw [cnt_succ_of ho.1, ho.2] at a3
    have hi := rise_inv hp u
    cases h : inTx c u
    · rw [h] at hi; simp at hi; omega
    · rfl
  have : ∀ d, r + 1 + d ≤ s → c.dat (r + 1 + d) = c.dat (r + 1) := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [show r + 1 + (d + 1) = r + 1 + d + 1 by omega,
        hh _ (hin _ (by omega) (by omega)) (hin _ (by omega) (by omega)), ih (by omega)]
  have := this (s - (r + 1)) (by omega)
  rwa [show r + 1 + (s - (r + 1)) = s by omega] at this

/-- The value at the k-th close is the value of the k-th offer. -/
theorem close_val {c : Chan} (hp : Protocol c) (hh : Held c) {k e r : Nat}
    (h : TokAt c k e) (ho : OffAt c k r) : c.dat e = c.dat (r + 1) := by
  obtain ⟨r', hr', ho'⟩ := tok_off hp h
  have := off_unique ho ho'; subst this
  exact held_at hp hh ho hr' h.2

/-- The last offer before a step where `req` is high: it is the
`(#req↑ - 1)`-th, `req` stayed high since, and no close happened since. -/
theorem open_offer {c : Chan} (hp : Protocol c) {t : Nat} (hq : c.req t = true) :
    ∃ r k, r < t ∧ OffAt c k r ∧ cnt (riseB c.req) t = k + 1 ∧ cnt (fallB c.ack) t = k ∧
      ∀ u, r < u → u ≤ t → c.req u = true := by
  obtain ⟨r, hr, h0, h1, hl⟩ := last_rise c.req hp.1.1 t hq
  have hrise : riseB c.req r = true := by simp [riseB, h0, h1]
  -- no rise in (r, t)
  have hnr : ∀ u, r < u → u < t → riseB c.req u = false := by
    intro u h1 h2; have := hl u h1 (by omega); simp [riseB, this]
  have hcr : cnt (riseB c.req) t = cnt (riseB c.req) r + 1 := by
    have : ∀ d, r + 1 + d ≤ t → cnt (riseB c.req) (r + 1 + d) = cnt (riseB c.req) r + 1 := by
      intro d
      induction d with
      | zero => intro _; exact cnt_succ_of hrise
      | succ d ih =>
        intro hd
        have e := hnr (r + 1 + d) (by omega) (by omega)
        show cnt (riseB c.req) (r + 1 + d + 1) = _
        simp only [cnt, e]; simpa using ih (by omega)
    have := this (t - (r + 1)) (by omega)
    rwa [show r + 1 + (t - (r + 1)) = t by omega] at this
  refine ⟨r, cnt (riseB c.req) r, hr, ⟨hrise, rfl⟩, hcr, ?_, hl⟩
  have hi := rise_inv hp t
  simp [inTx, hq] at hi; omega

/-- Counting offers with a property of their value, in time or in token index:
if `σ` is the circuit's offer value on every token offered before `R`, then for
`r ≤ R` the number of offers before `r` whose value satisfies `P` equals the
number of indices `< #offers before r` with `P (σ i)`. -/
theorem cnt_offers {c : Chan} {σ : Nat → Nat} {R : Nat} (P : Nat → Bool)
    (hag : ∀ i u, u < R → OffAt c i u → σ i = c.dat (u + 1)) :
    ∀ r, r ≤ R → cnt (fun u => riseB c.req u && P (c.dat (u + 1))) r =
      cnt (fun i => P (σ i)) (cnt (riseB c.req) r) := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    have ih := ih (by omega)
    cases hrise : riseB c.req r
    · simp [cnt, hrise, ih]
    · have hs := hag _ r (by omega) ⟨hrise, rfl⟩
      simp [cnt, hrise, ih, hs]

/-! ## Networks -/

variable {C O : Type}

/-- A handshake network: operators with input and output channel lists; each
channel has exactly one producer `prod c` and one consumer `cons c`. -/
structure Net (C O : Type) where
  ins : O → List C
  outs : O → List C
  prod : C → O
  cons : C → O
  prod_iff : ∀ c o, c ∈ outs o ↔ prod c = o
  cons_iff : ∀ c o, c ∈ ins o ↔ cons c = o

/-- Causal assume-guarantee protocol spec of one operator (inputs: it is the
receiver; outputs: it is the sender). -/
structure OpProto (ch : C → Chan) (ins outs : List C) : Prop where
  ag : ∀ t, (∀ c ∈ ins, Init (ch c)) → (∀ c ∈ outs, Init (ch c)) → (∀ c ∈ ins, Held (ch c)) →
       (∀ s, s < t → (∀ c ∈ ins, Rules (ch c) s) ∧ (∀ c ∈ outs, Rules (ch c) s)) →
       (∀ c ∈ ins, RecvStep (ch c) t) ∧ (∀ c ∈ outs, SendStep (ch c) t)
  initIn : ∀ c ∈ ins, (ch c).ack 0 = false
  initOut : ∀ c ∈ outs, (ch c).req 0 = false

/-- Every channel of a network of causal operators obeys the four-phase
protocol. Cycles allowed; strong induction on time. -/
theorem net_protocol (N : Net C O) (ch : C → Chan)
    (hop : ∀ o, OpProto ch (N.ins o) (N.outs o)) (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ c, Protocol (ch c) := by
  have hinit : ∀ c, Init (ch c) := fun c =>
    ⟨(hop (N.prod c)).initOut c ((N.prod_iff c _).2 rfl),
     (hop (N.cons c)).initIn c ((N.cons_iff c _).2 rfl)⟩
  have step : ∀ t, ∀ c, Rules (ch c) t := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      intro c
      have prem : ∀ o, ∀ s, s < t → (∀ c ∈ N.ins o, Rules (ch c) s) ∧
          (∀ c ∈ N.outs o, Rules (ch c) s) := fun o s hs => ⟨fun c _ => ih s hs c, fun c _ => ih s hs c⟩
      exact ⟨((hop (N.prod c)).ag t (fun c _ => hinit c) (fun c _ => hinit c) (fun c _ => H_BUNDLE c) (prem _)).2 c
                ((N.prod_iff c _).2 rfl),
             ((hop (N.cons c)).ag t (fun c _ => hinit c) (fun c _ => hinit c) (fun c _ => H_BUNDLE c) (prem _)).1 c
                ((N.cons_iff c _).2 rfl)⟩
  intro c
  exact ⟨hinit c, fun t => step t c⟩

/-- `σ` agrees with the circuit on every token offered strictly before `r`. -/
def Agree (ch : C → Chan) (σ : C → Nat → Nat) (r : Nat) : Prop :=
  ∀ c k r', r' < r → OffAt (ch c) k r' → σ c k = (ch c).dat (r' + 1)

/-- Per-operator data spec: given the protocol and `Held` on its channels, the
value of each output token is forced by the operator's token equations `E`
and the tokens offered strictly earlier. -/
def OpData (ch : C → Chan) (ins outs : List C) (E : (C → Nat → Nat) → Prop) : Prop :=
  (∀ c ∈ ins, Protocol (ch c) ∧ Held (ch c)) → (∀ c ∈ outs, Protocol (ch c) ∧ Held (ch c)) →
  ∀ c ∈ outs, ∀ k r, OffAt (ch c) k r → ∀ σ, Agree ch σ r → E σ → σ c k = (ch c).dat (r + 1)

/-- Refinement: every offered token on every channel has the value that every
solution of the token equations gives it. -/
theorem net_refines (N : Net C O) (ch : C → Chan) (E : O → (C → Nat → Nat) → Prop)
    (hop : ∀ o, OpProto ch (N.ins o) (N.outs o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (hdat : ∀ o, OpData ch (N.ins o) (N.outs o) (E o))
    (ref : C → Nat → Nat) (href : ∀ o, E o ref) :
    ∀ c k r, OffAt (ch c) k r → ref c k = (ch c).dat (r + 1) := by
  have hp := net_protocol N ch hop H_BUNDLE
  have all : ∀ r, ∀ c k, OffAt (ch c) k r → ref c k = (ch c).dat (r + 1) := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro c k ho
      have hag : Agree ch ref r := fun c' k' r' hr' ho' => ih r' hr' c' k' ho'
      exact hdat (N.prod c) (fun c _ => ⟨hp c, H_BUNDLE c⟩) (fun c _ => ⟨hp c, H_BUNDLE c⟩)
        c ((N.prod_iff c _).2 rfl) k r ho ref hag (href _)
  exact fun c k r => all r c k

/-- The same at the close: the k-th token latched on any channel is `ref c k`. -/
theorem net_refines_close (N : Net C O) (ch : C → Chan) (E : O → (C → Nat → Nat) → Prop)
    (hop : ∀ o, OpProto ch (N.ins o) (N.outs o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (hdat : ∀ o, OpData ch (N.ins o) (N.outs o) (E o))
    (ref : C → Nat → Nat) (href : ∀ o, E o ref) :
    ∀ c k e, TokAt (ch c) k e → (ch c).dat e = ref c k := by
  intro c k e h
  have hp := net_protocol N ch hop H_BUNDLE c
  obtain ⟨r, _, ho⟩ := tok_off hp h
  rw [close_val hp (H_BUNDLE c) h ho, net_refines N ch E hop H_BUNDLE hdat ref href c k r ho]

/-- Kahn determinacy, circuit side: two solutions of the token equations agree
on every token the circuit offers. (So the circuit's values do not depend on
which solution is called "the" semantics.) -/
theorem net_determinate (N : Net C O) (ch : C → Chan) (E : O → (C → Nat → Nat) → Prop)
    (hop : ∀ o, OpProto ch (N.ins o) (N.outs o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (hdat : ∀ o, OpData ch (N.ins o) (N.outs o) (E o))
    (ref ref' : C → Nat → Nat) (href : ∀ o, E o ref) (href' : ∀ o, E o ref') :
    ∀ c k r, OffAt (ch c) k r → ref c k = ref' c k := by
  intro c k r ho
  rw [net_refines N ch E hop H_BUNDLE hdat ref href c k r ho,
      net_refines N ch E hop H_BUNDLE hdat ref' href' c k r ho]

/-- Prefix form: the list of values latched on `c` (at its closes) before time `t`. -/
def closedVals (c : Chan) (t : Nat) : List Nat :=
  ((List.range t).filter (fun u => fallB c.ack u)).map c.dat

theorem closedVals_succ (c : Chan) (t : Nat) : closedVals c (t + 1) =
    closedVals c t ++ (if fallB c.ack t = true then [c.dat t] else []) := by
  unfold closedVals
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  cases h : fallB c.ack t <;> simp [h]

/-- At every time `t`, the sequence of values latched on each channel so far
is exactly the first `#closes` values of the token semantics' stream. -/
theorem net_prefix (N : Net C O) (ch : C → Chan) (E : O → (C → Nat → Nat) → Prop)
    (hop : ∀ o, OpProto ch (N.ins o) (N.outs o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (hdat : ∀ o, OpData ch (N.ins o) (N.outs o) (E o))
    (ref : C → Nat → Nat) (href : ∀ o, E o ref) :
    ∀ c t, closedVals (ch c) t = (List.range (cnt (fallB (ch c).ack) t)).map (ref c) := by
  intro c t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [closedVals_succ, ih]
    cases h : fallB (ch c).ack t
    · simp [cnt, h]
    · have hv := net_refines_close N ch E hop H_BUNDLE hdat ref href c _ t ⟨h, rfl⟩
      simp [cnt, h, List.range_succ, hv]

end Formal.Net.Ops
