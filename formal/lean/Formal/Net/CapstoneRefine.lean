import Formal.Timing.WinArray
import Formal.Timing.Unroll
import Formal.Net.Ops

/-!
# Probe C-8x: physical (bounded-delay) channel ⇒ zero-delay observation (per channel)

Core Lean only. Links the two trace models that probe 8w found the capstone mixes up:

* tcheck's **run semantics** (`Formal.Timing.Run`, 10a): one launch at time 0, per-arc
  `BoundedDelay lo hi` pins (the delay may differ from event to event, pure delay, glitches
  pass), quiescent start, zero-delay node functions `g v` on the pins;
* the **Ops channel model** (`Chan`, `Held`, `OffAt`): one req/ack/bus per channel, many
  transactions.

## R2: a settled node equals its zero-delay value (`run_settles`, `settled_of_quiet`)

`zdEval net g b v` evaluates the netlist with ALL delays set to zero, the launch node at `b`
and the run's own node functions `g`. In every run of a well-formed netlist, every node equals
`zdEval` of the launch's new value `sig 0 1` from time `1 + v * hmaxL net.arcs` on
(`run_settles`); hence any node that does not change at or after `t` already equals it at `t`
(`settled_of_quiet`). No glitch-freedom or monotonicity is assumed: whatever the node did
before, once it is quiet it holds the zero-delay value.

## R1+R2 per run: tcheck's verdicts give the value, not only the order

* `dag_settled`  (DAG verdict, `checkArr`: rules A, E, F, J): from the moment the request node
  changes (minus `setup`) on, every data node holds its zero-delay value.
* `cert_settled` (cert verdict, `potOK` + `winArr`: rules Hc, Rc, Fd, Z, X): the same, with the
  request change taken from the late-side run.

## Per channel, many transactions (`TxWin`, `sampled_eq_zd`, `held_of_txwin`)

`TxWin P sig data R` (H_TXWIN) windows the physical channel `P` (req/ack at the capture cell's
pins, `P.dat` = the bus at the capture pins, as a number of `data.length` bits, `bv`) into
single-launch runs: transaction `k` is launched at `τ k` with the channel idle and `k` offers
made (H_LAUNCH_AFTER_CLOSE, as 8w's `TxCover`), its offer is a request change of run `k`
(H_REQ_IN_RUN), and on `[τ k, τ (k+1))` the physical bus IS run `k`'s data nodes, shifted by
`τ k` (H_DATA_IS_RUN; stronger than 8w's `datIn`, which only attributed changes). Then:

* `sampled_eq_zd`: at EVERY instant `t` of transaction `k` (after its offer `r`, before the
  channel goes idle again) the observed bus equals `bv` of run `k`'s ZERO-DELAY data values.
  So a capture latch that closes anywhere inside the transaction (H_SAMPLE_IN_TX: its closing
  instant lies in that window) captures the zero-delay value.
* `held_of_txwin`: the observed channel satisfies the Ops `Held` (H_BUNDLE), given physical
  reset (`Init`) and the receiver rule (`RecvStep`, H_RECV, as in 8w).
* `zd_token`: the k-th token value (`P.dat (r+1)`, the Ops token convention) is the zero-delay
  value of run `k`.
* `*_dag`, `*_cert`: the same with the separation supplied by tcheck's DAG or cert verdict.

## What is NOT shown here

* That a physical channel meets `TxWin` (the gate/timing-model correspondence, H_TXWIN): that
  the bus between two launches is the response of the obligation netlist to its launch, with
  the netlist at rest at `τ k` (H_QUIESCENT at every launch).
* That `zdEval` of the obligation netlist is the Ops cell's function of its input tokens
  (H_FN: the LUT functions on the netlist implement the operator) and that its launch value is
  the upstream latch content (R3). These are what an Ops trace satisfying `H_CELLS` needs.
-/

namespace Formal.Net.CapstoneRefine
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing

/-! ## Zero-delay evaluation of a netlist -/

/-- The largest `hi` of an arc list. -/
def hmaxL : List Arc → Nat
  | [] => 0
  | a :: l => max a.hi (hmaxL l)

theorem hi_le_hmaxL : ∀ {l : List Arc} {a : Arc}, a ∈ l → a.hi ≤ hmaxL l
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.le_max_left _ _
    · have := hi_le_hmaxL h; simp only [hmaxL]; omega

/-- The netlist's value with every delay set to zero: launch node at `b`, node `v` = `g v` of
its sources' zero-delay values (arcs not into `v` are read as `false`; `g v` ignores them under
H_LOCAL). -/
def zdEval (net : Netlist) (g : Nat → (Nat → Bool) → Bool) (b : Bool) (v : Nat) : Bool :=
  if v = 0 then b else
  g v (fun k => match net.arcs[k]? with
    | some a => if h : a.src < v then zdEval net g b a.src else false
    | none => false)
termination_by v
decreasing_by exact h

theorem zdEval_zero (net : Netlist) (g : Nat → (Nat → Bool) → Bool) (b : Bool) :
    zdEval net g b 0 = b := by
  rw [zdEval]; simp

theorem zdEval_ne (net : Netlist) (g : Nat → (Nat → Bool) → Bool) (b : Bool) {v : Nat}
    (hv : v ≠ 0) : zdEval net g b v = g v (fun k => match net.arcs[k]? with
      | some a => if a.src < v then zdEval net g b a.src else false
      | none => false) := by
  rw [zdEval]; simp only [hv]
  congr 1

/-! ## R2: settling to the zero-delay value -/

/-- **Every node of a run reaches its zero-delay value** by `1 + v * hmaxL net.arcs` and keeps
it (single launch). -/
theorem run_settles {net : Netlist} (hwf : net.WF) {sig : Nat → Trace} (r : Run net sig) :
    ∀ v t, 1 + v * hmaxL net.arcs ≤ t → sig v t = zdEval net r.g (sig 0 1) v := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
  intro t ht
  by_cases hv : v = 0
  · subst hv
    rw [zdEval_zero]
    exact const_from (i := sig 0) (c := 1) (fun s hs => by have := r.launch s hs; omega) t
      (by omega)
  · rw [r.node v hv t, zdEval_ne net r.g _ hv]
    apply r.local_ v
    intro k a hk hd
    have hlt : a.src < v := hd ▸ (hwf a (List.mem_of_getElem? hk)).1
    simp only [hk, hlt, ↓reduceIte]
    have hhi : a.hi ≤ hmaxL net.arcs := hi_le_hmaxL (List.mem_of_getElem? hk)
    have hm : a.src * hmaxL net.arcs + hmaxL net.arcs ≤ v * hmaxL net.arcs := by
      have := Nat.mul_le_mul_right (hmaxL net.arcs) (show a.src + 1 ≤ v by omega)
      rw [Nat.succ_mul] at this; exact this
    have hset : stableOn (sig a.src) (t - a.hi) t := by
      intro s h1 _
      rw [ih a.src hlt s (by omega), ih a.src hlt (t - a.hi) (by omega)]
    rw [(r.bd k a hk).settle t (by omega) hset]
    exact ih a.src hlt t (by omega)

/-- **A node that is quiet from `t` on holds its zero-delay value at `t`.** -/
theorem settled_of_quiet {net : Netlist} (hwf : net.WF) {sig : Nat → Trace} (r : Run net sig)
    {v t : Nat} (hq : ∀ s, changes (sig v) s → s < t) :
    sig v t = zdEval net r.g (sig 0 1) v := by
  have hc := const_from hq (max t (1 + v * hmaxL net.arcs)) (Nat.le_max_left _ _)
  rw [← hc]
  exact run_settles hwf r v _ (Nat.le_max_right _ _)

/-- Window form: past the late end of its tcheck window a node holds its zero-delay value. -/
theorem settled_of_win {net : Netlist} (hwf : net.WF) {sig : Nat → Trace} (r : Run net sig)
    {v t : Nat} (hw : ∀ e l, winArr net v = some (e, l) → l < t) :
    sig v t = zdEval net r.g (sig 0 1) v := by
  apply settled_of_quiet hwf r
  intro s hs
  obtain ⟨e, l, h, _, h2⟩ := changes_in_winArr hwf r v s hs
  have := hw e l h; omega

/-! ## Per run: tcheck PASS ⇒ data nodes hold their zero-delay values at the request -/

/-- **DAG verdict** (`Tcheck.verdict = decide net.WF && checkArr ..`): once the request node has
changed at `v`, every data node holds its zero-delay value from `v + 1 - setup` on. -/
theorem dag_settled {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat} {setup : Nat}
    (hc : checkArr net req data setup = true) {sig : Nat → Trace} (r : Run net sig)
    {v : Nat} (hv : changes (sig req) v) {d : Nat} (hd : d ∈ data) {t : Nat}
    (ht : v + 1 ≤ t + setup) : sig d t = zdEval net r.g (sig 0 1) d :=
  settled_of_quiet hwf r (fun s hs => by
    have := checkArr_sound hwf hc r d hd s v hs hv; omega)

/-- **Cert verdict** (the four conjuncts of `Tcheck.cverdict`, as in 8w's `held_of_cert`): a
request change of the late-side run at `v` (a target `q`) ⇒ every data node of the data-side
run holds its zero-delay value from `v + 1 - setup` on. -/
theorem cert_settled {dag late : Netlist} (hwf : dag.WF) {pot : Nat → Nat}
    (hpot : potOK late.arcs pot = true) {data targets : List Nat} {setup : Nat}
    (hnz : ∀ q ∈ targets, q ≠ 0)
    (hwin : ∀ d ∈ data, ∀ e l, winArr dag d = some (e, l) → ∀ q ∈ targets, l + setup ≤ pot q)
    {sigD sigL : Nat → Trace} (rD : Run dag sigD) (rL : Run late sigL)
    {q v : Nat} (hq : q ∈ targets) (hv : changes (sigL q) v) {d : Nat} (hd : d ∈ data) {t : Nat}
    (ht : v + 1 ≤ t + setup) : sigD d t = zdEval dag rD.g (sigD 0 1) d := by
  apply settled_of_win hwf rD
  intro e l hw
  have h1 := hwin d hd e l hw q hq
  have h2 := potOK_sound hpot rL v q (hnz q hq) hv
  omega

/-! ## Bus encoding -/

/-- `n` bits, bit `j` = `f j`, as a number. -/
def bv : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => bv n f + (if f n then 2 ^ n else 0)

theorem bv_congr : ∀ (n : Nat) {f f' : Nat → Bool}, (∀ j, j < n → f j = f' j) → bv n f = bv n f'
  | 0, _, _, _ => rfl
  | n + 1, f, f', h => by
    simp only [bv]
    rw [bv_congr n (fun j hj => h j (by omega)), h n (by omega)]

/-! ## Per channel, many transactions -/

/-- Transaction `k` occurs on `P`: the channel makes a `k`-th offer (0-based) at some time. -/
def HasOff (P : Chan) (k : Nat) : Prop := ∃ r, OffAt P k r

/-- H_TXWIN for a physical channel `P` and one obligation: `sig k` is the `k`-th transaction's
single-launch run (data nodes `data`, bit `j` of the bus at capture pin `data[j]`), `R k v` =
"a request (target) node of run `k` changes at run time `v`".

Indexed by the transactions that OCCUR (audit P12a row 18, 2026-10-31): `idle`/`count` are
demanded only for `k` with a `k`-th offer (`HasOff P k`), and the window of the LAST transaction
is unbounded on the right, and `win` too is demanded only for transactions that occur (its premise only bounds `u` by `τ (k+1)` when a `(k+1)`-th offer
exists). The previous form (`count : ∀ k, ...`) forced infinitely many offers, so no channel of
a terminating run could meet it (`txwin_finite_witness` below shows a one-offer channel does). -/
structure TxWin (P : Chan) (sig : Nat → Nat → Trace) (data : List Nat) (R : Nat → Nat → Prop) where
  τ : Nat → Nat
  idle : ∀ k, HasOff P k → P.req (τ k) = false ∧ P.ack (τ k) = false
  count : ∀ k, HasOff P k → cnt (riseB P.req) (τ k) = k
  reqIn : ∀ k r, OffAt P k r → R k (r - τ k)
  win : ∀ k u, HasOff P k → τ k ≤ u → (HasOff P (k + 1) → u < τ (k + 1)) →
    P.dat u = bv data.length (fun j => sig k (data.getD j 0) (u - τ k))

/-- The zero-delay bus value of transaction `k`. -/
def zdBus {net : Netlist} {sig : Nat → Nat → Trace} (runs : ∀ k, Run net (sig k))
    (data : List Nat) (k : Nat) : Nat :=
  bv data.length (fun j => zdEval net (runs k).g (sig k 0 1) (data.getD j 0))

/-- The offer of transaction `k` lies in `[τ k, τ (k+1))` (no right end for the last one). -/
theorem off_in_win {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat} {R : Nat → Nat → Prop}
    (X : TxWin P sig data R) {k r : Nat} (ho : OffAt P k r) :
    X.τ k ≤ r ∧ (HasOff P (k + 1) → r < X.τ (k + 1)) := by
  have h1 := cnt_succ_of ho.1
  rw [ho.2] at h1
  constructor
  · apply Classical.byContradiction; intro h
    have := cnt_mono (riseB P.req) (show r + 1 ≤ X.τ k by omega)
    rw [h1, X.count k ⟨r, ho⟩] at this; omega
  · intro hn
    apply Classical.byContradiction; intro h
    have := cnt_mono (riseB P.req) (show X.τ (k + 1) ≤ r by omega)
    rw [ho.2, X.count (k + 1) hn] at this; omega

/-- **Sampled value = zero-delay value (generic separation).** If every data change of run `k`
is no later than every request change of run `k` (`hsep`), then at every instant `t` of the
`k`-th transaction (after the offer `r`, the channel busy on `(r, t]`) the physical bus equals
the zero-delay bus value of run `k`. -/
theorem sampled_eq_zd {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    {k r t : Nat} (ho : OffAt P k r) (hrt : r < t)
    (hbusy : ∀ s, r < s → s ≤ t → inTx P s = true) :
    P.dat t = zdBus runs data k := by
  obtain ⟨h1, h2⟩ := off_in_win X ho
  have h3 : HasOff P (k + 1) → t < X.τ (k + 1) := by
    intro hn
    have h2 := h2 hn
    apply Classical.byContradiction; intro h
    have hb := hbusy (X.τ (k + 1)) (by omega) (by omega)
    simp [inTx, (X.idle (k + 1) hn).1, (X.idle (k + 1) hn).2] at hb
  rw [X.win k t ⟨r, ho⟩ (by omega) h3, zdBus]
  apply bv_congr
  intro j hj
  have hd : data.getD j 0 ∈ data := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hR := X.reqIn k r ho
  exact settled_of_quiet hwf (runs k) (fun s hs => by
    have := hsep k _ hR _ hd s hs; omega)

/-- **Latch capture window** (H_LATCH_WINDOW): a capture latch that closes at `tc` with setup
`su` and hold `hd` margins, its whole window `[tc - su, tc + hd]` after the offer and inside
the transaction, sees the zero-delay value, constant, over the whole window. -/
theorem capture_window {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    {k r tc su hd : Nat} (ho : OffAt P k r) (hopen : r < tc - su)
    (hbusy : ∀ s, r < s → s ≤ tc + hd → inTx P s = true) :
    ∀ s, tc - su ≤ s → s ≤ tc + hd → P.dat s = zdBus runs data k :=
  fun s h1 h2 => sampled_eq_zd hwf runs X hsep ho (by omega) (fun u a b => hbusy u a (by omega))

/-! ## The observed channel is bundled (Ops `Held`) -/

/-- Between a launch and the next offer the channel stays idle (receiver rule). -/
theorem idle_until {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat} {R : Nat → Nat → Prop}
    (X : TxWin P sig data R) (hrecv : ∀ t, RecvStep P t) {k r : Nat} (ho : OffAt P k r) :
    ∀ n, X.τ k + n ≤ r → P.req (X.τ k + n) = false ∧ P.ack (X.τ k + n) = false := by
  intro n
  induction n with
  | zero => intro _; exact X.idle k ⟨r, ho⟩
  | succ n ih =>
    intro hn
    obtain ⟨hr, ha⟩ := ih (by omega)
    have hreq : P.req (X.τ k + n + 1) = false := by
      cases hq : P.req (X.τ k + n + 1) with
      | false => rfl
      | true =>
        exfalso
        have hrise : riseB P.req (X.τ k + n) = true := by simp [riseB, hr, hq]
        have := cnt_mono (riseB P.req) (show X.τ k + n + 1 ≤ r by omega)
        rw [cnt_succ_of hrise, ho.2] at this
        have := cnt_mono (riseB P.req) (show X.τ k ≤ X.τ k + n by omega)
        rw [X.count k ⟨r, ho⟩] at this; omega
    refine ⟨hreq, ?_⟩
    cases hq : P.ack (X.τ k + n + 1) with
    | false => rfl
    | true =>
      exfalso
      have := hrecv (X.τ k + n) (by rw [hq, ha]; decide)
      rw [ha, hr] at this; exact this rfl

/-- Every busy instant belongs to a transaction: some offer `r < t` with the channel busy on
`(r, t]`. -/
theorem busy_cover {P : Chan} (hinit : Init P) (hrecv : ∀ t, RecvStep P t) :
    ∀ t, inTx P t = true → ∃ k r, OffAt P k r ∧ r < t ∧ ∀ s, r < s → s ≤ t → inTx P s = true := by
  intro t
  induction t with
  | zero => intro h; simp [inTx, hinit.1, hinit.2] at h
  | succ t ih =>
    intro h
    by_cases hb : inTx P t = true
    · obtain ⟨k, r, ho, hr, hs⟩ := ih hb
      refine ⟨k, r, ho, by omega, fun s h1 h2 => ?_⟩
      rcases Nat.lt_or_eq_of_le h2 with h2 | h2
      · exact hs s h1 (by omega)
      · rw [h2]; exact h
    · have hr0 : P.req t = false := by simp [inTx] at hb; exact hb.1
      have ha0 : P.ack t = false := by simp [inTx] at hb; exact hb.2
      have ha1 : P.ack (t + 1) = false := by
        cases hq : P.ack (t + 1) with
        | false => rfl
        | true =>
          exfalso
          have := hrecv t (by rw [hq, ha0]; decide)
          rw [ha0, hr0] at this; exact this rfl
      have hr1 : P.req (t + 1) = true := by simpa [inTx, ha1] using h
      refine ⟨cnt (riseB P.req) t, t, ⟨by simp [riseB, hr0, hr1], rfl⟩, by omega, fun s h1 h2 => ?_⟩
      rw [show s = t + 1 by omega]; exact h

/-- **The observed channel satisfies the Ops H_BUNDLE.** -/
theorem held_of_txwin {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    (hinit : Init P) (hrecv : ∀ t, RecvStep P t) : Held P := by
  intro t h0 h1
  obtain ⟨k, r, ho, hr, hs⟩ := busy_cover hinit hrecv (t + 1) h1
  rcases Nat.lt_or_eq_of_le (show r ≤ t by omega) with hlt | heq
  · rw [sampled_eq_zd hwf runs X hsep ho (by omega) hs,
      sampled_eq_zd hwf runs X hsep ho hlt (fun s a b => hs s a (by omega))]
  · -- the offer is at `t`, but the channel was busy at `t`: impossible after a launch
    exfalso
    subst heq
    obtain ⟨h1', _⟩ := off_in_win X ho
    obtain ⟨hr0, ha0⟩ := idle_until X hrecv ho (r - X.τ k) (by omega)
    rw [show X.τ k + (r - X.τ k) = r by omega] at hr0 ha0
    simp [inTx, hr0, ha0] at h0

/-- **The k-th token's value (Ops convention, `P.dat (r+1)`) is run `k`'s zero-delay bus.** -/
theorem zd_token {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    {k r : Nat} (ho : OffAt P k r) : P.dat (r + 1) = zdBus runs data k := by
  apply sampled_eq_zd hwf runs X hsep ho (by omega)
  intro s h1 h2
  rw [show s = r + 1 by omega]
  have : P.req (r + 1) = true := by
    have h := ho.1; simp only [riseB, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2
  simp [inTx, this]

/-- **The value a latch captures at the close (`ack↓`, `TokAt`) is the zero-delay value**, for a
channel obeying the protocol. -/
theorem zd_close {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    (hp : Protocol P) {k e : Nat} (he : TokAt P k e) : P.dat e = zdBus runs data k := by
  obtain ⟨r, _, ho⟩ := tok_off hp he
  have hh := held_of_txwin hwf runs X hsep hp.1 (fun t => (hp.2 t).2)
  rw [close_val hp hh he ho]
  exact zd_token hwf runs X hsep ho

/-! ## Instantiations with tcheck's verdicts -/

/-- Separation from the DAG verdict. -/
theorem sep_dag {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat} {setup : Nat}
    (hc : checkArr net req data setup = true) {sig : Nat → Nat → Trace}
    (runs : ∀ k, Run net (sig k)) :
    ∀ k v, changes (sig k req) v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v :=
  fun k v hv d hd s hs => by have := checkArr_sound hwf hc (runs k) d hd s v hs hv; omega

/-- **tcheck DAG PASS ⇒ every sample inside a transaction is the zero-delay value.** -/
theorem sampled_eq_zd_dag {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : checkArr net req data setup = true) {P : Chan} {sig : Nat → Nat → Trace}
    (runs : ∀ k, Run net (sig k)) (X : TxWin P sig data (fun k v => changes (sig k req) v))
    {k r t : Nat} (ho : OffAt P k r) (hrt : r < t)
    (hbusy : ∀ s, r < s → s ≤ t → inTx P s = true) : P.dat t = zdBus runs data k :=
  sampled_eq_zd hwf runs X (sep_dag hwf hc runs) ho hrt hbusy

/-- **tcheck DAG PASS ⇒ Ops H_BUNDLE of the observed channel.** -/
theorem held_dag {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : checkArr net req data setup = true) {P : Chan} {sig : Nat → Nat → Trace}
    (runs : ∀ k, Run net (sig k)) (X : TxWin P sig data (fun k v => changes (sig k req) v))
    (hinit : Init P) (hrecv : ∀ t, RecvStep P t) : Held P :=
  held_of_txwin hwf runs X (sep_dag hwf hc runs) hinit hrecv

/-- Separation from the cert verdict (data-side runs `sigD`, late-side runs `sigL`). -/
theorem sep_cert {dag late : Netlist} (hwf : dag.WF) {pot : Nat → Nat}
    (hpot : potOK late.arcs pot = true) {data targets : List Nat} {setup : Nat}
    (hnz : ∀ q ∈ targets, q ≠ 0)
    (hwin : ∀ d ∈ data, ∀ e l, winArr dag d = some (e, l) → ∀ q ∈ targets, l + setup ≤ pot q)
    {sigD sigL : Nat → Nat → Trace} (rD : ∀ k, Run dag (sigD k)) (rL : ∀ k, Run late (sigL k)) :
    ∀ k v, (∃ q ∈ targets, changes (sigL k q) v) → ∀ d ∈ data, ∀ s, changes (sigD k d) s → s ≤ v :=
  fun k v ⟨q, hq, hv⟩ d hd s hs => by
    have hb := potOK_sound hpot (rL k) v q (hnz q hq) hv
    obtain ⟨e, l, hw, _, hul⟩ := changes_in_winArr hwf (rD k) d s hs
    have := hwin d hd e l hw q hq
    omega

/-- **tcheck cert PASS ⇒ every sample inside a transaction is the zero-delay value.** -/
theorem sampled_eq_zd_cert {dag late : Netlist} (hwf : dag.WF) {pot : Nat → Nat}
    (hpot : potOK late.arcs pot = true) {data targets : List Nat} {setup : Nat}
    (hnz : ∀ q ∈ targets, q ≠ 0)
    (hwin : ∀ d ∈ data, ∀ e l, winArr dag d = some (e, l) → ∀ q ∈ targets, l + setup ≤ pot q)
    {P : Chan} {sigD sigL : Nat → Nat → Trace} (rD : ∀ k, Run dag (sigD k))
    (rL : ∀ k, Run late (sigL k))
    (X : TxWin P sigD data (fun k v => ∃ q ∈ targets, changes (sigL k q) v))
    {k r t : Nat} (ho : OffAt P k r) (hrt : r < t)
    (hbusy : ∀ s, r < s → s ≤ t → inTx P s = true) : P.dat t = zdBus rD data k :=
  sampled_eq_zd hwf rD X (sep_cert hwf hpot hnz hwin rD rL) ho hrt hbusy

/-- **tcheck cert PASS ⇒ Ops H_BUNDLE of the observed channel.** -/
theorem held_cert {dag late : Netlist} (hwf : dag.WF) {pot : Nat → Nat}
    (hpot : potOK late.arcs pot = true) {data targets : List Nat} {setup : Nat}
    (hnz : ∀ q ∈ targets, q ≠ 0)
    (hwin : ∀ d ∈ data, ∀ e l, winArr dag d = some (e, l) → ∀ q ∈ targets, l + setup ≤ pot q)
    {P : Chan} {sigD sigL : Nat → Nat → Trace} (rD : ∀ k, Run dag (sigD k))
    (rL : ∀ k, Run late (sigL k))
    (X : TxWin P sigD data (fun k v => ∃ q ∈ targets, changes (sigL k q) v))
    (hinit : Init P) (hrecv : ∀ t, RecvStep P t) : Held P :=
  held_of_txwin hwf rD X (sep_cert hwf hpot hnz hwin rD rL) hinit hrecv

end Formal.Net.CapstoneRefine
