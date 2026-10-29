import Formal.Timing.Checker
import Formal.Net.Ops
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

/-- H_TXWIN for a physical channel `P` and one obligation: `sig k` is the `k`-th transaction's
single-launch run (data nodes `data`, bit `j` of the bus at capture pin `data[j]`), `R k v` =
"a request (target) node of run `k` changes at run time `v`". -/
structure TxWin (P : Chan) (sig : Nat → Nat → Trace) (data : List Nat) (R : Nat → Nat → Prop) where
  τ : Nat → Nat
  idle : ∀ k, P.req (τ k) = false ∧ P.ack (τ k) = false
  count : ∀ k, cnt (riseB P.req) (τ k) = k
  reqIn : ∀ k r, OffAt P k r → R k (r - τ k)
  win : ∀ k u, τ k ≤ u → u < τ (k + 1) →
    P.dat u = bv data.length (fun j => sig k (data.getD j 0) (u - τ k))

/-- The zero-delay bus value of transaction `k`. -/
def zdBus {net : Netlist} {sig : Nat → Nat → Trace} (runs : ∀ k, Run net (sig k))
    (data : List Nat) (k : Nat) : Nat :=
  bv data.length (fun j => zdEval net (runs k).g (sig k 0 1) (data.getD j 0))

/-- The offer of transaction `k` lies in `[τ k, τ (k+1))`. -/
theorem off_in_win {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat} {R : Nat → Nat → Prop}
    (X : TxWin P sig data R) {k r : Nat} (ho : OffAt P k r) : X.τ k ≤ r ∧ r < X.τ (k + 1) := by
  have h1 := cnt_succ_of ho.1
  rw [ho.2] at h1
  constructor
  · apply Classical.byContradiction; intro h
    have := cnt_mono (riseB P.req) (show r + 1 ≤ X.τ k by omega)
    rw [h1, X.count k] at this; omega
  · apply Classical.byContradiction; intro h
    have := cnt_mono (riseB P.req) (show X.τ (k + 1) ≤ r by omega)
    rw [ho.2, X.count (k + 1)] at this; omega

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
  have h3 : t < X.τ (k + 1) := by
    apply Classical.byContradiction; intro h
    have hb := hbusy (X.τ (k + 1)) (by omega) (by omega)
    simp [inTx, (X.idle (k + 1)).1, (X.idle (k + 1)).2] at hb
  rw [X.win k t (by omega) h3, zdBus]
  apply bv_congr
  intro j hj
  have hd : data.getD j 0 ∈ data := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hR := X.reqIn k r ho
  exact settled_of_quiet hwf (runs k) (fun s hs => by
    have := hsep k _ hR _ hd s hs; omega)

/-! ## The observed channel is bundled (Ops `Held`) -/

/-- Between a launch and the next offer the channel stays idle (receiver rule). -/
theorem idle_until {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat} {R : Nat → Nat → Prop}
    (X : TxWin P sig data R) (hrecv : ∀ t, RecvStep P t) {k r : Nat} (ho : OffAt P k r) :
    ∀ n, X.τ k + n ≤ r → P.req (X.τ k + n) = false ∧ P.ack (X.τ k + n) = false := by
  intro n
  induction n with
  | zero => intro _; exact X.idle k
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
        rw [X.count k] at this; omega
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

end Formal.Net.CapstoneRefine
namespace Formal.Net.CapstoneRefine.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine
def bnet : Netlist := ⟨[⟨0, 1, 3, 3⟩, ⟨0, 2, 1, 1⟩]⟩


def bsig : Nat → Trace := fun v t =>
  if v = 0 then decide (1 ≤ t) else if v = 1 then decide (4 ≤ t)
  else if v = 2 then decide (2 ≤ t) else false

def bg : Nat → (Nat → Bool) → Bool := fun v p => if v = 1 then p 0 else if v = 2 then p 1 else false

theorem bshift (d t : Nat) : shift d (bsig 0) t = decide (d + 1 ≤ t) := by
  simp only [shift, bsig, ite_true]
  by_cases h : t < d
  · rw [if_pos h]; simp; omega
  · rw [if_neg h]; simp; omega

def bfrun : FixedRun bnet bsig where
  d := fun i => if i = 0 then 3 else 1
  g := bg
  launch := by
    intro t h
    simp only [changes, bsig, ite_true] at h
    apply Classical.byContradiction; intro h0
    apply h; simp; omega
  range := by
    intro i a h
    match i with
    | 0 => simp [bnet] at h; subst h; decide
    | 1 => simp [bnet] at h; subst h; decide
    | n + 2 => simp [bnet] at h
  local_ := by
    intro v x y h
    simp only [bg]
    by_cases h1 : v = 1
    · subst h1; simp only [ite_true]; exact h 0 ⟨0, 1, 3, 3⟩ rfl rfl
    · by_cases h2 : v = 2
      · subst h2; simp only [ite_true]; exact h 1 ⟨0, 2, 1, 1⟩ rfl rfl
      · simp only [h1, h2, ite_false]
  node := by
    intro v hv t
    have e0 : fixedPin bnet (fun i => if i = 0 then 3 else 1) bsig 0 t = shift 3 (bsig 0) t := rfl
    have e1 : fixedPin bnet (fun i => if i = 0 then 3 else 1) bsig 1 t = shift 1 (bsig 0) t := rfl
    by_cases h1 : v = 1
    · subst h1; simp only [bg, ite_true, e0, bshift]; simp [bsig]
    · by_cases h2 : v = 2
      · subst h2; simp only [bg, e1, bshift]; simp [bsig]
      · simp [bsig, bg, hv, h1, h2]

theorem stale_without_check :
    changes (bsig 2) 1 ∧
      bsig 1 2 = false ∧ zdEval bnet bfrun.toRun.g (bsig 0 1) 1 = true := by
  refine ⟨by simp [changes, bsig], by decide, ?_⟩
  rw [zdEval_ne _ _ _ (by decide)]
  show bg 1 _ = _
  simp only [bg, ite_true]
  rw [zdEval_zero]; rfl

end Formal.Net.CapstoneRefine.Wit
