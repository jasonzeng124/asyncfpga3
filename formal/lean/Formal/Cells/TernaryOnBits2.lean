import Formal.Cells.TernaryOnBits
open Formal.Core.LutList

/-!
# Probe Bx2: more scenarios, shared O5/O6 reads, and a certificate generator

Follow-up of Bx (`TernaryOnBits.lean`, imported read-only). Same network
(`TernaryOnBits.circ`: the whole routed `link_arb` netlist of C-11c's four
bitstreams, seeds 1..4, nextpnr sha256 9c732bc6303458df), same run model
(7f's `Run` / `Bounded`).

1. **Generator** (`gen`): certificates for a schedule are computed by a Lean
   definition (Algorithm A with joins to a closed state, then B for `M`
   steps) and checked by Bx's `certB` in the same kernel decision. To run the
   checker on another design: a `PNet` from C's importer, a `Seed` map, a
   `Spec` list and expected logical tables (see the notes).
2. **Two scenarios** (`specs2`, `expTables2`, `cert2_s*`, `txn2`): the A0 fall
   with client 2 waiting (A2 is `x` during AND after the window), and a tie
   followed by a server ack (A1 and A2 both `x`). All four seeds.
3. **Explicit runs** (`dv`, `dRun`): unit gate delay, a FIXED transport delay
   per routed pin, FIFO, kernel-evaluable. With them:
   * `early_ack_latched` / `early_ack_runt`: A0 falls once with client 2
     waiting; with the A0 branch into ua2's site 8 (resp. 6) steps slow and
     every other wire 1 step, A2 rises and stays 1 although A0 = 0 (resp.
     never settles). `slow_pin_s*` names the physical pin.
   * `tie_ack_both`: tie, then server ack: A1 = A2 = 1 for ever.
4. **Shared O5/O6 reads** (`SiteSync`, H_LUT62_SHARED_READ): Bx's universal
   theorems hold unchanged; Bx's contested witness is NOT in the class
   (`bx_witness_overlap`, `bx_witness_not_sync`: it shows g1 = g2 = 1 freshly
   evaluated), and the contested iff is re-proved with a shared-read FIFO
   fixed-delay witness (`contested_sync`). All runs of 3. are shared-read.
-/

namespace Formal.Cells.TernaryOnBits2
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.TernaryPhases Formal.Cells.TernaryOnBits

/-! ## 1. The certificate generator (a definition; no `#eval` needed)

Algorithm A from the previous phase's B result, iterated with a join so the
sequence only rises in the information order; Algorithm B for `M` steps from
it. The result is fed to Bx's `certB`, which CHECKS it (closure, B recomputed,
links, tables), so nothing the generator does is trusted: a wrong or
too-short generator only makes `certB` fail. -/

def joinL (l l' : List K3) : List K3 := List.zipWith K3.join l l'

def fixA (N : Circ) (u : Nat → K3) : Nat → List K3 → List K3
  | 0, l => l
  | m + 1, l =>
    let l' := joinL l (stepL N u l)
    if l' == l then l else fixA N u m l'

def genCerts (N : Circ) (fuel : Nat) : List Spec → List K3 → List (List K3 × List K3)
  | [], _ => []
  | sp :: rest, prev =>
    let s := fixA N (V sp.u) fuel prev
    let r := iterL N (V sp.a) M s
    (s, r) :: genCerts N fuel rest r

/-- Certificates for a whole schedule, from all-`x` power-up. -/
def gen (N : Circ) (sp : List Spec) : List (List K3 × List K3) :=
  genCerts N 8 sp (List.replicate N.size .x)

/-! ## 2. The two missing scenarios as one schedule

Phases 0..8 are Bx's (reset, release, link transaction, client 1: r1 up,
A0 up, r1 down). Then:
* 9  r2 rises while A0 = 1 (client 2 WAITS: q is frozen by A0);
* 10 A0 falls with client 2 waiting (7i's early-ack case);
* 11 A0 rises (the server serves client 2);
* 12 r2 falls; 13 A0 falls (idle, q = 0: client 2 was last);
* 14 r1 and r2 rise in one window (the tie);
* 15 the server acknowledges (A0 rises). -/

open K3 in
def specs2 : List Spec := specs.take 9 ++ [
  -- 9 r2 up while A0 = 1
  ⟨P t f f t f f x f f, P t f f t f f t f f⟩,
  -- 10 A0 down, client 2 waiting
  ⟨P x f f t f f t f f, P f f f t f f t f f⟩,
  -- 11 A0 up
  ⟨P x f f t f f t f f, P t f f t f f t f f⟩,
  -- 12 r2 down
  ⟨P t f f t f f x f f, P t f f t f f f f f⟩,
  -- 13 A0 down
  ⟨P x f f t f f f f f, P f f f t f f f f f⟩,
  -- 14 tie: r1 and r2 up together
  ⟨P f f f t f x x f f, P f f f t f t t f f⟩,
  -- 15 server ack after the tie
  ⟨P x f f t f t t f f, P t f f t f t t f f⟩]

open K3 in
/-- Expected tables for phases 9..15, written from the cell specifications
(q = rst + C(r1,~r2) frozen while A0 = 1; g1 = r1.q, g2 = r2.~q;
R0 = r1.q + r2.~q; A_k = C(g_k, A0)), not from a run. -/
def expTables2 : List (List K3 × List K3) := expTables.take 9 ++ [
  -- r1 r2 a0 rst rq ak d0 d1 d2 | c q0 q1 q2 | A1 A2 q g1 g2 R0
  -- 9: q frozen at 1 by A0, so g2 = r2.~q stays 0: hazard-free
  ([f, x, t, f, f, f, f, t, f,  f, t, f, t,  t, f, t, f, f, f],
   [f, t, t, f, f, f, f, t, f,  f, t, f, t,  t, f, t, f, f, f]),
  -- 10: A0 falls: A1 falls, q resets, g2 and R0 rise, A2 = C(g2, A0) races:
  --     x in A (early ack possible) AND x in B (C(1,0) holds whatever it caught)
  ([f, t, x, f, f, f, f, t, f,  f, t, f, t,  x, x, x, f, x, x],
   [f, t, f, f, f, f, f, t, f,  f, t, f, t,  f, x, f, f, t, t]),
  -- 11: A0 rises: A2 = C(1, 1) = 1 resolves the latched x
  ([f, t, x, f, f, f, f, t, f,  f, t, f, t,  f, x, f, f, t, t],
   [f, t, t, f, f, f, f, t, f,  f, t, f, t,  f, t, f, f, t, t]),
  -- 12: r2 falls
  ([f, x, t, f, f, f, f, t, f,  f, t, f, t,  f, t, f, f, x, x],
   [f, f, t, f, f, f, f, t, f,  f, t, f, t,  f, t, f, f, f, f]),
  -- 13: A0 falls
  ([f, f, x, f, f, f, f, t, f,  f, t, f, t,  f, x, f, f, f, f],
   [f, f, f, f, f, f, f, t, f,  f, t, f, t,  f, f, f, f, f, f]),
  -- 14: tie: q, g1, g2 x for ever; R0 = q + ~q = 1 in B (Kleene LUT); acks 0
  ([x, x, f, f, f, f, f, t, f,  f, t, f, t,  f, f, x, x, x, x],
   [t, t, f, f, f, f, f, t, f,  f, t, f, t,  f, f, x, x, x, t]),
  -- 15: server ack: A_k = C(g_k, 1) latches the x of g_k: BOTH acks x
  ([t, t, x, f, f, f, f, t, f,  f, t, f, t,  x, x, x, x, x, t],
   [t, t, t, f, f, f, f, t, f,  f, t, f, t,  x, x, x, x, x, t])]

/-! ### Scenario theorems (soundness half, all four seeds)

The certificate is the generator's output, checked inside the same kernel
decision (`certB S specs2 (gen ..) expTables2`); about 10 s per seed. -/

theorem cert2_s1 : certB seed1 specs2 (gen (circ seed1.net) specs2) expTables2 = true := by
  decide +kernel
theorem cert2_s2 : certB seed2 specs2 (gen (circ seed2.net) specs2) expTables2 = true := by
  decide +kernel
theorem cert2_s3 : certB seed3 specs2 (gen (circ seed3.net) specs2) expTables2 = true := by
  decide +kernel
theorem cert2_s4 : certB seed4 specs2 (gen (circ seed4.net) specs2) expTables2 = true := by
  decide +kernel

/-- **The two scenarios, every seed (soundness).** Every bounded run of the
whole physical netlist following `specs2` with `TimesOK` times is covered by
`expTables2`: in the A0-fall window with client 2 waiting, A1, A2, q, g2, R0
may move and A2 stays `x` after the window (it latches whatever it caught);
after a tie and a server ack, A1 and A2 are both `x`. -/
theorem txn2 (S : OnNetlist.Seed) (hc : certB S specs2 (gen (circ S.net) specs2) expTables2 = true)
    {v : Nat → Nat → Bool} (R : Run (circ S.net) v) {D W : Nat}
    (hB : Bounded (circ S.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 16)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ S.net) v (build (circ S.net) M ((specs2.zip (gen (circ S.net) specs2)).zip ts))) :
    HoldsT S D W v expTables2 ts :=
  schedule_holds S specs2 _ expTables2 hc R hB ts hlen hT hF

open K3 in
/-- Negative control: claiming that A2 does NOT move when A0 falls with
client 2 waiting (A table of phase 10 with A2 = 0) is refuted. -/
theorem neg_no_early_ack :
    certB seed1 specs2 (gen (circ seed1.net) specs2) (expTables2.set 10
      ([f, t, x, f, f, f, f, t, f,  f, t, f, t,  x, f, x, f, x, x],
       [f, t, f, f, f, f, f, t, f,  f, t, f, t,  f, x, f, f, t, t])) = false := by
  decide +kernel


/-! ## 3. Explicit fixed-delay transport runs

`dv N e L inp c` is the run in which pin `p` of gate `n` reads, at step `k`,
the state of step `k - e n p` (a FIXED transport delay per routed pin), and
every gate takes its LUT value one step later (unit delay). The state is kept
as a history list of the last `L + 1` steps, so the kernel can evaluate it. -/

def stepE (N : Circ) (e : Nat → Nat → Nat) (iv : Nat → Bool) (h : List (List Bool)) : List Bool :=
  (List.range N.size).map (fun n => match N.node n with
    | .input => iv n
    | .gate init pins => lutB init (pinsB (fun p i => (h.getD (e n p) []).getD i false) pins 0))

def hist (N : Circ) (e : Nat → Nat → Nat) (L : Nat) (inp : Nat → Nat → Bool) (c : List Bool) :
    Nat → List (List Bool)
  | 0 => List.replicate (L + 1) c
  | k + 1 => stepE N e (inp (k + 1)) (hist N e L inp c k) :: (hist N e L inp c k).take L

def dv (N : Circ) (e : Nat → Nat → Nat) (L : Nat) (inp : Nat → Nat → Bool) (c : List Bool)
    (k n : Nat) : Bool :=
  ((hist N e L inp c k).headD []).getD n false

section drun
variable (N : Circ) (e : Nat → Nat → Nat) (L : Nat) (inp : Nat → Nat → Bool) (c : List Bool)

theorem hist_get : ∀ k m, m ≤ L →
    (hist N e L inp c k).getD m [] = (hist N e L inp c (k - m)).headD []
  | 0, m, hm => by
    rw [Nat.zero_sub]
    show (List.replicate (L + 1) c).getD m [] = (List.replicate (L + 1) c).headD []
    rw [List.replicate_succ]
    cases m with
    | zero => rfl
    | succ m => simp [List.getD_eq_getElem?_getD, show m < L by omega]
  | k + 1, 0, _ => by simp [hist]
  | k + 1, m + 1, hm => by
    rw [show k + 1 - (m + 1) = k - m by omega, ← hist_get k m (by omega)]
    simp only [hist, List.getD_cons_succ]
    simp [List.getD_eq_getElem?_getD, show m < L by omega]

variable (hN : ∀ n, N.size ≤ n → N.node n = .input) (he : ∀ j p, e j p ≤ L)

include hN he in
theorem dv_gate {k j init : Nat} {pins : List Src} (hj : N.node j = .gate init pins) :
    dv N e L inp c (k + 1) j = lutB init (pinsB (fun p i => dv N e L inp c (k - e j p) i) pins 0) := by
  have hjs : j < N.size := by
    rcases Nat.lt_or_ge j N.size with h | h
    · exact h
    · rw [hN j h] at hj; cases hj
  simp only [dv, hist, List.headD_cons, stepE, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hjs, Option.map_some, Option.getD_some, hj]
  congr 1
  congr 1
  funext p i
  have h := hist_get N e L inp c k (e j p) (he j p)
  rw [List.getD_eq_getElem?_getD] at h
  rw [h]

theorem dv_zero (n : Nat) : dv N e L inp c 0 n = c.getD n false := by
  simp [dv, hist, List.replicate_succ]

theorem dv_input {k n : Nat} (hn : N.node n = .input) (hs : n < N.size) :
    dv N e L inp c (k + 1) n = inp (k + 1) n := by
  simp only [dv, hist, List.headD_cons, stepE, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hs, Option.map_some, Option.getD_some, hn]

theorem dv_ge {k n : Nat} (hs : N.size ≤ n) (hc : c.length ≤ n) : dv N e L inp c k n = false := by
  cases k with
  | zero => rw [dv_zero]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc]
  | succ k =>
    simp only [dv, hist, List.headD_cons, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp [stepE]; exact hs)]; rfl

include hN he in
/-- The fixed-delay run is a 7f `Run` (H_WIRE_CAUSAL, H_GMW_GATE). -/
def dRun : Run N (dv N e L inp c) where
  rd k j p := k - e j p
  rd_le k _ _ := Nat.sub_le k _
  gate _ _ _ _ hj := Or.inr (dv_gate N e L inp c hN he hj)

include hN he in
/-- ... and it is bounded: unit gate delay (`D = 0`), wires at most `L` old. -/
theorem dRun_bounded : Bounded N (dv N e L inp c) (dRun N e L inp c hN he) 0 L where
  wire k j p := by show k ≤ k - e j p + L; have := he j p; omega
  gate k _ _ _ _ hj h := ⟨k + 1, by omega, by omega, by
    rw [dv_gate N e L inp c hN he hj]; exact h k (Nat.le_refl _) (by omega)⟩

/-- Fixed delays are FIFO: read times never go back. -/
theorem dRun_fifo : ∀ k j p, (dRun N e L inp c hN he).rd k j p ≤ (dRun N e L inp c hN he).rd (k + 1) j p := by
  intro k j p; show k - e j p ≤ k + 1 - e j p; omega

theorem hist_shift (t0 T P : Nat) (hc : ∀ t, t0 ≤ t → inp t = inp t0) (hT : t0 ≤ T + 1)
    (hp : hist N e L inp c (T + P) = hist N e L inp c T) :
    ∀ m, hist N e L inp c (T + P + m) = hist N e L inp c (T + m)
  | 0 => hp
  | m + 1 => by
    show stepE N e (inp (T + P + m + 1)) (hist N e L inp c (T + P + m)) ::
        (hist N e L inp c (T + P + m)).take L =
      stepE N e (inp (T + m + 1)) (hist N e L inp c (T + m)) :: (hist N e L inp c (T + m)).take L
    rw [hist_shift t0 T P hc hT hp m, hc (T + P + m + 1) (by omega), hc (T + m + 1) (by omega)]

theorem hist_period (t0 T P : Nat) (hc : ∀ t, t0 ≤ t → inp t = inp t0) (hT : t0 ≤ T + 1)
    (hp : hist N e L inp c (T + P) = hist N e L inp c T) :
    ∀ j r, hist N e L inp c (T + j * P + r) = hist N e L inp c (T + r)
  | 0, r => by simp
  | j + 1, r => by
    rw [show T + (j + 1) * P + r = T + P + (j * P + r) by rw [Nat.succ_mul]; omega,
      hist_shift N e L inp c t0 T P hc hT hp, ← Nat.add_assoc]
    exact hist_period t0 T P hc hT hp j r

/-- Every step of a run that is periodic from `T` shows a state of a step `< T + P`. -/
theorem dv_reduce (t0 T P : Nat) (hP : 0 < P) (hc : ∀ t, t0 ≤ t → inp t = inp t0) (hT : t0 ≤ T + 1)
    (hp : hist N e L inp c (T + P) = hist N e L inp c T) :
    ∀ t, ∃ t', t' < T + P ∧ ∀ n, dv N e L inp c t n = dv N e L inp c t' n := by
  intro t
  rcases Nat.lt_or_ge t (T + P) with h | h
  · exact ⟨t, h, fun _ => rfl⟩
  · obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < P ∧ t = T + j * P + r :=
      ⟨(t - T) / P, (t - T) % P, Nat.mod_lt _ hP, by
        have hd := Nat.div_add_mod (t - T) P; rw [Nat.mul_comm] at hd; omega⟩
    refine ⟨T + r, by omega, fun n => ?_⟩
    simp only [dv]
    rw [hist_period N e L inp c t0 T P hc hT hp]

end drun

section dperiod
variable (N : Circ) (e : Nat → Nat → Nat) (L : Nat) (inp : Nat → Nat → Bool) (c : List Bool)
  (t0 T P : Nat) (hc : ∀ t, t0 ≤ t → inp t = inp t0) (hT : t0 ≤ T + 1)
  (hp : hist N e L inp c (T + P) = hist N e L inp c T)
include hc hT hp

theorem dv_period (j r n : Nat) : dv N e L inp c (T + j * P + r) n = dv N e L inp c (T + r) n := by
  simp only [dv]; rw [hist_period N e L inp c t0 T P hc hT hp]

/-- Period 2 and two different values: the node never settles. -/
theorem dv_never (h2 : P = 2) {n : Nat} (hne : dv N e L inp c T n ≠ dv N e L inp c (T + 1) n) :
    ∀ X b, ∃ t, X ≤ t ∧ dv N e L inp c t n ≠ b := by
  subst h2
  intro X b
  by_cases h : dv N e L inp c T n = b
  · refine ⟨T + X * 2 + 1, by omega, ?_⟩
    rw [dv_period N e L inp c t0 T 2 hc hT hp]; rw [← h]; exact Ne.symm hne
  · refine ⟨T + X * 2 + 0, by omega, ?_⟩
    rw [dv_period N e L inp c t0 T 2 hc hT hp]; exact h

/-- Period 1: the run is constant from `T`. -/
theorem dv_settle (h1 : P = 1) (n : Nat) : ∀ t, T ≤ t → dv N e L inp c t n = dv N e L inp c T n := by
  subst h1
  intro t ht
  have := dv_period N e L inp c t0 T 1 hc hT hp (t - T) 0 n
  rw [show T + (t - T) * 1 + 0 = t by omega] at this
  exact this

end dperiod

/-! ## 4. Shared O5/O6 reads (H_LUT62_SHARED_READ) -/

/-- **H_LUT62_SHARED_READ**: O5 and O6 of one LUT6_2 site see each shared
physical pin A1..A5 at the SAME time (equal read times for pins 0..4 of the
two gate nodes `pidx i .o6`, `pidx i .o5`). Physical fact: the two outputs
are taps of one mux tree behind ONE input buffer per pin; only the last
(A6) stage and the output paths differ. The residual skew after the buffer
(inside the tree, a few ps) is ignored. Test: GLS/board, drive one pin of a
fractured LUT and measure the O5-vs-O6 delta; it must stay below one model
step. This is a restriction of 7f's run class: every theorem that holds for
ALL runs (Bx's reset and transaction theorems, 7f/7i soundness) holds for
these runs unchanged; only witnesses (existential statements) must be
rebuilt. -/
def SiteSync (N : PNet) {v : Nat → Nat → Bool} (R : Run (circ N) v) : Prop :=
  ∀ k i p, p < 5 → R.rd k (pidx i .o6) p = R.rd k (pidx i .o5) p

theorem site_o6 (i : Nat) : (pidx i .o6 - 9) / 2 = i := by simp only [pidx]; omega
theorem site_o5 (i : Nat) : (pidx i .o5 - 9) / 2 = i := by simp only [pidx]; omega
theorem pidx_ge (i : Nat) (o : LOut) : 9 ≤ pidx i o := by cases o <;> simp only [pidx] <;> omega

/-- A delay that depends only on the SITE `(j - 9) / 2` and the pin index
gives a run with shared O5/O6 reads. -/
theorem sync_of_site (N : PNet) (e : Nat → Nat → Nat) (L : Nat) (inp : Nat → Nat → Bool)
    (c : List Bool) (hN : ∀ n, (circ N).size ≤ n → (circ N).node n = .input)
    (he : ∀ j p, e j p ≤ L)
    (hs : ∀ i p, e (pidx i .o6) p = e (pidx i .o5) p) :
    SiteSync N (dRun (circ N) e L inp c hN he) := by
  intro k i p _
  show k - e (pidx i .o6) p = k - e (pidx i .o5) p
  rw [hs]

theorem circ_input_cases (N : PNet) {i : Nat} (h : (circ N).node i = .input) :
    i < 9 ∨ (circ N).size ≤ i := by
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · exact Or.inl h9
  · rcases Nat.lt_or_ge i (circ N).size with hs | hs
    · obtain ⟨_, _, hg⟩ := circ_gate N i h9 hs
      rw [hg] at h; cases h
    · exact Or.inr hs

theorem size_ge9 (N : PNet) : 9 ≤ (circ N).size := by simp only [circ]; omega

theorem aF_ge {i : Nat} (h : 9 ≤ i) : aF i = false := by
  simp only [aF, aC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem c0f_ge {c : List Bool} {i : Nat} (h : c.length ≤ i) : c0f c i = false := by
  simp [c0f, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-! ### 4a. The contested witness rebuilt with shared reads

Bx's contested witness is 7l's `wv`, whose reads are chosen per (gate, pin),
so O5 (g1) and O6 (g2) of the grant site may see different `q`. Here: EVERY
routed pin has delay exactly 1 step, every gate delay exactly 1 step; r2
rises at step 1 and r1 at step 2 (a one-step input skew, each one clean
edge). This run is FIFO, has fixed delays and trivially shared O5/O6 reads,
and q, g1, g2 never settle in it: the transport loop of q carries a 1-step
pulse for ever. It also never shows g1 = g2 = 1 (both grants decode the
same q read). -/

def e1 : Nat → Nat → Nat := fun _ _ => 1

def inpC (c : List Bool) (t i : Nat) : Bool :=
  if t = 0 then c0f c i else if t = 1 ∧ i = 5 then c0f c i else aF i

theorem inpC_const (c : List Bool) : ∀ t, 2 ≤ t → inpC c t = inpC c 2 := by
  intro t ht; funext i; simp only [inpC]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The decided facts of the shared-read contested witness. -/
def syncB (S : OnNetlist.Seed) (c : List Bool) : Bool :=
  let N := circ S.net
  (hist N e1 1 (inpC c) c 7 == hist N e1 1 (inpC c) c 5) &&
  ([phys S .q, phys S .g1, phys S .g2].all
    (fun n => dv N e1 1 (inpC c) c 5 n != dv N e1 1 (inpC c) c 6 n)) &&
  ((List.range 7).all
    (fun t => !(dv N e1 1 (inpC c) c t (phys S .g1) && dv N e1 1 (inpC c) c t (phys S .g2))))

theorem sync_s1 : syncB seed1 idle1 = true := by decide +kernel
theorem sync_s2 : syncB seed2 idle2 = true := by decide +kernel
theorem sync_s3 : syncB seed3 idle3 = true := by decide +kernel
theorem sync_s4 : syncB seed4 idle4 = true := by decide +kernel

section csync
variable (S : OnNetlist.Seed) (cs : List (List K3 × List K3)) (c : List Bool)
  (hc : contestB S cs c = true) (hs : syncB S c = true)

theorem e1_le : ∀ j p, e1 j p ≤ 1 := fun _ _ => Nat.le_refl 1

/-- The shared-read witness run of the contested case. -/
abbrev cv := dv (circ S.net) e1 1 (inpC c) c
abbrev cR := dRun (circ S.net) e1 1 (inpC c) c (circ_ge S.net) e1_le

include hc in
theorem cv_inputs : ∀ t i, (circ S.net).node i = .input →
    K3.admits (V uC i) (cv S c t i) = true ∧ (2 ≤ t → cv S c t i = aF i) := by
  intro t i hi
  have hlen := c_len S cs c hc
  rcases circ_input_cases S.net hi with h9 | hge
  · have hu := c_hu S cs c hc i hi
    have hsz : i < (circ S.net).size := Nat.lt_of_lt_of_le h9 (size_ge9 S.net)
    cases t with
    | zero =>
      refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [cv, dv_zero]; exact hu.1
    | succ t =>
      rw [cv, dv_input _ _ _ _ _ hi hsz]
      refine ⟨?_, fun h2 => ?_⟩
      · simp only [inpC]
        split
        · omega
        · split
          · exact hu.1
          · exact hu.2
      · simp only [inpC]; rw [if_neg (by omega), if_neg (by omega)]
  · have hl : c.length ≤ i := by omega
    rw [cv, dv_ge _ _ _ _ _ hge hl, V_ge (by simp [uC, P]; have := size_ge9 S.net; omega),
      aF_ge (by have := size_ge9 S.net; omega)]
    exact ⟨rfl, fun _ => rfl⟩

include hs in
theorem cv_period : hist (circ S.net) e1 1 (inpC c) c (5 + 2) = hist (circ S.net) e1 1 (inpC c) c 5 := by
  simp only [syncB, Bool.and_eq_true, beq_iff_eq] at hs; exact hs.1.1

include hs in
/-- In the shared-read witness the two grants are never 1 together. -/
theorem cv_excl : ∀ t, ¬ (cv S c t (phys S .g1) = true ∧ cv S c t (phys S .g2) = true) := by
  intro t
  obtain ⟨t', ht', heq⟩ := dv_reduce (circ S.net) e1 1 (inpC c) c 2 5 2 (by decide)
    (inpC_const c) (by decide) (cv_period S c hs) t
  rw [cv, heq, heq]
  have h := hs
  simp only [syncB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 t' ht'
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at this
  rintro ⟨h1, h2⟩
  rcases this with h' | h' <;> simp_all

include hc hs in
/-- **The contested case with shared O5/O6 reads.** Over every physical gate
node `n`: some bounded run with SHARED O5/O6 reads (`SiteSync`), FIFO wires,
inputs inside `uC` and final from step 2 never settles at `n` iff `n` is the
physical q, g1 or g2. Bx's iff survives the restriction; its witness does
not (see `bx_witness_overlap`), so it is rebuilt: fixed delay 1 on every
wire, unit gate delay, r2 one step before r1. -/
theorem contested_sync (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ S.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ S.net) v) (D W : Nat),
        Bounded (circ S.net) v R D W ∧ SiteSync S.net R ∧
        (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ v 0 = c0f c ∧
        (∀ t i, (circ S.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ S.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys S .q ∨ n = phys S .g1 ∨ n = phys S .g2) := by
  constructor
  · rintro ⟨v, R, D, W, hB, _, _, h0, hi, hf, hns⟩
    exact (contested_exact S cs c hc n h9 hn).1 ⟨v, R, D, W, hB, h0, hi, hf, hns⟩
  · intro hq
    refine ⟨cv S c, cR S c, 0, 1, dRun_bounded _ _ _ _ _ _ _,
      sync_of_site S.net e1 1 (inpC c) c _ e1_le (fun _ _ => rfl), dRun_fifo _ _ _ _ _ _ _,
      funext (dv_zero _ _ _ _ _), fun t i hi => (cv_inputs S cs c hc t i hi).1,
      fun t i hi h2 => (cv_inputs S cs c hc t i hi).2 h2, ?_⟩
    have hne : cv S c 5 n ≠ cv S c 6 n := by
      have h := hs
      simp only [syncB, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_nil_iff,
        or_false, bne_iff_ne, ne_eq] at h
      exact h.1.2 n hq
    exact dv_never (circ S.net) e1 1 (inpC c) c 2 5 2 (inpC_const c) (by decide)
      (cv_period S c hs) rfl hne

end csync

theorem contested_sync_s1 (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed1.net).size) :
    (∃ (v : Nat → Nat → Bool) (R : Run (circ seed1.net) v) (D W : Nat),
        Bounded (circ seed1.net) v R D W ∧ SiteSync seed1.net R ∧
        (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ v 0 = c0f idle1 ∧
        (∀ t i, (circ seed1.net).node i = .input → K3.admits (V uC i) (v t i) = true) ∧
        (∀ t i, (circ seed1.net).node i = .input → 2 ≤ t → v t i = aF i) ∧
        ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) ↔
      (n = phys seed1 .q ∨ n = phys seed1 .g1 ∨ n = phys seed1 .g2) :=
  contested_sync seed1 cert1 idle1 contest_s1 sync_s1 n h9 hn

/-! ### 4b. The A0 fall with a waiting client: explicit early-ack runs

Start: the phase-9 state of `specs2` (client 1 done with A1 = 1, client 2
waiting with r2 = 1, A0 = 1, q = 1 frozen by A0); `wB` checks it is binary,
stable, and equal to the B table of phase 9 on all 19 logical nodes. A0
falls at step 1 and stays 0 for ever (the server never acknowledges client
2). Every routed pin has delay 1 step EXCEPT the pin(s) of ua2's site that
read A0 (the A0 fork branch into `ua2 = C(g2, A0)`), which have delay `L`.
* `L = 8`: A2 rises at step 7 and stays 1 for ever: client 2 is
  acknowledged although A0 = 0 (the EARLY ACK, latched).
* `L = 6`: A2 never settles (the 1-step overlap leaves a pulse in ua2's
  feedback loop: the binary shadow of a runt into the C-element).
The chain the branch must lose to is A0 -> ustate (q falls) -> ugrant (g2
rises) -> ua2: 3 gates and 3 unit wires; the A0 branch into ua2 must be
more than about 5 wire-steps slower than the branch into ustate. Both runs
are FIFO with fixed delays and shared O5/O6 reads. -/

/-- Delay `L` on the pins of site `s` that read port 0 (A0), else 1. -/
def eA (N : PNet) (s L : Nat) (j p : Nat) : Nat :=
  if 9 ≤ j ∧ (j - 9) / 2 = s ∧ ((N.luts[s]?).bind (fun Lu => Lu.pins[p]?)) = some (.port 0)
  then L else 1

theorem eA_le (N : PNet) (s L : Nat) (hL : 1 ≤ L) : ∀ j p, eA N s L j p ≤ L := by
  intro j p; unfold eA; split <;> omega

theorem eA_site (N : PNet) (s L : Nat) : ∀ i p, eA N s L (pidx i .o6) p = eA N s L (pidx i .o5) p := by
  intro i p; simp only [eA, site_o6, site_o5, pidx_ge, true_and]

def inpA (c : List Bool) (t i : Nat) : Bool :=
  if t = 0 then c0f c i else if i = 0 then false else c0f c i

theorem inpA_const (c : List Bool) : ∀ t, 1 ≤ t → inpA c t = inpA c 1 := by
  intro t ht; funext i; simp [inpA, show t ≠ 0 by omega]

open K3 in
def wait1 : List Bool := ([t, f, f, t, f, f, t, f, f, f, f, f, t, t, t, t, f, t, t, f, f, f, f] : List K3).map (· == t)
open K3 in
def wait2 : List Bool := ([t, f, f, t, f, f, t, f, f, f, f, f, t, t, t, f, f, t, f, t, t, f, f] : List K3).map (· == t)
open K3 in
def wait3 : List Bool := ([t, f, f, t, f, f, t, f, f, f, f, t, t, f, t, f, f, t, f, t, t, f, f] : List K3).map (· == t)
open K3 in
def wait4 : List Bool := ([t, f, f, t, f, f, t, f, f, f, f, f, t, t, t, t, f, f, f, f, f, t, t] : List K3).map (· == t)

/-- Decided facts of the early-ack runs from start `c`, slow site `s`. -/
def wB (S : OnNetlist.Seed) (c : List Bool) (s : Nat) : Bool :=
  let N := circ S.net
  let a2 := phys S .a2
  decide (c.length = N.size) && stabB N (c0f c) &&
  (logical S (c0K c) == (expTables2.getD 9 ([], [])).2) &&
  decide (a2 = pidx s .o6) &&
  -- L = 8: A2 = 0 up to step 6, 1 from 16 on (the history is constant from 16)
  (hist N (eA S.net s 8) 8 (inpA c) c (16 + 1) == hist N (eA S.net s 8) 8 (inpA c) c 16) &&
  dv N (eA S.net s 8) 8 (inpA c) c 16 a2 &&
  ((List.range 7).all (fun t => !dv N (eA S.net s 8) 8 (inpA c) c t a2)) &&
  -- L = 6: period 2 from 12, A2 differs at 12 and 13
  (hist N (eA S.net s 6) 6 (inpA c) c (12 + 2) == hist N (eA S.net s 6) 6 (inpA c) c 12) &&
  (dv N (eA S.net s 6) 6 (inpA c) c 12 a2 != dv N (eA S.net s 6) 6 (inpA c) c 13 a2)

theorem wB_s1 : wB seed1 wait1 6 = true := by decide +kernel
theorem wB_s2 : wB seed2 wait2 6 = true := by decide +kernel
theorem wB_s3 : wB seed3 wait3 3 = true := by decide +kernel
theorem wB_s4 : wB seed4 wait4 4 = true := by decide +kernel

/-- Which physical pins carry the slow branch: exactly one pin of ua2's
site reads A0. Seed 1: LUT 6 (SLICE_X42Y95), pin A2 (index 1); seed 2:
LUT 6 (SLICE_X42Y92), pin A1; seed 3: LUT 3 (SLICE_X43Y93), pin A2;
seed 4: LUT 4 (SLICE_X43Y91), pin A1. -/
theorem slow_pin_s1 : (List.range 6).filter (fun p => eA seed1.net 6 8 (pidx 6 .o6) p == 8) = [1] := by decide
theorem slow_pin_s2 : (List.range 6).filter (fun p => eA seed2.net 6 8 (pidx 6 .o6) p == 8) = [0] := by decide
theorem slow_pin_s3 : (List.range 6).filter (fun p => eA seed3.net 3 8 (pidx 3 .o6) p == 8) = [1] := by decide
theorem slow_pin_s4 : (List.range 6).filter (fun p => eA seed4.net 4 8 (pidx 4 .o6) p == 8) = [0] := by decide

section eack
variable (S : OnNetlist.Seed) (c : List Bool) (s : Nat) (hw : wB S c s = true)

theorem inpA_ok (L : Nat) (hL : 1 ≤ L) (hlen : c.length = (circ S.net).size) :
    ∀ t i, (circ S.net).node i = .input →
      dv (circ S.net) (eA S.net s L) L (inpA c) c t i = inpA c t i := by
  intro t i hi
  rcases circ_input_cases S.net hi with h9 | hge
  · cases t with
    | zero => rw [dv_zero]; rfl
    | succ t => exact dv_input _ _ _ _ _ hi (Nat.lt_of_lt_of_le h9 (size_ge9 S.net))
  · rw [dv_ge _ _ _ _ _ hge (by omega)]
    simp only [inpA, c0f_ge (show c.length ≤ i by omega)]
    split <;> (try split) <;> rfl

include hw in
theorem wB_len : c.length = (circ S.net).size := by
  simp only [wB, Bool.and_eq_true, decide_eq_true_eq] at hw; exact hw.1.1.1.1.1.1.1.1

include hw in
/-- **Early ack, latched** (A0 fall with client 2 waiting). A bounded run
(unit gate delay, every wire a FIXED transport delay: 8 steps on the A0
branch into ua2's site, 1 step elsewhere), FIFO, with shared O5/O6 reads,
from the stable waiting state, in which A0 falls once at step 1 and never
rises again, and A2 is 0 up to step 6 and 1 from step 16 for ever. -/
theorem early_ack_latched :
    ∃ (v : Nat → Nat → Bool) (R : Run (circ S.net) v),
      Bounded (circ S.net) v R 0 8 ∧ SiteSync S.net R ∧
      (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ (∀ k j p, R.rd k j p = k - eA S.net s 8 j p) ∧
      v 0 = c0f c ∧ (∀ t i, (circ S.net).node i = .input → v t i = inpA c t i) ∧
      (∀ t, t ≤ 6 → v t (phys S .a2) = false) ∧ (∀ t, 16 ≤ t → v t (phys S .a2) = true) := by
  have h := hw
  simp only [wB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  have he := eA_le S.net s 8 (by decide)
  refine ⟨dv (circ S.net) (eA S.net s 8) 8 (inpA c) c,
    dRun (circ S.net) (eA S.net s 8) 8 (inpA c) c (circ_ge S.net) he,
    dRun_bounded _ _ _ _ _ _ _, sync_of_site _ _ _ _ _ _ _ (eA_site S.net s 8),
    dRun_fifo _ _ _ _ _ _ _, fun _ _ _ => rfl, funext (dv_zero _ _ _ _ _),
    inpA_ok S c s 8 (by decide) (wB_len S c s hw), fun t ht => h.1.1.2 t (by omega), ?_⟩
  intro t ht
  rw [dv_settle (circ S.net) (eA S.net s 8) 8 (inpA c) c 1 16 1 (inpA_const c) (by decide)
    h.1.1.1.1.2 rfl _ t ht]
  exact h.1.1.1.2

include hw in
/-- **Early ack, never settling**: the same with 6 steps on the A0 branch
into ua2's site; A2 never settles. -/
theorem early_ack_runt :
    ∃ (v : Nat → Nat → Bool) (R : Run (circ S.net) v),
      Bounded (circ S.net) v R 0 6 ∧ SiteSync S.net R ∧
      (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ (∀ k j p, R.rd k j p = k - eA S.net s 6 j p) ∧
      v 0 = c0f c ∧ (∀ t i, (circ S.net).node i = .input → v t i = inpA c t i) ∧
      ∀ T b, ∃ t, T ≤ t ∧ v t (phys S .a2) ≠ b := by
  have h := hw
  simp only [wB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  have he := eA_le S.net s 6 (by decide)
  exact ⟨dv (circ S.net) (eA S.net s 6) 6 (inpA c) c,
    dRun (circ S.net) (eA S.net s 6) 6 (inpA c) c (circ_ge S.net) he,
    dRun_bounded _ _ _ _ _ _ _, sync_of_site _ _ _ _ _ _ _ (eA_site S.net s 6),
    dRun_fifo _ _ _ _ _ _ _, fun _ _ _ => rfl, funext (dv_zero _ _ _ _ _),
    inpA_ok S c s 6 (by decide) (wB_len S c s hw),
    dv_never (circ S.net) (eA S.net s 6) 6 (inpA c) c 1 12 2 (inpA_const c) (by decide)
      h.1.2 rfl h.2⟩

end eack

/-! ### 4c. The tie followed by a server ack: both acks latch

From Bx's idle state (contested start `c`, checked by `contestB`), r2 rises
at step 1, r1 at step 2 (the shared-read contested witness), and the server
acknowledges at step 10 (A0 rises; R0 has been 1 since step 4). Every wire
has delay 1 step except the pins of the two ack sites (ua1, ua2), which have
delay 2. Then q, g1, g2 never settle and BOTH A1 and A2 are 1 from step 18
for ever: the ternary `x` that the acks latch (`expTables2` phase 15) is
realised as a mutual-exclusion failure. FIFO, fixed delays, shared reads. -/

def eT (S : OnNetlist.Seed) (j _p : Nat) : Nat :=
  if 9 ≤ j ∧ ((j - 9) / 2 = (phys S .a1 - 9) / 2 ∨ (j - 9) / 2 = (phys S .a2 - 9) / 2) then 2 else 1

theorem eT_le (S : OnNetlist.Seed) : ∀ j p, eT S j p ≤ 2 := by
  intro j p; unfold eT; split <;> omega

theorem eT_site (S : OnNetlist.Seed) : ∀ i p, eT S (pidx i .o6) p = eT S (pidx i .o5) p := by
  intro i p; simp only [eT, site_o6, site_o5, pidx_ge, true_and]

def inpT (c : List Bool) (t i : Nat) : Bool :=
  if t = 0 then c0f c i else if t = 1 ∧ i = 5 then c0f c i
  else if i = 0 then decide (10 ≤ t) else aF i

theorem inpT_const (c : List Bool) : ∀ t, 10 ≤ t → inpT c t = inpT c 10 := by
  intro t ht; funext i
  simp [inpT, show t ≠ 0 by omega, show t ≠ 1 by omega, show 10 ≤ t from ht]

def tieB (S : OnNetlist.Seed) (c : List Bool) : Bool :=
  let N := circ S.net
  let v := dv N (eT S) 2 (inpT c) c
  (hist N (eT S) 2 (inpT c) c (18 + 2) == hist N (eT S) 2 (inpT c) c 18) &&
  v 18 (phys S .a1) && v 19 (phys S .a1) && v 18 (phys S .a2) && v 19 (phys S .a2) &&
  ((List.range 10).all (fun t => !v t (phys S .a1) && !v t (phys S .a2))) &&
  ((List.range 6).all (fun k => v (4 + k) (phys S .r0))) &&
  ([phys S .q, phys S .g1, phys S .g2].all (fun n => v 18 n != v 19 n))

theorem tie_s1 : tieB seed1 idle1 = true := by decide +kernel
theorem tie_s2 : tieB seed2 idle2 = true := by decide +kernel
theorem tie_s3 : tieB seed3 idle3 = true := by decide +kernel
theorem tie_s4 : tieB seed4 idle4 = true := by decide +kernel

theorem dv_true2 (N : Circ) (e : Nat → Nat → Nat) (L : Nat) (inp : Nat → Nat → Bool) (c : List Bool)
    (t0 T : Nat) (hc : ∀ t, t0 ≤ t → inp t = inp t0) (hT : t0 ≤ T + 1)
    (hp : hist N e L inp c (T + 2) = hist N e L inp c T) {n : Nat}
    (h0 : dv N e L inp c T n = true) (h1 : dv N e L inp c (T + 1) n = true) :
    ∀ t, T ≤ t → dv N e L inp c t n = true := by
  intro t ht
  have hd := Nat.div_add_mod (t - T) 2
  have hm := Nat.mod_lt (t - T) (show 0 < 2 by decide)
  have : t = T + (t - T) / 2 * 2 + (t - T) % 2 := by rw [Nat.mul_comm] at hd; omega
  rw [this, dv_period N e L inp c t0 T 2 hc hT hp]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
  · rw [show (t - T) % 2 = 0 by omega]; exact h0
  · rw [h]; exact h1

section tie
variable (S : OnNetlist.Seed) (cs : List (List K3 × List K3)) (c : List Bool)
  (hc : contestB S cs c = true) (ht : tieB S c = true)

include hc ht in
/-- **Tie, then server ack: both acks latch.** A bounded FIFO run with
fixed delays (1 step, 2 on the ack sites) and shared O5/O6 reads, from the
idle state: r2 rises at step 1, r1 at step 2, A0 at step 10 (after R0, which
is 1 from step 4); q, g1, g2 never settle, A1 = A2 = 0 before the server's
ack, and A1 = A2 = 1 from step 18 for ever. -/
theorem tie_ack_both :
    ∃ (v : Nat → Nat → Bool) (R : Run (circ S.net) v),
      Bounded (circ S.net) v R 0 2 ∧ SiteSync S.net R ∧
      (∀ k j p, R.rd k j p ≤ R.rd (k + 1) j p) ∧ v 0 = c0f c ∧
      (∀ t i, (circ S.net).node i = .input → v t i = inpT c t i) ∧
      (∀ t, 4 ≤ t → t < 10 → v t (phys S .r0) = true) ∧
      (∀ t, t < 10 → v t (phys S .a1) = false ∧ v t (phys S .a2) = false) ∧
      (∀ t, 18 ≤ t → v t (phys S .a1) = true ∧ v t (phys S .a2) = true) ∧
      (∀ n, (n = phys S .q ∨ n = phys S .g1 ∨ n = phys S .g2) → ∀ T b, ∃ t, T ≤ t ∧ v t n ≠ b) := by
  have h := ht
  simp only [tieB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true', bne_iff_ne, ne_eq, List.mem_cons, List.mem_nil_iff, or_false] at h
  have hlen := c_len S cs c hc
  have hp := h.1.1.1.1.1.1.1
  refine ⟨dv (circ S.net) (eT S) 2 (inpT c) c,
    dRun (circ S.net) (eT S) 2 (inpT c) c (circ_ge S.net) (eT_le S),
    dRun_bounded _ _ _ _ _ _ _, sync_of_site _ _ _ _ _ _ _ (eT_site S),
    dRun_fifo _ _ _ _ _ _ _, funext (dv_zero _ _ _ _ _), ?_, ?_, ?_, ?_, ?_⟩
  · intro t i hi
    rcases circ_input_cases S.net hi with h9 | hge
    · cases t with
      | zero => rw [dv_zero]; rfl
      | succ t => exact dv_input _ _ _ _ _ hi (Nat.lt_of_lt_of_le h9 (size_ge9 S.net))
    · rw [dv_ge _ _ _ _ _ hge (by omega)]
      have h9 : 9 ≤ i := by have := size_ge9 S.net; omega
      simp only [inpT, c0f_ge (show c.length ≤ i by omega), aF_ge h9]
      rw [if_neg (show i ≠ 0 by omega)]
      split <;> (try split) <;> rfl
  · intro t h4 h10
    have := h.1.2 (t - 4) (by omega)
    rwa [show 4 + (t - 4) = t by omega] at this
  · intro t h10; exact h.1.1.2 t h10
  · intro t h18
    exact ⟨dv_true2 _ _ _ _ _ 10 18 (inpT_const c) (by decide) hp h.1.1.1.1.1.1.2
        h.1.1.1.1.1.2 t h18,
      dv_true2 _ _ _ _ _ 10 18 (inpT_const c) (by decide) hp h.1.1.1.1.2 h.1.1.1.2 t h18⟩
  · intro n hn
    exact dv_never _ _ _ _ _ 10 18 2 (inpT_const c) (by decide) hp rfl (h.2 n hn)

end tie

/-! ### 4d. Bx's contested witness is outside the shared-read class

7l's witness `wv` (used by Bx's `contested_exact`) shows the parity of the
step on every `x` node. With q, g1, g2 all `x` after 3 A-steps, it has
g1 = g2 = 0 at step 6 and g1 = g2 = 1 at step 7, so at step 6 BOTH grant
outputs took a fresh LUT value 1. No run with shared O5/O6 reads can do that:
both outputs would decode the same pin reads, and the grant INIT (on the
physical pins, all completions of the tie pins) never gives O5 = O6 = 1. -/

theorem pinsB_take (rv : Nat → Nat → Bool) :
    ∀ (l : List Src) (off m : Nat), pinsB rv (l.take m) off = (pinsB rv l off).take m
  | [], _, _ => by simp [pinsB]
  | _ :: _, _, 0 => by simp [pinsB]
  | a :: l, off, m + 1 => by simp [pinsB, pinsB_take rv l (off + 1) m]

theorem pinsB_congr (rv rv' : Nat → Nat → Bool) :
    ∀ (l : List Src) (off : Nat), (∀ p i, off ≤ p → p < off + l.length → rv p i = rv' p i) →
      pinsB rv l off = pinsB rv' l off
  | [], _, _ => rfl
  | a :: l, off, h => by
    simp only [pinsB]
    congr 1
    · cases a with
      | node i => exact h off i (Nat.le_refl _) (by simp)
      | const b => rfl
    · exact pinsB_congr rv rv' l (off + 1) (fun p i h1 h2 => h p i (by omega) (by simp; omega))

theorem pinsB_adm (rv : Nat → Nat → Bool) :
    ∀ (l : List Src) (off : Nat),
      Pw (fun z b => K3.admits z b = true) (l.map (srcK (fun _ => .x))) (pinsB rv l off)
  | [], _ => Pw.nil
  | a :: l, off => by
    refine Pw.cons ?_ (pinsB_adm rv l (off + 1))
    cases a with
    | node i => rfl
    | const b => cases b <;> rfl

theorem circ_o6 (N : PNet) {i : Nat} {Lu : Formal.Net.Fasm.PLut} (h : N.luts[i]? = some Lu) :
    (circ N).node (pidx i .o6) = .gate Lu.init (Lu.pins.map toSrc) := by
  have e1 : ¬ (9 + 2 * i < 9) := by omega
  have e2 : (9 + 2 * i - 9) / 2 = i := by omega
  have e3 : (9 + 2 * i - 9) % 2 = 0 := by omega
  simp only [circ, pidx, e1, e2, e3, h, ↓reduceIte]

theorem circ_o5 (N : PNet) {i : Nat} {Lu : Formal.Net.Fasm.PLut} (h : N.luts[i]? = some Lu) :
    (circ N).node (pidx i .o5) = .gate (Lu.init % 2 ^ 32) ((Lu.pins.take 5).map toSrc) := by
  have e1 : ¬ (10 + 2 * i < 9) := by omega
  have e2 : (10 + 2 * i - 9) / 2 = i := by omega
  have e3 : ¬ ((10 + 2 * i - 9) % 2 = 0) := by omega
  simp only [circ, pidx, e1, e2, e3, h, ↓reduceIte]

/-- The grant site `s` never gives O5 = O6 = 1 from one pin vector. -/
def exclB (N : PNet) (s : Nat) : Bool :=
  match N.luts[s]? with
  | some Lu => (completions ((Lu.pins.map toSrc).map (srcK (fun _ => .x)))).all
      (fun bs => !(lutB (Lu.init % 2 ^ 32) (bs.take 5) && lutB Lu.init bs))
  | none => false

/-- Decided facts: g1/g2 are O5/O6 of site `s`, `exclB`, and A's result after
3 steps of the contested window is `x` on both. -/
def ovB (S : OnNetlist.Seed) (c : List Bool) (s : Nat) : Bool :=
  decide (phys S .g1 = pidx s .o5) && decide (phys S .g2 = pidx s .o6) && exclB S.net s &&
  (V (iterL (circ S.net) (V uC) 3 (c0K c)) (pidx s .o5) == .x) &&
  (V (iterL (circ S.net) (V uC) 3 (c0K c)) (pidx s .o6) == .x)

theorem ov_s1 : ovB seed1 idle1 5 = true := by decide +kernel
theorem ov_s2 : ovB seed2 idle2 3 = true := by decide +kernel
theorem ov_s3 : ovB seed3 idle3 6 = true := by decide +kernel
theorem ov_s4 : ovB seed4 idle4 5 = true := by decide +kernel

section overlap
variable (S : OnNetlist.Seed) (cs : List (List K3 × List K3)) (c : List Bool) (s : Nat)
  (hc : contestB S cs c = true) (ho : ovB S c s = true)

/-- Bx's witness run. -/
abbrev bxv := TernaryExact.wv (circ S.net) (c0f c) aF (V uC) 3

include ho in
theorem ov_lut : ∃ Lu, S.net.luts[s]? = some Lu := by
  simp only [ovB, Bool.and_eq_true] at ho
  have h := ho.1.1.2
  unfold exclB at h
  split at h
  · next Lu hL => exact ⟨Lu, hL⟩
  · cases h

include hc ho in
/-- **Bx's contested witness shows both grants high**: at step 6 g1 = g2 = 0,
at step 7 g1 = g2 = 1. -/
theorem bx_witness_overlap :
    bxv S c 6 (phys S .g1) = false ∧ bxv S c 7 (phys S .g1) = true ∧
    bxv S c 6 (phys S .g2) = false ∧ bxv S c 7 (phys S .g2) = true := by
  obtain ⟨Lu, hL⟩ := ov_lut S c s ho
  have hs : s < S.net.luts.length := by
    rcases Nat.lt_or_ge s S.net.luts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hL; cases hL
  have h := ho
  simp only [ovB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hg1, hg2⟩, _⟩, hx5⟩, hx6⟩ := h
  have hsz5 : pidx s .o5 < (circ S.net).size := by simp only [pidx, circ]; omega
  have hsz6 : pidx s .o6 < (circ S.net).size := by simp only [pidx, circ]; omega
  have w5 := TernaryExact.A_witness (circ S.net) (c0f c) aF (V uC) 3 3 (Nat.le_refl _)
    (circ_o5 S.net hL) (by rw [c_inner S cs c hc _ hsz5]; exact hx5)
  have w6 := TernaryExact.A_witness (circ S.net) (c0f c) aF (V uC) 3 3 (Nat.le_refl _)
    (circ_o6 S.net hL) (by rw [c_inner S cs c hc _ hsz6]; exact hx6)
  rw [hg1, hg2]
  exact ⟨w5.1, w5.2, w6.1, w6.2⟩

include hc ho in
/-- **No run of Bx's witness has shared O5/O6 reads.** -/
theorem bx_witness_not_sync (R : Run (circ S.net) (bxv S c)) : ¬ SiteSync S.net R := by
  intro hsync
  obtain ⟨Lu, hL⟩ := ov_lut S c s ho
  have hov := bx_witness_overlap S cs c s hc ho
  have h := ho
  simp only [ovB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hg1, hg2⟩, hex⟩, _⟩, _⟩ := h
  rw [hg1, hg2] at hov
  have g5 := R.gate 6 (pidx s .o5) _ _ (circ_o5 S.net hL)
  have g6 := R.gate 6 (pidx s .o6) _ _ (circ_o6 S.net hL)
  rw [hov.2.1, hov.1] at g5
  rw [hov.2.2.2, hov.2.2.1] at g6
  simp only [Bool.true_eq_false, false_or] at g5 g6
  -- the O5 read equals the first five O6 reads
  have e5 : pinsB (fun p i => bxv S c (R.rd 6 (pidx s .o5) p) i) ((Lu.pins.take 5).map toSrc) 0 =
      (pinsB (fun p i => bxv S c (R.rd 6 (pidx s .o6) p) i) (Lu.pins.map toSrc) 0).take 5 := by
    rw [← pinsB_take, ← List.map_take]
    apply pinsB_congr
    intro p i _ hp
    simp only [List.length_map, List.length_take] at hp
    rw [hsync 6 s p (by omega)]
  rw [e5] at g5
  have hm := mem_completions_of_forall2
    (pinsB_adm (fun p i => bxv S c (R.rd 6 (pidx s .o6) p) i) (Lu.pins.map toSrc) 0)
  unfold exclB at hex
  rw [hL] at hex
  simp only [List.all_eq_true] at hex
  have := hex _ hm
  rw [← g5, ← g6] at this
  exact absurd this (by decide)

end overlap

end Formal.Cells.TernaryOnBits2

namespace Formal.Cells.TernaryOnBits2
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.TernaryPhases Formal.Cells.TernaryOnBits

/-! ## 5. Per-seed instances -/

theorem txn2_s1 {v : Nat → Nat → Bool} (R : Run (circ seed1.net) v) {D W : Nat}
    (hB : Bounded (circ seed1.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 16)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed1.net) v
      (build (circ seed1.net) M ((specs2.zip (gen (circ seed1.net) specs2)).zip ts))) :
    HoldsT seed1 D W v expTables2 ts := txn2 seed1 cert2_s1 R hB ts hlen hT hF
theorem txn2_s2 {v : Nat → Nat → Bool} (R : Run (circ seed2.net) v) {D W : Nat}
    (hB : Bounded (circ seed2.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 16)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed2.net) v
      (build (circ seed2.net) M ((specs2.zip (gen (circ seed2.net) specs2)).zip ts))) :
    HoldsT seed2 D W v expTables2 ts := txn2 seed2 cert2_s2 R hB ts hlen hT hF
theorem txn2_s3 {v : Nat → Nat → Bool} (R : Run (circ seed3.net) v) {D W : Nat}
    (hB : Bounded (circ seed3.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 16)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed3.net) v
      (build (circ seed3.net) M ((specs2.zip (gen (circ seed3.net) specs2)).zip ts))) :
    HoldsT seed3 D W v expTables2 ts := txn2 seed3 cert2_s3 R hB ts hlen hT hF
theorem txn2_s4 {v : Nat → Nat → Bool} (R : Run (circ seed4.net) v) {D W : Nat}
    (hB : Bounded (circ seed4.net) v R D W) (ts : List (Nat × Nat)) (hlen : ts.length = 16)
    (hT : TimesOK D W M ts)
    (hF : Follows (circ seed4.net) v
      (build (circ seed4.net) M ((specs2.zip (gen (circ seed4.net) specs2)).zip ts))) :
    HoldsT seed4 D W v expTables2 ts := txn2 seed4 cert2_s4 R hB ts hlen hT hF

/- The remaining instances (decided hypotheses `sync_s*`, `wB_s*`, `tie_s*`,
`ov_s*` plugged into the generic theorems) are checked as `example`s. -/
/-- `contested_sync_s2` -/
example (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed2.net).size) :=
  contested_sync seed2 cert2 idle2 contest_s2 sync_s2 n h9 hn
/-- `contested_sync_s3` -/
example (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed3.net).size) :=
  contested_sync seed3 cert3 idle3 contest_s3 sync_s3 n h9 hn
/-- `contested_sync_s4` -/
example (n : Nat) (h9 : 9 ≤ n) (hn : n < (circ seed4.net).size) :=
  contested_sync seed4 cert4 idle4 contest_s4 sync_s4 n h9 hn

/-- `early_ack_latched_s1` -/
example := early_ack_latched seed1 wait1 6 wB_s1
/-- `early_ack_latched_s2` -/
example := early_ack_latched seed2 wait2 6 wB_s2
/-- `early_ack_latched_s3` -/
example := early_ack_latched seed3 wait3 3 wB_s3
/-- `early_ack_latched_s4` -/
example := early_ack_latched seed4 wait4 4 wB_s4
/-- `early_ack_runt_s1` -/
example := early_ack_runt seed1 wait1 6 wB_s1
/-- `early_ack_runt_s2` -/
example := early_ack_runt seed2 wait2 6 wB_s2
/-- `early_ack_runt_s3` -/
example := early_ack_runt seed3 wait3 3 wB_s3
/-- `early_ack_runt_s4` -/
example := early_ack_runt seed4 wait4 4 wB_s4

/-- `tie_ack_both_s1` -/
example := tie_ack_both seed1 cert1 idle1 contest_s1 tie_s1
/-- `tie_ack_both_s2` -/
example := tie_ack_both seed2 cert2 idle2 contest_s2 tie_s2
/-- `tie_ack_both_s3` -/
example := tie_ack_both seed3 cert3 idle3 contest_s3 tie_s3
/-- `tie_ack_both_s4` -/
example := tie_ack_both seed4 cert4 idle4 contest_s4 tie_s4

/-- `bx_witness_overlap_s1` -/
example := bx_witness_overlap seed1 cert1 idle1 5 contest_s1 ov_s1
/-- `bx_witness_not_sync_s1` -/
example := bx_witness_not_sync seed1 cert1 idle1 5 contest_s1 ov_s1
/-- `bx_witness_not_sync_s2` -/
example := bx_witness_not_sync seed2 cert2 idle2 3 contest_s2 ov_s2
/-- `bx_witness_not_sync_s3` -/
example := bx_witness_not_sync seed3 cert3 idle3 6 contest_s3 ov_s3
/-- `bx_witness_not_sync_s4` -/
example := bx_witness_not_sync seed4 cert4 idle4 5 contest_s4 ov_s4

end Formal.Cells.TernaryOnBits2
