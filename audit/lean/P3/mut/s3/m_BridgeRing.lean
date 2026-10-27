import Formal.Net.Bridge
import Formal.Net.Ring

/-!
# Probe 8d: the ring theorems of probe 9a, for timed traces

`Formal/Net/Ring.lean` proves its results under H_SI (interleavings). Here the
ring is a `Bridge.Net` whose gate `i` is the REAL `bd_c2n`/`bd_c2n_set` LUT in
run mode (`Ring.gate n K false`, i.e. `lutB` of the verbatim INIT), it is
persistent (`Ring.persistent`), so `Bridge` turns every 9a result into a
statement about EVERY timed trace in which each stage is an inertial channel
with any per-stage bounds `[lo i, hi i]` (`lo i ≥ 1`) and forks are isochronic
(H_ISO). The safety/liveness corollaries are stated for the weaker
no-overtaking channels (`TimedF`); an inertial trace gives one by `Timed.toF`. Hypotheses carried: H_RESET_CLEAN (`x 0 = resetState K`), H_ISO,
H_NO_OVERTAKE (`TimedF`; or H_INERTIAL, `Timed`, for the frozen results), H_FB_SETTLED (the feedback pin reads the
node itself: it is inside `gate`).

* `timed_ring_safe`     one loop token (2 wavefronts) at every ps.
* `timed_ring_dead`     N ≤ 2: the ring never moves, from any state.
* `timed_ring_degenerate` K = 0 or K ≥ N: frozen at reset.
* `timed_ring_live`     N ≥ 3, 0 < K < N: in every window `[t, t + max hi)`
                         some stage toggles.
* `timed_ring_every_stage` N ≥ 3: every stage toggles in every window of
                         `(N(N-1)+1)·H` ps, `H ≥ hi i` for all stages.
* `timed_ring_k_tokens` k tokens: if N ≥ 2k+1 the ring never deadlocks.
-/

namespace Formal.Net.Bridge.RingT
open Formal.Net Formal.Net.Bridge

/-- The ring of `tb_ring.v` as a network: gate `i` is the real LUT in run mode. -/
def ringNet (n K : Nat) : Net where
  n := n
  f i s := Ring.gate n K false s i

theorem excited_ring {n K : Nat} {s : State} {i : Nat} :
    Bridge.excited (ringNet n K) s i ↔ Ring.excited n s i :=
  (Ring.excited_gate n K s i).symm

theorem reach_ring {n K : Nat} {s0 s : State} (h : Bridge.Reach (ringNet n K) s0 s) :
    Ring.Reach n s0 s := by
  induction h with
  | refl => exact .refl
  | step i _ he ih => exact Ring.Reach.step i ih (excited_ring.1 he)

theorem run_ring {n K : Nat} : ∀ {L : List Nat} {s : State},
    Bridge.Run (ringNet n K) s L → Ring.Run n s L := by
  intro L
  induction L with
  | nil => intro _ _; trivial
  | cons i L ih => intro s ⟨he, hr⟩; exact ⟨excited_ring.1 he, ih hr⟩

theorem ring_persistent (n K : Nat) (s0 : State) : Persistent (ringNet n K) s0 := by
  intro s _ i j hi hj hij
  by_cases hn : 3 ≤ n
  · exact excited_ring.2 (Ring.persistent hn (excited_ring.1 hi) (excited_ring.1 hj) hij)
  · exact absurd (excited_ring.1 hi) (Ring.dead_of_le_two (by omega) s i)

variable {n K : Nat} {lo hi : Nat → Nat} {x : Nat → State}

/-- **Timed safety.** From a clean reset with `0 < K < N`, `N ≥ 3`, the ring
holds exactly one loop token (two wavefronts) at every ps. -/
theorem timed_ring_safe (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n)
    (hx : TimedF (ringNet n K) hi x) (h0 : x 0 = Ring.resetState K) (t : Nat) :
    Ring.D n (x t) = 2 :=
  Ring.ring_safe hn hK0 hKn (reach_ring (timed_reachF (ring_persistent n K _) hx h0 t))

/-- **N ≤ 2 is dead in time too**, from any initial state. -/
theorem timed_ring_dead (hn : n ≤ 3) (hx : Timed (ringNet n K) lo hi x) (t : Nat) :
    x t = x 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [timed_frozen hx (fun i he => Ring.dead_of_le_two hn _ i (excited_ring.1 he)), ih]

/-- Empty (`K = 0`) or full (`K ≥ N`) rings stay at reset. -/
theorem timed_ring_degenerate (hK : K = 0 ∨ n ≤ K) (hx : Timed (ringNet n K) lo hi x)
    (h0 : x 0 = Ring.resetState K) (t : Nat) : x t = Ring.resetState K := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [timed_frozen hx (fun i he => by
      rw [ih] at he; exact Ring.ring_degenerate_dead hK i (excited_ring.1 he)), ih]

/-- **Timed liveness.** `N ≥ 3`, `0 < K < N`: at every `t` some stage toggles
within its own upper delay bound. -/
theorem timed_ring_live (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n)
    (hx : TimedF (ringNet n K) hi x) (h0 : x 0 = Ring.resetState K) (t : Nat) :
    ∃ i u, i < n ∧ t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i := by
  have hp := ring_persistent n K (Ring.resetState K)
  obtain ⟨i, he⟩ := (Ring.ring_three n K hK0 hKn).2 hn _ (reach_ring (timed_reachF hp hx h0 t))
  obtain ⟨u, h1, h2, h3⟩ := fires_withinF hp hx h0 (excited_ring.2 he)
  exact ⟨i, u, he.1, h1, h2, h3⟩

/-! ## Every stage toggles in a bounded window -/

theorem obs_add {N : Net} (x : Nat → State) (t a : Nat) :
    ∀ b, obs N x t (a + b) = obs N x t a ++ obs N x (t + a) b := by
  intro b
  induction b with
  | zero => simp [obs]
  | succ b ih =>
    show obs N x t (a + b) ++ chg N x (t + (a + b)) = _
    rw [ih]; simp only [obs, List.append_assoc, Nat.add_assoc]

theorem mem_obs {N : Net} {x : Nat → State} {t i : Nat} :
    ∀ {m}, i ∈ obs N x t m ↔ ∃ k, k < m ∧ i ∈ chg N x (t + k) := by
  intro m
  induction m with
  | zero => simp [obs]
  | succ m ih =>
    simp only [obs, List.mem_append, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      by_cases e : k = m
      · subst e; exact Or.inr h
      · exact Or.inl ⟨k, by omega, h⟩

theorem nf_mem : ∀ {L : List Nat} {i : Nat}, 0 < Ring.nf i L → i ∈ L := by
  intro L
  induction L with
  | nil => intro i h; simp [Ring.nf] at h
  | cons j L ih =>
    intro i h
    simp only [Ring.nf] at h
    by_cases e : j = i
    · subst e; exact List.mem_cons_self ..
    · simp [e] at h; exact List.mem_cons_of_mem _ (ih h)

/-- **Every stage toggles in every window of `(N(N-1)+1)·H` ps** (`H` bounds
every stage's upper delay). From `fair_window` of probe 9a: the window holds
at least `N(N-1)+1` SI firings, which is one more than any run that starves a
stage can have. -/
theorem timed_ring_every_stage (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n)
    (hx : TimedF (ringNet n K) hi x) (h0 : x 0 = Ring.resetState K)
    {H : Nat} (hH : ∀ i, hi i ≤ H) (t i : Nat) (hi' : i < n) :
    ∃ u, t ≤ u ∧ u < t + (n * (n - 1) + 1) * H ∧ x (u + 1) i ≠ x u i := by
  have hp := ring_persistent n K (Ring.resetState K)
  -- each block of H ticks holds at least one change
  have block : ∀ t', 0 < (obs (ringNet n K) x t' H).length := by
    intro t'
    obtain ⟨j, u, hj, h1, h2, h3⟩ := timed_ring_live hn hK0 hKn hx h0 t'
    have : j ∈ obs (ringNet n K) x t' H :=
      mem_obs.2 ⟨u - t', by have := hH j; omega, mem_chg.2 ⟨hj, by
        have e : t' + (u - t') = u := by omega
        rw [e]; exact fun h => h3 h.symm⟩⟩
    exact List.length_pos_of_mem this
  have len : ∀ k, k ≤ (obs (ringNet n K) x t (k * H)).length := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      rw [Nat.succ_mul, obs_add, List.length_append]
      have := block (t + k * H); omega
  obtain ⟨hr, _⟩ := timed_runF hp hx h0 t ((n * (n - 1) + 1) * H)
  have hpos := Ring.every_stage_fires hn (run_ring hr)
    (by have := len (n * (n - 1) + 1); omega) i hi'
  obtain ⟨k, hk, hm⟩ := mem_obs.1 (nf_mem hpos)
  exact ⟨t + k, by omega, by omega, fun h => (mem_chg.1 hm).2 h.symm⟩

/-- **k tokens, timed.** From any initial state carrying `k ≥ 1` four-phase
tokens (`D = 2k`) on `N ≥ 2k+1` stages, the timed ring is never stuck:
at every `t` some stage toggles within its upper bound. -/
theorem timed_ring_k_tokens {k : Nat} (hk : 1 ≤ k) (hn : 2 * k + 1 ≤ n)
    (hx : TimedF (ringNet n K) hi x) (hD : Ring.D n (x 0) = 2 * k) (t : Nat) :
    ∃ i u, i < n ∧ t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i := by
  have hp := ring_persistent n K (x 0)
  obtain ⟨i, he⟩ := (Ring.k_tokens n k hk (x 0) hD).2 hn _
    (reach_ring (timed_reachF hp hx rfl t))
  obtain ⟨u, h1, h2, h3⟩ := fires_withinF hp hx rfl (excited_ring.2 he)
  exact ⟨i, u, he.1, h1, h2, h3⟩

/-! ## H_ATOMIC_LUT for the ring's concurrent two-input transition

In the ring, a stage's `a` (`c_{i-1}`) and `b` (`c_{i+1}`) can change
concurrently. When stage `i` is excited its pins are stable (an excited
neighbour would need a wavefront at `i` / none at `i+1`, contradicting
`excited_tok`). When it is not excited and both neighbours are (wavefronts at
`i-1` and `i+1`, none at `i`, `i+2`), then `a = q` and `b = !q`, and both
firings give `(a, b) = (!q, q)`, which excites the stage. So this is the ONLY
concurrent multi-pin change a ring stage ever sees (the feedback pin is
covered by H_FB_SETTLED, single-pin changes by shard B's results). With the Kleene LUT (shard B's `c2nK`, H_KLEENE_LUT), every point of
every monotone path (each pin moves `v → X → !v` at its own time) gives an
output that moves `q → X → !q` and never returns: no dynamic hazard, so the
atomic-gate abstraction `e_i t = f i (x t)` loses nothing on this transition
(the channel sees one edge, possibly through X). -/

open Formal.Cells in
/-- Pin position along its own transition from `v`: `0 = v`, `1 = X`, `2 = !v`. -/
def pos (v : Bool) : Nat → Formal.Cells.K3
  | 0 => Formal.Cells.K3.ofBool v
  | 1 => .x
  | _ => Formal.Cells.K3.ofBool (!v)

open Formal.Cells Formal.Cells.CElemFn in
set_option synthInstance.maxSize 4096 in
theorem ring_lut_two_input_monotone : ∀ q : Bool, ∀ i1, i1 < 3 → ∀ j1, j1 < 3 →
    ∀ i2, i2 < 3 → ∀ j2, j2 < 3 → i1 ≤ i2 → j1 ≤ j2 →
    (c2nK (pos q i1) (pos (!q) j1) (K3.ofBool q) .f ≠ K3.ofBool q →
      c2nK (pos q i2) (pos (!q) j2) (K3.ofBool q) .f ≠ K3.ofBool q) ∧
    (c2nK (pos q i1) (pos (!q) j1) (K3.ofBool q) .f = K3.ofBool (!q) →
      c2nK (pos q i2) (pos (!q) j2) (K3.ofBool q) .f = K3.ofBool (!q)) ∧
    (c2nsetK (pos q i1) (pos (!q) j1) (K3.ofBool q) .f ≠ K3.ofBool q →
      c2nsetK (pos q i2) (pos (!q) j2) (K3.ofBool q) .f ≠ K3.ofBool q) ∧
    (c2nsetK (pos q i1) (pos (!q) j1) (K3.ofBool q) .f = K3.ofBool (!q) →
      c2nsetK (pos q i2) (pos (!q) j2) (K3.ofBool q) .f = K3.ofBool (!q)) := by
  decide

open Formal.Cells Formal.Cells.CElemFn in
/-- Endpoints: before, the stage holds `q`; after, it is excited to `!q`. -/
theorem ring_lut_two_input_ends : ∀ q : Bool,
    c2nK (pos q 0) (pos (!q) 0) (K3.ofBool q) .f = K3.ofBool q ∧
    c2nK (pos q 2) (pos (!q) 2) (K3.ofBool q) .f = K3.ofBool (!q) ∧
    c2nsetK (pos q 0) (pos (!q) 0) (K3.ofBool q) .f = K3.ofBool q ∧
    c2nsetK (pos q 2) (pos (!q) 2) (K3.ofBool q) .f = K3.ofBool (!q) := by
  decide

end Formal.Net.Bridge.RingT
