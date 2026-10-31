-- MUTANT M03_FiniteNet of Formal/Cells/FiniteNet.lean: ag_trunc with H_LUT_POS 0 <= lo (non-strict rule) (must FAIL)
import Formal.Cells.FiniteRuns
import Formal.Cells.AssumeGuaranteeLinks

/-!
# Probe Bfin2 (shard B): a time-indexed assume-guarantee rule, finite and infinite runs alike

Note: `formal/notes/B-finite-net.md`. Bfin (`FiniteRuns`) gave the link class for runs that
finish (`FEnv1`, `FPhysLink`, `gcd_hw_safe_fin_links`), but each link's `FEnv1` was assumed:
Bnet's closure (`AssumeGuarantee.ag_time` over (cell, segment) events timed by the segment's
END) does not apply to a quiet run, whose last segments never end. This file replaces the
event clock by a TIME clock: the guarantee of a cell at time `T` is "its node is correct on
`[0, T)`", its assumption at `T` is "its pins are correct on `[0, T)`", and the strictness
is the LUT's minimum delay: pins correct up to `T` give the node correct up to `T + lo`,
`lo ≥ 1`. A run that goes quiet is then no different from one that does not.

## Assumed / proved / NOT covered

**Proved (generic):**
* `GPhT x c L T`: `x` is a clean step signal on `[0, T)` with edges `c j` for the indices
  `j` in the edge set `L` (`L = (· < n)`: `n` edges, the last phase forever; `L = True`:
  infinitely many). `gph_fin_iff`: for all `T` this is Bfin's `FPhases`; `gph_inf_iff`: Bfb's
  `Phases`. One notion covers both kinds of run.
* `ag_trunc`: the time-indexed assume-guarantee rule (induction on `T`; strict by
  `lo ≥ 1`); `ag_trunc_zero_unsound`, `ag_trunc_zero_cex`: with `lo = 0` the same premises
  prove a false guarantee, on Bnet's two-zero-delay-buffer loop (`x = y = true`);
  `ag_trunc_unit_ok`: the one-tick loop meets the rule.
* `tnode` (a `Win` LUT with H_NO_REVERT carries a truncated clean excitation to its node,
  `T ↦ T + lo`; no spacing hypothesis), `twire` (the same for a wire, `T ↦ T + wl`),
  `tlink_ex`, `tlink` (B's link controller, real `bd_c2n`: pins correct on `[0, T)` give the
  node correct on `[0, T + lo)`; the node's edge set is `LnL`: edge `j` exists iff request
  edge `j` and acknowledge edge `j-1` exist).
* `FChain`: Bnet's chain of links (`ChainData` verbatim) with an edge set per cell, the two
  END cells given by TRUNCATED contracts; `fchain_nodes`, `fchain_reqPin`,
  `fchain_ackPin` (every node and pin clean, by `ag_trunc`), `fchain_env1` (every link's
  `FEnv1` and `Timing1` DERIVED, Bnet's slacks `Es = vl + lo + wl`, `Ea = wl + lo + vl`),
  `fchain_nodes_inf` (the same theorem with every edge set `True` gives Bfb's `Phases`).
* `FInChain`, `fphysLink_of_inChain`, `gcd_hw_safe_fin_chains`: C's `gcd_hw_circuit_safe`
  with `H_CELLS` of every link replaced by `FInChain` (the link sits in a finite-or-infinite
  chain of B's links; its `FEnv1` is derived, not assumed).

**Assumed** (named fields of `FChain`, `FChainT`): every link: B's `Stage`, H_PWR,
H_LUT_POS; every wire: `Wire`; H_RST; H_TIMES (edge times read off the traces, as Bnet);
H_CNT (edge counts read off the pins, the definition `LnL`); the END cells: a truncated
segment contract each (`SRC_SEG`, `SNK_SEG`), their waits (`SRC_WAIT`, `SNK_WAIT`, only
for edges that exist) and edge-time floors (`SRC_T`, `SNK_T`); timing: `Timing1` per
link with the derived slacks, H_WIRE_R. No wire-spacing hypothesis (Bnet's H_RT) is needed.

**NOT covered:** the END contracts are assumptions (on gcd_hw: the chain-end classes of
`AssumeGuaranteeCap.head_classes`/`tail_classes`); the mixed network is in
`FiniteNetMixed`; the witness on C's run `chW` in `FiniteNetWit`. Core Lean only.
-/

namespace Formal.Cells.FiniteNet
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before Stage Timing1 cph τs)
open Formal.Cells.PipeTimed (Vph ex lfind lfind_le lfind_spec lfind_min)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)
open Formal.Cells.FiniteRuns (FPhases FEnv1 FPhysLink fe)
open Formal.Cells.AssumeGuaranteeLinks (ChainData)

/-! ## 1. Truncated step signals -/

/-- **A step signal on `[0, T)`.** `c j` is the `j`-th edge, for the indices in the edge set
`L` (`j ∈ L`: the `j`-th edge exists); `x` is 0 before the first edge (always, if there is
none), `Vph j` from edge `j` to edge `j+1` (forever, if edge `j+1` does not exist); only
instants `< T` are constrained. -/
structure GPhT (x : Nat → Bool) (c : Nat → Nat) (L : Nat → Prop) (T : Nat) : Prop where
  pre : ∀ s, s < T → (¬ L 0 ∨ s < c 0) → x s = false
  ph : ∀ j s, s < T → L j → c j ≤ s → (L (j + 1) → s < c (j + 1)) → x s = Vph j

/-- A step signal at every time. -/
def GPh (x : Nat → Bool) (c : Nat → Nat) (L : Nat → Prop) : Prop := ∀ T, GPhT x c L T

theorem gphT_mono {x : Nat → Bool} {c : Nat → Nat} {L : Nat → Prop} {T T' : Nat}
    (h : GPhT x c L T') (hT : T ≤ T') : GPhT x c L T :=
  ⟨fun s hs h' => h.pre s (by omega) h', fun j s hs a b d => h.ph j s (by omega) a b d⟩

theorem gphT_zero (x : Nat → Bool) (c : Nat → Nat) (L : Nat → Prop) : GPhT x c L 0 :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **Finite runs**: with `L = (· < n)` the notion is Bfin's `FPhases`. -/
theorem gph_fin_iff {x : Nat → Bool} {c : Nat → Nat} {n : Nat} :
    GPh x c (fun j => j < n) ↔ FPhases x c n := by
  constructor
  · intro h
    refine ⟨fun s hs => (h (s + 1)).pre s (by omega) (by omega), fun j s hj h1 h2 =>
      (h (s + 1)).ph j s (by omega) hj h1 h2⟩
  · intro h T
    exact ⟨fun s _ hs => h.pre s (by omega), fun j s _ hj h1 h2 => h.ph j s hj h1 h2⟩

/-- **Infinite runs**: with `L = True` the notion is Bfb's `Phases`. -/
theorem gph_inf_iff {x : Nat → Bool} {c : Nat → Nat} :
    GPh x c (fun _ => True) ↔ Phases x c := by
  constructor
  · intro h
    exact ⟨fun s hs => (h (s + 1)).pre s (by omega) (Or.inr hs), fun j s h1 h2 =>
      (h (s + 1)).ph j s (by omega) trivial h1 (fun _ => h2)⟩
  · intro h T
    refine ⟨fun s _ hs => ?_, fun j s _ _ h1 h2 => h.ph j s h1 (h2 trivial)⟩
    rcases hs with hs | hs
    · exact absurd trivial hs
    · exact h.pre s hs

/-! ## 2. The time-indexed assume-guarantee rule -/

/-- **The assume-guarantee rule, time-indexed.** `G i T`: cell `i` is correct on `[0, T)`;
`A i T`: its environment (its pins) is correct on `[0, T)`. H_ENV: every assumption at `T`
follows from all guarantees at `T`; H_CELL: a cell whose assumption holds up to `T`
guarantees up to `T + lo i`, with `lo i ≥ 1` (strict causality: the LUT's minimum delay).
No event has to END: the induction is on time, so runs that go quiet are covered. -/
theorem ag_trunc {ι : Type} (G A : ι → Nat → Prop) (lo : ι → Nat)
    (H_LUT_POS : ∀ i, 0 ≤ lo i)
    (H_MONO : ∀ i T T', T ≤ T' → G i T' → G i T)
    (H_BASE : ∀ i, G i 0)
    (H_ENV : ∀ i T, (∀ i', G i' T) → A i T)
    (H_CELL : ∀ i T, A i T → G i (T + lo i)) : ∀ i T, G i T := by
  intro i T
  induction T generalizing i with
  | zero => exact H_BASE i
  | succ T ih =>
    exact H_MONO i (T + 1) (T + lo i) (by have := H_LUT_POS i; omega) (H_CELL i T (H_ENV i T ih))

open Formal.Cells.AssumeGuarantee (Low)

/-- **With `lo = 0` the rule is unsound**: on the trace `true`, "low on `[0, T)`" satisfies
every premise (monotone, base, environment, cell with `T + 0`), and is false at `T = 1`. -/
theorem ag_trunc_zero_unsound :
    ∃ (G A : Bool → Nat → Prop),
      (∀ i T T', T ≤ T' → G i T' → G i T) ∧ (∀ i, G i 0) ∧
      (∀ i T, (∀ i', G i' T) → A i T) ∧ (∀ i T, A i T → G i (T + 0)) ∧
      ¬ (∀ i T, G i T) := by
  refine ⟨fun _ => Low (fun _ => true), fun _ => Low (fun _ => true),
    fun _ T T' h hl t ht => hl t (by omega), fun _ t ht => absurd ht (Nat.not_lt_zero _),
    fun _ T h => h true, fun _ T h => h, fun h => ?_⟩
  have := h true 1 0 (by decide); simp at this

/-- **The circuit form (Bnet's `zero_delay_cex`, truncated)**: two zero-delay buffers in a
loop, `x = y`, `y = x`, on `x = y = true`. Each meets its truncated contract with delay 0
("input low on `[0, T)` gives output low on `[0, T + 0)`"), and `x` is not low. -/
theorem ag_trunc_zero_cex :
    ∃ x y : Nat → Bool, (∀ t, x t = y t) ∧ (∀ t, y t = x t) ∧
      (∀ T, Low y T → Low x (T + 0)) ∧ (∀ T, Low x T → Low y (T + 0)) ∧
      (∀ i : Bool, (if i then Low y 0 else Low x 0)) ∧ ¬ (∀ T, Low x T) := by
  refine ⟨fun _ => true, fun _ => true, fun _ => rfl, fun _ => rfl, fun T h => h,
    fun T h => h, fun i => ?_, fun h => ?_⟩
  · cases i <;> (intro t ht; omega)
  · have := h 1 0 (by decide); simp at this

/-- **The one-tick loop meets the rule** (`lo = 1`), which proves both wires low forever. -/
theorem ag_trunc_unit_ok (x y : Nat → Bool) (hx : ∀ t, x (t + 1) = y t)
    (hy : ∀ t, y (t + 1) = x t) (hx0 : x 0 = false) (hy0 : y 0 = false) :
    ∀ t, x t = false ∧ y t = false := by
  have r := ag_trunc (ι := Bool) (fun i => if i then Low y else Low x)
    (fun i => if i then Low x else Low y) (fun _ => 1) (fun _ => Nat.le_refl 1)
    (fun i T T' h hl => by cases i <;> exact fun t ht => hl t (by omega))
    (fun i => by cases i <;> (intro t ht; omega))
    (fun i n h => by cases i; exact h true; exact h false)
    (fun i n h => by
      cases i
      · intro t ht
        cases t with
        | zero => exact hx0
        | succ t => rw [hx t]; exact h t (by omega)
      · intro t ht
        cases t with
        | zero => exact hy0
        | succ t => rw [hy t]; exact h t (by omega))
  exact fun t => ⟨r false (t + 1) t (by omega), r true (t + 1) t (by omega)⟩

/-! ## 3. Truncated cell lemmas: a `Win` LUT, a wire -/

theorem nt_found {O : Nat → Bool} {lo hi c : Nat} {v : Bool}
    (h : nt O lo hi c v < c + hi + 1) : O (nt O lo hi c v) = v := by
  have hs := lfind_spec (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  exact hs.2

theorem nt_hit {O : Nat → Bool} {lo hi c t : Nat} {v : Bool} (h1 : c + lo ≤ t) (h2 : t ≤ c + hi)
    (hv : O t = v) : nt O lo hi c v ≤ c + hi := by
  apply Classical.byContradiction; intro hn
  have := lfind_min (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) t
    (by unfold nt at hn; omega)
  simp [hv, h1] at this

/-- **A `Win` LUT with H_NO_REVERT, truncated.** If the excitation is a clean step signal on
`[0, T)` (edges `c`, edge set `L`), the node is one on `[0, T + lo)`, with edges
`nt O lo hi (c j) (Vph j)` (read off the node). Only `hi ≤ c j + lo` and H_PWR are needed:
no spacing, no bound on when the run stops. -/
theorem tnode {x O : Nat → Bool} {lo hi T : Nat} {c : Nat → Nat} {L : Nat → Prop}
    (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : GPhT x c L T)
    (hc : ∀ j, L j → hi ≤ c j + lo) (hP : ∀ t, t < hi → O t = false) :
    GPhT O (fe O lo hi c) L (T + lo) := by
  have hlh := win_le hW
  refine ⟨fun s hs h => ?_, fun j s hs hj h1 h2 => ?_⟩
  · by_cases h0 : s < hi
    · exact hP s h0
    · by_cases hq : ¬ L 0 ∨ s < c 0 + lo
      · obtain ⟨u, u1, u2, u3⟩ := hW s (by omega)
        rw [u3]; refine hx.pre u (by omega) ?_
        rcases hq with hq | hq
        · exact Or.inl hq
        · exact Or.inr (by omega)
      · have hL : L 0 := Classical.byContradiction fun h' => hq (Or.inl h')
        have hs' : s < fe O lo hi c 0 := by
          rcases h with h | h
          · exact absurd hL h
          · exact h
        rw [nt_before O lo hi (c 0) (Vph 0) s (by omega) hs', PipeTimed.Vph_even 0]; rfl
  · simp only [fe] at h1 h2
    by_cases hk : L (j + 1) ∧ c (j + 1) + lo ≤ s
    · rw [nt_before O lo hi (c (j + 1)) (Vph (j + 1)) s hk.2 (h2 hk.1), PipeTimed.Vph_succ,
        Bool.not_not]
    · have hcl := nt_lo O (c j) (Vph j) hlh (hi := hi)
      have hcj := hc j hj
      have hseg : ∀ u, c j ≤ u → u < s + 1 - lo → x u = Vph j := fun u a b =>
        hx.ph j u (by omega) hj a (fun h => by
          have : ¬ (c (j + 1) + lo ≤ s) := fun h' => hk ⟨h, h'⟩
          omega)
      have hv : O (nt O lo hi (c j) (Vph j)) = Vph j := by
        by_cases hf : nt O lo hi (c j) (Vph j) < c j + hi + 1
        · exact nt_found hf
        · have := lfind_le (fun t => decide (c j + lo ≤ t) && (O t == Vph j)) (c j + hi + 1)
          have he : nt O lo hi (c j) (Vph j) = c j + hi + 1 := by unfold nt at hf ⊢; omega
          have hcs : c j + hi + 1 ≤ s := by omega
          obtain ⟨u, u1, u2, u3⟩ := hW (c j + hi) (by omega)
          have hv0 : O (c j + hi) = Vph j := by rw [u3]; exact hseg u (by omega) (by omega)
          have := nt_hit (O := O) (lo := lo) (hi := hi) (c := c j) (t := c j + hi) (v := Vph j)
            (by omega) (Nat.le_refl _) hv0
          omega
      exact hN (c j) (s + 1 - lo) (Vph j) _ s hseg (by omega) hcl h1 (by omega) hv

/-- **A wire, truncated**: a node clean on `[0, T)` gives a pin clean on `[0, T + wl)`. -/
theorem twire {wl wh T : Nat} {O P : Nat → Bool} {e : Nat → Nat} {L : Nat → Prop}
    (W : Wire wl wh O P) (hO : GPhT O e L T) (hc : ∀ j, L j → wh ≤ e j + wl) :
    GPhT P (ε P wl wh e) L (T + wl) :=
  tnode W.H_WIN W.H_NO_REVERT hO hc W.H_PWR

/-! ## 4. A link controller, truncated -/

/-- **The node's edge set of a link**: edge `j` exists iff the request's edge `j` exists
and (for `j ≥ 1`) the acknowledge's edge `j - 1`. Finite form: `min nr (na + 1)` edges. -/
def LnL (Lr La : Nat → Prop) (j : Nat) : Prop := Lr j ∧ ∀ i, j = i + 1 → La i

theorem lnL_fin (nr na j : Nat) : LnL (fun j => j < nr) (fun j => j < na) j ↔ j < min nr (na + 1) := by
  unfold LnL
  constructor
  · intro ⟨h1, h2⟩
    cases j with
    | zero => omega
    | succ i => have := h2 i rfl; omega
  · intro h
    exact ⟨by omega, fun i hi => by omega⟩

section link
variable {req ack rst O qp : Nat → Bool} {lo hi wl wh R E T : Nat} {ρ ea : Nat → Nat}
  {Lr La : Nat → Prop}

/-- **The excitation of a link, truncated**: pins clean on `[0, T)` (the request with edges
`ρ`, set `Lr`; the acknowledge with its own edges `ea`, set `La`; phase starts
`α = ash R ea`) give the excitation clean on `[0, T)`, edges `cph ρ α`, set `LnL Lr La`.
The departure bounds are asked only for edges that exist. -/
theorem tlink_ex (S : Stage req ack rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E)
    (H_RST_EARLY : ∀ j, R ≤ ρ j)
    (H_SND : ∀ j, LnL Lr La j → Lr (j + 1) → τs O lo hi ρ (ash R ea) j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, LnL Lr La j → La j → τs O lo hi ρ (ash R ea) j + E ≤ ea j)
    (hr : GPhT req ρ Lr T) (ha : GPhT ack ea La T) :
    GPhT (ex req ack qp rst) (cph ρ (ash R ea)) (LnL Lr La) T := by
  have hlh := win_le S.H_LUT_WIN
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := S.H_FB wh (Nat.le_refl _); omega
  have hpos := S.H_LOOP_POS
  have rlo : ∀ t, R ≤ t → rst t = false := fun t h => by rw [H_RST]; simp; omega
  have cge : ∀ j, R ≤ cph ρ (ash R ea) j := fun j => by
    have := H_RST_EARLY j; unfold cph; omega
  -- the acknowledge, phase by phase (phase `j` = `!Vph j` on `[α j, α (j+1))`)
  have hack : ∀ j s, s < T → LnL Lr La j → ash R ea j ≤ s → (La j → s < ea j) →
      ack s = !Vph j := by
    intro j s hs hj h1 h2
    cases j with
    | zero =>
      rw [ha.pre s hs (by
        by_cases h : La 0
        · exact Or.inr (h2 h)
        · exact Or.inl h), PipeTimed.Vph_even 0]; rfl
    | succ i =>
      rw [ha.ph i s hs (hj.2 i rfl) h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  -- the feedback: `qp s` is the excitation at some `s' ∈ [s - wh - hi, s - wl - lo]`
  have hfb : ∀ s, hi + wh ≤ s → ∃ s', s' + lo + wl ≤ s ∧ s ≤ s' + hi + wh ∧
      qp s = ex req ack qp rst s' := by
    intro s hs
    obtain ⟨u, hu1, hu2, e⟩ := S.H_FB s (by omega)
    obtain ⟨s', q1, q2, q3⟩ := S.H_LUT_WIN u (by omega)
    exact ⟨s', by omega, by omega, by rw [e, q3]⟩
  refine ⟨fun s => ?_, fun j s => ?_⟩
  · induction s using Nat.strongRecOn with
    | _ s ih =>
      intro hs h
      unfold ex; rw [CElemTiming.c2n_eq]
      by_cases hR : s < R
      · rw [H_RST s]; simp [hR]
      · obtain ⟨s', q1, q2, q3⟩ := hfb s (by omega)
        have hq : qp s = false := by
          rw [q3]; refine ih s' (by omega) (by omega) ?_
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        have hrq : req s = false := hr.pre s hs (by
          rcases h with h | h
          · exact Or.inl (fun h' => h ⟨h', fun _ hi => absurd hi (by omega)⟩)
          · have e0 : cph ρ (ash R ea) 0 = max (ρ 0) R := rfl
            exact Or.inr (by omega))
        rw [hrq, hq]; cases rst s <;> cases ack s <;> rfl
  · induction s using Nat.strongRecOn with
    | _ s ih =>
      intro hs hj h1 h2
      have hR := cge j
      have hl := nt_lo O (cph ρ (ash R ea) j) (Vph j) hlh (hi := hi)
      have hr0 : rst s = false := rlo s (by omega)
      unfold ex; rw [CElemTiming.c2n_eq, hr0]
      have hρj : ρ j ≤ s := by unfold cph at h1; omega
      have hαj : ash R ea j ≤ s := by unfold cph at h1; omega
      by_cases hd : Lr (j + 1) ∧ ρ (j + 1) ≤ s
      · -- the request has moved on: the acknowledge has not, the feedback holds `Vph j`
        have hna : ¬ (La j ∧ ea j ≤ s) := fun hb => by
          have := h2 ⟨hd.1, fun i hi => by
            have : i = j := by omega
            subst this; exact hb.1⟩
          have : cph ρ (ash R ea) (j + 1) = max (ρ (j + 1)) (ea j) := rfl
          omega
        have ha' := hack j s hs hj hαj (fun h => by
          apply Classical.byContradiction; intro h'; exact hna ⟨h, by omega⟩)
        have hsnd := H_SND j hj hd.1
        unfold τs at hsnd
        obtain ⟨s', q1, q2, q3⟩ := hfb s (by omega)
        have hq : qp s = Vph j := by
          rw [q3]; exact ih s' (by omega) (by omega) hj (by omega) (fun h => by
            have := h2 h; omega)
        rw [ha', hq]; cases Vph j <;> cases req s <;> rfl
      · have hrq : req s = Vph j := hr.ph j s hs hj.1 hρj (fun h => by
          apply Classical.byContradiction; intro h'; exact hd ⟨h, by omega⟩)
        by_cases hb : La j ∧ ea j ≤ s
        · have hrcv := H_RCV j hj hb.1
          unfold τs at hrcv
          obtain ⟨s', q1, q2, q3⟩ := hfb s (by omega)
          have hq : qp s = Vph j := by
            rw [q3]; exact ih s' (by omega) (by omega) hj (by omega) (fun h => by
              have := h2 h; omega)
          rw [hrq, hq]; cases Vph j <;> cases ack s <;> rfl
        · have ha' := hack j s hs hj hαj (fun h => by
            apply Classical.byContradiction; intro h'; exact hb ⟨h, by omega⟩)
          rw [hrq, ha']; cases Vph j <;> cases qp s <;> rfl

/-- **B's link controller, truncated** (real `bd_c2n`, `Stage`): pins clean on `[0, T)`
give the node clean on `[0, T + lo)`, with edges `τs` and edge set `LnL Lr La`. -/
theorem tlink (S : Stage req ack rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_RST_EARLY : ∀ j, R ≤ ρ j)
    (H_SND : ∀ j, LnL Lr La j → Lr (j + 1) → τs O lo hi ρ (ash R ea) j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, LnL Lr La j → La j → τs O lo hi ρ (ash R ea) j + E ≤ ea j)
    (hr : GPhT req ρ Lr T) (ha : GPhT ack ea La T) :
    GPhT O (τs O lo hi ρ (ash R ea)) (LnL Lr La) (T + lo) :=
  tnode S.H_LUT_WIN S.H_NO_REVERT
    (tlink_ex S H_RST H_RST_LONG H_LAT H_RST_EARLY H_SND H_RCV hr ha)
    (fun j _ => by have := H_RST_EARLY j; unfold cph; omega) H_PWR

end link

/-! ## 5. A chain of links, finite or infinite -/

/-- **The gate relations of a chain (Bnet's `ChainData`), with an edge set `L i` per cell.**
No environment hypothesis on any link. The two END cells are contracts in TRUNCATED form
(their node correct up to `T + lo` if their input pin is correct up to `T`), with their
waits asked only for edges that exist. -/
structure FChain (D : ChainData) (L : Nat → Nat → Prop) : Prop where
  H_RST : ∀ t, D.rst t = decide (t < D.R)
  H_STAGE : ∀ m, m < D.N → Stage (D.req (m + 1)) (D.ack (m + 1)) D.rst (D.O (m + 1))
    (D.qp (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.fl (m + 1)) (D.fh (m + 1))
  H_PWR : ∀ m, m < D.N → ∀ t, t < D.hi (m + 1) → D.O (m + 1) t = false
  /-- **H_LUT_POS** for every cell (for the ends: the minimum wait). -/
  H_LUT_POS : ∀ i, i ≤ D.N + 1 → 1 ≤ D.lo i
  H_WF : ∀ i, i ≤ D.N → Wire (D.wl i) (D.wh i) (D.O i) (D.req (i + 1))
  H_WB : ∀ i, i ≤ D.N → Wire (D.vl i) (D.vh i) (D.O (i + 1)) (D.ack i)
  /-- **H_TIMES** (Bnet's): link edge times read off the node after its pins' phase starts. -/
  H_TIMES : ∀ m, m < D.N → ∀ j, D.τ (m + 1) j =
    τs (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.ρL m) (D.αL m) j
  /-- **H_CNT**: a link's edges exist exactly as its pins' edges allow (`LnL`). -/
  H_CNT : ∀ m, m < D.N → ∀ j, L (m + 1) j ↔ LnL (L m) (L (m + 2)) j
  /-- **Source**: edge-time floor, wait (for existing edges), truncated contract. -/
  SRC_T : ∀ j, D.R ≤ D.τ 0 j + D.wl 0
  SRC_WAIT : ∀ j, L 0 (j + 1) → L 1 j → D.εB 0 j + D.lo 0 ≤ D.τ 0 (j + 1)
  SRC_SEG : ∀ T, GPhT (D.ack 0) (D.εB 0) (L 1) T → GPhT (D.O 0) (D.τ 0) (L 0) (T + D.lo 0)
  /-- **Sink**: edge-time floor, wait (for existing edges), truncated contract. -/
  SNK_T : ∀ j, L (D.N + 1) j → D.vh D.N ≤ D.τ (D.N + 1) j + D.vl D.N
  SNK_WAIT : ∀ j, L (D.N + 1) j → L D.N j → D.εF D.N j + D.lo (D.N + 1) ≤ D.τ (D.N + 1) j
  SNK_SEG : ∀ T, GPhT (D.req (D.N + 1)) (D.εF D.N) (L D.N) T →
    GPhT (D.O (D.N + 1)) (D.τ (D.N + 1)) (L (D.N + 1)) (T + D.lo (D.N + 1))

/-- **Timing of the chain**: B's `Timing1` per link with Bnet's derived `Es`, `Ea`;
H_WIRE_R. (No H_RT: the truncated wire lemma needs no spacing.) -/
structure FChainT (D : ChainData) : Prop where
  H_RST_LONG : ∀ m, m < D.N → D.hi (m + 1) + D.fh (m + 1) ≤ D.R
  H_LAT : ∀ m, m < D.N → D.hi (m + 1) + D.fh (m + 1) ≤ D.lo (m + 1) + min (D.Es m) (D.Ea m)
  H_WIRE_R : ∀ i, i ≤ D.N → D.wh i ≤ D.R ∧ D.vh i ≤ D.R

section chain
variable {D : ChainData} {L : Nat → Nat → Prop} (C : FChain D L) (T : FChainT D)
include C

theorem fc_lh (m : Nat) (hm : m < D.N) : D.lo (m + 1) ≤ D.hi (m + 1) :=
  win_le (C.H_STAGE m hm).H_LUT_WIN

theorem fc_eF (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.τ i j + D.wl i ≤ D.εF i j :=
  ε_lo (C.H_WF i hi) (D.τ i) j

theorem fc_eB (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.τ (i + 1) j + D.vl i ≤ D.εB i j :=
  ε_lo (C.H_WB i hi) (D.τ (i + 1)) j

/-- A link waits for its request pin (unconditional). -/
theorem fc_wF (m : Nat) (hm : m < D.N) (j : Nat) : D.εF m j + D.lo (m + 1) ≤ D.τ (m + 1) j := by
  rw [C.H_TIMES m hm j]
  have := nt_lo (D.O (m + 1)) (cph (D.ρL m) (D.αL m) j) (Vph j) (fc_lh C m hm)
    (hi := D.hi (m + 1))
  have : D.ρL m j ≤ cph (D.ρL m) (D.αL m) j := Nat.le_max_left _ _
  unfold τs; unfold ChainData.ρL at *; omega

/-- A link waits for its acknowledge pin (unconditional). -/
theorem fc_wB (m : Nat) (hm : m < D.N) (j : Nat) :
    D.εB (m + 1) j + D.lo (m + 1) ≤ D.τ (m + 1) (j + 1) := by
  rw [C.H_TIMES m hm (j + 1)]
  have := nt_lo (D.O (m + 1)) (cph (D.ρL m) (D.αL m) (j + 1)) (Vph (j + 1)) (fc_lh C m hm)
    (hi := D.hi (m + 1))
  have : D.αL m (j + 1) ≤ cph (D.ρL m) (D.αL m) (j + 1) := Nat.le_max_right _ _
  have e : D.αL m (j + 1) = D.εB (m + 1) j := rfl
  unfold τs; omega

/-- Every link's phase starts come after reset release (unconditional). -/
theorem fc_geR (m : Nat) (hm : m < D.N) (j : Nat) : D.R ≤ D.ρL m j := by
  induction m with
  | zero => have := fc_eF C 0 (by omega) j; have := C.SRC_T j; unfold ChainData.ρL; omega
  | succ m ih =>
    have := ih (by omega); have := fc_wF C m (by omega) j; have := fc_eF C (m + 1) (by omega) j
    unfold ChainData.ρL at *; omega

theorem fc_cge (m : Nat) (hm : m < D.N) (j : Nat) : D.R ≤ cph (D.ρL m) (D.αL m) j := by
  have := fc_geR C m hm j; unfold cph; omega

theorem fc_linkR (m : Nat) (hm : m < D.N) (j : Nat) : D.R ≤ D.τ (m + 1) j := by
  have := fc_geR C m hm j; have := fc_wF C m hm j; unfold ChainData.ρL at *; omega

/-- Link `m+1`'s H_SND with `Es`, for every node edge `j` followed by a request edge. -/
theorem fc_snd (m : Nat) (hm : m < D.N) (j : Nat) (hj : L (m + 1) j) (hr : L m (j + 1)) :
    D.τ (m + 1) j + D.Es m ≤ D.ρL m (j + 1) := by
  have h1 := fc_eF C m (by omega) (j + 1)
  have h2 := fc_eB C m (by omega) j
  have h3 : D.εB m j + D.lo m ≤ D.τ m (j + 1) := by
    cases m with
    | zero => exact C.SRC_WAIT j hr hj
    | succ k => exact fc_wB C k (by omega) j
  unfold ChainData.Es ChainData.ρL; omega

/-- Link `m+1`'s H_RCV with `Ea`, for every node edge `j` answered by an acknowledge edge. -/
theorem fc_rcv (m : Nat) (hm : m < D.N) (j : Nat) (hj : L (m + 1) j) (ha : L (m + 2) j) :
    D.τ (m + 1) j + D.Ea m ≤ D.εB (m + 1) j := by
  have h1 := fc_eB C (m + 1) (by omega) j
  have h2 := fc_eF C (m + 1) (by omega) j
  have h3 : D.εF (m + 1) j + D.lo (m + 2) ≤ D.τ (m + 2) j := by
    rcases Nat.lt_or_ge (m + 1) D.N with h | h
    · exact fc_wF C (m + 1) h j
    · have e : m + 1 = D.N := by omega
      have := C.SNK_WAIT j (by rw [← e]; exact ha) (by rw [← e]; exact hj)
      rw [← e] at this; exact this
  have e2 : D.τ (m + 1 + 1) j = D.τ (m + 2) j := rfl
  unfold ChainData.Ea; omega

/-- The floor of `twire` for the backward wire into `ack i`. -/
theorem fc_hcB (T : FChainT D) (i : Nat) (hi : i ≤ D.N) (j : Nat) (hj : L (i + 1) j) :
    D.vh i ≤ D.τ (i + 1) j + D.vl i := by
  rcases Nat.lt_or_ge i D.N with h | h
  · have := fc_linkR C i h j; have := (T.H_WIRE_R i hi).2; omega
  · have e : i = D.N := by omega
    subst e; exact C.SNK_T j hj

/-- The floor of `twire` for the forward wire out of cell `i`. -/
theorem fc_hcF (T : FChainT D) (i : Nat) (hi : i ≤ D.N) (j : Nat) :
    D.wh i ≤ D.τ i j + D.wl i := by
  have := (T.H_WIRE_R i hi).1
  cases i with
  | zero => have := C.SRC_T j; omega
  | succ m => have := fc_linkR C m (by omega) j; omega

/-! ### The circle, closed by the time-indexed rule -/

/-- Guarantee of cell `i` at time `T`. -/
def FG (D : ChainData) (L : Nat → Nat → Prop) (i T : Nat) : Prop :=
  i ≤ D.N + 1 → GPhT (D.O i) (D.τ i) (L i) T

/-- Assumption of cell `i` at time `T`: the input pins it reads, on `[0, T)`. -/
def FA (D : ChainData) (L : Nat → Nat → Prop) (i T : Nat) : Prop :=
  (i = 0 → GPhT (D.ack 0) (D.εB 0) (L 1) T) ∧
  (∀ m, i = m + 1 → m < D.N →
    GPhT (D.req (m + 1)) (D.εF m) (L m) T ∧ GPhT (D.ack (m + 1)) (D.εB (m + 1)) (L (m + 2)) T) ∧
  (i = D.N + 1 → GPhT (D.req (D.N + 1)) (D.εF D.N) (L D.N) T)

theorem fchain_env (T : FChainT D) (i Tm : Nat) (ih : ∀ i', FG D L i' Tm) : FA D L i Tm := by
  refine ⟨fun h0 => ?_, fun m hi hm => ⟨?_, ?_⟩, fun hN => ?_⟩
  · exact gphT_mono (twire (C.H_WB 0 (by omega)) (ih 1 (by omega)) (fc_hcB C T 0 (by omega)))
      (by omega)
  · exact gphT_mono (twire (C.H_WF m (by omega)) (ih m (by omega)) (fun j _ => fc_hcF C T m (by omega) j))
      (by omega)
  · exact gphT_mono (twire (C.H_WB (m + 1) (by omega)) (ih (m + 2) (by omega))
      (fc_hcB C T (m + 1) (by omega))) (by omega)
  · exact gphT_mono (twire (C.H_WF D.N (by omega)) (ih D.N (by omega))
      (fun j _ => fc_hcF C T D.N (by omega) j)) (by omega)

theorem fchain_cell (T : FChainT D) (i Tm : Nat) (hA : FA D L i Tm) : FG D L i (Tm + 1) := by
  obtain ⟨a0, a1, a2⟩ := hA
  intro hi
  rcases i with _ | m
  · exact gphT_mono (C.SRC_SEG Tm (a0 rfl)) (by have := C.H_LUT_POS 0 (by omega); omega)
  · rcases Nat.lt_or_ge m D.N with hm | hm
    · obtain ⟨hr, ha⟩ := a1 m rfl hm
      have hL : L (m + 1) = LnL (L m) (L (m + 2)) := funext fun j => propext (C.H_CNT m hm j)
      have hτ : D.τ (m + 1) = τs (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.ρL m)
          (ash D.R (D.εB (m + 1))) := funext (C.H_TIMES m hm)
      have := tlink (E := min (D.Es m) (D.Ea m)) (C.H_STAGE m hm) C.H_RST (T.H_RST_LONG m hm)
        (T.H_LAT m hm) (C.H_PWR m hm) (fc_geR C m hm)
        (fun j hj hr' => by
          rw [← hτ]; have := fc_snd C m hm j (by rw [hL]; exact hj) hr'; omega)
        (fun j hj ha' => by
          rw [← hτ]; have := fc_rcv C m hm j (by rw [hL]; exact hj) ha'; omega) hr ha
      rw [hτ, hL]
      exact gphT_mono this (by have := C.H_LUT_POS (m + 1) (by omega); omega)
    · have e : m = D.N := by omega
      subst e
      exact gphT_mono (C.SNK_SEG Tm (a2 rfl)) (by have := C.H_LUT_POS (D.N + 1) (by omega); omega)

/-- **The circle closed, every node** (time-indexed rule; finite and infinite runs alike). -/
theorem fchain_nodes (T : FChainT D) (i : Nat) (hi : i ≤ D.N + 1) : GPh (D.O i) (D.τ i) (L i) :=
  fun Tm => ag_trunc (FG D L) (FA D L) (fun _ => 1) (fun _ => Nat.le_refl 1)
    (fun _ _ _ h hg hi => gphT_mono (hg hi) h) (fun i _ => gphT_zero _ _ _)
    (fchain_env C T) (fchain_cell C T) i Tm hi

theorem fchain_reqPin (T : FChainT D) (i : Nat) (hi : i ≤ D.N) :
    GPh (D.req (i + 1)) (D.εF i) (L i) :=
  fun Tm => gphT_mono (twire (C.H_WF i hi) (fchain_nodes C T i (by omega) Tm)
    (fun j _ => fc_hcF C T i hi j)) (by omega)

theorem fchain_ackPin (T : FChainT D) (i : Nat) (hi : i ≤ D.N) :
    GPh (D.ack i) (D.εB i) (L (i + 1)) :=
  fun Tm => gphT_mono (twire (C.H_WB i hi) (fchain_nodes C T (i + 1) (by omega) Tm)
    (fc_hcB C T i hi)) (by omega)

/-- **Every link's `FEnv1` and `Timing1`, DERIVED** (finite edge counts `n i`): the request
makes `n m` edges, the acknowledge `n (m+2)`; Bnet's slacks `Es`, `Ea`. -/
theorem fchain_env1 (T : FChainT D) (n : Nat → Nat) (hn : ∀ i j, L i j ↔ j < n i)
    (m : Nat) (hm : m < D.N) :
    FEnv1 (D.req (m + 1)) (D.ack (m + 1)) D.rst (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1))
      D.R (D.ρL m) (D.αL m) (n m) (n (m + 2)) (D.Es m) (D.Ea m) ∧
    Timing1 (D.lo (m + 1)) (D.hi (m + 1)) (D.fh (m + 1)) D.R (D.Es m) (D.Ea m) := by
  have pr := fchain_reqPin C T m (by omega)
  have pa := fchain_ackPin C T (m + 1) (by omega)
  have hL : ∀ i, L i = fun j => j < n i := fun i => funext fun j => propext (hn i j)
  rw [hL] at pr pa
  have pr' := gph_fin_iff.1 pr
  have pa' := gph_fin_iff.1 pa
  have hlnk : ∀ j, j < n m → (∀ i, j = i + 1 → i < n (m + 2)) → L (m + 1) j := fun j h1 h2 =>
    (C.H_CNT m hm j).2 ⟨(hn m j).2 h1, fun i hi => (hn (m + 2) i).2 (h2 i hi)⟩
  refine ⟨{ H_RST := C.H_RST
            H_REQ_LOW0 := fun t _ h => pr'.pre t h
            H_REQ := pr'.ph
            H_ACK0 := rfl
            H_ACK := fun j t hj h1 h2 => ?_
            H_RST_EARLY := fc_geR C m hm 0
            H_SND := fun j h1 h2 => ?_
            H_RCV := fun j h1 h2 => ?_ },
    ⟨?_, T.H_RST_LONG m hm, T.H_LAT m hm⟩⟩
  · cases j with
    | zero => rw [pa'.pre t (by by_cases h : n (m + 2) = 0; exact Or.inl h; exact Or.inr (h2 (by omega)))]; rfl
    | succ k =>
      have : n (m + 1 + 1) = n (m + 2) := rfl
      rw [pa'.ph k t (by omega) h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · rw [← C.H_TIMES m hm j]
    exact fc_snd C m hm j (hlnk j (by omega) (fun i hi => by omega)) ((hn m (j + 1)).2 h1)
  · rw [← C.H_TIMES m hm j]
    exact fc_rcv C m hm j (hlnk j h2 (fun i hi => by omega)) ((hn (m + 2) j).2 h1)
  · have := T.H_RST_LONG m hm; have := fc_lh C m hm; have := C.H_LUT_POS (m + 1) (by omega)
    omega

omit C in
/-- **The same theorem on an INFINITE run** (every edge set `True`): every node is Bfb's
`Phases` (`gph_inf_iff`). -/
theorem fchain_nodes_inf (C' : FChain D (fun _ _ => True)) (T : FChainT D) (i : Nat)
    (hi : i ≤ D.N + 1) : Phases (D.O i) (D.τ i) :=
  gph_inf_iff.1 (fchain_nodes C' T i hi)

end chain

/-! ## 6. gcd_hw: every link in a chain, finite runs -/

open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink isLink_eq)

/-- **B's physical model of a link INSIDE A CHAIN, finite run** (Bnet's `InChain` with
`FChain`): the link is cell `m+1` of a chain whose edge sets are finite counts `n i` and
whose pins at this link ARE C's channel traces; plus H_WIRE_SPREAD for its two outgoing
wires and the latch data fields (as `FPhysLink`). -/
def FInChainC (ci co : Chan) : Prop :=
  ∃ (D : ChainData) (L : Nat → Nat → Prop) (n : Nat → Nat) (m : Nat), m < D.N ∧ FChain D L ∧
    FChainT D ∧ (∀ i j, L i j ↔ j < n i) ∧
    D.req (m + 1) = ci.req ∧ D.ack (m + 1) = co.ack ∧
    D.ack m = ci.ack ∧ D.req (m + 2) = co.req ∧
    D.vh m + D.hi (m + 1) ≤ 2 * D.lo (m + 1) + min (D.Es m) (D.Ea m) ∧
    D.wh (m + 1) + D.hi (m + 1) ≤ 2 * D.lo (m + 1) + min (D.Es m) (D.Ea m) ∧
    (∀ t, D.O (m + 1) t = true → co.dat t = ci.dat t) ∧
    (∀ t, D.O (m + 1) (t + 1) = false → co.dat (t + 1) = co.dat t)

/-- `FInChainC` on C's channels `i` (input) and `o` (output). -/
def FInChain (ch : Fin NC → Chan) (i o : Fin NC) : Prop := FInChainC (ch i) (ch o)

/-- **`FPhysLink` (with its `FEnv1`) from the chain** (`fchain_env1`). -/
theorem fphysLink_of_inChain {ci co : Chan} (h : FInChainC ci co) :
    FPhysLink ci co := by
  obtain ⟨D, L, n, m, hm, C, T, hn, e1, e2, e3, e4, s1, s2, d1, d2⟩ := h
  obtain ⟨E, Tm⟩ := fchain_env1 C T n hn m hm
  have St := C.H_STAGE m hm
  have Wa := C.H_WB m (by omega)
  have Wr := C.H_WF (m + 1) (by omega)
  rw [e1, e2] at St E
  rw [e3] at Wa
  rw [e4] at Wr
  exact ⟨D.rst, D.O (m + 1), D.qp (m + 1), D.lo (m + 1), D.hi (m + 1), D.fl (m + 1),
    D.fh (m + 1), D.R, D.Es m, D.Ea m, D.vl m, D.vh m, D.wl (m + 1), D.wh (m + 1), n m,
    n (m + 2), D.ρL m, D.αL m, St, E, Tm, C.H_LUT_POS (m + 1) (by omega), C.H_PWR m hm, Wa, Wr,
    (T.H_WIRE_R m (by omega)).2, (T.H_WIRE_R (m + 1) (by omega)).1, s1, s2, d1, d2⟩

/-- **End to end, finite runs, no link environment assumed.** C's gcd_hw circuit safety
(`gcd_hw_circuit_safe`, via Bfin's `gcd_hw_safe_fin_links`), with `H_CELLS` of all 175
links replaced by `FInChain`: each link sits in a chain of B's links (finite edge counts)
whose `FEnv1` is DERIVED by the time-indexed rule (`fchain_env1`). Still assumed: inside
`FInChain`, each chain's two truncated end contracts; outside, C's `H_CELLS` of the 192
other operators, H_BUNDLE, H_CM_FORCED. -/
theorem gcd_hw_safe_fin_chains (a b : Nat) (ch : Fin NC → Chan)
    (H_LINKS : ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FInChain ch i o')
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  FiniteRuns.gcd_hw_safe_fin_links a b ch
    (fun o i o' h => fphysLink_of_inChain (H_LINKS o i o' h)) H_OTHER H_BUNDLE H_CM_FORCED

end Formal.Cells.FiniteNet
