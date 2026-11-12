import Formal.Cells.LutFbBridge2Env

/-!
# Probe Bfin (shard B): the link class for FINITE (eventually quiet) handshake runs

Note: `formal/notes/B-finite-runs.md`. Self-audit 5 (`SelfAuditB8.physLink_req_alternates`)
found that Bfb2's `PhysLink` (through `WinFifoCausal.Env1`, whose phase sequences `ρ α : ℕ → ℕ`
are infinite) allows only runs in which the link handshakes FOREVER, so
`LutFbBridge2Env.gcd_hw_safe_phys_links` says nothing about a gcd run that finishes and goes
quiet. This file restates the link class with a FINITE environment: the request makes `nr`
edges, the acknowledge `na` edges (any finite numbers, possibly 0), each pin constant after
its last edge, with the SAME per-phase timing as `Env1` (H_SND, H_RCV measured from the
node's own edges), and re-proves the chain `link_lutFb` → `link_of_phys` →
`gcd_hw_safe_phys_links` for it. The witness on C's terminating run `Wit.chW` is in
`FiniteRunsWit`.

## Assumed / proved / NOT covered

**Assumed** (named, per link): B's `Stage` (Win LUT + H_NO_REVERT + Win feedback wire,
H_LOOP_POS), `Timing1` (H_RST_LONG, H_LAT), H_LUT_POS, H_PWR, the two `Wire`s with
H_WIRE_R / H_WIRE_SPREAD and the latch data fields, all VERBATIM as in `PhysLink`; and the
finite environment `FEnv1`: `Env1`'s fields with every phase index bounded by the pin's
edge count (`nr` request edges, `na` acknowledge edges), the last phase of each pin
unbounded (constant forever), H_SND for every request edge that follows a node edge,
H_RCV for every acknowledge edge that follows a node edge.

**Proved:**
* `fnode_steps`, `fchange_at`, `flutFb_of_fphases`, `ffbFirst_of_fphases`: Bfb's generic
  bridge for an excitation with `n` phases (`FPhases`, the last one unbounded): the node
  makes exactly `n` clean edges, one per phase, then is constant; C's `LutFb`/`FbFirst`.
* `fs_phase`, `fs_pre`, `fs_gap`: the single-stage causal argument (`WinFifoCausal`'s
  `s_phase`/`s_pre`/`s_gap`) for `FEnv1`, with `n = min nr (na + 1)` excitation phases.
  The last phase is constant forever whatever the other pin does afterwards
  (a C-element with one pin and its feedback at `v` stays at `v`).
* `flink_lutFb` (finite `link_lutFb`), `flink_guar` (finite `link_guar`), `fwire_di`
  (finite `wire_di`), `link_of_fphys` (finite `link_of_phys`), and
  `gcd_hw_safe_fin_links`: C's `gcd_hw_circuit_safe` with `H_CELLS` of all 175 links
  replaced by `FPhysLink`.
* `fcelG_lutFb` (finite `celG_lutFb`, any `ι`-pin C-element law, `FEnvG`: per-pin edge
  counts `m i`, `n` node edges, some pin never starts phase `n`), `fwire_steps` (finite
  `wire_steps`), `flink_link_env` (finite `link_link_env`: B's request-side and A's
  acknowledge-side `FEnv1` fields across a link-to-link channel from the two finite
  guarantees).

**NOT covered:** the finite forms of the segment lemmas (`link_segK`, `celG_segK`,
`steer_segK`) and of the network closure (`chain_env1`, `net_closed_gen`,
`mixed_closed`), hence of `gcd_hw_safe_chains` / `gcd_hw_safe_net`. The strict-causality
induction (`AssumeGuarantee.ag_time`) is over (cell, segment) events timed by the segment's
END; in a quiet run the LAST segment of every cell has no end, and those last segments
depend on each other (see the note). An infinite run is NOT a special case of `FEnv1`
(the counts are natural numbers): the infinite theorems stay as they are, beside these.
Core Lean only.
-/

namespace Formal.Cells.FiniteRuns
open Formal.Cells
open Formal.Net.Ops.Gen (LutFb FbFirst link_of_gen)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo node_win Stage Timing1 cph τs exc_phase_w
  exc_pre_w)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.LutFbBridge2Env (Wire)

/-! ## 1. Generic: a `Win` LUT on an excitation with finitely many phases -/

/-- **H_EX_CLEAN, finite phase form**: `x` is 0 before `c 0` (always, if `n = 0`), `Vph j`
on `[c j, c (j+1))` for `j + 1 < n`, and `Vph (n-1)` from `c (n-1)` on. -/
structure FPhases (x : Nat → Bool) (c : Nat → Nat) (n : Nat) : Prop where
  pre : ∀ s, (n = 0 ∨ s < c 0) → x s = false
  ph : ∀ j s, j < n → c j ≤ s → (j + 1 < n → s < c (j + 1)) → x s = Vph j

/-- The node's `j`-th edge (as `LutFbBridge.τ`). -/
abbrev fe (O : Nat → Bool) (lo hi : Nat) (c : Nat → Nat) (j : Nat) : Nat :=
  nt O lo hi (c j) (Vph j)

theorem fc_mono {c : Nat → Nat} {n hi : Nat} (hsp : ∀ j, j + 1 < n → c j + hi ≤ c (j + 1)) :
    ∀ i j, i ≤ j → j < n → c i ≤ c j := by
  intro i j h hj
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with h' | h'
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _
    · have := hsp j hj; have := ih h' (by omega); omega

/-- Segments of a finite strictly increasing sequence cover `ℕ` from `e 0` on (the last
segment unbounded). -/
theorem fseg (e : Nat → Nat) : ∀ n, 0 < n → (∀ j, j + 1 < n → e j < e (j + 1)) →
    ∀ m, m < e 0 ∨ ∃ j, j < n ∧ e j ≤ m ∧ (j + 1 < n → m < e (j + 1)) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hm m
    cases n with
    | zero =>
      by_cases h : m < e 0
      · exact Or.inl h
      · exact Or.inr ⟨0, by omega, by omega, fun h => by omega⟩
    | succ n =>
      rcases ih (by omega) (fun j hj => hm j (by omega)) m with h | ⟨j, hj, h1, h2⟩
      · exact Or.inl h
      · by_cases hl : j + 1 < n + 1
        · exact Or.inr ⟨j, by omega, h1, fun _ => h2 hl⟩
        · have hj' : j = n := by omega
          subst hj'
          by_cases h3 : m < e (j + 1)
          · exact Or.inr ⟨j, by omega, h1, fun _ => h3⟩
          · exact Or.inr ⟨j + 1, by omega, by omega, fun h => by omega⟩

section generic
variable {x O qp : Nat → Bool} {lo hi wl wh n : Nat} {c : Nat → Nat}

/-- **The node is a clean step signal with exactly `n` edges** `fe j ∈ [c j + lo, c j + hi]`,
constant after the last. -/
theorem fnode_steps (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : FPhases x c n)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, j + 1 < n → c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false) :
    (∀ j, j < n → c j + lo ≤ fe O lo hi c j ∧ fe O lo hi c j ≤ c j + hi) ∧
    FPhases O (fe O lo hi c) n := by
  have cm := fc_mono hsp
  have nw : ∀ j, j < n → ∀ E, (j + 1 < n → E = c (j + 1)) → c j + hi < E + lo →
      c j + lo ≤ fe O lo hi c j ∧ fe O lo hi c j ≤ c j + hi ∧
      (∀ t, fe O lo hi c j ≤ t → t < E + lo → O t = Vph j) ∧
      (∀ t, c j + lo ≤ t → t < fe O lo hi c j → O t = !Vph j) := by
    intro j hj E hE hs
    exact node_win hW hN (fun s h1 h2 => hx.ph j s hj h1 (fun h => by rw [← hE h]; exact h2))
      (by have := cm 0 j (Nat.zero_le _) hj; omega) hs
  have nwb : ∀ j, j < n → c j + lo ≤ fe O lo hi c j ∧ fe O lo hi c j ≤ c j + hi := by
    intro j hj
    by_cases h1 : j + 1 < n
    · have := nw j hj (c (j + 1)) (fun _ => rfl) (by have := hsp j h1; omega)
      exact ⟨this.1, this.2.1⟩
    · have := nw j hj (c j + hi) (fun h => absurd h h1) (by omega)
      exact ⟨this.1, this.2.1⟩
  refine ⟨nwb, ⟨fun s hs => ?_, fun j s hj h1 h2 => ?_⟩⟩
  · by_cases h0 : s < hi
    · exact hP s h0
    · rcases hs with hn | hs
      · obtain ⟨u, u1, u2, u3⟩ := hW s (by omega)
        rw [u3]; exact hx.pre u (Or.inl hn)
      · by_cases hn : n = 0
        · obtain ⟨u, u1, u2, u3⟩ := hW s (by omega)
          rw [u3]; exact hx.pre u (Or.inl hn)
        · by_cases h1 : s < c 0 + lo
          · obtain ⟨u, u1, u2, u3⟩ := hW s (by omega)
            rw [u3]; exact hx.pre u (Or.inr (by omega))
          · have hn0 : 0 < n := by omega
            by_cases h01 : 0 + 1 < n
            · have := (nw 0 hn0 (c (0 + 1)) (fun _ => rfl) (by have := hsp 0 h01; omega)).2.2.2
                s (by omega) hs
              rw [this, PipeTimed.Vph_even 0]; rfl
            · have := (nw 0 hn0 (c 0 + hi) (fun h => absurd h h01) (by omega)).2.2.2 s
                (by omega) hs
              rw [this, PipeTimed.Vph_even 0]; rfl
  · by_cases hj1 : j + 1 < n
    · have hs := hsp j hj1
      by_cases ht : s < c (j + 1) + lo
      · exact (nw j hj (c (j + 1)) (fun _ => rfl) (by omega)).2.2.1 s h1 ht
      · have hj2 := h2 hj1
        by_cases hj2' : j + 1 + 1 < n
        · have := (nw (j + 1) hj1 (c (j + 1 + 1)) (fun _ => rfl)
            (by have := hsp (j + 1) hj2'; omega)).2.2.2 s (by omega) hj2
          rw [this, PipeTimed.Vph_succ, Bool.not_not]
        · have := (nw (j + 1) hj1 (c (j + 1) + hi) (fun h => absurd h hj2') (by omega)).2.2.2 s
            (by omega) hj2
          rw [this, PipeTimed.Vph_succ, Bool.not_not]
    · have hb := nwb j hj
      exact (nw j hj (s + hi + 1) (fun h => absurd h hj1) (by omega)).2.2.1 s h1 (by omega)

/-- Every output change is one of the `n` node edges. -/
theorem fchange_at (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : FPhases x c n)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, j + 1 < n → c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false) :
    ∀ t, O (t + 1) ≠ O t → ∃ j, j < n ∧ t + 1 = fe O lo hi c j := by
  obtain ⟨hb, hO⟩ := fnode_steps hW hN hx hlo hR hsp hP
  intro t h
  by_cases hn : n = 0
  · exact absurd ((hO.pre (t + 1) (Or.inl hn)).trans (hO.pre t (Or.inl hn)).symm) h
  have hm : ∀ j, j + 1 < n → fe O lo hi c j < fe O lo hi c (j + 1) := fun j hj => by
    have := (hb j (by omega)).2; have := (hb (j + 1) hj).1; have := hsp j hj; omega
  rcases fseg _ n (by omega) hm (t + 1) with h0 | ⟨j, hj, h1, h2⟩
  · exact absurd ((hO.pre (t + 1) (Or.inr h0)).trans (hO.pre t (Or.inr (by omega))).symm) h
  · refine ⟨j, hj, ?_⟩
    apply Classical.byContradiction; intro hne
    exact h ((hO.ph j (t + 1) hj h1 h2).trans
      (hO.ph j t hj (by omega) (fun h' => by have := h2 h'; omega)).symm)

/-- **C's `LutFb` from the physical LUT, finitely many phases.** -/
theorem flutFb_of_fphases {α : Type} {F : α → Bool → Bool} {p : Nat → α}
    (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : FPhases x c n)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, j + 1 < n → c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false)
    (hF : ∀ t, c 0 ≤ t → x t = F (p t) (qp t)) : LutFb F p qp O := by
  intro t h
  obtain ⟨j, hj, he⟩ := fchange_at hW hN hx hlo hR hsp hP t h
  obtain ⟨hb, hO⟩ := fnode_steps hW hN hx hlo hR hsp hP
  have cm := fc_mono hsp
  have b1 := (hb j hj).1; have b2 := (hb j hj).2
  have c0 := cm 0 j (Nat.zero_le _) hj
  have e1 : O (t + 1) = Vph j := hO.ph j (t + 1) hj (by omega) (fun h' => by
    have := (hb (j + 1) h').1; have := hsp j h'; omega)
  have e2 : x t = Vph j := hx.ph j t hj (by omega) (fun h' => by have := hsp j h'; omega)
  rw [e1, ← e2, hF t (by omega)]

/-- **C's `FbFirst` from the physical feedback wire, finitely many phases.** -/
theorem ffbFirst_of_fphases (hW : Win lo hi x O) (hN : NoRevertI lo hi x O)
    (hx : FPhases x c n)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, j + 1 < n → c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false)
    (hFB : CElemTiming.WinDelay wl wh O qp) (hRw : hi + wh ≤ c 0)
    (hspw : ∀ j, j + 1 < n → c j + hi + wh < c (j + 1) + lo) : FbFirst qp O := by
  intro t h
  obtain ⟨j, hj, he⟩ := fchange_at hW hN hx hlo hR hsp hP t h
  obtain ⟨hb, hO⟩ := fnode_steps hW hN hx hlo hR hsp hP
  have cm := fc_mono hsp
  have c0 := cm 0 j (Nat.zero_le _) hj
  have b1 := (hb j hj).1
  obtain ⟨u, u1, u2, e⟩ := hFB t (by omega)
  rw [e]
  cases j with
  | zero => rw [hO.pre u (Or.inr (by omega)), hO.pre t (Or.inr (by omega))]
  | succ k =>
    have := (hb k (by omega)).2; have := hspw k hj
    rw [hO.ph k u (by omega) (by omega) (fun _ => by omega),
      hO.ph k t (by omega) (by omega) (fun _ => by omega)]

end generic

/-! ## 2. One `bd_link_ctl` stage in a finite four-phase environment -/

/-- **The environment of one stage, finite form.** `Env1`'s fields, with the request
making `nr` edges `ρ 0 < … < ρ (nr-1)` and the acknowledge `na` edges
`α 1 < … < α na` (`α 0 = R`), each pin constant after its last edge; the departures
H_SND / H_RCV are asked for the edges that follow a node edge `j` (`j < nr`, `j ≤ na`). -/
structure FEnv1 (req ack rst O : Nat → Bool) (lo hi R : Nat) (ρ α : Nat → Nat)
    (nr na Es Ea : Nat) : Prop where
  /-- **H_RST** -/
  H_RST : ∀ t, rst t = decide (t < R)
  /-- **H_REQ_SHAPE** (from `R` on), finite. -/
  H_REQ_LOW0 : ∀ t, R ≤ t → (nr = 0 ∨ t < ρ 0) → req t = false
  H_REQ : ∀ j t, j < nr → ρ j ≤ t → (j + 1 < nr → t < ρ (j + 1)) → req t = Vph j
  /-- **H_ACK_SHAPE**, finite. -/
  H_ACK0 : α 0 = R
  H_ACK : ∀ j t, j ≤ na → α j ≤ t → (j < na → t < α (j + 1)) → ack t = !Vph j
  H_RST_EARLY : R ≤ ρ 0
  /-- **H_SND**: each later request edge comes `Es` after the node edge before it. -/
  H_SND : ∀ j, j + 1 < nr → j ≤ na → τs O lo hi ρ α j + Es ≤ ρ (j + 1)
  /-- **H_RCV**: each acknowledge edge comes `Ea` after the node edge before it. -/
  H_RCV : ∀ j, j < na → j < nr → τs O lo hi ρ α j + Ea ≤ α (j + 1)

section stage
variable {req ack rst O qp : Nat → Bool} {lo hi wl wh R Es Ea nr na : Nat} {ρ α : Nat → Nat}
variable (S : Stage req ack rst O qp lo hi wl wh) (E : FEnv1 req ack rst O lo hi R ρ α nr na Es Ea)
  (T : Timing1 lo hi wh R Es Ea)
include S E T
set_option linter.unusedSectionVars false

theorem fs_lh : lo ≤ hi := win_le S.H_LUT_WIN

theorem fs_wlh : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := S.H_FB wh (Nat.le_refl _); omega

theorem fcph0 : R ≤ cph ρ α 0 := by
  have := E.H_ACK0; unfold cph; omega

theorem fcph_ge (j : Nat) (hj : j < min nr (na + 1)) : R ≤ cph ρ α j := by
  induction j with
  | zero => exact fcph0 S E T
  | succ j ih =>
    have h1 := E.H_SND j (by omega) (by omega)
    have h2 := nt_lo O (cph ρ α j) (Vph j) (fs_lh S E T) (hi := hi)
    have h3 : ρ (j + 1) ≤ cph ρ α (j + 1) := Nat.le_max_left _ _
    have := ih (by omega)
    unfold τs at h1; omega

theorem fs_gap (j : Nat) (hj : j + 1 < min nr (na + 1)) :
    cph ρ α j + lo + min Es Ea ≤ cph ρ α (j + 1) := by
  have := E.H_SND j (by omega) (by omega); have := E.H_RCV j (by omega) (by omega)
  have := nt_lo O (cph ρ α j) (Vph j) (fs_lh S E T) (hi := hi)
  unfold τs at *; unfold cph at *; omega

theorem fs_rst_lo : ∀ t, R ≤ t → rst t = false := by
  intro t h; rw [E.H_RST]; simp; omega

/-- **H_EX_CLEAN, phase `j` of a finite run**: the excitation is `Vph j` on
`[cph j, cph (j+1))`, and from `cph j` on forever for the last phase. -/
theorem fs_phase (j : Nat) (hj : j < min nr (na + 1)) (s : Nat) (h1 : cph ρ α j ≤ s)
    (h2 : j + 1 < min nr (na + 1) → s < cph ρ α (j + 1)) : ex req ack qp rst s = Vph j := by
  have hjr : j < nr := by have := Nat.min_le_left nr (na + 1); omega
  have hja : j ≤ na := by have := Nat.min_le_right nr (na + 1); omega
  have hR := fcph_ge S E T j hj
  have hl := nt_lo O (cph ρ α j) (Vph j) (fs_lh S E T) (hi := hi)
  have hb := T.H_RST_LONG
  have hcr : ρ j ≤ cph ρ α j := Nat.le_max_left _ _
  have hca : α j ≤ cph ρ α j := Nat.le_max_right _ _
  have hcm : cph ρ α j = max (ρ j) (α j) := rfl
  -- the two phase ends: the next edge if there is one, else far beyond `s`
  obtain ⟨ρ', hρ1, hρ2⟩ : ∃ ρ' : Nat, (j + 1 < nr → ρ' = ρ (j + 1)) ∧
      (¬ j + 1 < nr → ρ' = s + cph ρ α j + lo + Es + Ea + 1) := by
    by_cases h : j + 1 < nr
    · exact ⟨_, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨_, fun h' => absurd h' h, fun _ => rfl⟩
  obtain ⟨α', hα1, hα2⟩ : ∃ α' : Nat, (j < na → α' = α (j + 1)) ∧
      (¬ j < na → α' = s + cph ρ α j + lo + Es + Ea + 1) := by
    by_cases h : j < na
    · exact ⟨_, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨_, fun h' => absurd h' h, fun _ => rfl⟩
  have hreq : ∀ t, ρ j ≤ t → t < ρ' → req t = Vph j := fun t a b =>
    E.H_REQ j t hjr a (fun h => by rw [← hρ1 h]; exact b)
  have hack : ∀ t, α j ≤ t → t < α' → ack t = !Vph j := fun t a b =>
    E.H_ACK j t hja a (fun h => by rw [← hα1 h]; exact b)
  have hdr : max (ρ j) (α j) + lo + min Es Ea ≤ ρ' := by
    rw [← hcm]
    by_cases h : j + 1 < nr
    · rw [hρ1 h]; have := E.H_SND j h hja; unfold τs at this; omega
    · rw [hρ2 h]; omega
  have hda : max (ρ j) (α j) + lo + min Es Ea ≤ α' := by
    rw [← hcm]
    by_cases h : j < na
    · rw [hα1 h]; have := E.H_RCV j h hjr; unfold τs at this; omega
    · rw [hα2 h]; omega
  have res := exc_phase_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS (Vph j) (ρ j) ρ' (α j) α'
    (min Es Ea) hreq hack (fun t ht => fs_rst_lo S E T t (by omega))
    hdr hda T.H_LAT (by omega)
  apply res s (by omega)
  by_cases hl1 : j + 1 < min nr (na + 1)
  · have := h2 hl1
    have a1 : j + 1 < nr := by have := Nat.min_le_left nr (na + 1); omega
    have a2 : j < na := by have := Nat.min_le_right nr (na + 1); omega
    rw [hρ1 a1, hα1 a2]; exact this
  · by_cases h : j + 1 < nr
    · have a2 : ¬ j < na := by
        intro h'; apply hl1; omega
      rw [hα2 a2]; omega
    · rw [hρ2 h]; omega

/-- Before the first phase (forever, if there is none) the excitation is 0. -/
theorem fs_pre (s : Nat) (hs : min nr (na + 1) = 0 ∨ s < cph ρ α 0) : ex req ack qp rst s = false := by
  have hc : cph ρ α 0 = ρ 0 := by unfold cph; rw [E.H_ACK0]; have := E.H_RST_EARLY; omega
  rcases hs with hn | hs
  · have hnr : nr = 0 := by
      omega
    exact exc_pre_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS R (s + 1)
      (fun t h => by rw [E.H_RST]; simp [h])
      (fun t h _ => E.H_REQ_LOW0 t h (Or.inl hnr)) T.H_RST_LONG s (by omega)
  · rw [hc] at hs
    exact exc_pre_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS R (ρ 0)
      (fun t h => by rw [E.H_RST]; simp [h])
      (fun t h h' => E.H_REQ_LOW0 t h (Or.inr h')) T.H_RST_LONG s hs

theorem fs_ex : FPhases (ex req ack qp rst) (cph ρ α) (min nr (na + 1)) :=
  ⟨fs_pre S E T, fun j s hj h1 h2 => fs_phase S E T j hj s h1 h2⟩

/-- **Finite `link_lutFb`**: B's physical single-stage model of the `bd_link` controller in
a FINITE four-phase environment gives C's premises of `link_bound`. -/
theorem flink_lutFb (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb Formal.Net.Ops.Gen.linkF (fun t => (req t, ack t)) qp O ∧ FbFirst qp O := by
  have hx := fs_ex S E T
  have hR := fcph0 S E T
  have hlat := T.H_LAT; have hrl := T.H_RST_LONG
  have hsp : ∀ j, j + 1 < min nr (na + 1) → cph ρ α j + hi ≤ cph ρ α (j + 1) := fun j hj => by
    have := fs_gap S E T j hj; omega
  have hspw : ∀ j, j + 1 < min nr (na + 1) → cph ρ α j + hi + wh < cph ρ α (j + 1) + lo :=
    fun j hj => by have := fs_gap S E T j hj; omega
  refine ⟨flutFb_of_fphases S.H_LUT_WIN S.H_NO_REVERT hx H_LUT_POS (by omega) hsp H_PWR
      (fun t ht => ?_),
    ffbFirst_of_fphases S.H_LUT_WIN S.H_NO_REVERT hx H_LUT_POS (by omega) hsp H_PWR S.H_FB
      (by omega) hspw⟩
  show CElemTiming.exc _ (req t) (ack t) (qp t) (rst t) = Formal.Net.Ops.Gen.linkF (req t, ack t) (qp t)
  rw [fs_rst_lo S E T t (by omega), LutFbBridge.linkF_c2n]

/-- **Finite `link_guar`**: the node makes exactly `min nr (na + 1)` clean edges `τs j`, each at
least `lo` after both pins' phase-`j` arrivals and at most `hi` after the later one, and
is constant after the last. -/
theorem flink_guar (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false) :
    FPhases O (τs O lo hi ρ α) (min nr (na + 1)) ∧
    (∀ j, j < min nr (na + 1) → cph ρ α j + lo ≤ τs O lo hi ρ α j ∧ τs O lo hi ρ α j ≤ cph ρ α j + hi) := by
  have hR := fcph0 S E T
  have hrl := T.H_RST_LONG
  have hsp : ∀ j, j + 1 < min nr (na + 1) → cph ρ α j + hi ≤ cph ρ α (j + 1) := fun j hj => by
    have := fs_gap S E T j hj; have := T.H_LAT; omega
  obtain ⟨hb, hO⟩ := fnode_steps S.H_LUT_WIN S.H_NO_REVERT (fs_ex S E T) H_LUT_POS (by omega)
    hsp H_PWR
  exact ⟨hO, hb⟩

end stage

/-! ## 3. The generic C-element (`LutFbBridge2.CelG`) in a finite environment -/

/-- **The environment of an `ι`-pin C-element, finite form** (`LutFbBridge2.EnvG` with
counts): pin `i` makes `m i` edges `ρ i 0 < …`, constant after its last; the node makes
`n` edges, at the phase starts `c j` (`j < n`, every pin arrived, `H_ARR`, and the last
arrival, `H_LAST`); no pin is behind the node (`H_CNT`) and some pin never starts phase
`n` (`H_STOP`, the run is quiet); H_SND for every later pin edge. -/
structure FEnvG {ι : Type} (p : Nat → ι → Bool) (rst O : Nat → Bool) (lo hi R : Nat)
    (ρ : ι → Nat → Nat) (m : ι → Nat) (c : Nat → Nat) (n E : Nat) : Prop where
  H_NE : Nonempty ι
  H_RST : ∀ t, rst t = decide (t < R)
  H_P0 : ∀ i t, R ≤ t → (m i = 0 ∨ t < ρ i 0) → p t i = false
  H_P : ∀ i j t, j < m i → ρ i j ≤ t → (j + 1 < m i → t < ρ i (j + 1)) → p t i = Vph j
  H_CNT : ∀ i, n ≤ m i
  H_STOP : ∃ i, m i = n
  H_ARR : ∀ i j, j < n → ρ i j ≤ c j
  H_LAST : ∀ j s, j < n → s < c j → ∃ i, s < ρ i j
  H_RST_EARLY : R ≤ c 0
  H_SND : ∀ i j, j + 1 < m i → j < n → nt O lo hi (c j) (Vph j) + E ≤ ρ i (j + 1)

section gen
open Formal.Cells.LutFbBridge2 (CelLaw CelG)
variable {ι : Type} {G : (ι → Bool) → Bool → Bool → Bool} {p : Nat → ι → Bool}
  {rst O qp : Nat → Bool} {lo hi wl wh R E n : Nat} {ρ : ι → Nat → Nat} {m : ι → Nat}
  {c : Nat → Nat}

theorem fg_gap (C : CelG G p rst O qp lo hi wl wh) (Ev : FEnvG p rst O lo hi R ρ m c n E)
    (j : Nat) (hj : j + 1 < n) : c j + lo + E ≤ c (j + 1) := by
  obtain ⟨i0⟩ := Ev.H_NE
  have := Ev.H_CNT i0
  have := Ev.H_SND i0 j (by omega) (by omega); have := Ev.H_ARR i0 (j + 1) hj
  have := nt_lo O (c j) (Vph j) (win_le C.H_LUT_WIN) (hi := hi)
  omega

theorem fg_ge (C : CelG G p rst O qp lo hi wl wh) (Ev : FEnvG p rst O lo hi R ρ m c n E) :
    ∀ j, j < n → R ≤ c j := by
  intro j
  induction j with
  | zero => intro _; exact Ev.H_RST_EARLY
  | succ j ih => intro hj; have := fg_gap C Ev j hj; have := ih (by omega); omega

/-- **H_EX_CLEAN, phase `j` of a finite run** (generic C-element); the last phase forever. -/
theorem fg_phase (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (Ev : FEnvG p rst O lo hi R ρ m c n E) (hRL : hi + wh ≤ R) (hLAT : hi + wh ≤ lo + E)
    (j : Nat) (hj : j < n) :
    ∀ s, c j ≤ s → (j + 1 < n → s < c (j + 1)) → G (p s) (qp s) (rst s) = Vph j := by
  have hR := fg_ge C Ev j hj
  have hl := nt_lo O (c j) (Vph j) (win_le C.H_LUT_WIN) (hi := hi)
  have hlo := C.H_LUT_POS
  -- a pin still in phase `j` at `s` reads `Vph j`
  have still : ∀ i s, c j ≤ s → (j + 1 < m i → s < ρ i (j + 1)) → p s i = Vph j :=
    fun i s h1 h2 => Ev.H_P i j s (by have := Ev.H_CNT i; omega)
      (Nat.le_trans (Ev.H_ARR i j hj) h1) h2
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h1 h2
    have hr : rst s = false := by rw [Ev.H_RST]; simp; omega
    rw [hr]
    by_cases hd : ∀ i, j + 1 < m i → s < ρ i (j + 1)
    · exact L.all _ _ _ (fun i => still i s h1 (hd i))
    · rw [Classical.not_forall] at hd
      obtain ⟨i0, hi0⟩ := hd
      have hm0 : j + 1 < m i0 := Classical.byContradiction fun h => hi0 (fun h' => absurd h' h)
      have hge : ρ i0 (j + 1) ≤ s := Classical.byContradiction fun h => hi0 (fun _ => by omega)
      have hsnd := Ev.H_SND i0 j hm0 hj
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
      have hq : qp s = Vph j := by
        rw [e, q3]; exact ih s' (by omega) (by omega) (fun h => by have := h2 h; omega)
      rw [hq]
      by_cases hl1 : j + 1 < n
      · obtain ⟨i1, hi1⟩ := Ev.H_LAST (j + 1) s hl1 (h2 hl1)
        exact L.hold _ _ ⟨i1, still i1 s h1 (fun _ => hi1)⟩
      · obtain ⟨i1, hi1⟩ := Ev.H_STOP
        exact L.hold _ _ ⟨i1, still i1 s h1 (fun h => by omega)⟩

/-- **Before the first phase** (forever, if the node never moves), generic C-element. -/
theorem fg_pre (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (Ev : FEnvG p rst O lo hi R ρ m c n E) (hRL : hi + wh ≤ R) :
    ∀ s, (n = 0 ∨ s < c 0) → G (p s) (qp s) (rst s) = false := by
  have hlo := C.H_LUT_POS
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h
    by_cases hs : s < R
    · rw [Ev.H_RST s]; simp only [hs, decide_true]; exact L.rst _ _
    · have hr : rst s = false := by rw [Ev.H_RST]; simp; omega
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
      have hq : qp s = false := by
        rw [e, q3]; exact ih s' (by omega) (by rcases h with h | h; exact Or.inl h; omega)
      rw [hr, hq]
      rcases h with h | h
      · obtain ⟨i1, hi1⟩ := Ev.H_STOP
        exact L.hold _ _ ⟨i1, Ev.H_P0 i1 s (by omega) (Or.inl (by omega))⟩
      · by_cases hn : n = 0
        · obtain ⟨i1, hi1⟩ := Ev.H_STOP
          exact L.hold _ _ ⟨i1, Ev.H_P0 i1 s (by omega) (Or.inl (by omega))⟩
        · obtain ⟨i1, hi1⟩ := Ev.H_LAST 0 s (by omega) h
          exact L.hold _ _ ⟨i1, Ev.H_P0 i1 s (by omega) (Or.inr hi1)⟩

/-- **Finite `celG_lutFb`**: the generic C-element bridge for a finite (quiet) run. -/
theorem fcelG_lutFb (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (Ev : FEnvG p rst O lo hi R ρ m c n E) (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E)
    (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb (fun pv q => G pv q false) p qp O ∧ FbFirst qp O := by
  have hx : FPhases (fun t => G (p t) (qp t) (rst t)) c n :=
    ⟨fg_pre L C Ev H_RST_LONG, fun j s hj h1 h2 => fg_phase L C Ev H_RST_LONG H_LAT j hj s h1 h2⟩
  have hR := Ev.H_RST_EARLY
  have hlo := C.H_LUT_POS
  have hsp : ∀ j, j + 1 < n → c j + hi ≤ c (j + 1) := fun j hj => by
    have := fg_gap C Ev j hj; omega
  have hspw : ∀ j, j + 1 < n → c j + hi + wh < c (j + 1) + lo := fun j hj => by
    have := fg_gap C Ev j hj; omega
  refine ⟨flutFb_of_fphases C.H_LUT_WIN C.H_NO_REVERT hx hlo (by omega) hsp H_PWR
      (fun t ht => ?_),
    ffbFirst_of_fphases C.H_LUT_WIN C.H_NO_REVERT hx hlo (by omega) hsp H_PWR C.H_FB
      (by omega) hspw⟩
  have hr : rst t = false := by
    have := Ev.H_RST t; rw [this]; simp; omega
  show G (p t) (qp t) (rst t) = G (p t) (qp t) false
  rw [hr]

end gen

/-- **Finite `wire_steps`**: through a wire, a node with `n` clean edges gives a pin with `n`
clean edges `ε j ∈ [e j + wl, e j + wh]`, constant after the last. -/
theorem fwire_steps {wl wh n : Nat} {O P : Nat → Bool} {e : Nat → Nat} (W : Wire wl wh O P)
    (hO : FPhases O e n) (h0 : wh ≤ e 0) (hsp : ∀ j, j + 1 < n → e j + wh ≤ e (j + 1)) :
    FPhases P (LutFbBridge2Env.ε P wl wh e) n ∧
    ∀ j, j < n → e j + wl ≤ LutFbBridge2Env.ε P wl wh e j ∧ LutFbBridge2Env.ε P wl wh e j ≤ e j + wh := by
  obtain ⟨hb, hP⟩ := fnode_steps W.H_WIN W.H_NO_REVERT hO W.H_POS h0 hsp W.H_PWR
  exact ⟨hP, hb⟩

/-! ## 4. Wires and the link class -/

/-- **Finite `wire_di`**: C's DI wire relation through a physical wire, for a node with
finitely many edges. -/
theorem fwire_di {wl wh n : Nat} {O P : Nat → Bool} {e : Nat → Nat} (W : Wire wl wh O P)
    (hO : FPhases O e n) (h0 : wh ≤ e 0) (hsp : ∀ j, j + 1 < n → e j + wh ≤ e (j + 1)) :
    ∀ t, P (t + 1) ≠ P t → P (t + 1) = O t := by
  have hx : FPhases O (fun j => e j) n := hO
  exact flutFb_of_fphases (F := fun (a : Bool) (_ : Bool) => a) (p := O) (qp := fun _ => false)
    W.H_WIN W.H_NO_REVERT hx W.H_POS h0 hsp W.H_PWR (fun _ _ => rfl)

/-- **Finite `link_link_env`** (link-to-link channel `A → B`, `A`'s node `OA` making `nA`
edges, `B`'s `OB` making `nB`): from the two controllers' guarantees in their finite form
(`GA`: A's edge `j+1` waits for B's edge `j`, which exists; `GB`: B's edge `j` waits for
A's edge `j`, which exists), the two wires, H_WIRE_R and H_RT: B's request-side `FEnv1`
fields (`nr = nA`) and A's acknowledge-side fields (`na = nB`), and both DI wires. -/
theorem flink_link_env {OA OB reqB ackA : Nat → Bool} {τA τB : Nat → Nat}
    {nA nB loA loB wlab whab wlba whba R : Nat}
    (hA : FPhases OA τA nA) (hB : FPhases OB τB nB)
    (Wab : Wire wlab whab OA reqB) (Wba : Wire wlba whba OB ackA)
    (GA0 : R + loA ≤ τA 0)
    (GA : ∀ j, j + 1 < nA → j < nB ∧ LutFbBridge2Env.ε ackA wlba whba τB j + loA ≤ τA (j + 1))
    (GB : ∀ j, j < nB → j < nA ∧ LutFbBridge2Env.ε reqB wlab whab τA j + loB ≤ τB j)
    (GB0 : nB = 0 → R + loB ≤ τB 0)
    (H_WIRE_R : whab ≤ R ∧ whba ≤ R)
    (H_RT : whab ≤ wlab + loB + wlba + loA ∧ whba ≤ wlab + loB + wlba + loA) :
    -- B, request side (`FEnv1` with `ρ = ε reqB …`, `nr = nA`)
    (∀ t, R ≤ t → (nA = 0 ∨ t < LutFbBridge2Env.ε reqB wlab whab τA 0) → reqB t = false) ∧
    (∀ j t, j < nA → LutFbBridge2Env.ε reqB wlab whab τA j ≤ t →
      (j + 1 < nA → t < LutFbBridge2Env.ε reqB wlab whab τA (j + 1)) → reqB t = Vph j) ∧
    R ≤ LutFbBridge2Env.ε reqB wlab whab τA 0 ∧
    (∀ j, j + 1 < nA → τB j + (wlba + loA + wlab) ≤ LutFbBridge2Env.ε reqB wlab whab τA (j + 1)) ∧
    -- A, acknowledge side (`FEnv1` with `α = ash R (ε ackA …)`, `na = nB`)
    (∀ j t, j ≤ nB → LutFbBridge2Env.ash R (LutFbBridge2Env.ε ackA wlba whba τB) j ≤ t →
      (j < nB → t < LutFbBridge2Env.ash R (LutFbBridge2Env.ε ackA wlba whba τB) (j + 1)) →
      ackA t = !Vph j) ∧
    (∀ j, j < nB → τA j + (wlab + loB + wlba) ≤
      LutFbBridge2Env.ash R (LutFbBridge2Env.ε ackA wlba whba τB) (j + 1)) ∧
    -- C's DI wires
    (∀ t, reqB (t + 1) ≠ reqB t → reqB (t + 1) = OA t) ∧
    (∀ t, ackA (t + 1) ≠ ackA t → ackA (t + 1) = OB t) := by
  have lab := LutFbBridge2Env.ε_lo Wab τA
  have lba := LutFbBridge2Env.ε_lo Wba τB
  have spA : ∀ j, j + 1 < nA → τA j + whab ≤ τA (j + 1) := fun j hj => by
    obtain ⟨h1, h2⟩ := GA j hj; have := lba j; have := (GB j h1).2; have := lab j; omega
  have spB : ∀ j, j + 1 < nB → τB j + whba ≤ τB (j + 1) := fun j hj => by
    obtain ⟨h1, h2⟩ := GB (j + 1) hj; have := lab (j + 1); have := (GA j h1).2; have := lba j
    omega
  have h0A : whab ≤ τA 0 := by omega
  have h0B : whba ≤ τB 0 := by
    by_cases hn : nB = 0
    · have := GB0 hn; omega
    · have := (GB 0 (by omega)).2; have := lab 0; omega
  obtain ⟨PA, _⟩ := fwire_steps Wab hA h0A spA
  obtain ⟨PB, _⟩ := fwire_steps Wba hB h0B spB
  refine ⟨fun t _ h => PA.pre t h, PA.ph, by have := lab 0; omega, fun j hj => ?_,
    fun j t hj h1 h2 => ?_, fun j hj => ?_, fwire_di Wab hA h0A spA, fwire_di Wba hB h0B spB⟩
  · have := lab (j + 1); have := (GA j hj).2; have := lba j; omega
  · cases j with
    | zero =>
      have : ackA t = false := PB.pre t (by
        by_cases hn : nB = 0
        · exact Or.inl hn
        · exact Or.inr (h2 (by omega)))
      rw [this]; rfl
    | succ k =>
      rw [PB.ph k t (by omega) h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · show τA j + (wlab + loB + wlba) ≤ LutFbBridge2Env.ε ackA wlba whba τB j
    have := lba j; have := (GB j hj).2; have := lab j; omega

open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink isLink_eq)

/-- **B's physical model of one `bd_link` operator, finite run**: `PhysLink` VERBATIM, with
`Env1` replaced by `FEnv1` (the request makes `nr` edges and the acknowledge `na`, any
finite numbers). -/
def FPhysLink (i o : Chan) : Prop :=
  ∃ (rst c qp : Nat → Bool) (lo hi wl wh R Es Ea wla wha wlr whr nr na : Nat) (ρ α : Nat → Nat),
    Stage i.req o.ack rst c qp lo hi wl wh ∧ FEnv1 i.req o.ack rst c lo hi R ρ α nr na Es Ea ∧
    Timing1 lo hi wh R Es Ea ∧ 1 ≤ lo ∧ (∀ t, t < hi → c t = false) ∧
    Wire wla wha c i.ack ∧ Wire wlr whr c o.req ∧
    wha ≤ R ∧ whr ≤ R ∧ wha + hi ≤ 2 * lo + min Es Ea ∧ whr + hi ≤ 2 * lo + min Es Ea ∧
    (∀ t, c t = true → o.dat t = i.dat t) ∧ (∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t)

/-- **C's `Link` from B's physical link model, finite run** (finite `link_of_phys`). -/
theorem link_of_fphys {i o : Chan} (h : FPhysLink i o) : ∃ c, Link.Link i o c := by
  obtain ⟨rst, c, qp, lo, hi, wl, wh, R, Es, Ea, wla, wha, wlr, whr, nr, na, ρ, α, S, E, T,
    hpos, hpwr, Wa, Wr, ra, rr, sa, sr, lop, lho⟩ := h
  have hL := flink_lutFb S E T hpos hpwr
  obtain ⟨hc, hb⟩ := flink_guar S E T hpos hpwr
  have hR := fcph0 S E T
  have hsp : ∀ j, j + 1 < min nr (na + 1) →
      τs c lo hi ρ α j + lo + min Es Ea + lo ≤ τs c lo hi ρ α (j + 1) + hi := by
    intro j hj
    have := (hb j (by omega)).2; have := (hb (j + 1) hj).1; have := fs_gap S E T j hj
    have := fs_lh S E T
    omega
  have sa' : ∀ j, j + 1 < min nr (na + 1) → τs c lo hi ρ α j + wha ≤ τs c lo hi ρ α (j + 1) :=
    fun j hj => by have := hsp j hj; omega
  have sr' : ∀ j, j + 1 < min nr (na + 1) → τs c lo hi ρ α j + whr ≤ τs c lo hi ρ α (j + 1) :=
    fun j hj => by have := hsp j hj; omega
  have h0 : R ≤ τs c lo hi ρ α 0 := by
    have := nt_lo c (cph ρ α 0) (Vph 0) (fs_lh S E T) (hi := hi); unfold τs; omega
  have hlo1 : 1 ≤ hi := by have := fs_lh S E T; omega
  refine ⟨c, link_of_gen hL.1 hL.2 (fwire_di Wa hc (by omega) sa') (fwire_di Wr hc (by omega) sr')
    lop lho (hpwr 0 (by omega)) (Wa.H_PWR 0 (by have := Wa.H_POS; have := win_le Wa.H_WIN; omega))
    (Wr.H_PWR 0 (by have := Wr.H_POS; have := win_le Wr.H_WIN; omega))⟩

/-- **End to end, link class, finite runs.** C's gcd_hw circuit safety
(`gcd_hw_circuit_safe`), with `H_CELLS` for every one of the 175 link operators replaced by
B's physical link model in a FINITE environment (`FPhysLink`); `H_CELLS` for the other
operator classes, H_BUNDLE and H_CM_FORCED stay C's hypotheses. Same conclusion as
`LutFbBridge2Env.gcd_hw_safe_phys_links`. -/
theorem gcd_hw_safe_fin_links (a b : Nat) (ch : Fin NC → Chan)
    (H_LINKS : ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FPhysLink (ch i) (ch o'))
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  refine gcd_hw_circuit_safe a b ch (fun o => ?_) H_BUNDLE H_CM_FORCED
  by_cases hl : isLink (opAt o) = true
  · obtain ⟨i, o', hk⟩ := isLink_eq hl
    rw [hk]; exact link_of_fphys (H_LINKS o i o' hk)
  · exact H_OTHER o (by simpa using hl)

end Formal.Cells.FiniteRuns
