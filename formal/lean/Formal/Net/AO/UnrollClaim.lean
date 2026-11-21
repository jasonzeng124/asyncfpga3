import Formal.Net.AO.UnrollRest

/-!
# The unrolled certificate, part 6: claim proofs, initial and environment claims for every word (shard C)

**Problem, plainly.** `UnrollRest.timedA_follows_unroll` / `timedA_live_unroll` still take three hypotheses about the
LONG claim list `uclT (wk (wP ks)) 0` of a word of window kinds: `hGC` (every claim on a gate has a proof
`GateProof`, or is the union, `ChainOK`, of a chain of claims with proofs), `hInit` (every claim holds up to `t0`)
and `hEnvC` (every claim on an environment node holds). There are infinitely many words; `hGC` and `hInit` should
follow from checks on boundedly many consecutive kinds, as the timing tables do in `UnrollTime`.

**How claims shift.** The long list is the windows' claim lists in order, window `j`'s claims shifted by its offsets
(`shC (off j)`). Splitting at window `j` (`uclT_split`, `uclT_base`), the claim list of the sub-word
`(ks.drop j).take r` (in its own coordinates) sits in the long list from index `ncl (ks.take j)` on, every claim
shifted by `off j` (`uclT_win`). A proof in the sub-word transfers (`gateProof_window`): its coverage `.cl n`
becomes `.cl (ncl (ks.take j) + n)` (`.X` when out of range: the sub-word's `ValOK` already treats it as unknown),
`.ex k` becomes `.ex (k + off j u)`, and covering windows, `CovTime` (`covTime_window`) and chains (`chainOK_window`)
shift with the separation table (`UnrollTime.sep_win`, restricted to the sub-word's events).

**Where the start state enters.** In `GateProof` the start state enters ONLY through exact coverage `.ex k`, whose
value is the start state flipped `k` times. That is per pin and not tied to claims without a start event, so the
sub-word is checked with its own start state: the long one flipped by the event-count parities before it
(`gc_unroll`), or, when the kinds' start states chain (`UnrollData.StChain`) on a set holding all claim pins, the
first kind's own `s0` (`gc_unroll_kind`, then a check of the sub-word alone). One more condition is needed: `.ex 0`
covers a pin from before its first event in the sub-word, but in the long certificate that covering window starts at
the previous event, before the sub-word, which the sub-word cannot time. `GateProofW` (`GateProof` plus this demand)
allows `.ex 0` only in the sub-words that start the word (`t = 0`). In `hInit` the start state DOES enter through
claims with no start event (`A = none`, or a negative start delay): such a claim must hold before `t0` with nothing
to anchor it. `init_unroll` allows them only in the first window and asks them to hold there; `holds_init_quiet`
discharges one on an exact node whose value is its value at `t0`.

**Proved.**
* `uclT_length`, `uclT_add`, `uclT_base`, `uclT_split`, `uclT_win`, `mem_uclT`, `shC_zero`: the long claim list,
  window by window.
* `covTime_window`, `chainOK_window`, `covWin_shCov`, `gateProof_window`: a sub-word's claim proofs and chains give
  those of the shifted claims in the long certificate.
* `gc_unroll_gen`, `gc_unroll`, `gc_unroll_kind`: `hGC` for every word from the window checks `GcWin` on the sub-words
  `(ks.drop (i - 1)).take r` (`r ≥ 2`, window `i - (i - 1)`, as in `UnrollTime`).
* `holds_init_start`, `holds_init_quiet`, `init_unroll`: `hInit` for every word from a per-kind check.
* `env_unroll`, `env_none`: `hEnvC` restated window by window; vacuous when no kind claims a non-gate node.
* `timedA_follows_unrollC`, `timedA_live_unrollC`: `timedA_follows_unroll` / `timedA_live_unroll` with `hGC` replaced
  by `GcWin` checks and `hInit` by the per-kind check.

**Not shown here.** That any instance (THE target's kinds) passes these checks. `hEnvC` is NOT reduced: whether an
environment claim holds is a property of the run (`env_unroll` only restates it per window). `GcWin` in `gc_unroll`
depends on the run's start state through the parities before the sub-word (finitely many values per sub-word, but
not a check on the sub-word alone); `gc_unroll_kind` removes this only under `StChain`. The checks are only
sufficient: a claim of window `i` must be proved inside the sub-word from window `i - 1` (every coverage claim and
chain claim it uses must lie there), and `.ex 0` is refused in every sub-word with `t = 1`, even the one starting at
window 0 (`i = 1`), where it would be harmless. The remaining hypotheses of `timedA_follows_unrollC` are those of
`UnrollRest.timedA_follows_unroll` other than `hGC` and `hInit`.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## The long claim list, window by window -/

/-- The long claim list has one entry per window claim. -/
theorem uclT_length : ∀ (ks : List (WKind α)) (b : α → Nat), (uclT ks b).length = ncl ks
  | [], _ => rfl
  | w :: ks, b => by simp [uclT, ncl, uclT_length ks]

/-- Raising the base by `o` shifts every claim of the long list by `o`. -/
theorem uclT_add (o : α → Nat) : ∀ (ks : List (WKind α)) (b : α → Nat),
    uclT ks (fun p => b p + o p) = (uclT ks b).map (shC o)
  | [], _ => rfl
  | w :: ks, b => by
    simp only [uclT, List.map_append, List.map_map]
    have e : (fun p => b p + o p + w.len p) = (fun p => (b p + w.len p) + o p) := by funext p; omega
    rw [e, uclT_add o ks (fun p => b p + w.len p)]
    have e2 : (shC o ∘ shC b) = shC (fun p => b p + o p) := by funext c; simp [shC_shC]
    rw [e2]

/-- The long list with base `o` is the list with base 0, shifted by `o`. -/
theorem uclT_base (o : α → Nat) (ks : List (WKind α)) : uclT ks o = (uclT ks (fun _ => 0)).map (shC o) := by
  have h := uclT_add o ks (fun _ => 0)
  have e : (fun p => (fun _ => (0 : Nat)) p + o p) = o := by funext p; simp
  rw [e] at h
  exact h

/-- **The long claim list splits at window `j`**: the claims of the first `j` windows, then those of the rest with
base raised by window `j`'s offsets. -/
theorem uclT_split : ∀ (ks : List (WKind α)) (b : α → Nat) (j : Nat),
    uclT ks b = uclT (ks.take j) b ++ uclT (ks.drop j) (fun p => b p + off (wcs ks) j p)
  | [], _, j => by simp [uclT]
  | w :: ks, b, 0 => by
    simp only [List.take_zero, List.drop_zero]
    have e : (fun p => b p + off (wcs (w :: ks)) 0 p) = b := by funext p; rw [off_zero]; omega
    rw [e]; rfl
  | w :: ks, b, j + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, uclT, List.append_assoc]
    rw [uclT_split ks (fun p => b p + w.len p) j]
    have e : (fun p => b p + w.len p + off (wcs ks) j p) = (fun p => b p + off (wcs (w :: ks)) (j + 1) p) := by
      funext p; rw [off_wcs_succ]; omega
    rw [e]

/-- **The claims of the sub-word from window `j` sit in the long list** after the `ncl (ks.take j)` claims of the
earlier windows, shifted by window `j`'s offsets. -/
theorem uclT_win (ks : List (WKind α)) (j r n : Nat) (hn : n < (uclT ((ks.drop j).take r) (fun _ => 0)).length) :
    (uclT ks (fun _ => 0))[ncl (ks.take j) + n]? =
      ((uclT ((ks.drop j).take r) (fun _ => 0))[n]?).map (shC (off (wcs ks) j)) := by
  rw [uclT_split ks (fun _ => 0) j]
  have e : (fun p => (fun _ => (0 : Nat)) p + off (wcs ks) j p) = off (wcs ks) j := by funext p; simp
  rw [e, uclT_base (off (wcs ks) j) (ks.drop j), uclT_split (ks.drop j) (fun _ => 0) r, List.map_append,
    List.getElem?_append_right (by rw [uclT_length]; omega), uclT_length,
    show ncl (ks.take j) + n - ncl (ks.take j) = n by omega,
    List.getElem?_append_left (by rw [List.length_map]; exact hn), List.getElem?_map]

/-- Every long claim is a window's claim shifted by that window's offsets. -/
theorem mem_uclT : ∀ (ks : List (WKind α)) (b : α → Nat) (c : Claim α), c ∈ uclT ks b →
    ∃ i, ∃ h : i < ks.length, ∃ c0 ∈ ks[i].cl, c = shC (fun p => b p + off (wcs ks) i p) c0
  | [], _, _, h => by simp [uclT] at h
  | w :: ks, b, c, h => by
    simp only [uclT, List.mem_append, List.mem_map] at h
    rcases h with ⟨c0, hc0, rfl⟩ | h
    · refine ⟨0, by simp, c0, by simpa using hc0, ?_⟩
      have e : (fun p => b p + off (wcs (w :: ks)) 0 p) = b := by funext p; rw [off_zero]; omega
      rw [e]
    · obtain ⟨i, hi, c0, hc0, rfl⟩ := mem_uclT ks _ c h
      refine ⟨i + 1, by simp; omega, c0, by simpa using hc0, ?_⟩
      have e : (fun p => b p + w.len p + off (wcs ks) i p) = (fun p => b p + off (wcs (w :: ks)) (i + 1) p) := by
        funext p; rw [off_wcs_succ]; omega
      rw [e]

/-- Shifting by zero offsets does nothing. -/
theorem shC_zero {o : α → Nat} (h : ∀ u, o u = 0) (c : Claim α) : shC o c = c := by
  cases c with
  | mk z val A a B b => cases A <;> cases B <;> simp [shC, shE, h]

/-! ## Transferring claim proofs from a window -/

section transfer
variable {N : TNet α} {dat : α → Bool} {C' : Cert α} {Sep Sep' : α → Nat → α → Nat → Option Nat} {o : α → Nat}

/-- **Covering-window timing of shifted claims** follows from the window's. -/
theorem covTime_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (c w : Claim α) (hiZ loZ : Nat) (h : CovTime Sep' c w hiZ loZ) : CovTime Sep (shC o c) (shC o w) hiZ loZ := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨?_, ?_⟩
  · cases hw : w.A with
    | none => simp [shC, hw]
    | some e' =>
      rw [hw] at hA
      obtain ⟨e, he, d, hd, hle⟩ := hA
      obtain ⟨h1, h2⟩ := hSepDom _ _ _ _ _ hd
      simp only [shC, hw, he, Option.map]
      refine ⟨shE o e, rfl, d, ?_, hle⟩
      simp only [shE]; rw [hSep e'.1 e'.2 e.1 e.2 h1 h2]; exact hd
  · cases hw : w.B with
    | none => simp [shC, hw]
    | some e' =>
      rw [hw] at hB
      obtain ⟨e, he, d, hd, hle⟩ := hB
      obtain ⟨h1, h2⟩ := hSepDom _ _ _ _ _ hd
      simp only [shC, hw, he, Option.map]
      refine ⟨shE o e, rfl, d, ?_, hle⟩
      simp only [shE]; rw [hSep e.1 e.2 e'.1 e'.2 h1 h2]; exact hd

/-- **A shifted chain of claims is a chain** for the long separation table, when the window's chain is one for the
window's table. -/
theorem chainOK_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainOK Sep' c cs → ChainOK Sep (shC o c) (cs.map (shC o))
  | [], _, h => h.elim
  | [c1], c, h => by
    obtain ⟨hz, hv, hA, ha, hB, hb⟩ := h
    simp only [List.map_cons, List.map_nil, ChainOK, shC]
    exact ⟨hz, hv, by rw [hA], ha, by rw [hB], hb⟩
  | c1 :: c2 :: cs, c, h => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    have ih := chainOK_window hSep hSepDom (c2 :: cs) ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ hrest
    simp only [List.map_cons] at ih ⊢
    refine ⟨hz, hv, by simp only [shC]; rw [hA], ha, ?_, ih⟩
    cases hB1 : c1.B with
    | none => simp [shC, hB1]
    | some e1 =>
      cases hA2 : c2.A with
      | none => simp [shC, hB1, hA2]
      | some e2 =>
        rw [hB1, hA2] at hj
        obtain ⟨d, hd, hle⟩ := hj
        obtain ⟨h1, h2⟩ := hSepDom _ _ _ _ _ hd
        simp only [shC, hB1, hA2, Option.map, shE]
        exact ⟨d, by rw [hSep e2.1 e2.2 e1.1 e1.2 h1 h2]; exact hd, hle⟩

/-- A window coverage made long: exact sources shifted by the offsets, claim `n` of the window's list (of length
`len`) to claim `P + n` of the long list, out-of-range claims to `X`. -/
def shCov (o : α → Nat) (P len : Nat) (u : α) : Cov → Cov
  | .ex k => .ex (k + o u)
  | .cl n => if n < len then .cl (P + n) else .X
  | .X => .X

/-- **`GateProof` in a window** of the sub-word, with one extra demand: an exact source may be covered from before
its first event in the sub-word (`Cov.ex 0`) only when the sub-word starts the word (`t = 0`); otherwise the long
covering window would start at an event before the sub-word, which the sub-word cannot time. -/
def GateProofW (N : TNet α) (dat : α → Bool) (Sep : α → Nat → α → Nat → Option Nat) (s0 : α → Bool)
    (cl : List (Claim α)) (t : Nat) (c : Claim α) : Prop :=
  N.gate c.z = true ∧ 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N s0 cl c cov ∧
    (∀ u ∈ N.pins c.z, ∀ w, covWin s0 cl u (cov u) = some w → CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
    (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false ∧ (k = 0 → t = 0)) ∧
      (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u))

/-- The long covering window of a shifted coverage is the window's covering window, shifted. -/
theorem covWin_shCov (s0 s0' : α → Bool) (S L : List (Claim α)) (P : Nat)
    (hL : ∀ n (h : n < S.length), L[P + n]? = some (shC o S[n])) (u : α)
    (hst : s0' u = xor (s0 u) (o u % 2 == 1)) (cv : Cov) (hz : cv = .ex 0 → o u = 0) :
    covWin s0 L u (shCov o P S.length u cv) = (covWin s0' S u cv).map (shC o) := by
  cases cv with
  | ex k =>
    simp only [shCov, covWin, Option.map, shC, shE, hst]
    have hv : xor (s0 u) ((k + o u) % 2 == 1) = xor (xor (s0 u) (o u % 2 == 1)) (k % 2 == 1) := by
      rw [Nat.add_comm, xor_par]
    rw [hv]
    by_cases hk : k = 0
    · subst hk
      have := hz rfl
      simp [this]
    · have hk' : ¬ (k + o u = 0) := by omega
      simp only [hk, hk', ↓reduceIte]
      congr 4
      omega
  | cl n =>
    simp only [shCov, covWin]
    by_cases hn : n < S.length
    · simp only [hn, ↓reduceIte]; rw [hL n hn, List.getElem?_eq_getElem hn]; rfl
    · simp only [hn, ↓reduceIte]; rw [List.getElem?_eq_none (by omega)]; rfl
  | X => rfl

/-- **A window's claim proof gives the long claim proof** of the shifted claim. -/
theorem gateProof_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (s0 s0' : α → Bool) (S L : List (Claim α)) (P t : Nat)
    (hL : ∀ n (h : n < S.length), L[P + n]? = some (shC o S[n])) (c : Claim α)
    (hst : ∀ u ∈ N.pins c.z, s0' u = xor (s0 u) (o u % 2 == 1)) (ht0 : t = 0 → ∀ u, o u = 0)
    (h : GateProofW N dat Sep' s0' S t c) : GateProof N dat Sep s0 L (shC o c) := by
  obtain ⟨hg, ha, cov, hval, hcov, hpin⟩ := h
  have hcw : ∀ u ∈ N.pins c.z, covWin s0 L u (shCov o P S.length u (cov u)) = (covWin s0' S u (cov u)).map (shC o) :=
    fun u hu => covWin_shCov s0 s0' S L P hL u (hst u hu) (cov u)
      (fun he => ht0 (((hpin u hu).1 0 he).2 rfl) u)
  refine ⟨hg, ha, fun u => shCov o P S.length u (cov u), ?_, ?_, ?_⟩
  · intro bb hbb
    apply hval bb
    intro u hu w' hw'
    exact hbb u hu (shC o w') (by rw [hcw u hu, hw']; rfl)
  · intro u hu w hw
    rw [hcw u hu] at hw
    obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hw
    exact covTime_window hSep hSepDom c w' _ _ (hcov u hu w' hw')
  · intro u hu
    refine ⟨fun k hk => ?_, fun i w hi hw => ?_⟩
    · cases hc : cov u with
      | ex k0 => exact ((hpin u hu).1 k0 hc).1
      | cl n =>
        simp only [hc, shCov] at hk
        split at hk <;> cases hk
      | X => simp [hc, shCov] at hk
    · cases hc : cov u with
      | ex k0 => simp [hc, shCov] at hi
      | cl n =>
        simp only [hc, shCov] at hi
        by_cases hn : n < S.length
        · simp only [hn, ↓reduceIte, Cov.cl.injEq] at hi
          subst hi
          rw [hL n hn] at hw
          cases hw
          exact (hpin u hu).2 n S[n] hc (List.getElem?_eq_getElem hn)
        · simp only [hn, ↓reduceIte] at hi; cases hi
      | X => simp [hc, shCov] at hi

end transfer

/-! ## The claim hypothesis `hGC` for every word -/

/-- **The window check for claim proofs** of the sub-word `s` (target window `t`), with `s0` the state at the start of
`s`: every claim of window `t`'s kind on a gate, shifted to `s`'s coordinates, has a proof `GateProofW` in `s`'s claim
list `uclT (wk s) 0` with `s`'s restricted separation table, or is the union (`ChainOK`) of a chain of claims of that
list that have such proofs. A property of `s`, `t` and `s0` only. -/
def GcWin (N : TNet α) (dat : α → Bool) (s0 : α → Bool) (s : List (WKindT α)) (t : Nat) : Prop :=
  ∀ (h : t < s.length), ∀ c0 ∈ s[t].cl, N.gate c0.z = true →
    GateProofW N dat (WSep s) s0 (uclT (wk s) (fun _ => 0)) t (shC (off (wt s) t) c0) ∨
    ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk s) (fun _ => 0) ∧
      GateProofW N dat (WSep s) s0 (uclT (wk s) (fun _ => 0)) t c') ∧ ChainOK (WSep s) (shC (off (wt s) t) c0) cs

/-- **`hGC` of the long certificate, for every word, from the window checks**, general form: the claims of window `i`
are checked in the sub-word of `r ≥ 2` kinds from window `i - 1` (from window 0 when `i = 0`) with a start state
`sw i` that agrees, on the pins of the sub-word's claim nodes, with the long start state `s0` flipped by the parities
of the event counts before the sub-word. -/
theorem gc_unroll_gen (N : TNet α) (dat : α → Bool) (r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α)) (s0 : α → Bool)
    (sw : Nat → α → Bool)
    (hsw : ∀ i, i < ks.length → ∀ w ∈ (ks.drop (i - 1)).take r, ∀ c0 ∈ w.cl, ∀ u ∈ N.pins c0.z,
      sw i u = st s0 (off (wt ks) (i - 1)) u)
    (hW : ∀ i, i < ks.length → GcWin N dat (sw i) ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), N.gate c.z = true →
      GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk ks) (fun _ => 0) ∧
        GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c') ∧ ChainOK (LSep ks) c cs := by
  intro c hc hg
  obtain ⟨i, hi, c0, hc0, rfl⟩ := mem_uclT (wk ks) _ c hc
  have hi' : i < ks.length := by simpa [wk] using hi
  have hwi : (wk ks)[i] = ks[i].toWKind := by simp [wk]
  have ht : i - (i - 1) < ((ks.drop (i - 1)).take r).length := by simp; omega
  have hst : ((ks.drop (i - 1)).take r)[i - (i - 1)] = ks[i] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1; omega
  have hcE : shC (fun p => (fun _ => 0) p + off (wcs (wk ks)) i p) c0 =
      shC (off (wt ks) (i - 1)) (shC (off (wt ((ks.drop (i - 1)).take r)) (i - (i - 1))) c0) := by
    rw [shC_shC]; congr 1; funext p
    have e1 := off_wt_split ks (i - 1) (i - (i - 1)) p
    rw [show i - 1 + (i - (i - 1)) = i by omega] at e1
    have e2 := off_wt_take (ks.drop (i - 1)) r (i - (i - 1)) p (by omega)
    show 0 + off (wt ks) i p = _
    omega
  have hws : wk ((ks.drop (i - 1)).take r) = ((wk ks).drop (i - 1)).take r := by rw [wk_take, wk_drop]
  have hL : ∀ n (h : n < (uclT (wk ((ks.drop (i - 1)).take r)) (fun _ => 0)).length),
      (uclT (wk ks) (fun _ => 0))[ncl ((wk ks).take (i - 1)) + n]? =
        some (shC (off (wt ks) (i - 1)) (uclT (wk ((ks.drop (i - 1)).take r)) (fun _ => 0))[n]) := by
    intro n h
    have := uclT_win (wk ks) (i - 1) r n (by rw [← hws]; exact h)
    rw [← hws] at this
    rw [this, List.getElem?_eq_getElem h]
    rfl
  have ht0 : i - (i - 1) = 0 → ∀ u, off (wt ks) (i - 1) u = 0 := by
    intro h u
    have : i = 0 := by omega
    subst this
    exact off_zero _ _
  have hc0' : c0 ∈ ks[i].cl := by rw [hwi] at hc0; exact hc0
  have hW' := hW i hi' ht c0 (by rw [hst]; exact hc0') hg
  rw [hcE]
  rcases hW' with hp | ⟨cs, hcs, hch⟩
  · left
    exact gateProof_window (sep_win 0 ks (i - 1) r) (wsep_dom 0 ks (i - 1) r) s0 _ _ _ _ _ hL _
      (fun u hu => hsw i hi' _ (by rw [← hst]; exact List.getElem_mem ht) c0 hc0' u hu) ht0 hp
  · right
    refine ⟨cs.map (shC (off (wt ks) (i - 1))), fun c' hc' => ?_,
      chainOK_window (sep_win 0 ks (i - 1) r) (wsep_dom 0 ks (i - 1) r) cs _ hch⟩
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hm, hgp⟩ := hcs c'' hc''
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨j, hj, c1, hc1, heq⟩ := mem_uclT _ _ _ hm
    have hj' : j < ((ks.drop (i - 1)).take r).length := by simpa [wk] using hj
    have hwj : (wk ((ks.drop (i - 1)).take r))[j] = ((ks.drop (i - 1)).take r)[j].toWKind := by simp [wk]
    rw [hwj] at hc1
    exact ⟨List.mem_iff_getElem?.mpr ⟨_, hL n hn⟩,
      gateProof_window (sep_win 0 ks (i - 1) r) (wsep_dom 0 ks (i - 1) r) s0 _ _ _ _ _ hL _
        (fun u hu => hsw i hi' _ (List.getElem_mem hj') c1 hc1 u (by rw [heq] at hu; exact hu)) ht0 hgp⟩

/-- **`hGC` of the long certificate, for every word, from the window checks**: the claims of window `i` are checked
in the sub-word of `r ≥ 2` kinds from window `i - 1` (from window 0 when `i = 0`), whose start state is the long start
state `s0` flipped by the parities of the event counts before it. -/
theorem gc_unroll (N : TNet α) (dat : α → Bool) (r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α)) (s0 : α → Bool)
    (hW : ∀ i, i < ks.length →
      GcWin N dat (st s0 (off (wt ks) (i - 1))) ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), N.gate c.z = true →
      GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk ks) (fun _ => 0) ∧
        GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c') ∧ ChainOK (LSep ks) c cs :=
  gc_unroll_gen N dat r hr ks s0 (fun i => st s0 (off (wt ks) (i - 1))) (fun _ _ _ _ _ _ _ _ => rfl) hW

/-- **`hGC` of the long certificate, for every word, from checks on the sub-words alone**: as `gc_unroll`, but each
sub-word is checked with its FIRST kind's own start state (`WKind.s0`), which is the long start state there by
`UnrollData.st_off` when the kinds' start states chain (`StChain Dv`, the first kind's agreeing with `s0`) on a set
`Dv` holding every pin of every claim node of every kind. Each check `GcWin` is then a property of the sub-word and
`t` only, so finitely many for finitely many kinds. -/
theorem gc_unroll_kind (N : TNet α) (dat : α → Bool) (r : Nat) (hr : 2 ≤ r) (ks : List (WKindT α)) (s0 : α → Bool)
    (Dv : List α) (hDv : ∀ w ∈ ks, ∀ c0 ∈ w.cl, ∀ u ∈ N.pins c0.z, u ∈ Dv) (hSC : StChain Dv (wk ks))
    (hhd : ∀ w, (wk ks).head? = some w → ∀ u ∈ Dv, w.s0 u = s0 u)
    (hW : ∀ i (hi : i < ks.length), GcWin N dat (ks[i - 1]'(by omega)).s0 ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), N.gate c.z = true →
      GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk ks) (fun _ => 0) ∧
        GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c') ∧ ChainOK (LSep ks) c cs := by
  refine gc_unroll_gen N dat r hr ks s0 (fun i u => match ks[i - 1]? with | some w => w.s0 u | none => s0 u) ?_ ?_
  · intro i hi w hw c0 hc0 u hu
    have hi1 : i - 1 < ks.length := by omega
    simp only [List.getElem?_eq_getElem hi1]
    have hwk : (wk ks)[i - 1]? = some ks[i - 1].toWKind := by simp [wk, hi1]
    exact (st_off Dv (wk ks) s0 hSC hhd (i - 1) _ hwk u (hDv w (mem_sub hw) c0 hc0 u hu)).symm
  · intro i hi
    have hi1 : i - 1 < ks.length := by omega
    simp only [List.getElem?_eq_getElem hi1]
    exact hW i hi
/-! ## The initial claims `hInit` and the environment claims `hEnvC` -/

section init
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat}

/-- A claim with a start event and a nonnegative start delay holds up to `t0` trivially: no event has happened. -/
theorem holds_init_start (c : Claim α) (hA : c.A ≠ none) (ha : 0 ≤ c.a) : ∀ s, s ≤ t0 → Holds x t0 H c s := by
  intro s hs _ hA' _
  cases hc : c.A with
  | none => exact absurd hc hA
  | some e =>
    simp only [hc, hbI] at hA'
    obtain ⟨h0, hlt⟩ := hA'
    rw [cnt_le_t0 (x := x) (t0 := t0) e.1 _ (by omega)] at hlt
    omega

/-- A claim on an exact node whose value is the node's value at `t0` holds up to `t0` (the node is quiet before). -/
theorem holds_init_quiet (hb : TBehX N dat envEn x r t0 H) (c : Claim α) (hd : dat c.z = false)
    (hv : x c.z t0 = c.val) : ∀ s, s ≤ t0 → Holds x t0 H c s :=
  fun s hs hH _ _ => by rw [hb.quiet c.z s hd hH hs]; exact hv

/-- **`hInit` for every word, from a per-kind check**: every claim of every kind has a start event and a nonnegative
start delay, except claims of the FIRST window, which must hold up to `t0` themselves (e.g. by `holds_init_quiet`).
The start state enters `hInit` only through such claims; a claim without a start event in a later window would have
to hold before `t0` with no event to anchor it, which this check excludes. -/
theorem init_unroll (ks : List (WKindT α))
    (h : ∀ i (hi : i < ks.length), ∀ c0 ∈ ks[i].cl,
      (c0.A ≠ none ∧ 0 ≤ c0.a) ∨ (i = 0 ∧ ∀ s, s ≤ t0 → Holds x t0 H c0 s)) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), ∀ s, s ≤ t0 → Holds x t0 H c s := by
  intro c hc
  obtain ⟨i, hi, c0, hc0, rfl⟩ := mem_uclT (wk ks) _ c hc
  have hi' : i < ks.length := by simpa [wk] using hi
  have hwi : (wk ks)[i] = ks[i].toWKind := by simp [wk]
  rw [hwi] at hc0
  rcases h i hi' c0 hc0 with ⟨hA, ha⟩ | ⟨rfl, hH⟩
  · exact holds_init_start _ (by simpa [shC] using hA) ha
  · rw [shC_zero (fun u => by simp [off_zero])]
    exact hH

/-- **`hEnvC` for every word, window by window**: for any premise `Q` (in `timedA_follows_unroll`, the ideal
condition on `CFu`), the environment claims of the long list are the windows' environment claims shifted by the
window offsets. This only restates `hEnvC` per window: whether an environment claim holds is a property of the run. -/
theorem env_unroll (ks : List (WKindT α)) (Q : Nat → Prop)
    (h : ∀ i (hi : i < ks.length), ∀ c0 ∈ ks[i].cl, N.gate c0.z = false → ∀ s, Q s →
      Holds x t0 H (shC (off (wt ks) i) c0) s) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), N.gate c.z = false → ∀ s, Q s → Holds x t0 H c s := by
  intro c hc hg s hs
  obtain ⟨i, hi, c0, hc0, rfl⟩ := mem_uclT (wk ks) _ c hc
  have hi' : i < ks.length := by simpa [wk] using hi
  have hwi : (wk ks)[i] = ks[i].toWKind := by simp [wk]
  rw [hwi] at hc0
  have e : (fun p => (fun _ => 0) p + off (wcs (wk ks)) i p) = off (wt ks) i := by funext p; simp; rfl
  rw [e]
  exact h i hi' c0 hc0 hg s hs

/-- **`hEnvC` holds vacuously** when no kind has a claim on a non-gate node. -/
theorem env_none (ks : List (WKindT α)) (Q : Nat → Prop) (h : ∀ w ∈ ks, ∀ c0 ∈ w.cl, N.gate c0.z = true) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), N.gate c.z = false → ∀ s, Q s → Holds x t0 H c s := by
  intro c hc hg
  obtain ⟨i, hi, c0, hc0, rfl⟩ := mem_uclT (wk ks) _ c hc
  have hi' : i < ks.length := by simpa [wk] using hi
  have hwi : (wk ks)[i] = ks[i].toWKind := by simp [wk]
  rw [hwi] at hc0
  have := h ks[i] (List.getElem_mem hi') c0 hc0
  simp only [shC] at hg
  rw [this] at hg
  cases hg

end init

/-! ## The timed theorems with the claim hypotheses reduced -/

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {D : α → List α}

/-- **`timedA_follows` for the certificate of every word, claim proofs and initial claims from window checks**:
`UnrollRest.timedA_follows_unroll` with `hGC` replaced by the window checks `GcWin` on the sub-words
`((wP ks).drop (i - 1)).take r'` (start state: the long start state flipped by the event-count parities before the
sub-word) and `hInit` by the per-kind check of `init_unroll`. -/
theorem timedA_follows_unrollC (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGW : ∀ i, i < (wP ks).length → GcWin N dat (st (fun w => x w t0) (off (wt (wP ks)) (i - 1)))
      (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hIk : ∀ i (hi : i < (wP ks).length), ∀ c0 ∈ (wP ks)[i].cl,
      (c0.A ≠ none ∧ 0 ≤ c0.a) ∨ (i = 0 ∧ ∀ s, s ≤ t0 → Holds x t0 H c0 s)) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N (CPu BIG ks) x t0 r v s) ∧
      (∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 (LSep (wP ks)) t :=
  timedA_follows_unroll BIG r' hr ks Dc hKP hKF hcD hBC hS hU hT hG hL hRTk hSEk hDLk hb hDE hloc hEnvE hgdF
    (gc_unroll N dat r' hr (wP ks) (fun w => x w t0) hGW) hEnvC (init_unroll (wP ks) hIk)

/-- **`timedA_live` for the certificate of every word, claim proofs and initial claims from window checks**:
`UnrollRest.timedA_live_unroll` with `hGC` and `hInit` replaced as in `timedA_follows_unrollC`. -/
theorem timedA_live_unrollC (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hSubk : ∀ w ∈ ks, KindSub w) (hNek : ∀ w ∈ ks, KindNe w)
    (U : List α) (hCovk : ∀ w ∈ ks, ∀ u, 0 < w.len u → u ∈ U)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGW : ∀ i, i < (wP ks).length → GcWin N dat (st (fun w => x w t0) (off (wt (wP ks)) (i - 1)))
      (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hIk : ∀ i (hi : i < (wP ks).length), ∀ c0 ∈ (wP ks)[i].cl,
      (c0.A ≠ none ∧ 0 ≤ c0.a) ∨ (i = 0 ∧ ∀ s, s ≤ t0 → Holds x t0 H c0 s))
    (K : α → Nat) (hK : ∀ v, N.gate v = true → 1 ≤ K v ∧ ∀ w ∈ N.pins v, N.hi v w < K v)
    (henv : ∀ u t, N.gate u = false → dat u = false → t0 ≤ t → Enabled (CFu BIG ks) (fun w => cntE dat x t0 w t) u →
      ∃ t', t < t' ∧ cnt x t0 u t < cnt x t0 u t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cntE dat x t0 u T = (CFu BIG ks).len u) ∧ ∀ u s, dat u = false → T ≤ s → x u s = x u T :=
  timedA_live_unroll BIG r' hr ks Dc hKP hKF hcD hBC hS hU hT hG hL hRTk hSEk hDLk hSubk hNek U hCovk hb hDE hloc
    hEnvE hgdF (gc_unroll N dat r' hr (wP ks) (fun w => x w t0) hGW) hEnvC (init_unroll (wP ks) hIk) K hK henv

end main

end Formal.Net.AO
