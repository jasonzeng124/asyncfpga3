import Formal.Cells.CovUpGC

/-!
# Formal.Cells.CovUpChunk — the claim check `hgcB` with indexed claim lookup, split into ranges (shard B, 2026-11-10)

**Problem, plainly.** `CovUpGC.hgcB` (and C's `valB`, `covWin`) read claims as `cl[i]?` on a `List`; in the kernel
that costs O(i) per lookup, so a certificate with ~80k claims needs ~10^9 steps, and the whole check is one `decide`.
Can the same hypothesis `hGC` of `CovUpMain.timedA_follows_cu` be obtained from checks that look claims up through a
faster structure and are split into many small `decide`s?

**Proved.**
* `getC`, `getC_eq`: a claim list stored as chunks of `C` claims (all chunks but the last full, none longer) is looked up in
  O(#chunks + C) steps, and agrees with `cl[i]?` on the flattened list.
* `covWinF`, `valBF`, `gateProofUBF`, `chainIdsF`: C's / B's Boolean checks with claim lookup by any function `get`;
  equal to the List versions when `get i = cl[i]?` for all `i` (`valBF_eq`, `gateProofUBF_eq`).
* `claimOKF` (one claim, with its hint looked up by `hget`) and `hgc_of_claimOKF`: if every index below
  `cl.length` passes `claimOKF` (checked in ranges, `rangeOK`, one `decide` each: `hgc_of_ranges`), then the hGC
  premise of `timedA_follows_cu` holds.

**Not shown here:** any instance.
-/

namespace Formal.Cells.CovUpChunk
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX
  Formal.Net.AO Formal.Cells.UnionUp Formal.Cells.UnionUpDec Formal.Cells.CovUp Formal.Cells.CovUpDec
  Formal.Cells.CovUpGC

variable {α : Type} [DecidableEq α]

/-- Lookup in a chunked list. -/
def getC {β : Type} (C : Nat) (chs : List (List β)) (i : Nat) : Option β := (chs.getD (i / C) [])[i % C]?

theorem getC_eq {β : Type} {C : Nat} (hC : 0 < C) :
    ∀ (chs : List (List β)), (∀ k, k + 1 < chs.length → (chs.getD k []).length = C) →
      (∀ k, (chs.getD k []).length ≤ C) → ∀ i, getC C chs i = chs.flatten[i]?
  | [], _, _, i => by simp [getC]
  | ch :: chs, h, hle, i => by
    by_cases hi : i < C
    · have hd : i / C = 0 := Nat.div_eq_of_lt hi
      have hm : i % C = i := Nat.mod_eq_of_lt hi
      simp only [getC, hd, hm, List.getD_cons_zero, List.flatten_cons]
      by_cases hl : chs = []
      · subst hl; simp
      · have hlen : ch.length = C := by
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
          have := h 0 (by simp)
          simpa using this
        rw [List.getElem?_append_left (by omega)]
    · have hlen : ch.length = C ∨ chs = [] := by
        by_cases hl : chs = []
        · exact Or.inr hl
        · left
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
          have := h 0 (by simp); simpa using this
      have ih := getC_eq hC chs (fun k hk => by have := h (k + 1) (by simp; omega); simpa using this)
        (fun k => by have := hle (k + 1); simpa using this) (i - C)
      have hd : i / C = (i - C) / C + 1 := by
        have : i = (i - C) + C := by omega
        rw [this, Nat.add_div_right _ hC]; simp
      have hm : i % C = (i - C) % C := by
        have : i = (i - C) + C := by omega
        rw [this, Nat.add_mod_right]; simp
      simp only [getC, hd, hm, List.getD_cons_succ, List.flatten_cons] at ih ⊢
      rcases hlen with hlen | hl
      · rw [List.getElem?_append_right (by omega), hlen]; exact ih
      · subst hl
        have h0 := hle 0
        simp only [List.getD_cons_zero] at h0
        simp only [List.getD_nil, List.getElem?_nil, List.flatten_nil, List.append_nil]
        rw [List.getElem?_eq_none (by omega)]

section
variable (N : TNet α) (dat : α → Bool) (sl : List (α × Nat × α × Nat × Nat))
  (ul : List ((α × Nat) × (α × Nat) × Nat)) (s0 : α → Bool) (get : Nat → Option (Claim α))

def covWinF (u : α) : Cov → Option (Claim α)
  | .ex k => some ⟨u, xor (s0 u) (k % 2 == 1), (if k = 0 then none else some (u, k - 1)), 0, some (u, k), 0⟩
  | .cl i => get i
  | .X => none

def valBF (c : Claim α) (cov : α → Cov) : Bool :=
  (allBools (N.pins c.z).length).all fun bs =>
    !((N.pins c.z).all fun u => match covWinF s0 get u (cov u) with
      | some w => asg (N.pins c.z) bs u == w.val | none => true) ||
    (N.F c.z ((N.pins c.z).map (asg (N.pins c.z) bs)) == c.val)

def gateProofUBF (c : Claim α) (cov : α → Cov) : Bool :=
  N.gate c.z && decide (0 ≤ c.a) && valBF N s0 get c cov &&
  (N.pins c.z).all fun u =>
    (match covWinF s0 get u (cov u) with
      | some w => covTimeUB (sepL sl) (upL ul) c w (N.hi c.z u) (N.lo c.z u)
      | none => true) &&
    (match cov u with
      | .ex _ => !dat u
      | .cl i => (match get i with | some w => w.z == u | none => true)
      | .X => true)
end

section eq
variable {N : TNet α} {dat : α → Bool} {sl : List (α × Nat × α × Nat × Nat)}
  {ul : List ((α × Nat) × (α × Nat) × Nat)} {s0 : α → Bool} {get : Nat → Option (Claim α)} {cl : List (Claim α)}

theorem covWinF_eq (hget : ∀ i, get i = cl[i]?) (u : α) (k : Cov) : covWinF s0 get u k = covWin s0 cl u k := by
  cases k <;> simp [covWinF, covWin, hget]

theorem covWinF_fun (hget : ∀ i, get i = cl[i]?) : covWinF s0 get = covWin s0 cl :=
  funext fun u => funext fun k => covWinF_eq hget u k

theorem valBF_eq (hget : ∀ i, get i = cl[i]?) (c : Claim α) (cov : α → Cov) :
    valBF N s0 get c cov = valB N cl s0 c cov := by
  unfold valBF valB; rw [covWinF_fun hget]; rfl

theorem gateProofUBF_eq (hget : ∀ i, get i = cl[i]?) (c : Claim α) (cov : α → Cov) :
    gateProofUBF N dat sl ul s0 get c cov = gateProofUB N dat (sepL sl) (upL ul) s0 cl c cov := by
  have hv := valBF_eq (N := N) (s0 := s0) hget c cov
  have hf := covWinF_fun (s0 := s0) hget
  have hg : get = fun i => cl[i]? := funext hget
  unfold gateProofUBF gateProofUB; rw [hv, hf, hg]; rfl
end eq

section
variable (N : TNet α) (dat : α → Bool) (sl : List (α × Nat × α × Nat × Nat))
  (ul : List ((α × Nat) × (α × Nat) × Nat)) (s0 : α → Bool) (get : Nat → Option (Claim α))
  (hget : Nat → Option (GHint α))

/-- Claim `j` is gate-proved by its hint (lookup version of `CovUpGC.gpOK`). -/
def gpOKF (j : Nat) : Bool :=
  match hget j, get j with
  | some (.gp covL), some c => gateProofUBF N dat sl ul s0 get c (covOf covL)
  | _, _ => false

/-- The check of one claim index. -/
def claimOKF (i : Nat) : Bool :=
  match get i with
  | none => true
  | some c => !N.gate c.z || (match hget i with
    | some (.gp covL) => gateProofUBF N dat sl ul s0 get c (covOf covL)
    | some (.ch ids) => ids.all (gpOKF N dat sl ul s0 get hget) && chainUpB sl ul c (ids.filterMap get)
    | none => false)

/-- A range of claim indices `[lo, lo + n)`. -/
def rangeOK (lo n : Nat) : Bool := (List.range' lo n).all (claimOKF N dat sl ul s0 get hget)
end

theorem hgc_of_claimOKF {N : TNet α} {dat : α → Bool} {sl : List (α × Nat × α × Nat × Nat)}
    {ul : List ((α × Nat) × (α × Nat) × Nat)} {s0 : α → Bool} {get : Nat → Option (Claim α)}
    {hget : Nat → Option (GHint α)} {cl : List (Claim α)} (hnd : ∀ v, (N.pins v).Nodup)
    (hg : ∀ i, get i = cl[i]?) (h : ∀ i, i < cl.length → claimOKF N dat sl ul s0 get hget i = true) :
    ∀ c ∈ cl, N.gate c.z = true → GateProofU N dat (sepL sl) (upL ul) s0 cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProofU N dat (sepL sl) (upL ul) s0 cl c') ∧
        ChainUpOK (sepL sl) (upL ul) c cs := by
  intro c hc hgz
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have hci' : get i = some c := by rw [hg, List.getElem?_eq_getElem hi, hci]
  have hall := h i hi
  unfold claimOKF at hall
  rw [hci'] at hall
  simp only [hgz, Bool.not_true, Bool.false_or] at hall
  cases hh : hget i with
  | none => rw [hh] at hall; cases hall
  | some g =>
    rw [hh] at hall
    cases g with
    | gp covL =>
      dsimp only at hall
      rw [gateProofUBF_eq hg] at hall
      exact Or.inl (gateProofU_of_B N dat _ _ s0 cl c _ (hnd c.z) hall)
    | ch ids =>
      simp only [Bool.and_eq_true, List.all_eq_true] at hall
      obtain ⟨hids, hch⟩ := hall
      refine Or.inr ⟨ids.filterMap get, ?_, ?_⟩
      · intro c' hc'
        obtain ⟨j, hj, hjc⟩ := List.mem_filterMap.1 hc'
        have hok := hids j hj
        unfold gpOKF at hok
        cases hh2 : hget j with
        | none => rw [hh2] at hok; cases hok
        | some g2 =>
          cases g2 with
          | ch _ => rw [hh2] at hok; cases hok
          | gp covL2 =>
            rw [hh2, hjc] at hok
            dsimp only at hok
            rw [gateProofUBF_eq hg] at hok
            have hjm : c' ∈ cl := by
              rw [hg] at hjc; exact List.mem_of_getElem? hjc
            exact ⟨hjm, gateProofU_of_B N dat _ _ s0 cl c' _ (hnd c'.z) hok⟩
      · exact chainUpB_sound sl ul _ c hch

/-- Ranges covering `[0, cl.length)` suffice. -/
theorem hgc_of_ranges {N : TNet α} {dat : α → Bool} {sl : List (α × Nat × α × Nat × Nat)}
    {ul : List ((α × Nat) × (α × Nat) × Nat)} {s0 : α → Bool} {get : Nat → Option (Claim α)}
    {hget : Nat → Option (GHint α)} {cl : List (Claim α)} (hnd : ∀ v, (N.pins v).Nodup)
    (hg : ∀ i, get i = cl[i]?) (rs : List (Nat × Nat)) (hcov : ∀ i, i < cl.length → ∃ r ∈ rs, r.1 ≤ i ∧ i < r.1 + r.2)
    (hr : rs.all (fun r => rangeOK N dat sl ul s0 get hget r.1 r.2) = true) :
    ∀ c ∈ cl, N.gate c.z = true → GateProofU N dat (sepL sl) (upL ul) s0 cl c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ cl ∧ GateProofU N dat (sepL sl) (upL ul) s0 cl c') ∧
        ChainUpOK (sepL sl) (upL ul) c cs := by
  apply hgc_of_claimOKF hnd hg
  intro i hi
  obtain ⟨r, hrm, h1, h2⟩ := hcov i hi
  have := List.all_eq_true.1 hr r hrm
  unfold rangeOK at this
  exact List.all_eq_true.1 this i (List.mem_range'_1.2 ⟨h1, h2⟩)

end Formal.Cells.CovUpChunk
