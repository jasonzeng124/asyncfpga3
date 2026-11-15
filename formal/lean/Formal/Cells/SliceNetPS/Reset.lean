import Formal.Cells.SliceNetPS.TBeh
import Formal.Net.CViewPS.RIslAll

/-!
# Formal.Cells.SliceNetPS.Reset — `TBehX` on THE target with the `quiet` field derived (shard B, 2026-11-15)

**Problem, plainly.** `target_tbehX` gives C's timed-net behaviour hypothesis `TBehX` on THE target's slice nets
`tnPS p c1 c2`, except for two fields left as premises: `quiet` (the nodes a certificate tracks exactly do not move
during `[t0 - H, t0]`) and `env` (each change of an exactly tracked non-gate node is allowed by the certificate's
environment rule `envEn`). Can `quiet` be derived for a concrete exact set, from THE statement's own hypotheses?

**Proved.**
* `quiet_reset`: take as exact set the 3,224 nodes of C's reset island (`memR`) plus the six environment-driven
  boundary nodes (reset, the input requests of `a`, `b`, `start`, the acknowledges of `out0`, `pend`), every other
  node data (`datR`). In every behaviour of THE theorem's circuit (any sane `p`) whose environment obeys H_ENV
  (`Env`, any `R su Δo n va vb`), every exact node is constant on `[t0 - H, t0]` for every
  `t0 ≤ R - 1` with `⌈(1+κ)g⌉·(19,832 + 15·4,636) + H ≤ t0` and every `H`. (Island: C's `reset_quiet_all`;
  boundary nodes: `Env` keeps reset high and those requests/acknowledges low up to `R`.)
* `env_island`: every island member is a gate of `tnPS`, so TBehX's `env` field constrains only the six boundary
  nodes (`env_of_bnd`).
* `target_tbehX_reset` (κ < 1): with `H = ⌈(1+κ)g⌉·33,002` and `t0` as above (e.g. `t0 = R - 1` for any reset
  `R ≥ 1 + ⌈(1+κ)g⌉·122,374` ps, 122.4 ns at g = 1, κ = 0; the board's reset is far longer): there is a corner `c`
  such that on every slice `[c1, c2] ∋ c` and for every `envEn` that allows the boundary nodes' moves after `t0`,
  `TBehX (tnPS p c1 c2) datR envEn x r t0 H` holds for some read times `r`. The only premise left is about the
  six environment nodes and the certificate's own `envEn`.

**Not shown.** Any certificate with this exact set; that `datR` is the exact set a certificate needs (a certificate
may want more exact nodes, e.g. A's `IslR`, whose quietness at `t0` would need its own argument); anything after `t0`.
-/

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Net.CViewPS Formal.Net.OccNet
  Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Cells.CornerSlice Formal.Cells.StartBound
  Formal.Cells.StartBoundPS

/-- The six environment-driven boundary nodes of THE target. -/
def bndEnv : List Nat :=
  [boundary.rst, boundary.a.req, boundary.b.req, boundary.start.req, boundary.out0.ack, boundary.pend.ack]

/-- Data marking: exact = reset island or an environment-driven boundary node. -/
def datR (u : Nat) : Bool := !(memR u || bndEnv.contains u)

theorem cp_eq_mOf (p : DelayPar) : Cp p = mOf p := rfl

/-- Every environment-driven boundary node is constant on `[0, R - 1]` under H_ENV. -/
theorem bnd_quiet {x : Beh} {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat}
    (he : Env x boundary R su Δo n va vb) {u : Nat} (hu : u ∈ bndEnv) :
    ∀ s t, s ≤ R - 1 → t ≤ R - 1 → 0 < R → x u s = x u t := by
  obtain ⟨hr, _, _, ha, hb, hs, ho, hpd⟩ := he
  intro s t hs' ht' hR
  simp only [bndEnv, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hr s (by omega), hr t (by omega)]
  · rw [ha.1 s (by omega), ha.1 t (by omega)]
  · rw [hb.1 s (by omega), hb.1 t (by omega)]
  · rw [hs.1 s (by omega), hs.1 t (by omega)]
  · rw [ho.1 s (by omega), ho.1 t (by omega)]
  · rw [hpd.1 s (by omega), hpd.1 t (by omega)]

/-- **`quiet` for the reset exact set.** -/
theorem quiet_reset {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat} (he : Env x boundary R su Δo n va vb)
    (t0 H : Nat) (hlo : Cp p * A2 + 15 * (Cp p * M2) + H ≤ t0) (hhi : t0 ≤ R - 1) :
    ∀ u s, datR u = false → t0 ≤ s + H → s ≤ t0 → x u s = x u t0 := by
  have hC : 0 < Cp p := by
    obtain ⟨hk0, hk1, hg⟩ := hp
    unfold Cp
    have : (0 : ℚ) < (1 + p.κ) * p.g := by positivity
    have : (0 : ℤ) < ⌈(1 + p.κ) * p.g⌉ := Int.ceil_pos.mpr this
    omega
  have hA : 0 < Cp p * A2 := Nat.mul_pos hC (by decide)
  have hR0 : 0 < R := by omega
  have hrst : ∀ t, t < R → x rstPS t = true := fun t ht => he.1 t ht
  intro u s hu h1 h2
  simp only [datR, Bool.not_eq_false', Bool.or_eq_true, List.contains_iff_mem] at hu
  rcases hu with hm | hbn
  · have q := reset_quiet_all hp hb R hrst hR0 u hm
    rw [q s (by omega) (by omega), q t0 (by omega) hhi]
  · exact bnd_quiet he hbn s t0 (by omega) hhi hR0

/-- Every reset-island member is a gate of every slice net. -/
theorem env_island {p : DelayPar} {c1 c2 : ℚ} {u : Nat} (hu : memR u = true) : (tnPS p c1 c2).gate u = true := by
  have h := (rentry_facts hu).1
  show logicB u = true
  exact logicB_iff.mpr h

/-- TBehX's `env` field for `datR` reduces to the six boundary nodes. -/
theorem env_of_bnd {p : DelayPar} {c1 c2 : ℚ} {x : Beh} {t0 : Nat} {envEn : Nat → (Nat → Bool) → Bool}
    (h : ∀ u ∈ bndEnv, ∀ t, (tnPS p c1 c2).gate u = false → t0 < t → x u t ≠ x u (t - 1) →
      envEn u (fun w => x w (t - 1)) = true) :
    ∀ u t, (tnPS p c1 c2).gate u = false → datR u = false → t0 < t → x u t ≠ x u (t - 1) →
      envEn u (fun w => x w (t - 1)) = true := by
  intro u t hg hd ht hx
  simp only [datR, Bool.not_eq_false', Bool.or_eq_true, List.contains_iff_mem] at hd
  rcases hd with hm | hbn
  · rw [env_island hm] at hg; exact absurd hg (by decide)
  · exact h u hbn t hg ht hx

/-- **TBehX on THE target's slice nets with the reset exact set; `quiet` derived.** -/
theorem target_tbehX_reset {p : DelayPar} (hp : Sane p) (hk : p.κ < 1) {x : Beh}
    (hb : Behaves p (circuit net boundary) x)
    {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat} (he : Env x boundary R su Δo n va vb) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (c1 c2 : ℚ) (t0 : Nat) (envEn : Nat → (Nat → Bool) → Bool),
      c1 ≤ c → c ≤ c2 → 0 ≤ c1 → c2 ≤ 1 →
      Cp p * A2 + 15 * (Cp p * M2) + mOf p * HB ≤ t0 → t0 ≤ R - 1 →
      (∀ u ∈ bndEnv, ∀ t, (tnPS p c1 c2).gate u = false → t0 < t → x u t ≠ x u (t - 1) →
        envEn u (fun w => x w (t - 1)) = true) →
      ∃ r, TBehX (tnPS p c1 c2) datR envEn x r t0 (mOf p * HB) := by
  obtain ⟨c, hc0, hc1, h⟩ := target_tbehX hp hk hb
  refine ⟨c, hc0, hc1, fun c1 c2 t0 envEn h1 h2 h0 hc2 hlo hhi henv => ?_⟩
  have h2H : 2 * (mOf p * HB) ≤ t0 := by
    rw [← cp_eq_mOf] at hlo ⊢
    have : 2 * (Cp p * HB) ≤ Cp p * A2 + 15 * (Cp p * M2) := by
      have e1 : 2 * (Cp p * HB) = Cp p * 66004 := by unfold HB; ring
      have e2 : Cp p * A2 + 15 * (Cp p * M2) = Cp p * 89372 := by unfold A2 M2; ring
      rw [e1, e2]; exact Nat.mul_le_mul_left _ (by decide)
    omega
  exact h c1 c2 t0 datR envEn h1 h2 h0 hc2 h2H (quiet_reset hp hb he t0 _ hlo hhi) (env_of_bnd henv)

/-- Every exact node has its reset value `valR` (the island's listed value; `true` for the reset node, `false` for
the other five boundary nodes) on the whole quiet window. -/
theorem val_reset {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat} (he : Env x boundary R su Δo n va vb)
    (u : Nat) (hu : datR u = false) (t : Nat) (hlo : Cp p * A2 + 15 * (Cp p * M2) ≤ t) (hhi : t ≤ R - 1) :
    x u t = valR u := by
  have hC : 0 < Cp p := by
    obtain ⟨hk0, hk1, hg⟩ := hp
    unfold Cp
    have : (0 : ℚ) < (1 + p.κ) * p.g := by positivity
    have : (0 : ℤ) < ⌈(1 + p.κ) * p.g⌉ := Int.ceil_pos.mpr this
    omega
  have hA : 0 < Cp p * A2 := Nat.mul_pos hC (by decide)
  have hR0 : 0 < R := by omega
  simp only [datR, Bool.not_eq_false', Bool.or_eq_true, List.contains_iff_mem] at hu
  rcases hu with hm | hbn
  · exact reset_quiet_all hp hb R (fun t ht => he.1 t ht) hR0 u hm t hlo hhi
  · obtain ⟨hr, _, _, ha, hb', hs, ho, hpd⟩ := he
    have hbv : boundary.rst = rstPS ∧ boundary.a.req = 186985 ∧ boundary.b.req = 186985 ∧
        boundary.start.req = 186985 ∧ boundary.out0.ack = 154859 ∧ boundary.pend.ack = 104477 :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hv : valR 186985 = false ∧ valR 154859 = false ∧ valR 104477 = false ∧ valR rstPS = true := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel
    simp only [bndEnv, List.mem_cons, List.not_mem_nil, or_false] at hbn
    rcases hbn with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hr t (by omega), hbv.1, hv.2.2.2]
    · rw [ha.1 t (by omega), hbv.2.1, hv.1]
    · rw [hb'.1 t (by omega), hbv.2.2.1, hv.1]
    · rw [hs.1 t (by omega), hbv.2.2.2.1, hv.1]
    · rw [ho.1 t (by omega), hbv.2.2.2.2.1, hv.2.1]
    · rw [hpd.1 t (by omega), hbv.2.2.2.2.2, hv.2.2.1]

/-- **The certificate's `hInit` premise** for every claim on an exact node that states its reset value. -/
theorem init_reset {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat} (he : Env x boundary R su Δo n va vb)
    (t0 H : Nat) (hlo : Cp p * A2 + 15 * (Cp p * M2) + H ≤ t0) (hhi : t0 ≤ R - 1)
    (c : Claim Nat) (hz : datR c.z = false) (hv : c.val = valR c.z) :
    ∀ s, s ≤ t0 → Holds x t0 H c s := by
  intro s hs h1 _ _
  rw [hv]
  exact val_reset hp hb he c.z hz s (by omega) (by omega)

end Formal.Cells.SliceNetPS
