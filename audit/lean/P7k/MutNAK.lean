import Formal.Cells.ArbA0Fork
import Formal.Cells.OnNetlistArb
import Formal.Cells.ArbCornersPin
import Formal.Core.Substrate.CornerNat

/-!
# Probe Bk1: the routed arbiter's A0 fork under shard A's corner model (κ)

Shard B. Notes: `formal/notes/B-arb-kappa.md`.

Bt3 (`OnNetlistArb`) found that the A0 fork of the routed `bd_arbiter` on the
four `link_arb` bitstreams is safe at one die corner and unsafe in the
independent box. This file decides the 8 seed x client pairs under A's
settled model (`Formal.Core.Substrate.CornerNat`): ONE shared corner `c` for
the die (H_SHARED_CORNER), each arc's nominal delay the interpolation of its
fast and slow endpoint (H_AFFINE), and each actual delay within `1 ± κ` of
that nominal (H_SCATTER κ, `Scat`).

The fork condition is 7g's exact one (`ArbA0Fork.no_early_ack_iff`,
rule J' with per-pin site pins and per-pin LUT arcs as in `ArbCornersPin`):
client k's ack never rises early iff
`wAC ≤ wSt + aSt + wQG + aG + wGC` (late A0 branch vs the chain through
ustate and ugrant), the shared A0 prefix `c` being ONE arc (one wire) that
cancels.

Two readings of the arc endpoints (both are instances of A's `CArc`):
* `lit`: A's literal H_ENDPOINTS, `F = FAST_MIN`, `S = SLOW_MAX` (+ Elmore on
  routes) for every arc. The prjxray within-corner min..max spread is then part
  of the scatter.
* `cons`: side-pessimistic endpoints: early arcs `(FAST_MIN, SLOW_MIN)`, the
  late arc `(FAST_MAX + Elmore, SLOW_MAX + Elmore)`. At κ = 0 this is Bt3's
  one-corner reading (with the shared-prefix credit); κ is scatter on top.

Per pair and reading (§3):
* `safe_*`: for every κ ≤ κ* (exact rational, from the binding endpoint), every
  corner, every assignment that `Scat`s, every run of 7g's gate relations is
  safe.
* `unsafe_*`: for every κ ≥ κ* + 6/(E+L) (one ps of rounding per fork arc,
  delays being whole ps), an assignment that `Scat`s at the binding endpoint
  on which the ack rises early on every run (runs exist).
Between the two (width ≤ 0.0057) the whole-ps model is not decided here.
§4: verdicts at rule A's 1/11 and rule E's / the guardband's 383/1927.
§5: the arc data is C's generated `pinDelay` and the SDF columns (decided).
-/

namespace Formal.Cells.OnNetlistArbKappa

open Formal.Core.Substrate
open Formal.Cells.ArbA0Fork

-- omega's certificates for the per-pair κ arithmetic (coefficients up to ~3700) recurse deeply.
set_option maxRecDepth 200000

/-! ## 1. The fork's arcs and the 7g record they give -/

/-- The timing arcs of one client's A0 handover (7g's `Dl` fields; the site
pins are folded into the route arcs, as in `OnNetlistArb.dl7g`).
`c` is the A0 prefix shared by both branches: ONE physical wire, so ONE arc
(and one delay) in A's model. -/
inductive Arc
  | c | wSt | aSt | wQf | wQG | aG | wGC | wAC | aC | wCf
  deriving DecidableEq, Repr

/-- The 7g delay record of a per-arc delay assignment. -/
def dlOf (d : Arc → Nat) : Dl :=
  { c := d .c, wSt := d .wSt, pSt := 0, aSt := d .aSt, wQf := d .wQf, pQf := 0,
    wQG := d .wQG, pQG := 0, aG := d .aG, wGC := d .wGC, pGC := 0, wAC := d .wAC,
    pAC := 0, aC := d .aC, wCf := d .wCf, pCf := 0 }

/-- The early chain A0 -> ustate -> q -> ugrant -> g_k -> ua_k (past the shared
prefix) as one corner-model arc (endpoints summed). -/
def earlyArc (A : Arc → CArc) : CArc :=
  CArc.add (A .wSt) (CArc.add (A .aSt) (CArc.add (A .wQG) (CArc.add (A .aG) (A .wGC))))

/-! ## 2. Generic: endpoint check gives safety; a gap gives a counter-instance -/

/-- Under A's corner model (one corner `c`, every arc within κ of its nominal
delay at `c`), the endpoint check of (late, early) gives 7g's exact fork
inequality `late ≤ early`. -/
theorem fork_le_of_endpoint {k : Kappa} {A : Arc → CArc}
    (h : EndpointOK k (A .wAC) (earlyArc A) 0) {c : Corner} {d : Arc → Nat}
    (hd : ∀ e, Scat k c (A e) (d e)) :
    d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC := by
  -- (A's `bundle_endpoints` gives the same; this core proof avoids its
  -- Mathlib-only step `endpoint_nom`.)
  have a1 := (hd .wSt).1
  have a2 := (hd .aSt).1
  have a3 := (hd .wQG).1
  have a4 := (hd .aG).1
  have a5 := (hd .wGC).1
  have b := (hd .wAC).2
  obtain ⟨hF, hS⟩ := h
  simp only [earlyArc, CArc.add, Nat.mul_zero, Nat.add_zero] at hF hS
  have m0 := Nat.mul_le_mul_left c.w0 hF
  have m1 := Nat.mul_le_mul_left c.w1 hS
  have key : k.den * c.W * d .wAC ≤
      k.den * c.W * (d .wSt + d .aSt + d .wQG + d .aG + d .wGC) := by
    simp only [nom, Nat.mul_add] at a1 a2 a3 a4 a5 b m0 m1 ⊢
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at a1 a2 a3 a4 a5 b m0 m1 ⊢
    omega
  exact Nat.le_of_mul_le_mul_left key (q_pos k c)

theorem safe1_of_le {d : Arc → Nat} (h : d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC) :
    Safe F1 G1 false (dlOf d) := fun _ _ _ _ _ R =>
  (client1_iff R).2 (by simp only [Dl.late, Dl.early, dlOf]; omega)

theorem safe2_of_le {d : Arc → Nat} (h : d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC) :
    Safe F2 G2 true (dlOf d) := fun _ _ _ _ _ R =>
  (client2_iff R).2 (by simp only [Dl.late, Dl.early, dlOf]; omega)

/-- If the late branch is slower, NO run is safe, and runs exist (loops positive). -/
theorem not_safe1 {d : Arc → Nat} (h : d .wSt + d .aSt + d .wQG + d .aG + d .wGC < d .wAC)
    (hq : 0 < d .aSt + d .wQf) (hc : 0 < d .aC + d .wCf) : ¬ Safe F1 G1 false (dlOf d) := by
  intro hs
  obtain ⟨a0, q, g, A, R⟩ := run_exists F1 G1 true (dlOf d) 1 F1_hold F1_go G1_vals.1
    (by decide) (by simp only [Dl.dQf, dlOf]; omega) (by simp only [Dl.dCf, dlOf]; omega)
  have := (client1_iff R).1 (hs 1 a0 q g A R)
  simp only [Dl.late, Dl.early, dlOf] at this
  omega

theorem not_safe2 {d : Arc → Nat} (h : d .wSt + d .aSt + d .wQG + d .aG + d .wGC < d .wAC)
    (hq : 0 < d .aSt + d .wQf) (hc : 0 < d .aC + d .wCf) : ¬ Safe F2 G2 true (dlOf d) := by
  intro hs
  obtain ⟨a0, q, g, A, R⟩ := run_exists F2 G2 false (dlOf d) 1 F2_hold F2_go G2_vals.1
    (by decide) (by simp only [Dl.dQf, dlOf]; omega) (by simp only [Dl.dCf, dlOf]; omega)
  have := (client2_iff R).1 (hs 1 a0 q g A R)
  simp only [Dl.late, Dl.early, dlOf] at this
  omega

/-- The counter-instance at an endpoint corner (value `v a` = the arc's F or S):
late at `⌊(1+κ)·v⌋`, early arcs at `⌈(1-κ)·v⌉`, the rest at nominal. -/
def wit (k : Kappa) (v : CArc → Nat) (A : Arc → CArc) : Arc → Nat
  | .wAC => k.hi * v (A .wAC) / k.den
  | .wSt => cdiv (k.lo * v (A .wSt)) k.den
  | .aSt => cdiv (k.lo * v (A .aSt)) k.den
  | .wQG => cdiv (k.lo * v (A .wQG)) k.den
  | .aG => cdiv (k.lo * v (A .aG)) k.den
  | .wGC => cdiv (k.lo * v (A .wGC)) k.den
  | e => v (A e)

theorem up_scat {k : Kappa} {c : Corner} {v : CArc → Nat}
    (hS : ∀ a d, Scat k c a d ↔ k.lo * v a ≤ k.den * d ∧ k.den * d ≤ k.hi * v a)
    {a : CArc} (hside : k.lo * v a + k.den ≤ k.hi * v a + 1) :
    Scat k c a (cdiv (k.lo * v a) k.den) := by
  rw [hS]
  have h1 := le_cdiv_mul (a := k.lo * v a) k.den_pos
  have h2 := cdiv_mul_le (a := k.lo * v a) k.den_pos
  have h3 := k.den_pos
  rw [Nat.mul_comm k.den]
  omega

theorem down_scat {k : Kappa} {c : Corner} {v : CArc → Nat}
    (hS : ∀ a d, Scat k c a d ↔ k.lo * v a ≤ k.den * d ∧ k.den * d ≤ k.hi * v a)
    {a : CArc} (hside : k.lo * v a + k.den ≤ k.hi * v a + 1) :
    Scat k c a (k.hi * v a / k.den) := by
  rw [hS]
  have h1 := Nat.div_mul_le_self (k.hi * v a) k.den
  have h2 := div_mul_add_gt (a := k.hi * v a) k.den_pos
  have h3 := k.den_pos
  rw [Nat.mul_comm k.den]
  omega

theorem nom_scat {k : Kappa} {c : Corner} {v : CArc → Nat}
    (hS : ∀ a d, Scat k c a d ↔ k.lo * v a ≤ k.den * d ∧ k.den * d ≤ k.hi * v a)
    (a : CArc) : Scat k c a (v a) := by
  rw [hS]
  exact ⟨Nat.mul_le_mul_right _ k.lo_le_den, Nat.mul_le_mul_right _ k.den_le_hi⟩

/-- **Generic counter-instance.** At a corner where `Scat` reads
`(1-κ)v ≤ d ≤ (1+κ)v`, if `(1+κ)·late ≥ (1-κ)·early + 6` (ps, times `den`;
the 6 absorbs one ps of rounding per arc of the fork) and every arc is long
enough for its rounded value to stay in its band (`hside`), then `wit`
realises the model and its late branch is strictly slower. -/
theorem counter_core {k : Kappa} {c : Corner} (v : CArc → Nat)
    (hS : ∀ a d, Scat k c a d ↔ k.lo * v a ≤ k.den * d ∧ k.den * d ≤ k.hi * v a)
    (A : Arc → CArc)
    (hgap : k.lo * v (A .wSt) + k.lo * v (A .aSt) + k.lo * v (A .wQG) + k.lo * v (A .aG) +
      k.lo * v (A .wGC) + 6 * k.den ≤ k.hi * v (A .wAC))
    (hside : ∀ e, k.lo * v (A e) + k.den ≤ k.hi * v (A e) + 1) :
    (∀ e, Scat k c (A e) (wit k v A e)) ∧
      wit k v A .wSt + wit k v A .aSt + wit k v A .wQG + wit k v A .aG + wit k v A .wGC <
        wit k v A .wAC := by
  refine ⟨?_, ?_⟩
  · intro e
    cases e
    · exact nom_scat hS _
    · exact up_scat hS (hside _)
    · exact up_scat hS (hside _)
    · exact nom_scat hS _
    · exact up_scat hS (hside _)
    · exact up_scat hS (hside _)
    · exact up_scat hS (hside _)
    · exact down_scat hS (hside _)
    · exact nom_scat hS _
    · exact nom_scat hS _
  · simp only [wit]
    have u1 := cdiv_mul_le (a := k.lo * v (A .wSt)) k.den_pos
    have u2 := cdiv_mul_le (a := k.lo * v (A .aSt)) k.den_pos
    have u3 := cdiv_mul_le (a := k.lo * v (A .wQG)) k.den_pos
    have u4 := cdiv_mul_le (a := k.lo * v (A .aG)) k.den_pos
    have u5 := cdiv_mul_le (a := k.lo * v (A .wGC)) k.den_pos
    have l1 := div_mul_add_gt (a := k.hi * v (A .wAC)) k.den_pos
    have hd := k.den_pos
    apply Nat.lt_of_mul_lt_mul_right (a := k.den)
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
    omega

/-- Non-vacuity of the safety hypotheses: at κ = 0 the fast endpoints realise
the model (A's `realizes_fast`), and runs exist for them. -/
theorem nonvacuous (A : Arc → CArc) (hq : 0 < (A .aSt).F + (A .wQf).F)
    (hc : 0 < (A .aC).F + (A .wCf).F) :
    (∀ e, Scat Kappa.zero Corner.fast (A e) ((A e).F)) ∧
      ∃ a0 q g Ak, Run F1 G1 false (dlOf (fun e => (A e).F)) 1 a0 q g Ak := by
  refine ⟨realizes_fast ⟨A, Kappa.zero⟩, ?_⟩
  exact run_exists F1 G1 true _ 1 F1_hold F1_go G1_vals.1 (by decide)
    (by simp only [Dl.dQf, dlOf]; omega) (by simp only [Dl.dCf, dlOf]; omega)

/-! ## 3. Per seed x client x reading: arc data, exact threshold, both directions

Generated by `scratchpad/Bk1/gen.py` from `run7g_*` records of
`OnNetlistArb.lean` (route windows: fast `[fast_min, fast_max+Elmore]`,
slow `[slow_min, slow_max+Elmore]`, site pins included) and the per-pin LUT
arcs of `ArbCornersPin.lean` (O6 45/56/100/124; SLICEM A5->O5 48/60/93/116;
SLICEM A3->O5 43/53/120/148; ugrant's q pin: A5 on S1, S3, S4, A3 on S2).
-/

/-- Arc endpoints (F, S) ps, seed 1, client 1, reading `lit`. -/
def A_s1c1_lit : Arc → CArc
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 903, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 429, by decide⟩
  | .aG => ⟨48, 116, by decide⟩
  | .wGC => ⟨209, 677, by decide⟩
  | .wAC => ⟨196, 795, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 276, by decide⟩

/-- **Seed 1, client 1, `lit`: safe for every κ ≤ 727/1522 ≈ 0.4777**, at every
corner and for every delay assignment within κ of nominal (early = 686 / 2249, late =
196 / 795 ps at fast / slow; binding endpoint slow). -/
theorem safe_s1c1_lit (k : Kappa) (H_KAPPA : k.num * 1522 ≤ k.den * 727)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s1c1_lit e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s1c1_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 1, client 1, `lit`: unsafe for every κ ≥ 1460/3044 ≈ 0.4796**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s1c1_lit (k : Kappa) (H_KAPPA : k.den * 1460 ≤ k.num * 3044) :
    ∃ c d, (∀ e, Scat k c (A_s1c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s1c1_lit
    (by simp only [A_s1c1_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s1c1_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s1c1_lit]; omega
  · simp only [wit, A_s1c1_lit]; omega

/-- Arc endpoints (F, S) ps, seed 1, client 2, reading `lit`. -/
def A_s1c2_lit : Arc → CArc
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 903, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 429, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨176, 651, by decide⟩
  | .wAC => ⟨259, 955, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨195, 677, by decide⟩

/-- **Seed 1, client 2, `lit`: safe for every κ ≤ 638/1593 ≈ 0.4005**, at every
corner and for every delay assignment within κ of nominal (early = 650 / 2231, late =
259 / 955 ps at fast / slow; binding endpoint slow). -/
theorem safe_s1c2_lit (k : Kappa) (H_KAPPA : k.num * 1593 ≤ k.den * 638)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s1c2_lit e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s1c2_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 1, client 2, `lit`: unsafe for every κ ≥ 1282/3186 ≈ 0.4024**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s1c2_lit (k : Kappa) (H_KAPPA : k.den * 1282 ≤ k.num * 3186) :
    ∃ c d, (∀ e, Scat k c (A_s1c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s1c2_lit
    (by simp only [A_s1c2_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s1c2_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s1c2_lit]; omega
  · simp only [wit, A_s1c2_lit]; omega

/-- Arc endpoints (F, S) ps, seed 2, client 1, reading `lit`. -/
def A_s2c1_lit : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 849, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 677, by decide⟩
  | .aG => ⟨43, 148, by decide⟩
  | .wGC => ⟨241, 801, by decide⟩
  | .wAC => ⟨192, 760, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨115, 423, by decide⟩

/-- **Seed 2, client 1, `lit`: safe for every κ ≤ 1839/3359 ≈ 0.5475**, at every
corner and for every delay assignment within κ of nominal (early = 756 / 2599, late =
192 / 760 ps at fast / slow; binding endpoint slow). -/
theorem safe_s2c1_lit (k : Kappa) (H_KAPPA : k.num * 3359 ≤ k.den * 1839)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s2c1_lit e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s2c1_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 2, client 1, `lit`: unsafe for every κ ≥ 1845/3359 ≈ 0.5493**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s2c1_lit (k : Kappa) (H_KAPPA : k.den * 1845 ≤ k.num * 3359) :
    ∃ c d, (∀ e, Scat k c (A_s2c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s2c1_lit
    (by simp only [A_s2c1_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s2c1_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s2c1_lit]; omega
  · simp only [wit, A_s2c1_lit]; omega

/-- Arc endpoints (F, S) ps, seed 2, client 2, reading `lit`. -/
def A_s2c2_lit : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 849, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 677, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨325, 1015, by decide⟩
  | .wAC => ⟨262, 940, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨76, 288, by decide⟩

/-- **Seed 2, client 2, `lit`: safe for every κ ≤ 1849/3729 ≈ 0.4958**, at every
corner and for every delay assignment within κ of nominal (early = 842 / 2789, late =
262 / 940 ps at fast / slow; binding endpoint slow). -/
theorem safe_s2c2_lit (k : Kappa) (H_KAPPA : k.num * 3729 ≤ k.den * 1849)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s2c2_lit e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s2c2_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 2, client 2, `lit`: unsafe for every κ ≥ 1855/3729 ≈ 0.4975**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s2c2_lit (k : Kappa) (H_KAPPA : k.den * 1855 ≤ k.num * 3729) :
    ∃ c d, (∀ e, Scat k c (A_s2c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s2c2_lit
    (by simp only [A_s2c2_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s2c2_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s2c2_lit]; omega
  · simp only [wit, A_s2c2_lit]; omega

/-- Arc endpoints (F, S) ps, seed 3, client 1, reading `lit`. -/
def A_s3c1_lit : Arc → CArc
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 761, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 714, by decide⟩
  | .aG => ⟨48, 116, by decide⟩
  | .wGC => ⟨274, 972, by decide⟩
  | .wAC => ⟨183, 809, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨69, 298, by decide⟩

/-- **Seed 3, client 1, `lit`: safe for every κ ≤ 939/1748 ≈ 0.5372**, at every
corner and for every delay assignment within κ of nominal (early = 763 / 2687, late =
183 / 809 ps at fast / slow; binding endpoint slow). -/
theorem safe_s3c1_lit (k : Kappa) (H_KAPPA : k.num * 1748 ≤ k.den * 939)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s3c1_lit e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s3c1_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 3, client 1, `lit`: unsafe for every κ ≥ 1884/3496 ≈ 0.5389**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s3c1_lit (k : Kappa) (H_KAPPA : k.den * 1884 ≤ k.num * 3496) :
    ∃ c d, (∀ e, Scat k c (A_s3c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s3c1_lit
    (by simp only [A_s3c1_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s3c1_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s3c1_lit]; omega
  · simp only [wit, A_s3c1_lit]; omega

/-- Arc endpoints (F, S) ps, seed 3, client 2, reading `lit`. -/
def A_s3c2_lit : Arc → CArc
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 761, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 714, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨268, 879, by decide⟩
  | .wAC => ⟨258, 965, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨211, 685, by decide⟩

/-- **Seed 3, client 2, `lit`: safe for every κ ≤ 1637/3567 ≈ 0.4589**, at every
corner and for every delay assignment within κ of nominal (early = 754 / 2602, late =
258 / 965 ps at fast / slow; binding endpoint slow). -/
theorem safe_s3c2_lit (k : Kappa) (H_KAPPA : k.num * 3567 ≤ k.den * 1637)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s3c2_lit e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s3c2_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 3, client 2, `lit`: unsafe for every κ ≥ 1643/3567 ≈ 0.4606**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s3c2_lit (k : Kappa) (H_KAPPA : k.den * 1643 ≤ k.num * 3567) :
    ∃ c d, (∀ e, Scat k c (A_s3c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s3c2_lit
    (by simp only [A_s3c2_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s3c2_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s3c2_lit]; omega
  · simp only [wit, A_s3c2_lit]; omega

/-- Arc endpoints (F, S) ps, seed 4, client 1, reading `lit`. -/
def A_s4c1_lit : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 1079, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 571, by decide⟩
  | .aG => ⟨48, 116, by decide⟩
  | .wGC => ⟨127, 471, by decide⟩
  | .wAC => ⟨246, 978, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨214, 689, by decide⟩

/-- **Seed 4, client 1, `lit`: safe for every κ ≤ 461/1113 ≈ 0.4142**, at every
corner and for every delay assignment within κ of nominal (early = 704 / 2361, late =
246 / 978 ps at fast / slow; binding endpoint slow). -/
theorem safe_s4c1_lit (k : Kappa) (H_KAPPA : k.num * 1113 ≤ k.den * 461)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s4c1_lit e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s4c1_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 4, client 1, `lit`: unsafe for every κ ≥ 1389/3339 ≈ 0.4160**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s4c1_lit (k : Kappa) (H_KAPPA : k.den * 1389 ≤ k.num * 3339) :
    ∃ c d, (∀ e, Scat k c (A_s4c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s4c1_lit
    (by simp only [A_s4c1_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s4c1_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s4c1_lit]; omega
  · simp only [wit, A_s4c1_lit]; omega

/-- Arc endpoints (F, S) ps, seed 4, client 2, reading `lit`. -/
def A_s4c2_lit : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 1079, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 571, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨258, 863, by decide⟩
  | .wAC => ⟨256, 942, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 274, by decide⟩

/-- **Seed 4, client 2, `lit`: safe for every κ ≤ 1819/3703 ≈ 0.4912**, at every
corner and for every delay assignment within κ of nominal (early = 832 / 2761, late =
256 / 942 ps at fast / slow; binding endpoint slow). -/
theorem safe_s4c2_lit (k : Kappa) (H_KAPPA : k.num * 3703 ≤ k.den * 1819)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s4c2_lit e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s4c2_lit]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 4, client 2, `lit`: unsafe for every κ ≥ 1825/3703 ≈ 0.4928**: at the
slow endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s4c2_lit (k : Kappa) (H_KAPPA : k.den * 1825 ≤ k.num * 3703) :
    ∃ c d, (∀ e, Scat k c (A_s4c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.slow) CArc.S (fun _ _ => scat_slow_iff) A_s4c2_lit
    (by simp only [A_s4c2_lit]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s4c2_lit] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.slow, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s4c2_lit]; omega
  · simp only [wit, A_s4c2_lit]; omega

/-- Arc endpoints (F, S) ps, seed 1, client 1, reading `cons`. -/
def A_s1c1_cons : Arc → CArc
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 638, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 325, by decide⟩
  | .aG => ⟨48, 93, by decide⟩
  | .wGC => ⟨209, 524, by decide⟩
  | .wAC => ⟨375, 795, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 276, by decide⟩

/-- **Seed 1, client 1, `cons`: safe for every κ ≤ 311/1061 ≈ 0.2931**, at every
corner and for every delay assignment within κ of nominal (early = 686 / 1680, late =
375 / 795 ps at fast / slow; binding endpoint fast). -/
theorem safe_s1c1_cons (k : Kappa) (H_KAPPA : k.num * 1061 ≤ k.den * 311)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s1c1_cons e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s1c1_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 1, client 1, `cons`: unsafe for every κ ≥ 317/1061 ≈ 0.2988**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s1c1_cons (k : Kappa) (H_KAPPA : k.den * 317 ≤ k.num * 1061) :
    ∃ c d, (∀ e, Scat k c (A_s1c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s1c1_cons
    (by simp only [A_s1c1_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s1c1_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s1c1_cons]; omega
  · simp only [wit, A_s1c1_cons]; omega

/-- Arc endpoints (F, S) ps, seed 1, client 2, reading `cons`. -/
def A_s1c2_cons : Arc → CArc
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 638, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 325, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨176, 503, by decide⟩
  | .wAC => ⟨453, 955, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨195, 677, by decide⟩

/-- **Seed 1, client 2, `cons`: safe for every κ ≤ 197/1103 ≈ 0.1786**, at every
corner and for every delay assignment within κ of nominal (early = 650 / 1666, late =
453 / 955 ps at fast / slow; binding endpoint fast). -/
theorem safe_s1c2_cons (k : Kappa) (H_KAPPA : k.num * 1103 ≤ k.den * 198)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s1c2_cons e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s1c2_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 1, client 2, `cons`: unsafe for every κ ≥ 203/1103 ≈ 0.1840**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s1c2_cons (k : Kappa) (H_KAPPA : k.den * 203 ≤ k.num * 1103) :
    ∃ c d, (∀ e, Scat k c (A_s1c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s1c2_cons
    (by simp only [A_s1c2_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s1c2_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s1c2_cons]; omega
  · simp only [wit, A_s1c2_cons]; omega

/-- Arc endpoints (F, S) ps, seed 2, client 1, reading `cons`. -/
def A_s2c1_cons : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 578, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 525, by decide⟩
  | .aG => ⟨43, 120, by decide⟩
  | .wGC => ⟨241, 610, by decide⟩
  | .wAC => ⟨378, 760, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨115, 423, by decide⟩

/-- **Seed 2, client 1, `cons`: safe for every κ ≤ 1/3 ≈ 0.3333**, at every
corner and for every delay assignment within κ of nominal (early = 756 / 1933, late =
378 / 760 ps at fast / slow; binding endpoint fast). -/
theorem safe_s2c1_cons (k : Kappa) (H_KAPPA : k.num * 3 ≤ k.den * 1)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s2c1_cons e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s2c1_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 2, client 1, `cons`: unsafe for every κ ≥ 384/1134 ≈ 0.3386**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s2c1_cons (k : Kappa) (H_KAPPA : k.den * 384 ≤ k.num * 1134) :
    ∃ c d, (∀ e, Scat k c (A_s2c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s2c1_cons
    (by simp only [A_s2c1_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s2c1_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s2c1_cons]; omega
  · simp only [wit, A_s2c1_cons]; omega

/-- Arc endpoints (F, S) ps, seed 2, client 2, reading `cons`. -/
def A_s2c2_cons : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 578, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 525, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨325, 785, by decide⟩
  | .wAC => ⟨466, 940, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨76, 288, by decide⟩

/-- **Seed 2, client 2, `cons`: safe for every κ ≤ 94/327 ≈ 0.2875**, at every
corner and for every delay assignment within κ of nominal (early = 842 / 2088, late =
466 / 940 ps at fast / slow; binding endpoint fast). -/
theorem safe_s2c2_cons (k : Kappa) (H_KAPPA : k.num * 327 ≤ k.den * 94)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s2c2_cons e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s2c2_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 2, client 2, `cons`: unsafe for every κ ≥ 382/1308 ≈ 0.2920**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s2c2_cons (k : Kappa) (H_KAPPA : k.den * 382 ≤ k.num * 1308) :
    ∃ c d, (∀ e, Scat k c (A_s2c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s2c2_cons
    (by simp only [A_s2c2_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s2c2_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s2c2_cons]; omega
  · simp only [wit, A_s2c2_cons]; omega

/-- Arc endpoints (F, S) ps, seed 3, client 1, reading `cons`. -/
def A_s3c1_cons : Arc → CArc
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 505, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 543, by decide⟩
  | .aG => ⟨48, 93, by decide⟩
  | .wGC => ⟨274, 662, by decide⟩
  | .wAC => ⟨404, 809, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨69, 298, by decide⟩

/-- **Seed 3, client 1, `cons`: safe for every κ ≤ 359/1167 ≈ 0.3076**, at every
corner and for every delay assignment within κ of nominal (early = 763 / 1903, late =
404 / 809 ps at fast / slow; binding endpoint fast). -/
theorem safe_s3c1_cons (k : Kappa) (H_KAPPA : k.num * 1167 ≤ k.den * 359)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s3c1_cons e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s3c1_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 3, client 1, `cons`: unsafe for every κ ≥ 365/1167 ≈ 0.3128**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s3c1_cons (k : Kappa) (H_KAPPA : k.den * 365 ≤ k.num * 1167) :
    ∃ c d, (∀ e, Scat k c (A_s3c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s3c1_cons
    (by simp only [A_s3c1_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s3c1_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s3c1_cons]; omega
  · simp only [wit, A_s3c1_cons]; omega

/-- Arc endpoints (F, S) ps, seed 3, client 2, reading `cons`. -/
def A_s3c2_cons : Arc → CArc
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 505, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 543, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨268, 677, by decide⟩
  | .wAC => ⟨461, 965, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨211, 685, by decide⟩

/-- **Seed 3, client 2, `cons`: safe for every κ ≤ 293/1215 ≈ 0.2412**, at every
corner and for every delay assignment within κ of nominal (early = 754 / 1925, late =
461 / 965 ps at fast / slow; binding endpoint fast). -/
theorem safe_s3c2_cons (k : Kappa) (H_KAPPA : k.num * 1215 ≤ k.den * 293)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s3c2_cons e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s3c2_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 3, client 2, `cons`: unsafe for every κ ≥ 299/1215 ≈ 0.2461**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s3c2_cons (k : Kappa) (H_KAPPA : k.den * 299 ≤ k.num * 1215) :
    ∃ c d, (∀ e, Scat k c (A_s3c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s3c2_cons
    (by simp only [A_s3c2_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s3c2_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s3c2_cons]; omega
  · simp only [wit, A_s3c2_cons]; omega

/-- Arc endpoints (F, S) ps, seed 4, client 1, reading `cons`. -/
def A_s4c1_cons : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 749, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 434, by decide⟩
  | .aG => ⟨48, 93, by decide⟩
  | .wGC => ⟨127, 356, by decide⟩
  | .wAC => ⟨464, 978, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨214, 689, by decide⟩

/-- **Seed 4, client 1, `cons`: safe for every κ ≤ 15/73 ≈ 0.2055**, at every
corner and for every delay assignment within κ of nominal (early = 704 / 1732, late =
464 / 978 ps at fast / slow; binding endpoint fast). -/
theorem safe_s4c1_cons (k : Kappa) (H_KAPPA : k.num * 73 ≤ k.den * 15)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s4c1_cons e) (d e)) :
    Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s4c1_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 4, client 1, `cons`: unsafe for every κ ≥ 246/1168 ≈ 0.2106**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 1's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s4c1_cons (k : Kappa) (H_KAPPA : k.den * 246 ≤ k.num * 1168) :
    ∃ c d, (∀ e, Scat k c (A_s4c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s4c1_cons
    (by simp only [A_s4c1_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s4c1_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe1 hlt ?_ ?_⟩
  · simp only [wit, A_s4c1_cons]; omega
  · simp only [wit, A_s4c1_cons]; omega

/-- Arc endpoints (F, S) ps, seed 4, client 2, reading `cons`. -/
def A_s4c2_cons : Arc → CArc
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 749, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 434, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨258, 671, by decide⟩
  | .wAC => ⟨468, 942, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 274, by decide⟩

/-- **Seed 4, client 2, `cons`: safe for every κ ≤ 7/25 ≈ 0.2800**, at every
corner and for every delay assignment within κ of nominal (early = 832 / 2054, late =
468 / 942 ps at fast / slow; binding endpoint fast). -/
theorem safe_s4c2_cons (k : Kappa) (H_KAPPA : k.num * 25 ≤ k.den * 7)
    (c : Corner) (d : Arc → Nat) (H_SCAT : ∀ e, Scat k c (A_s4c2_cons e) (d e)) :
    Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  apply fork_le_of_endpoint _ H_SCAT
  simp only [EndpointOK, earlyArc, CArc.add, A_s4c2_cons]
  (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega)

/-- **Seed 4, client 2, `cons`: unsafe for every κ ≥ 370/1300 ≈ 0.2846**: at the
fast endpoint there is a delay assignment within κ of nominal on which client 2's ack
rises early, on every run (and runs exist). -/
theorem unsafe_s4c2_cons (k : Kappa) (H_KAPPA : k.den * 370 ≤ k.num * 1300) :
    ∃ c d, (∀ e, Scat k c (A_s4c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  obtain ⟨hS, hlt⟩ := counter_core (c := Corner.fast) CArc.F (fun _ _ => scat_fast_iff) A_s4c2_cons
    (by simp only [A_s4c2_cons]; (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
    (by intro e; cases e <;> simp only [A_s4c2_cons] <;> (have h1 := Kappa.lo_add k; have h2 : Kappa.hi k = Kappa.den k + Kappa.num k := rfl; generalize Kappa.hi k = H at *; generalize Kappa.lo k = L at *; generalize Kappa.num k = N at *; generalize Kappa.den k = D at *; omega))
  refine ⟨Corner.fast, _, hS, not_safe2 hlt ?_ ?_⟩
  · simp only [wit, A_s4c2_cons]; omega
  · simp only [wit, A_s4c2_cons]; omega


/-! ## 4. Verdicts at the two reference κ values (decided instances of §3)

There is no current measured κ (A-kappa.md correction): the two values here are
the scatter limits the shipped rules are sound for (Corner.lean): rule A's
`1/11` and rule E's / the CLAUDE.md guardband's `kappaE = 383/1927` (the
0.772/1.155 guard is exactly `(1+κ)/(1-κ) = 1155/772`). -/

def κA : Kappa := ⟨1, 11, by decide, by decide⟩
def κE : Kappa := ⟨383, 1927, by decide, by decide⟩

theorem verdict_s1c1_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s1c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s1c1_lit κA (by decide) c d h
theorem verdict_s1c1_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s1c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s1c1_lit κE (by decide) c d h
theorem verdict_s1c2_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s1c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s1c2_lit κA (by decide) c d h
theorem verdict_s1c2_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s1c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s1c2_lit κE (by decide) c d h
theorem verdict_s2c1_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s2c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s2c1_lit κA (by decide) c d h
theorem verdict_s2c1_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s2c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s2c1_lit κE (by decide) c d h
theorem verdict_s2c2_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s2c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s2c2_lit κA (by decide) c d h
theorem verdict_s2c2_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s2c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s2c2_lit κE (by decide) c d h
theorem verdict_s3c1_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s3c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s3c1_lit κA (by decide) c d h
theorem verdict_s3c1_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s3c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s3c1_lit κE (by decide) c d h
theorem verdict_s3c2_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s3c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s3c2_lit κA (by decide) c d h
theorem verdict_s3c2_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s3c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s3c2_lit κE (by decide) c d h
theorem verdict_s4c1_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s4c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s4c1_lit κA (by decide) c d h
theorem verdict_s4c1_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s4c1_lit e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s4c1_lit κE (by decide) c d h
theorem verdict_s4c2_lit_κA : ∀ c d, (∀ e, Scat κA c (A_s4c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s4c2_lit κA (by decide) c d h
theorem verdict_s4c2_lit_κE : ∀ c d, (∀ e, Scat κE c (A_s4c2_lit e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s4c2_lit κE (by decide) c d h
theorem verdict_s1c1_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s1c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s1c1_cons κA (by decide) c d h
theorem verdict_s1c1_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s1c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s1c1_cons κE (by decide) c d h
theorem verdict_s1c2_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s1c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s1c2_cons κA (by decide) c d h
theorem verdict_s1c2_cons_κE : ∃ c d, (∀ e, Scat κE c (A_s1c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) :=
  unsafe_s1c2_cons κE (by decide)
theorem verdict_s2c1_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s2c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s2c1_cons κA (by decide) c d h
theorem verdict_s2c1_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s2c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s2c1_cons κE (by decide) c d h
theorem verdict_s2c2_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s2c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s2c2_cons κA (by decide) c d h
theorem verdict_s2c2_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s2c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s2c2_cons κE (by decide) c d h
theorem verdict_s3c1_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s3c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s3c1_cons κA (by decide) c d h
theorem verdict_s3c1_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s3c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s3c1_cons κE (by decide) c d h
theorem verdict_s3c2_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s3c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s3c2_cons κA (by decide) c d h
theorem verdict_s3c2_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s3c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s3c2_cons κE (by decide) c d h
theorem verdict_s4c1_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s4c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s4c1_cons κA (by decide) c d h
theorem verdict_s4c1_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s4c1_cons e) (d e)) → Safe F1 G1 false (dlOf d) :=
  fun c d h => safe_s4c1_cons κE (by decide) c d h
theorem verdict_s4c2_cons_κA : ∀ c d, (∀ e, Scat κA c (A_s4c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s4c2_cons κA (by decide) c d h
theorem verdict_s4c2_cons_κE : ∀ c d, (∀ e, Scat κE c (A_s4c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  fun c d h => safe_s4c2_cons κE (by decide) c d h

/-! ## 5. The data is the routed bits' and the SDF's (decided)

`lit` endpoints: every route arc's (F, S) is C's generated box window
`pinDelay` (fast_min, slow_max + Elmore, site pins included) of the routed
`link_arb` bitstreams; the shared prefix `c` enters only through the two
full routes (A0 -> ustate, A0 -> ua_k), whose sums are tied. The LUT arcs are
ArbCornersPin's per-pin SDF columns, with ugrant's q pin read from the bits
(`ArbCornersPin.s{n}_bits`). `cons` endpoints use the same F for early arcs and
the same S for the late arc; its early S (slow_min) and late F (fast_max +
Elmore) come from Bt3's per-corner windows (`OnNetlistArb.run7g_*`), which C's
generated file does not carry (Bt3 limitation 3). -/

theorem tie_s1c1 :
    (((A_s1c1_lit .c).F + (A_s1c1_lit .wSt).F, (A_s1c1_lit .c).S + (A_s1c1_lit .wSt).S) = Formal.Net.FasmLink.S1.pinDelay[3]![1]! ∧
    ((A_s1c1_lit .wQf).F, (A_s1c1_lit .wQf).S) = Formal.Net.FasmLink.S1.pinDelay[3]![4]! ∧
    ((A_s1c1_lit .wQG).F, (A_s1c1_lit .wQG).S) = Formal.Net.FasmLink.S1.pinDelay[5]![4]! ∧
    ((A_s1c1_lit .wGC).F, (A_s1c1_lit .wGC).S) = Formal.Net.FasmLink.S1.pinDelay[4]![1]! ∧
    ((A_s1c1_lit .c).F + (A_s1c1_lit .wAC).F, (A_s1c1_lit .c).S + (A_s1c1_lit .wAC).S) = Formal.Net.FasmLink.S1.pinDelay[4]![2]! ∧
    ((A_s1c1_lit .wCf).F, (A_s1c1_lit .wCf).S) = Formal.Net.FasmLink.S1.pinDelay[4]![4]!) ∧
    (((A_s1c1_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s1c1_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s1c1_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s1c1_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s1c1_lit .aG).F : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s1.ug.getD 2 9)).fmin ∧ ((A_s1c1_lit .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s1.ug.getD 2 9)).smax) ∧
    ((A_s1c1_cons .wSt).F = (A_s1c1_lit .wSt).F ∧ (A_s1c1_cons .aSt).F = (A_s1c1_lit .aSt).F ∧ (A_s1c1_cons .wQG).F = (A_s1c1_lit .wQG).F ∧
     (A_s1c1_cons .aG).F = (A_s1c1_lit .aG).F ∧ (A_s1c1_cons .wGC).F = (A_s1c1_lit .wGC).F ∧ (A_s1c1_cons .wAC).S = (A_s1c1_lit .wAC).S ∧
     ((A_s1c1_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s1c1_cons .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s1.ug.getD 2 9)).smin) := by
  decide

theorem tie_s1c2 :
    (((A_s1c2_lit .c).F + (A_s1c2_lit .wSt).F, (A_s1c2_lit .c).S + (A_s1c2_lit .wSt).S) = Formal.Net.FasmLink.S1.pinDelay[3]![1]! ∧
    ((A_s1c2_lit .wQf).F, (A_s1c2_lit .wQf).S) = Formal.Net.FasmLink.S1.pinDelay[3]![4]! ∧
    ((A_s1c2_lit .wQG).F, (A_s1c2_lit .wQG).S) = Formal.Net.FasmLink.S1.pinDelay[5]![4]! ∧
    ((A_s1c2_lit .wGC).F, (A_s1c2_lit .wGC).S) = Formal.Net.FasmLink.S1.pinDelay[6]![3]! ∧
    ((A_s1c2_lit .c).F + (A_s1c2_lit .wAC).F, (A_s1c2_lit .c).S + (A_s1c2_lit .wAC).S) = Formal.Net.FasmLink.S1.pinDelay[6]![1]! ∧
    ((A_s1c2_lit .wCf).F, (A_s1c2_lit .wCf).S) = Formal.Net.FasmLink.S1.pinDelay[6]![2]!) ∧
    (((A_s1c2_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s1c2_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s1c2_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s1c2_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s1c2_lit .aG).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s1c2_lit .aG).S : Int) = Formal.Cells.ArbCorners.O6.smax) ∧
    ((A_s1c2_cons .wSt).F = (A_s1c2_lit .wSt).F ∧ (A_s1c2_cons .aSt).F = (A_s1c2_lit .aSt).F ∧ (A_s1c2_cons .wQG).F = (A_s1c2_lit .wQG).F ∧
     (A_s1c2_cons .aG).F = (A_s1c2_lit .aG).F ∧ (A_s1c2_cons .wGC).F = (A_s1c2_lit .wGC).F ∧ (A_s1c2_cons .wAC).S = (A_s1c2_lit .wAC).S ∧
     ((A_s1c2_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s1c2_cons .aG).S : Int) = Formal.Cells.ArbCorners.O6.smin) := by
  decide

theorem tie_s2c1 :
    (((A_s2c1_lit .c).F + (A_s2c1_lit .wSt).F, (A_s2c1_lit .c).S + (A_s2c1_lit .wSt).S) = Formal.Net.FasmLink.S2.pinDelay[4]![3]! ∧
    ((A_s2c1_lit .wQf).F, (A_s2c1_lit .wQf).S) = Formal.Net.FasmLink.S2.pinDelay[4]![4]! ∧
    ((A_s2c1_lit .wQG).F, (A_s2c1_lit .wQG).S) = Formal.Net.FasmLink.S2.pinDelay[3]![2]! ∧
    ((A_s2c1_lit .wGC).F, (A_s2c1_lit .wGC).S) = Formal.Net.FasmLink.S2.pinDelay[5]![3]! ∧
    ((A_s2c1_lit .c).F + (A_s2c1_lit .wAC).F, (A_s2c1_lit .c).S + (A_s2c1_lit .wAC).S) = Formal.Net.FasmLink.S2.pinDelay[5]![2]! ∧
    ((A_s2c1_lit .wCf).F, (A_s2c1_lit .wCf).S) = Formal.Net.FasmLink.S2.pinDelay[5]![4]!) ∧
    (((A_s2c1_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s2c1_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s2c1_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s2c1_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s2c1_lit .aG).F : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s2.ug.getD 2 9)).fmin ∧ ((A_s2c1_lit .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s2.ug.getD 2 9)).smax) ∧
    ((A_s2c1_cons .wSt).F = (A_s2c1_lit .wSt).F ∧ (A_s2c1_cons .aSt).F = (A_s2c1_lit .aSt).F ∧ (A_s2c1_cons .wQG).F = (A_s2c1_lit .wQG).F ∧
     (A_s2c1_cons .aG).F = (A_s2c1_lit .aG).F ∧ (A_s2c1_cons .wGC).F = (A_s2c1_lit .wGC).F ∧ (A_s2c1_cons .wAC).S = (A_s2c1_lit .wAC).S ∧
     ((A_s2c1_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s2c1_cons .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s2.ug.getD 2 9)).smin) := by
  decide

theorem tie_s2c2 :
    (((A_s2c2_lit .c).F + (A_s2c2_lit .wSt).F, (A_s2c2_lit .c).S + (A_s2c2_lit .wSt).S) = Formal.Net.FasmLink.S2.pinDelay[4]![3]! ∧
    ((A_s2c2_lit .wQf).F, (A_s2c2_lit .wQf).S) = Formal.Net.FasmLink.S2.pinDelay[4]![4]! ∧
    ((A_s2c2_lit .wQG).F, (A_s2c2_lit .wQG).S) = Formal.Net.FasmLink.S2.pinDelay[3]![2]! ∧
    ((A_s2c2_lit .wGC).F, (A_s2c2_lit .wGC).S) = Formal.Net.FasmLink.S2.pinDelay[6]![1]! ∧
    ((A_s2c2_lit .c).F + (A_s2c2_lit .wAC).F, (A_s2c2_lit .c).S + (A_s2c2_lit .wAC).S) = Formal.Net.FasmLink.S2.pinDelay[6]![0]! ∧
    ((A_s2c2_lit .wCf).F, (A_s2c2_lit .wCf).S) = Formal.Net.FasmLink.S2.pinDelay[6]![4]!) ∧
    (((A_s2c2_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s2c2_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s2c2_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s2c2_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s2c2_lit .aG).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s2c2_lit .aG).S : Int) = Formal.Cells.ArbCorners.O6.smax) ∧
    ((A_s2c2_cons .wSt).F = (A_s2c2_lit .wSt).F ∧ (A_s2c2_cons .aSt).F = (A_s2c2_lit .aSt).F ∧ (A_s2c2_cons .wQG).F = (A_s2c2_lit .wQG).F ∧
     (A_s2c2_cons .aG).F = (A_s2c2_lit .aG).F ∧ (A_s2c2_cons .wGC).F = (A_s2c2_lit .wGC).F ∧ (A_s2c2_cons .wAC).S = (A_s2c2_lit .wAC).S ∧
     ((A_s2c2_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s2c2_cons .aG).S : Int) = Formal.Cells.ArbCorners.O6.smin) := by
  decide

theorem tie_s3c1 :
    (((A_s3c1_lit .c).F + (A_s3c1_lit .wSt).F, (A_s3c1_lit .c).S + (A_s3c1_lit .wSt).S) = Formal.Net.FasmLink.S3.pinDelay[4]![3]! ∧
    ((A_s3c1_lit .wQf).F, (A_s3c1_lit .wQf).S) = Formal.Net.FasmLink.S3.pinDelay[4]![0]! ∧
    ((A_s3c1_lit .wQG).F, (A_s3c1_lit .wQG).S) = Formal.Net.FasmLink.S3.pinDelay[6]![4]! ∧
    ((A_s3c1_lit .wGC).F, (A_s3c1_lit .wGC).S) = Formal.Net.FasmLink.S3.pinDelay[5]![3]! ∧
    ((A_s3c1_lit .c).F + (A_s3c1_lit .wAC).F, (A_s3c1_lit .c).S + (A_s3c1_lit .wAC).S) = Formal.Net.FasmLink.S3.pinDelay[5]![0]! ∧
    ((A_s3c1_lit .wCf).F, (A_s3c1_lit .wCf).S) = Formal.Net.FasmLink.S3.pinDelay[5]![4]!) ∧
    (((A_s3c1_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s3c1_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s3c1_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s3c1_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s3c1_lit .aG).F : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s3.ug.getD 2 9)).fmin ∧ ((A_s3c1_lit .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s3.ug.getD 2 9)).smax) ∧
    ((A_s3c1_cons .wSt).F = (A_s3c1_lit .wSt).F ∧ (A_s3c1_cons .aSt).F = (A_s3c1_lit .aSt).F ∧ (A_s3c1_cons .wQG).F = (A_s3c1_lit .wQG).F ∧
     (A_s3c1_cons .aG).F = (A_s3c1_lit .aG).F ∧ (A_s3c1_cons .wGC).F = (A_s3c1_lit .wGC).F ∧ (A_s3c1_cons .wAC).S = (A_s3c1_lit .wAC).S ∧
     ((A_s3c1_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s3c1_cons .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s3.ug.getD 2 9)).smin) := by
  decide

theorem tie_s3c2 :
    (((A_s3c2_lit .c).F + (A_s3c2_lit .wSt).F, (A_s3c2_lit .c).S + (A_s3c2_lit .wSt).S) = Formal.Net.FasmLink.S3.pinDelay[4]![3]! ∧
    ((A_s3c2_lit .wQf).F, (A_s3c2_lit .wQf).S) = Formal.Net.FasmLink.S3.pinDelay[4]![0]! ∧
    ((A_s3c2_lit .wQG).F, (A_s3c2_lit .wQG).S) = Formal.Net.FasmLink.S3.pinDelay[6]![4]! ∧
    ((A_s3c2_lit .wGC).F, (A_s3c2_lit .wGC).S) = Formal.Net.FasmLink.S3.pinDelay[3]![3]! ∧
    ((A_s3c2_lit .c).F + (A_s3c2_lit .wAC).F, (A_s3c2_lit .c).S + (A_s3c2_lit .wAC).S) = Formal.Net.FasmLink.S3.pinDelay[3]![1]! ∧
    ((A_s3c2_lit .wCf).F, (A_s3c2_lit .wCf).S) = Formal.Net.FasmLink.S3.pinDelay[3]![0]!) ∧
    (((A_s3c2_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s3c2_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s3c2_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s3c2_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s3c2_lit .aG).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s3c2_lit .aG).S : Int) = Formal.Cells.ArbCorners.O6.smax) ∧
    ((A_s3c2_cons .wSt).F = (A_s3c2_lit .wSt).F ∧ (A_s3c2_cons .aSt).F = (A_s3c2_lit .aSt).F ∧ (A_s3c2_cons .wQG).F = (A_s3c2_lit .wQG).F ∧
     (A_s3c2_cons .aG).F = (A_s3c2_lit .aG).F ∧ (A_s3c2_cons .wGC).F = (A_s3c2_lit .wGC).F ∧ (A_s3c2_cons .wAC).S = (A_s3c2_lit .wAC).S ∧
     ((A_s3c2_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s3c2_cons .aG).S : Int) = Formal.Cells.ArbCorners.O6.smin) := by
  decide

theorem tie_s4c1 :
    (((A_s4c1_lit .c).F + (A_s4c1_lit .wSt).F, (A_s4c1_lit .c).S + (A_s4c1_lit .wSt).S) = Formal.Net.FasmLink.S4.pinDelay[3]![1]! ∧
    ((A_s4c1_lit .wQf).F, (A_s4c1_lit .wQf).S) = Formal.Net.FasmLink.S4.pinDelay[3]![4]! ∧
    ((A_s4c1_lit .wQG).F, (A_s4c1_lit .wQG).S) = Formal.Net.FasmLink.S4.pinDelay[5]![4]! ∧
    ((A_s4c1_lit .wGC).F, (A_s4c1_lit .wGC).S) = Formal.Net.FasmLink.S4.pinDelay[6]![3]! ∧
    ((A_s4c1_lit .c).F + (A_s4c1_lit .wAC).F, (A_s4c1_lit .c).S + (A_s4c1_lit .wAC).S) = Formal.Net.FasmLink.S4.pinDelay[6]![2]! ∧
    ((A_s4c1_lit .wCf).F, (A_s4c1_lit .wCf).S) = Formal.Net.FasmLink.S4.pinDelay[6]![0]!) ∧
    (((A_s4c1_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s4c1_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s4c1_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s4c1_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s4c1_lit .aG).F : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s4.ug.getD 2 9)).fmin ∧ ((A_s4c1_lit .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s4.ug.getD 2 9)).smax) ∧
    ((A_s4c1_cons .wSt).F = (A_s4c1_lit .wSt).F ∧ (A_s4c1_cons .aSt).F = (A_s4c1_lit .aSt).F ∧ (A_s4c1_cons .wQG).F = (A_s4c1_lit .wQG).F ∧
     (A_s4c1_cons .aG).F = (A_s4c1_lit .aG).F ∧ (A_s4c1_cons .wGC).F = (A_s4c1_lit .wGC).F ∧ (A_s4c1_cons .wAC).S = (A_s4c1_lit .wAC).S ∧
     ((A_s4c1_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s4c1_cons .aG).S : Int) = (Formal.Cells.ArbCornersPin.pinCol (Formal.Cells.ArbCornersPin.s4.ug.getD 2 9)).smin) := by
  decide

theorem tie_s4c2 :
    (((A_s4c2_lit .c).F + (A_s4c2_lit .wSt).F, (A_s4c2_lit .c).S + (A_s4c2_lit .wSt).S) = Formal.Net.FasmLink.S4.pinDelay[3]![1]! ∧
    ((A_s4c2_lit .wQf).F, (A_s4c2_lit .wQf).S) = Formal.Net.FasmLink.S4.pinDelay[3]![4]! ∧
    ((A_s4c2_lit .wQG).F, (A_s4c2_lit .wQG).S) = Formal.Net.FasmLink.S4.pinDelay[5]![4]! ∧
    ((A_s4c2_lit .wGC).F, (A_s4c2_lit .wGC).S) = Formal.Net.FasmLink.S4.pinDelay[4]![1]! ∧
    ((A_s4c2_lit .c).F + (A_s4c2_lit .wAC).F, (A_s4c2_lit .c).S + (A_s4c2_lit .wAC).S) = Formal.Net.FasmLink.S4.pinDelay[4]![0]! ∧
    ((A_s4c2_lit .wCf).F, (A_s4c2_lit .wCf).S) = Formal.Net.FasmLink.S4.pinDelay[4]![4]!) ∧
    (((A_s4c2_lit .aSt).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s4c2_lit .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s4c2_lit .aC).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s4c2_lit .aC).S : Int) = Formal.Cells.ArbCorners.O6.smax ∧
     ((A_s4c2_lit .aG).F : Int) = Formal.Cells.ArbCorners.O6.fmin ∧ ((A_s4c2_lit .aG).S : Int) = Formal.Cells.ArbCorners.O6.smax) ∧
    ((A_s4c2_cons .wSt).F = (A_s4c2_lit .wSt).F ∧ (A_s4c2_cons .aSt).F = (A_s4c2_lit .aSt).F ∧ (A_s4c2_cons .wQG).F = (A_s4c2_lit .wQG).F ∧
     (A_s4c2_cons .aG).F = (A_s4c2_lit .aG).F ∧ (A_s4c2_cons .wGC).F = (A_s4c2_lit .wGC).F ∧ (A_s4c2_cons .wAC).S = (A_s4c2_lit .wAC).S ∧
     ((A_s4c2_cons .aSt).S : Int) = Formal.Cells.ArbCorners.O6.smin ∧ ((A_s4c2_cons .aG).S : Int) = Formal.Cells.ArbCorners.O6.smin) := by
  decide


/-! ## 6. Non-vacuity: the safety hypotheses hold at κ = 0 for every pair, with runs -/

theorem nonvacuous_lit : ∀ A ∈ [A_s1c1_lit, A_s1c2_lit, A_s2c1_lit, A_s2c2_lit, A_s3c1_lit,
    A_s3c2_lit, A_s4c1_lit, A_s4c2_lit, A_s1c1_cons, A_s1c2_cons, A_s2c1_cons, A_s2c2_cons,
    A_s3c1_cons, A_s3c2_cons, A_s4c1_cons, A_s4c2_cons],
    (∀ e, Scat Kappa.zero Corner.fast (A e) ((A e).F)) ∧
      ∃ a0 q g Ak, Run F1 G1 false (dlOf (fun e => (A e).F)) 1 a0 q g Ak := by
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact nonvacuous _ (by decide) (by decide)

/-- `Kappa.zero` satisfies every `safe_*` hypothesis, and κ = 1 every `unsafe_*` one. -/
theorem hyps_satisfiable : Kappa.zero.num * 1103 ≤ Kappa.zero.den * 197 ∧
    (⟨1, 1, by decide, by decide⟩ : Kappa).den * 203 ≤ (⟨1, 1, by decide, by decide⟩ : Kappa).num * 1103 := by
  decide

end Formal.Cells.OnNetlistArbKappa
