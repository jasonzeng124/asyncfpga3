import Formal.Timing.GrantFork
open Formal.Core.LutList

/-!
# C-10j: does the grant-fork runt break the handshake? (H_RUNT_ACK)

C-10i (`GrantFork.lean`) proved that the held `bd_arbiter`'s grant wire `g_k` can
carry a runt while the other grant is high (H_GRANT_FORK fails on 32/40 routed
instances). This file decides what DOWNSTREAM of the grant wires can observe of that
runt, in the same per-(pin, output) transport-delay model with the real INITs
(shard B's `Formal.Cells.ArbBinary`, read-only):

* `ustate` O6 `q   = stA (r1) (r2) (q) (A0)`   INIT FFF0_FFB2_ACAC_ACAC   (`Common.st`)
* `ustate` O5 `R0  = r0A (r1) (r2) (q) (A0)`   same INIT, low half        (`Common.r0`)
* `ugrant` O6 `g2  = gr2 (r1) (r2) (q)`, O5 `g1 = gr1 ...`  INIT 0C0C_0C0C_A0A0_A0A0
* `ua_k`      `A_k = c2 (g_k) (A0) (A_k)`      INIT 00E8_00E8_00E8_00E8 (`bd_c2`)
* the server: A0 rises only after R0 has been high for at least `srv` (H_SRV, `Common.srv`)
* the amerge index / data LUTs (any LUT `y = f (g_k) (other inputs)`; bdc's index is
  `won = g2 | A2`, INIT `1110`, `idxLut`), and the cell's request z_req, which rises
  only after R0 has been high for at least `dz` (H_ZREQ).

Each argument of each LUT has its own pure delay (route + site pin + that pin's arc).

## H_RUNT_ACK, precisely (client 2; client 1 is the mirror)

Scenario `Scn2` (C-10i's race): A0 low, r1 asks alone, q rises at T, r2 rises late,
and q does not reverse (q is a step on the horizon `t < H`).
* `W2 d = (b6 - L) - (a2 - s2)` is C-10i's window (> 0 iff a runt exists).
* `early2 d = min Lr (L - s2 + u2) + srv + da`: the earliest instant, after T, at
  which A0 can be seen by ua2's core. R0 can rise through the q path (`Lr`), or
  through the r2·¬q term BEFORE the new q reaches ustate's O5 (`L - s2 + u2`: r2
  reaches ustate's core no earlier than `T + L - s2`, `cons2`). The second term is
  not in C-10i's ackcheck; it is an O5-vs-O6 arc difference, tens of ps.
* `late2 d = b6 + dg`: the instant, after T, at which the runt ends at ua2's core.
* **`Ok2 d := W2 d ≤ 0 ∨ late2 d ≤ early2 d`** (H_RUNT_ACK2).

Theorems:
* `no_extra_ack2`: `Ok2` ⇒ A2 stays low on the whole horizon: no extra
  acknowledgement, so client 2's transaction is not lost (r2 stays up, and it is
  served after the handover, which is B's ArbHeldTimed territory).
* `idx_clean2`: the index form: if `W2 ≤ 0 ∨ b6 + e ≤ min Lr (L - s2 + u2) + dz`
  then at every instant z_req is high, every LUT that reads g2 through delay `e`
  outputs exactly its runt-free value (`f false _`): no wrong-index offer.
* Converses (exact): `extra_ack2` / `spurious_ack2_iff`: when `Ok2` fails (and two
  physical side conditions hold, `hu1`, `hsa`), there is a concrete trace satisfying
  every gate relation in which R0 rises exactly once, ustate's core never sees client 2
  asking with the state on its side, and yet A2 rises: an acknowledgement for a
  transaction the server never carried. `wrong_index2`: when the index inequality
  fails, z_req is high while the index LUT outputs 1 and the arbiter has granted
  client 1.
* Client 1: `no_extra_ack1`, `extra_ack1`, `spurious_ack1_iff` (q falls, r1 late,
  g1 runt on O5). g1 has no index reader in bdc_amerge (`unused_g1`), so client 1 has
  no index theorem.
* `Row`, `okAck`, `okAck_sound2/1`, `okAck_exact2/1`: the integer checker over
  prefix-cancelled routed quantities (H_SHARED_PREFIX, as C-10i), and `Cert`,
  `Cert.ok`, `cert_bound`: a potential certificate proving that every path of a
  timing graph from R0 to a target is at least `c.p target` long (the server and
  z_req lower bounds, H_CAUSAL_PATH).
-/

namespace Formal.Timing.RuntAck
open Formal.Cells Formal.Cells.ArbBinary Formal.Timing.GrantFork

/-- Per-(pin, output) pure delays around one client's acknowledge. -/
structure D where
  /-- ustate O6 (q): r1 pin, r2 pin, own q pin, A0 pin -/
  s1 : Int
  s2 : Int
  L : Int
  sa : Int
  /-- ustate O5 (R0): r1 pin, r2 pin, q pin -/
  u1 : Int
  u2 : Int
  Lr : Int
  /-- ugrant O6 (g2): r1, r2, q pins -/
  x1 : Int
  a2 : Int
  b6 : Int
  /-- ugrant O5 (g1): r1, r2, q pins -/
  a1 : Int
  x2 : Int
  b5 : Int
  /-- ua_k: g_k pin, A0 pin, own feedback -/
  dg : Int
  da : Int
  dc : Int
  /-- server: A0 (at its driver) rises at least `srv` after an R0-high instant -/
  srv : Int

structure Pos (d : D) : Prop where
  L : 0 < d.L
  s1 : 0 ≤ d.s1
  s2 : 0 ≤ d.s2
  sa : 0 ≤ d.sa
  u1 : 0 ≤ d.u1
  u2 : 0 ≤ d.u2
  Lr : 0 ≤ d.Lr
  x1 : 0 ≤ d.x1
  a2 : 0 ≤ d.a2
  b6 : 0 ≤ d.b6
  a1 : 0 ≤ d.a1
  x2 : 0 ≤ d.x2
  b5 : 0 ≤ d.b5
  dg : 0 ≤ d.dg
  da : 0 ≤ d.da
  dc : 0 < d.dc
  srv : 0 ≤ d.srv

/-- The traces around one client k: requests, state, R0, the client's grant `g`, A0 at
its driver, and the client's acknowledge `A` (= A_k). -/
structure Tr where
  r1 : Sig
  r2 : Sig
  q : Sig
  R0 : Sig
  g : Sig
  A0 : Sig
  A : Sig

/-- The gate relations shared by both clients, on the horizon `t < H`; `ua_k` leaves
reset at `t0`. -/
structure Common (d : D) (H t0 : Int) (x : Tr) : Prop where
  st : ∀ t < H, x.q t = stA (x.r1 (t - d.s1)) (x.r2 (t - d.s2)) (x.q (t - d.L)) (x.A0 (t - d.sa))
  r0 : ∀ t < H, x.R0 t = r0A (x.r1 (t - d.u1)) (x.r2 (t - d.u2)) (x.q (t - d.Lr)) (x.A0 (t - d.sa))
  /-- H_SRV: the server answers no earlier than `srv` after R0 was high. -/
  srv : ∀ t, x.A0 t = true → ∃ t', x.R0 t' = true ∧ t' + d.srv ≤ t
  ua : ∀ t < H, t0 ≤ t → x.A t = c2 (x.g (t - d.dg)) (x.A0 (t - d.da)) (x.A (t - d.dc))
  rst : ∀ t < t0, x.A t = false

/-- Client 2's scenario: r1 = step t1, r2 = step t2, q a rising step at T (no q runt),
g = g2 (ugrant O6). -/
structure Scn2 (d : D) (H t1 t2 T t0 : Int) (x : Tr) : Prop extends Common d H t0 x where
  hr1 : ∀ t < H, x.r1 t = step t1 t
  hr2 : ∀ t < H, x.r2 t = step t2 t
  hq : ∀ t < H, x.q t = step T t
  gg : ∀ t < H, x.g t = gr2 (x.r1 (t - d.x1)) (x.r2 (t - d.a2)) (x.q (t - d.b6))

def W2 (d : D) : Int := (d.b6 - d.L) - (d.a2 - d.s2)
def early2 (d : D) : Int := min d.Lr (d.L - d.s2 + d.u2) + d.srv + d.da
def late2 (d : D) : Int := d.b6 + d.dg
/-- **H_RUNT_ACK2.** -/
def Ok2 (d : D) : Prop := W2 d ≤ 0 ∨ late2 d ≤ early2 d

theorem step_t {a t : Int} (h : a ≤ t) : step a t = true := decide_eq_true h
theorem step_f {a t : Int} (h : t < a) : step a t = false := decide_eq_false (by omega)
theorem fstep_t {a t : Int} (h : t < a) : fstep a t = true := decide_eq_true h
theorem fstep_f {a t : Int} (h : a ≤ t) : fstep a t = false := decide_eq_false (by omega)

/-! ## A C-element that never sees both inputs high never rises -/

theorem c_low (A g a : Sig) (dc t0 H : Int) (hdc : 0 < dc)
    (hua : ∀ t < H, t0 ≤ t → A t = c2 (g t) (a t) (A (t - dc)))
    (hr : ∀ t < t0, A t = false)
    (hn : ∀ t < H, t0 ≤ t → ¬ (g t = true ∧ a t = true)) : ∀ t < H, A t = false := by
  have key : ∀ n : Nat, ∀ t, t < t0 + n → t < H → A t = false := by
    intro n
    induction n with
    | zero => intro t ht _; exact hr t (by omega)
    | succ n ih =>
      intro t ht hH
      by_cases h0 : t < t0
      · exact hr t h0
      · rw [hua t hH (by omega), ih (t - dc) (by omega) (by omega), c2_eq]
        have := hn t hH (by omega)
        cases hg : g t <;> cases ha : a t <;> simp_all
  intro t hH
  exact key (t - t0 + 1).toNat t (by omega) hH

/-! ## Client 2 -/

section C2
variable {d : D} {H t1 t2 T t0 : Int} {x : Tr}

/-- r2 reaches ustate's core no earlier than q's own feedback (else q reverses),
whatever A0 does (with both requests up the state LUT holds either way). -/
theorem cons2 (hp : Pos d) (h : Scn2 d H t1 t2 T t0 x) (hH : T + d.L ≤ H) :
    T + d.L ≤ t2 + d.s2 := by
  have hL := hp.L; have hs2 := hp.s2
  refine Int.not_lt.mp fun hlt => ?_
  have ht := h.st (max T (t2 + d.s2)) (by omega)
  rw [h.hq _ (by omega), h.hq _ (by omega), h.hr2 _ (by omega)] at ht
  simp only [step] at ht
  rw [decide_eq_true (by omega : T ≤ max T (t2 + d.s2)),
    decide_eq_false (by omega : ¬ T ≤ max T (t2 + d.s2) - d.L),
    decide_eq_true (by omega : t2 ≤ max T (t2 + d.s2) - d.s2)] at ht
  revert ht
  cases x.r1 (max T (t2 + d.s2) - d.s1) <;> cases x.A0 (max T (t2 + d.s2) - d.sa) <;> decide

/-- R0 cannot rise before `T + min Lr (L - s2 + u2)`. -/
theorem r0lb2 (hp : Pos d) (h : Scn2 d H t1 t2 T t0 x) (hH : T + d.L ≤ H) (t : Int)
    (ht : t < H) (hR : x.R0 t = true) : T + min d.Lr (d.L - d.s2 + d.u2) ≤ t := by
  have hc := cons2 hp h hH
  have := hp.Lr; have := hp.u2
  rw [h.r0 t ht, r0A_eq, gr1_eq, gr2_eq, h.hq _ (by omega), h.hr2 _ (by omega)] at hR
  simp only [step, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hR
  omega

/-- On the horizon g2 is high only inside `[t2 + a2, T + b6)`. -/
theorem gwin2 (hp : Pos d) (h : Scn2 d H t1 t2 T t0 x) (s : Int) (hs : s < H)
    (hg : x.g s = true) : t2 + d.a2 ≤ s ∧ s < T + d.b6 := by
  have := hp.a2; have := hp.b6
  rw [h.gg s hs, gr2_eq, h.hq _ (by omega), h.hr2 _ (by omega)] at hg
  simp only [step, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hg
  omega

/-- **No extra acknowledgement (client 2).** Under H_RUNT_ACK2, A2 never rises on the
horizon. -/
theorem no_extra_ack2 (hp : Pos d) (h : Scn2 d H t1 t2 T t0 x) (hH : T + d.L ≤ H)
    (hok : Ok2 d) : ∀ t < H, x.A t = false := by
  apply c_low x.A (fun t => x.g (t - d.dg)) (fun t => x.A0 (t - d.da)) d.dc t0 H hp.dc
    (fun t ht h0 => h.ua t ht h0) h.rst
  rintro t ht _ ⟨hg, ha⟩
  have hc := cons2 hp h hH
  have := hp.dg; have := hp.da; have := hp.srv
  obtain ⟨h1, h2⟩ := gwin2 hp h (t - d.dg) (by omega) hg
  obtain ⟨t', hR, ht'⟩ := h.srv _ ha
  have := r0lb2 hp h hH t' (by omega) hR
  unfold Ok2 W2 late2 early2 at hok
  omega

/-- **No wrong-index offer (client 2).** Any LUT `y = f (g2 (t - e)) (o t)` (the amerge
index `g2 | A2`, the data mux) outputs its runt-free value at every instant z_req is
high, provided the runt ends at y before z_req can rise. -/
theorem idx_clean2 {α : Type} (hp : Pos d) (h : Scn2 d H t1 t2 T t0 x) (hH : T + d.L ≤ H)
    (f : Bool → α → Bool) (y Z : Sig) (o : Int → α) (e dz : Int) (he : 0 ≤ e) (hdz : 0 ≤ dz)
    (hy : ∀ t < H, y t = f (x.g (t - e)) (o t))
    (hz : ∀ t, Z t = true → ∃ t', x.R0 t' = true ∧ t' + dz ≤ t)
    (hok : W2 d ≤ 0 ∨ d.b6 + e ≤ min d.Lr (d.L - d.s2 + d.u2) + dz) :
    ∀ t < H, Z t = true → y t = f false (o t) := by
  intro t ht hZ
  rw [hy t ht]
  cases hg : x.g (t - e)
  · rfl
  · exfalso
    have hc := cons2 hp h hH
    obtain ⟨h1, h2⟩ := gwin2 hp h (t - e) (by omega) hg
    obtain ⟨t', hR, ht'⟩ := hz t hZ
    have := r0lb2 hp h hH t' (by omega) hR
    unfold W2 at hok
    omega

/-! ### The converse: a concrete trace -/

def ceTr (g a : Sig) (dc t0 : Int) (t : Int) : Bool :=
  if _h : t < t0 then false
  else if _hd : 0 < dc then c2 (g t) (a t) (ceTr g a dc t0 (t - dc)) else false
termination_by (t - t0 + 1).toNat
decreasing_by omega

theorem ceTr_lo (g a : Sig) (dc t0 t : Int) (h : t < t0) : ceTr g a dc t0 t = false := by
  rw [ceTr]; simp [h]

theorem ceTr_hi (g a : Sig) (dc t0 t : Int) (h : t0 ≤ t) (hd : 0 < dc) :
    ceTr g a dc t0 t = c2 (g t) (a t) (ceTr g a dc t0 (t - dc)) := by
  rw [ceTr]; simp [show ¬ t < t0 by omega, hd]

def R0f2 (d : D) : Int := d.s1 + min d.Lr (d.L - d.s2 + d.u2)
def t2w (d : D) : Int := d.s1 + d.L - d.s2

def g2w' (d : D) : Sig := fun t => gr2 (step 0 (t - d.x1)) (step (t2w d) (t - d.a2)) (step d.s1 (t - d.b6))

/-- The witness: r1 at 0, q at T = s1, r2 at the earliest consistent instant, the
server answering at exactly `srv`. -/
def wit2 (d : D) (t0 : Int) : Tr where
  r1 := step 0
  r2 := step (t2w d)
  q := step d.s1
  R0 := step (R0f2 d)
  g := g2w' d
  A0 := step (R0f2 d + d.srv)
  A := ceTr (fun t => g2w' d (t - d.dg)) (fun t => step (R0f2 d + d.srv) (t - d.da)) d.dc t0

theorem wit2_scn (hp : Pos d) (hu1 : d.u1 ≤ d.s1 + d.Lr)
    (hsa : d.L ≤ min d.Lr (d.L - d.s2 + d.u2) + d.srv + d.sa) (H t0 : Int) :
    Scn2 d H 0 (t2w d) d.s1 t0 (wit2 d t0) where
  st := by
    intro t _
    have := hp.L; have := hp.s1
    simp only [wit2, stA_eq, stF_eq, step, R0f2, t2w]
    by_cases h1 : 0 ≤ t - d.s1 <;> by_cases h2 : d.s1 + d.L - d.s2 ≤ t - d.s2 <;>
      by_cases h3 : d.s1 ≤ t - d.L <;> by_cases h4 : d.s1 + min d.Lr (d.L - d.s2 + d.u2) + d.srv ≤ t - d.sa <;>
      by_cases h5 : d.s1 ≤ t <;> simp [h1, h2, h3, h4, h5] <;> omega
  r0 := by
    intro t _
    simp only [wit2, r0A_eq, gr1_eq, gr2_eq, step, R0f2, t2w]
    by_cases h1 : 0 ≤ t - d.u1 <;> by_cases h2 : d.s1 + d.L - d.s2 ≤ t - d.u2 <;>
      by_cases h3 : d.s1 ≤ t - d.Lr <;> by_cases h4 : d.s1 + min d.Lr (d.L - d.s2 + d.u2) ≤ t <;>
      simp [h1, h2, h3, h4] <;> omega
  srv := by
    intro t ht
    refine ⟨R0f2 d, ?_, ?_⟩
    · simp [wit2, step]
    · simp only [wit2, step, decide_eq_true_eq] at ht; omega
  ua := by
    intro t _ h0
    simp only [wit2]
    exact ceTr_hi _ _ _ _ _ h0 hp.dc
  rst := by
    intro t h0
    simp only [wit2]
    exact ceTr_lo _ _ _ _ _ h0
  hr1 := fun _ _ => rfl
  hr2 := fun _ _ => rfl
  hq := fun _ _ => rfl
  gg := fun _ _ => rfl

def tstar2 (d : D) : Int := max (t2w d + d.a2 + d.dg) (R0f2 d + d.srv + d.da)

/-- **The extra acknowledgement (client 2).** When the runt exists and outlives the
earliest A0 at ua2, the witness trace (which satisfies every gate relation,
`wit2_scn`) has: R0 rising exactly once (`step (R0f2 d)`), ustate's core never seeing
r2 with q low, and A2 high at `tstar2`. -/
theorem extra_ack2 (hp : Pos d) (hW : 0 < W2 d) (hlate : early2 d < late2 d) (t0 : Int)
    (ht0 : t0 ≤ tstar2 d) :
    (wit2 d t0).A (tstar2 d) = true ∧
    (∀ t, (wit2 d t0).R0 t = step (R0f2 d) t) ∧
    (∀ t, ¬ ((wit2 d t0).r2 (t - d.s2) = true ∧ (wit2 d t0).q (t - d.L) = false)) := by
  refine ⟨?_, fun _ => rfl, ?_⟩
  · simp only [wit2]
    rw [ceTr_hi _ _ _ _ _ ht0 hp.dc, c2_eq]
    unfold W2 at hW; unfold early2 late2 at hlate
    have h1 : t2w d ≤ tstar2 d - d.dg - d.a2 := by unfold tstar2; omega
    have h2 : tstar2 d - d.dg - d.b6 < d.s1 := by unfold tstar2 t2w R0f2; omega
    have h3 : R0f2 d + d.srv ≤ tstar2 d - d.da := by unfold tstar2; omega
    have hg : g2w' d (tstar2 d - d.dg) = true := by
      simp only [g2w']; rw [gr2_eq, step_t h1, step_f h2]; rfl
    have ha : step (R0f2 d + d.srv) (tstar2 d - d.da) = true := step_t h3
    rw [hg, ha]; rfl
  · intro t
    simp only [wit2, step, t2w, decide_eq_true_eq, decide_eq_false_iff_not]
    omega

/-- In the same witness client 1 is acknowledged too (for any ua1 delays): two
acknowledgements for the one R0 rise. -/
theorem extra_ack2_both (hp : Pos d) (a1 x2 b5 dg1 da1 dc1 t0' : Int) (hdc1 : 0 < dc1) :
    let g1 : Sig := fun t => gr1 (step 0 (t - a1)) (step (t2w d) (t - x2)) (step d.s1 (t - b5))
    let s := max (max a1 (d.s1 + b5) + dg1) (R0f2 d + d.srv + da1)
    t0' ≤ s →
    ceTr (fun t => g1 (t - dg1)) (fun t => step (R0f2 d + d.srv) (t - da1)) dc1 t0' s = true := by
  intro g1 s hs
  rw [ceTr_hi _ _ _ _ _ hs hdc1, c2_eq]
  have h1 : 0 ≤ s - dg1 - a1 := by simp only [s]; omega
  have h2 : d.s1 ≤ s - dg1 - b5 := by simp only [s]; omega
  have h3 : R0f2 d + d.srv ≤ s - da1 := by simp only [s]; omega
  have hg : g1 (s - dg1) = true := by
    simp only [g1]; rw [gr1_eq, step_t h1, step_t h2]; rfl
  rw [hg, step_t h3]; rfl

/-- **H_RUNT_ACK2 is exact.** Under the physical side conditions `hu1` (r1 reaches R0's
core before the q it caused) and `hsa` (A0 reaches ustate after q's own feedback), a
scenario with an extra acknowledgement exists iff `Ok2` fails. -/
theorem spurious_ack2_iff (hp : Pos d) (hu1 : d.u1 ≤ d.s1 + d.Lr)
    (hsa : d.L ≤ min d.Lr (d.L - d.s2 + d.u2) + d.srv + d.sa) :
    (∃ H t1 t2 T t0 x, T + d.L ≤ H ∧ Scn2 d H t1 t2 T t0 x ∧ ∃ t < H, x.A t = true) ↔
      (0 < W2 d ∧ early2 d < late2 d) := by
  constructor
  · rintro ⟨H, t1, t2, T, t0, x, hH, h, t, ht, hA⟩
    have : ¬ Ok2 d := fun hok => by
      rw [no_extra_ack2 hp h hH hok t ht] at hA; exact absurd hA (by decide)
    unfold Ok2 at this; omega
  · rintro ⟨hW, hl⟩
    refine ⟨max (tstar2 d + 1) (d.s1 + d.L), 0, t2w d, d.s1, tstar2 d, wit2 d (tstar2 d), ?_,
      wit2_scn hp hu1 hsa _ _, tstar2 d, ?_, (extra_ack2 hp hW hl _ (Int.le_refl _)).1⟩
    · omega
    · omega

/-- bdc's amerge index `won = g2 | A2` (INIT `1110`). -/
def idxLut (g a : Bool) : Bool := lutB 0xE [g, a]

theorem idxLut_eq (g a : Bool) : idxLut g a = (g || a) := by cases g <;> cases a <;> rfl

/-- **The wrong-index offer (client 2).** If the runt exists and outlives the earliest
z_req, then in the witness (client 1 granted, q never falls) z_req (rising exactly `dz`
after R0) is high while the index LUT, whatever its other input, outputs 1. -/
theorem wrong_index2 (hp : Pos d) (hW : 0 < W2 d) (e dz : Int) (hdz : 0 ≤ dz)
    (hs2 : d.s2 ≤ d.L + d.u2)
    (hlate : min d.Lr (d.L - d.s2 + d.u2) + dz < d.b6 + e) (a : Sig) :
    let s := max (t2w d + d.a2 + e) (R0f2 d + dz)
    step (R0f2 d + dz) s = true ∧ idxLut ((wit2 d 0).g (s - e)) (a s) = true ∧
      (wit2 d 0).q s = true := by
  intro s
  have := hp.Lr
  unfold W2 at hW
  have h0 : R0f2 d + dz ≤ s := by simp only [s]; omega
  have h1 : t2w d ≤ s - e - d.a2 := by simp only [s]; omega
  have h2 : s - e - d.b6 < d.s1 := by simp only [s, t2w, R0f2]; omega
  have h3 : d.s1 ≤ s := by simp only [s, R0f2]; omega
  refine ⟨step_t h0, ?_, step_t h3⟩
  rw [idxLut_eq]
  have : (wit2 d 0).g (s - e) = true := by
    simp only [wit2, g2w']; rw [gr2_eq, step_t h1, step_f h2]; rfl
  rw [this]; rfl

end C2

/-! ## Client 1 (mirror): q falls for r2, r1 rises late, g1 = r1·q runt on O5 -/

structure Scn1 (d : D) (H t1 t2 T t0 : Int) (x : Tr) : Prop extends Common d H t0 x where
  hr1 : ∀ t < H, x.r1 t = step t1 t
  hr2 : ∀ t < H, x.r2 t = step t2 t
  hq : ∀ t < H, x.q t = fstep T t
  gg : ∀ t < H, x.g t = gr1 (x.r1 (t - d.a1)) (x.r2 (t - d.x2)) (x.q (t - d.b5))

def W1 (d : D) : Int := (d.b5 - d.L) - (d.a1 - d.s1)
def early1 (d : D) : Int := min d.Lr (d.L - d.s1 + d.u1) + d.srv + d.da
def late1 (d : D) : Int := d.b5 + d.dg
/-- **H_RUNT_ACK1.** -/
def Ok1 (d : D) : Prop := W1 d ≤ 0 ∨ late1 d ≤ early1 d

section C1
variable {d : D} {H t1 t2 T t0 : Int} {x : Tr}

theorem cons1 (hp : Pos d) (h : Scn1 d H t1 t2 T t0 x) (hH : T + d.L ≤ H) :
    T + d.L ≤ t1 + d.s1 := by
  have hL := hp.L; have hs1 := hp.s1
  refine Int.not_lt.mp fun hlt => ?_
  have ht := h.st (max T (t1 + d.s1)) (by omega)
  rw [h.hq _ (by omega), h.hq _ (by omega), h.hr1 _ (by omega)] at ht
  simp only [step, fstep] at ht
  rw [decide_eq_false (by omega : ¬ max T (t1 + d.s1) < T),
    decide_eq_true (by omega : max T (t1 + d.s1) - d.L < T),
    decide_eq_true (by omega : t1 ≤ max T (t1 + d.s1) - d.s1)] at ht
  revert ht
  cases x.r2 (max T (t1 + d.s1) - d.s2) <;> cases x.A0 (max T (t1 + d.s1) - d.sa) <;> decide

theorem r0lb1 (hp : Pos d) (h : Scn1 d H t1 t2 T t0 x) (hH : T + d.L ≤ H) (t : Int)
    (ht : t < H) (hR : x.R0 t = true) : T + min d.Lr (d.L - d.s1 + d.u1) ≤ t := by
  have hc := cons1 hp h hH
  have := hp.Lr; have := hp.u1
  rw [h.r0 t ht, r0A_eq, gr1_eq, gr2_eq, h.hq _ (by omega), h.hr1 _ (by omega)] at hR
  simp only [step, fstep, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hR
  omega

theorem gwin1 (hp : Pos d) (h : Scn1 d H t1 t2 T t0 x) (s : Int) (hs : s < H)
    (hg : x.g s = true) : t1 + d.a1 ≤ s ∧ s < T + d.b5 := by
  have := hp.a1; have := hp.b5
  rw [h.gg s hs, gr1_eq, h.hq _ (by omega), h.hr1 _ (by omega)] at hg
  simp only [step, fstep, Bool.and_eq_true, decide_eq_true_eq] at hg
  omega

/-- **No extra acknowledgement (client 1).** -/
theorem no_extra_ack1 (hp : Pos d) (h : Scn1 d H t1 t2 T t0 x) (hH : T + d.L ≤ H)
    (hok : Ok1 d) : ∀ t < H, x.A t = false := by
  apply c_low x.A (fun t => x.g (t - d.dg)) (fun t => x.A0 (t - d.da)) d.dc t0 H hp.dc
    (fun t ht h0 => h.ua t ht h0) h.rst
  rintro t ht _ ⟨hg, ha⟩
  have hc := cons1 hp h hH
  have := hp.dg; have := hp.da; have := hp.srv
  obtain ⟨h1, h2⟩ := gwin1 hp h (t - d.dg) (by omega) hg
  obtain ⟨t', hR, ht'⟩ := h.srv _ ha
  have := r0lb1 hp h hH t' (by omega) hR
  unfold Ok1 W1 late1 early1 at hok
  omega

def R0f1 (d : D) : Int := d.s2 + min d.Lr (d.L - d.s1 + d.u1)
def t1w (d : D) : Int := d.s2 + d.L - d.s1
def g1w' (d : D) : Sig := fun t => gr1 (step (t1w d) (t - d.a1)) (step 0 (t - d.x2)) (fstep d.s2 (t - d.b5))

def wit1 (d : D) (t0 : Int) : Tr where
  r1 := step (t1w d)
  r2 := step 0
  q := fstep d.s2
  R0 := step (R0f1 d)
  g := g1w' d
  A0 := step (R0f1 d + d.srv)
  A := ceTr (fun t => g1w' d (t - d.dg)) (fun t => step (R0f1 d + d.srv) (t - d.da)) d.dc t0

theorem wit1_scn (hp : Pos d) (hu2 : d.u2 ≤ d.s2 + d.Lr)
    (hsa : d.L ≤ min d.Lr (d.L - d.s1 + d.u1) + d.srv + d.sa) (H t0 : Int) :
    Scn1 d H (t1w d) 0 d.s2 t0 (wit1 d t0) where
  st := by
    intro t _
    have := hp.L; have := hp.s2
    simp only [wit1, stA_eq, stF_eq, step, fstep, R0f1, t1w]
    by_cases h1 : d.s2 + d.L - d.s1 ≤ t - d.s1 <;> by_cases h2 : 0 ≤ t - d.s2 <;>
      by_cases h3 : t - d.L < d.s2 <;> by_cases h4 : d.s2 + min d.Lr (d.L - d.s1 + d.u1) + d.srv ≤ t - d.sa <;>
      by_cases h5 : t < d.s2 <;> simp [h1, h2, h3, h4, h5] <;> omega
  r0 := by
    intro t _
    simp only [wit1, r0A_eq, gr1_eq, gr2_eq, step, fstep, R0f1, t1w]
    by_cases h1 : d.s2 + d.L - d.s1 ≤ t - d.u1 <;> by_cases h2 : 0 ≤ t - d.u2 <;>
      by_cases h3 : t - d.Lr < d.s2 <;> by_cases h4 : d.s2 + min d.Lr (d.L - d.s1 + d.u1) ≤ t <;>
      simp [h1, h2, h3, h4] <;> omega
  srv := by
    intro t ht
    refine ⟨R0f1 d, ?_, ?_⟩
    · simp [wit1, step]
    · simp only [wit1, step, decide_eq_true_eq] at ht; omega
  ua := by
    intro t _ h0
    simp only [wit1]
    exact ceTr_hi _ _ _ _ _ h0 hp.dc
  rst := by
    intro t h0
    simp only [wit1]
    exact ceTr_lo _ _ _ _ _ h0
  hr1 := fun _ _ => rfl
  hr2 := fun _ _ => rfl
  hq := fun _ _ => rfl
  gg := fun _ _ => rfl

def tstar1 (d : D) : Int := max (t1w d + d.a1 + d.dg) (R0f1 d + d.srv + d.da)

/-- **The extra acknowledgement (client 1).** -/
theorem extra_ack1 (hp : Pos d) (hW : 0 < W1 d) (hlate : early1 d < late1 d) (t0 : Int)
    (ht0 : t0 ≤ tstar1 d) :
    (wit1 d t0).A (tstar1 d) = true ∧
    (∀ t, (wit1 d t0).R0 t = step (R0f1 d) t) ∧
    (∀ t, ¬ ((wit1 d t0).r1 (t - d.s1) = true ∧ (wit1 d t0).q (t - d.L) = true)) := by
  refine ⟨?_, fun _ => rfl, ?_⟩
  · simp only [wit1]
    rw [ceTr_hi _ _ _ _ _ ht0 hp.dc, c2_eq]
    unfold W1 at hW; unfold early1 late1 at hlate
    have h1 : t1w d ≤ tstar1 d - d.dg - d.a1 := by unfold tstar1; omega
    have h2 : tstar1 d - d.dg - d.b5 < d.s2 := by unfold tstar1 t1w R0f1; omega
    have h3 : R0f1 d + d.srv ≤ tstar1 d - d.da := by unfold tstar1; omega
    have hg : g1w' d (tstar1 d - d.dg) = true := by
      simp only [g1w']; rw [gr1_eq, step_t h1, fstep_t h2]; rfl
    have ha : step (R0f1 d + d.srv) (tstar1 d - d.da) = true := step_t h3
    rw [hg, ha]; rfl
  · intro t
    simp only [wit1, step, fstep, t1w, decide_eq_true_eq]
    omega

theorem spurious_ack1_iff (hp : Pos d) (hu2 : d.u2 ≤ d.s2 + d.Lr)
    (hsa : d.L ≤ min d.Lr (d.L - d.s1 + d.u1) + d.srv + d.sa) :
    (∃ H t1 t2 T t0 x, T + d.L ≤ H ∧ Scn1 d H t1 t2 T t0 x ∧ ∃ t < H, x.A t = true) ↔
      (0 < W1 d ∧ early1 d < late1 d) := by
  constructor
  · rintro ⟨H, t1, t2, T, t0, x, hH, h, t, ht, hA⟩
    have : ¬ Ok1 d := fun hok => by
      rw [no_extra_ack1 hp h hH hok t ht] at hA; exact absurd hA (by decide)
    unfold Ok1 at this; omega
  · rintro ⟨hW, hl⟩
    refine ⟨max (tstar1 d + 1) (d.s2 + d.L), t1w d, 0, d.s2, tstar1 d, wit1 d (tstar1 d), ?_,
      wit1_scn hp hu2 hsa _ _, tstar1 d, ?_, (extra_ack1 hp hW hl _ (Int.le_refl _)).1⟩
    · omega
    · omega

end C1

/-! ## The routed checker

`Row` = the prefix-cancelled routed quantities of one client at one corner (ps). The
lumped delays are prefix + suffix + arc with ONE prefix `cq` per q net and `cr` per
r_k net (H_SHARED_PREFIX, C-10i's `lumped_W`):
`L = cq+dqs+asq`, `s_k = cr+drs+asr`, `Lr = cq+dqs5+aRq`, `u_k = cr+drs5+aRr`,
`b = cq+dqg+agq`, `a_k = cr+drg+agr`, `dg = gw+ga`, and the server bound
`P + aa ≤ srv + da` (P: min path R0 → ua_k's A0 pin, `cert_bound`; aa: ua_k's A0 arc).
For the index check use `gw + ga` = reader route + arc, `P` = min path R0 → z_req,
`aa = 0`. -/

structure Row where
  dqg : Int
  dqs : Int
  drg : Int
  drs : Int
  agq : Int
  agr : Int
  asq : Int
  asr : Int
  dqs5 : Int
  drs5 : Int
  aRq : Int
  aRr : Int
  gw : Int
  ga : Int
  aa : Int
  P : Int
deriving Repr

def Row.W (x : Row) : Int := (x.dqg + x.agq) - (x.dqs + x.asq) - ((x.drg + x.agr) - (x.drs + x.asr))
def Row.late (x : Row) : Int := x.dqg + x.agq + x.gw + x.ga
def Row.early (x : Row) : Int :=
  min (x.dqs5 + x.aRq) (x.dqs + x.asq - (x.drs + x.asr) + (x.drs5 + x.aRr)) + x.P + x.aa
def okAck (x : Row) : Bool := decide (x.W ≤ 0 ∨ x.late ≤ x.early)
/-- the margin reported (negative = the race is live at this point) -/
def Row.margin (x : Row) : Int := x.early - x.late

/-- `d` realises row `x` for client 2 with prefixes `cq`, `cr`. -/
structure Real2 (x : Row) (d : D) (cq cr : Int) : Prop where
  L : d.L = cq + x.dqs + x.asq
  s : d.s2 = cr + x.drs + x.asr
  Lr : d.Lr = cq + x.dqs5 + x.aRq
  u : d.u2 = cr + x.drs5 + x.aRr
  b : d.b6 = cq + x.dqg + x.agq
  a : d.a2 = cr + x.drg + x.agr
  g : d.dg = x.gw + x.ga
  E : x.P + x.aa ≤ d.srv + d.da

structure Real1 (x : Row) (d : D) (cq cr : Int) : Prop where
  L : d.L = cq + x.dqs + x.asq
  s : d.s1 = cr + x.drs + x.asr
  Lr : d.Lr = cq + x.dqs5 + x.aRq
  u : d.u1 = cr + x.drs5 + x.aRr
  b : d.b5 = cq + x.dqg + x.agq
  a : d.a1 = cr + x.drg + x.agr
  g : d.dg = x.gw + x.ga
  E : x.P + x.aa ≤ d.srv + d.da

theorem okAck_sound2 (x : Row) (d : D) (cq cr : Int) (hr : Real2 x d cq cr)
    (hok : okAck x = true) : Ok2 d := by
  unfold okAck at hok; simp only [decide_eq_true_eq] at hok
  unfold Ok2 W2 late2 early2
  unfold Row.W Row.late Row.early at hok
  rw [hr.L, hr.s, hr.Lr, hr.u, hr.b, hr.a, hr.g]
  have := hr.E
  omega

theorem okAck_sound1 (x : Row) (d : D) (cq cr : Int) (hr : Real1 x d cq cr)
    (hok : okAck x = true) : Ok1 d := by
  unfold okAck at hok; simp only [decide_eq_true_eq] at hok
  unfold Ok1 W1 late1 early1
  unfold Row.W Row.late Row.early at hok
  rw [hr.L, hr.s, hr.Lr, hr.u, hr.b, hr.a, hr.g]
  have := hr.E
  omega

/-- A failing row is a real violation when the server answers at its bound
(`srv + da = P + aa`). -/
theorem okAck_exact2 (x : Row) (d : D) (cq cr : Int) (hr : Real2 x d cq cr)
    (hE : d.srv + d.da = x.P + x.aa) (hok : okAck x = false) : 0 < W2 d ∧ early2 d < late2 d := by
  unfold okAck at hok; simp only [decide_eq_false_iff_not] at hok
  unfold W2 late2 early2
  unfold Row.W Row.late Row.early at hok
  rw [hr.L, hr.s, hr.Lr, hr.u, hr.b, hr.a, hr.g]
  omega

theorem okAck_exact1 (x : Row) (d : D) (cq cr : Int) (hr : Real1 x d cq cr)
    (hE : d.srv + d.da = x.P + x.aa) (hok : okAck x = false) : 0 < W1 d ∧ early1 d < late1 d := by
  unfold okAck at hok; simp only [decide_eq_false_iff_not] at hok
  unfold W1 late1 early1
  unfold Row.W Row.late Row.early at hok
  rw [hr.L, hr.s, hr.Lr, hr.u, hr.b, hr.a, hr.g]
  omega

/-- **Routed instance, client 2: a passing row means no extra acknowledgement**, at
every delay assignment realising it (any prefixes) and every trace of the scenario. -/
theorem inst_no_extra_ack2 (x : Row) (hok : okAck x = true) (d : D) (cq cr : Int)
    (hr : Real2 x d cq cr) (hp : Pos d) {H t1 t2 T t0 : Int} {tr : Tr}
    (h : Scn2 d H t1 t2 T t0 tr) (hH : T + d.L ≤ H) : ∀ t < H, tr.A t = false :=
  no_extra_ack2 hp h hH (okAck_sound2 x d cq cr hr hok)

theorem inst_no_extra_ack1 (x : Row) (hok : okAck x = true) (d : D) (cq cr : Int)
    (hr : Real1 x d cq cr) (hp : Pos d) {H t1 t2 T t0 : Int} {tr : Tr}
    (h : Scn1 d H t1 t2 T t0 tr) (hH : T + d.L ≤ H) : ∀ t < H, tr.A t = false :=
  no_extra_ack1 hp h hH (okAck_sound1 x d cq cr hr hok)

/-- **Routed instance, index:** a passing index row (`gw + ga` = reader route + arc as
`e`, `P` ≤ `dz`, `aa = 0`) means no wrong-index offer. -/
theorem inst_idx_clean2 {α : Type} (x : Row) (hok : okAck x = true) (d : D) (cq cr : Int)
    (hL : d.L = cq + x.dqs + x.asq) (hs : d.s2 = cr + x.drs + x.asr)
    (hLr : d.Lr = cq + x.dqs5 + x.aRq) (hu : d.u2 = cr + x.drs5 + x.aRr)
    (hb : d.b6 = cq + x.dqg + x.agq) (ha : d.a2 = cr + x.drg + x.agr)
    (hp : Pos d) {H t1 t2 T t0 : Int} {tr : Tr} (h : Scn2 d H t1 t2 T t0 tr) (hH : T + d.L ≤ H)
    (f : Bool → α → Bool) (y Z : Sig) (o : Int → α) (e dz : Int) (he : e = x.gw + x.ga)
    (he0 : 0 ≤ e) (hdz : x.P + x.aa ≤ dz)
    (hdz0 : 0 ≤ dz) (hy : ∀ t < H, y t = f (tr.g (t - e)) (o t))
    (hz : ∀ t, Z t = true → ∃ t', tr.R0 t' = true ∧ t' + dz ≤ t) :
    ∀ t < H, Z t = true → y t = f false (o t) := by
  refine idx_clean2 hp h hH f y Z o e dz he0 hdz0 hy hz ?_
  unfold okAck at hok; simp only [decide_eq_true_eq] at hok
  unfold W2
  unfold Row.W Row.late Row.early at hok
  rw [hL, hs, hLr, hu, hb, ha, he]
  omega

/-! ## Potential certificates for minimum path lengths (H_CAUSAL_PATH)

A timing graph `G` is a list of arcs `(u, v, w)`, `w` = the arc's lower delay bound at
the corner. A certificate gives a truncated potential `p ≤ M` with `p src = 0` and
`p v ≤ p u + w` on every listed arc; the arcs that must be listed are exactly those
leaving a node with `p u < M` (`Complete`, the extractor's completeness claim). Then
every path from `src` to `v` is at least `p v` long (`cert_bound`). -/

inductive PTree where
  | leaf
  | node (k v : Nat) (l r : PTree)

def PTree.find (M : Nat) : PTree → Nat → Nat
  | leaf, _ => M
  | node k v l r, x => if Nat.blt x k then l.find M x else if Nat.blt k x then r.find M x else v

structure Cert where
  M : Nat
  src : Nat
  pot : PTree
  edges : List (Nat × Nat × Nat)

def Cert.p (c : Cert) (x : Nat) : Nat := min (c.pot.find c.M x) c.M

def Cert.ok (c : Cert) : Bool :=
  Nat.beq (c.p c.src) 0 && c.edges.all (fun e => Nat.ble (c.p e.2.1) (c.p e.1 + e.2.2))

def Complete (c : Cert) (G : List (Nat × Nat × Nat)) : Prop :=
  ∀ e ∈ G, c.p e.1 < c.M → e ∈ c.edges

inductive Path (G : List (Nat × Nat × Nat)) (s : Nat) : Nat → Nat → Prop
  | nil : Path G s s 0
  | cons {u v len w : Nat} : Path G s u len → (u, v, w) ∈ G → Path G s v (len + w)

theorem cert_bound (c : Cert) (G : List (Nat × Nat × Nat)) (hok : c.ok = true)
    (hc : Complete c G) {v len : Nat} (hp : Path G c.src v len) : c.p v ≤ len := by
  unfold Cert.ok at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.ble_eq] at hok
  obtain ⟨h0, he⟩ := hok
  induction hp with
  | nil => omega
  | @cons u v len w _ hmem ih =>
    have hle : ∀ y, c.p y ≤ c.M := fun y => Nat.min_le_right _ _
    by_cases hu : c.p u < c.M
    · have := he _ (hc _ hmem hu); simp only at this; omega
    · have := hle v; have := hle u; omega

end Formal.Timing.RuntAck
