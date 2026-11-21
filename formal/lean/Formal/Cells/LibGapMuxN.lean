import Formal.Cells.LibGapMux
import Formal.Cells.AMergeGates

/-!
# LibGapMuxN: `bdc_muxn`'s select timing at the joins, per pin, per index bit, exact

Probe Bmn (shard B, Phase 2 library gap, follow-up of `LibGapMux`, which
covers `bd_mux` and explicitly NOT `bdc_muxn`).

`bdc_muxn{n}_{w}` (`bdc/emit.py` `emit_muxn`; gcd_hw has one, `bdc_muxn3_32`,
its 3-way loop header) does NOT fold the decode into the join LUT as `bd_mux`
does. It emits

    assign sel[k] = ctl_req & (s == 2'dk);           // ordinary logic, yosys maps it
    bd_c2 uj{k} (.a(in{k}_req), .b(sel[k]), .rst(rst), .q(j[k]));

so each join is TWO LUTs: a combinational decode LUT3 (inferred INITs, from
`AMergeGates`, hypothesis **H_YOSYS_MAP**: `sel[0]` = `8'h10` on
`[s0, s1, ctl_req]`, `sel[1]` = `8'h40` on `[s1, s0, ctl_req]`, `sel[2]` =
`8'h40` on `[s0, s1, ctl_req]`), a wire `sel[k] -> uj_k.I1`, and the frozen
`bd_c2` (`00E8_00E8_00E8_00E8`, pins `a b q rst`) with its feedback. The
index has TWO bits, each its own wire and decode pin with its own window.

## Model (named hypotheses)

* **H_PIN_READ (decode)** (`DecEq`): for EVERY `t` the decode output `D t` is
  its INIT applied to `s0` read at `p0.σ t`, `s1` at `p1.σ t`, `ctl_req` at
  `pc.σ t` (per-pin read maps, `Rd` of `LibGapSteer`: wire + site pin + that
  pin's arc, not necessarily monotone). The decode has no reset and no state.
* **H_PIN_READ (join)** (`JEq`): for `t ≥ 0` the join output is `bd_c2`'s INIT
  of the request read at `pr.σ t`, the decode output at `pd.σ t` (the
  `sel -> uj.I1` wire + SP + arc) and its own output at `pq.σ t` (feedback).
  `rst` reads 0 from 0 on.
* **H_RESET** (`Rest`): the join is 0 before 0.
* **H_CTL_PULSE**: `ctl_req` at its driver is high exactly on `[Cr, Cf)`.
* The index: either a GIVEN trace per bit (`join_exact_fixed`, any traces),
  **H_S_STABLE_BIT** (`M1`: bit `i` shows `bit_i v` on its own window
  `[S0_i, S1_i)`, arbitrary outside), or **H_S_STEP** (`M2`: bit `i` changes
  ONCE, cleanly, at `T_i`, from the previous code's bit to the token's).
* **H_S_RANGE**: codes `< 3` (the code `3` = `11` decodes to no join).
* The client request is arbitrary.

## Spec (`NSpec`)

`j t = c2(r read, ctl_req read through the decode && (v == k), j read)`: the
join is `bd_c2` on (request, ctl_req) when the token selects it, and stays 0
(with H_RESET) when it does not. ctl_req is read through the COMPOSITE map
`pc ∘ pd`.

## Results

* `join_exact_fixed` (the core, fixed per-pin delays, ANY index-bit traces):
  NSpec for every request trace and every trace obeying H_PIN_READ + H_RESET
  **iff** there is no instant `u` where ctl_req reads 1 at the decode and the
  decode's per-bit reading of the code disagrees with the token about `k`
  (`Bad`). The decode→join wire, the request pin and the feedback pin drop out.
* `maps_ok` / `maps_needed`: the same with read maps in a delay box.
* M1, box exact: `sel_box_exact` (selected join, `v = k`): iff
  **both** bits meet setup `S0_i + hi_i ≤ Cr + Clo` and hold
  `Cf + Chi ≤ S1_i + lo_i` (the `bd_mux` form, once per bit, decode pins only).
  `unsel_box_exact` (`v ≠ k`): iff `Cover`: every instant at which ctl_req
  may read 1 lies inside the read-stable window of SOME bit in which `k` and
  `v` differ. One differing bit (`{k,v}` ∋ 0) gives the single-bit form; for
  `{k,v} = {1,2}` the two windows may cover the ctl window TOGETHER
  (`cover2_iff`, closed form).
* `sel_cond_cover`, `decode_exact_all_tokens`: each decode's per-bit
  setup/hold implies every unselected join's `Cover`, so "for every token
  value" the per-bit condition at decode `k` is exact.
* M2, the THIRD branch (`third_fixed_exact`, `third_box_exact`): the index
  changes `1 -> 2` or `2 -> 1` (both bits change; the intermediate code `00`
  selects join 0, which neither token wants; `11` selects nothing). Join 0
  is correct iff **H_NO_THIRD**:
  `Cf + Chi ≤ Tf + lo_f ∨ Tr + hi_r ≤ Cr + Clo ∨ Tr + hi_r ≤ Tf + lo_f`
  (`r`: the bit going 0→1, `f`: the bit going 1→0): ctl_req's read window is
  over before the falling bit can be read changed, or the rising bit is set
  up before ctl_req can be read high, or the rising bit is read changed
  before the falling bit can be (the transition passes through `11`). The
  same lemma serves the hold side (`v -> n`).
* `step_sel_exact` (selected join after a clean step: iff BOTH changed bits
  are read changed by the time ctl_req reads 1), `step_old_exact` (the old
  branch is excluded once ONE changed bit is), `third_implied_by_setup`
  (whenever the selected join is correct, join 0 is: the third branch is
  never the only failure), `rise_first_example` (rise-first: join 0 correct,
  the selected join fires late: an NSpec deviation, not a wrong token).
* Counter-traces: `third_branch_latched` (1→2, the rising bit read 600 ps
  late: join 0 with in0_req waiting latches 1 for ever: input 0's token is
  consumed by a control token meant for input 2). Non-vacuity:
  `witness_third` (join 0 is 0 at every instant and join 2 fires, same cell,
  good timing).

NOT covered: the `ua_k` acks, `|j`, the line, z bundling (`MuxN3Timed`); the
ctl_req and s forks as cross-decode obligations (each decode has its own maps
here); where `S0`, `S1`, `T_i` come from (the control sender's contract);
reset timing; Kleene X on the bits (mid-rail select, H_KLEENE_LUT); internal
mux-tree delay (folded into per-pin arcs); correlated pin delays (box
necessity takes pins independent: use `join_exact_fixed` per realisation);
`n > 3` (more bits, possibly a decode split over several LUTs: not mapped);
several tokens (per token only).
-/

namespace Formal.Cells.LibGapMuxN
open Formal.Cells
open Formal.Cells.LibGapSteer (Rd pulse Stable)
open Formal.Cells.LibGapMux (int_ind run run_eq run_rest)
open Formal.Cells.AMergeGates (sel0 sel1 sel2 c2 sel0_eq sel1_eq sel2_eq c2_eq)

/-! ## 0. Gates from the real INITs -/

def bit0 (v : Nat) : Bool := v % 2 == 1
def bit1 (v : Nat) : Bool := v / 2 % 2 == 1
/-- The code the decode sees on its two index pins. -/
def code (s0 s1 : Bool) : Nat := (if s0 then 1 else 0) + (if s1 then 2 else 0)

theorem code_eq_iff (s0 s1 : Bool) (v : Nat) (hv : v < 4) :
    code s0 s1 = v ↔ (s0 = bit0 v ∧ s1 = bit1 v) := by
  obtain rfl | rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
  all_goals cases s0 <;> cases s1 <;> decide

theorem code_bits (v : Nat) (hv : v < 4) : code (bit0 v) (bit1 v) = v :=
  (code_eq_iff _ _ v hv).mpr ⟨rfl, rfl⟩

/-- Decode `k` (REAL inferred LUT3 INITs, pin orders of H_YOSYS_MAP). -/
def dec : Nat → Bool → Bool → Bool → Bool
  | 0 => sel0
  | 1 => sel1
  | _ => sel2

/-- `sel[k] = ctl_req & (s == k)`: from the INITs. -/
theorem dec_eq (k : Nat) (hk : k < 3) (s0 s1 c : Bool) :
    dec k s0 s1 c = (c && (code s0 s1 == k)) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals cases s0 <;> cases s1 <;> cases c <;> decide

/-- `bd_c2`: the join's output differs between two decode values iff they
differ and the request read differs from the feedback read. -/
theorem c2_dev : ∀ a b b' q : Bool, c2 a b q ≠ c2 a b' q ↔ (b ≠ b' ∧ a ≠ q) := by decide
theorem c2_low : ∀ a : Bool, c2 a false false = false := by decide
theorem c2_11 : ∀ q : Bool, c2 true true q = true := by decide
theorem c2_x11 : ∀ a : Bool, c2 a true true = true := by decide
theorem c2_1x1 : ∀ b : Bool, c2 true b true = true := by decide

/-! ## 1. Relations -/

/-- **H_PIN_READ** at the decode LUT3 (combinational, every `t`). -/
def DecEq (k : Nat) (p0 p1 pc : Rd) (s0 s1 c D : Int → Bool) : Prop :=
  ∀ t, D t = dec k (s0 (p0.σ t)) (s1 (p1.σ t)) (c (pc.σ t))

/-- **H_PIN_READ** at the join `bd_c2` (rst released at 0). -/
def JEq (pr pd pq : Rd) (r D j : Int → Bool) : Prop :=
  ∀ t, 0 ≤ t → j t = c2 (r (pr.σ t)) (D (pd.σ t)) (j (pq.σ t))

/-- **H_RESET**. -/
def Rest (j : Int → Bool) : Prop := ∀ t, t < 0 → j t = false

/-- The spec: the decode replaced by the token's value. -/
def NSpec (k v : Nat) (pr pd pc pq : Rd) (r c j : Int → Bool) : Prop :=
  ∀ t, 0 ≤ t → j t = c2 (r (pr.σ t)) (c (pc.σ (pd.σ t)) && (v == k)) (j (pq.σ t))

/-! ## 2. Sufficient, any read maps -/

theorem join_ok_of_reads (k v : Nat) (hk : k < 3) (pr pd pc p0 p1 pq : Rd)
    (r c s0 s1 D j : Int → Bool) (hD : DecEq k p0 p1 pc s0 s1 c D) (hJ : JEq pr pd pq r D j)
    (hrd : ∀ u, c (pc.σ u) = true → (code (s0 (p0.σ u)) (s1 (p1.σ u)) == k) = (v == k)) :
    NSpec k v pr pd pc pq r c j := by
  intro t ht
  rw [hJ t ht, hD, dec_eq k hk]
  cases hc : c (pc.σ (pd.σ t))
  · rfl
  · simp only [Bool.true_and]; rw [hrd _ hc]

/-- Unselected join: NSpec + H_RESET + a positive loop ⇒ 0 for ever. -/
theorem unsel_low (k v : Nat) (hvk : v ≠ k) (pr pd pc pq : Rd) (hq : 1 ≤ pq.lo)
    (r c j : Int → Bool) (hS : NSpec k v pr pd pc pq r c j) (hR : Rest j) : ∀ t, j t = false := by
  have hf : (v == k) = false := by simp [hvk]
  apply int_ind (fun t => j t = false) hR
  intro t ht ih
  rw [hS t ht, hf, Bool.and_false, ih _ (by have := pq.le t; omega)]
  exact c2_low _

/-- Selected join: request and ctl_req (through the decode) read 1 ⇒ 1. -/
theorem sel_fires (k : Nat) (pr pd pc pq : Rd) (r c j : Int → Bool)
    (hS : NSpec k k pr pd pc pq r c j) (t : Int) (ht : 0 ≤ t)
    (hr : r (pr.σ t) = true) (hc : c (pc.σ (pd.σ t)) = true) : j t = true := by
  rw [hS t ht, hr, hc]; simp [c2_11]

/-! ## 3. Exact, fixed delays, ANY index-bit traces -/

def C (d : Int) : Rd := Rd.const d

/-- A bad decode instant `u`: ctl_req reads 1 and the per-bit code reading
disagrees with the token about `k`. -/
def Bad (k v : Nat) (dc d0 d1 : Int) (c s0 s1 : Int → Bool) (u : Int) : Prop :=
  c (u - dc) = true ∧ (code (s0 (u - d0)) (s1 (u - d1)) == k) ≠ (v == k)

/-- The fixed-delay decode output. -/
def Dfix (k : Nat) (dc d0 d1 : Int) (c s0 s1 : Int → Bool) (u : Int) : Bool :=
  dec k (s0 (u - d0)) (s1 (u - d1)) (c (u - dc))

theorem dfix_dec (k : Nat) (dc d0 d1 : Int) (c s0 s1 : Int → Bool) :
    DecEq k (C d0) (C d1) (C dc) s0 s1 c (Dfix k dc d0 d1 c s0 s1) := fun _ => rfl

def jfN (dr dd : Int) (r D : Int → Bool) (t : Int) (q : Bool) : Bool := c2 (r (t - dr)) (D (t - dd)) q

/-- Every fixed-delay environment has a join trace (H_PIN_READ, H_RESET). -/
theorem run_jeq (dr dd : Int) (dq : Nat) (hdq : 0 < dq) (r D : Int → Bool) :
    JEq (C dr) (C dd) (C dq) r D (run (jfN dr dd r D) dq hdq) :=
  fun t ht => run_eq _ dq hdq t ht

theorem exists_min (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ n, ∀ m, m ≤ n → ¬ P m := by
    intro n
    induction n with
    | zero => intro m hm hp; exact hno ⟨m, hp, fun m' hm' => by omega⟩
    | succ n ih =>
      intro m hm hp
      by_cases h' : m ≤ n
      · exact ih m h' hp
      · exact hno ⟨m, hp, fun m' hm' => ih m' (by omega)⟩
  obtain ⟨n, hn⟩ := h
  exact key n n (Nat.le_refl n) hn

section Fixed
set_option linter.unusedSectionVars false
variable (k v : Nat) (hk : k < 3) (dr dd dc d0 d1 : Int) (dq : Nat) (hdq : 0 < dq)
  (Cr Cf : Int) (hRst : 0 ≤ Cr + dc + dd) (s0 s1 : Int → Bool)
include hk hdq hRst

/-- **Necessity**: every bad decode instant has a request trace and a real join
trace on which NSpec fails. Unselected join: request waiting, the join rises.
Selected join (least bad instant `w`): request waiting and the join still 0
one loop back (it fails to rise), or the request falls exactly at `w` with the
join already 1 (it falls early). -/
theorem join_needed (u : Int) (hbad : Bad k v dc d0 d1 (pulse Cr Cf) s0 s1 u) :
    ∃ r j : Int → Bool, JEq (C dr) (C dd) (C dq) r (Dfix k dc d0 d1 (pulse Cr Cf) s0 s1) j ∧
      Rest j ∧ ¬ NSpec k v (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j := by
  have hc := hbad.1
  have hu : Cr ≤ u - dc ∧ u - dc < Cf := by simpa [pulse] using hc
  let D := Dfix k dc d0 d1 (pulse Cr Cf) s0 s1
  have hDlo : ∀ x, x < Cr + dc → D x = false := by
    intro x hx
    show dec k _ _ (pulse Cr Cf (x - dc)) = false
    rw [dec_eq k hk]; simp [pulse]; omega
  have mk : ∀ r : Int → Bool, (∀ j, JEq (C dr) (C dd) (C dq) r D j → Rest j →
      ¬ NSpec k v (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) →
      ∃ r j : Int → Bool, JEq (C dr) (C dd) (C dq) r D j ∧ Rest j ∧
        ¬ NSpec k v (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j :=
    fun r h => ⟨r, _, run_jeq dr dd dq hdq r D, run_rest _ dq hdq,
      h _ (run_jeq dr dd dq hdq r D) (run_rest _ dq hdq)⟩
  by_cases hvk : v = k
  · -- selected: least bad instant
    have hb2 : (code (s0 (u - d0)) (s1 (u - d1)) == k) = false := by
      have := hbad.2; subst hvk; simpa using this
    obtain ⟨m, hm, hmin⟩ := exists_min (fun n : Nat => Bad k v dc d0 d1 (pulse Cr Cf) s0 s1 (Cr + dc + n))
      ⟨(u - (Cr + dc)).toNat, by rw [show Cr + dc + ((u - (Cr + dc)).toNat : Int) = u by omega]; exact hbad⟩
    let w : Int := Cr + dc + m
    have hw : Cr ≤ w - dc ∧ w - dc < Cf := by simpa [pulse] using hm.1
    have hDw : D w = false := by
      show dec k _ _ (pulse Cr Cf (w - dc)) = false
      rw [dec_eq k hk, hm.1]
      have := hm.2; subst hvk; simpa using this
    have hDin : ∀ x, Cr + dc ≤ x → x < w → D x = true := by
      intro x h1 h2
      have hcx : pulse Cr Cf (x - dc) = true := by simp [pulse]; omega
      have hnb := hmin (x - (Cr + dc)).toNat (by omega)
      rw [show Cr + dc + ((x - (Cr + dc)).toNat : Int) = x by omega] at hnb
      show dec k _ _ (pulse Cr Cf (x - dc)) = true
      rw [dec_eq k hk, hcx]
      have : (code (s0 (x - d0)) (s1 (x - d1)) == k) = (v == k) :=
        Classical.byContradiction fun hne => hnb ⟨hcx, hne⟩
      rw [this]; subst hvk; simp
    have hspec_w : (pulse Cr Cf (w - dc) && (v == k)) = true := by
      rw [hm.1]; subst hvk; simp
    by_cases hsh : w - dq < Cr + dc
    · refine mk (fun _ => true) (fun j hJ hR hS => ?_)
      have hlow : ∀ t, t < Cr + dc + dd → j t = false := by
        apply int_ind (fun t => t < Cr + dc + dd → j t = false) (fun t ht _ => hR t ht)
        intro t ht ih hlt
        rw [hJ t ht]
        show c2 true (D (t - dd)) (j (t - (dq : Int))) = false
        rw [hDlo _ (by omega), ih _ (by omega) (by omega)]; exact c2_low _
      have e1 := hJ (w + dd) (by omega)
      have e2 := hS (w + dd) (by omega)
      have hq : j (w + dd - (dq : Int)) = false := hlow _ (by omega)
      change j (w + dd) = c2 true (D (w + dd - dd)) (j (w + dd - (dq : Int))) at e1
      change j (w + dd) = c2 true (pulse Cr Cf (w + dd - dd - dc) && (v == k)) (j (w + dd - (dq : Int))) at e2
      rw [show w + dd - dd = w by omega] at e1 e2
      rw [hDw, hq] at e1; rw [hspec_w, hq] at e2
      rw [e1] at e2; exact absurd e2 (by decide)
    · refine mk (fun x => decide (x < w + dd - dr)) (fun j hJ _ hS => ?_)
      have hhi : ∀ t, Cr + dc + dd ≤ t → t < w + dd → j t = true := by
        intro t h1 h2
        rw [hJ t (by omega)]
        show c2 (decide (t - dr < w + dd - dr)) (D (t - dd)) _ = true
        rw [hDin _ (by omega) (by omega), decide_eq_true (by omega)]; exact c2_11 _
      have e1 := hJ (w + dd) (by omega)
      have e2 := hS (w + dd) (by omega)
      have hq : j (w + dd - (dq : Int)) = true := hhi _ (by omega) (by omega)
      change j (w + dd) = c2 (decide (w + dd - dr < w + dd - dr)) (D (w + dd - dd))
        (j (w + dd - (dq : Int))) at e1
      change j (w + dd) = c2 (decide (w + dd - dr < w + dd - dr))
        (pulse Cr Cf (w + dd - dd - dc) && (v == k)) (j (w + dd - (dq : Int))) at e2
      rw [show w + dd - dd = w by omega] at e1 e2
      rw [hDw, hq] at e1; rw [hspec_w, hq] at e2
      rw [e1] at e2; simp at e2; exact absurd e2 (by decide)
  · -- unselected: the join rises with the request waiting
    have hf : (v == k) = false := by simp [hvk]
    have hb2 : (code (s0 (u - d0)) (s1 (u - d1)) == k) = true := by
      have := hbad.2; rw [hf] at this; simpa using this
    refine mk (fun _ => true) (fun j hJ hR hS => ?_)
    have hz := unsel_low k v hvk _ _ _ _ (by simp [C, Rd.const]; omega) _ _ j hS hR
    have e1 := hJ (u + dd) (by omega)
    change j (u + dd) = c2 true (D (u + dd - dd)) (j (u + dd - (dq : Int))) at e1
    rw [show u + dd - dd = u by omega, hz, hz] at e1
    have hDu : D u = true := by
      show dec k _ _ (pulse Cr Cf (u - dc)) = true
      rw [dec_eq k hk, hc, hb2]; rfl
    rw [hDu] at e1; exact absurd e1 (by decide)

/-- **Exact, fixed per-pin delays, any index-bit traces.** The request pin
`dr`, the decode→join wire `dd` and the feedback `dq` do not appear on the
right. -/
theorem join_exact_fixed :
    (∀ r D j : Int → Bool, DecEq k (C d0) (C d1) (C dc) s0 s1 (pulse Cr Cf) D →
      JEq (C dr) (C dd) (C dq) r D j → Rest j → NSpec k v (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) ↔
    ∀ u, ¬ Bad k v dc d0 d1 (pulse Cr Cf) s0 s1 u := by
  constructor
  · intro h u hb
    obtain ⟨r, j, hJ, hR, hS⟩ := join_needed k v hk dr dd dc d0 d1 dq hdq Cr Cf hRst s0 s1 u hb
    exact hS (h r _ j (dfix_dec k dc d0 d1 _ s0 s1) hJ hR)
  · intro hno r D j hD hJ _
    apply join_ok_of_reads k v hk _ _ _ _ _ _ r _ s0 s1 D j hD hJ
    intro u hc
    exact Classical.byContradiction fun hne => hno u ⟨hc, hne⟩

end Fixed

/-! ## 4. Delay box (read maps), generic -/

def InBox (lo hi : Int) (p : Rd) : Prop := lo ≤ p.lo ∧ p.hi ≤ hi

theorem inbox_const {lo hi d : Int} (h1 : lo ≤ d) (h2 : d ≤ hi) : InBox lo hi (C d) := by
  simp [InBox, C, Rd.const]; omega

section Box
set_option linter.unusedSectionVars false
variable (k v : Nat) (hk : k < 3)
  (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf : Int)
  (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
  (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr < Cf) (hRst : 0 ≤ Cr + Clo + Dlo)

/-- NSpec for every read-map sextuple in the box (pins: request `R`, decode →
join `D`, ctl_req `C`, `s0` `A`, `s1` `B`, feedback `Q`), every request
trace and every trace obeying H_PIN_READ + H_RESET, for GIVEN bit traces. -/
def MapsOK (s0 s1 : Int → Bool) : Prop :=
  ∀ pr pd pc p0 p1 pq : Rd, InBox Rlo Rhi pr → InBox Dlo Dhi pd → InBox Clo Chi pc →
    InBox Alo Ahi p0 → InBox Blo Bhi p1 → InBox Qlo Qhi pq →
    ∀ r D j : Int → Bool, DecEq k p0 p1 pc s0 s1 (pulse Cr Cf) D → JEq pr pd pq r D j → Rest j →
      NSpec k v pr pd pc pq r (pulse Cr Cf) j

include hk in
/-- Sufficient, per instant: whenever ctl_req may read 1 at the decode, every
pair of bit readings allowed by the windows gives the right answer. -/
theorem maps_ok (s0 s1 : Int → Bool)
    (h : ∀ u, Cr + Clo ≤ u → u < Cf + Chi → ∀ x0 x1 : Int, u - Ahi ≤ x0 → x0 ≤ u - Alo →
      u - Bhi ≤ x1 → x1 ≤ u - Blo → (code (s0 x0) (s1 x1) == k) = (v == k)) :
    MapsOK k v Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf s0 s1 := by
  intro pr pd pc p0 p1 pq _ _ hc ha hb _ r D j hD hJ _
  apply join_ok_of_reads k v hk _ _ _ _ _ _ r _ s0 s1 D j hD hJ
  intro u hcu
  have hp : Cr ≤ pc.σ u ∧ pc.σ u < Cf := by simpa [pulse] using hcu
  have := pc.ge u; have := pc.le u; have := p0.ge u; have := p0.le u
  have := p1.ge u; have := p1.le u
  have := hc.1; have := hc.2; have := ha.1; have := ha.2; have := hb.1; have := hb.2
  exact h u (by omega) (by omega) _ _ (by omega) (by omega) (by omega) (by omega)

include hk hRb hDb hQ1 hQb hRst in
/-- Necessary: a bad instant under constant delays inside the box refutes MapsOK. -/
theorem maps_needed (s0 s1 : Int → Bool) (dc d0 d1 u : Int)
    (h1 : Clo ≤ dc) (h2 : dc ≤ Chi) (h3 : Alo ≤ d0) (h4 : d0 ≤ Ahi) (h5 : Blo ≤ d1) (h6 : d1 ≤ Bhi)
    (hbad : Bad k v dc d0 d1 (pulse Cr Cf) s0 s1 u) :
    ¬ MapsOK k v Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf s0 s1 := by
  intro hM
  have hq0 : 0 < Qlo.toNat := by omega
  obtain ⟨r, j, hJ, hR, hS⟩ :=
    join_needed k v hk Rlo Dlo dc d0 d1 Qlo.toNat hq0 Cr Cf (by omega) s0 s1 u hbad
  exact hS (hM _ _ _ _ _ _ (inbox_const (Int.le_refl _) hRb) (inbox_const (Int.le_refl _) hDb)
    (inbox_const h1 h2) (inbox_const h3 h4) (inbox_const h5 h6) (inbox_const (by omega) (by omega))
    r _ j (dfix_dec k dc d0 d1 _ s0 s1) hJ hR)

end Box

/-- A ctl_req read map can put `u`'s reading inside the pulse iff `u` is in the
pulse widened by the window. -/
theorem pick_c {Clo Chi Cr Cf u : Int} (h1 : Cr + Clo ≤ u) (h2 : u < Cf + Chi) (h3 : Clo ≤ Chi)
    (hCF : Cr < Cf) :
    ∃ dc, Clo ≤ dc ∧ dc ≤ Chi ∧ Cr ≤ u - dc ∧ u - dc < Cf := by
  by_cases h : u - Clo < Cf
  · exact ⟨Clo, Int.le_refl _, h3, by omega, h⟩
  · exact ⟨u - Cf + 1, by omega, by omega, by omega, by omega⟩

/-- A bit whose window does not contain `u` widened can be read outside it. -/
theorem pick_d {lo hi S0 S1 u : Int} (hb : lo ≤ hi) (h : ¬ (S0 + hi ≤ u ∧ u < S1 + lo)) :
    ∃ d, lo ≤ d ∧ d ≤ hi ∧ ¬ (S0 ≤ u - d ∧ u - d < S1) := by
  by_cases h' : S0 + hi ≤ u
  · exact ⟨lo, Int.le_refl _, hb, by omega⟩
  · exact ⟨hi, hb, Int.le_refl _, by omega⟩

/-! ## 5. M1: each bit stable on its own window, arbitrary outside -/

/-- A bit trace: `a` on `[S0, S1)`, `b` outside. -/
def sW (a b : Bool) (S0 S1 : Int) (x : Int) : Bool := if S0 ≤ x ∧ x < S1 then a else b

theorem sW_stable (a b : Bool) (S0 S1 : Int) : Stable (sW a b S0 S1) a S0 S1 := by
  intro t h1 h2; simp [sW, h1, h2]
theorem sW_out {a b : Bool} {S0 S1 x : Int} (h : ¬ (S0 ≤ x ∧ x < S1)) : sW a b S0 S1 x = b := by
  unfold sW; split
  · exact absurd ‹_› h
  · rfl
theorem sW_same (a : Bool) (S0 S1 x : Int) : sW a a S0 S1 x = a := by simp [sW]

section M1
set_option linter.unusedSectionVars false
variable (k v : Nat) (hk : k < 3) (hv : v < 3)
  (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf : Int)
  (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
  (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr < Cf) (hRst : 0 ≤ Cr + Clo + Dlo)
  (A0 A1 B0 B1 : Int)

/-- M1 box statement: every pair of bit traces with bit `i` = `bit_i v` on
its window (**H_S_STABLE_BIT**; `A0,A1` for `s0`, `B0,B1` for `s1`). -/
def BoxOK1 : Prop :=
  ∀ s0 s1 : Int → Bool, Stable s0 (bit0 v) A0 A1 → Stable s1 (bit1 v) B0 B1 →
    MapsOK k v Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf s0 s1

/-- The selected join's condition: setup and hold per bit, decode pins only. -/
def SelCond : Prop :=
  A0 + Ahi ≤ Cr + Clo ∧ Cf + Chi ≤ A1 + Alo ∧ B0 + Bhi ≤ Cr + Clo ∧ Cf + Chi ≤ B1 + Blo

/-- The unselected join's condition: every instant at which ctl_req may read 1
is inside the read-stable window of a bit in which `k` and `v` differ. -/
def Cover : Prop :=
  ∀ u, Cr + Clo ≤ u → u < Cf + Chi →
    (bit0 k ≠ bit0 v ∧ A0 + Ahi ≤ u ∧ u < A1 + Alo) ∨ (bit1 k ≠ bit1 v ∧ B0 + Bhi ≤ u ∧ u < B1 + Blo)

include hk hRb hDb hCb hAb hBb hQ1 hQb hCF hRst in
/-- **Selected join, exact over the box (M1).** -/
theorem sel_box_exact :
    BoxOK1 k k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf A0 A1 B0 B1 ↔
    SelCond Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 := by
  have hk4 : k < 4 := by omega
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    -- a bad instant `u` and the bit that is not read-stable there
    have hex : ∃ u, Cr + Clo ≤ u ∧ u < Cf + Chi ∧
        (¬ (A0 + Ahi ≤ u ∧ u < A1 + Alo) ∨ ¬ (B0 + Bhi ≤ u ∧ u < B1 + Blo)) := by
      unfold SelCond at hn
      by_cases hs : A0 + Ahi ≤ Cr + Clo ∧ B0 + Bhi ≤ Cr + Clo
      · exact ⟨Cf + Chi - 1, by omega, by omega, by omega⟩
      · exact ⟨Cr + Clo, by omega, by omega, by omega⟩
    obtain ⟨u, hu1, hu2, hbit⟩ := hex
    obtain ⟨dc, c1, c2', c3, c4⟩ := pick_c hu1 hu2 hCb hCF
    let s0 := sW (bit0 k) (!bit0 k) A0 A1
    let s1 := sW (bit1 k) (!bit1 k) B0 B1
    have key : ∃ d0 d1, Alo ≤ d0 ∧ d0 ≤ Ahi ∧ Blo ≤ d1 ∧ d1 ≤ Bhi ∧
        (s0 (u - d0) ≠ bit0 k ∨ s1 (u - d1) ≠ bit1 k) := by
      rcases hbit with hb | hb
      · obtain ⟨d0, e1, e2, e3⟩ := pick_d hAb hb
        refine ⟨d0, Blo, e1, e2, Int.le_refl _, hBb, Or.inl ?_⟩
        show sW _ _ A0 A1 (u - d0) ≠ _; rw [sW_out e3]; cases bit0 k <;> decide
      · obtain ⟨d1, e1, e2, e3⟩ := pick_d hBb hb
        refine ⟨Alo, d1, Int.le_refl _, hAb, e1, e2, Or.inr ?_⟩
        show sW _ _ B0 B1 (u - d1) ≠ _; rw [sW_out e3]; cases bit1 k <;> decide
    obtain ⟨d0, d1, e1, e2, e3, e4, hne⟩ := key
    apply maps_needed k k hk Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf hRb hDb hQ1 hQb hRst
      s0 s1 dc d0 d1 u c1 c2' e1 e2 e3 e4 _ (h s0 s1 (sW_stable _ _ _ _) (sW_stable _ _ _ _))
    refine ⟨by simp [pulse]; omega, ?_⟩
    have : code (s0 (u - d0)) (s1 (u - d1)) ≠ k := by
      rw [Ne, code_eq_iff _ _ k hk4]; intro ⟨a, b⟩; rcases hne with h' | h' <;> contradiction
    simpa using this
  · intro hc s0 s1 hs0 hs1
    apply maps_ok k k hk Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf s0 s1
    intro u h1 h2 x0 x1 a1 a2 b1 b2
    unfold SelCond at hc
    rw [hs0 x0 (by omega) (by omega), hs1 x1 (by omega) (by omega), code_bits k hk4]

include hk hv hRb hDb hCb hAb hBb hQ1 hQb hCF hRst in
/-- **Unselected join, exact over the box (M1).** -/
theorem unsel_box_exact (hvk : v ≠ k) :
    BoxOK1 k v Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf A0 A1 B0 B1 ↔
    Cover k v Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 := by
  have hk4 : k < 4 := by omega
  have hv4 : v < 4 := by omega
  have hf : (v == k) = false := by simp [hvk]
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    unfold Cover at hn
    rw [Classical.not_forall] at hn
    obtain ⟨u, hu⟩ := hn
    have hu1 : Cr + Clo ≤ u := Classical.byContradiction fun h' => hu (fun h'' => absurd h'' h')
    have hu2 : u < Cf + Chi := Classical.byContradiction fun h' => hu (fun _ h'' => absurd h'' h')
    have hnc : ¬ ((bit0 k ≠ bit0 v ∧ A0 + Ahi ≤ u ∧ u < A1 + Alo) ∨
        (bit1 k ≠ bit1 v ∧ B0 + Bhi ≤ u ∧ u < B1 + Blo)) := fun h' => hu (fun _ _ => h')
    obtain ⟨dc, c1, c2', c3, c4⟩ := pick_c hu1 hu2 hCb hCF
    let s0 := sW (bit0 v) (bit0 k) A0 A1
    let s1 := sW (bit1 v) (bit1 k) B0 B1
    have r0 : ∃ d0, Alo ≤ d0 ∧ d0 ≤ Ahi ∧ s0 (u - d0) = bit0 k := by
      by_cases he : bit0 k = bit0 v
      · exact ⟨Alo, Int.le_refl _, hAb, by show sW _ _ _ _ _ = _; rw [he, sW_same]⟩
      · obtain ⟨d0, e1, e2, e3⟩ := pick_d hAb (fun hw => hnc (Or.inl ⟨he, hw⟩))
        exact ⟨d0, e1, e2, sW_out e3⟩
    have r1 : ∃ d1, Blo ≤ d1 ∧ d1 ≤ Bhi ∧ s1 (u - d1) = bit1 k := by
      by_cases he : bit1 k = bit1 v
      · exact ⟨Blo, Int.le_refl _, hBb, by show sW _ _ _ _ _ = _; rw [he, sW_same]⟩
      · obtain ⟨d1, e1, e2, e3⟩ := pick_d hBb (fun hw => hnc (Or.inr ⟨he, hw⟩))
        exact ⟨d1, e1, e2, sW_out e3⟩
    obtain ⟨d0, e1, e2, e3⟩ := r0
    obtain ⟨d1, e4, e5, e6⟩ := r1
    apply maps_needed k v hk Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf hRb hDb hQ1 hQb hRst
      s0 s1 dc d0 d1 u c1 c2' e1 e2 e4 e5 _ (h s0 s1 (sW_stable _ _ _ _) (sW_stable _ _ _ _))
    refine ⟨by simp [pulse]; omega, ?_⟩
    rw [e3, e6, code_bits k hk4, hf]; simp
  · intro hc s0 s1 hs0 hs1
    apply maps_ok k v hk Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf s0 s1
    intro u h1 h2 x0 x1 a1 a2 b1 b2
    rw [hf]
    have hne : code (s0 x0) (s1 x1) ≠ k := by
      rw [Ne, code_eq_iff _ _ k hk4]
      rintro ⟨e0, e1⟩
      rcases hc u h1 h2 with ⟨hd, w1, w2⟩ | ⟨hd, w1, w2⟩
      · exact hd (by rw [← e0, hs0 x0 (by omega) (by omega)])
      · exact hd (by rw [← e1, hs1 x1 (by omega) (by omega)])
    simpa using hne

end M1

/-- Each decode's per-bit setup/hold implies every unselected join's Cover. -/
theorem sel_cond_cover (k v : Nat) (hk : k < 3) (hv : v < 3) (hvk : v ≠ k)
    (Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 : Int)
    (h : SelCond Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1) :
    Cover k v Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 := by
  intro u h1 h2
  unfold SelCond at h
  have hd : bit0 k ≠ bit0 v ∨ bit1 k ≠ bit1 v := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals obtain rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    all_goals first | exact absurd rfl hvk | decide
  rcases hd with hd | hd
  · exact Or.inl ⟨hd, by omega, by omega⟩
  · exact Or.inr ⟨hd, by omega, by omega⟩

/-- **Per decode, over all token values (M1, box):** join `k` is correct for
EVERY token value `v < 3` iff decode `k`'s two index pins meet the per-bit
setup and hold. -/
theorem decode_exact_all_tokens (k : Nat) (hk : k < 3)
    (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf : Int)
    (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
    (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr < Cf) (hRst : 0 ≤ Cr + Clo + Dlo) (A0 A1 B0 B1 : Int) :
    (∀ v, v < 3 → BoxOK1 k v Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf A0 A1 B0 B1) ↔
    SelCond Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 := by
  constructor
  · intro h
    exact (sel_box_exact k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRb hDb hCb hAb hBb hQ1 hQb hCF hRst
      A0 A1 B0 B1).mp (h k hk)
  · intro hc v hv
    by_cases hvk : v = k
    · subst hvk
      exact (sel_box_exact v hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRb hDb hCb hAb hBb hQ1 hQb hCF hRst
        A0 A1 B0 B1).mpr hc
    · exact (unsel_box_exact k v hk hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRb hDb hCb hAb hBb hQ1 hQb hCF hRst
        A0 A1 B0 B1 hvk).mpr (sel_cond_cover k v hk hv hvk _ _ _ _ _ _ _ _ _ _ _ _ hc)

/-- Two windows covering an interval, closed form (the `{k,v} = {1,2}` Cover). -/
theorem cover2_iff (L H a0 b0 a1 b1 : Int) (hLH : L < H) :
    (∀ u, L ≤ u → u < H → (a0 ≤ u ∧ u < b0) ∨ (a1 ≤ u ∧ u < b1)) ↔
    ((a0 ≤ L ∧ H ≤ b0) ∨ (a1 ≤ L ∧ H ≤ b1) ∨ (a0 ≤ L ∧ a1 ≤ b0 ∧ H ≤ b1) ∨
     (a1 ≤ L ∧ a0 ≤ b1 ∧ H ≤ b0)) := by
  constructor
  · intro h
    have h1 := h L; have h2 := h b0; have h3 := h b1
    omega
  · intro h u h1 h2; omega

/-- For `k = 2`, `v = 1` (and symmetrically), both bits differ: Cover is the
two-window cover. -/
theorem cover_12 (Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 : Int) :
    Cover 2 1 Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 ↔
    (∀ u, Cr + Clo ≤ u → u < Cf + Chi → (A0 + Ahi ≤ u ∧ u < A1 + Alo) ∨ (B0 + Bhi ≤ u ∧ u < B1 + Blo)) := by
  have e0 : bit0 2 ≠ bit0 1 := by decide
  have e1 : bit1 2 ≠ bit1 1 := by decide
  unfold Cover
  constructor
  · intro h u h1 h2
    rcases h u h1 h2 with ⟨_, a, b⟩ | ⟨_, a, b⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨a, b⟩
  · intro h u h1 h2
    rcases h u h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨e0, a, b⟩
    · exact Or.inr ⟨e1, a, b⟩

/-- A one-bit difference (`k = 0`, `v = 1`): Cover is `bd_mux`'s single-bit form. -/
theorem cover_01 (Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 : Int) (hLH : Cr + Clo < Cf + Chi) :
    Cover 0 1 Clo Chi Alo Ahi Blo Bhi Cr Cf A0 A1 B0 B1 ↔
    (A0 + Ahi ≤ Cr + Clo ∧ Cf + Chi ≤ A1 + Alo) := by
  have e0 : bit0 0 ≠ bit0 1 := by decide
  have e1 : ¬ (bit1 0 ≠ bit1 1) := by decide
  unfold Cover
  constructor
  · intro h
    have h1 := h (Cr + Clo) (Int.le_refl _) hLH
    have h2 := h (Cf + Chi - 1) (by omega) (by omega)
    rcases h1 with ⟨_, a, _⟩ | ⟨x, _⟩
    · rcases h2 with ⟨_, _, b⟩ | ⟨y, _⟩
      · omega
      · exact absurd y e1
    · exact absurd x e1
  · intro h u h1 h2; exact Or.inl ⟨e0, by omega, by omega⟩

/-! ## 6. M2: clean per-bit steps, and the THIRD branch -/

/-- Bit `i` changes once, cleanly, at `T`, from `a` to `b` (**H_S_STEP**). -/
def step (a b : Bool) (T : Int) (x : Int) : Bool := if x < T then a else b

/-- Index `1 -> 2`: `s0` falls at `T0`, `s1` rises at `T1`. Code `00` (join 0)
is read iff `s0` reads changed and `s1` reads unchanged. -/
theorem code12_zero (T0 T1 x y : Int) :
    (code (step true false T0 x) (step false true T1 y) == 0) = decide (T0 ≤ x ∧ y < T1) := by
  unfold step
  by_cases h0 : x < T0 <;> by_cases h1 : y < T1 <;> simp [h0, h1, code] <;> omega

/-- Index `2 -> 1`: `s0` rises at `T0`, `s1` falls at `T1`. -/
theorem code21_zero (T0 T1 x y : Int) :
    (code (step false true T0 x) (step true false T1 y) == 0) = decide (x < T0 ∧ T1 ≤ y) := by
  unfold step
  by_cases h0 : x < T0 <;> by_cases h1 : y < T1 <;> simp [h0, h1, code] <;> omega

section Third
set_option linter.unusedSectionVars false
variable (v : Nat) (hv0 : v ≠ 0) (hv : v < 3)
  (dr dd dc d0 d1 : Int) (dq : Nat) (hdq : 0 < dq) (Cr Cf : Int) (hCF : Cr < Cf)
  (hRst : 0 ≤ Cr + dc + dd) (T0 T1 : Int)

include hv0 hv hdq hCF hRst in
/-- **Third branch, fixed delays (1 → 2).** With the index changing `1 -> 2`
(token `v ∈ {1, 2}`: `v = 2` is the setup side, `v = 1` the hold side), join 0
is correct for every request trace and every real trace iff H_NO_THIRD:
the falling bit `s0` (read `T0 + d0`) is read changed only after ctl_req's
read window, or the rising bit `s1` (read `T1 + d1`) is read changed before
ctl_req reads 1, or before `s0` is. -/
theorem third_fixed_exact :
    (∀ r D j : Int → Bool, DecEq 0 (C d0) (C d1) (C dc) (step true false T0) (step false true T1)
        (pulse Cr Cf) D → JEq (C dr) (C dd) (C dq) r D j → Rest j →
        NSpec 0 v (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) ↔
    (Cf + dc ≤ T0 + d0 ∨ T1 + d1 ≤ Cr + dc ∨ T1 + d1 ≤ T0 + d0) := by
  rw [join_exact_fixed 0 v (by decide) dr dd dc d0 d1 dq hdq Cr Cf hRst]
  have hf : (v == 0) = false := by simp [hv0]
  unfold Bad
  simp only [code12_zero, hf, pulse]
  constructor
  · intro h
    have h1 := h (Cr + dc); have h2 := h (T0 + d0)
    simp at h1 h2
    omega
  · intro h u; simp; omega

include hv0 hv hdq hCF hRst in
/-- The mirror (index `2 -> 1`): `s0` rises, `s1` falls. -/
theorem third_fixed_exact_21 :
    (∀ r D j : Int → Bool, DecEq 0 (C d0) (C d1) (C dc) (step false true T0) (step true false T1)
        (pulse Cr Cf) D → JEq (C dr) (C dd) (C dq) r D j → Rest j →
        NSpec 0 v (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) ↔
    (Cf + dc ≤ T1 + d1 ∨ T0 + d0 ≤ Cr + dc ∨ T0 + d0 ≤ T1 + d1) := by
  rw [join_exact_fixed 0 v (by decide) dr dd dc d0 d1 dq hdq Cr Cf hRst]
  have hf : (v == 0) = false := by simp [hv0]
  unfold Bad
  simp only [code21_zero, hf, pulse]
  constructor
  · intro h
    have h1 := h (Cr + dc); have h2 := h (T1 + d1)
    simp at h1 h2
    omega
  · intro h u; simp; omega

end Third

section ThirdBox
set_option linter.unusedSectionVars false
variable (v : Nat) (hv0 : v ≠ 0) (hv : v < 3)
  (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf : Int)
  (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
  (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr < Cf) (hRst : 0 ≤ Cr + Clo + Dlo) (T0 T1 : Int)

include hv0 hv hRb hDb hCb hAb hBb hQ1 hQb hCF hRst in
/-- **Third branch, exact over the box (1 → 2): H_NO_THIRD.** The falling
bit enters with its EARLIEST read (`Alo`), the rising bit with its LATEST
(`Bhi`), ctl_req with both ends of its window. -/
theorem third_box_exact :
    MapsOK 0 v Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf
      (step true false T0) (step false true T1) ↔
    (Cf + Chi ≤ T0 + Alo ∨ T1 + Bhi ≤ Cr + Clo ∨ T1 + Bhi ≤ T0 + Alo) := by
  have hf : (v == 0) = false := by simp [hv0]
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    let u : Int := if Cr + Clo ≤ T0 + Alo then T0 + Alo else Cr + Clo
    have hu1 : Cr + Clo ≤ u := by simp only [u]; split <;> omega
    have hu2 : u < Cf + Chi := by simp only [u]; split <;> omega
    obtain ⟨dc, c1, c2', c3, c4⟩ := pick_c hu1 hu2 hCb hCF
    apply maps_needed 0 v (by decide) Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf
      hRb hDb hQ1 hQb hRst _ _ dc Alo Bhi u c1 c2' (Int.le_refl _) hAb hBb (Int.le_refl _) _ h
    refine ⟨by simp [pulse]; omega, ?_⟩
    rw [code12_zero, hf]
    have : T0 ≤ u - Alo ∧ u - Bhi < T1 := by simp only [u]; split <;> omega
    simp [this]
  · intro hc
    apply maps_ok 0 v (by decide) Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf
    intro u h1 h2 x0 x1 a1 a2 b1 b2
    rw [code12_zero, hf]
    simp; omega

end ThirdBox

/-! ## 7. M2, the selected join, and why the third branch is never alone -/

/-! ## 7. M2: the selected join, the old branch, and why the third branch is never alone -/

theorem code12_two (T0 T1 x y : Int) :
    (code (step true false T0 x) (step false true T1 y) == 2) = decide (T0 ≤ x ∧ T1 ≤ y) := by
  unfold step
  by_cases h0 : x < T0 <;> by_cases h1 : y < T1 <;> simp [h0, h1, code] <;> omega

theorem code12_one (T0 T1 x y : Int) :
    (code (step true false T0 x) (step false true T1 y) == 1) = decide (x < T0 ∧ y < T1) := by
  unfold step
  by_cases h0 : x < T0 <;> by_cases h1 : y < T1 <;> simp [h0, h1, code] <;> omega

section Step
set_option linter.unusedSectionVars false
variable (dr dd dc d0 d1 : Int) (dq : Nat) (hdq : 0 < dq) (Cr Cf : Int) (hCF : Cr < Cf)
  (hRst : 0 ≤ Cr + dc + dd) (T0 T1 : Int)
include hdq hCF hRst

/-- The selected join after a clean `1 -> 2` change (token `v = 2`), fixed
delays: exact iff BOTH changed bits are read changed by the time ctl_req
reads 1 (no hold side: the step trace stays at 2). -/
theorem step_sel_exact :
    (∀ r D j : Int → Bool, DecEq 2 (C d0) (C d1) (C dc) (step true false T0) (step false true T1)
        (pulse Cr Cf) D → JEq (C dr) (C dd) (C dq) r D j → Rest j →
        NSpec 2 2 (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) ↔
    (T0 + d0 ≤ Cr + dc ∧ T1 + d1 ≤ Cr + dc) := by
  rw [join_exact_fixed 2 2 (by decide) dr dd dc d0 d1 dq hdq Cr Cf hRst]
  unfold Bad
  simp only [code12_two, pulse]
  constructor
  · intro h
    have h1 := h (Cr + dc)
    simp at h1
    omega
  · intro h u; simp; omega

/-- The OLD branch (join 1, token `v = 2` after `1 -> 2`): excluded as soon as
ONE changed bit is read changed when ctl_req reads 1. -/
theorem step_old_exact :
    (∀ r D j : Int → Bool, DecEq 1 (C d0) (C d1) (C dc) (step true false T0) (step false true T1)
        (pulse Cr Cf) D → JEq (C dr) (C dd) (C dq) r D j → Rest j →
        NSpec 1 2 (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) ↔
    (T0 + d0 ≤ Cr + dc ∨ T1 + d1 ≤ Cr + dc) := by
  rw [join_exact_fixed 1 2 (by decide) dr dd dc d0 d1 dq hdq Cr Cf hRst]
  unfold Bad
  simp only [code12_one, pulse]
  constructor
  · intro h
    have h1 := h (Cr + dc)
    simp at h1
    omega
  · intro h u; simp; omega

/-- **The third branch is never the only failure**: whenever the selected
join 2 is correct (every request trace, every real trace), join 0 is too. -/
theorem third_implied_by_setup
    (hsel : ∀ r D j : Int → Bool, DecEq 2 (C d0) (C d1) (C dc) (step true false T0) (step false true T1)
        (pulse Cr Cf) D → JEq (C dr) (C dd) (C dq) r D j → Rest j →
        NSpec 2 2 (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j) :
    ∀ r D j : Int → Bool, DecEq 0 (C d0) (C d1) (C dc) (step true false T0) (step false true T1)
        (pulse Cr Cf) D → JEq (C dr) (C dd) (C dq) r D j → Rest j →
        NSpec 0 2 (C dr) (C dd) (C dc) (C dq) r (pulse Cr Cf) j := by
  have h := (step_sel_exact dr dd dc d0 d1 dq hdq Cr Cf hCF hRst T0 T1).mp hsel
  exact (third_fixed_exact 2 (by decide) (by decide) dr dd dc d0 d1 dq hdq Cr Cf hCF hRst T0 T1).mpr
    (Or.inr (Or.inl h.2))

end Step

/-- Rise-first (`s1` read changed late but BEFORE `s0`: the transition is read
through `11`, which selects nothing): join 0 is correct, the selected join 2
is not (it fires late: a deviation from NSpec, not a wrong-branch token).
ctl_req `[1000, 3000)` via 300 at the decode; `s0` falls at 800 via 800
(read 1600), `s1` rises at 800 via 700 (read 1500). -/
theorem rise_first_example :
    (∀ r D j : Int → Bool, DecEq 0 (C 800) (C 700) (C 300) (step true false 800) (step false true 800)
        (pulse 1000 3000) D → JEq (C 0) (C 100) (C (50 : Nat)) r D j → Rest j →
        NSpec 0 2 (C 0) (C 100) (C 300) (C (50 : Nat)) r (pulse 1000 3000) j) ∧
    ¬ (∀ r D j : Int → Bool, DecEq 2 (C 800) (C 700) (C 300) (step true false 800) (step false true 800)
        (pulse 1000 3000) D → JEq (C 0) (C 100) (C (50 : Nat)) r D j → Rest j →
        NSpec 2 2 (C 0) (C 100) (C 300) (C (50 : Nat)) r (pulse 1000 3000) j) := by
  refine ⟨(third_fixed_exact 2 (by decide) (by decide) 0 100 300 800 700 50 (by decide) 1000 3000
    (by decide) (by decide) 800 800).mpr (by decide), fun h => ?_⟩
  have := (step_sel_exact 0 100 300 800 700 50 (by decide) 1000 3000 (by decide) (by decide) 800 800).mp h
  omega

/-! ## 8. Counter-trace and non-vacuity -/

/-- With the request held high, a decode read high for one loop latches the join. -/
theorem latch (dr dd : Int) (dq : Nat) (hdq : 0 < dq) (D j : Int → Bool) (T : Int) (hT : 0 ≤ T)
    (hJ : JEq (C dr) (C dd) (C dq) (fun _ => true) D j)
    (hd : ∀ t, T ≤ t → t < T + dq → D (t - dd) = true) : ∀ t, T ≤ t → j t = true := by
  apply int_ind (fun t => T ≤ t → j t = true) (fun t ht _ => by omega)
  intro t ht ih hTt
  rw [hJ t ht]
  show c2 true (D (t - dd)) (j (t - (dq : Int))) = true
  by_cases h : t < T + dq
  · rw [hd t hTt h]; exact c2_11 _
  · rw [ih _ (by omega) (by omega)]; exact c2_1x1 _

/-- **Wrong-branch token through the THIRD branch.** The index changes
`1 -> 2` for a control token meant for input 2. ctl_req `[1000, 3000)` read at
the decode through 300 ps (1 from 1300); `s0` falls at 800, read through
100 ps (changed from 900); `s1` rises at 800, read through 700 ps (changed
from 1500); decode→join 100 ps; in0_req WAITING; loop 50 ps. The decode of
input 0 reads `00` on `[1300, 1500)`, and join 0 latches 1 from 1400 for
EVERY trace obeying H_PIN_READ: input 0's token is consumed by a control
token for input 2. H_NO_THIRD fails (`3300 > 900`, `1500 > 1300`, `1500 > 900`). -/
theorem third_branch_latched (D j : Int → Bool)
    (hD : DecEq 0 (C 100) (C 700) (C 300) (step true false 800) (step false true 800) (pulse 1000 3000) D)
    (hJ : JEq (C 0) (C 100) (C (50 : Nat)) (fun _ => true) D j) :
    ∀ t, 1400 ≤ t → j t = true := by
  apply latch 0 100 50 (by decide) D j 1400 (by decide) hJ
  intro t h1 h2
  rw [hD, dec_eq 0 (by decide)]
  show (pulse 1000 3000 (t - 100 - 300) &&
    (code (step true false 800 (t - 100 - 100)) (step false true 800 (t - 100 - 700)) == 0)) = true
  rw [code12_zero]
  simp [pulse]; omega

/-- Good timing for the same change (`s1` read changed from 1000, before
ctl_req reads 1 at 1300): H_NO_THIRD holds. Both requests waiting. -/
def wD (k : Nat) : Int → Bool := Dfix k 300 100 200 (pulse 1000 3000) (step true false 800) (step false true 800)
def wj (k : Nat) : Int → Bool := run (jfN 0 100 (fun _ => true) (wD k)) 50 (by decide)

/-- **Non-vacuity**: in the constructed runs (every hypothesis holds by
construction), join 0 is 0 at every instant and the selected join 2 fires
at 1400. -/
theorem witness_third : (∀ t, wj 0 t = false) ∧ wj 2 1400 = true := by
  have hJ0 := run_jeq 0 100 50 (by decide) (fun _ => true) (wD 0)
  have hJ2 := run_jeq 0 100 50 (by decide) (fun _ => true) (wD 2)
  have S0 := (third_fixed_exact 2 (by decide) (by decide) 0 100 300 100 200 50 (by decide) 1000 3000
    (by decide) (by decide) 800 800).mpr (by decide) _ _ _ (dfix_dec 0 300 100 200 _ _ _) hJ0
    (run_rest _ 50 (by decide))
  have S2 := (step_sel_exact 0 100 300 100 200 50 (by decide) 1000 3000 (by decide) (by decide) 800 800).mpr
    (by decide) _ _ _ (dfix_dec 2 300 100 200 _ _ _) hJ2 (run_rest _ 50 (by decide))
  refine ⟨unsel_low 0 2 (by decide) _ _ _ _ (by simp [C, Rd.const]) _ _ _ S0 (run_rest _ 50 (by decide)), ?_⟩
  exact sel_fires 2 _ _ _ _ _ _ _ S2 1400 (by decide) rfl (by decide)

/-- Non-vacuity of the M1 box theorems: the per-bit condition is satisfiable
with a nonempty box (numbers in ps). -/
theorem selcond_witness : SelCond 250 350 100 450 100 450 1000 3000 500 4000 500 4000 :=
  by unfold SelCond; decide

end Formal.Cells.LibGapMuxN
