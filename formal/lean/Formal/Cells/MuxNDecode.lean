import Formal.Timing.Island

/-!
# Formal.Cells.MuxNDecode — research's N-way mux decode race, as a sufficient condition (shard B, 2026-11-19)

**Problem, plainly.** bdc's N-way mux (`bdc_muxnN`, emit.py) decodes its index outside its joins: one LUT per input k,
`sel[k] = ctl_req & (s == k)`, read by the join `uj<k>`. If the index `s` is still moving when `ctl_req` rises at a
decode LUT, the LUT of a NOT-selected input can pulse high, and its join may fire for an input that was not chosen.
Research found such pulses on cmpchain routes (its muxsel note, 2026-11-19) and made its rule E check the pair
(ctl_req pin, index pin) at every decode LUT (`BD_SKEW_MUXN=1`): the index must be settled at the LUT before the
request reaches it. Formal's simx reproduced the pulses and their absence (FOR-RESEARCH B13). This file states, in
the Spec gate model (every pin reads its source at a read time whose distance is admissible in the band, glitches
included), the condition under which a non-selected decode LUT cannot pulse, for EVERY delay in the band.

**Proved.**
* `gate_window`: one LUT; pins `P` at listed values force its INIT to `v`; if each such pin's source holds its value
  on `[α j, β j]`, and `L j ≤ delay ≤ U j` bounds the pin's composite delay, the output is `v` at every `t ≥ S` with
  `α j + U j ≤ t ≤ β j + L j` for every `j ∈ P`. (The other pins may do anything, glitches included.)
* `gate_union`: two forcing windows `[A1, B1]`, `[A2, B2]` of the same output value that overlap (`A2 ≤ B1 + 1`) give
  the value on `[A1, B2]`: no pulse in between.
* `decode_no_pulse`: the decode instance. Window 1: the request pin's source is 0 on `[a0, tr]` (before ctl_req rises)
  and forces the LUT to 0. Window 2: the index pins' sources hold a value `≠ k` on `[ts, b]` (from the moment the
  index is settled) and force the LUT to 0. **Rule E's inequality** `ts + U_s ≤ tr + L_r` (latest index arrival at the
  LUT no later than the earliest request arrival, per pin) then gives `sel[k] = 0` on the whole `[a0 + U_r, b + L_s]`:
  the not-selected input's decode cannot pulse. The two forcing facts are Bool (`ForcesP`), decided per route from
  the decode LUT's INIT and nextpnr's pin permutation.

**Not shown.** That a real route meets the inequality (that is the rule's / the margin tool's job; no route row is
emitted here); the selected input's decode (it must rise once, which is a liveness / handshake fact, not this race);
what a pulse does to the join (it is enough here that none occurs); runt filtering (none is assumed: the statement
holds with transport delays, w = 0).
-/

namespace Formal.Cells.MuxNDecode
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.Island

/-- **One LUT held by a forcing set of pins.** -/
theorem gate_window {p : DelayPar} {c : ℚ} {x : Beh} (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc)
    (S : Nat) (P : List Nat) (pv : Nat → Bool) (v : Bool) (α β L U : Nat → Nat)
    (hg : CGateOK p c g src arcs S x)
    (hLU : ∀ j ∈ P, j < g.k ∧ ∀ D, SumAdm p c (arcs j) D → L j ≤ D ∧ D ≤ U j)
    (hF : ForcesP g.k g.init (P.map fun j => (j, pv j)) v = true)
    (hsrc : ∀ j ∈ P, ∀ t, α j ≤ t → t ≤ β j → x (src j) t = pv j)
    (t : Nat) (hS : S ≤ t) (hw : ∀ j ∈ P, α j + U j ≤ t ∧ t ≤ β j + L j) :
    x g.out t = v := by
  obtain ⟨F, -, hFt⟩ := hg
  obtain ⟨hrd, ho⟩ := hFt t hS
  rw [ho]
  apply forcesP_sound hF
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨j, hj, rfl⟩ := he
  dsimp only
  obtain ⟨hjk, hb⟩ := hLU j hj
  refine ⟨hjk, ?_⟩
  obtain ⟨r1, r2⟩ := hrd j hjk
  obtain ⟨b1, b2⟩ := hb _ r2
  obtain ⟨w1, w2⟩ := hw j hj
  exact hsrc j hj _ (by omega) (by omega)

/-- **Two overlapping windows of one value: no pulse between them.** -/
theorem gate_union {x : Beh} (o : Nat) (v : Bool) (A1 B1 A2 B2 : Nat)
    (h1 : ∀ t, A1 ≤ t → t ≤ B1 → x o t = v) (h2 : ∀ t, A2 ≤ t → t ≤ B2 → x o t = v)
    (hov : A2 ≤ B1 + 1) : ∀ t, A1 ≤ t → t ≤ B2 → x o t = v := by
  intro t ht1 ht2
  by_cases h : t ≤ B1
  · exact h1 t ht1 h
  · exact h2 t (by omega) ht2

/-- **The N-way mux decode race: rule E at a decode LUT is sufficient.** `r` is the request pin; `P` the index pins
with the held index bits `sv` (a value other than this LUT's `k`); `hF0` / `hFs` are the LUT's two forcing facts. -/
theorem decode_no_pulse {p : DelayPar} {c : ℚ} {x : Beh} (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc)
    (S : Nat) (r : Nat) (P : List Nat) (sv : Nat → Bool) (L U : Nat → Nat)
    (a0 tr ts b : Nat)
    (hg : CGateOK p c g src arcs S x)
    (hLU : ∀ j ∈ r :: P, j < g.k ∧ ∀ D, SumAdm p c (arcs j) D → L j ≤ D ∧ D ≤ U j)
    (hF0 : ForcesP g.k g.init ([r].map fun j => (j, false)) false = true)
    (hFs : ForcesP g.k g.init (P.map fun j => (j, sv j)) false = true)
    (hreq : ∀ t, a0 ≤ t → t ≤ tr → x (src r) t = false)
    (hidx : ∀ j ∈ P, ∀ t, ts ≤ t → t ≤ b → x (src j) t = sv j)
    (hS : S ≤ a0 + U r)
    -- the index pins all settle by `ts`; the window over them starts at `Us` and ends at `Ls` (worst pin of each)
    (Us Ls : Nat) (hUs : ∀ j ∈ P, U j ≤ Us) (hLs : ∀ j ∈ P, Ls ≤ L j)
    -- **rule E**: the latest index arrival is no later than the earliest request arrival (+ 1 tick)
    (hE : ts + Us ≤ tr + L r + 1) :
    ∀ t, a0 + U r ≤ t → t ≤ b + Ls → x g.out t = false := by
  have hr : r < g.k := (hLU r (List.mem_cons_self ..)).1
  -- window 1: the request pin holds 0
  have w1 : ∀ t, a0 + U r ≤ t → t ≤ tr + L r → x g.out t = false := by
    intro t h1 h2
    refine gate_window g src arcs S [r] (fun _ => false) false (fun _ => a0) (fun _ => tr) L U hg
      (fun j hj => by simp at hj; rw [hj]; exact hLU r (List.mem_cons_self ..)) hF0
      (fun j hj t' h1' h2' => by simp at hj; rw [hj]; exact hreq t' h1' h2') t (by omega)
      (fun j hj => by simp at hj; rw [hj]; omega)
  -- window 2: the index pins hold a value other than k
  have w2 : ∀ t, ts + Us ≤ t → t ≤ b + Ls → S ≤ t → x g.out t = false := by
    intro t h1 h2 h3
    refine gate_window g src arcs S P sv false (fun _ => ts) (fun _ => b) L U hg
      (fun j hj => hLU j (List.mem_cons_of_mem _ hj)) hFs hidx t h3
      (fun j hj => ⟨by have := hUs j hj; omega, by have := hLs j hj; omega⟩)
  intro t h1 h2
  by_cases h : t ≤ tr + L r
  · exact w1 t h1 h
  · exact w2 t (by omega) h2 (by omega)

/-! ### The forcing facts on a decode LUT, decided

A 4-way mux's decode for input k = 1, unpermuted: pins (0: ctl_req, 1: s[0], 2: s[1]), `sel[1] = req & s0 & ~s1`,
INIT = 8 (only address 0b011). Each fact is checked by `decide` (kernel evaluation, no `native_decide`). A route's
LUT has nextpnr's pin permutation and its own INIT: the same check runs on those numbers. -/

/-- The request at 0 forces `sel[1]` to 0. -/
theorem sel1_req_low : ForcesP 3 8 ([0].map fun j => (j, false)) false = true := by decide

/-- Index 2 (s0 = 0, s1 = 1) forces `sel[1]` to 0. -/
theorem sel1_idx2 : ForcesP 3 8 ([1, 2].map fun j => (j, (if j = 2 then true else false))) false = true := by decide

/-- Negative control: index 1 does NOT force `sel[1]` to 0 (the selected input's decode follows the request). -/
theorem sel1_idx1_not : ForcesP 3 8 ([1, 2].map fun j => (j, (if j = 1 then true else false))) false = false := by decide


/-! ### The same theorem for a branch steer (bd_steer)

A steer's two outputs are `req & s` (taken) and `req & ~s` (not taken), LUT2s with INIT 8 and 2 (pin 0 = req, pin 1 = s).
`decode_no_pulse` applies with `P = [1]`: the not-taken output cannot pulse if the condition `s` has settled (at the
LUT pin) no later than the request arrives: research's rule E at a steer (FOR-RESEARCH B18 measured that race on ipow s7).
The forcing facts, decided: -/

theorem steer_true_req_low : ForcesP 2 8 ([0].map fun j => (j, false)) false = true := by decide
theorem steer_true_cond_low : ForcesP 2 8 ([1].map fun j => (j, false)) false = true := by decide
theorem steer_false_req_low : ForcesP 2 2 ([0].map fun j => (j, false)) false = true := by decide
theorem steer_false_cond_high : ForcesP 2 2 ([1].map fun j => (j, true)) false = true := by decide
/-- Negative control: the condition at the TAKEN value does not force the output. -/
theorem steer_true_cond_high_not : ForcesP 2 8 ([1].map fun j => (j, true)) false = false := by decide

end Formal.Cells.MuxNDecode
