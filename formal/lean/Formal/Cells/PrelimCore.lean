import Formal.Cells.Prelim
import Formal.Cells.CElemTiming
import Formal.Core.Substrate.Chan

/-!
# PrelimCore: every Prelim / CElemTiming notion B's cell files use, against Core

Shard B, PROGRAM.md Phase 1 ("port every Cells/ proof from Prelim to Core.
Delete Prelim"). Note: formal/notes/B-port-core2.md. This file is the
dictionary that makes the deletion of `Formal.Cells.Prelim` a renaming: for
each definition the Cells files use, it states the Core object it equals, or,
where Core has no exact counterpart, the precise one-way relation.

| B notion | Core counterpart | relation (theorem) |
|---|---|---|
| `K3`, `K3.f/t/x`, `K3.ofBool` | `Core.K3`, `zero/one/X`, `ofBool` | same constants (`rfl`) |
| `K3.join`, `K3.not`, `K3.mux` | `K3.merge`, `K3.not`, `kevalT`'s node | `= ` (`rfl` / `mux_eq`) |
| `K3.admits a b` | `a ⊑ ofBool b` | `↔` (`admits_iff_le`) |
| `lutIdx l` | `addr` | `=` on `List.ofFn` and on any list via `bvec` (`lutIdx_list`) |
| `lutB init l` | `Lut.eval` | `=` on any list, any `init` (`lutB_list`) |
| `muxTree g l` | `kevalT` | `=` (`muxTree_list`) |
| `lutK init l` | `Lut.keval`, `Lut.kevalSpec` | `=` on any list, any `init` (`lutK_list`, `lutK_list_spec`) |
| `o6B/o5B/o6K/o5K` | `Lut62.o6/o5` `.eval/.keval` | `=` for 6-pin lists (`o6B_eq` ...) |
| `completions l` | Core's `Consistent v` | `List.ofFn x ∈ completions (List.ofFn v) ↔ Consistent v x` (`ofFn_mem_completions_iff`) |
| `CElemTiming.Trace` | `Substrate.Sig` | same type (`rfl`) |
| `CElemTiming.WinDelay lo hi` | `Substrate.Win lo hi` | same relation (`winDelay_eq_win`, `rfl`) |
| `CElemTiming.Transport d` | `Substrate.Win d d` | `↔` (`transport_iff_win`); Core's `TraceDiscrete.Transport d d` is STRICTLY stronger (`transport_of_core`, `not_core_of_transport`) |
| `CElemTiming.exc init` | `Lut.eval` of the 6-input LUT | `=` (`exc_eq_eval`) |
| `CElemTiming.Loop` | two `Win` relations + `H_LOOP_POS` | `↔` (`loop_iff_win`) |
| `CElemTiming.Inertial d` | `TraceDiscrete.inertial (d-1)` one tick late | one-way + exact with a power-up hypothesis (`inertial_of_core`, `core_of_inertial`, `inertial_powerup_needed`) |

Plain-language statements.

* Assumed: nothing (no hypothesis of any theorem here is physical; every
  hypothesis is a side condition on lengths / delays, named where nontrivial).
* Proved: the equalities and equivalences of the table, for EVERY list (any
  length, any INIT number: INIT bits beyond `2^len` are ignored on both sides),
  every trace and every delay bound.
* Not exact (one-way): (1) B's fixed transport `Transport d` leaves the output
  free on `[0, d)`; Core's `TraceDiscrete.Transport d d` forces it to the
  input's initial value. Core ⊂ B (`transport_of_core`), not conversely
  (`not_core_of_transport`, a concrete trace). B's `Transport d` is exactly
  Core's `Win d d`. (2) B's `Inertial d` (output at `t + d` from the input on
  `[t, t + d)`) is Core's `inertial (d - 1)` delayed by one tick, for `d ≥ 1`,
  but B's output on `[0, d)` is free power-up state that the channel holds
  until the first stable window, whereas Core's starts at the input's initial
  value. Core's (shifted) trace is a B behaviour (`inertial_of_core`); a B
  behaviour equals it from `d - 1` on iff its power-up value at `d - 1` agrees
  (`core_of_inertial`, hypothesis **H_POWERUP**), and that hypothesis cannot
  be dropped (`inertial_powerup_needed`, a concrete trace).
* Not covered: physical pin order (Core.Bridge), timing numbers.
-/

namespace Formal.Cells.PrelimCore

open Formal.Core

/-! ## 1. Values -/

theorem k3_eq : Formal.Cells.K3 = Formal.Core.K3 := rfl
theorem f_eq : Formal.Cells.K3.f = Formal.Core.K3.zero := rfl
theorem t_eq : Formal.Cells.K3.t = Formal.Core.K3.one := rfl
theorem x_eq : Formal.Cells.K3.x = Formal.Core.K3.X := rfl
theorem ofBool_eq : Formal.Cells.K3.ofBool = Formal.Core.K3.ofBool := rfl
theorem join_eq : Formal.Cells.K3.join = Formal.Core.K3.merge := Formal.Cells.K3.join_eq_merge
theorem not_eq : Formal.Cells.K3.not = Formal.Core.K3.not := Formal.Cells.K3.not_eq_core

/-- B's Kleene 2:1 mux is the node of Core's mux tree `kevalT`. -/
theorem mux_eq (s a b : Formal.Core.K3) :
    Formal.Cells.K3.mux s a b = match s with
      | .zero => a
      | .one => b
      | .X => Formal.Core.K3.merge a b := Formal.Cells.mux_eq s a b

theorem admits_iff_le (a : Formal.Core.K3) (b : Bool) :
    Formal.Cells.K3.admits a b = true ↔ Formal.Core.K3.Le a (Formal.Core.K3.ofBool b) :=
  Formal.Cells.K3.admits_iff_le a b

/-! ## 2. LUTs on arbitrary lists -/

/-- The `k`-input Core LUT whose INIT is the low `2^k` bits of the number `init`. -/
abbrev lutOf (k init : Nat) : Lut k := ⟨BitVec.ofNat (2 ^ k) init⟩

theorem ofFn_ofList {α : Type} (d : α) (l : List α) : List.ofFn (ofList d l l.length) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem ofList_take {α : Type} (d : α) (l : List α) (n : Nat) : ofList d (l.take n) n = ofList d l n := by
  funext i
  simp only [ofList, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt]

theorem lutIdx_list (l : List Bool) : lutIdx l = addr (bvec l l.length) := by
  conv => lhs; rw [← ofFn_ofList false l]
  exact lutIdx_ofFn _

theorem lutOf_entry (k init a : Nat) (h : a < 2 ^ k) : (lutOf k init).entry a = init.testBit a := by
  rw [Lut.entry, BitVec.getLsbD_ofNat]; simp [h]

/-- **`lutB` is Core's `Lut.eval`** on any pin list `[I0, I1, …]`, for any INIT number. -/
theorem lutB_list (init : Nat) (l : List Bool) :
    lutB init l = (lutOf l.length init).eval (bvec l l.length) := by
  rw [lutB, Lut.eval, lutOf_entry _ _ _ (addr_lt _), lutIdx_list]

/-- `lutB_list` at a stated width `n = l.length`. -/
theorem lutB_len {init n : Nat} {l : List Bool} (hn : l.length = n) :
    lutB init l = (lutOf n init).eval (bvec l n) := by
  subst hn; exact lutB_list init l

/-- `muxTree` is Core's `kevalT` on any list. -/
theorem muxTree_list (g : Nat → Bool) (l : List Formal.Core.K3) :
    muxTree g l = kevalT l.length g (kvec l l.length) := by
  conv => lhs; rw [← ofFn_ofList Formal.Core.K3.X l]
  exact muxTree_ofFn _ _ _

/-- `kevalT k` reads only the table entries below `2^k`. -/
theorem kevalT_congr_lt : ∀ (k : Nat) (g g' : Nat → Bool) (v : Fin k → Formal.Core.K3),
    (∀ a, a < 2 ^ k → g a = g' a) → kevalT k g v = kevalT k g' v
  | 0, g, g', _, h => by simp [kevalT, h 0 (by decide)]
  | k + 1, g, g', v, h => by
      have h0 := kevalT_congr_lt k (fun a => g (2 * a)) (fun a => g' (2 * a)) (vtail v)
        (fun a ha => h _ (by rw [Nat.pow_succ]; omega))
      have h1 := kevalT_congr_lt k (fun a => g (2 * a + 1)) (fun a => g' (2 * a + 1)) (vtail v)
        (fun a ha => h _ (by rw [Nat.pow_succ]; omega))
      simp only [kevalT, h0, h1]

/-- **`lutK` is Core's `Lut.keval`** on any pin list, for any INIT number. -/
theorem lutK_list (init : Nat) (l : List Formal.Core.K3) :
    lutK init l = (lutOf l.length init).keval (kvec l l.length) := by
  rw [lutK, muxTree_list, Lut.keval]
  exact kevalT_congr_lt _ _ _ _ (fun a ha => (lutOf_entry _ _ _ ha).symm)

theorem lutK_len {init n : Nat} {l : List Formal.Core.K3} (hn : l.length = n) :
    lutK init l = (lutOf n init).keval (kvec l n) := by
  subst hn; exact lutK_list init l

/-- **`lutK` is Core's specification `Lut.kevalSpec`** (the closure). -/
theorem lutK_list_spec (init : Nat) (l : List Formal.Core.K3) :
    lutK init l = (lutOf l.length init).kevalSpec (kvec l l.length) := by
  rw [lutK_list, Lut.keval_eq_kevalSpec]

/-! ### LUT6_2 outputs (6-pin lists) -/

/-- The Core `Lut62` with 64-bit INIT `init`. -/
abbrev lut62Of (init : Nat) : Lut62 := ⟨BitVec.ofNat 64 init⟩

theorem o6B_eq (init : Nat) (l : List Bool) (hl : l.length = 6) :
    o6B init l = (lut62Of init).o6.eval (bvec l 6) := by
  rw [o6B, lutB_len hl]; rfl

theorem o6K_eq (init : Nat) (l : List Formal.Core.K3) (hl : l.length = 6) :
    o6K init l = (lut62Of init).o6.keval (kvec l 6) := by
  rw [o6K, lutK_len hl]; rfl

theorem o5_entry (init a : Nat) (h : a < 2 ^ 5) :
    (lut62Of init).o5.entry a = (init % 2 ^ 32).testBit a := by
  simp only [Lut62.o5, Lut.entry, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow]
  have : a < 32 := by omega
  have : a < 64 := by omega
  simp [*]

theorem o5B_eq (init : Nat) (l : List Bool) (hl : l.length = 6) :
    o5B init l = (lut62Of init).o5.eval (bvec l 5) := by
  rw [o5B, lutB_len (n := 5) (by simp [hl]), bvec, bvec, ofList_take, Lut.eval, Lut.eval,
    lutOf_entry _ _ _ (addr_lt _), o5_entry _ _ (addr_lt _)]

theorem o5K_eq (init : Nat) (l : List Formal.Core.K3) (hl : l.length = 6) :
    o5K init l = (lut62Of init).o5.keval (kvec l 5) := by
  rw [o5K, lutK_len (n := 5) (by simp [hl]), kvec, kvec, ofList_take, Lut.keval, Lut.keval]
  exact kevalT_congr_lt _ _ _ _ (fun a ha => by rw [lutOf_entry _ _ _ ha, o5_entry _ _ ha])

/-! ### `completions` = the Boolean resolutions (Core's `Consistent`) -/

theorem mem_completions_cons (a : Formal.Core.K3) (as : List Formal.Core.K3) (b : Bool) (w : List Bool) :
    (b :: w) ∈ completions (a :: as) ↔ K3.admits a b = true ∧ w ∈ completions as := by
  cases a <;> cases b <;> simp [completions, K3.admits]

/-- **`completions` of a Core vector are exactly its `Consistent` Boolean resolutions.** -/
theorem ofFn_mem_completions_iff {k : Nat} (v : Fin k → Formal.Core.K3) (x : Fin k → Bool) :
    List.ofFn x ∈ completions (List.ofFn v) ↔ Formal.Core.K3.Consistent v x := by
  induction k with
  | zero => simp [completions, Formal.Core.K3.Consistent]
  | succ k ih =>
      rw [List.ofFn_succ, List.ofFn_succ, mem_completions_cons, ih (fun i => v i.succ) (fun i => x i.succ),
        K3.admits_iff_le]
      exact ⟨fun ⟨h0, hs⟩ i => Fin.cases h0 hs i, fun h => ⟨h 0, fun j => h j.succ⟩⟩

/-! ## 3. Traces and channels (CElemTiming) -/

section Traces
open Formal.Cells.CElemTiming
open Formal.Core.Substrate

theorem trace_eq : Formal.Cells.CElemTiming.Trace = Formal.Core.Substrate.Sig := rfl

/-- **B's window channel is the substrate's `Win`**, by definition. -/
theorem winDelay_eq_win : @WinDelay = @Win := rfl

theorem winDelay_iff_win {lo hi : Nat} {x y : Sig} : WinDelay lo hi x y ↔ Win lo hi x y := Iff.rfl

/-- **B's fixed transport delay is exactly `Win d d`** (output free before `d`). -/
theorem transport_iff_win {d : Nat} {x y : Sig} : Transport d x y ↔ Win d d x y := by
  constructor
  · intro h t ht
    exact ⟨t - d, by omega, by omega, by have := h (t - d); rwa [Nat.sub_add_cancel ht] at this⟩
  · intro h t
    obtain ⟨s, h1, h2, h3⟩ := h (t + d) (by omega)
    have : s = t := by omega
    rw [h3, this]

/-- Core's transport channel `[d, d]` (output = `delay d x`, also before `d`)
is a B transport behaviour. -/
theorem transport_of_core {d : Nat} {x y : Sig} (h : TraceDiscrete.Transport d d x y) :
    Transport d x y := by
  have := TraceDiscrete.transport_exact h
  intro t; rw [this]; simp [TraceDiscrete.delay]

/-- Strictness: B's `Transport` leaves `[0, d)` free; Core's does not. -/
theorem not_core_of_transport :
    Transport 1 (fun _ => false) (fun t => decide (t = 0)) ∧
      ¬ TraceDiscrete.Transport 1 1 (fun _ => false) (fun t => decide (t = 0)) := by
  refine ⟨fun t => by simp, fun h => ?_⟩
  have := congrFun (TraceDiscrete.transport_exact h) 0
  simp [TraceDiscrete.delay] at this

/-- `exc` is the Core LUT `Lut.eval` of the cell's 6-input LUT. -/
theorem exc_eq_eval (init : Nat) (a b q r : Bool) :
    exc init a b q r = (lutOf 6 init).eval (bvec [a, b, q, r, false, false] 6) := by
  rw [exc, lutB_list]; rfl

/-- B's feedback-LUT cell relation: two substrate `Win` relations and H_LOOP_POS. -/
theorem loop_iff_win {init : Nat} {a b rst O qp : Sig} {dlmin dlmax dwmin dwmax : Nat} :
    Loop init a b rst O qp dlmin dlmax dwmin dwmax ↔
      Win dlmin dlmax (fun t => exc init (a t) (b t) (qp t) (rst t)) O ∧
      Win dwmin dwmax O qp ∧ 0 < dlmin + dwmin :=
  ⟨fun L => ⟨L.H_LUT, L.H_FB, L.H_LOOP_POS⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-! ### Inertial: B's `Inertial d` vs Core's `TraceDiscrete.inertial (d - 1)` -/

/-- Core's inertial trace, one tick late. -/
def coreInertial (d : Nat) (x : Sig) : Sig := fun t => TraceDiscrete.inertial (d - 1) x (t - 1)

theorem stable_iff_stab {d t : Nat} (x : Sig) (hd : 1 ≤ d) :
    (∀ k, k < d → x (t + k) = x t) ↔ TraceDiscrete.stab x (d - 1) (t + (d - 1)) = true := by
  rw [TraceDiscrete.stab_iff]
  constructor
  · intro h k hk
    rw [show t + (d - 1) - k = t + (d - 1 - k) by omega, h _ (by omega), h _ (by omega)]
  · intro h k hk
    have e1 := h (d - 1 - k) (by omega)
    have e2 := h (d - 1) (by omega)
    rw [show t + (d - 1) - (d - 1 - k) = t + k by omega] at e1
    rw [show t + (d - 1) - (d - 1) = t by omega] at e2
    rw [e1, e2]

/-- **Core's inertial delay, one tick late, is a B `Inertial d` behaviour** (`d ≥ 1`). -/
theorem inertial_of_core {d : Nat} (x : Sig) (hd : 1 ≤ d) : Inertial d x (coreInertial d x) := by
  intro t
  simp only [coreInertial]
  by_cases hs : ∀ k, k < d → x (t + k) = x t
  · rw [if_pos hs]
    have hst := (stable_iff_stab x hd).mp hs
    rcases Nat.eq_zero_or_pos (t + (d - 1)) with h0 | hpos
    · have : t + d - 1 = 0 := by omega
      rw [this]; simp only [TraceDiscrete.inertial]
      have : t = 0 := by omega
      rw [this]
    · obtain ⟨m, hm⟩ : ∃ m, t + d - 1 = m + 1 := ⟨t + d - 2, by omega⟩
      rw [hm, TraceDiscrete.inertial]
      rw [show m + 1 = t + (d - 1) by omega, if_pos hst]
      exact hs (d - 1) (by omega)
  · rw [if_neg hs]
    have hst : ¬ TraceDiscrete.stab x (d - 1) (t + (d - 1)) = true :=
      fun h => hs ((stable_iff_stab x hd).mpr h)
    have hpos : 0 < t + (d - 1) := by
      rcases Nat.eq_zero_or_pos (t + (d - 1)) with h0 | h
      · exact absurd (fun k hk => by have : t = 0 := by omega
                                     have : k = 0 := by omega
                                     subst_vars; rfl) hs
      · exact h
    obtain ⟨m, hm⟩ : ∃ m, t + d - 1 = m + 1 := ⟨t + d - 2, by omega⟩
    rw [hm, TraceDiscrete.inertial, show m + 1 = t + (d - 1) by omega, if_neg hst]
    congr 1; omega

/-- **Exactness with a power-up hypothesis.** A B `Inertial d` behaviour whose
power-up value at `d - 1` agrees with Core's (**H_POWERUP**) equals Core's
inertial trace (one tick late) from `d - 1` on. -/
theorem core_of_inertial {d : Nat} {x y : Sig} (hd : 1 ≤ d) (h : Inertial d x y)
    (H_POWERUP : y (d - 1) = coreInertial d x (d - 1)) :
    ∀ t, d - 1 ≤ t → y t = coreInertial d x t := by
  have hc := inertial_of_core x hd
  intro t ht
  obtain ⟨j, rfl⟩ : ∃ j, t = d - 1 + j := ⟨t - (d - 1), by omega⟩
  clear ht
  induction j with
  | zero => exact H_POWERUP
  | succ n ih =>
      have e1 := h n
      have e2 := hc n
      rw [show n + d = d - 1 + (n + 1) by omega, show d - 1 + (n + 1) - 1 = d - 1 + n by omega]
        at e1 e2
      rw [e1, e2, ih]

/-- Non-vacuity of `core_of_inertial`: for every `d ≥ 1` and input `x`, the
shifted Core trace satisfies all its hypotheses. -/
theorem core_of_inertial_nonvacuous {d : Nat} (x : Sig) (hd : 1 ≤ d) :
    Inertial d x (coreInertial d x) ∧ coreInertial d x (d - 1) = coreInertial d x (d - 1) :=
  ⟨inertial_of_core x hd, rfl⟩

/-- H_POWERUP cannot be dropped: input alternating every tick, so it is never
stable for 2 ticks; a B `Inertial 2` channel may hold power-up `true` forever,
while Core's inertial trace stays at the input's initial value `false`. -/
theorem inertial_powerup_needed :
    Inertial 2 (fun t => t % 2 == 1) (fun _ => true) ∧
      coreInertial 2 (fun t => t % 2 == 1) 1 = false := by
  refine ⟨fun t => ?_, by decide⟩
  have : ¬ ∀ k, k < 2 → ((t + k) % 2 == 1) = (t % 2 == 1) := by
    intro h; have := h 1 (by decide)
    revert this; rcases Nat.mod_two_eq_zero_or_one t with e | e <;>
      simp [Nat.add_mod, e]
  simp only [this, if_false]

end Traces

end Formal.Cells.PrelimCore
