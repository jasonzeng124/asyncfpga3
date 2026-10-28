import Formal.Core.XAudit.Parse

/-!
# Formal.Core.XAudit.BandCheck — reject malformed band files before the reader sees them

Probe A / KapRes2. The trusted band reader `Parse.parseBands` / `Parse.toSteps` has two
silent behaviours on bad input:

* an entry of `cells` / `arcs` that is not a JSON array of exactly two naturals is DROPPED
  (`filterMap` over `pairOf`), so that arc or gate gets the default band instead;
* a band with `lo > hi` is NARROWED to `[lo, lo]` by `toSteps` (`toSteps_inverted` below),
  with no flag. The committed FAST band files have such bands on 2–20 arcs per gcd_hw seed
  (prjxray-db's BRKH_INT pips have FAST_MIN > FAST_MAX, `formal/notes/A-kapres2.md`).

`jsonBandsOK` is a decidable check on the raw JSON that rejects both. This file proves what
passing it guarantees (`checked_complete`, `checked_ordered`, `checked_steps`): every entry of
the file is read, with exactly the file's band (only `lo = 0` is changed, to 1, and that is
flagged, as before). The committed executables do not call it (they are shared modules this
probe does not edit); the same check runs as `kapres2/check_bands.py check` in front of them,
and the lead may wire `jsonBandsOK` into `Parse` / the `run` functions (notes, "For the lead").

TRUSTED, as `Parse` is: that `Lean.Json`'s parser reads the file's text faithfully.
NOT covered: whether the numbers in the file are right (that is the data's provenance).
-/

namespace Formal.Core.XAudit.BandCheck

open Lean (Json)
open Formal.Core.XAudit.Parse

/-- A band is well formed: `lo ≤ hi`. -/
def bandOK (b : Nat × Nat) : Bool := decide (b.1 ≤ b.2)

/-- One raw entry: two naturals (`Parse.pairOf` accepts it) with `lo ≤ hi`. -/
def entryOK (v : Json) : Bool :=
  match pairOf v with
  | some b => bandOK b
  | none => false

/-- The raw entries of a section, exactly as `parseBands` iterates over them. -/
def rawSec (j : Json) (k : String) : List (String × Json) := ((jget j k).map jobj).getD []

/-- A section (`cells`, `arcs`) is absent, or an object every entry of which is `entryOK`. -/
def sectionOK (j : Json) (k : String) : Bool :=
  match jget j k with
  | none => true
  | some s => match s.getObj? with
    | .ok _ => (jobj s).all (fun kv => entryOK kv.2)
    | .error _ => false

/-- A summary field is absent or `entryOK`. -/
def fieldOK (j : Json) (k : String) : Bool :=
  match jget j k with
  | none => true
  | some v => entryOK v

/-- **The check.** -/
def jsonBandsOK (j : Json) : Bool :=
  sectionOK j "cells" && sectionOK j "arcs" &&
  fieldOK j "lut" && fieldOK j "route" && fieldOK j "feedback" && fieldOK j "pad_steps"

/-- The violations, for a report (empty iff the check passes on the sections). -/
def violations (j : Json) : List String :=
  let sec (k : String) : List String :=
    match jget j k with
    | none => []
    | some s => match s.getObj? with
      | .ok _ => ((jobj s).filter (fun kv => !entryOK kv.2)).map (fun kv => s!"{k} {kv.1} {kv.2.compress}")
      | .error _ => [s!"{k}: not an object"]
  let fld (k : String) : List String :=
    match jget j k with
    | none => []
    | some v => if entryOK v then [] else [s!"{k} {v.compress}"]
  sec "cells" ++ sec "arcs" ++ fld "lut" ++ fld "route" ++ fld "feedback" ++ fld "pad_steps"

/-! ## What the reader does with a band -/

/-- An ordered band with `lo ≥ 1` is read exactly (unit 1 ps, as every `Events*Main` sets). -/
theorem toSteps_exact {b : Nat × Nat} (h1 : 1 ≤ b.1) (h : b.1 ≤ b.2) :
    toSteps 1 b = (b.1, b.2, false) := by
  obtain ⟨lo, hi⟩ := b
  simp only at h1 h
  simp only [toSteps, Nat.div_one, Nat.add_sub_cancel]
  have e1 : max 1 lo = lo := Nat.max_eq_right h1
  have e2 : max lo hi = hi := Nat.max_eq_right h
  have e3 : (lo == 0) = false := by
    cases lo with
    | zero => omega
    | succ n => rfl
  rw [e1, e2, e3]

/-- `lo = 0` is raised to 1 and FLAGGED (`Parse.bandFor` records it in `raised`). -/
theorem toSteps_zero {hi : Nat} : toSteps 1 (0, hi) = (1, max 1 hi, true) := by
  simp [toSteps]

/-- **The silent narrowing**: an inverted band with `lo ≥ 1` is read as `[lo, lo]`, with the
flag false. This is why the check rejects `lo > hi`. -/
theorem toSteps_inverted {b : Nat × Nat} (h1 : 1 ≤ b.1) (h : b.2 < b.1) :
    toSteps 1 b = (b.1, b.1, false) := by
  obtain ⟨lo, hi⟩ := b
  simp only at h1 h
  simp only [toSteps, Nat.div_one, Nat.add_sub_cancel]
  have e1 : max 1 lo = lo := Nat.max_eq_right h1
  have e2 : max lo hi = lo := Nat.max_eq_left (Nat.le_of_lt h)
  have e3 : (lo == 0) = false := by
    cases lo with
    | zero => omega
    | succ n => rfl
  rw [e1, e2, e3]

/-- For any unit `u > 0`, an ordered band's step band covers it outward (the lo side unless
raised, which is flagged). -/
theorem toSteps_covers {u : Nat} (hu : 0 < u) {b : Nat × Nat} (h : b.1 ≤ b.2) :
    b.2 ≤ (toSteps u b).2.1 * u ∧ ((toSteps u b).1 * u ≤ b.1 ∨ (toSteps u b).2.2 = true) := by
  obtain ⟨lo, hi⟩ := b
  simp only at h
  simp only [toSteps]
  constructor
  · have : hi ≤ (hi + u - 1) / u * u := by
      have h1 := Nat.div_add_mod (hi + u - 1) u
      have h2 := Nat.mod_lt (hi + u - 1) hu
      rw [Nat.mul_comm] at h1
      omega
    exact Nat.le_trans this (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
  · by_cases h0 : lo / u = 0
    · right; simp [h0]
    · left
      have : max 1 (lo / u) = lo / u := Nat.max_eq_right (Nat.pos_of_ne_zero h0)
      rw [this]; exact Nat.div_mul_le_self _ _

/-! ## What passing the check guarantees -/

theorem sectionOK_entries {j : Json} {k : String} (h : sectionOK j k = true) :
    ∀ kv ∈ rawSec j k, entryOK kv.2 = true := by
  intro kv hkv
  unfold sectionOK at h
  unfold rawSec at hkv
  cases hj : jget j k with
  | none => rw [hj] at hkv; simp at hkv
  | some s =>
    rw [hj] at h hkv
    simp only [Option.map_some, Option.getD_some] at hkv
    dsimp only at h
    cases hs : s.getObj? with
    | error e => rw [hs] at h; simp at h
    | ok _ =>
      rw [hs] at h
      exact (List.all_eq_true.mp h) kv hkv

theorem entryOK_pair {v : Json} (h : entryOK v = true) : ∃ b, pairOf v = some b ∧ b.1 ≤ b.2 := by
  unfold entryOK at h
  cases hp : pairOf v with
  | none => rw [hp] at h; simp at h
  | some b => rw [hp] at h; exact ⟨b, rfl, by simpa [bandOK] using h⟩

theorem parse_cells (j : Json) :
    (parseBands j).cells = (rawSec j "cells").filterMap (fun (k, v) => (pairOf v).map (k, ·)) := rfl

theorem parse_arcs (j : Json) :
    (parseBands j).arcs = (rawSec j "arcs").filterMap (fun (k, v) => (pairOf v).map (k, ·)) := rfl

/-- Completeness on a checked section: every raw entry is read (none dropped), as its band. -/
theorem complete_of_sectionOK {j : Json} {k : String} (h : sectionOK j k = true) :
    ∀ kv ∈ rawSec j k, ∃ b, pairOf kv.2 = some b ∧ b.1 ≤ b.2 ∧
      (kv.1, b) ∈ (rawSec j k).filterMap (fun (k, v) => (pairOf v).map (k, ·)) := by
  intro kv hkv
  obtain ⟨b, hb, hle⟩ := entryOK_pair (sectionOK_entries h kv hkv)
  refine ⟨b, hb, hle, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨kv, hkv, by simp [hb]⟩

/-- Order on a checked section: every band read from it has `lo ≤ hi`. -/
theorem ordered_of_sectionOK {j : Json} {k : String} (h : sectionOK j k = true) :
    ∀ kb ∈ (rawSec j k).filterMap (fun (k, v) => (pairOf v).map (k, ·)), kb.2.1 ≤ kb.2.2 := by
  intro kb hkb
  rw [List.mem_filterMap] at hkb
  obtain ⟨kv, hkv, he⟩ := hkb
  obtain ⟨b, hb, hle⟩ := entryOK_pair (sectionOK_entries h kv hkv)
  obtain ⟨k', v⟩ := kv
  simp only at hb he
  rw [hb] at he
  simp only [Option.map_some, Option.some.injEq] at he
  subst he
  exact hle

theorem field_ordered {j : Json} {k : String} {d : Nat × Nat} (h : fieldOK j k = true)
    (hd : d.1 ≤ d.2) : (((jget j k).bind pairOf).getD d).1 ≤ (((jget j k).bind pairOf).getD d).2 := by
  unfold fieldOK at h
  cases hj : jget j k with
  | none => simpa using hd
  | some v =>
    rw [hj] at h
    obtain ⟨b, hb, hle⟩ := entryOK_pair h
    simp [hb, hle]

theorem jsonBandsOK_parts {j : Json} (h : jsonBandsOK j = true) :
    sectionOK j "cells" = true ∧ sectionOK j "arcs" = true ∧ fieldOK j "lut" = true ∧
    fieldOK j "route" = true ∧ fieldOK j "feedback" = true ∧ fieldOK j "pad_steps" = true := by
  unfold jsonBandsOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  exact ⟨a, b, c, d, e, f⟩

/-- **Completeness.** On a checked file, every raw `cells` / `arcs` entry is in the parsed
band list with its band (no entry silently falls back to a default band). -/
theorem checked_complete {j : Json} (h : jsonBandsOK j = true) :
    (∀ kv ∈ rawSec j "cells", ∃ b, pairOf kv.2 = some b ∧ (kv.1, b) ∈ (parseBands j).cells) ∧
    (∀ kv ∈ rawSec j "arcs", ∃ b, pairOf kv.2 = some b ∧ (kv.1, b) ∈ (parseBands j).arcs) := by
  obtain ⟨hc, ha, -⟩ := jsonBandsOK_parts h
  refine ⟨fun kv hkv => ?_, fun kv hkv => ?_⟩
  · obtain ⟨b, hb, -, hm⟩ := complete_of_sectionOK hc kv hkv
    exact ⟨b, hb, by rw [parse_cells]; exact hm⟩
  · obtain ⟨b, hb, -, hm⟩ := complete_of_sectionOK ha kv hkv
    exact ⟨b, hb, by rw [parse_arcs]; exact hm⟩

/-- **Order.** On a checked file every band the reader holds has `lo ≤ hi`: every cell and arc
band, `lut`, `route`, `pad`, and `feedback` when present. -/
theorem checked_ordered {j : Json} (h : jsonBandsOK j = true) :
    (∀ kb ∈ (parseBands j).cells, kb.2.1 ≤ kb.2.2) ∧
    (∀ kb ∈ (parseBands j).arcs, kb.2.1 ≤ kb.2.2) ∧
    (parseBands j).lut.1 ≤ (parseBands j).lut.2 ∧
    (parseBands j).route.1 ≤ (parseBands j).route.2 ∧
    (parseBands j).pad.1 ≤ (parseBands j).pad.2 ∧
    (∀ b, (parseBands j).feedback = some b → b.1 ≤ b.2) := by
  obtain ⟨hc, ha, hl, hr, hf, hp⟩ := jsonBandsOK_parts h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parse_cells]; exact ordered_of_sectionOK hc
  · rw [parse_arcs]; exact ordered_of_sectionOK ha
  · exact field_ordered (d := (45, 124)) hl (by decide)
  · exact field_ordered (d := (100, 700)) hr (by decide)
  · exact field_ordered (d := (1, 1)) hp (by decide)
  · intro b hb
    unfold fieldOK at hf
    simp only [parseBands] at hb
    cases hj : jget j "feedback" with
    | none => rw [hj] at hb; simp at hb
    | some v =>
      rw [hj] at hf hb
      obtain ⟨b', hb', hle⟩ := entryOK_pair hf
      simp only [Option.bind_some] at hb
      rw [hb'] at hb
      cases hb
      exact hle

/-- **The step bands of a checked file** (unit 1 ps, as in every `Events*Main`): every cell or
arc band of the file is read exactly, except that `lo = 0` becomes 1 with the `raised` flag.
In particular no band is narrowed. -/
theorem checked_steps {j : Json} (h : jsonBandsOK j = true) :
    ∀ kb ∈ (parseBands j).cells ++ (parseBands j).arcs,
      (1 ≤ kb.2.1 → toSteps 1 kb.2 = (kb.2.1, kb.2.2, false)) ∧
      (kb.2.1 = 0 → toSteps 1 kb.2 = (1, max 1 kb.2.2, true)) := by
  obtain ⟨hc, ha, -, -, -, -⟩ := checked_ordered h
  intro kb hkb
  have hle : kb.2.1 ≤ kb.2.2 := by
    rcases List.mem_append.mp hkb with m | m
    · exact hc kb m
    · exact ha kb m
  refine ⟨fun h1 => toSteps_exact h1 hle, fun h0 => ?_⟩
  obtain ⟨k, lo, hi⟩ := kb
  simp only at h0 ⊢
  subst h0
  exact toSteps_zero

end Formal.Core.XAudit.BandCheck
