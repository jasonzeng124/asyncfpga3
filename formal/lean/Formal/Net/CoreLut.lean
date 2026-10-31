import Formal.Core.Lut

/-!
# Probe 11e: shard C's list view of shard A's Core LUT semantics

Shard C's netlists (`Formal.Gen`, `Formal.Net.Import`, `Formal.Net.Fasm`) carry
a LUT's INIT as a `Nat` and its pins as a list `[I0, I1, ...]`, as yosys and the
FASM give them. This file reads such a pair with **shard A's Core semantics**
(`Formal.Core.Lut`: `Lut k`, `Lut.eval`, `Lut.keval`, `Lut62.o5/o6`, the
canonical `Formal.Core.K3`). Nothing is redefined: every function below is a
Core function applied to `Lut k := ⟨BitVec.ofNat (2^k) init⟩` and to the pin
vector `bvec`/`kvec` of `Formal.Core.Lut`.

It replaces shard B's `Formal.Cells.Prelim` (`lutB`, `lutK`, `o5B`, `o6B`,
`K3.mux`) in shard C's files, so they survive B's planned deletion of Prelim
(formal/PROGRAM.md, Phase 1). Name map:

| Prelim (shard B) | here (Core) |
|---|---|
| `Formal.Core.LutList.K3` `f t x` | `Formal.Core.K3` `zero one X` |
| `lutB init ins` | `evalL init ins` = `(lutOf init ins.length).eval (bvec ins ins.length)` |
| `lutK init ins` (H_KLEENE_LUT) | `kevalL init ins` = `(lutOf init ins.length).keval (kvec ..)` |
| `o6B` / `o5B` | `o6L` / `o5L` (`Lut62.o6` / `Lut62.o5`) |
| `o6K` / `o5K` | `o6KL` / `o5KL` |
| `K3.mux s a b` | `kmux s a b` (select `X`: `K3.merge`, as in Core's `kevalT`) |
| `K3.join` | `K3.merge` |

The equality with Prelim, for every INIT and every pin list, is proved in
`Formal.Net.CoreLutPrelim` (`lutB_eq_evalL`, `lutK_eq_kevalL`, ...), which
is deleted together with Prelim.

Main lemmas here: `evalL_eq_testBit` (the INIT bit at the LSB-first address,
for fast `decide`), `kevalL_ofBool`, `kevalTL_cons` (the head pin is the
root mux select), `kevalT_congr`, `kmux_eq_kevalL`.
-/

namespace Formal.Net.CoreLut
open Formal.Core Formal.Core.K3

/-- The Core `k`-input LUT whose INIT is the natural number `init` (bit `j` =
output at address `j`, `I0` = LSB; bits at `2^k` and above are not part of a
`k`-input LUT and are dropped). -/
def lutOf (init k : Nat) : Lut k := ⟨BitVec.ofNat (2 ^ k) init⟩

/-- The Core `LUT6_2` with this 64-bit INIT. -/
def lut62Of (init : Nat) : Lut62 := ⟨BitVec.ofNat 64 init⟩

/-- Core Boolean LUT on a pin list `[I0, I1, ...]` (`k` = number of pins). -/
def evalL (init : Nat) (ins : List Bool) : Bool :=
  (lutOf init ins.length).eval (bvec ins ins.length)

/-- Core Kleene LUT (`Lut.keval`, the mux tree; = `Lut.kevalSpec`) on a pin list. -/
def kevalL (init : Nat) (ins : List K3) : K3 :=
  (lutOf init ins.length).keval (kvec ins ins.length)

/-- `LUT6_2` outputs, pins `[I0, ..., I5]`: `O6` = LUT6, `O5` = LUT5 on `I0..I4`
reading `INIT[31:0]` (Core `Lut62`). -/
def o6L (init : Nat) (ins : List Bool) : Bool := (lut62Of init).o6.eval (bvec ins 6)
def o5L (init : Nat) (ins : List Bool) : Bool := (lut62Of init).o5.eval (bvec ins 5)
def o6KL (init : Nat) (ins : List K3) : K3 := (lut62Of init).o6.keval (kvec ins 6)
def o5KL (init : Nat) (ins : List K3) : K3 := (lut62Of init).o5.keval (kvec ins 5)

/-- The Kleene 2:1 mux of Core's mux-tree reading (`kevalT`): select `zero`
takes `a`, `one` takes `b`, `X` gives `K3.merge a b`. -/
def kmux (s a b : K3) : K3 :=
  match s with
  | .zero => a
  | .one => b
  | .X => merge a b

/-- Decidability of `∀` over `K3`, for `decide` on Kleene statements. -/
instance decForall {P : K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
  if h : P .zero ∧ P .one ∧ P .X then
    isTrue (fun k => by cases k <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _⟩)

/-! ## Lemmas -/

/-- LSB-first address of a pin list. -/
def lsbIdx : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * lsbIdx bs

theorem lsbIdx_lt : ∀ l : List Bool, lsbIdx l < 2 ^ l.length
  | [] => by decide
  | b :: bs => by
      have := lsbIdx_lt bs
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      simp only [lsbIdx, List.length_cons, Nat.pow_succ]
      omega

theorem vtail_ofList {α : Type} (d a : α) (l : List α) (k : Nat) :
    vtail (ofList d (a :: l) (k + 1)) = ofList d l k := by
  funext i; rfl

theorem addr_bvec : ∀ l : List Bool, addr (bvec l l.length) = lsbIdx l
  | [] => rfl
  | b :: bs => by
      show (bvec (b :: bs) (bs.length + 1) 0).toNat + 2 * addr (vtail (bvec (b :: bs) (bs.length + 1))) = _
      rw [vtail_ofList, addr_bvec bs]; rfl

theorem entry_lutOf {init k a : Nat} (h : a < 2 ^ k) : (lutOf init k).entry a = init.testBit a := by
  show (BitVec.ofNat (2 ^ k) init).getLsbD a = _
  rw [BitVec.getLsbD_ofNat]; simp [h]

/-- The Core Boolean LUT reads INIT bit `lsbIdx ins` (used to keep `decide` fast). -/
theorem evalL_eq_testBit (init : Nat) (ins : List Bool) : evalL init ins = init.testBit (lsbIdx ins) := by
  unfold evalL Lut.eval
  rw [addr_bvec, entry_lutOf (lsbIdx_lt ins)]

/-- Core's mux tree only reads table entries below `2^k`. -/
theorem kevalT_congr : ∀ (k : Nat) (t t' : Nat → Bool) (v : Fin k → K3),
    (∀ a, a < 2 ^ k → t a = t' a) → kevalT k t v = kevalT k t' v
  | 0, t, t', v, h => by simp [kevalT, h 0 (by decide)]
  | k + 1, t, t', v, h => by
      have h0 : ∀ a, a < 2 ^ k → t (2 * a) = t' (2 * a) := fun a ha =>
        h _ (by rw [Nat.pow_succ]; omega)
      have h1 : ∀ a, a < 2 ^ k → t (2 * a + 1) = t' (2 * a + 1) := fun a ha =>
        h _ (by rw [Nat.pow_succ]; omega)
      have e0 := kevalT_congr k _ _ (vtail v) h0
      have e1 := kevalT_congr k _ _ (vtail v) h1
      simp only [kevalT]
      rw [e0, e1]

/-- `kevalL` with an arbitrary table: Core's `kevalT` on the pin list. -/
def kevalTL (t : Nat → Bool) (ins : List K3) : K3 := kevalT ins.length t (kvec ins ins.length)

theorem kevalL_eq_kevalTL (init : Nat) (ins : List K3) : kevalL init ins = kevalTL init.testBit ins :=
  kevalT_congr _ _ _ _ (fun _ ha => entry_lutOf ha)

theorem kevalTL_nil (t : Nat → Bool) : kevalTL t [] = ofBool (t 0) := rfl

/-- The head pin `I0` is the select of the root mux, as in Core's `kevalT`. -/
theorem kevalTL_cons (t : Nat → Bool) (a : K3) (as : List K3) :
    kevalTL t (a :: as) = kmux a (kevalTL (fun j => t (2 * j)) as) (kevalTL (fun j => t (2 * j + 1)) as) := by
  show kevalT (as.length + 1) t (kvec (a :: as) (as.length + 1)) = _
  simp only [kevalT]
  rw [vtail_ofList]
  cases a <;> rfl

theorem kvec_map_ofBool (l : List Bool) :
    kvec (l.map ofBool) l.length = ofBoolVec (bvec l l.length) := by
  funext i
  have hi : i.val < l.length := i.isLt
  simp only [ofList, ofBoolVec]
  simp [List.getD_eq_getElem?_getD, hi]

/-- On Boolean pins the Kleene LUT is the Boolean one (Core `keval_ofBoolVec`). -/
theorem kevalL_ofBool (init : Nat) (ins : List Bool) :
    kevalL init (ins.map ofBool) = ofBool (evalL init ins) := by
  unfold kevalL evalL
  rw [List.length_map, kvec_map_ofBool]
  exact Lut.keval_ofBoolVec _ _

/-- `MUXF7`/`MUXF8`-style table `0xCA` on `[I0, I1, S]` is the Kleene mux. -/
theorem kmux_eq_kevalL : ∀ a b s : K3, kevalL 0xCA [a, b, s] = kmux s a b := by
  decide +kernel

theorem o6L_eq_evalL (init : Nat) (ins : List Bool) (h : ins.length = 6) :
    o6L init ins = evalL init ins := by
  unfold o6L evalL lutOf lut62Of Lut62.o6
  rw [h]

theorem o5L_eq_evalL (init : Nat) (ins : List Bool) (h : ins.length = 6) :
    o5L init ins = evalL (init % 2 ^ 32) (ins.take 5) := by
  have ht : (ins.take 5).length = 5 := by simp [h]
  unfold o5L evalL
  rw [ht]
  have hL : (lut62Of init).o5 = lutOf (init % 2 ^ 32) 5 := by
    unfold lut62Of Lut62.o5 lutOf
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
    simp
  have hv : bvec ins 5 = bvec (ins.take 5) 5 := by
    funext i
    have hi : i.val < 5 := i.isLt
    simp [ofList, List.getD_eq_getElem?_getD, hi]
  rw [hL, hv]

end Formal.Net.CoreLut
