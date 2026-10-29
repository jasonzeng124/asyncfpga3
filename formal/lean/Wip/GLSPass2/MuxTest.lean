/-- slice `v[hi:lo]` of width `w` starting at `lo`. -/
def slice (v lo w : Nat) : Nat := v / 2 ^ lo % 2 ^ w

def muxTree6 (INIT : Nat) (a1 a2 a3 a4 a5 a6 : Bool) : Bool :=
  let u5 := if a6 then slice INIT 32 32 else slice INIT 0 32
  let u4 := if a5 then slice u5 16 16 else slice u5 0 16
  let u3 := if a4 then slice u4 8 8 else slice u4 0 8
  let u2 := if a3 then slice u3 4 4 else slice u3 0 4
  let u1 := if a2 then slice u2 2 2 else slice u2 0 2
  if a1 then u1.testBit 1 else u1.testBit 0

def idx6 (a1 a2 a3 a4 a5 a6 : Bool) : Nat :=
  a1.toNat + 2 * a2.toNat + 4 * a3.toNat + 8 * a4.toNat + 16 * a5.toNat + 32 * a6.toNat

theorem testBit_slice (v lo w i : Nat) :
    (slice v lo w).testBit i = (decide (i < w) && v.testBit (i + lo)) := by
  simp [slice, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem muxTree6_eq (INIT : Nat) (a1 a2 a3 a4 a5 a6 : Bool) :
    muxTree6 INIT a1 a2 a3 a4 a5 a6 = INIT.testBit (idx6 a1 a2 a3 a4 a5 a6) := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;>
    simp only [muxTree6, idx6, testBit_slice, ite_true, ite_false, Bool.false_eq_true,
      Bool.toNat_true, Bool.toNat_false, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT,
      decide_true, Bool.true_and]
