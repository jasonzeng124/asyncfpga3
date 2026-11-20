#!/usr/bin/env python3
"""opsx_patch.py TOOLSCOPY -- runtime patch to a COPY of autoproof.py: a stronger leaf tactic.

The generated file gets a local macro `auto_ops2` (and a few lemmas, all proved in the file,
Core Lean only): before AutoLib's `auto_ops`, it also folds literal `&&&`, `^^^`, `|||`, `/`,
`+`, `-`, `*` (Nat.reduce* simprocs), rewrites `x &&& (2^n-1)` to `x % 2^n` (n = 2..5), and
`(x % 2^32 / 2^27) ^^^ 31` to `31 - (x % 2^32 / 2^27)` (proved: the left operand is < 32;
LLVM writes `31 - (acc >> 27)` as an xor), and unfolds `Ops.extsi` (literal sign extensions fold). Every component lemma's leaf uses `auto_ops2`."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()

def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old, s.count(old))
    s = s.replace(old, new)

HDR = r'''
theorem and_m3 (x : Nat) : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2
theorem and_m7 (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
theorem and_m15 (x : Nat) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4
theorem and_m31 (x : Nat) : x &&& 31 = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5
theorem xor31_lt : ∀ k < 32, k ^^^ 31 = 31 - k := by decide
theorem xor31_shr27 (x : Nat) : x % 4294967296 / 134217728 ^^^ 31 = 31 - x % 4294967296 / 134217728 :=
  xor31_lt _ (by have := Nat.mod_lt x (by decide : 0 < 4294967296); omega)

theorem xor_mod32 (a b : Nat) : (a ^^^ b) % 4294967296 = a % 4294967296 ^^^ b % 4294967296 :=
  Nat.xor_mod_two_pow (n := 32)
theorem xor_lcomm (x y z : Nat) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← Nat.xor_assoc, Nat.xor_comm x y, Nat.xor_assoc]

/-- `auto_ops` after folding literal bit operations and a few mask / xor identities; if that
fails, again after normalising xor modulo 2^32 (distribute `% 2^32`, AC, then fold the literals) (local, opsx patch). -/
macro "auto_ops2_pre" : tactic => `(tactic| (
  try simp only [E.eval, BOp.ev, UOp.ev, Ops.addi, Ops.subi, Ops.muli, Ops.andi, Ops.ori,
    Ops.xori, Ops.shli, Ops.shrui, Ops.trunci, Ops.extui, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod, Nat.pow_one,
    Nat.reduceAnd, Nat.reduceXor, Nat.reduceOr, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
    and_m3, and_m7, and_m15, and_m31, xor31_shr27] at *
  try simp only [Ops.extsi, Nat.reducePow, Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceAnd, Nat.reduceXor, Nat.reduceOr, ↓reduceIte] at *))
macro "auto_ops2" : tactic => `(tactic| first
  | (auto_ops2_pre; auto_ops; done)
  | (auto_ops2_pre
     try simp only [xor_mod32, Nat.mod_mod, Nat.reduceMod, Nat.reduceXor, Nat.xor_assoc, Nat.xor_comm, xor_lcomm] at *
     try simp only [← Nat.xor_assoc, Nat.reduceXor] at *
     auto_ops))
'''
rep('    w(f"open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto {opt.graph_ns}\\n")\n',
    '    w(f"open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto {opt.graph_ns}\\n")\n    w(' + repr(HDR) + ')\n')
rep('        L.append("  auto_ops")\n', '        L.append("  auto_ops2")\n')
open(a, 'w').write(s)
