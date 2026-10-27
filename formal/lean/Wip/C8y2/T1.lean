structure Ker where
  rules : List Nat
  n : Nat

class Ker.OK (κ : Ker) : Prop where
  len : κ.rules.length = κ.n

section
variable {κ : Ker} [hκ : κ.OK]

def foo (c : Fin κ.n) : Nat := κ.rules.length + c.val
theorem foo_eq (c : Fin κ.n) : foo c = κ.n + c.val := by
  unfold foo; rw [hκ.len]
theorem foo2 (c : Fin κ.n) : foo c = κ.n + c.val := foo_eq c
end
#check @foo
#check @foo_eq
def k1 : Ker := ⟨[1,2], 2⟩
instance : k1.OK := ⟨rfl⟩
example (c : Fin 2) : foo (κ := k1) c = 2 + c.val := foo_eq c
