import Formal.Net.RingCheck

/-!
# Certificate form of the ring checker, for kernel `decide` (probe C-9b)

`RingCheck.check` is fine under `#eval` but the kernel evaluates it lazily
and re-computes the shared table on every read (an attempt at
`decide +kernel` on collatz's 45-node graph was killed by the OOM killer
after 2 min).  For proofs about real bdc graphs we therefore check a
*certificate*: one table `d_s : List Nat` per source `s` (an untrusted
Python script supplies it) satisfying, for every edge `e`,
`d_s[e.dst] ≤ cand k s d_s e`, and `k ≤ d_s[s]`.

* `certCheck_sound`:   a valid certificate proves `AllCyclesGe g k`.
* `certCheck_complete`: whenever `AllCyclesGe g k` holds, the checker's own
  fixpoint tables (`makeCert`) are a valid certificate, so no true instance
  is ever rejected for want of a certificate.

The kernel only does table lookups on literals: cost `O(n · |E| · n)`.
-/

namespace Formal.Net.RingCheck

def lval (k : Nat) (d : List Nat) (v : Nat) : Nat := d.getD v k

def lcand (k s : Nat) (d : List Nat) (e : Edge) : Nat :=
  if e.src = s then min k e.w else min k (lval k d e.src + e.w)

def fixOk (k s : Nat) (g : Graph) (d : List Nat) : Bool :=
  g.all (fun e => decide (lval k d e.dst ≤ lcand k s d e)) && decide (k ≤ lval k d s)

def certCheck (g : Graph) (k : Nat) (cert : List (List Nat)) : Bool :=
  (List.range (numNodes g)).all (fun s => fixOk k s g (cert.getD s []))

/-- Any table closed under the relaxation bounds every walk from `s` below. -/
theorem table_le_walk {k s : Nat} {g : Graph} {f : Nat → Nat}
    (key : ∀ e ∈ g, f e.dst ≤ (if e.src = s then min k e.w else min k (f e.src + e.w))) :
    ∀ v c, Walk g s v c → f v ≤ c := by
  intro v c hw
  induction hw with
  | @edge e he hsrc => have := key e he; rw [ite_eq_left hsrc] at this; omega
  | @snoc c e _ he ih => have := key e he; split at this <;> omega

theorem fixOk_sound {k s : Nat} {g : Graph} {d : List Nat} (h : fixOk k s g d = true) :
    ∀ c, Walk g s s c → k ≤ c := by
  simp only [fixOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro c hw
  have := table_le_walk (k := k) (f := lval k d) (fun e he => h.1 e he) s c hw
  omega

theorem certCheck_sound {g : Graph} {k : Nat} {cert : List (List Nat)}
    (h : certCheck g k cert = true) : AllCyclesGe g k := by
  intro s c hw
  unfold certCheck at h; rw [List.all_eq_true] at h
  exact fixOk_sound (h s (List.mem_range.mpr (walk_src_lt hw))) c hw

/-- The checker's own fixpoint tables, as a certificate. -/
def makeCert (g : Graph) (k : Nat) : List (List Nat) :=
  (List.range (numNodes g)).map fun s =>
    match iter k s g (fuel k g) (init k g) with
    | some d => d.toList
    | none => []

theorem lval_toList (k : Nat) (d : Array Nat) (v : Nat) : lval k d.toList v = val k d v := by
  unfold lval val
  split
  · simp [List.getD_eq_getElem?_getD, *]
  · rename_i hv
    have : d.toList[v]? = none := List.getElem?_eq_none (by simp; omega)
    simp [List.getD_eq_getElem?_getD, this]

theorem certCheck_complete {g : Graph} {k : Nat} (h : AllCyclesGe g k) :
    certCheck g k (makeCert g k) = true := by
  unfold certCheck; rw [List.all_eq_true]
  intro s hs
  have hs' := List.mem_range.mp hs
  have hget : (makeCert g k).getD s [] =
      (match iter k s g (fuel k g) (init k g) with | some d => d.toList | none => []) := by
    simp [makeCert, List.getD_eq_getElem?_getD, hs']
  rw [hget]
  obtain ⟨d, hd, hinv, hfix⟩ :=
    iter_spec k s g (fuel k g) (init k g) (inv_init k s g)
      (by have := pot_le (inv_init k s g); unfold fuel; omega)
  rw [hd]
  simp only [fixOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, lval_toList]
  constructor
  · intro e he
    have := foldl_relax_cand k s d g d e he (by rw [hinv.1]; exact (lt_numNodes he).2)
    rw [← step, hfix] at this
    unfold lcand cand at *; simp only [lval_toList]; exact this
  · apply Nat.le_of_not_lt; intro hlt
    obtain ⟨c, hw, hc⟩ := (hinv.2 s).2 hlt
    have := h s c hw; omega

/-! ### Chunked form: one kernel `decide` per block of sources

Large graphs (isprime, gcd) exhaust memory when the whole certificate is
checked in one `decide`; the generated files check `certCheckFrom` on
`List.range' a m` blocks and glue them with `certCheckFrom_append`. -/

def certCheckFrom (g : Graph) (k : Nat) (cert : List (List Nat)) (ss : List Nat) : Bool :=
  ss.all (fun s => fixOk k s g (cert.getD s []))

theorem certCheckFrom_append {g : Graph} {k : Nat} {cert : List (List Nat)} {a m b : Nat}
    (h₁ : certCheckFrom g k cert (List.range' a m) = true)
    (h₂ : certCheckFrom g k cert (List.range' (a + m) b) = true) :
    certCheckFrom g k cert (List.range' a (m + b)) = true := by
  have e := @List.range'_append a m b 1
  rw [Nat.one_mul] at e
  rw [← e]; unfold certCheckFrom at *; rw [List.all_append, h₁, h₂]; rfl

theorem certCheckFrom_sound {g : Graph} {k : Nat} {cert : List (List Nat)} {N : Nat}
    (hn : numNodes g = N) (h : certCheckFrom g k cert (List.range' 0 N) = true) :
    AllCyclesGe g k := by
  intro s c hw
  unfold certCheckFrom at h; rw [List.all_eq_true] at h
  have hs := walk_src_lt hw
  exact fixOk_sound (h s (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)) c hw

theorem allCyclesGe_iff_cert (g : Graph) (k : Nat) :
    AllCyclesGe g k ↔ ∃ cert, certCheck g k cert = true :=
  ⟨fun h => ⟨_, certCheck_complete h⟩, fun ⟨_, h⟩ => certCheck_sound h⟩

end Formal.Net.RingCheck
