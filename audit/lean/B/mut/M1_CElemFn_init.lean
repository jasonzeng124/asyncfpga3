import Formal.Cells.Prelim

/-!
# Track 5, probe 5a: the C-elements of `cells/rtl/bd_ce.v`, functional and Kleene

Every cell in `bd_ce.v` is ONE `LUT6` whose output `O` is routed back to one of
its own input pins. We take the real `INIT` constants and pin maps from
`bd_ce.v` (copied verbatim below, with the pin each signal sits on) and
evaluate them with `lutB` (binary) and `lutK` (Kleene, hypothesis
**H_KLEENE_LUT** of `Prelim`). Nothing here is a hand-written Boolean
equation of the cell: the equations are *proved* equal to the INIT.

What is modelled, and what is not:
* `next` = the LUT's combinational function with the feedback pin read as an
  independent input `q`. This is the next-state function of the loop.
* The feedback wire is a routed net with a delay interval. Its timing is NOT
  modelled here (probe 5b). The only use made of it is the steady-state
  reading: a stable state of the loop is a value of the feedback net that the
  LUT reproduces at `O`. That reading is the named hypothesis
  `H_FB_SETTLED` (see `Settled`).
* Tied pins (`1'b0` in the RTL) are read as constant `false`. We also prove that
  the INIT is replicated across every tied pin, so the cell's function does not
  depend on how the toolchain ties them (GND route, or INIT rewrite), binary
  or Kleene.

Sections:
1. INITs, pin maps, binary next-state = spec with reset polarity (all 8 cells).
2. Fixed points of the loop: hold vs forced.
3. Kleene: exact closed form of every cell; X containment; single-input-change
   glitch freedom (every pin of every cell); X on the feedback pin
   (logical metastability) and its persistence.

All proofs are `decide` over finite enumerations, checked by the kernel
(no compiled evaluation, no extra axioms: `#print axioms` shows only `propext`).
-/

namespace Formal.Cells.CElemFn
open Formal.Cells

/-! ## Decidability of `∀` over `K3` (local helper; Prelim has none) -/

instance K3.decForall {P : K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
  if h : P .f ∧ P .t ∧ P .x then
    isTrue (fun k => by cases k <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _⟩)

/-! ## 1. INITs from `bd_ce.v` (verbatim) -/

/-- `bd_c2`:      `I0=a I1=b I2=q I3=rst I4=0 I5=0`. -/
def INIT_c2       : Nat := 0x00E800E800E800E9
/-- `bd_c2_set`:  `I0=a I1=b I2=q I3=rst I4=0 I5=0`. -/
def INIT_c2_set   : Nat := 0xFFE8FFE8FFE8FFE8
/-- `bd_c2n`:     `I0=a I1=b I2=q I3=rst I4=0 I5=0`. -/
def INIT_c2n      : Nat := 0x00B200B200B200B2
/-- `bd_c2n_set`: `I0=a I1=b I2=q I3=rst I4=0 I5=0`. -/
def INIT_c2n_set  : Nat := 0xFFB2FFB2FFB2FFB2
/-- `bd_c3`:      `I0=a I1=b I2=c I3=q I4=rst I5=0`. -/
def INIT_c3       : Nat := 0x0000FE800000FE80
/-- `bd_c4`:      `I0=a I1=b I2=c I3=d I4=q I5=rst`. -/
def INIT_c4       : Nat := 0x00000000FFFE8000
/-- `bd_c2_norst`: `I0=a I1=b I2=q I3=0 I4=0 I5=0`. -/
def INIT_c2_norst : Nat := 0xE8E8E8E8E8E8E8E8
/-- `bd_c3_norst`: `I0=a I1=b I2=c I3=q I4=0 I5=0`. -/
def INIT_c3_norst : Nat := 0xFE80FE80FE80FE80

/-! ### Pin maps (the `.I0(..) .. .I5(..)` lists of `bd_ce.v`), binary -/

def c2B       (a b q rst : Bool)     : Bool := lutB INIT_c2       [a, b, q, rst, false, false]
def c2setB    (a b q rst : Bool)     : Bool := lutB INIT_c2_set   [a, b, q, rst, false, false]
def c2nB      (a b q rst : Bool)     : Bool := lutB INIT_c2n      [a, b, q, rst, false, false]
def c2nsetB   (a b q rst : Bool)     : Bool := lutB INIT_c2n_set  [a, b, q, rst, false, false]
def c3B       (a b c q rst : Bool)   : Bool := lutB INIT_c3       [a, b, c, q, rst, false]
def c4B       (a b c d q rst : Bool) : Bool := lutB INIT_c4       [a, b, c, d, q, rst]
def c2norstB  (a b q : Bool)         : Bool := lutB INIT_c2_norst [a, b, q, false, false, false]
def c3norstB  (a b c q : Bool)       : Bool := lutB INIT_c3_norst [a, b, c, q, false, false]

/-! ### Pin maps, Kleene (tied pins read as definite `f`) -/

def c2K       (a b q rst : K3)     : K3 := lutK INIT_c2       [a, b, q, rst, .f, .f]
def c2setK    (a b q rst : K3)     : K3 := lutK INIT_c2_set   [a, b, q, rst, .f, .f]
def c2nK      (a b q rst : K3)     : K3 := lutK INIT_c2n      [a, b, q, rst, .f, .f]
def c2nsetK   (a b q rst : K3)     : K3 := lutK INIT_c2n_set  [a, b, q, rst, .f, .f]
def c3K       (a b c q rst : K3)   : K3 := lutK INIT_c3       [a, b, c, q, rst, .f]
def c4K       (a b c d q rst : K3) : K3 := lutK INIT_c4       [a, b, c, d, q, rst]
def c2norstK  (a b q : K3)         : K3 := lutK INIT_c2_norst [a, b, q, .f, .f, .f]
def c3norstK  (a b c q : K3)       : K3 := lutK INIT_c3_norst [a, b, c, q, .f, .f]

/-! ### The specification: an n-input Muller C-element -/

/-- Binary C-element: all inputs 1 → 1, all inputs 0 → 0, otherwise hold `q`. -/
def cSpec (ins : List Bool) (q : Bool) : Bool :=
  if ins.all id then true else if ins.all (! ·) then false else q

/-- Reset that clears (`bd_c2`, `bd_c2n`, `bd_c3`, `bd_c4`): `~rst . C`. -/
def clr (rst v : Bool) : Bool := !rst && v
/-- Reset that sets (`_set` cells): `rst + C`. -/
def set (rst v : Bool) : Bool := rst || v

/-- The INIT really is a majority for the symmetric 2-input cell
(`bd_ce.v` header: "C(a,b) is exactly majority(a, b, q)"). -/
theorem c2_init_is_majority :
    ∀ a b q : Bool, c2B a b q false = ((a && b) || (a && q) || (b && q)) := by decide

theorem c2_spec : ∀ a b q rst : Bool, c2B a b q rst = clr rst (cSpec [a, b] q) := by decide
theorem c2_set_spec : ∀ a b q rst : Bool, c2setB a b q rst = set rst (cSpec [a, b] q) := by decide
/-- `bd_c2n` is `C(a, ~b)`: the bubble is on pin I1. -/
theorem c2n_spec : ∀ a b q rst : Bool, c2nB a b q rst = clr rst (cSpec [a, !b] q) := by decide
theorem c2n_set_spec : ∀ a b q rst : Bool,
    c2nsetB a b q rst = set rst (cSpec [a, !b] q) := by decide
theorem c3_spec : ∀ a b c q rst : Bool,
    c3B a b c q rst = clr rst (cSpec [a, b, c] q) := by decide
theorem c4_spec : ∀ a b c d q rst : Bool,
    c4B a b c d q rst = clr rst (cSpec [a, b, c, d] q) := by decide
theorem c2_norst_spec : ∀ a b q : Bool, c2norstB a b q = cSpec [a, b] q := by decide
theorem c3_norst_spec : ∀ a b c q : Bool, c3norstB a b c q = cSpec [a, b, c] q := by decide

/-- `bd_c2n` read as the SR latch of its comment: set = a.~b, reset = ~a.b, hold on a tie. -/
theorem c2n_is_sr : ∀ a b q : Bool,
    c2nB a b q false = (if a && !b then true else if !a && b then false else q) := by decide

/-! ### Tied pins are don't-cares (robust to how the toolchain ties `1'b0`) -/

theorem c2_tied_dontcare : ∀ a b q rst u v : Bool,
    lutB INIT_c2 [a, b, q, rst, u, v] = c2B a b q rst := by decide
theorem c2_set_tied_dontcare : ∀ a b q rst u v : Bool,
    lutB INIT_c2_set [a, b, q, rst, u, v] = c2setB a b q rst := by decide
theorem c2n_tied_dontcare : ∀ a b q rst u v : Bool,
    lutB INIT_c2n [a, b, q, rst, u, v] = c2nB a b q rst := by decide
theorem c2n_set_tied_dontcare : ∀ a b q rst u v : Bool,
    lutB INIT_c2n_set [a, b, q, rst, u, v] = c2nsetB a b q rst := by decide
theorem c3_tied_dontcare : ∀ a b c q rst u : Bool,
    lutB INIT_c3 [a, b, c, q, rst, u] = c3B a b c q rst := by decide
theorem c2_norst_tied_dontcare : ∀ a b q u v w : Bool,
    lutB INIT_c2_norst [a, b, q, u, v, w] = c2norstB a b q := by decide
theorem c3_norst_tied_dontcare : ∀ a b c q u v : Bool,
    lutB INIT_c3_norst [a, b, c, q, u, v] = c3norstB a b c q := by decide

/-- Kleene form: even an X on a tied pin (e.g. an undriven tie) does not reach `O`. -/
theorem c2_tied_dontcare_K : ∀ a b q rst u v : K3,
    lutK INIT_c2 [a, b, q, rst, u, v] = c2K a b q rst := by decide
theorem c3_tied_dontcare_K : ∀ a b c q rst u : K3,
    lutK INIT_c3 [a, b, c, q, rst, u] = c3K a b c q rst := by decide

/-! ## 2. Fixed points of the loop: hold vs forced -/

/-- **H_FB_SETTLED.** The feedback net has settled: the value on the LUT's
feedback pin equals the LUT's output for the present inputs. Physically: the
routed wire `O → I(q)` has delivered the last `O` transition and nothing is in
flight on it. Testable on GLS by checking that the feedback pin and `O` agree
once every input has been stable for longer than the loop's max routed delay
(LUT + net, slow corner). -/
structure Settled (next : Bool → Bool) (q : Bool) : Prop where
  H_FB_SETTLED : next q = q

/-! Stable states with reset deasserted: `q` is stable iff the inputs are not
unanimously `!q`. So: unanimous inputs FORCE one state (`q` = the common
value); mixed inputs HOLD (both values are stable: the loop is bistable). -/

theorem c2_fixed_iff : ∀ a b q : Bool,
    c2B a b q false = q ↔ ¬ (a = !q ∧ b = !q) := by decide
theorem c2_set_fixed_iff : ∀ a b q : Bool,
    c2setB a b q false = q ↔ ¬ (a = !q ∧ b = !q) := by decide
theorem c2n_fixed_iff : ∀ a b q : Bool,
    c2nB a b q false = q ↔ ¬ (a = !q ∧ b = q) := by decide
theorem c2n_set_fixed_iff : ∀ a b q : Bool,
    c2nsetB a b q false = q ↔ ¬ (a = !q ∧ b = q) := by decide
theorem c3_fixed_iff : ∀ a b c q : Bool,
    c3B a b c q false = q ↔ ¬ (a = !q ∧ b = !q ∧ c = !q) := by decide
theorem c4_fixed_iff : ∀ a b c d q : Bool,
    c4B a b c d q false = q ↔ ¬ (a = !q ∧ b = !q ∧ c = !q ∧ d = !q) := by decide
theorem c2_norst_fixed_iff : ∀ a b q : Bool,
    c2norstB a b q = q ↔ ¬ (a = !q ∧ b = !q) := by decide
theorem c3_norst_fixed_iff : ∀ a b c q : Bool,
    c3norstB a b c q = q ↔ ¬ (a = !q ∧ b = !q ∧ c = !q) := by decide

/-- Forced: unanimous inputs fix the next state whatever `q` is. -/
theorem c2_forced : ∀ a q : Bool, c2B a a q false = a := by decide
theorem c2n_forced : ∀ a q : Bool, c2nB a (!a) q false = a := by decide
theorem c3_forced : ∀ a q : Bool, c3B a a a q false = a := by decide
theorem c4_forced : ∀ a q : Bool, c4B a a a a q false = a := by decide
/-- Hold: with the inputs not unanimous the next state is `q` itself. -/
theorem c2_hold : ∀ a q : Bool, c2B a (!a) q false = q := by decide
theorem c2n_hold : ∀ a q : Bool, c2nB a a q false = q := by decide
theorem c3_hold : ∀ a b c q : Bool,
    ¬ (a = b ∧ b = c) → c3B a b c q false = q := by decide
theorem c4_hold : ∀ a b c d q : Bool,
    ¬ (a = b ∧ b = c ∧ c = d) → c4B a b c d q false = q := by decide
/-- Reset asserted forces the reset value, whatever the inputs and `q`. -/
theorem c2_rst_forced : ∀ a b q : Bool, c2B a b q true = false := by decide
theorem c2_set_rst_forced : ∀ a b q : Bool, c2setB a b q true = true := by decide
theorem c2n_rst_forced : ∀ a b q : Bool, c2nB a b q true = false := by decide
theorem c2n_set_rst_forced : ∀ a b q : Bool, c2nsetB a b q true = true := by decide
theorem c3_rst_forced : ∀ a b c q : Bool, c3B a b c q true = false := by decide
theorem c4_rst_forced : ∀ a b c d q : Bool, c4B a b c d q true = false := by decide

/-- Under H_FB_SETTLED, a settled `bd_c2` with unanimous inputs shows that value. -/
theorem c2_settled_unanimous (a q : Bool)
    (h : Settled (fun q => c2B a a q false) q) : q = a := by
  have hs := h.H_FB_SETTLED
  clear h; revert hs; revert a q; decide

/-- Under H_FB_SETTLED, a settled `bd_c4` with unanimous inputs shows that value. -/
theorem c4_settled_unanimous (a q : Bool)
    (h : Settled (fun q => c4B a a a a q false) q) : q = a := by
  have hs := h.H_FB_SETTLED
  clear h; revert hs; revert a q; decide

/-- Under H_FB_SETTLED with rst deasserted, `bd_c2`'s settled value is one of
its stable states, and any value is settled when the inputs differ. -/
theorem c2_settled_iff (a b q : Bool) :
    Settled (fun q => c2B a b q false) q ↔ ¬ (a = !q ∧ b = !q) :=
  ⟨fun h => (c2_fixed_iff a b q).1 h.H_FB_SETTLED,
   fun h => ⟨(c2_fixed_iff a b q).2 h⟩⟩

/-- Number of stable states of the loop (out of {0,1}). -/
def nStable (next : Bool → Bool) : Nat :=
  [false, true].countP (fun q => next q == q)

theorem c2_nStable : ∀ a b : Bool,
    nStable (fun q => c2B a b q false) = (if a = b then 1 else 2) := by decide
theorem c4_nStable : ∀ a b c d : Bool,
    nStable (fun q => c4B a b c d q false) = (if a = b ∧ b = c ∧ c = d then 1 else 2) := by
  decide
theorem c2_nStable_rst : ∀ a b : Bool, nStable (fun q => c2B a b q true) = 1 := by decide

/-! ## 3. Kleene (H_KLEENE_LUT) -/

/-- Kleene AND / OR (strong Kleene). -/
def kand : K3 → K3 → K3
  | .f, _ => .f
  | _, .f => .f
  | .t, .t => .t
  | _, _ => .x
def kor : K3 → K3 → K3
  | .t, _ => .t
  | _, .t => .t
  | .f, .f => .f
  | _, _ => .x

/-- Kleene C-element, closed form: all inputs `t` → `t`; all `f` → `f`;
otherwise `q` survives iff `q` is definite and some input equals `q` (that
input pins the hold: no completion can make the inputs unanimous against
`q`); else `x`. -/
def cK (ins : List K3) (q : K3) : K3 :=
  if ins.all (· == .t) then .t
  else if ins.all (· == .f) then .f
  else if q != .x && ins.contains q then q
  else .x

/-! ### Exact closed forms of every cell's Kleene LUT (all 3^n input vectors) -/

theorem c2K_closed : ∀ a b q rst : K3,
    c2K a b q rst = kand (K3.not rst) (cK [a, b] q) := by decide
theorem c2setK_closed : ∀ a b q rst : K3,
    c2setK a b q rst = kor rst (cK [a, b] q) := by decide
theorem c2nK_closed : ∀ a b q rst : K3,
    c2nK a b q rst = kand (K3.not rst) (cK [a, K3.not b] q) := by decide
theorem c2nsetK_closed : ∀ a b q rst : K3,
    c2nsetK a b q rst = kor rst (cK [a, K3.not b] q) := by decide
theorem c3K_closed : ∀ a b c q rst : K3,
    c3K a b c q rst = kand (K3.not rst) (cK [a, b, c] q) := by decide
theorem c4K_closed : ∀ a b c d q rst : K3,
    c4K a b c d q rst = kand (K3.not rst) (cK [a, b, c, d] q) := by decide
theorem c2norstK_closed : ∀ a b q : K3, c2norstK a b q = cK [a, b] q := by decide
theorem c3norstK_closed : ∀ a b c q : K3, c3norstK a b c q = cK [a, b, c] q := by decide

/-- The Kleene cell agrees with the binary cell on definite inputs. -/
theorem c2K_ofBool : ∀ a b q rst : Bool,
    c2K (.ofBool a) (.ofBool b) (.ofBool q) (.ofBool rst) = .ofBool (c2B a b q rst) := by
  decide
theorem c4K_ofBool : ∀ a b c d q rst : Bool,
    c4K (.ofBool a) (.ofBool b) (.ofBool c) (.ofBool d) (.ofBool q) (.ofBool rst)
      = .ofBool (c4B a b c d q rst) := by decide

/-! ### Which X patterns keep `q` definite (rst deasserted) -/

/-- a = b = 1 drives 1 whatever `q` (even `q = x`); likewise 0. -/
theorem c2K_both_one : ∀ q : K3, c2K .t .t q .f = .t := by decide
theorem c2K_both_zero : ∀ q : K3, c2K .f .f q .f = .f := by decide

/-- X on `b` while `a` agrees with the held `q`: `q` is undisturbed. -/
theorem c2K_x_contained : ∀ q : Bool, c2K (.ofBool q) .x (.ofBool q) .f = .ofBool q := by
  decide
/-- X on `b` while `a` disagrees with the held `q`: the output is X (b may be
the edge that completes the rendezvous). -/
theorem c2K_x_escapes : ∀ q : Bool, c2K (.ofBool (!q)) .x (.ofBool q) .f = .x := by decide
/-- Exactly: with X on `b`, the output is definite iff `q` is definite and `a = q`. -/
theorem c2K_xb_definite_iff : ∀ a q : K3,
    c2K a .x q .f ≠ .x ↔ (q ≠ .x ∧ a = q) := by decide
theorem c2K_xa_definite_iff : ∀ b q : K3,
    c2K .x b q .f ≠ .x ↔ (q ≠ .x ∧ b = q) := by decide
/-- `bd_c2n`: the bubble flips which value of `b` pins the hold. -/
theorem c2nK_xa_definite_iff : ∀ b q : K3,
    c2nK .x b q .f ≠ .x ↔ (q ≠ .x ∧ K3.not b = q) := by decide
/-- `bd_c4`: with X on `d`, `q` stays definite iff it is definite and one of
`a, b, c` equals it. (If `a, b, c` all equal `!q`, the X on `d` may be the
edge that completes the rendezvous, so the output is X.) -/
theorem c4K_xd_definite_iff : ∀ a b c q : K3,
    c4K a b c .x q .f ≠ .x ↔ (q ≠ .x ∧ (a = q ∨ b = q ∨ c = q)) := by decide

/-! ### Single input change with unchanged output is glitch-free

For every cell and every one of its six pins (inputs, feedback, rst, and the
tied pins), and every binary vector `v`: X on pin `i` (the input in transit)
gives exactly the join of the two endpoint values. Hence if the two endpoints
agree, the output during the change is that same definite value (no glitch),
and if they differ it is X (a real transition, whose timing is not decided
by the logic). -/

def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).map (false :: ·) ++ (allVecs n).map (true :: ·)

/-- The single-pin-change property of a 6-input INIT. -/
def SingleX (init : Nat) : Prop :=
  ∀ v ∈ allVecs 6, ∀ i, i < 6 →
    lutK init ((v.map K3.ofBool).set i .x)
      = K3.join (.ofBool (lutB init v)) (.ofBool (lutB init (v.set i (!v.getD i false))))

theorem c2_singleX       : SingleX INIT_c2       := by unfold SingleX; decide
theorem c2_set_singleX   : SingleX INIT_c2_set   := by unfold SingleX; decide
theorem c2n_singleX      : SingleX INIT_c2n      := by unfold SingleX; decide
theorem c2n_set_singleX  : SingleX INIT_c2n_set  := by unfold SingleX; decide
theorem c3_singleX       : SingleX INIT_c3       := by unfold SingleX; decide
theorem c4_singleX       : SingleX INIT_c4       := by unfold SingleX; decide
theorem c2_norst_singleX : SingleX INIT_c2_norst := by unfold SingleX; decide
theorem c3_norst_singleX : SingleX INIT_c3_norst := by unfold SingleX; decide

/-- Glitch freedom from `SingleX`: endpoints equal ⇒ the transit value is that value. -/
theorem glitchFree_of_singleX {init : Nat} (h : SingleX init) {v : List Bool}
    (hv : v ∈ allVecs 6) {i : Nat} (hi : i < 6)
    (heq : lutB init (v.set i (!v.getD i false)) = lutB init v) :
    lutK init ((v.map K3.ofBool).set i .x) = .ofBool (lutB init v) := by
  rw [h v hv i hi, heq]; simp [K3.join]

/-- The same, stated on `bd_c2`'s named pins: input `a` changes, `b`, `q`, `rst`
steady; if the C-element's next value is the same at both endpoints, the
value during the change (a = X) is that definite value. -/
theorem c2_glitchfree_a : ∀ a b q rst : Bool,
    c2B (!a) b q rst = c2B a b q rst →
    c2K .x (.ofBool b) (.ofBool q) (.ofBool rst) = .ofBool (c2B a b q rst) := by decide
theorem c2_glitchfree_b : ∀ a b q rst : Bool,
    c2B a (!b) q rst = c2B a b q rst →
    c2K (.ofBool a) .x (.ofBool q) (.ofBool rst) = .ofBool (c2B a b q rst) := by decide
/-- Reset released (or asserted) while the cell's value would not change: no glitch. -/
theorem c2_glitchfree_rst : ∀ a b q rst : Bool,
    c2B a b q (!rst) = c2B a b q rst →
    c2K (.ofBool a) (.ofBool b) (.ofBool q) .x = .ofBool (c2B a b q rst) := by decide
theorem c4_glitchfree_d : ∀ a b c d q rst : Bool,
    c4B a b c (!d) q rst = c4B a b c d q rst →
    c4K (.ofBool a) (.ofBool b) (.ofBool c) .x (.ofBool q) (.ofBool rst)
      = .ofBool (c4B a b c d q rst) := by decide

/-! ### X on the feedback pin: logical metastability -/

/-- `bd_c2` restores a definite value from `q = X` iff `a = b` (definite). -/
theorem c2K_meta_resolve : ∀ a b : K3,
    c2K a b .x .f ≠ .x ↔ (a = b ∧ a ≠ .x) := by decide
theorem c2setK_meta_resolve : ∀ a b : K3,
    c2setK a b .x .f ≠ .x ↔ (a = b ∧ a ≠ .x) := by decide
/-- `bd_c2n` restores iff `a = ~b` (definite): set or reset asserted, not a tie. -/
theorem c2nK_meta_resolve : ∀ a b : K3,
    c2nK a b .x .f ≠ .x ↔ (a = K3.not b ∧ a ≠ .x) := by decide
theorem c2nsetK_meta_resolve : ∀ a b : K3,
    c2nsetK a b .x .f ≠ .x ↔ (a = K3.not b ∧ a ≠ .x) := by decide
theorem c3K_meta_resolve : ∀ a b c : K3,
    c3K a b c .x .f ≠ .x ↔ (a = b ∧ b = c ∧ a ≠ .x) := by decide
theorem c4K_meta_resolve : ∀ a b c d : K3,
    c4K a b c d .x .f ≠ .x ↔ (a = b ∧ b = c ∧ c = d ∧ a ≠ .x) := by decide
theorem c2norstK_meta_resolve : ∀ a b : K3,
    c2norstK a b .x ≠ .x ↔ (a = b ∧ a ≠ .x) := by decide
theorem c3norstK_meta_resolve : ∀ a b c : K3,
    c3norstK a b c .x ≠ .x ↔ (a = b ∧ b = c ∧ a ≠ .x) := by decide
/-- When it resolves, it resolves to the common input value. -/
theorem c2K_meta_resolves_to : ∀ a : Bool, c2K (.ofBool a) (.ofBool a) .x .f = .ofBool a := by
  decide
/-- A definite reset clears an X state (and the `_set` cell sets it); an X reset does not. -/
theorem c2K_rst_clears_x : ∀ a b : K3, c2K a b .x .t = .f := by decide
theorem c2setK_rst_sets_x : ∀ a b : K3, c2setK a b .x .t = .t := by decide
theorem c4K_rst_clears_x : ∀ a b c d : K3, c4K a b c d .x .t = .f := by decide
/-- An X reset on an X state leaves X unless both inputs are `f` (then the
C-element and the reset agree on `f`). -/
theorem c2K_xrst_keeps_x : ∀ a b : K3, ¬ (a = .f ∧ b = .f) → c2K a b .x .x = .x := by decide

/-- Iterating the Kleene loop with steady inputs. -/
def kIter (next : K3 → K3) : Nat → K3 → K3
  | 0, q => q
  | n + 1, q => kIter next n (next q)

theorem kIter_fixed {next : K3 → K3} {q : K3} (h : next q = q) : ∀ n, kIter next n q = q
  | 0 => rfl
  | n + 1 => by simp only [kIter, h]; exact kIter_fixed h n

/-- **X persists in hold mode.** With the inputs not unanimous (here, `a ≠ b`
or one of them X) and rst deasserted, X is a fixed point of the Kleene loop:
the three-valued model never resolves it. Resolution of a held X needs the
analog model (track 7c); Kleene logic only says *when* the logic forces a
value (unanimous inputs, or reset). -/
theorem c2K_x_persists (a b : K3) (h : ¬ (a = b ∧ a ≠ .x)) :
    ∀ n, kIter (fun q => c2K a b q .f) n .x = .x := by
  apply kIter_fixed
  have := (c2K_meta_resolve a b)
  by_cases hx : c2K a b .x .f = .x
  · exact hx
  · exact absurd (this.1 hx) h

/-- With unanimous definite inputs, one step of the loop leaves X for good. -/
theorem c2K_x_resolves (a : Bool) :
    ∀ n, kIter (fun q => c2K (.ofBool a) (.ofBool a) q .f) (n + 1) .x = .ofBool a := by
  intro n
  simp only [kIter]
  rw [c2K_meta_resolves_to]
  apply kIter_fixed
  revert a; decide

/-- In hold mode the Kleene loop has exactly three fixed points: `f`, `t`, `x`. -/
theorem c2K_hold_fixed : ∀ q : K3, c2K .t .f q .f = q := by decide

end Formal.Cells.CElemFn
