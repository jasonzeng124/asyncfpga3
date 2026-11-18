/-!
# bd_mux's join LUTs with the select fixed are C-elements (shard C, 2026-11-18)

**Problem, plainly.** `StageNetTree` covers C-elements and buffers between stages; a mux's
select join `j1 = C(y_req, ctl_req · s)` has an AND inside. This file reads the two join LUTs of
`cells/rtl/bd_mux.v` straight from their INITs (`uj0`: `64'h0000_AE08_0000_AE08`, pins I0 x_req,
I1 ctl_req, I2 s, I3 j0, I4 rst; `uj1`: `64'h0000_EA80_0000_EA80`, pins I0 y_req, I1 ctl_req, I2 s,
I3 j1, I4 rst) and shows, by evaluating the INIT bits:
* with `rst = 0` and the select routing to that input (`s = 1` for `uj1`, `s = 0` for `uj0`), the
  LUT is the two-input C-element `C(req, ctl_req)` with state `j` (`uj1_sel`, `uj0_sel`);
* with the select routing away, it is `C(req, 0)`: it can only fall (`uj1_unsel`, `uj0_unsel`);
* `rst = 1` forces 0.
So in a fixed mode the selected input's join is a C-element of `StageNetTree`'s kind, and the
unselected one is held at 0 once empty. What this does NOT cover: a select that changes (the
x_ack race in FOR-RESEARCH C53 / C56), timing, glitches inside the LUT, X.
-/

namespace Formal.Net.StageNet.Mux

/-- A LUT6 output: bit `I0 + 2 I1 + 4 I2 + 8 I3 + 16 I4 + 32 I5` of `init`. -/
def lut6 (init : Nat) (i0 i1 i2 i3 i4 i5 : Bool) : Bool :=
  Nat.testBit init (i0.toNat + 2 * i1.toNat + 4 * i2.toNat + 8 * i3.toNat + 16 * i4.toNat + 32 * i5.toNat)

def initJ0 : Nat := 0x0000AE080000AE08
def initJ1 : Nat := 0x0000EA800000EA80

/-- The two-input C-element with state `q`. -/
def celem (a b q : Bool) : Bool := if a == b then a else q

theorem uj1_sel : ∀ y c q : Bool, lut6 initJ1 y c true q false false = celem y c q := by decide
theorem uj1_unsel : ∀ y c q : Bool, lut6 initJ1 y c false q false false = celem y false q := by decide
theorem uj0_sel : ∀ x c q : Bool, lut6 initJ0 x c false q false false = celem x c q := by decide
theorem uj0_unsel : ∀ x c q : Bool, lut6 initJ0 x c true q false false = celem x false q := by decide
theorem uj1_rst : ∀ y c s q : Bool, lut6 initJ1 y c s q true false = false := by decide
theorem uj0_rst : ∀ x c s q : Bool, lut6 initJ0 x c s q true false = false := by decide

end Formal.Net.StageNet.Mux
