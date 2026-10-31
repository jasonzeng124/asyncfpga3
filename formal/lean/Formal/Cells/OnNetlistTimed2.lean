import Formal.Core.LutList
import Formal.Cells.CElemTiming
import Formal.Cells.Latch
import Formal.Cells.OnNetlistTimed
import Formal.Cells.Bundling
import Formal.Cells.LinkTimed
import Formal.Net.Fasm.Basic
import Formal.Net.FasmLink.S1
import Formal.Net.FasmLink.S2
import Formal.Net.FasmLink.S3
import Formal.Net.FasmLink.S4
open Formal.Core.LutList

/-!
# Probe Bt2: finishing the timed bridge on the routed bits (link_arb, 4 seeds)

Shard B x shard C. Continues probe Bt (`OnNetlistTimed`). Same physical side:
C-11b's `Behaves` on C-11c's netlists read back from the four routed
`link_arb` bitstreams (`Formal.Net.FasmLink.S1..S4`, nextpnr sha256
9c732bc6303458df, `toolchain.sh` ok as stamped by `fasm2lean2/check.sh`).
No re-route; every delay is C's generated `pinDelay` (rfl-linked) or the
prjxray-db CLB SDF LUT envelope (O6 `[45, 124]`, O5 `[42, 157]` ps).

1. Latch bits q1 (O6 of the pair LUT6_2) and q2 (the odd LUT6) get B's
   `Latch.holds_value` on every seed (`latch_q1_s*`, `latch_q2_s*`), through
   the generic `latch_bit_net`.
2. `c2_reset` on the C node, every seed (`c_reset_s*`).
3. Rule H (`E ≤ A + R`), windowed form of `Latch.link_latch_holds`, for every
   seed and every bit (`rule_h_q{0,1,2}_s*`): `E` = the routed enable-pin
   window max (C node O6 -> latch enable pin, `pinDelay`), `R` = the routed
   data-pin window min (port -> latch data pin, `pinDelay`), `A` = a NAMED
   hypothesis (node fall -> the sender changes its data port: the ack_in
   output route, IOB, off-chip sender), whose required lower bound `E - R` is
   the per-seed, per-bit number in the theorem.

Core Lean only; no native evaluation.
-/

namespace Formal.Cells.OnNetlistTimed2
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm Formal.Cells.OnNetlistTimed

/-! ## 1. Generic: a physical latch bit (any LUT, any output) -/

section generic
variable {N : PNet} {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}

/-- **Bridge (latch family, any bit).** LUT `i` output `o` whose physical
function on its physical pins is `bmux (pin ie) (pin id) (pin iq)` (`hfn`,
decided per seed) and whose pin `iq` is routed from its own output `o` gives
B's `Latch.holds_value` (via `latch_holds_bits`): loop bound `dhi + whi`. -/
theorem latch_bit_net (h : Behaves N ins out pin dl dw) {i : Nat} {L : PLut}
    (hL : N.luts[i]? = some L) (o : LOut) {ie id iq : Nat}
    (hq : L.pins[iq]? = some (.lut i o))
    (hfn : ∀ t, L.fn o ((List.range 6).map (fun k => pin i k t)) =
      Latch.bmux (pin i ie t) (pin i id t) (pin i iq t))
    {dlo dhi wlo whi : Nat} (H_DL : dl i = (dlo, dhi)) (H_DW : dw i iq = (wlo, whi))
    (hpos : 1 ≤ dlo + wlo) (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin i ie t = false → s + (dhi + whi) ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin i ie t = true → pin i id t = v) :
    ∀ t, s + dhi ≤ t → t ≤ T + dlo → out i o t = v := by
  have hl := h.H_LUT i L o hL
  have hf := h.H_ROUTE i L iq (.lut i o) hL hq (by intro v hv; cases hv)
  have e : (fun t => L.fn o ((List.range 6).map (fun k => pin i k t))) =
      (fun t => Latch.bmux (pin i ie t) (pin i id t) (pin i iq t)) := funext hfn
  rw [e, H_DL] at hl; rw [H_DW] at hf
  exact (latch_holds_bits (d1 := pin i id) (p1 := pin i id) hl hf hpos v s T
    H_EN_OPEN H_DATA).2

/-- **Rule H on the bits (windowed `Latch.link_latch_holds`).** As
`latch_bit_net`, with the enable pin `ie` routed from source `se` (the C node)
with window `[elo, ehi]` and the data pin `id` routed from `sd` (the sender's
data port) with window `[rlo, rhi]`.
* `H_NODE_LOW`: the node is low on `[tc, T]` (it fell at `tc`);
* `H_SENDER_HOLD`: the sender keeps its data at `v` from `s0` until `A` ticks
  after `tc` (it releases only once it has seen the fall: `A` = node -> ack
  port route + IOB + sender reaction);
* `H_SETUP_PORT`: the data was launched at least `rhi` before `s`;
* `H_RULE_H : ehi ≤ A + rlo` (rule H: latest enable fall at the pin no later
  than the earliest arrival of released data at the pin).
Then the bit holds `v` on `[s + dhi, T + dlo]`. Unlike `Latch.link_latch_holds`
the enable need only be low up to `T` (it rises again for the next token). -/
theorem latch_rule_h_net (h : Behaves N ins out pin dl dw) {i : Nat} {L : PLut}
    (hL : N.luts[i]? = some L) (o : LOut) {ie id iq : Nat}
    (hq : L.pins[iq]? = some (.lut i o))
    (hfn : ∀ t, L.fn o ((List.range 6).map (fun k => pin i k t)) =
      Latch.bmux (pin i ie t) (pin i id t) (pin i iq t))
    {se sd : Src} (hse : L.pins[ie]? = some se) (hse' : ∀ v, se ≠ .const v)
    (hsd : L.pins[id]? = some sd) (hsd' : ∀ v, sd ≠ .const v)
    {dlo dhi wlo whi elo ehi rlo rhi : Nat} (H_DL : dl i = (dlo, dhi))
    (H_DW : dw i iq = (wlo, whi)) (H_DWE : dw i ie = (elo, ehi)) (H_DWD : dw i id = (rlo, rhi))
    (hpos : 1 ≤ dlo + wlo) (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin i ie t = false → s + (dhi + whi) ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → se.trace ins out t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → sd.trace ins out t = v)
    (H_SETUP_PORT : s0 + rhi ≤ s)
    (H_RULE_H : ehi ≤ A + rlo) :
    ∀ t, s + dhi ≤ t → t ≤ T + dlo → out i o t = v := by
  have Re := h.H_ROUTE i L ie se hL hse hse'
  have Rd := h.H_ROUTE i L id sd hL hsd hsd'
  rw [H_DWE] at Re; rw [H_DWD] at Rd
  apply latch_bit_net h hL o hq hfn H_DL H_DW hpos v s T H_EN_OPEN
  intro t h1 h2 hen
  have hlt : t + 1 ≤ tc + ehi := by
    refine Nat.lt_of_not_le (fun hge => ?_)
    obtain ⟨u, hu1, hu2, e⟩ := Re t (by simp only at *; omega)
    rw [H_NODE_LOW u (by simp only at *; omega) (by simp only at *; omega)] at e
    rw [hen] at e; cases e
  obtain ⟨u, hu1, hu2, e⟩ := Rd t (by simp only at *; omega)
  rw [e]; exact H_SENDER_HOLD u (by simp only at *; omega) (by simp only at *; omega)

end generic

/-! ## 2. `c2_reset` for the C node `C(a, ~b)` -/

theorem c2n_reset {a b rst O qp : Trace} {dlo dhi wlo whi : Nat}
    (L : Loop INIT_c2 a (fun t => !b t) rst O qp dlo dhi wlo whi) (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dhi + whi) → rst s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → a s = false ∨ b s = true) :
    (∀ t, t0 + dhi ≤ t → t ≤ t2 + dlo → O t = false) ∧
    (∀ t, t0 + (dhi + whi) ≤ t → t ≤ t2 + (dlo + wlo) → qp t = false) :=
  c2_reset L t0 t2 H_RST_PULSE (fun s h1 h2 => (H_RELEASE s h1 h2).imp id (fun hb => by
    show (!b s) = false; rw [hb]; rfl))

section seeds
variable {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}

/-- **Reset on the bits.** `rst = 1` at the C node's rst pin for `Dmax`
(569 / 838 / 960 / 590 ps), then req/ack never both at the set value: the
routed node reads 0 from 124 ps on, its feedback pin from `Dmax` on. -/
theorem c_reset_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S1.pinDelay[0]![3]!)
    (t0 t2 : Nat) (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + 569 → pin 0 0 s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 1 s = false ∨ pin 0 2 s = true) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = false) ∧
    (∀ t, t0 + 569 ≤ t → t ≤ t2 + 170 → pin 0 3 t = false) :=
  c2n_reset (cloop_s1 h H_DL H_DW) t0 t2 H_RST_PULSE H_RELEASE

theorem c_reset_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 0 = Formal.Net.FasmLink.S2.pinDelay[0]![0]!)
    (t0 t2 : Nat) (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + 838 → pin 0 4 s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 2 s = false ∨ pin 0 1 s = true) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = false) ∧
    (∀ t, t0 + 838 ≤ t → t ≤ t2 + 256 → pin 0 0 t = false) :=
  c2n_reset (cloop_s2 h H_DL H_DW) t0 t2 H_RST_PULSE H_RELEASE

theorem c_reset_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S3.pinDelay[0]![3]!)
    (t0 t2 : Nat) (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + 960 → pin 0 0 s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 4 s = false ∨ pin 0 1 s = true) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = false) ∧
    (∀ t, t0 + 960 ≤ t → t ≤ t2 + 251 → pin 0 3 t = false) :=
  c2n_reset (cloop_s3 h H_DL H_DW) t0 t2 H_RST_PULSE H_RELEASE

theorem c_reset_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S4.pinDelay[0]![3]!)
    (t0 t2 : Nat) (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + 590 → pin 0 0 s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 4 s = false ∨ pin 0 2 s = true) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = false) ∧
    (∀ t, t0 + 590 ≤ t → t ≤ t2 + 169 → pin 0 3 t = false) :=
  c2n_reset (cloop_s4 h H_DL H_DW) t0 t2 H_RST_PULSE H_RELEASE

/-! ## 3. Physical functions of q1 (pair O6) and q2 (odd LUT), decided

Pins (A1..A6), from C's `rho[1]` = `[q0, q1, q2]`:
* S1: pair LUT 1 `[q1, q0, en, d1, d0, 1]`; odd LUT 2 `[d2, 0, en, 1, q2, 0]`
* S2: pair LUT 1 `[d1, q0, d0, en, q1, 1]`; odd LUT 2 `[en, q2, 0, 1, d2, 0]`
* S3: pair LUT 2 `[q1, d0, d1, en, q0, 1]`; odd LUT 1 `[0, en, 1, d2, q2, 0]`
* S4: pair LUT 1 `[q1, en, d1, d0, q0, 1]`; odd LUT 2 `[q2, d2, en, 0, 1, 0]`
`d_j` = port `2 + j`, `en` = LUT 0 O6. -/

theorem q12_pins :
    Formal.Net.FasmLink.S1.lut2.pins = [.port 4, .const false, .lut 0 .o6, .const true, .lut 2 .o6, .const false] ∧
    Formal.Net.FasmLink.S2.lut2.pins = [.lut 0 .o6, .lut 2 .o6, .const false, .const true, .port 4, .const false] ∧
    Formal.Net.FasmLink.S3.lut1.pins = [.const false, .lut 0 .o6, .const true, .port 4, .lut 1 .o6, .const false] ∧
    Formal.Net.FasmLink.S4.lut2.pins = [.lut 2 .o6, .port 4, .lut 0 .o6, .const false, .const true, .const false] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem l6_fn_s1 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S1.lut1.fn .o6 [x0, x1, x2, x3, x4, true] = Latch.bmux x2 x3 x0 := by decide
theorem l6_fn_s2 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S2.lut1.fn .o6 [x0, x1, x2, x3, x4, true] = Latch.bmux x3 x0 x4 := by decide
theorem l6_fn_s3 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S3.lut2.fn .o6 [x0, x1, x2, x3, x4, true] = Latch.bmux x3 x2 x0 := by decide
theorem l6_fn_s4 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S4.lut1.fn .o6 [x0, x1, x2, x3, x4, true] = Latch.bmux x1 x2 x0 := by decide

theorem lo_fn_s1 : ∀ x0 x2 x4 : Bool,
    Formal.Net.FasmLink.S1.lut2.fn .o6 [x0, false, x2, true, x4, false] = Latch.bmux x2 x0 x4 := by decide
theorem lo_fn_s2 : ∀ x0 x1 x4 : Bool,
    Formal.Net.FasmLink.S2.lut2.fn .o6 [x0, x1, false, true, x4, false] = Latch.bmux x0 x4 x1 := by decide
theorem lo_fn_s3 : ∀ x1 x3 x4 : Bool,
    Formal.Net.FasmLink.S3.lut1.fn .o6 [false, x1, true, x3, x4, false] = Latch.bmux x1 x3 x4 := by decide
theorem lo_fn_s4 : ∀ x0 x1 x2 : Bool,
    Formal.Net.FasmLink.S4.lut2.fn .o6 [x0, x1, x2, false, true, false] = Latch.bmux x2 x1 x0 := by decide

/-- Negative controls: q1 with its own data/feedback swapped for q0's is not
the physical O6; the odd bit with d and q swapped is not the physical LUT. -/
theorem l6_fn_wrong_fails_s1 : ¬ ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S1.lut1.fn .o6 [x0, x1, x2, x3, x4, true] = Latch.bmux x2 x4 x1 := by decide
theorem lo_fn_swap_fails_s1 : ¬ ∀ x0 x2 x4 : Bool,
    Formal.Net.FasmLink.S1.lut2.fn .o6 [x0, false, x2, true, x4, false] = Latch.bmux x2 x4 x0 := by decide

/-! Feedback pin delays (rfl-linked to C's `pinDelay`). -/
theorem q1fb_s1 : Formal.Net.FasmLink.S1.pinDelay[1]![0]! = (286, 975) := rfl
theorem q1fb_s2 : Formal.Net.FasmLink.S2.pinDelay[1]![4]! = (76, 290) := rfl
theorem q1fb_s3 : Formal.Net.FasmLink.S3.pinDelay[2]![0]! = (286, 975) := rfl
theorem q1fb_s4 : Formal.Net.FasmLink.S4.pinDelay[1]![0]! = (286, 975) := rfl
theorem q2fb_s1 : Formal.Net.FasmLink.S1.pinDelay[2]![4]! = (71, 276) := rfl
theorem q2fb_s2 : Formal.Net.FasmLink.S2.pinDelay[2]![1]! = (228, 873) := rfl
theorem q2fb_s3 : Formal.Net.FasmLink.S3.pinDelay[1]![4]! = (71, 272) := rfl
theorem q2fb_s4 : Formal.Net.FasmLink.S4.pinDelay[2]![0]! = (214, 689) := rfl

/-! ## 4. `holds_value` for q1 (pair O6, window [42, 157]) and q2 (odd LUT6
O6, window [45, 124]) on every seed. Loop bounds `L`:
q1 1132 / 447 / 1132 / 1132, q2 400 / 997 / 396 / 813 ps. -/

theorem latch_q1_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DW : dw 1 0 = Formal.Net.FasmLink.S1.pinDelay[1]![0]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 2 t = false → s + 1132 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 2 t = true → pin 1 3 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut1.fn .o6
        [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s1])
    H_DL (H_DW.trans q1fb_s1) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q1_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DW : dw 1 4 = Formal.Net.FasmLink.S2.pinDelay[1]![4]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 3 t = false → s + 447 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 3 t = true → pin 1 0 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut1.fn .o6
        [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s2])
    H_DL (H_DW.trans q1fb_s2) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q1_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 2 = (42, 157)) (H_DW : dw 2 0 = Formal.Net.FasmLink.S3.pinDelay[2]![0]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 3 t = false → s + 1132 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 2 3 t = true → pin 2 2 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 2 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut2.fn .o6
        [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 5 true rfl rfl t, l6_fn_s3])
    H_DL (H_DW.trans q1fb_s3) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q1_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DW : dw 1 0 = Formal.Net.FasmLink.S4.pinDelay[1]![0]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = false → s + 1132 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = true → pin 1 2 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut1.fn .o6
        [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s4])
    H_DL (H_DW.trans q1fb_s4) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q2_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DW : dw 2 4 = Formal.Net.FasmLink.S1.pinDelay[2]![4]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 2 t = false → s + 400 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 2 2 t = true → pin 2 0 t = v) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 2 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut2.fn .o6
        [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 1 false rfl rfl t, h.H_TIE 2 _ 3 true rfl rfl t,
        h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s1])
    H_DL (H_DW.trans q2fb_s1) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q2_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DW : dw 2 1 = Formal.Net.FasmLink.S2.pinDelay[2]![1]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 0 t = false → s + 997 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 2 0 t = true → pin 2 4 t = v) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 2 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 1) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut2.fn .o6
        [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 2 false rfl rfl t, h.H_TIE 2 _ 3 true rfl rfl t,
        h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s2])
    H_DL (H_DW.trans q2fb_s2) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q2_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 1 = (45, 124)) (H_DW : dw 1 4 = Formal.Net.FasmLink.S3.pinDelay[1]![4]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = false → s + 396 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = true → pin 1 3 t = v) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 1 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut1.fn .o6
        [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 0 false rfl rfl t, h.H_TIE 1 _ 2 true rfl rfl t,
        h.H_TIE 1 _ 5 false rfl rfl t, lo_fn_s3])
    H_DL (H_DW.trans q2fb_s3) (by decide) v s T H_EN_OPEN H_DATA

theorem latch_q2_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DW : dw 2 0 = Formal.Net.FasmLink.S4.pinDelay[2]![0]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 2 t = false → s + 813 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 2 2 t = true → pin 2 1 t = v) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 2 .o6 t = v :=
  latch_bit_net h rfl .o6 (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut2.fn .o6
        [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 3 false rfl rfl t, h.H_TIE 2 _ 4 true rfl rfl t,
        h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s4])
    H_DL (H_DW.trans q2fb_s4) (by decide) v s T H_EN_OPEN H_DATA

end seeds

end Formal.Cells.OnNetlistTimed2

namespace Formal.Cells.OnNetlistTimed2
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm Formal.Cells.OnNetlistTimed

/-! ## 5. Rule H on every seed and bit

`E` = enable-pin window max, `R` = data-pin window min (both C's `pinDelay`),
`H_A` = the required lower bound `E - R` on the node-fall -> sender-release
latency `A` (not available from `pinDelay`: it includes the ack_in output
route, the IOB and the off-chip sender). -/

section rh
variable {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}

/-- Rule H, seed 1, bit q0: enable pin A3 (152, 525), data pin A5 (292, 1029)
(port 2), feedback A2 (261, 872); needs `A ≥ 525 - 292 = 233`. -/
theorem rule_h_q0_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S1.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 2 t = false → s + 1029 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 2 t = v)
    (H_SETUP_PORT : s0 + 1029 ≤ s)
    (H_A : 233 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o5 t = v :=
  latch_rule_h_net h (i := 1) rfl .o5 (ie := 2) (id := 4) (iq := 1) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut1.fn .o5 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s1])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![1]! = (261, 872)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![2]! = (152, 525)))
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![4]! = (292, 1029)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 1, bit q1: enable pin A3 (152, 525), data pin A4 (388, 1358)
(port 3), feedback A1 (286, 975); needs `A ≥ 525 - 388 = 137`. -/
theorem rule_h_q1_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S1.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 2 t = false → s + 1132 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 3 t = v)
    (H_SETUP_PORT : s0 + 1358 ≤ s)
    (H_A : 137 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o6 t = v :=
  latch_rule_h_net h (i := 1) rfl .o6 (ie := 2) (id := 3) (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s1])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![0]! = (286, 975)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![2]! = (152, 525)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![3]! = (388, 1358)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 1, bit q2: enable pin A3 (309, 1066), data pin A1 (388, 1390)
(port 4), feedback A5 (71, 276); needs `A ≥ 1066 - 388 = 678`. -/
theorem rule_h_q2_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S1.pinDelay[2]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 2 t = false → s + 400 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 4 t = v)
    (H_SETUP_PORT : s0 + 1390 ≤ s)
    (H_A : 678 ≤ A) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 2 .o6 t = v :=
  latch_rule_h_net h (i := 2) rfl .o6 (ie := 2) (id := 0) (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 1 false rfl rfl t, h.H_TIE 2 _ 3 true rfl rfl t, h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s1])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[2]![4]! = (71, 276)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[2]![2]! = (309, 1066)))
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[2]![0]! = (388, 1390)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 2, bit q0: enable pin A4 (178, 690), data pin A3 (362, 1237)
(port 2), feedback A2 (261, 872); needs `A ≥ 690 - 362 = 328`. -/
theorem rule_h_q0_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S2.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 3 t = false → s + 1029 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 2 t = v)
    (H_SETUP_PORT : s0 + 1237 ≤ s)
    (H_A : 328 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o5 t = v :=
  latch_rule_h_net h (i := 1) rfl .o5 (ie := 3) (id := 2) (iq := 1) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut1.fn .o5 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s2])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![1]! = (261, 872)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![3]! = (178, 690)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![2]! = (362, 1237)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 2, bit q1: enable pin A4 (178, 690), data pin A1 (477, 1586)
(port 3), feedback A5 (76, 290); needs `A ≥ 690 - 477 = 213`. -/
theorem rule_h_q1_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S2.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 3 t = false → s + 447 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 3 t = v)
    (H_SETUP_PORT : s0 + 1586 ≤ s)
    (H_A : 213 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o6 t = v :=
  latch_rule_h_net h (i := 1) rfl .o6 (ie := 3) (id := 0) (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s2])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![4]! = (76, 290)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![3]! = (178, 690)))
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![0]! = (477, 1586)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 2, bit q2: enable pin A1 (329, 1172), data pin A5 (243, 1011)
(port 4), feedback A2 (228, 873); needs `A ≥ 1172 - 243 = 929`. -/
theorem rule_h_q2_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S2.pinDelay[2]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 0 t = false → s + 997 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 4 t = v)
    (H_SETUP_PORT : s0 + 1011 ≤ s)
    (H_A : 929 ≤ A) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 2 .o6 t = v :=
  latch_rule_h_net h (i := 2) rfl .o6 (ie := 0) (id := 4) (iq := 1) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 2 false rfl rfl t, h.H_TIE 2 _ 3 true rfl rfl t, h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s2])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[2]![1]! = (228, 873)))
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[2]![0]! = (329, 1172)))
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[2]![4]! = (243, 1011)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 3, bit q0: enable pin A4 (173, 640), data pin A2 (417, 1432)
(port 2), feedback A5 (123, 444); needs `A ≥ 640 - 417 = 223`. -/
theorem rule_h_q0_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 2 = (42, 157)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S3.pinDelay[2]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 3 t = false → s + 601 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 2 t = v)
    (H_SETUP_PORT : s0 + 1432 ≤ s)
    (H_A : 223 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 2 .o5 t = v :=
  latch_rule_h_net h (i := 2) rfl .o5 (ie := 3) (id := 1) (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut2.fn .o5 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 5 true rfl rfl t, l_fn_s3])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![4]! = (123, 444)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![3]! = (173, 640)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![1]! = (417, 1432)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 3, bit q1: enable pin A4 (173, 640), data pin A3 (368, 1275)
(port 3), feedback A1 (286, 975); needs `A ≥ 640 - 368 = 272`. -/
theorem rule_h_q1_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 2 = (42, 157)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S3.pinDelay[2]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 3 t = false → s + 1132 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 3 t = v)
    (H_SETUP_PORT : s0 + 1275 ≤ s)
    (H_A : 272 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 2 .o6 t = v :=
  latch_rule_h_net h (i := 2) rfl .o6 (ie := 3) (id := 2) (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 5 true rfl rfl t, l6_fn_s3])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![0]! = (286, 975)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![3]! = (173, 640)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![2]! = (368, 1275)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 3, bit q2: enable pin A2 (252, 844), data pin A4 (334, 1147)
(port 4), feedback A5 (71, 272); needs `A ≥ 844 - 334 = 510`. -/
theorem rule_h_q2_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 1 = (45, 124)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S3.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = false → s + 396 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 4 t = v)
    (H_SETUP_PORT : s0 + 1147 ≤ s)
    (H_A : 510 ≤ A) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 1 .o6 t = v :=
  latch_rule_h_net h (i := 1) rfl .o6 (ie := 1) (id := 3) (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 0 false rfl rfl t, h.H_TIE 1 _ 2 true rfl rfl t, h.H_TIE 1 _ 5 false rfl rfl t, lo_fn_s3])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[1]![4]! = (71, 272)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[1]![1]! = (252, 844)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[1]![3]! = (334, 1147)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 4, bit q0: enable pin A2 (212, 696), data pin A4 (305, 1171)
(port 2), feedback A5 (123, 447); needs `A ≥ 696 - 305 = 391`. -/
theorem rule_h_q0_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S4.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = false → s + 604 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 2 t = v)
    (H_SETUP_PORT : s0 + 1171 ≤ s)
    (H_A : 391 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o5 t = v :=
  latch_rule_h_net h (i := 1) rfl .o5 (ie := 1) (id := 3) (iq := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut1.fn .o5 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s4])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![4]! = (123, 447)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![1]! = (212, 696)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![3]! = (305, 1171)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 4, bit q1: enable pin A2 (212, 696), data pin A3 (312, 1093)
(port 3), feedback A1 (286, 975); needs `A ≥ 696 - 312 = 384`. -/
theorem rule_h_q1_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S4.pinDelay[1]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = false → s + 1132 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 3 t = v)
    (H_SETUP_PORT : s0 + 1093 ≤ s)
    (H_A : 384 ≤ A) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o6 t = v :=
  latch_rule_h_net h (i := 1) rfl .o6 (ie := 1) (id := 2) (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s4])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![0]! = (286, 975)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![1]! = (212, 696)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![2]! = (312, 1093)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

/-- Rule H, seed 4, bit q2: enable pin A3 (151, 521), data pin A2 (386, 1360)
(port 4), feedback A1 (214, 689); needs `A ≥ 521 - 386 = 135`. -/
theorem rule_h_q2_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S4.pinDelay[2]![k]!)
    (v : Bool) (s T tc A s0 : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 2 t = false → s + 813 ≤ t)
    (H_NODE_LOW : ∀ t, tc ≤ t → t ≤ T → out 0 .o6 t = false)
    (H_SENDER_HOLD : ∀ t, s0 ≤ t → t + 1 ≤ tc + A → ins 4 t = v)
    (H_SETUP_PORT : s0 + 1360 ≤ s)
    (H_A : 135 ≤ A) :
    ∀ t, s + 124 ≤ t → t ≤ T + 45 → out 2 .o6 t = v :=
  latch_rule_h_net h (i := 2) rfl .o6 (ie := 2) (id := 1) (iq := 0) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 3 false rfl rfl t, h.H_TIE 2 _ 4 true rfl rfl t, h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s4])
    rfl (by intro v hv; cases hv) rfl (by intro v hv; cases hv) H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[2]![0]! = (214, 689)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[2]![2]! = (151, 521)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[2]![1]! = (386, 1360)))
    (by decide) v s T tc A s0 H_EN_OPEN H_NODE_LOW H_SENDER_HOLD H_SETUP_PORT (by omega)

end rh

/-- **Negative control for rule H**: with zero node-fall -> release latency
(`A = 0`) rule H fails for every seed and bit: the `H_A` premise is not vacuous. -/
theorem rule_h_needs_ack_latency :
    ¬ (525 ≤ 0 + 292) ∧
    ¬ (525 ≤ 0 + 388) ∧
    ¬ (1066 ≤ 0 + 388) ∧
    ¬ (690 ≤ 0 + 362) ∧
    ¬ (690 ≤ 0 + 477) ∧
    ¬ (1172 ≤ 0 + 243) ∧
    ¬ (640 ≤ 0 + 417) ∧
    ¬ (640 ≤ 0 + 368) ∧
    ¬ (844 ≤ 0 + 334) ∧
    ¬ (696 ≤ 0 + 305) ∧
    ¬ (696 ≤ 0 + 312) ∧
    ¬ (521 ≤ 0 + 386) := by decide

end Formal.Cells.OnNetlistTimed2

/-! ## 6. LinkTimed's `stage_token` on the bits

`LinkTimed.DataPath.H_LATCH` is B's `Bundling.LatchRel` (Kleene windows,
`winK`) for ALL `t`, including the power-up interval where `Behaves` (a window
channel only constrains `t ≥ dmax`) says nothing. So `LatchRel` is derived
from `Behaves` only from `tstar` on (`latchRel_from`), `capture_win` is
re-proved with the relation required only from `tstar` (`capture_win_from`),
and `stage_token` with it (`stage_token_bit`, hypothesis `H_PU`: token `k`'s
enable arrives after `tstar`). The windows are the LUT window plus the route:
`[dllo + rlo, dlhi + rhi]` etc. -/

namespace Formal.Cells.OnNetlistTimed2
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm Formal.Cells.OnNetlistTimed

theorem bmux_of_mux : ∀ (e a b : K3) (x y z v : Bool),
    K3.admits e x = true → K3.admits a y = true → K3.admits b z = true →
    K3.mux e a b = K3.ofBool v → Latch.bmux x z y = v := by
  decide

/-- **Behaves -> `Bundling.LatchRel` from `tstar` on.** The LUT output `out`
is a window copy of `bmux en d p`; `en`, `d`, `p` are window copies of the
node `O`, the data net `D` and `out`. Then from `t ≥ dhi + M` (`M` ≥ every
route max) the Kleene reading over the summed windows determines `out`. -/
theorem latchRel_from {O D en d p out : Trace} {dlo dhi elo ehi rlo rhi wlo whi M : Nat}
    (H_LUT : WinDelay dlo dhi (fun t => Latch.bmux (en t) (d t) (p t)) out)
    (Re : WinDelay elo ehi O en) (Rd : WinDelay rlo rhi D d) (Rf : WinDelay wlo whi out p)
    (hM : ehi ≤ M ∧ rhi ≤ M ∧ whi ≤ M) :
    ∀ t b, dhi + M ≤ t →
      K3.mux (Bundling.winK O (dlo + elo) (dhi + ehi) t)
        (Bundling.winK out (dlo + wlo) (dhi + whi) t)
        (Bundling.winK D (dlo + rlo) (dhi + rhi) t) = K3.ofBool b → out t = b := by
  intro t b ht hm
  obtain ⟨s, hs1, hs2, e⟩ := H_LUT t (by omega)
  obtain ⟨u1, a1, a2, e1⟩ := Re s (by omega)
  obtain ⟨u2, b1, b2, e2⟩ := Rd s (by omega)
  obtain ⟨u3, c1, c2, e3⟩ := Rf s (by omega)
  have k1 := Bundling.win_consistent (x := O) (t := t) (lo := dlo + elo) (hi := dhi + ehi)
    (d := t - u1) (by omega) (by omega)
  have k2 := Bundling.win_consistent (x := out) (t := t) (lo := dlo + wlo) (hi := dhi + whi)
    (d := t - u3) (by omega) (by omega)
  have k3 := Bundling.win_consistent (x := D) (t := t) (lo := dlo + rlo) (hi := dhi + rhi)
    (d := t - u2) (by omega) (by omega)
  rw [show t - (t - u1) = u1 by omega, ← e1] at k1
  rw [show t - (t - u3) = u3 by omega, ← e3] at k2
  rw [show t - (t - u2) = u2 by omega, ← e2] at k3
  rw [e]; exact bmux_of_mux _ _ _ _ _ _ _ k1 k2 k3 hm

/-- `LinkTimed.capture_win` with the latch relation needed only from `tstar`. -/
theorem capture_win_from (d en q : Bundling.Sig) (dlo dhi elo ehi flo fhi tstar : Nat)
    (hL : ∀ t b, tstar ≤ t → K3.mux (Bundling.winK en elo ehi t) (Bundling.winK q flo fhi t)
      (Bundling.winK d dlo dhi t) = K3.ofBool b → q t = b)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff1 Toff2 Tnext Td Tnew : Nat) (v : Bool)
    (h12 : Toff1 ≤ Toff2)
    (h_on : ∀ t, Ton ≤ t → t < Toff1 → en t = true)
    (h_off : ∀ t, Toff2 ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_PU : tstar ≤ max (Ton + ehi) (Td + dhi))
    (H_SETUP : max (Ton + ehi) (Td + dhi) + fhi ≤ Toff1 + elo)
    (H_HOLD : Toff2 + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v := by
  suffices H : ∀ n, ∀ t, t < n → max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v
    from fun t h1 h2 => H (t + 1) t (Nat.lt_succ_self t) h1 h2
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t htn h1 h2
    have hts : tstar ≤ t := by omega
    by_cases hA : t < Toff1 + elo
    · have he : Bundling.winK en elo ehi t = .t :=
        Bundling.win_eq (b := true) hew (fun u hu1 hu2 => h_on u (by omega) (by omega))
      have hd : Bundling.winK d dlo dhi t = K3.ofBool v :=
        Bundling.win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
      exact hL t v hts (by rw [he, hd]; rfl)
    · have hq : Bundling.winK q flo fhi t = K3.ofBool v :=
        Bundling.win_eq hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      by_cases hB : t < Toff2 + ehi
      · have hd : Bundling.winK d dlo dhi t = K3.ofBool v :=
          Bundling.win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
        exact hL t v hts (by rw [hq, hd, Bundling.mux_same])
      · have he : Bundling.winK en elo ehi t = .f :=
          Bundling.win_eq (b := false) hew (fun u hu1 hu2 => h_off u (by omega) (by omega))
        exact hL t v hts (by rw [he, hq]; rfl)

section stage
open Formal.Cells.LinkTimed
variable {req ack rst O qp : CElemTiming.Trace} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}

/-- **`LinkTimed.stage_token` for one bit, latch relation from `tstar` on.**
The data-path fields of `LinkTimed.DataPath` for this bit, as named
hypotheses with the same names, plus `H_PU`. -/
theorem stage_token_bit (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (d q : Bundling.Sig) (val : Nat → Bool) (dS dE : Nat → Nat)
    (dlo dhi elo ehi flo fhi tstar Erel Sdr Lag : Nat)
    (H_LATCH : ∀ t b, tstar ≤ t → K3.mux (Bundling.winK O elo ehi t) (Bundling.winK q flo fhi t)
      (Bundling.winK d dlo dhi t) = K3.ofBool b → q t = b)
    (H_WIN : dlo ≤ dhi ∧ elo ≤ ehi ∧ flo ≤ fhi)
    (H_LATCH_LOOP_POS : 1 ≤ flo)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → d t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧ O u = false)
    (H_PULSE_WIDTH : dlmax + ehi + fhi ≤ 2 * dlmin + E + elo)
    (H_DATA_SETUP : dhi + fhi + Lag ≤ Sdr + 2 * dlmin + E + elo)
    (H_RULE_H : dlmax + ehi ≤ dlmin + Erel + dlo)
    (k : Nat) (H_PU : tstar ≤ cph ρ φ α β (2 * k) + dlmax + ehi) :
    ∀ t, max (cph ρ φ α β (2 * k) + dlmax + ehi) (dS k + dhi) ≤ t →
      t < cph ρ φ α β (2 * k + 1 + 1) + dlmin + elo → q t = val k := by
  have hl := CElemTiming.winDelay_le C.H_CTL.H_LUT
  have ⟨hon, hoff, _, _⟩ := enable_train C k
  have hfa := fall_after C k
  have hrel : cph ρ φ α β (2 * k + 1) + dlmin + Erel ≤ dE k := by
    obtain ⟨u, hu1, hu2, hu3⟩ := H_DATA_REL k
    have := obs_late C (2 * k + 1) u hu1 (by rw [Vph_o]; exact hu3)
    omega
  have hlead := H_DATA_LEAD k
  have hrho : ρ k ≤ cph ρ φ α β (2 * k) := by rw [cph_e]; exact Nat.le_max_left _ _
  have ⟨hdw, hew, hfw⟩ := H_WIN
  exact capture_win_from d O q dlo dhi elo ehi flo fhi tstar H_LATCH hdw hew hfw H_LATCH_LOOP_POS
    (cph ρ φ α β (2 * k) + dlmax) (cph ρ φ α β (2 * k + 1) + dlmin)
    (cph ρ φ α β (2 * k + 1) + dlmax) (cph ρ φ α β (2 * k + 1 + 1) + dlmin)
    (dS k) (dE k) (val k) (by omega) hon hoff
    (fun t h1 h2 => H_DATA_VALID k t h1 h2) (by omega) (by omega) (by omega)

end stage

/-- **Bridge: the physical C node is `LinkTimed`'s `H_CTL`** (`Loop INIT_c2n`
on the req, ack and rst pins, not negated). -/
theorem cnode_loop_n {N : PNet} {ins : Nat → Trace} {out : Nat → LOut → Trace}
    {pin : Nat → Nat → Trace} {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
    (h : Behaves N ins out pin dl dw) {i : Nat} {L : PLut}
    (hL : N.luts[i]? = some L) {ia ib iq ir : Nat}
    (hq : L.pins[iq]? = some (.lut i .o6))
    (hfn : ∀ t, L.fn .o6 ((List.range 6).map (fun k => pin i k t)) =
      exc INIT_c2n (pin i ia t) (pin i ib t) (pin i iq t) (pin i ir t))
    (H_LOOP_POS : 0 < (dl i).1 + (dw i iq).1) :
    Loop INIT_c2n (pin i ia) (pin i ib) (pin i ir) (out i .o6) (pin i iq)
      (dl i).1 (dl i).2 (dw i iq).1 (dw i iq).2 where
  H_LUT := by
    have hl := h.H_LUT i L .o6 hL
    rw [funext hfn] at hl; exact hl
  H_FB := h.H_ROUTE i L iq (.lut i .o6) hL hq (by intro v hv; cases hv)
  H_LOOP_POS := H_LOOP_POS

end Formal.Cells.OnNetlistTimed2

namespace Formal.Cells.OnNetlistTimed2
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm Formal.Cells.OnNetlistTimed

/-- **`stage_token` on a physical latch bit.** LUT `i` output `o` is the latch
(`hfn`), its enable pin `ie` routed from the C node (LUT 0 O6), its data pin
`id` from port `j`, its feedback `iq` from itself. With `C` the stage's
controller contract on the C node's pin traces (its `H_CTL` is discharged on
the bits by `ctl_loop_s*`), the latch output carries token `k`'s value as in
`LinkTimed.stage_token`, with windows LUT + route. -/
theorem stage_token_net {N : PNet} {ins : Nat → Trace} {out : Nat → LOut → Trace}
    {pin : Nat → Nat → Trace} {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
    (h : Behaves N ins out pin dl dw) {i : Nat} {L : PLut}
    (hL : N.luts[i]? = some L) (o : LOut) {ie id iq j : Nat}
    (hq : L.pins[iq]? = some (.lut i o))
    (hfn : ∀ t, L.fn o ((List.range 6).map (fun k => pin i k t)) =
      Latch.bmux (pin i ie t) (pin i id t) (pin i iq t))
    (hse : L.pins[ie]? = some (.lut 0 .o6)) (hsd : L.pins[id]? = some (.port j))
    {dllo dlhi wlo whi elo ehi rlo rhi M : Nat} (H_DL : dl i = (dllo, dlhi))
    (H_DW : dw i iq = (wlo, whi)) (H_DWE : dw i ie = (elo, ehi)) (H_DWD : dw i id = (rlo, rhi))
    (hM : ehi ≤ M ∧ rhi ≤ M ∧ whi ≤ M) (hpos : 1 ≤ dllo + wlo)
    {req ack rst qp : Trace} {ρ φ α β : Nat → Nat} {dlmin dlmax dwmin dwmax E t0 : Nat}
    (C : LinkTimed.CtlEnv req ack rst (out 0 .o6) qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins j t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : dlmax + (dlhi + ehi) + (dlhi + whi) ≤ 2 * dlmin + E + (dllo + elo))
    (H_DATA_SETUP : (dlhi + rhi) + (dlhi + whi) + Lag ≤ Sdr + 2 * dlmin + E + (dllo + elo))
    (H_RULE_H : dlmax + (dlhi + ehi) ≤ dlmin + Erel + (dllo + rlo))
    (k : Nat) (H_PU : dlhi + M ≤ LinkTimed.cph ρ φ α β (2 * k) + dlmax + (dlhi + ehi)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + dlmax + (dlhi + ehi)) (dS k + (dlhi + rhi)) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + dlmin + (dllo + elo) → out i o t = val k := by
  have hl := h.H_LUT i L o hL
  have e : (fun t => L.fn o ((List.range 6).map (fun k => pin i k t))) =
      (fun t => Latch.bmux (pin i ie t) (pin i id t) (pin i iq t)) := funext hfn
  rw [e, H_DL] at hl
  have Rf := h.H_ROUTE i L iq _ hL hq (by intro v hv; cases hv)
  have Re := h.H_ROUTE i L ie _ hL hse (by intro v hv; cases hv)
  have Rd := h.H_ROUTE i L id _ hL hsd (by intro v hv; cases hv)
  rw [H_DW] at Rf; rw [H_DWE] at Re; rw [H_DWD] at Rd
  have w1 := winDelay_le hl; have w2 := winDelay_le Rf
  have w3 := winDelay_le Re; have w4 := winDelay_le Rd
  have hR := latchRel_from hl Re Rd Rf hM
  exact stage_token_bit C (ins j) (out i o) val dS dE (dllo + rlo) (dlhi + rhi) (dllo + elo)
    (dlhi + ehi) (dllo + wlo) (dlhi + whi) (dlhi + M) Erel Sdr Lag
    (fun t b ht hm => hR t b ht hm) ⟨by omega, by omega, by omega⟩ (by omega)
    H_DATA_VALID H_DATA_LEAD H_DATA_REL H_PULSE_WIDTH H_DATA_SETUP H_RULE_H k H_PU

end Formal.Cells.OnNetlistTimed2

namespace Formal.Cells.OnNetlistTimed2
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm Formal.Cells.OnNetlistTimed

section st
variable {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
  {ρ φ α β : Nat → Nat} {E t0 : Nat}

/-- `LinkTimed.CtlEnv.H_CTL` discharged on the seed-1 bits. -/
theorem ctl_loop_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S1.pinDelay[0]![3]!) :
    Loop INIT_c2n (pin 0 1) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) 45 124 125 445 := by
  have H_DW' : dw 0 3 = (125, 445) := H_DW.trans rfl
  have L := cnode_loop_n (iq := 3) (ia := 1) (ib := 2) (ir := 0) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut0.fn .o6 [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 4 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s1])
    (by rw [H_DL, H_DW']; decide)
  rw [H_DL, H_DW'] at L; exact L

/-- `LinkTimed.CtlEnv.H_CTL` discharged on the seed-2 bits. -/
theorem ctl_loop_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 0 = Formal.Net.FasmLink.S2.pinDelay[0]![0]!) :
    Loop INIT_c2n (pin 0 2) (pin 0 1) (pin 0 4) (out 0 .o6) (pin 0 0) 45 124 211 714 := by
  have H_DW' : dw 0 0 = (211, 714) := H_DW.trans rfl
  have L := cnode_loop_n (iq := 0) (ia := 2) (ib := 1) (ir := 4) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut0.fn .o6 [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 3 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s2])
    (by rw [H_DL, H_DW']; decide)
  rw [H_DL, H_DW'] at L; exact L

/-- `LinkTimed.CtlEnv.H_CTL` discharged on the seed-3 bits. -/
theorem ctl_loop_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S3.pinDelay[0]![3]!) :
    Loop INIT_c2n (pin 0 4) (pin 0 1) (pin 0 0) (out 0 .o6) (pin 0 3) 45 124 206 836 := by
  have H_DW' : dw 0 3 = (206, 836) := H_DW.trans rfl
  have L := cnode_loop_n (iq := 3) (ia := 4) (ib := 1) (ir := 0) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut0.fn .o6 [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 2 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s3])
    (by rw [H_DL, H_DW']; decide)
  rw [H_DL, H_DW'] at L; exact L

/-- `LinkTimed.CtlEnv.H_CTL` discharged on the seed-4 bits. -/
theorem ctl_loop_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S4.pinDelay[0]![3]!) :
    Loop INIT_c2n (pin 0 4) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) 45 124 124 466 := by
  have H_DW' : dw 0 3 = (124, 466) := H_DW.trans rfl
  have L := cnode_loop_n (iq := 3) (ia := 4) (ib := 2) (ir := 0) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut0.fn .o6 [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 1 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s4])
    (by rw [H_DL, H_DW']; decide)
  rw [H_DL, H_DW'] at L; exact L

/-- `stage_token`, seed 1, bit q0: windows (LUT + route) enable
[194, 682], data [334, 1186], loop [303, 1029]. Obligations: `E ≥ 1551`
(pulse width), `Sdr + E ≥ 1931 + Lag` (setup), `Erel ≥ 427` (rule H, LinkTimed form),
`cph (2k) ≥ 380` (power-up). -/
theorem stage_token_q0_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S1.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 1) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 125 445 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 2 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1551 ≤ E) (H_DATA_SETUP : 1931 + Lag ≤ Sdr + E) (H_RULE_H : 427 ≤ Erel)
    (k : Nat) (H_PU : 380 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 806) (dS k + 1186) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 239 → out 1 .o5 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o5 (ie := 2) (id := 4) (iq := 1) (j := 2) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut1.fn .o5 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s1])
    rfl rfl H_DL
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![1]! = (261, 872)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![2]! = (152, 525)))
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![4]! = (292, 1029)))
    (M := 1029) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 1, bit q1: windows (LUT + route) enable
[194, 682], data [430, 1515], loop [328, 1132]. Obligations: `E ≥ 1654`
(pulse width), `Sdr + E ≥ 2363 + Lag` (setup), `Erel ≥ 331` (rule H, LinkTimed form),
`cph (2k) ≥ 709` (power-up). -/
theorem stage_token_q1_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S1.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 1) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 125 445 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 3 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1654 ≤ E) (H_DATA_SETUP : 2363 + Lag ≤ Sdr + E) (H_RULE_H : 331 ≤ Erel)
    (k : Nat) (H_PU : 709 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 806) (dS k + 1515) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 239 → out 1 .o6 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o6 (ie := 2) (id := 3) (iq := 0) (j := 3) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s1])
    rfl rfl H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![0]! = (286, 975)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![2]! = (152, 525)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[1]![3]! = (388, 1358)))
    (M := 1358) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 1, bit q2: windows (LUT + route) enable
[354, 1190], data [433, 1514], loop [116, 400]. Obligations: `E ≥ 1270`
(pulse width), `Sdr + E ≥ 1470 + Lag` (setup), `Erel ≥ 836` (rule H, LinkTimed form),
`cph (2k) ≥ 200` (power-up). -/
theorem stage_token_q2_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S1.pinDelay[2]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 1) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 125 445 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 4 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1270 ≤ E) (H_DATA_SETUP : 1470 + Lag ≤ Sdr + E) (H_RULE_H : 836 ≤ Erel)
    (k : Nat) (H_PU : 200 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 1314) (dS k + 1514) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 399 → out 2 .o6 t = val k := by
  have e := stage_token_net h (i := 2) rfl .o6 (ie := 2) (id := 0) (iq := 4) (j := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 1 false rfl rfl t, h.H_TIE 2 _ 3 true rfl rfl t, h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s1])
    rfl rfl H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[2]![4]! = (71, 276)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[2]![2]! = (309, 1066)))
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S1.pinDelay[2]![0]! = (388, 1390)))
    (M := 1390) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 2, bit q0: windows (LUT + route) enable
[220, 847], data [404, 1394], loop [303, 1029]. Obligations: `E ≥ 1690`
(pulse width), `Sdr + E ≥ 2113 + Lag` (setup), `Erel ≥ 522` (rule H, LinkTimed form),
`cph (2k) ≥ 423` (power-up). -/
theorem stage_token_q0_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S2.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 2) (pin 0 1) (pin 0 4) (out 0 .o6) (pin 0 0) ρ φ α β
      45 124 211 714 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 2 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1690 ≤ E) (H_DATA_SETUP : 2113 + Lag ≤ Sdr + E) (H_RULE_H : 522 ≤ Erel)
    (k : Nat) (H_PU : 423 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 971) (dS k + 1394) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 265 → out 1 .o5 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o5 (ie := 3) (id := 2) (iq := 1) (j := 2) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut1.fn .o5 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s2])
    rfl rfl H_DL
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![1]! = (261, 872)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![3]! = (178, 690)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![2]! = (362, 1237)))
    (M := 1237) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 2, bit q1: windows (LUT + route) enable
[220, 847], data [519, 1743], loop [118, 447]. Obligations: `E ≥ 1108`
(pulse width), `Sdr + E ≥ 1880 + Lag` (setup), `Erel ≥ 407` (rule H, LinkTimed form),
`cph (2k) ≥ 772` (power-up). -/
theorem stage_token_q1_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S2.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 2) (pin 0 1) (pin 0 4) (out 0 .o6) (pin 0 0) ρ φ α β
      45 124 211 714 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 3 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1108 ≤ E) (H_DATA_SETUP : 1880 + Lag ≤ Sdr + E) (H_RULE_H : 407 ≤ Erel)
    (k : Nat) (H_PU : 772 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 971) (dS k + 1743) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 265 → out 1 .o6 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o6 (ie := 3) (id := 0) (iq := 4) (j := 3) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s2])
    rfl rfl H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![4]! = (76, 290)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![3]! = (178, 690)))
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[1]![0]! = (477, 1586)))
    (M := 1586) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 2, bit q2: windows (LUT + route) enable
[374, 1296], data [288, 1135], loop [273, 997]. Obligations: `E ≥ 1953`
(pulse width), `Sdr + E ≥ 1668 + Lag` (setup), `Erel ≥ 1087` (rule H, LinkTimed form),
`cph (2k) ≥ 0` (power-up). -/
theorem stage_token_q2_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S2.pinDelay[2]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 2) (pin 0 1) (pin 0 4) (out 0 .o6) (pin 0 0) ρ φ α β
      45 124 211 714 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 4 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1953 ≤ E) (H_DATA_SETUP : 1668 + Lag ≤ Sdr + E) (H_RULE_H : 1087 ≤ Erel)
    (k : Nat) (H_PU : 0 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 1420) (dS k + 1135) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 419 → out 2 .o6 t = val k := by
  have e := stage_token_net h (i := 2) rfl .o6 (ie := 0) (id := 4) (iq := 1) (j := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 2 false rfl rfl t, h.H_TIE 2 _ 3 true rfl rfl t, h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s2])
    rfl rfl H_DL
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[2]![1]! = (228, 873)))
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[2]![0]! = (329, 1172)))
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S2.pinDelay[2]![4]! = (243, 1011)))
    (M := 1172) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 3, bit q0: windows (LUT + route) enable
[215, 797], data [459, 1589], loop [165, 601]. Obligations: `E ≥ 1217`
(pulse width), `Sdr + E ≥ 1885 + Lag` (setup), `Erel ≥ 417` (rule H, LinkTimed form),
`cph (2k) ≥ 668` (power-up). -/
theorem stage_token_q0_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 2 = (42, 157)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S3.pinDelay[2]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 4) (pin 0 1) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 206 836 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 2 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1217 ≤ E) (H_DATA_SETUP : 1885 + Lag ≤ Sdr + E) (H_RULE_H : 417 ≤ Erel)
    (k : Nat) (H_PU : 668 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 921) (dS k + 1589) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 260 → out 2 .o5 t = val k := by
  have e := stage_token_net h (i := 2) rfl .o5 (ie := 3) (id := 1) (iq := 4) (j := 2) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut2.fn .o5 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 5 true rfl rfl t, l_fn_s3])
    rfl rfl H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![4]! = (123, 444)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![3]! = (173, 640)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![1]! = (417, 1432)))
    (M := 1432) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 3, bit q1: windows (LUT + route) enable
[215, 797], data [410, 1432], loop [328, 1132]. Obligations: `E ≥ 1748`
(pulse width), `Sdr + E ≥ 2259 + Lag` (setup), `Erel ≥ 466` (rule H, LinkTimed form),
`cph (2k) ≥ 511` (power-up). -/
theorem stage_token_q1_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 2 = (42, 157)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S3.pinDelay[2]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 4) (pin 0 1) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 206 836 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 3 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1748 ≤ E) (H_DATA_SETUP : 2259 + Lag ≤ Sdr + E) (H_RULE_H : 466 ≤ Erel)
    (k : Nat) (H_PU : 511 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 921) (dS k + 1432) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 260 → out 2 .o6 t = val k := by
  have e := stage_token_net h (i := 2) rfl .o6 (ie := 3) (id := 2) (iq := 0) (j := 3) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 5 true rfl rfl t, l6_fn_s3])
    rfl rfl H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![0]! = (286, 975)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![3]! = (173, 640)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[2]![2]! = (368, 1275)))
    (M := 1275) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 3, bit q2: windows (LUT + route) enable
[297, 968], data [379, 1271], loop [116, 396]. Obligations: `E ≥ 1101`
(pulse width), `Sdr + E ≥ 1280 + Lag` (setup), `Erel ≥ 668` (rule H, LinkTimed form),
`cph (2k) ≥ 179` (power-up). -/
theorem stage_token_q2_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 1 = (45, 124)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S3.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 4) (pin 0 1) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 206 836 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 4 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1101 ≤ E) (H_DATA_SETUP : 1280 + Lag ≤ Sdr + E) (H_RULE_H : 668 ≤ Erel)
    (k : Nat) (H_PU : 179 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 1092) (dS k + 1271) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 342 → out 1 .o6 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o6 (ie := 1) (id := 3) (iq := 4) (j := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 0 false rfl rfl t, h.H_TIE 1 _ 2 true rfl rfl t, h.H_TIE 1 _ 5 false rfl rfl t, lo_fn_s3])
    rfl rfl H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[1]![4]! = (71, 272)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[1]![1]! = (252, 844)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S3.pinDelay[1]![3]! = (334, 1147)))
    (M := 1147) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 4, bit q0: windows (LUT + route) enable
[254, 853], data [347, 1328], loop [165, 604]. Obligations: `E ≥ 1237`
(pulse width), `Sdr + E ≥ 1588 + Lag` (setup), `Erel ≥ 585` (rule H, LinkTimed form),
`cph (2k) ≥ 351` (power-up). -/
theorem stage_token_q0_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S4.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 4) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 124 466 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 2 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1237 ≤ E) (H_DATA_SETUP : 1588 + Lag ≤ Sdr + E) (H_RULE_H : 585 ≤ Erel)
    (k : Nat) (H_PU : 351 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 977) (dS k + 1328) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 299 → out 1 .o5 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o5 (ie := 1) (id := 3) (iq := 4) (j := 2) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut1.fn .o5 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s4])
    rfl rfl H_DL
    ((H_DWALL 4).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![4]! = (123, 447)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![1]! = (212, 696)))
    ((H_DWALL 3).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![3]! = (305, 1171)))
    (M := 1171) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 4, bit q1: windows (LUT + route) enable
[254, 853], data [354, 1250], loop [328, 1132]. Obligations: `E ≥ 1765`
(pulse width), `Sdr + E ≥ 2038 + Lag` (setup), `Erel ≥ 578` (rule H, LinkTimed form),
`cph (2k) ≥ 273` (power-up). -/
theorem stage_token_q1_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DWALL : ∀ k, dw 1 k = Formal.Net.FasmLink.S4.pinDelay[1]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 4) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 124 466 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 3 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1765 ≤ E) (H_DATA_SETUP : 2038 + Lag ≤ Sdr + E) (H_RULE_H : 578 ≤ Erel)
    (k : Nat) (H_PU : 273 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 977) (dS k + 1250) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 299 → out 1 .o6 t = val k := by
  have e := stage_token_net h (i := 1) rfl .o6 (ie := 1) (id := 2) (iq := 0) (j := 3) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h.H_TIE 1 _ 5 true rfl rfl t, l6_fn_s4])
    rfl rfl H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![0]! = (286, 975)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![1]! = (212, 696)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[1]![2]! = (312, 1093)))
    (M := 1093) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

/-- `stage_token`, seed 4, bit q2: windows (LUT + route) enable
[196, 645], data [431, 1484], loop [259, 813]. Obligations: `E ≥ 1296`
(pulse width), `Sdr + E ≥ 2011 + Lag` (setup), `Erel ≥ 293` (rule H, LinkTimed form),
`cph (2k) ≥ 715` (power-up). -/
theorem stage_token_q2_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 2 = (45, 124)) (H_DWALL : ∀ k, dw 2 k = Formal.Net.FasmLink.S4.pinDelay[2]![k]!)
    (C : LinkTimed.CtlEnv (pin 0 4) (pin 0 2) (pin 0 0) (out 0 .o6) (pin 0 3) ρ φ α β
      45 124 124 466 E t0)
    (val : Nat → Bool) (dS dE : Nat → Nat) (Erel Sdr Lag : Nat)
    (H_DATA_VALID : ∀ k t, dS k ≤ t → t < dE k → ins 4 t = val k)
    (H_DATA_LEAD : ∀ k, dS k + Sdr ≤ ρ k + Lag)
    (H_DATA_REL : ∀ k, ∃ u, LinkTimed.cph ρ φ α β (2 * k + 1) ≤ u ∧ u + Erel ≤ dE k ∧
      out 0 .o6 u = false)
    (H_PULSE_WIDTH : 1296 ≤ E) (H_DATA_SETUP : 2011 + Lag ≤ Sdr + E) (H_RULE_H : 293 ≤ Erel)
    (k : Nat) (H_PU : 715 ≤ LinkTimed.cph ρ φ α β (2 * k)) :
    ∀ t, max (LinkTimed.cph ρ φ α β (2 * k) + 769) (dS k + 1484) ≤ t →
      t < LinkTimed.cph ρ φ α β (2 * k + 1 + 1) + 241 → out 2 .o6 t = val k := by
  have e := stage_token_net h (i := 2) rfl .o6 (ie := 2) (id := 1) (iq := 0) (j := 4) rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut2.fn .o6 [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
      rw [h.H_TIE 2 _ 3 false rfl rfl t, h.H_TIE 2 _ 4 true rfl rfl t, h.H_TIE 2 _ 5 false rfl rfl t, lo_fn_s4])
    rfl rfl H_DL
    ((H_DWALL 0).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[2]![0]! = (214, 689)))
    ((H_DWALL 2).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[2]![2]! = (151, 521)))
    ((H_DWALL 1).trans (rfl : Formal.Net.FasmLink.S4.pinDelay[2]![1]! = (386, 1360)))
    (M := 1360) (by decide) (by decide) C val dS dE Erel Sdr Lag H_DATA_VALID H_DATA_LEAD H_DATA_REL
    (by omega) (by omega) (by omega) k (by omega)
  intro t h1 h2; exact e t (by omega) (by omega)

end st

end Formal.Cells.OnNetlistTimed2
