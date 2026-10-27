import Formal.Cells.Prelim
import Formal.Cells.CElemTiming
import Formal.Cells.Latch
import Formal.Net.Fasm.Basic
import Formal.Net.FasmLink.S1
import Formal.Net.FasmLink.S2
import Formal.Net.FasmLink.S3
import Formal.Net.FasmLink.S4

/-!
# Probe Bt: shard B's TIMED cell theorems on the routed bits (link_arb, 4 seeds)

Shard B x shard C. The physical side is C-11b's gate-relation semantics
`Formal.Net.Fasm.Behaves` on C-11c's netlists read back from the four routed
`link_arb` bitstreams (`Formal.Net.FasmLink.S1..S4`; nextpnr sha256
9c732bc6303458df, `toolchain.sh` ok, as stamped by `fasm2lean2/check.sh`):
every physical LUT pin `pin i k` has its own trace, a window-delay copy of its
routed source (`H_ROUTE`, bounds `dw i k`), every LUT output a window-delay copy
of the PHYSICAL INIT on the PHYSICAL pins (`H_LUT`, bounds `dl i`), ties are
constant (`H_TIE`).

## The bridge

* `cnode_loop` (generic, any `PNet`): if LUT `i` computes `bd_c2n` on its
  physical pins (`hfn`, decided per seed) and its pin `iq` is routed from its
  own O6, then `Behaves` gives B's `CElemTiming.Loop INIT_c2` for that LUT,
  with inputs `a` = the req pin, `b` = the NEGATED ack pin (`C(a, ~b)` is
  `C(a, b')` with `b' = ~b`, `c2n_as_c2`), LUT window `dl i` and feedback
  window `dw i iq` (the routed feedback pin's own bounds).
* `latch_holds_bits` (generic): a Bool LUT output that is a window-delay copy
  of `bmux en d p` with `p` a window-delay copy of the output (any O5/O6, any
  bounds) carries a B `Latch.LatchBit` with loop bound `L = dlmax + dwmax`
  (the loop delay `k t` is chosen pointwise from the two windows,
  `loop_k`), so B's `Latch.holds_value` applies.

## Instantiated on the bits, with numbers

LUT windows (hypothesis `H_DL`, from prjxray-db `timings/CLB*.sdf`, envelope of
min-of-fast and max-of-slow over all `IOPATH A* O6` (144 arcs) resp. `A* O5`
(120 arcs) entries of all four CLB tile types):
O6 `[45, 124]` ps (the link C node is a LUT6 using O6 only),
O5 `[42, 157]` ps (the latch pair is a LUT6_2; one `dl` per site in `Behaves`,
so it takes the O5 envelope, which contains the O6 one).
Feedback windows (hypothesis `H_DW`, rfl-linked to C's generated `pinDelay`):

| seed | C node fb pin | dw fb | Dmin | Dmax | E >= | latch q0 fb pin | dw fb | latch L |
|---|---|---|---|---|---|---|---|---|
| 1 | A4 | [125, 445] | 170 | 569 | 524 | A2 | [261, 872] | 1029 |
| 2 | A1 | [211, 714] | 256 | 838 | 793 | A2 | [261, 872] | 1029 |
| 3 | A4 | [206, 836] | 251 | 960 | 915 | A5 | [123, 444] | 601 |
| 4 | A4 | [124, 466] | 169 | 590 | 545 | A5 | [123, 447] | 604 |

(`Dmax = 124 + dw_hi`, `Dmin = 45 + dw_lo`, `E >= Dmax - 45` is B's
`H_ENV_LATENCY`, latch `L = 157 + dw_hi`.)

Port-level forms (`c_follow_hold_ports_s*`): through the routed input pins
(`H_ROUTE`, C's `pinDelay` for every pin, `H_DWALL`) the ports must hold
`req = v, ack_out = !v, rst = 0` for 1646 / 2083 / 2137 / 1745 ps; the excess
over `Dmax` is the IOB-to-LUT input-route skew of this harness.
Negative controls: `c_fn_unpermuted_fails_s1`, `l_fn_swap_fails_s1`.

Core Lean only. Every proof is closed; nothing beyond core Lean's own
foundations is assumed, and no native evaluation is used.
-/

namespace Formal.Cells.OnNetlistTimed
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm

/-! ## 0. Function lemmas -/

/-- `bd_c2n` is `bd_c2` with its `b` input inverted (on the real INITs). -/
theorem c2n_as_c2 : ∀ a b q r : Bool, exc INIT_c2n a b q r = exc INIT_c2 a (!b) q r := by
  decide

theorem ofBool_inj : ∀ {a b : Bool}, K3.ofBool a = K3.ofBool b → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

theorem mux_ofBool (en d p : Bool) :
    K3.mux (K3.ofBool en) (K3.ofBool p) (K3.ofBool d) = K3.ofBool (Latch.bmux en d p) := by
  cases en <;> cases d <;> cases p <;> rfl

/-! ## 1. Generic bridge: physical C node -> B's `Loop` -/

section cbridge
variable {N : PNet} {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}

/-- **Bridge (C-element family).** From the physical gate relations, a LUT `i`
whose physical function on its pins is `bd_c2n(pin ia, pin ib, pin iq, pin ir)`
(`hfn`) and whose pin `iq` is routed from its own O6 (`hq`) is B's `Loop` for
`bd_c2` with `b` = the negated `ib` pin, LUT window `dl i`, feedback window
`dw i iq`. -/
theorem cnode_loop (h : Behaves N ins out pin dl dw) {i : Nat} {L : PLut}
    (hL : N.luts[i]? = some L) {ia ib iq ir : Nat}
    (hq : L.pins[iq]? = some (.lut i .o6))
    (hfn : ∀ t, L.fn .o6 ((List.range 6).map (fun k => pin i k t)) =
      exc INIT_c2n (pin i ia t) (pin i ib t) (pin i iq t) (pin i ir t))
    (H_LOOP_POS : 0 < (dl i).1 + (dw i iq).1) :
    Loop INIT_c2 (pin i ia) (fun t => !pin i ib t) (pin i ir) (out i .o6) (pin i iq)
      (dl i).1 (dl i).2 (dw i iq).1 (dw i iq).2 where
  H_LUT := by
    have hl := h.H_LUT i L .o6 hL
    have e : (fun t => L.fn .o6 ((List.range 6).map (fun k => pin i k t))) =
        (fun t => exc INIT_c2 (pin i ia t) (!pin i ib t) (pin i iq t) (pin i ir t)) := by
      funext t; rw [hfn t, c2n_as_c2]
    rw [e] at hl; exact hl
  H_FB := h.H_ROUTE i L iq (.lut i .o6) hL hq (by intro v hv; cases hv)
  H_LOOP_POS := H_LOOP_POS

end cbridge

/-! ## 2. B's C-element theorems restated for `C(a, ~b)` -/

section c2n
variable {a b rst O qp : Trace} {dlo dhi wlo whi : Nat}

/-- `c2_follow_hold` for the C node `C(a, ~b)`: `a = v`, `b = !v` for `Dmax`. -/
theorem c2n_follow_hold (L : Loop INIT_c2 a (fun t => !b t) rst O qp dlo dhi wlo whi)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + (dhi + whi) → a s = v ∧ b s = !v ∧ rst s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → rst s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → a s = v ∨ b s = !v) :
    (∀ t, t0 + dhi ≤ t → t ≤ t2 + dlo → O t = v) ∧
    (∀ t, t0 + (dhi + whi) ≤ t → t ≤ t2 + (dlo + wlo) → qp t = v) :=
  c2_follow_hold L v t0 t2
    (fun s h1 h2 => by
      obtain ⟨ha, hb, hr⟩ := H_PULSE s h1 h2
      exact ⟨ha, by show (!b s) = v; rw [hb, Bool.not_not], hr⟩)
    H_NORST
    (fun s h1 h2 => by
      rcases H_NOT_BOTH s h1 h2 with h | h
      · exact Or.inl h
      · exact Or.inr (by show (!b s) = v; rw [h, Bool.not_not]))

/-- `c2_four_phase` for the C node `C(a, ~b)`: phase `k` targets `a = V k`,
`b = !V k`. -/
theorem c2n_four_phase (L : Loop INIT_c2 a (fun t => !b t) rst O qp dlo dhi wlo whi)
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, a (c k) = V k ∧ b (c k) = !V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → a s = V k ∨ b s = !V k)
    (H_NORST : ∀ s, c 0 ≤ s → rst s = false)
    (H_ACK : ∀ k s, c k ≤ s → (a s ≠ V k ∨ b s ≠ !V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dhi + whi ≤ dlo + E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + dlo → O u = !V 0) :
    ∀ k, (∀ t, c k + dhi ≤ t → t + 1 ≤ c (k + 1) + dlo → O t = V k) ∧
         (∀ t, c k + (dhi + whi) ≤ t → t + 1 ≤ c (k + 1) + (dlo + wlo) → qp t = V k) := by
  have key : ∀ (x y : Bool), ((!x) = y) ↔ (x = !y) := by decide
  have keyn : ∀ (x y : Bool), ((!x) ≠ y) ↔ (x ≠ !y) := by decide
  exact c2_four_phase L V c E H_ALT H_ORDER
    (fun k => ⟨(H_BOTH k).1, (key _ _).2 (H_BOTH k).2⟩)
    (fun k s h1 h2 => (H_NEXT k s h1 h2).imp id (key _ _).2)
    H_NORST
    (fun k s h1 hd => H_ACK k s h1 (hd.imp id (keyn _ _).1))
    H_ENV_LATENCY H_RESET_DONE

end c2n


/-! ## 2b. From the ports: input routes in front of the C node

`winDelay_held`: a window channel carries a held value, shifted. Used to turn
B's pin-level obligations into port-level ones: the C node's three input pins
are routed copies (`H_ROUTE`) of ports `req_in`, `ack_out`, `rst`. -/

theorem winDelay_held {lo hi : Nat} {x y : Trace} (H : WinDelay lo hi x y) (v : Bool) (a b : Nat)
    (hx : ∀ s, a ≤ s → s ≤ b → x s = v) : ∀ t, a + hi ≤ t → t ≤ b + lo → y t = v := by
  intro t h1 h2
  obtain ⟨s, hs1, hs2, e⟩ := H t (by omega)
  rw [e]; exact hx s (by omega) (by omega)

/-- **Follow-and-hold from the ports.** Ports `pa, pb, pr` reach the pins
`a, b, rst` through window routes; `M` bounds every route's maximum, `m` is
below every route's minimum. If the ports hold `a = v, b = !v, rst = 0` on
`[P, P + W]` with `W + m + 1 ≥ M + Dmax` (the pulse must cover the loop delay
PLUS the input-route skew), the C node output is `v` on
`[P + M + dhi, P + W + m + dlo]`. -/
theorem c2n_follow_hold_ports {a b rst O qp pa pb pr : Trace} {dlo dhi wlo whi : Nat}
    (L : Loop INIT_c2 a (fun t => !b t) rst O qp dlo dhi wlo whi)
    {alo ahi blo bhi rlo rhi : Nat}
    (Ra : WinDelay alo ahi pa a) (Rb : WinDelay blo bhi pb b) (Rr : WinDelay rlo rhi pr rst)
    (M m : Nat) (hM : ahi ≤ M ∧ bhi ≤ M ∧ rhi ≤ M) (hm : m ≤ alo ∧ m ≤ blo ∧ m ≤ rlo)
    (v : Bool) (P W : Nat) (hW : M + (dhi + whi) ≤ W + m + 1)
    (H_PORTS : ∀ s, P ≤ s → s ≤ P + W → pa s = v ∧ pb s = !v ∧ pr s = false) :
    ∀ t, P + M + dhi ≤ t → t ≤ P + W + m + dlo → O t = v := by
  have ha := winDelay_held Ra v P (P + W) (fun s h1 h2 => (H_PORTS s h1 h2).1)
  have hb := winDelay_held Rb (!v) P (P + W) (fun s h1 h2 => (H_PORTS s h1 h2).2.1)
  have hr := winDelay_held Rr false P (P + W) (fun s h1 h2 => (H_PORTS s h1 h2).2.2)
  have := c2n_follow_hold L v (P + M) (P + W + m)
    (fun s h1 h2 => ⟨ha s (by omega) (by omega), hb s (by omega) (by omega), hr s (by omega) (by omega)⟩)
    (fun s h1 h2 => hr s (by omega) (by omega))
    (fun s h1 h2 => Or.inl (ha s (by omega) (by omega)))
  exact this.1

/-! ## 3. Generic bridge: physical latch bit -> B's `LatchBit` -/

/-- The loop delay of a LUT-then-wire loop, chosen pointwise: at every `t` past
the maximum loop delay, the feedback pin shows the excitation `k t` ticks
earlier, `k t` within the summed windows. -/
theorem loop_k {e out p : Trace} {dlo dhi wlo whi : Nat}
    (H1 : WinDelay dlo dhi e out) (H2 : WinDelay wlo whi out p) (hpos : 1 ≤ dlo + wlo) :
    ∀ t, ∃ k, 1 ≤ k ∧ k ≤ dhi + whi ∧ (k ≤ t → p t = e (t - k)) := by
  intro t
  by_cases ht : dhi + whi ≤ t
  · obtain ⟨s, h1, h2, hs⟩ := winDelay_comp H1 H2 t ht
    refine ⟨t - s, by omega, by omega, fun _ => ?_⟩
    rw [show t - (t - s) = s by omega]; exact hs
  · exact ⟨t + 1, by omega, by omega, fun h => absurd h (by omega)⟩

/-- **Bridge (latch family) and B's `holds_value` on it.** `out` is the latch
LUT output, a window copy (`[dlo, dhi]`) of `bmux en d p` on the pins; `p` (its
feedback pin) a window copy (`[wlo, whi]`) of `out`; `d1, p1` are the other bit's
pins (unconstrained). With `L = dhi + whi`, B's `LatchBit L` is built from these
traces and `Latch.holds_value` gives: the excitation is `v` on `[s, T]`, the
LUT output on `[s + dhi, T + dlo]`. Binary traces: the `x` (edge-in-flight)
cases of `holds_value` are not exercised (C's `Behaves` is Boolean). -/
theorem latch_holds_bits {d en p d1 p1 out : Trace} {dlo dhi wlo whi : Nat}
    (H_LUT : WinDelay dlo dhi (fun t => Latch.bmux (en t) (d t) (p t)) out)
    (H_FB : WinDelay wlo whi out p) (hpos : 1 ≤ dlo + wlo)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → en t = false → s + (dhi + whi) ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → en t = true → d t = v) :
    (∀ t, s ≤ t → t ≤ T → Latch.bmux (en t) (d t) (p t) = v) ∧
    (∀ t, s + dhi ≤ t → t ≤ T + dlo → out t = v) := by
  have hk := loop_k H_LUT H_FB hpos
  let ld : Latch.LoopDelay (dhi + whi) :=
    ⟨fun t => Classical.choose (hk t), fun t => (Classical.choose_spec (hk t)).1,
     fun t => (Classical.choose_spec (hk t)).2.1⟩
  let b : Latch.LatchBit (dhi + whi) :=
    { d := fun t => K3.ofBool (d t), en := fun t => K3.ofBool (en t),
      p := fun t => K3.ofBool (p t), d1 := fun t => K3.ofBool (d1 t),
      p1 := fun t => K3.ofBool (p1 t),
      q := fun t => o5K Latch.PAIR [K3.ofBool (d t), K3.ofBool (en t), K3.ofBool (p t),
        K3.ofBool (d1 t), K3.ofBool (p1 t), .t],
      loop := ld,
      hlut := fun _ => rfl,
      hloop := by
        intro t hkt
        show K3.ofBool (p t) = o5K Latch.PAIR [_, _, _, _, _, _]
        rw [Latch.pair_o5_kleene, mux_ofBool]
        exact congrArg K3.ofBool ((Classical.choose_spec (hk t)).2.2 hkt) }
  have hq : ∀ t, b.q t = K3.ofBool (Latch.bmux (en t) (d t) (p t)) := by
    intro t; show o5K Latch.PAIR [_, _, _, _, _, _] = _
    rw [Latch.pair_o5_kleene, mux_ofBool]
  have hv := Latch.holds_value b (K3.ofBool v) s T
    (fun t h1 h2 hne => H_EN_OPEN t h1 h2 (by
      show en t = false
      cases he : en t
      · rfl
      · exact absurd (by show K3.ofBool (en t) = .t; rw [he]; rfl) hne))
    (fun t h1 h2 hne => by
      show K3.ofBool (d t) = K3.ofBool v
      have : en t = true := by
        cases he : en t
        · exact absurd (by show K3.ofBool (en t) = .f; rw [he]; rfl) hne
        · rfl
      rw [H_DATA t h1 h2 this])
  have hexc : ∀ t, s ≤ t → t ≤ T → Latch.bmux (en t) (d t) (p t) = v :=
    fun t h1 h2 => ofBool_inj ((hq t).symm.trans (hv t h1 h2))
  refine ⟨hexc, fun t h1 h2 => ?_⟩
  obtain ⟨s', ha, hb, e⟩ := H_LUT t (by omega)
  rw [e]; exact hexc s' (by omega) (by omega)

/-! ## 4. Per seed: the link C node (physical LUT 0, O6, on every seed) -/

section seeds
variable {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}

/-! ### Wiring facts read from the bits (decided). Port 7 = `req_in`, port 1 =
`ack_out`, port 8 = `rst`. -/

theorem ports_same : Formal.Net.FasmLink.S1.ports[7]? = some "req_in" ∧
    Formal.Net.FasmLink.S1.ports[1]? = some "ack_out" ∧
    Formal.Net.FasmLink.S1.ports[8]? = some "rst" ∧
    Formal.Net.FasmLink.S1.ports = Formal.Net.FasmLink.S2.ports ∧
    Formal.Net.FasmLink.S1.ports = Formal.Net.FasmLink.S3.ports ∧
    Formal.Net.FasmLink.S1.ports = Formal.Net.FasmLink.S4.ports := by decide

/-- The C node is LUT 0 / O6 on every seed (C's checked renaming `rho[0]`). -/
theorem cnode_rho : Formal.Net.FasmLink.S1.rho[0]? = some [.lut 0 .o6] ∧
    Formal.Net.FasmLink.S2.rho[0]? = some [.lut 0 .o6] ∧
    Formal.Net.FasmLink.S3.rho[0]? = some [.lut 0 .o6] ∧
    Formal.Net.FasmLink.S4.rho[0]? = some [.lut 0 .o6] := by decide

/-- Physical pin sources of the C node, per seed (A1..A6). -/
theorem cnode_pins :
    Formal.Net.FasmLink.S1.lut0.pins = [.port 8, .port 7, .port 1, .lut 0 .o6, .const false, .const false] ∧
    Formal.Net.FasmLink.S2.lut0.pins = [.lut 0 .o6, .port 1, .port 7, .const false, .port 8, .const false] ∧
    Formal.Net.FasmLink.S3.lut0.pins = [.port 8, .port 1, .const false, .lut 0 .o6, .port 7, .const false] ∧
    Formal.Net.FasmLink.S4.lut0.pins = [.port 8, .const false, .port 1, .lut 0 .o6, .port 7, .const false] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Physical functions (decided, 16 cases each, physical INIT on physical pins) -/

theorem c_fn_s1 : ∀ x0 x1 x2 x3 : Bool,
    Formal.Net.FasmLink.S1.lut0.fn .o6 [x0, x1, x2, x3, false, false] = exc INIT_c2n x1 x2 x3 x0 := by
  decide
theorem c_fn_s2 : ∀ x0 x1 x2 x4 : Bool,
    Formal.Net.FasmLink.S2.lut0.fn .o6 [x0, x1, x2, false, x4, false] = exc INIT_c2n x2 x1 x0 x4 := by
  decide
theorem c_fn_s3 : ∀ x0 x1 x3 x4 : Bool,
    Formal.Net.FasmLink.S3.lut0.fn .o6 [x0, x1, false, x3, x4, false] = exc INIT_c2n x4 x1 x3 x0 := by
  decide
theorem c_fn_s4 : ∀ x0 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S4.lut0.fn .o6 [x0, false, x2, x3, x4, false] = exc INIT_c2n x4 x2 x3 x0 := by
  decide

/-! ### The delay numbers, rfl-linked to C's generated `pinDelay` -/

theorem cfb_s1 : Formal.Net.FasmLink.S1.pinDelay[0]![3]! = (125, 445) := rfl
theorem cfb_s2 : Formal.Net.FasmLink.S2.pinDelay[0]![0]! = (211, 714) := rfl
theorem cfb_s3 : Formal.Net.FasmLink.S3.pinDelay[0]![3]! = (206, 836) := rfl
theorem cfb_s4 : Formal.Net.FasmLink.S4.pinDelay[0]![3]! = (124, 466) := rfl

/-! ### `Loop` on the bits, with numbers (LUT6 O6 window [45, 124] ps) -/

theorem cloop_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S1.pinDelay[0]![3]!) :
    Loop INIT_c2 (pin 0 1) (fun t => !pin 0 2 t) (pin 0 0) (out 0 .o6) (pin 0 3) 45 124 125 445 := by
  rw [cfb_s1] at H_DW
  have L := cnode_loop (iq := 3) (ia := 1) (ib := 2) (ir := 0) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S1.lut0.fn .o6
        [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 4 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s1])
    (by rw [H_DL, H_DW]; decide)
  rw [H_DL, H_DW] at L; exact L

theorem cloop_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 0 = Formal.Net.FasmLink.S2.pinDelay[0]![0]!) :
    Loop INIT_c2 (pin 0 2) (fun t => !pin 0 1 t) (pin 0 4) (out 0 .o6) (pin 0 0) 45 124 211 714 := by
  rw [cfb_s2] at H_DW
  have L := cnode_loop (iq := 0) (ia := 2) (ib := 1) (ir := 4) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S2.lut0.fn .o6
        [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 3 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s2])
    (by rw [H_DL, H_DW]; decide)
  rw [H_DL, H_DW] at L; exact L

theorem cloop_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S3.pinDelay[0]![3]!) :
    Loop INIT_c2 (pin 0 4) (fun t => !pin 0 1 t) (pin 0 0) (out 0 .o6) (pin 0 3) 45 124 206 836 := by
  rw [cfb_s3] at H_DW
  have L := cnode_loop (iq := 3) (ia := 4) (ib := 1) (ir := 0) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S3.lut0.fn .o6
        [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 2 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s3])
    (by rw [H_DL, H_DW]; decide)
  rw [H_DL, H_DW] at L; exact L

theorem cloop_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S4.pinDelay[0]![3]!) :
    Loop INIT_c2 (pin 0 4) (fun t => !pin 0 2 t) (pin 0 0) (out 0 .o6) (pin 0 3) 45 124 124 466 := by
  rw [cfb_s4] at H_DW
  have L := cnode_loop (iq := 3) (ia := 4) (ib := 2) (ir := 0) h rfl rfl
    (fun t => by
      show Formal.Net.FasmLink.S4.lut0.fn .o6
        [pin 0 0 t, pin 0 1 t, pin 0 2 t, pin 0 3 t, pin 0 4 t, pin 0 5 t] = _
      rw [h.H_TIE 0 _ 1 false rfl rfl t, h.H_TIE 0 _ 5 false rfl rfl t, c_fn_s4])
    (by rw [H_DL, H_DW]; decide)
  rw [H_DL, H_DW] at L; exact L

/-! ### `c2_follow_hold` on the bits: `req = v`, `ack_out = !v`, `rst = 0` at the
physical pins for `Dmax` ps set the routed C node to `v` from 124 ps on. -/

theorem c_follow_hold_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S1.pinDelay[0]![3]!)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + 569 → pin 0 1 s = v ∧ pin 0 2 s = !v ∧ pin 0 0 s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 0 s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 1 s = v ∨ pin 0 2 s = !v) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = v) ∧
    (∀ t, t0 + 569 ≤ t → t ≤ t2 + 170 → pin 0 3 t = v) :=
  c2n_follow_hold (cloop_s1 h H_DL H_DW) v t0 t2 H_PULSE H_NORST H_NOT_BOTH

theorem c_follow_hold_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 0 = Formal.Net.FasmLink.S2.pinDelay[0]![0]!)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + 838 → pin 0 2 s = v ∧ pin 0 1 s = !v ∧ pin 0 4 s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 4 s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 2 s = v ∨ pin 0 1 s = !v) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = v) ∧
    (∀ t, t0 + 838 ≤ t → t ≤ t2 + 256 → pin 0 0 t = v) :=
  c2n_follow_hold (cloop_s2 h H_DL H_DW) v t0 t2 H_PULSE H_NORST H_NOT_BOTH

theorem c_follow_hold_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S3.pinDelay[0]![3]!)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + 960 → pin 0 4 s = v ∧ pin 0 1 s = !v ∧ pin 0 0 s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 0 s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 4 s = v ∨ pin 0 1 s = !v) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = v) ∧
    (∀ t, t0 + 960 ≤ t → t ≤ t2 + 251 → pin 0 3 t = v) :=
  c2n_follow_hold (cloop_s3 h H_DL H_DW) v t0 t2 H_PULSE H_NORST H_NOT_BOTH

theorem c_follow_hold_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S4.pinDelay[0]![3]!)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + 590 → pin 0 4 s = v ∧ pin 0 2 s = !v ∧ pin 0 0 s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 0 s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → pin 0 4 s = v ∨ pin 0 2 s = !v) :
    (∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 0 .o6 t = v) ∧
    (∀ t, t0 + 590 ≤ t → t ≤ t2 + 169 → pin 0 3 t = v) :=
  c2n_follow_hold (cloop_s4 h H_DL H_DW) v t0 t2 H_PULSE H_NORST H_NOT_BOTH

/-! ### `c2_four_phase` on the bits. `H_ENV_LATENCY` becomes a concrete lower
bound on the environment's ack-to-input latency `E` (ps, at the pins):
524 / 793 / 915 / 545 for seeds 1..4. -/

theorem c_four_phase_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S1.pinDelay[0]![3]!)
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k) (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, pin 0 1 (c k) = V k ∧ pin 0 2 (c k) = !V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → pin 0 1 s = V k ∨ pin 0 2 s = !V k)
    (H_NORST : ∀ s, c 0 ≤ s → pin 0 0 s = false)
    (H_ACK : ∀ k s, c k ≤ s → (pin 0 1 s ≠ V k ∨ pin 0 2 s ≠ !V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ out 0 .o6 u = V k)
    (H_ENV_LATENCY : 524 ≤ E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + 45 → out 0 .o6 u = !V 0) :
    ∀ k, (∀ t, c k + 124 ≤ t → t + 1 ≤ c (k + 1) + 45 → out 0 .o6 t = V k) ∧
         (∀ t, c k + 569 ≤ t → t + 1 ≤ c (k + 1) + 170 → pin 0 3 t = V k) :=
  c2n_four_phase (cloop_s1 h H_DL H_DW) V c E H_ALT H_ORDER H_BOTH H_NEXT H_NORST H_ACK
    (by omega) H_RESET_DONE

theorem c_four_phase_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 0 = Formal.Net.FasmLink.S2.pinDelay[0]![0]!)
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k) (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, pin 0 2 (c k) = V k ∧ pin 0 1 (c k) = !V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → pin 0 2 s = V k ∨ pin 0 1 s = !V k)
    (H_NORST : ∀ s, c 0 ≤ s → pin 0 4 s = false)
    (H_ACK : ∀ k s, c k ≤ s → (pin 0 2 s ≠ V k ∨ pin 0 1 s ≠ !V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ out 0 .o6 u = V k)
    (H_ENV_LATENCY : 793 ≤ E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + 45 → out 0 .o6 u = !V 0) :
    ∀ k, (∀ t, c k + 124 ≤ t → t + 1 ≤ c (k + 1) + 45 → out 0 .o6 t = V k) ∧
         (∀ t, c k + 838 ≤ t → t + 1 ≤ c (k + 1) + 256 → pin 0 0 t = V k) :=
  c2n_four_phase (cloop_s2 h H_DL H_DW) V c E H_ALT H_ORDER H_BOTH H_NEXT H_NORST H_ACK
    (by omega) H_RESET_DONE

theorem c_four_phase_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S3.pinDelay[0]![3]!)
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k) (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, pin 0 4 (c k) = V k ∧ pin 0 1 (c k) = !V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → pin 0 4 s = V k ∨ pin 0 1 s = !V k)
    (H_NORST : ∀ s, c 0 ≤ s → pin 0 0 s = false)
    (H_ACK : ∀ k s, c k ≤ s → (pin 0 4 s ≠ V k ∨ pin 0 1 s ≠ !V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ out 0 .o6 u = V k)
    (H_ENV_LATENCY : 915 ≤ E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + 45 → out 0 .o6 u = !V 0) :
    ∀ k, (∀ t, c k + 124 ≤ t → t + 1 ≤ c (k + 1) + 45 → out 0 .o6 t = V k) ∧
         (∀ t, c k + 960 ≤ t → t + 1 ≤ c (k + 1) + 251 → pin 0 3 t = V k) :=
  c2n_four_phase (cloop_s3 h H_DL H_DW) V c E H_ALT H_ORDER H_BOTH H_NEXT H_NORST H_ACK
    (by omega) H_RESET_DONE

theorem c_four_phase_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DW : dw 0 3 = Formal.Net.FasmLink.S4.pinDelay[0]![3]!)
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k) (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, pin 0 4 (c k) = V k ∧ pin 0 2 (c k) = !V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → pin 0 4 s = V k ∨ pin 0 2 s = !V k)
    (H_NORST : ∀ s, c 0 ≤ s → pin 0 0 s = false)
    (H_ACK : ∀ k s, c k ≤ s → (pin 0 4 s ≠ V k ∨ pin 0 2 s ≠ !V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ out 0 .o6 u = V k)
    (H_ENV_LATENCY : 545 ≤ E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + 45 → out 0 .o6 u = !V 0) :
    ∀ k, (∀ t, c k + 124 ≤ t → t + 1 ≤ c (k + 1) + 45 → out 0 .o6 t = V k) ∧
         (∀ t, c k + 590 ≤ t → t + 1 ≤ c (k + 1) + 169 → pin 0 3 t = V k) :=
  c2n_four_phase (cloop_s4 h H_DL H_DW) V c E H_ALT H_ORDER H_BOTH H_NEXT H_NORST H_ACK
    (by omega) H_RESET_DONE


/-! ### Follow-and-hold from the PORTS, per seed. `H_DWALL`: every pin of the C
node has C's generated bounds. Port pulse widths needed (`W + 1`): 1646 / 2083 /
2137 / 1745 ps; they are dominated by the IOB-to-LUT input-route skew of this
test harness (ports at IOBs), not by the cell. -/

theorem c_follow_hold_ports_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DWALL : ∀ k, dw 0 k = Formal.Net.FasmLink.S1.pinDelay[0]![k]!)
    (v : Bool) (P : Nat)
    (H_PORTS : ∀ s, P ≤ s → s ≤ P + 1645 → ins 7 s = v ∧ ins 1 s = !v ∧ ins 8 s = false) :
    ∀ t, P + 1448 + 124 ≤ t → t ≤ P + 1645 + 371 + 45 → out 0 .o6 t = v := by
  have Ra := h.H_ROUTE 0 _ 1 (.port 7) rfl rfl (by intro v hv; cases hv)
  have Rb := h.H_ROUTE 0 _ 2 (.port 1) rfl rfl (by intro v hv; cases hv)
  have Rr := h.H_ROUTE 0 _ 0 (.port 8) rfl rfl (by intro v hv; cases hv)
  rw [H_DWALL] at Ra Rb Rr
  exact c2n_follow_hold_ports (cloop_s1 h H_DL (H_DWALL 3)) Ra Rb Rr 1448 371
    (by decide) (by decide) v P 1645 (by decide) H_PORTS

theorem c_follow_hold_ports_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DWALL : ∀ k, dw 0 k = Formal.Net.FasmLink.S2.pinDelay[0]![k]!)
    (v : Bool) (P : Nat)
    (H_PORTS : ∀ s, P ≤ s → s ≤ P + 2082 → ins 7 s = v ∧ ins 1 s = !v ∧ ins 8 s = false) :
    ∀ t, P + 1553 + 124 ≤ t → t ≤ P + 2082 + 308 + 45 → out 0 .o6 t = v := by
  have Ra := h.H_ROUTE 0 _ 2 (.port 7) rfl rfl (by intro v hv; cases hv)
  have Rb := h.H_ROUTE 0 _ 1 (.port 1) rfl rfl (by intro v hv; cases hv)
  have Rr := h.H_ROUTE 0 _ 4 (.port 8) rfl rfl (by intro v hv; cases hv)
  rw [H_DWALL] at Ra Rb Rr
  exact c2n_follow_hold_ports (cloop_s2 h H_DL (H_DWALL 0)) Ra Rb Rr 1553 308
    (by decide) (by decide) v P 2082 (by decide) H_PORTS

theorem c_follow_hold_ports_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DWALL : ∀ k, dw 0 k = Formal.Net.FasmLink.S3.pinDelay[0]![k]!)
    (v : Bool) (P : Nat)
    (H_PORTS : ∀ s, P ≤ s → s ≤ P + 2136 → ins 7 s = v ∧ ins 1 s = !v ∧ ins 8 s = false) :
    ∀ t, P + 1466 + 124 ≤ t → t ≤ P + 2136 + 289 + 45 → out 0 .o6 t = v := by
  have Ra := h.H_ROUTE 0 _ 4 (.port 7) rfl rfl (by intro v hv; cases hv)
  have Rb := h.H_ROUTE 0 _ 1 (.port 1) rfl rfl (by intro v hv; cases hv)
  have Rr := h.H_ROUTE 0 _ 0 (.port 8) rfl rfl (by intro v hv; cases hv)
  rw [H_DWALL] at Ra Rb Rr
  exact c2n_follow_hold_ports (cloop_s3 h H_DL (H_DWALL 3)) Ra Rb Rr 1466 289
    (by decide) (by decide) v P 2136 (by decide) H_PORTS

theorem c_follow_hold_ports_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 0 = (45, 124)) (H_DWALL : ∀ k, dw 0 k = Formal.Net.FasmLink.S4.pinDelay[0]![k]!)
    (v : Bool) (P : Nat)
    (H_PORTS : ∀ s, P ≤ s → s ≤ P + 1744 → ins 7 s = v ∧ ins 1 s = !v ∧ ins 8 s = false) :
    ∀ t, P + 1443 + 124 ≤ t → t ≤ P + 1744 + 288 + 45 → out 0 .o6 t = v := by
  have Ra := h.H_ROUTE 0 _ 4 (.port 7) rfl rfl (by intro v hv; cases hv)
  have Rb := h.H_ROUTE 0 _ 2 (.port 1) rfl rfl (by intro v hv; cases hv)
  have Rr := h.H_ROUTE 0 _ 0 (.port 8) rfl rfl (by intro v hv; cases hv)
  rw [H_DWALL] at Ra Rb Rr
  exact c2n_follow_hold_ports (cloop_s4 h H_DL (H_DWALL 3)) Ra Rb Rr 1443 288
    (by decide) (by decide) v P 1744 (by decide) H_PORTS

/-! ### Negative controls: the per-seed function checks can fail.
The logical pin order on the physical LUT (ignoring the placer's permutation)
is not the C node; d0 and d1 swapped is not latch bit q0. -/

theorem c_fn_unpermuted_fails_s1 : ¬ ∀ x0 x1 x2 x3 : Bool,
    Formal.Net.FasmLink.S1.lut0.fn .o6 [x0, x1, x2, x3, false, false] = exc INIT_c2n x0 x1 x2 x3 := by
  decide
theorem l_fn_swap_fails_s1 : ¬ ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S1.lut1.fn .o5 [x0, x1, x2, x3, x4, true] = Latch.bmux x2 x3 x1 := by
  decide

/-! ## 5. Per seed: latch bit q0 (O5 of the fractured pair LUT6_2)

Physical latch-pair LUT and its pins (A1..A6), from C's `rho[1][0]` = O5:
* S1: LUT 1 `[q1, q0, en, d1, d0, 1]`, q0 feedback A2;
* S2: LUT 1 `[d1, q0, d0, en, q1, 1]`, q0 feedback A2;
* S3: LUT 2 `[q1, d0, d1, en, q0, 1]`, q0 feedback A5;
* S4: LUT 1 `[q1, en, d1, d0, q0, 1]`, q0 feedback A5.
`d0` = port 2 (`data_in[0]`), `d1` = port 3, `en` = LUT 0 O6 (the C node). -/

theorem latch_rho : Formal.Net.FasmLink.S1.rho[1]? = some [.lut 1 .o5, .lut 1 .o6, .lut 2 .o6] ∧
    Formal.Net.FasmLink.S2.rho[1]? = some [.lut 1 .o5, .lut 1 .o6, .lut 2 .o6] ∧
    Formal.Net.FasmLink.S3.rho[1]? = some [.lut 2 .o5, .lut 2 .o6, .lut 1 .o6] ∧
    Formal.Net.FasmLink.S4.rho[1]? = some [.lut 1 .o5, .lut 1 .o6, .lut 2 .o6] := by decide

theorem latch_pins :
    Formal.Net.FasmLink.S1.lut1.pins = [.lut 1 .o6, .lut 1 .o5, .lut 0 .o6, .port 3, .port 2, .const true] ∧
    Formal.Net.FasmLink.S2.lut1.pins = [.port 3, .lut 1 .o5, .port 2, .lut 0 .o6, .lut 1 .o6, .const true] ∧
    Formal.Net.FasmLink.S3.lut2.pins = [.lut 2 .o6, .port 2, .port 3, .lut 0 .o6, .lut 2 .o5, .const true] ∧
    Formal.Net.FasmLink.S4.lut1.pins = [.lut 1 .o6, .lut 0 .o6, .port 3, .port 2, .lut 1 .o5, .const true] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem l_fn_s1 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S1.lut1.fn .o5 [x0, x1, x2, x3, x4, true] = Latch.bmux x2 x4 x1 := by decide
theorem l_fn_s2 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S2.lut1.fn .o5 [x0, x1, x2, x3, x4, true] = Latch.bmux x3 x2 x1 := by decide
theorem l_fn_s3 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S3.lut2.fn .o5 [x0, x1, x2, x3, x4, true] = Latch.bmux x3 x1 x4 := by decide
theorem l_fn_s4 : ∀ x0 x1 x2 x3 x4 : Bool,
    Formal.Net.FasmLink.S4.lut1.fn .o5 [x0, x1, x2, x3, x4, true] = Latch.bmux x1 x3 x4 := by decide

theorem lfb_s1 : Formal.Net.FasmLink.S1.pinDelay[1]![1]! = (261, 872) := rfl
theorem lfb_s2 : Formal.Net.FasmLink.S2.pinDelay[1]![1]! = (261, 872) := rfl
theorem lfb_s3 : Formal.Net.FasmLink.S3.pinDelay[2]![4]! = (123, 444) := rfl
theorem lfb_s4 : Formal.Net.FasmLink.S4.pinDelay[1]![4]! = (123, 447) := rfl

/-- **`holds_value` for latch bit q0 on the seed-1 bits.** LUT6_2 window
`[42, 157]` ps (O5 envelope, `H_DL`), q0 feedback route `[261, 872]` (`H_DW`):
loop bound `L = 1029` ps. If on `[s, T]` the enable pin (A3) is low only after
`s + 1029` (open for a full loop delay) and the data pin (A5) is `v` whenever
the enable pin is high, then the physical O5 is `v` on `[s + 157, T + 42]`. -/
theorem latch_q0_s1 (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DW : dw 1 1 = Formal.Net.FasmLink.S1.pinDelay[1]![1]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 2 t = false → s + 1029 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 2 t = true → pin 1 4 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o5 t = v := by
  rw [lfb_s1] at H_DW
  have hl := h.H_LUT 1 _ .o5 rfl
  have hf := h.H_ROUTE 1 _ 1 (.lut 1 .o5) rfl rfl (by intro v hv; cases hv)
  have e : (fun t => Formal.Net.FasmLink.S1.lut1.fn .o5 ((List.range 6).map (fun k => pin 1 k t))) =
      (fun t => Latch.bmux (pin 1 2 t) (pin 1 4 t) (pin 1 1 t)) := by
    funext t
    show Formal.Net.FasmLink.S1.lut1.fn .o5
      [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
    rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s1]
  rw [e, H_DL] at hl; rw [H_DW] at hf
  exact (latch_holds_bits (d1 := pin 1 3) (p1 := pin 1 0) hl hf (by decide) v s T
    H_EN_OPEN H_DATA).2

theorem latch_q0_s2 (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DW : dw 1 1 = Formal.Net.FasmLink.S2.pinDelay[1]![1]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 3 t = false → s + 1029 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 3 t = true → pin 1 2 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o5 t = v := by
  rw [lfb_s2] at H_DW
  have hl := h.H_LUT 1 _ .o5 rfl
  have hf := h.H_ROUTE 1 _ 1 (.lut 1 .o5) rfl rfl (by intro v hv; cases hv)
  have e : (fun t => Formal.Net.FasmLink.S2.lut1.fn .o5 ((List.range 6).map (fun k => pin 1 k t))) =
      (fun t => Latch.bmux (pin 1 3 t) (pin 1 2 t) (pin 1 1 t)) := by
    funext t
    show Formal.Net.FasmLink.S2.lut1.fn .o5
      [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
    rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s2]
  rw [e, H_DL] at hl; rw [H_DW] at hf
  exact (latch_holds_bits (d1 := pin 1 0) (p1 := pin 1 4) hl hf (by decide) v s T
    H_EN_OPEN H_DATA).2

theorem latch_q0_s3 (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw)
    (H_DL : dl 2 = (42, 157)) (H_DW : dw 2 4 = Formal.Net.FasmLink.S3.pinDelay[2]![4]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 2 3 t = false → s + 601 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 2 3 t = true → pin 2 1 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 2 .o5 t = v := by
  rw [lfb_s3] at H_DW
  have hl := h.H_LUT 2 _ .o5 rfl
  have hf := h.H_ROUTE 2 _ 4 (.lut 2 .o5) rfl rfl (by intro v hv; cases hv)
  have e : (fun t => Formal.Net.FasmLink.S3.lut2.fn .o5 ((List.range 6).map (fun k => pin 2 k t))) =
      (fun t => Latch.bmux (pin 2 3 t) (pin 2 1 t) (pin 2 4 t)) := by
    funext t
    show Formal.Net.FasmLink.S3.lut2.fn .o5
      [pin 2 0 t, pin 2 1 t, pin 2 2 t, pin 2 3 t, pin 2 4 t, pin 2 5 t] = _
    rw [h.H_TIE 2 _ 5 true rfl rfl t, l_fn_s3]
  rw [e, H_DL] at hl; rw [H_DW] at hf
  exact (latch_holds_bits (d1 := pin 2 2) (p1 := pin 2 0) hl hf (by decide) v s T
    H_EN_OPEN H_DATA).2

theorem latch_q0_s4 (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw)
    (H_DL : dl 1 = (42, 157)) (H_DW : dw 1 4 = Formal.Net.FasmLink.S4.pinDelay[1]![4]!)
    (v : Bool) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = false → s + 604 ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → pin 1 1 t = true → pin 1 3 t = v) :
    ∀ t, s + 157 ≤ t → t ≤ T + 42 → out 1 .o5 t = v := by
  rw [lfb_s4] at H_DW
  have hl := h.H_LUT 1 _ .o5 rfl
  have hf := h.H_ROUTE 1 _ 4 (.lut 1 .o5) rfl rfl (by intro v hv; cases hv)
  have e : (fun t => Formal.Net.FasmLink.S4.lut1.fn .o5 ((List.range 6).map (fun k => pin 1 k t))) =
      (fun t => Latch.bmux (pin 1 1 t) (pin 1 3 t) (pin 1 4 t)) := by
    funext t
    show Formal.Net.FasmLink.S4.lut1.fn .o5
      [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
    rw [h.H_TIE 1 _ 5 true rfl rfl t, l_fn_s4]
  rw [e, H_DL] at hl; rw [H_DW] at hf
  exact (latch_holds_bits (d1 := pin 1 2) (p1 := pin 1 0) hl hf (by decide) v s T
    H_EN_OPEN H_DATA).2

end seeds

end Formal.Cells.OnNetlistTimed
