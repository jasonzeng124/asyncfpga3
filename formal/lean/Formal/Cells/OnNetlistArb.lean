import Formal.Core.LutList
import Formal.Cells.CElemTiming
import Formal.Cells.ArbA0Fork
import Formal.Cells.ArbHeldTimed
import Formal.Cells.ArbHeldTimed2
import Formal.Net.Fasm.Basic
import Formal.Net.FasmLink.S1
import Formal.Net.FasmLink.S2
import Formal.Net.FasmLink.S3
import Formal.Net.FasmLink.S4

/-!
# Probe Bt3: the arbiter's timed theorems on the routed bits (link_arb, 4 seeds)

Shard B x shard C. Notes: `formal/notes/B-on-netlist-arb.md`.

The physical side is C-11b's gate relations `Formal.Net.Fasm.Behaves` on C-11c's
netlists read back from the four routed `link_arb` bitstreams
(`Formal.Net.FasmLink.S1..S4`; nextpnr sha256 9c732bc6303458df, `toolchain.sh`
ok, as stamped by `fasm2lean2/check.sh`). The routed `bd_arbiter` is four LUTs:
`ustate` (LUT6_2, O6 = q, O5 = R0), `ugrant` (LUT6_2, O5 = g1, O6 = g2),
`ua1`, `ua2` (`bd_c2`, LUT6). Which physical LUT and pin carries which logical
net is probe Bp's `PinAssign` (proved there from the bits); here the same
wiring is re-checked by `rfl` on C's `PLut.pins`.

## 1. The bridge for the A0 fork (7g)

* `fork_safe_win` (abstract): the positive direction of 7g's
  `no_early_ack_iff`, lifted from fixed transport delays to C/B's WINDOW
  channel `WinDelay` (the delay may vary per tick inside `[lo, hi]`): if the
  A0 branch into `ua_k` is at most `hi_late`, and the chain
  A0 -> ustate -> q -> ugrant -> g_k -> ua_k is at least
  `lo_early = lo(A0->ustate pin) + lo(ustate) + lo(q->ugrant pin) +
  lo(ugrant) + lo(g_k->ua_k pin)`, then with `hi_late <= lo_early` the ack
  `A_k` never rises. `ua_k`'s own window drops out (both its inputs are read at
  the same instant by the LUT function).
* `fork_safe_net` (bridge): the same, from `Behaves` on ANY `PNet`, for LUTs
  whose physical function on their physical pins is `ustate`/`ugrant`/`bd_c2`
  (hypotheses `hfn*`, decided per seed) and whose pins are routed as the
  arbiter wires them.

## 2. Per seed

* `fn_*`: the physical INIT on the physical pins, ties and steady requests
  substituted, is 7g's `F1/F2`, `G1/G2`, `cel` (decided).
* `fork_c{1,2}_s{n}_{slow,fast}`: no early ack on the bits, under C's
  `Behaves` with every window at ONE die corner (H_DIE_SLOW / H_DIE_FAST).
* `box7g_c{1,2}_s{n}_{full,unshared}`: in the independent-box reading
  (H_INDEP: each delay anywhere in prjxray [fast_min, slow_max + Elmore]),
  7g's `client{1,2}_box` says SOME delay choice in the box acknowledges early
  (margin negative on 8/8, with or without the shared-prefix credit).
* `rt_s{n}_{box,slow,fast}`: 7h/7j's RT1/RT2 (and the mirror RT1b/RT2b, and
  7g's A0Fork/A0Fork2 in arc form) for every delay record in the routed
  windows, given a server minimum response `smin` (H_SERVER_MIN, the server is
  a pad here) at least the number each seed needs.

Core Lean only; proofs are `omega`, strong induction and `decide`.
-/

namespace Formal.Cells.OnNetlistArb
open Formal.Cells Formal.Cells.CElemTiming Formal.Net.Fasm
open Formal.Cells.ArbA0Fork (cel cel_eq F1 F2 G1 G2 F1_hold F2_hold G1_vals G2_vals)

/-! ## 1. Window-channel lemmas -/

/-- A window copy of a trace that is `v` before `T` (and is `v` before the
settle time `Ts`, where the window constrains nothing yet) is `v` before
`T + lo`. -/
theorem win_before {lo hi Ts T : Nat} {x y : Trace} (H : WinDelay lo hi x y) (hTs : hi ≤ Ts)
    (v : Bool) (hinit : ∀ t, t < Ts → y t = v) (hx : ∀ s, s < T → x s = v) :
    ∀ t, t < T + lo → y t = v := by
  intro t ht
  by_cases h : t < Ts
  · exact hinit t h
  · obtain ⟨s, _, h2, e⟩ := H t (by omega)
    rw [e]; exact hx s (by omega)

/-- A window copy of a single falling step at `T0` can be high only before
`T0 + hi`. -/
theorem win_step_late {lo hi Ts T0 : Nat} {x y : Trace} (H : WinDelay lo hi x y)
    (hTs : hi ≤ Ts) (hT : Ts ≤ T0) (hx : ∀ s, x s = decide (s < T0)) :
    ∀ t, y t = true → t < T0 + hi := by
  intro t ht
  by_cases h : t < Ts
  · omega
  · obtain ⟨s, h1, _, e⟩ := H t (by omega)
    rw [e, hx] at ht
    have := of_decide_eq_true ht
    omega

/-- **7g's fork condition, positive direction, on window channels.**
Traces: `a0` the A0 net at its driver (one falling step at `T0`,
H_A0_FALL); `aS`/`aC` the A0 pins of ustate / ua_k; `qO` ustate's output,
`qF`/`qG` its feedback pin and ugrant's q pin; `gO` ugrant's grant output,
`gC` ua_k's grant pin; `AO` ua_k's output, `AF` its feedback pin. Every wire
and LUT is a `WinDelay` with its own window. H_SETTLED: before `Ts` (the
held state, at least every window's maximum before A0 falls) the traces carry
the held values. Conclusion: `A_k` never rises, if `hi(A0 -> ua_k) <= lo(early
chain)`. -/
theorem fork_safe_win {F : Bool → Bool → Bool} {G : Bool → Bool} {v : Bool}
    {a0 aS qO qF qG gO gC aC AO AF : Trace}
    {sL sH uL uH fL fH qL qH gL gH cL cH aL aH kL kH bL bH Ts T0 : Nat}
    (hF : ∀ b, F b true = b) (hG : G (!v) = false)
    (H_A0 : ∀ t, a0 t = decide (t < T0))
    (W_aS : WinDelay sL sH a0 aS)
    (W_ust : WinDelay uL uH (fun t => F (qF t) (aS t)) qO)
    (W_qF : WinDelay fL fH qO qF)
    (W_qG : WinDelay qL qH qO qG)
    (W_ug : WinDelay gL gH (fun t => G (qG t)) gO)
    (W_gC : WinDelay cL cH gO gC)
    (W_aC : WinDelay aL aH a0 aC)
    (W_ua : WinDelay kL kH (fun t => cel (gC t) (aC t) (AF t)) AO)
    (W_AF : WinDelay bL bH AO AF)
    (H_TS : sH ≤ Ts ∧ uH ≤ Ts ∧ fH ≤ Ts ∧ qH ≤ Ts ∧ gH ≤ Ts ∧ cH ≤ Ts ∧ aH ≤ Ts ∧
      kH ≤ Ts ∧ bH ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → aS t = true ∧ qO t = !v ∧ qF t = !v ∧ qG t = !v ∧
      gO t = false ∧ gC t = false ∧ AO t = false ∧ AF t = false)
    (H_LOOP : 1 ≤ uL + fL ∧ 1 ≤ kL + bL)
    (H_FORK : aH ≤ sL + uL + qL + gL + cL) :
    ∀ t, AO t = false := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := H_TS
  obtain ⟨l1, l2⟩ := H_LOOP
  have e1 : ∀ t, t < T0 + sL → aS t = true :=
    win_before W_aS t1 true (fun t h => (H_SETTLED t h).1)
      (fun s hs => by rw [H_A0]; exact decide_eq_true hs)
  have e2 : ∀ t, t < T0 + sL + uL → qO t = !v := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      intro ht
      by_cases h : t < Ts
      · exact (H_SETTLED t h).2.1
      · obtain ⟨s, h1, h2, e⟩ := W_ust t (by omega)
        rw [e]
        show F (qF s) (aS s) = !v
        rw [e1 s (by omega), hF]
        by_cases h' : s < Ts
        · exact (H_SETTLED s h').2.2.1
        · obtain ⟨s', h3, h4, e'⟩ := W_qF s (by omega)
          rw [e']; exact ih s' (by omega) (by omega)
  have e3 : ∀ t, t < T0 + sL + uL + qL → qG t = !v :=
    win_before W_qG t4 (!v) (fun t h => (H_SETTLED t h).2.2.2.1) e2
  have e4 : ∀ t, t < T0 + sL + uL + qL + gL → gO t = false :=
    win_before W_ug t5 false (fun t h => (H_SETTLED t h).2.2.2.2.1)
      (fun s hs => by show G (qG s) = false; rw [e3 s hs, hG])
  have e5 : ∀ t, t < T0 + sL + uL + qL + gL + cL → gC t = false :=
    win_before W_gC t6 false (fun t h => (H_SETTLED t h).2.2.2.2.2.1) e4
  have e6 := win_step_late W_aC t7 t10 H_A0
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    by_cases h : t < Ts
    · exact (H_SETTLED t h).2.2.2.2.2.2.1
    · obtain ⟨s, h1, h2, e⟩ := W_ua t (by omega)
      rw [e]
      show cel (gC s) (aC s) (AF s) = false
      have hAF : AF s = false := by
        by_cases h' : s < Ts
        · exact (H_SETTLED s h').2.2.2.2.2.2.2
        · obtain ⟨s', h3, h4, e'⟩ := W_AF s (by omega)
          rw [e']; exact ih s' (by omega)
      rw [hAF, cel_eq]
      cases hg : gC s
      · simp
      · have hs : ¬ s < T0 + sL + uL + qL + gL + cL := by
          intro hh; rw [e5 s hh] at hg; cases hg
        cases ha : aC s
        · simp
        · have := e6 s ha
          omega

/-! ## 2. Bridge: C's `Behaves` -> `fork_safe_win` -/

/-- **Bridge (arbiter fork).** In any physical net satisfying C's gate
relations, take LUTs `iS` (ustate), `iG` (ugrant, grant on output `og`) and
`iA` (ua_k) whose physical functions on their physical pins are `F`, `G`,
`cel` of the named pins (`hfn*`), wired as the arbiter wires them (`h*`: q
feedback, A0 from port `p0` into ustate and ua_k, q into ugrant, the grant into
ua_k, ua_k's feedback). If A0 falls once at `T0` at its port, the held state
is settled before `Ts`, both loops are positive and
`hi(A0 -> ua_k pin) <= lo(A0 -> ustate pin) + lo(ustate) + lo(q -> ugrant pin)
+ lo(ugrant) + lo(grant -> ua_k pin)`, then ua_k's output never rises. -/
theorem fork_safe_net {N : PNet} {ins : Nat → Trace} {out : Nat → LOut → Trace}
    {pin : Nat → Nat → Trace} {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
    (h : Behaves N ins out pin dl dw)
    {F : Bool → Bool → Bool} {G : Bool → Bool} {v : Bool}
    (hF : ∀ b, F b true = b) (hG : G (!v) = false)
    {iS iG iA p0 sq sa gq ag aa af : Nat} {og : LOut} {LS LG LA : PLut}
    (hLS : N.luts[iS]? = some LS) (hLG : N.luts[iG]? = some LG) (hLA : N.luts[iA]? = some LA)
    (hsq : LS.pins[sq]? = some (.lut iS .o6)) (hsa : LS.pins[sa]? = some (.port p0))
    (hgq : LG.pins[gq]? = some (.lut iS .o6)) (hag : LA.pins[ag]? = some (.lut iG og))
    (haa : LA.pins[aa]? = some (.port p0)) (haf : LA.pins[af]? = some (.lut iA .o6))
    (hfnS : ∀ t, LS.fn .o6 ((List.range 6).map (fun k => pin iS k t)) =
      F (pin iS sq t) (pin iS sa t))
    (hfnG : ∀ t, LG.fn og ((List.range 6).map (fun k => pin iG k t)) = G (pin iG gq t))
    (hfnA : ∀ t, LA.fn .o6 ((List.range 6).map (fun k => pin iA k t)) =
      cel (pin iA ag t) (pin iA aa t) (pin iA af t))
    {T0 Ts : Nat} (H_A0 : ∀ t, ins p0 t = decide (t < T0))
    (H_TS : (dw iS sa).2 ≤ Ts ∧ (dl iS).2 ≤ Ts ∧ (dw iS sq).2 ≤ Ts ∧ (dw iG gq).2 ≤ Ts ∧
      (dl iG).2 ≤ Ts ∧ (dw iA ag).2 ≤ Ts ∧ (dw iA aa).2 ≤ Ts ∧ (dl iA).2 ≤ Ts ∧
      (dw iA af).2 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin iS sa t = true ∧ out iS .o6 t = !v ∧ pin iS sq t = !v ∧
      pin iG gq t = !v ∧ out iG og t = false ∧ pin iA ag t = false ∧ out iA .o6 t = false ∧
      pin iA af t = false)
    (H_LOOP : 1 ≤ (dl iS).1 + (dw iS sq).1 ∧ 1 ≤ (dl iA).1 + (dw iA af).1)
    (H_FORK : (dw iA aa).2 ≤ (dw iS sa).1 + (dl iS).1 + (dw iG gq).1 + (dl iG).1 + (dw iA ag).1) :
    ∀ t, out iA .o6 t = false := by
  have nc : ∀ (i : Nat) (o : LOut) (w : Bool), (Src.lut i o) ≠ .const w := by
    intro i o w hh; cases hh
  have ncp : ∀ w : Bool, (Src.port p0) ≠ .const w := by intro w hh; cases hh
  have WS := h.H_LUT iS LS .o6 hLS
  rw [show (fun t => LS.fn .o6 ((List.range 6).map (fun k => pin iS k t))) =
    (fun t => F (pin iS sq t) (pin iS sa t)) from funext hfnS] at WS
  have WG := h.H_LUT iG LG og hLG
  rw [show (fun t => LG.fn og ((List.range 6).map (fun k => pin iG k t))) =
    (fun t => G (pin iG gq t)) from funext hfnG] at WG
  have WA := h.H_LUT iA LA .o6 hLA
  rw [show (fun t => LA.fn .o6 ((List.range 6).map (fun k => pin iA k t))) =
    (fun t => cel (pin iA ag t) (pin iA aa t) (pin iA af t)) from funext hfnA] at WA
  exact fork_safe_win hF hG H_A0
    (h.H_ROUTE iS LS sa _ hLS hsa ncp) WS (h.H_ROUTE iS LS sq _ hLS hsq (nc _ _))
    (h.H_ROUTE iG LG gq _ hLG hgq (nc _ _)) WG (h.H_ROUTE iA LA ag _ hLA hag (nc _ _))
    (h.H_ROUTE iA LA aa _ hLA haa ncp) WA (h.H_ROUTE iA LA af _ hLA haf (nc _ _))
    H_TS H_SETTLED H_LOOP H_FORK

/-! ## 3. Per seed: wiring, physical functions, fork theorems -/

section perseed
variable {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
  {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}

/-! ### Seed 1: ustate = LUT 3, ugrant = LUT 5, ua1 = LUT 4, ua2 = LUT 6 -/

theorem wiring_s1 :
    Formal.Net.FasmLink.S1.lut3.pins = [.port 8, .port 0, .port 5, .port 6, .lut 3 .o6, .const true] ∧
    Formal.Net.FasmLink.S1.lut4.pins = [.port 8, .lut 5 .o5, .port 0, .const false, .lut 4 .o6, .const false] ∧
    Formal.Net.FasmLink.S1.lut5.pins = [.port 5, .const false, .const true, .port 6, .lut 3 .o6, .const true] ∧
    Formal.Net.FasmLink.S1.lut6.pins = [.port 8, .port 0, .lut 6 .o6, .lut 5 .o6, .const false, .const false] ∧
    True := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The H_INDEP (box) windows of the fork pins are C's generated `pinDelay` (rfl):
A0->ustate, q fb, q->ugrant, then (g, A0, fb) of ua1 and of ua2. -/
theorem pinDelay_fork_s1 :
    Formal.Net.FasmLink.S1.pinDelay[3]![1]! = (422, 1391) ∧
    Formal.Net.FasmLink.S1.pinDelay[3]![4]! = (76, 288) ∧
    Formal.Net.FasmLink.S1.pinDelay[5]![4]! = (122, 429) ∧
    Formal.Net.FasmLink.S1.pinDelay[4]![1]! = (209, 677) ∧
    Formal.Net.FasmLink.S1.pinDelay[4]![2]! = (356, 1283) ∧
    Formal.Net.FasmLink.S1.pinDelay[4]![4]! = (71, 276) ∧
    Formal.Net.FasmLink.S1.pinDelay[6]![3]! = (176, 651) ∧
    Formal.Net.FasmLink.S1.pinDelay[6]![1]! = (419, 1443) ∧
    Formal.Net.FasmLink.S1.pinDelay[6]![2]! = (195, 677) := by
  decide

theorem fn_ust_c1_s1 : ∀ q a : Bool, Formal.Net.FasmLink.S1.lut3.fn .o6 [false, a, true, false, q, true] = F1 q a := by decide
theorem fn_ug_c1_s1 : ∀ q : Bool, Formal.Net.FasmLink.S1.lut5.fn .o5 [true, false, true, false, q, true] = G1 q := by decide
theorem fn_ua1_s1 : ∀ g a f : Bool, Formal.Net.FasmLink.S1.lut4.fn .o6 [false, g, a, false, f, false] = cel g a f := by decide

/-- Seed 1, client 1, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2084 - 1283 = +801` ps. -/
theorem fork_c1_s1_slow (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 3 = (93, 157) ∧ dl 5 = (93, 157) ∧ dl 4 = (100, 124) ∧
      dw 3 1 = (1049, 1391) ∧ dw 3 4 = (216, 288) ∧ dw 5 4 = (325, 429) ∧
      dw 4 1 = (524, 677) ∧ dw 4 2 = (951, 1283) ∧ dw 4 4 = (205, 276))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 2 t = true ∧ pin 3 3 t = false ∧ pin 3 0 t = false ∧
      pin 5 0 t = true ∧ pin 5 3 t = false ∧ pin 4 0 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !true ∧ pin 3 4 t = !true ∧
      pin 5 4 t = !true ∧ out 5 .o5 t = false ∧ pin 4 1 t = false ∧ out 4 .o6 t = false ∧
      pin 4 4 t = false) :
    ∀ t, out 4 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 3) (iG := 5) (iA := 4) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 1) (aa := 2) (af := 4) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S1.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c1_s1 _ _
  · intro t
    show Formal.Net.FasmLink.S1.lut5.fn .o5 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 2 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c1_s1 _
  · intro t
    show Formal.Net.FasmLink.S1.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 4 _ 3 false rfl rfl t, h.H_TIE 4 _ 5 false rfl rfl t]
    exact fn_ua1_s1 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 1, client 1, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 837 - 577 = +260` ps. -/
theorem fork_c1_s1_fast (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 3 = (42, 63) ∧ dl 5 = (42, 63) ∧ dl 4 = (45, 56) ∧
      dw 3 1 = (422, 644) ∧ dw 3 4 = (76, 119) ∧ dw 5 4 = (122, 184) ∧
      dw 4 1 = (209, 290) ∧ dw 4 2 = (356, 577) ∧ dw 4 4 = (71, 114))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 2 t = true ∧ pin 3 3 t = false ∧ pin 3 0 t = false ∧
      pin 5 0 t = true ∧ pin 5 3 t = false ∧ pin 4 0 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !true ∧ pin 3 4 t = !true ∧
      pin 5 4 t = !true ∧ out 5 .o5 t = false ∧ pin 4 1 t = false ∧ out 4 .o6 t = false ∧
      pin 4 4 t = false) :
    ∀ t, out 4 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 3) (iG := 5) (iA := 4) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 1) (aa := 2) (af := 4) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S1.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c1_s1 _ _
  · intro t
    show Formal.Net.FasmLink.S1.lut5.fn .o5 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 2 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c1_s1 _
  · intro t
    show Formal.Net.FasmLink.S1.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 4 _ 3 false rfl rfl t, h.H_TIE 4 _ 5 false rfl rfl t]
    exact fn_ua1_s1 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

theorem fn_ust_c2_s1 : ∀ q a : Bool, Formal.Net.FasmLink.S1.lut3.fn .o6 [false, a, false, true, q, true] = F2 q a := by decide
theorem fn_ug_c2_s1 : ∀ q : Bool, Formal.Net.FasmLink.S1.lut5.fn .o6 [false, false, true, true, q, true] = G2 q := by decide
theorem fn_ua2_s1 : ∀ g a f : Bool, Formal.Net.FasmLink.S1.lut6.fn .o6 [false, a, f, g, false, false] = cel g a f := by decide

/-- Seed 1, client 2, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2063 - 1443 = +620` ps. -/
theorem fork_c2_s1_slow (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 3 = (93, 157) ∧ dl 5 = (93, 157) ∧ dl 6 = (100, 124) ∧
      dw 3 1 = (1049, 1391) ∧ dw 3 4 = (216, 288) ∧ dw 5 4 = (325, 429) ∧
      dw 6 3 = (503, 651) ∧ dw 6 1 = (1080, 1443) ∧ dw 6 2 = (519, 677))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 2 t = false ∧ pin 3 3 t = true ∧ pin 3 0 t = false ∧
      pin 5 0 t = false ∧ pin 5 3 t = true ∧ pin 6 0 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !false ∧ pin 3 4 t = !false ∧
      pin 5 4 t = !false ∧ out 5 .o6 t = false ∧ pin 6 3 t = false ∧ out 6 .o6 t = false ∧
      pin 6 2 t = false) :
    ∀ t, out 6 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 3) (iG := 5) (iA := 6) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 3) (aa := 1) (af := 2) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S1.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c2_s1 _ _
  · intro t
    show Formal.Net.FasmLink.S1.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 2 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c2_s1 _
  · intro t
    show Formal.Net.FasmLink.S1.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 6 _ 4 false rfl rfl t, h.H_TIE 6 _ 5 false rfl rfl t]
    exact fn_ua2_s1 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 1, client 2, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 804 - 655 = +149` ps. -/
theorem fork_c2_s1_fast (h : Behaves Formal.Net.FasmLink.S1.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 3 = (42, 63) ∧ dl 5 = (42, 63) ∧ dl 6 = (45, 56) ∧
      dw 3 1 = (422, 644) ∧ dw 3 4 = (76, 119) ∧ dw 5 4 = (122, 184) ∧
      dw 6 3 = (176, 252) ∧ dw 6 1 = (419, 655) ∧ dw 6 2 = (195, 281))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 2 t = false ∧ pin 3 3 t = true ∧ pin 3 0 t = false ∧
      pin 5 0 t = false ∧ pin 5 3 t = true ∧ pin 6 0 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !false ∧ pin 3 4 t = !false ∧
      pin 5 4 t = !false ∧ out 5 .o6 t = false ∧ pin 6 3 t = false ∧ out 6 .o6 t = false ∧
      pin 6 2 t = false) :
    ∀ t, out 6 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 3) (iG := 5) (iA := 6) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 3) (aa := 1) (af := 2) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S1.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c2_s1 _ _
  · intro t
    show Formal.Net.FasmLink.S1.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 2 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c2_s1 _
  · intro t
    show Formal.Net.FasmLink.S1.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 6 _ 4 false rfl rfl t, h.H_TIE 6 _ 5 false rfl rfl t]
    exact fn_ua2_s1 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Negative control: with the r1 and r2 pins of ustate swapped (client 1's
request values on client 2's pins), the function is not `F2`, so the
request-pin identification in `fn_ust_c2_s1` is load-bearing. (Swapping A0
and q would NOT be a control: `F2 q a = q && a` is symmetric.) -/
theorem fn_ust_req_swap_fails_s1 : ¬ ∀ q a : Bool, Formal.Net.FasmLink.S1.lut3.fn .o6 [false, a, true, false, q, true] = F2 q a := by decide

/-! ### Seed 2: ustate = LUT 4, ugrant = LUT 3, ua1 = LUT 5, ua2 = LUT 6 -/

theorem wiring_s2 :
    Formal.Net.FasmLink.S2.lut3.pins = [.port 5, .const false, .lut 4 .o6, .const true, .port 6, .const true] ∧
    Formal.Net.FasmLink.S2.lut4.pins = [.port 8, .port 6, .port 5, .port 0, .lut 4 .o6, .const true] ∧
    Formal.Net.FasmLink.S2.lut5.pins = [.port 8, .const false, .port 0, .lut 3 .o5, .lut 5 .o6, .const false] ∧
    Formal.Net.FasmLink.S2.lut6.pins = [.port 0, .lut 3 .o6, .port 8, .const false, .lut 6 .o6, .const false] ∧
    True := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The H_INDEP (box) windows of the fork pins are C's generated `pinDelay` (rfl):
A0->ustate, q fb, q->ugrant, then (g, A0, fb) of ua1 and of ua2. -/
theorem pinDelay_fork_s2 :
    Formal.Net.FasmLink.S2.pinDelay[4]![3]! = (397, 1371) ∧
    Formal.Net.FasmLink.S2.pinDelay[4]![4]! = (76, 288) ∧
    Formal.Net.FasmLink.S2.pinDelay[3]![2]! = (202, 677) ∧
    Formal.Net.FasmLink.S2.pinDelay[5]![3]! = (241, 801) ∧
    Formal.Net.FasmLink.S2.pinDelay[5]![2]! = (364, 1282) ∧
    Formal.Net.FasmLink.S2.pinDelay[5]![4]! = (115, 423) ∧
    Formal.Net.FasmLink.S2.pinDelay[6]![1]! = (325, 1015) ∧
    Formal.Net.FasmLink.S2.pinDelay[6]![0]! = (434, 1462) ∧
    Formal.Net.FasmLink.S2.pinDelay[6]![4]! = (76, 288) := by
  decide

theorem fn_ust_c1_s2 : ∀ q a : Bool, Formal.Net.FasmLink.S2.lut4.fn .o6 [false, false, true, a, q, true] = F1 q a := by decide
theorem fn_ug_c1_s2 : ∀ q : Bool, Formal.Net.FasmLink.S2.lut3.fn .o5 [true, false, q, true, false, true] = G1 q := by decide
theorem fn_ua1_s2 : ∀ g a f : Bool, Formal.Net.FasmLink.S2.lut5.fn .o6 [false, false, a, g, f, false] = cel g a f := by decide

/-- Seed 2, client 1, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2338 - 1282 = +1056` ps. -/
theorem fork_c1_s2_slow (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 4 = (93, 157) ∧ dl 3 = (93, 157) ∧ dl 5 = (100, 124) ∧
      dw 4 3 = (1017, 1371) ∧ dw 4 4 = (216, 288) ∧ dw 3 2 = (525, 677) ∧
      dw 5 3 = (610, 801) ∧ dw 5 2 = (943, 1282) ∧ dw 5 4 = (314, 423))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 2 t = true ∧ pin 4 1 t = false ∧ pin 4 0 t = false ∧
      pin 3 0 t = true ∧ pin 3 4 t = false ∧ pin 5 0 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !true ∧ pin 4 4 t = !true ∧
      pin 3 2 t = !true ∧ out 3 .o5 t = false ∧ pin 5 3 t = false ∧ out 5 .o6 t = false ∧
      pin 5 4 t = false) :
    ∀ t, out 5 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 4) (iG := 3) (iA := 5) (p0 := 0)
    (sq := 4) (sa := 3) (gq := 2) (ag := 3) (aa := 2) (af := 4) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S2.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c1_s2 _ _
  · intro t
    show Formal.Net.FasmLink.S2.lut3.fn .o5 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 3 _ 1 false rfl rfl t, h.H_TIE 3 _ 3 true rfl rfl t, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ug_c1_s2 _
  · intro t
    show Formal.Net.FasmLink.S2.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 5 false rfl rfl t]
    exact fn_ua1_s2 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 2, client 1, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 924 - 595 = +329` ps. -/
theorem fork_c1_s2_fast (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 4 = (42, 63) ∧ dl 3 = (42, 63) ∧ dl 5 = (45, 56) ∧
      dw 4 3 = (397, 635) ∧ dw 4 4 = (76, 119) ∧ dw 3 2 = (202, 281) ∧
      dw 5 3 = (241, 353) ∧ dw 5 2 = (364, 595) ∧ dw 5 4 = (115, 183))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 2 t = true ∧ pin 4 1 t = false ∧ pin 4 0 t = false ∧
      pin 3 0 t = true ∧ pin 3 4 t = false ∧ pin 5 0 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !true ∧ pin 4 4 t = !true ∧
      pin 3 2 t = !true ∧ out 3 .o5 t = false ∧ pin 5 3 t = false ∧ out 5 .o6 t = false ∧
      pin 5 4 t = false) :
    ∀ t, out 5 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 4) (iG := 3) (iA := 5) (p0 := 0)
    (sq := 4) (sa := 3) (gq := 2) (ag := 3) (aa := 2) (af := 4) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S2.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c1_s2 _ _
  · intro t
    show Formal.Net.FasmLink.S2.lut3.fn .o5 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 3 _ 1 false rfl rfl t, h.H_TIE 3 _ 3 true rfl rfl t, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ug_c1_s2 _
  · intro t
    show Formal.Net.FasmLink.S2.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 5 false rfl rfl t]
    exact fn_ua1_s2 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

theorem fn_ust_c2_s2 : ∀ q a : Bool, Formal.Net.FasmLink.S2.lut4.fn .o6 [false, true, false, a, q, true] = F2 q a := by decide
theorem fn_ug_c2_s2 : ∀ q : Bool, Formal.Net.FasmLink.S2.lut3.fn .o6 [false, false, q, true, true, true] = G2 q := by decide
theorem fn_ua2_s2 : ∀ g a f : Bool, Formal.Net.FasmLink.S2.lut6.fn .o6 [a, g, false, false, f, false] = cel g a f := by decide

/-- Seed 2, client 2, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2513 - 1462 = +1051` ps. -/
theorem fork_c2_s2_slow (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 4 = (93, 157) ∧ dl 3 = (93, 157) ∧ dl 6 = (100, 124) ∧
      dw 4 3 = (1017, 1371) ∧ dw 4 4 = (216, 288) ∧ dw 3 2 = (525, 677) ∧
      dw 6 1 = (785, 1015) ∧ dw 6 0 = (1088, 1462) ∧ dw 6 4 = (216, 288))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 2 t = false ∧ pin 4 1 t = true ∧ pin 4 0 t = false ∧
      pin 3 0 t = false ∧ pin 3 4 t = true ∧ pin 6 2 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !false ∧ pin 4 4 t = !false ∧
      pin 3 2 t = !false ∧ out 3 .o6 t = false ∧ pin 6 1 t = false ∧ out 6 .o6 t = false ∧
      pin 6 4 t = false) :
    ∀ t, out 6 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 4) (iG := 3) (iA := 6) (p0 := 0)
    (sq := 4) (sa := 3) (gq := 2) (ag := 1) (aa := 0) (af := 4) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S2.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c2_s2 _ _
  · intro t
    show Formal.Net.FasmLink.S2.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 3 _ 1 false rfl rfl t, h.H_TIE 3 _ 3 true rfl rfl t, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ug_c2_s2 _
  · intro t
    show Formal.Net.FasmLink.S2.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 6 _ 3 false rfl rfl t, h.H_TIE 6 _ 5 false rfl rfl t]
    exact fn_ua2_s2 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 2, client 2, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 1008 - 683 = +325` ps. -/
theorem fork_c2_s2_fast (h : Behaves Formal.Net.FasmLink.S2.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 4 = (42, 63) ∧ dl 3 = (42, 63) ∧ dl 6 = (45, 56) ∧
      dw 4 3 = (397, 635) ∧ dw 4 4 = (76, 119) ∧ dw 3 2 = (202, 281) ∧
      dw 6 1 = (325, 453) ∧ dw 6 0 = (434, 683) ∧ dw 6 4 = (76, 119))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 2 t = false ∧ pin 4 1 t = true ∧ pin 4 0 t = false ∧
      pin 3 0 t = false ∧ pin 3 4 t = true ∧ pin 6 2 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !false ∧ pin 4 4 t = !false ∧
      pin 3 2 t = !false ∧ out 3 .o6 t = false ∧ pin 6 1 t = false ∧ out 6 .o6 t = false ∧
      pin 6 4 t = false) :
    ∀ t, out 6 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 4) (iG := 3) (iA := 6) (p0 := 0)
    (sq := 4) (sa := 3) (gq := 2) (ag := 1) (aa := 0) (af := 4) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S2.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c2_s2 _ _
  · intro t
    show Formal.Net.FasmLink.S2.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.1, (H_REQ_STEADY t).2.2.2.2.1, h.H_TIE 3 _ 1 false rfl rfl t, h.H_TIE 3 _ 3 true rfl rfl t, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ug_c2_s2 _
  · intro t
    show Formal.Net.FasmLink.S2.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 6 _ 3 false rfl rfl t, h.H_TIE 6 _ 5 false rfl rfl t]
    exact fn_ua2_s2 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-! ### Seed 3: ustate = LUT 4, ugrant = LUT 6, ua1 = LUT 5, ua2 = LUT 3 -/

theorem wiring_s3 :
    Formal.Net.FasmLink.S3.lut3.pins = [.lut 3 .o6, .port 0, .const false, .lut 6 .o6, .port 8, .const false] ∧
    Formal.Net.FasmLink.S3.lut4.pins = [.lut 4 .o6, .port 6, .port 8, .port 0, .port 5, .const true] ∧
    Formal.Net.FasmLink.S3.lut5.pins = [.port 0, .const false, .port 8, .lut 6 .o5, .lut 5 .o6, .const false] ∧
    Formal.Net.FasmLink.S3.lut6.pins = [.const false, .port 6, .port 5, .const true, .lut 4 .o6, .const true] ∧
    True := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The H_INDEP (box) windows of the fork pins are C's generated `pinDelay` (rfl):
A0->ustate, q fb, q->ugrant, then (g, A0, fb) of ua1 and of ua2. -/
theorem pinDelay_fork_s3 :
    Formal.Net.FasmLink.S3.pinDelay[4]![3]! = (394, 1413) ∧
    Formal.Net.FasmLink.S3.pinDelay[4]![0]! = (286, 973) ∧
    Formal.Net.FasmLink.S3.pinDelay[6]![4]! = (218, 714) ∧
    Formal.Net.FasmLink.S3.pinDelay[5]![3]! = (274, 972) ∧
    Formal.Net.FasmLink.S3.pinDelay[5]![0]! = (399, 1461) ∧
    Formal.Net.FasmLink.S3.pinDelay[5]![4]! = (69, 298) ∧
    Formal.Net.FasmLink.S3.pinDelay[3]![3]! = (268, 879) ∧
    Formal.Net.FasmLink.S3.pinDelay[3]![1]! = (474, 1617) ∧
    Formal.Net.FasmLink.S3.pinDelay[3]![0]! = (211, 685) := by
  decide

theorem fn_ust_c1_s3 : ∀ q a : Bool, Formal.Net.FasmLink.S3.lut4.fn .o6 [q, false, false, a, true, true] = F1 q a := by decide
theorem fn_ug_c1_s3 : ∀ q : Bool, Formal.Net.FasmLink.S3.lut6.fn .o5 [false, false, true, true, q, true] = G1 q := by decide
theorem fn_ua1_s3 : ∀ g a f : Bool, Formal.Net.FasmLink.S3.lut5.fn .o6 [a, false, false, g, f, false] = cel g a f := by decide

/-- Seed 3, client 1, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2442 - 1461 = +981` ps. -/
theorem fork_c1_s3_slow (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 4 = (93, 157) ∧ dl 6 = (93, 157) ∧ dl 5 = (100, 124) ∧
      dw 4 3 = (1051, 1413) ∧ dw 4 0 = (757, 973) ∧ dw 6 4 = (543, 714) ∧
      dw 5 3 = (662, 972) ∧ dw 5 0 = (965, 1461) ∧ dw 5 4 = (186, 298))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 4 t = true ∧ pin 4 1 t = false ∧ pin 4 2 t = false ∧
      pin 6 2 t = true ∧ pin 6 1 t = false ∧ pin 5 2 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !true ∧ pin 4 0 t = !true ∧
      pin 6 4 t = !true ∧ out 6 .o5 t = false ∧ pin 5 3 t = false ∧ out 5 .o6 t = false ∧
      pin 5 4 t = false) :
    ∀ t, out 5 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 4) (iG := 6) (iA := 5) (p0 := 0)
    (sq := 0) (sa := 3) (gq := 4) (ag := 3) (aa := 0) (af := 4) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S3.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c1_s3 _ _
  · intro t
    show Formal.Net.FasmLink.S3.lut6.fn .o5 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 6 _ 0 false rfl rfl t, h.H_TIE 6 _ 3 true rfl rfl t, h.H_TIE 6 _ 5 true rfl rfl t]
    exact fn_ug_c1_s3 _
  · intro t
    show Formal.Net.FasmLink.S3.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 5 false rfl rfl t]
    exact fn_ua1_s3 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 3, client 1, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 970 - 674 = +296` ps. -/
theorem fork_c1_s3_fast (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 4 = (42, 63) ∧ dl 6 = (42, 63) ∧ dl 5 = (45, 56) ∧
      dw 4 3 = (394, 631) ∧ dw 4 0 = (286, 400) ∧ dw 6 4 = (218, 321) ∧
      dw 5 3 = (274, 429) ∧ dw 5 0 = (399, 674) ∧ dw 5 4 = (69, 122))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 4 t = true ∧ pin 4 1 t = false ∧ pin 4 2 t = false ∧
      pin 6 2 t = true ∧ pin 6 1 t = false ∧ pin 5 2 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !true ∧ pin 4 0 t = !true ∧
      pin 6 4 t = !true ∧ out 6 .o5 t = false ∧ pin 5 3 t = false ∧ out 5 .o6 t = false ∧
      pin 5 4 t = false) :
    ∀ t, out 5 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 4) (iG := 6) (iA := 5) (p0 := 0)
    (sq := 0) (sa := 3) (gq := 4) (ag := 3) (aa := 0) (af := 4) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S3.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c1_s3 _ _
  · intro t
    show Formal.Net.FasmLink.S3.lut6.fn .o5 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 6 _ 0 false rfl rfl t, h.H_TIE 6 _ 3 true rfl rfl t, h.H_TIE 6 _ 5 true rfl rfl t]
    exact fn_ug_c1_s3 _
  · intro t
    show Formal.Net.FasmLink.S3.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 5 _ 1 false rfl rfl t, h.H_TIE 5 _ 5 false rfl rfl t]
    exact fn_ua1_s3 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

theorem fn_ust_c2_s3 : ∀ q a : Bool, Formal.Net.FasmLink.S3.lut4.fn .o6 [q, true, false, a, false, true] = F2 q a := by decide
theorem fn_ug_c2_s3 : ∀ q : Bool, Formal.Net.FasmLink.S3.lut6.fn .o6 [false, true, false, true, q, true] = G2 q := by decide
theorem fn_ua2_s3 : ∀ g a f : Bool, Formal.Net.FasmLink.S3.lut3.fn .o6 [f, a, false, g, false, false] = cel g a f := by decide

/-- Seed 3, client 2, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2457 - 1617 = +840` ps. -/
theorem fork_c2_s3_slow (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 4 = (93, 157) ∧ dl 6 = (93, 157) ∧ dl 3 = (100, 124) ∧
      dw 4 3 = (1051, 1413) ∧ dw 4 0 = (757, 973) ∧ dw 6 4 = (543, 714) ∧
      dw 3 3 = (677, 879) ∧ dw 3 1 = (1216, 1617) ∧ dw 3 0 = (531, 685))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 4 t = false ∧ pin 4 1 t = true ∧ pin 4 2 t = false ∧
      pin 6 2 t = false ∧ pin 6 1 t = true ∧ pin 3 4 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !false ∧ pin 4 0 t = !false ∧
      pin 6 4 t = !false ∧ out 6 .o6 t = false ∧ pin 3 3 t = false ∧ out 3 .o6 t = false ∧
      pin 3 0 t = false) :
    ∀ t, out 3 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 4) (iG := 6) (iA := 3) (p0 := 0)
    (sq := 0) (sa := 3) (gq := 4) (ag := 3) (aa := 1) (af := 0) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S3.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c2_s3 _ _
  · intro t
    show Formal.Net.FasmLink.S3.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 6 _ 0 false rfl rfl t, h.H_TIE 6 _ 3 true rfl rfl t, h.H_TIE 6 _ 5 true rfl rfl t]
    exact fn_ug_c2_s3 _
  · intro t
    show Formal.Net.FasmLink.S3.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 3 _ 2 false rfl rfl t, h.H_TIE 3 _ 5 false rfl rfl t]
    exact fn_ua2_s3 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 3, client 2, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 964 - 731 = +233` ps. -/
theorem fork_c2_s3_fast (h : Behaves Formal.Net.FasmLink.S3.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 4 = (42, 63) ∧ dl 6 = (42, 63) ∧ dl 3 = (45, 56) ∧
      dw 4 3 = (394, 631) ∧ dw 4 0 = (286, 400) ∧ dw 6 4 = (218, 321) ∧
      dw 3 3 = (268, 382) ∧ dw 3 1 = (474, 731) ∧ dw 3 0 = (211, 292))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 4 4 t = false ∧ pin 4 1 t = true ∧ pin 4 2 t = false ∧
      pin 6 2 t = false ∧ pin 6 1 t = true ∧ pin 3 4 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 4 3 t = true ∧ out 4 .o6 t = !false ∧ pin 4 0 t = !false ∧
      pin 6 4 t = !false ∧ out 6 .o6 t = false ∧ pin 3 3 t = false ∧ out 3 .o6 t = false ∧
      pin 3 0 t = false) :
    ∀ t, out 3 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 4) (iG := 6) (iA := 3) (p0 := 0)
    (sq := 0) (sa := 3) (gq := 4) (ag := 3) (aa := 1) (af := 0) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S3.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).1, h.H_TIE 4 _ 5 true rfl rfl t]
    exact fn_ust_c2_s3 _ _
  · intro t
    show Formal.Net.FasmLink.S3.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 6 _ 0 false rfl rfl t, h.H_TIE 6 _ 3 true rfl rfl t, h.H_TIE 6 _ 5 true rfl rfl t]
    exact fn_ug_c2_s3 _
  · intro t
    show Formal.Net.FasmLink.S3.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 3 _ 2 false rfl rfl t, h.H_TIE 3 _ 5 false rfl rfl t]
    exact fn_ua2_s3 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-! ### Seed 4: ustate = LUT 3, ugrant = LUT 5, ua1 = LUT 6, ua2 = LUT 4 -/

theorem wiring_s4 :
    Formal.Net.FasmLink.S4.lut3.pins = [.port 5, .port 0, .port 8, .port 6, .lut 3 .o6, .const true] ∧
    Formal.Net.FasmLink.S4.lut4.pins = [.port 0, .lut 5 .o6, .const false, .port 8, .lut 4 .o6, .const false] ∧
    Formal.Net.FasmLink.S4.lut5.pins = [.const false, .port 6, .port 5, .const true, .lut 3 .o6, .const true] ∧
    Formal.Net.FasmLink.S4.lut6.pins = [.lut 6 .o6, .port 8, .port 0, .lut 5 .o5, .const false, .const false] ∧
    True := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The H_INDEP (box) windows of the fork pins are C's generated `pinDelay` (rfl):
A0->ustate, q fb, q->ugrant, then (g, A0, fb) of ua1 and of ua2. -/
theorem pinDelay_fork_s4 :
    Formal.Net.FasmLink.S4.pinDelay[3]![1]! = (484, 1601) ∧
    Formal.Net.FasmLink.S4.pinDelay[3]![4]! = (76, 288) ∧
    Formal.Net.FasmLink.S4.pinDelay[5]![4]! = (172, 571) ∧
    Formal.Net.FasmLink.S4.pinDelay[6]![3]! = (127, 471) ∧
    Formal.Net.FasmLink.S4.pinDelay[6]![2]! = (418, 1500) ∧
    Formal.Net.FasmLink.S4.pinDelay[6]![0]! = (214, 689) ∧
    Formal.Net.FasmLink.S4.pinDelay[4]![1]! = (258, 863) ∧
    Formal.Net.FasmLink.S4.pinDelay[4]![0]! = (428, 1464) ∧
    Formal.Net.FasmLink.S4.pinDelay[4]![4]! = (71, 274) := by
  decide

theorem fn_ust_c1_s4 : ∀ q a : Bool, Formal.Net.FasmLink.S4.lut3.fn .o6 [true, a, false, false, q, true] = F1 q a := by decide
theorem fn_ug_c1_s4 : ∀ q : Bool, Formal.Net.FasmLink.S4.lut5.fn .o5 [false, false, true, true, q, true] = G1 q := by decide
theorem fn_ua1_s4 : ∀ g a f : Bool, Formal.Net.FasmLink.S4.lut6.fn .o6 [f, false, a, g, false, false] = cel g a f := by decide

/-- Seed 4, client 1, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2164 - 1500 = +664` ps. -/
theorem fork_c1_s4_slow (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 3 = (93, 157) ∧ dl 5 = (93, 157) ∧ dl 6 = (100, 124) ∧
      dw 3 1 = (1188, 1601) ∧ dw 3 4 = (216, 288) ∧ dw 5 4 = (434, 571) ∧
      dw 6 3 = (356, 471) ∧ dw 6 2 = (1106, 1500) ∧ dw 6 0 = (534, 689))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 0 t = true ∧ pin 3 3 t = false ∧ pin 3 2 t = false ∧
      pin 5 2 t = true ∧ pin 5 1 t = false ∧ pin 6 1 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !true ∧ pin 3 4 t = !true ∧
      pin 5 4 t = !true ∧ out 5 .o5 t = false ∧ pin 6 3 t = false ∧ out 6 .o6 t = false ∧
      pin 6 0 t = false) :
    ∀ t, out 6 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 3) (iG := 5) (iA := 6) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 3) (aa := 2) (af := 0) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S4.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c1_s4 _ _
  · intro t
    show Formal.Net.FasmLink.S4.lut5.fn .o5 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 5 _ 0 false rfl rfl t, h.H_TIE 5 _ 3 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c1_s4 _
  · intro t
    show Formal.Net.FasmLink.S4.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 6 _ 4 false rfl rfl t, h.H_TIE 6 _ 5 false rfl rfl t]
    exact fn_ua1_s4 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 4, client 1, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 867 - 681 = +186` ps. -/
theorem fork_c1_s4_fast (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 3 = (42, 63) ∧ dl 5 = (42, 63) ∧ dl 6 = (45, 56) ∧
      dw 3 1 = (484, 761) ∧ dw 3 4 = (76, 119) ∧ dw 5 4 = (172, 254) ∧
      dw 6 3 = (127, 191) ∧ dw 6 2 = (418, 681) ∧ dw 6 0 = (214, 296))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 0 t = true ∧ pin 3 3 t = false ∧ pin 3 2 t = false ∧
      pin 5 2 t = true ∧ pin 5 1 t = false ∧ pin 6 1 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !true ∧ pin 3 4 t = !true ∧
      pin 5 4 t = !true ∧ out 5 .o5 t = false ∧ pin 6 3 t = false ∧ out 6 .o6 t = false ∧
      pin 6 0 t = false) :
    ∀ t, out 6 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F1) (G := G1) (v := true) F1_hold G1_vals.1 (iS := 3) (iG := 5) (iA := 6) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 3) (aa := 2) (af := 0) (og := .o5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S4.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c1_s4 _ _
  · intro t
    show Formal.Net.FasmLink.S4.lut5.fn .o5 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 5 _ 0 false rfl rfl t, h.H_TIE 5 _ 3 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c1_s4 _
  · intro t
    show Formal.Net.FasmLink.S4.lut6.fn .o6 [pin 6 0 t, pin 6 1 t, pin 6 2 t, pin 6 3 t, pin 6 4 t, pin 6 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 6 _ 4 false rfl rfl t, h.H_TIE 6 _ 5 false rfl rfl t]
    exact fn_ua1_s4 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

theorem fn_ust_c2_s4 : ∀ q a : Bool, Formal.Net.FasmLink.S4.lut3.fn .o6 [false, a, false, true, q, true] = F2 q a := by decide
theorem fn_ug_c2_s4 : ∀ q : Bool, Formal.Net.FasmLink.S4.lut5.fn .o6 [false, true, false, true, q, true] = G2 q := by decide
theorem fn_ua2_s4 : ∀ g a f : Bool, Formal.Net.FasmLink.S4.lut4.fn .o6 [a, g, false, false, f, false] = cel g a f := by decide

/-- Seed 4, client 2, slow die (H_DIE_SLOW): every LUT and route window at that
corner. Margin `lo_early - hi_late = 2479 - 1464 = +1015` ps. -/
theorem fork_c2_s4_slow (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_SLOW : dl 3 = (93, 157) ∧ dl 5 = (93, 157) ∧ dl 4 = (100, 124) ∧
      dw 3 1 = (1188, 1601) ∧ dw 3 4 = (216, 288) ∧ dw 5 4 = (434, 571) ∧
      dw 4 1 = (671, 863) ∧ dw 4 0 = (1082, 1464) ∧ dw 4 4 = (205, 274))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 0 t = false ∧ pin 3 3 t = true ∧ pin 3 2 t = false ∧
      pin 5 2 t = false ∧ pin 5 1 t = true ∧ pin 4 3 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !false ∧ pin 3 4 t = !false ∧
      pin 5 4 t = !false ∧ out 5 .o6 t = false ∧ pin 4 1 t = false ∧ out 4 .o6 t = false ∧
      pin 4 4 t = false) :
    ∀ t, out 4 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_SLOW
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 3) (iG := 5) (iA := 4) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 1) (aa := 0) (af := 4) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S4.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c2_s4 _ _
  · intro t
    show Formal.Net.FasmLink.S4.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 5 _ 0 false rfl rfl t, h.H_TIE 5 _ 3 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c2_s4 _
  · intro t
    show Formal.Net.FasmLink.S4.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 4 _ 2 false rfl rfl t, h.H_TIE 4 _ 5 false rfl rfl t]
    exact fn_ua2_s4 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

/-- Seed 4, client 2, fast die (H_DIE_FAST): every LUT and route window at that
corner. Margin `lo_early - hi_late = 998 - 685 = +313` ps. -/
theorem fork_c2_s4_fast (h : Behaves Formal.Net.FasmLink.S4.net ins out pin dl dw) {T0 Ts : Nat}
    (H_DIE_FAST : dl 3 = (42, 63) ∧ dl 5 = (42, 63) ∧ dl 4 = (45, 56) ∧
      dw 3 1 = (484, 761) ∧ dw 3 4 = (76, 119) ∧ dw 5 4 = (172, 254) ∧
      dw 4 1 = (258, 357) ∧ dw 4 0 = (428, 685) ∧ dw 4 4 = (71, 112))
    (H_A0_FALL : ∀ t, ins 0 t = decide (t < T0))
    (H_REQ_STEADY : ∀ t, pin 3 0 t = false ∧ pin 3 3 t = true ∧ pin 3 2 t = false ∧
      pin 5 2 t = false ∧ pin 5 1 t = true ∧ pin 4 3 t = false)
    (H_TS : 2000 ≤ Ts ∧ Ts ≤ T0)
    (H_SETTLED : ∀ t, t < Ts → pin 3 1 t = true ∧ out 3 .o6 t = !false ∧ pin 3 4 t = !false ∧
      pin 5 4 t = !false ∧ out 5 .o6 t = false ∧ pin 4 1 t = false ∧ out 4 .o6 t = false ∧
      pin 4 4 t = false) :
    ∀ t, out 4 .o6 t = false := by
  obtain ⟨d1, d2, d3, w1, w2, w3, w4, w5, w6⟩ := H_DIE_FAST
  obtain ⟨hT1, hT2⟩ := H_TS
  refine fork_safe_net h (F := F2) (G := G2) (v := false) F2_hold G2_vals.1 (iS := 3) (iG := 5) (iA := 4) (p0 := 0)
    (sq := 4) (sa := 1) (gq := 4) (ag := 1) (aa := 0) (af := 4) (og := .o6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ H_A0_FALL ?_ H_SETTLED ?_ ?_
  · intro t
    show Formal.Net.FasmLink.S4.lut3.fn .o6 [pin 3 0 t, pin 3 1 t, pin 3 2 t, pin 3 3 t, pin 3 4 t, pin 3 5 t] = _
    rw [(H_REQ_STEADY t).1, (H_REQ_STEADY t).2.2.1, (H_REQ_STEADY t).2.1, h.H_TIE 3 _ 5 true rfl rfl t]
    exact fn_ust_c2_s4 _ _
  · intro t
    show Formal.Net.FasmLink.S4.lut5.fn .o6 [pin 5 0 t, pin 5 1 t, pin 5 2 t, pin 5 3 t, pin 5 4 t, pin 5 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.1, (H_REQ_STEADY t).2.2.2.1, h.H_TIE 5 _ 0 false rfl rfl t, h.H_TIE 5 _ 3 true rfl rfl t, h.H_TIE 5 _ 5 true rfl rfl t]
    exact fn_ug_c2_s4 _
  · intro t
    show Formal.Net.FasmLink.S4.lut4.fn .o6 [pin 4 0 t, pin 4 1 t, pin 4 2 t, pin 4 3 t, pin 4 4 t, pin 4 5 t] = _
    rw [(H_REQ_STEADY t).2.2.2.2.2, h.H_TIE 4 _ 2 false rfl rfl t, h.H_TIE 4 _ 5 false rfl rfl t]
    exact fn_ua2_s4 _ _ _
  · rw [d1, d2, d3, w1, w2, w3, w4, w5, w6]; omega
  · rw [d1, d3, w2, w6]; decide
  · rw [d1, d2, w1, w3, w4, w5]; decide

end perseed
/-! ## 4. 7g's run model on the routed windows (fixed delays, both directions)

7g's `client{1,2}_box` is an iff over fixed transport delays in a box. The
records below put C's routed windows into 7g's `Dl` (site pins are already
inside every route window, so the `p*` fields are 0). Readings:
* `full`: H_INDEP over whole routes, `c = 0` (C's `pinDelay` verbatim, no
  shared-prefix credit), LUTs at the site envelope `[42, 157]` (LUT6_2) /
  `[45, 124]` (LUT6);
* `unsh`: H_INDEP, with 7g's shared prefix `c` (the A0 pips common to both
  branches, H_A0_SHARED: one wire, one delay per run) and unshared branch
  windows;
* `slow` / `fast`: H_ONE_CORNER, every window at that die corner, with `c`.
-/

/-- 7g's delay record with the site pins folded into the routes. -/
def dl7g (c wSt aSt wQf wQG aG wGC wAC aC wCf : Nat) : ArbA0Fork.Dl :=
  { c := c, wSt := wSt, pSt := 0, aSt := aSt, wQf := wQf, pQf := 0, wQG := wQG, pQG := 0,
    aG := aG, wGC := wGC, pGC := 0, wAC := wAC, pAC := 0, aC := aC, wCf := wCf, pCf := 0 }

/-- Seed 1, client 1, box/full: margin -446 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s1_box_full : ¬ ∀ p, (dl7g 0 422 42 76 122 42 209 356 45 71).le p → p.le (dl7g 0 1391 157 288 429 157 677 1283 124 276) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 0 422 42 76 122 42 209 356 45 71) (dl7g 0 1391 157 288 429 157 677 1283 124 276) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 1, client 1, box/unsh: margin -118 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s1_box_unsh : ¬ ∀ p, (dl7g 160 262 42 76 122 42 209 196 45 71).le p → p.le (dl7g 488 903 157 288 429 157 677 795 124 276) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 160 262 42 76 122 42 209 196 45 71) (dl7g 488 903 157 288 429 157 677 795 124 276) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 1, client 1, slow/unsh: every fixed-delay run in the box is safe (margin +878). -/
theorem run7g_c1_s1_slow : ∀ p, (dl7g 411 638 93 216 325 93 524 540 100 205).le p → p.le (dl7g 488 903 157 288 429 157 677 795 124 276) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 411 638 93 216 325 93 524 540 100 205) (dl7g 488 903 157 288 429 157 677 795 124 276) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 1, client 1, fast/unsh: every fixed-delay run in the box is safe (margin +302). -/
theorem run7g_c1_s1_fast : ∀ p, (dl7g 160 262 42 76 122 42 209 196 45 71).le p → p.le (dl7g 202 442 63 119 184 63 290 375 56 114) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 160 262 42 76 122 42 209 196 45 71) (dl7g 202 442 63 119 184 63 290 375 56 114) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 1, client 2, box/full: margin -639 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s1_box_full : ¬ ∀ p, (dl7g 0 422 42 76 122 42 176 419 45 195).le p → p.le (dl7g 0 1391 157 288 429 157 651 1443 124 677) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 0 422 42 76 122 42 176 419 45 195) (dl7g 0 1391 157 288 429 157 651 1443 124 677) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 1, client 2, box/unsh: margin -311 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s1_box_unsh : ¬ ∀ p, (dl7g 160 262 42 76 122 42 176 259 45 195).le p → p.le (dl7g 488 903 157 288 429 157 651 955 124 677) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 160 262 42 76 122 42 176 259 45 195) (dl7g 488 903 157 288 429 157 651 955 124 677) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 1, client 2, slow/unsh: every fixed-delay run in the box is safe (margin +697). -/
theorem run7g_c2_s1_slow : ∀ p, (dl7g 411 638 93 216 325 93 503 669 100 519).le p → p.le (dl7g 488 903 157 288 429 157 651 955 124 677) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 411 638 93 216 325 93 503 669 100 519) (dl7g 488 903 157 288 429 157 651 955 124 677) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 1, client 2, fast/unsh: every fixed-delay run in the box is safe (margin +191). -/
theorem run7g_c2_s1_fast : ∀ p, (dl7g 160 262 42 76 122 42 176 259 45 195).le p → p.le (dl7g 202 442 63 119 184 63 252 453 56 281) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 160 262 42 76 122 42 176 259 45 195) (dl7g 202 442 63 119 184 63 252 453 56 281) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 2, client 1, box/full: margin -358 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s2_box_full : ¬ ∀ p, (dl7g 0 397 42 76 202 42 241 364 45 115).le p → p.le (dl7g 0 1371 157 288 677 157 801 1282 124 423) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 0 397 42 76 202 42 241 364 45 115) (dl7g 0 1371 157 288 677 157 801 1282 124 423) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 2, client 1, box/unsh: margin -8 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s2_box_unsh : ¬ ∀ p, (dl7g 172 225 42 76 202 42 241 192 45 115).le p → p.le (dl7g 522 849 157 288 677 157 801 760 124 423) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 172 225 42 76 202 42 241 192 45 115) (dl7g 522 849 157 288 677 157 801 760 124 423) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 2, client 1, slow/unsh: every fixed-delay run in the box is safe (margin +1139). -/
theorem run7g_c1_s2_slow : ∀ p, (dl7g 439 578 93 216 525 93 610 504 100 314).le p → p.le (dl7g 522 849 157 288 677 157 801 760 124 423) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 439 578 93 216 525 93 610 504 100 314) (dl7g 522 849 157 288 677 157 801 760 124 423) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 2, client 1, fast/unsh: every fixed-delay run in the box is safe (margin +374). -/
theorem run7g_c1_s2_fast : ∀ p, (dl7g 172 225 42 76 202 42 241 192 45 115).le p → p.le (dl7g 217 418 63 119 281 63 353 378 56 183) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 172 225 42 76 202 42 241 192 45 115) (dl7g 217 418 63 119 281 63 353 378 56 183) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 2, client 2, box/full: margin -454 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s2_box_full : ¬ ∀ p, (dl7g 0 397 42 76 202 42 325 434 45 76).le p → p.le (dl7g 0 1371 157 288 677 157 1015 1462 124 288) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 0 397 42 76 202 42 325 434 45 76) (dl7g 0 1371 157 288 677 157 1015 1462 124 288) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 2, client 2, box/unsh: margin -104 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s2_box_unsh : ¬ ∀ p, (dl7g 172 225 42 76 202 42 325 262 45 76).le p → p.le (dl7g 522 849 157 288 677 157 1015 940 124 288) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 172 225 42 76 202 42 325 262 45 76) (dl7g 522 849 157 288 677 157 1015 940 124 288) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 2, client 2, slow/unsh: every fixed-delay run in the box is safe (margin +1134). -/
theorem run7g_c2_s2_slow : ∀ p, (dl7g 439 578 93 216 525 93 785 649 100 216).le p → p.le (dl7g 522 849 157 288 677 157 1015 940 124 288) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 439 578 93 216 525 93 785 649 100 216) (dl7g 522 849 157 288 677 157 1015 940 124 288) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 2, client 2, fast/unsh: every fixed-delay run in the box is safe (margin +370). -/
theorem run7g_c2_s2_fast : ∀ p, (dl7g 172 225 42 76 202 42 325 262 45 76).le p → p.le (dl7g 217 418 63 119 281 63 453 466 56 119) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 172 225 42 76 202 42 325 262 45 76) (dl7g 217 418 63 119 281 63 453 466 56 119) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 3, client 1, box/full: margin -491 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s3_box_full : ¬ ∀ p, (dl7g 0 394 42 286 218 42 274 399 45 69).le p → p.le (dl7g 0 1413 157 973 714 157 972 1461 124 298) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 0 394 42 286 218 42 274 399 45 69) (dl7g 0 1413 157 973 714 157 972 1461 124 298) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 3, client 1, box/unsh: margin -55 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s3_box_unsh : ¬ ∀ p, (dl7g 216 178 42 286 218 42 274 183 45 69).le p → p.le (dl7g 652 761 157 973 714 157 972 809 124 298) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 216 178 42 286 218 42 274 183 45 69) (dl7g 652 761 157 973 714 157 972 809 124 298) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 3, client 1, slow/unsh: every fixed-delay run in the box is safe (margin +1087). -/
theorem run7g_c1_s3_slow : ∀ p, (dl7g 546 505 93 757 543 93 662 419 100 186).le p → p.le (dl7g 652 761 157 973 714 157 972 809 124 298) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 546 505 93 757 543 93 662 419 100 186) (dl7g 652 761 157 973 714 157 972 809 124 298) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 3, client 1, fast/unsh: every fixed-delay run in the box is safe (margin +350). -/
theorem run7g_c1_s3_fast : ∀ p, (dl7g 216 178 42 286 218 42 274 183 45 69).le p → p.le (dl7g 270 361 63 400 321 63 429 404 56 122) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 216 178 42 286 218 42 274 183 45 69) (dl7g 270 361 63 400 321 63 429 404 56 122) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 3, client 2, box/full: margin -653 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s3_box_full : ¬ ∀ p, (dl7g 0 394 42 286 218 42 268 474 45 211).le p → p.le (dl7g 0 1413 157 973 714 157 879 1617 124 685) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 0 394 42 286 218 42 268 474 45 211) (dl7g 0 1413 157 973 714 157 879 1617 124 685) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 3, client 2, box/unsh: margin -217 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s3_box_unsh : ¬ ∀ p, (dl7g 216 178 42 286 218 42 268 258 45 211).le p → p.le (dl7g 652 761 157 973 714 157 879 965 124 685) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 216 178 42 286 218 42 268 258 45 211) (dl7g 652 761 157 973 714 157 879 965 124 685) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 3, client 2, slow/unsh: every fixed-delay run in the box is safe (margin +946). -/
theorem run7g_c2_s3_slow : ∀ p, (dl7g 546 505 93 757 543 93 677 670 100 531).le p → p.le (dl7g 652 761 157 973 714 157 879 965 124 685) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 546 505 93 757 543 93 677 670 100 531) (dl7g 652 761 157 973 714 157 879 965 124 685) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 3, client 2, fast/unsh: every fixed-delay run in the box is safe (margin +287). -/
theorem run7g_c2_s3_fast : ∀ p, (dl7g 216 178 42 286 218 42 268 258 45 211).le p → p.le (dl7g 270 361 63 400 321 63 382 461 56 292) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 216 178 42 286 218 42 268 258 45 211) (dl7g 270 361 63 400 321 63 382 461 56 292) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 4, client 1, box/full: margin -633 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s4_box_full : ¬ ∀ p, (dl7g 0 484 42 76 172 42 127 418 45 214).le p → p.le (dl7g 0 1601 157 288 571 157 471 1500 124 689) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 0 484 42 76 172 42 127 418 45 214) (dl7g 0 1601 157 288 571 157 471 1500 124 689) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 4, client 1, box/unsh: margin -283 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client1_box`, only-if direction, worst corner). -/
theorem run7g_c1_s4_box_unsh : ¬ ∀ p, (dl7g 172 312 42 76 172 42 127 246 45 214).le p → p.le (dl7g 522 1079 157 288 571 157 471 978 124 689) → ArbA0Fork.Safe F1 G1 false p :=
  fun hs => absurd ((ArbA0Fork.client1_box (dl7g 172 312 42 76 172 42 127 246 45 214) (dl7g 522 1079 157 288 571 157 471 978 124 689) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 4, client 1, slow/unsh: every fixed-delay run in the box is safe (margin +747). -/
theorem run7g_c1_s4_slow : ∀ p, (dl7g 439 749 93 216 434 93 356 667 100 534).le p → p.le (dl7g 522 1079 157 288 571 157 471 978 124 689) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 439 749 93 216 434 93 356 667 100 534) (dl7g 522 1079 157 288 571 157 471 978 124 689) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 4, client 1, fast/unsh: every fixed-delay run in the box is safe (margin +231). -/
theorem run7g_c1_s4_fast : ∀ p, (dl7g 172 312 42 76 172 42 127 246 45 214).le p → p.le (dl7g 217 544 63 119 254 63 191 464 56 296) → ArbA0Fork.Safe F1 G1 false p :=
  (ArbA0Fork.client1_box (dl7g 172 312 42 76 172 42 127 246 45 214) (dl7g 217 544 63 119 254 63 191 464 56 296) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 4, client 2, box/full: margin -466 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s4_box_full : ¬ ∀ p, (dl7g 0 484 42 76 172 42 258 428 45 71).le p → p.le (dl7g 0 1601 157 288 571 157 863 1464 124 274) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 0 484 42 76 172 42 258 428 45 71) (dl7g 0 1601 157 288 571 157 863 1464 124 274) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 4, client 2, box/unsh: margin -116 < 0, so SOME fixed-delay run in the box
acknowledges early (7g's `client2_box`, only-if direction, worst corner). -/
theorem run7g_c2_s4_box_unsh : ¬ ∀ p, (dl7g 172 312 42 76 172 42 258 256 45 71).le p → p.le (dl7g 522 1079 157 288 571 157 863 942 124 274) → ArbA0Fork.Safe F2 G2 true p :=
  fun hs => absurd ((ArbA0Fork.client2_box (dl7g 172 312 42 76 172 42 258 256 45 71) (dl7g 522 1079 157 288 571 157 863 942 124 274) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).1 hs) (by decide)

/-- Seed 4, client 2, slow/unsh: every fixed-delay run in the box is safe (margin +1098). -/
theorem run7g_c2_s4_slow : ∀ p, (dl7g 439 749 93 216 434 93 671 643 100 205).le p → p.le (dl7g 522 1079 157 288 571 157 863 942 124 274) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 439 749 93 216 434 93 671 643 100 205) (dl7g 522 1079 157 288 571 157 863 942 124 274) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)

/-- Seed 4, client 2, fast/unsh: every fixed-delay run in the box is safe (margin +358). -/
theorem run7g_c2_s4_fast : ∀ p, (dl7g 172 312 42 76 172 42 258 256 45 71).le p → p.le (dl7g 217 544 63 119 254 63 357 468 56 112) → ArbA0Fork.Safe F2 G2 true p :=
  (ArbA0Fork.client2_box (dl7g 172 312 42 76 172 42 258 256 45 71) (dl7g 217 544 63 119 254 63 357 468 56 112) (by unfold ArbA0Fork.Dl.le dl7g; decide) (by decide) (by decide)).2 (by decide)
/-! ## 5. 7h/7j's RT1/RT2 conditions on the routed windows

7h/7j's model has one fixed delay per wire and per arc edge (`ArbHeldTimed.Dl`,
`Int` ps, site pins inside the routes). `RtBox` gives an interval for every
wire (from the bits) and one per arc class (O6, O5; rise and fall in the same
interval, ArbCorners' consistent-corner rule within a reading), and
`RtBox.has` says a record lies in it. The r1, r2 and A0 wires are the
UNSHARED parts past each net's divergence node (the scenario's `t0` and the
server's `A0` edge are taken at those nodes, so `smin` is measured from R0 at
ustate's output to A0 at its divergence node: off-chip pad round trip plus the
on-chip shared input prefix).

`rt_s{n}_{slow,fast}`: every record in the window with `smin ≥ S` satisfies
RT1, RT2, RT1b, RT2b and both A0Fork conditions, so 7h's `rt1_exclusion`,
`rt2_exclusion_arcs` and 7j's mirror theorems apply. `rt_s{n}_box`: RT1, RT2,
RT1b, RT2b hold for every record in the independent box with `smin ≥ S`;
the A0Fork conditions do NOT hold over the box (see `run7g_*_box_*`), so
`rt2_exclusion_arcs` is not available in that reading.
-/

/-- Interval bounds (ps) for 7h's delay record. -/
structure RtBox where
  wr1s : Int × Int
  wr2s : Int × Int
  wr1g : Int × Int
  wr2g : Int × Int
  wfb : Int × Int
  wa0s : Int × Int
  wq : Int × Int
  wg1 : Int × Int
  wa01 : Int × Int
  wfa1 : Int × Int
  wg2 : Int × Int
  wa02 : Int × Int
  wfa2 : Int × Int
  /-- every O6 arc (ustate q, ugrant g2, ua1, ua2), rise and fall -/
  o6 : Int × Int
  /-- every O5 arc (ustate R0, ugrant g1), rise and fall, every pin -/
  o5 : Int × Int

def inI (x : Int) (b : Int × Int) : Prop := b.1 ≤ x ∧ x ≤ b.2

/-- The record lies in the box (wires, and every arc in its class). -/
def RtBox.has (B : RtBox) (D : ArbHeldTimed.Dl) : Prop :=
  inI D.wr1s B.wr1s ∧ inI D.wr2s B.wr2s ∧ inI D.wr1g B.wr1g ∧ inI D.wr2g B.wr2g ∧
  inI D.wfb B.wfb ∧ inI D.wa0s B.wa0s ∧ inI D.wq B.wq ∧ inI D.wg1 B.wg1 ∧
  inI D.wa01 B.wa01 ∧ inI D.wfa1 B.wfa1 ∧ inI D.wg2 B.wg2 ∧ inI D.wa02 B.wa02 ∧
  inI D.wfa2 B.wfa2 ∧
  inI D.qr B.o6 ∧ inI D.qf B.o6 ∧ inI D.g2r B.o6 ∧ inI D.g2f B.o6 ∧
  inI D.c1r B.o6 ∧ inI D.c1f B.o6 ∧ inI D.c2r B.o6 ∧ inI D.c2f B.o6 ∧
  inI D.Rr1 B.o5 ∧ inI D.Rf1 B.o5 ∧ inI D.Rr2 B.o5 ∧ inI D.Rf2 B.o5 ∧
  inI D.Rrq B.o5 ∧ inI D.Rfq B.o5 ∧ inI D.g1r1 B.o5 ∧ inI D.g1f1 B.o5 ∧
  inI D.g1r2 B.o5 ∧ inI D.g1f2 B.o5 ∧ inI D.g1rq B.o5 ∧ inI D.g1fq B.o5

/-- Seed 1, box reading. -/
def rtS1Box : RtBox where
  wr1s := (260, 943)
  wr2s := (175, 697)
  wr1g := (313, 1125)
  wr2g := (129, 556)
  wfb := (76, 288)
  wa0s := (262, 903)
  wq := (122, 429)
  wg1 := (209, 677)
  wa01 := (196, 795)
  wfa1 := (71, 276)
  wg2 := (176, 651)
  wa02 := (259, 955)
  wfa2 := (195, 677)
  o6 := (45, 124)
  o5 := (42, 157)

/-- Seed 1, box: the RT conditions for every record in `rtS1Box` with `smin ≥ 718` (binding: g1). -/
theorem rt_s1_box (D : ArbHeldTimed.Dl) (hB : rtS1Box.has D) (H_SERVER_MIN : 718 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D := by
  simp only [RtBox.has, inI, rtS1Box] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩⟩

/-- Seed 2, box reading. -/
def rtS2Box : RtBox where
  wr1s := (254, 906)
  wr2s := (295, 1114)
  wr1g := (326, 1100)
  wr2g := (153, 686)
  wfb := (76, 288)
  wa0s := (225, 849)
  wq := (202, 677)
  wg1 := (241, 801)
  wa01 := (192, 760)
  wfa1 := (115, 423)
  wg2 := (325, 1015)
  wa02 := (262, 940)
  wfa2 := (76, 288)
  o6 := (45, 124)
  o5 := (42, 157)

/-- Seed 2, box: the RT conditions for every record in `rtS2Box` with `smin ≥ 865` (binding: g1). -/
theorem rt_s2_box (D : ArbHeldTimed.Dl) (hB : rtS2Box.has D) (H_SERVER_MIN : 865 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D := by
  simp only [RtBox.has, inI, rtS2Box] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩⟩

/-- Seed 3, box reading. -/
def rtS3Box : RtBox where
  wr1s := (166, 669)
  wr2s := (264, 901)
  wr1g := (202, 774)
  wr2g := (309, 1099)
  wfb := (286, 973)
  wa0s := (178, 761)
  wq := (218, 714)
  wg1 := (274, 972)
  wa01 := (183, 809)
  wfa1 := (69, 298)
  wg2 := (268, 879)
  wa02 := (258, 965)
  wfa2 := (211, 685)
  o6 := (45, 124)
  o5 := (42, 157)

/-- Seed 3, box: the RT conditions for every record in `rtS3Box` with `smin ≥ 898` (binding: g2). -/
theorem rt_s3_box (D : ArbHeldTimed.Dl) (hB : rtS3Box.has D) (H_SERVER_MIN : 898 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D := by
  simp only [RtBox.has, inI, rtS3Box] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩⟩

/-- Seed 4, box reading. -/
def rtS4Box : RtBox where
  wr1s := (317, 1112)
  wr2s := (239, 874)
  wr1g := (152, 620)
  wr2g := (314, 1046)
  wfb := (76, 288)
  wa0s := (312, 1079)
  wq := (172, 571)
  wg1 := (127, 471)
  wa01 := (246, 978)
  wfa1 := (214, 689)
  wg2 := (258, 863)
  wa02 := (256, 942)
  wfa2 := (71, 274)
  o6 := (45, 124)
  o5 := (42, 157)

/-- Seed 4, box: the RT conditions for every record in `rtS4Box` with `smin ≥ 710` (binding: g2). -/
theorem rt_s4_box (D : ArbHeldTimed.Dl) (hB : rtS4Box.has D) (H_SERVER_MIN : 710 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D := by
  simp only [RtBox.has, inI, rtS4Box] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩⟩

/-- Seed 1, slow reading. -/
def rtS1Slow : RtBox where
  wr1s := (667, 943)
  wr2s := (467, 697)
  wr1g := (800, 1125)
  wr2g := (358, 556)
  wfb := (216, 288)
  wa0s := (638, 903)
  wq := (325, 429)
  wg1 := (524, 677)
  wa01 := (540, 795)
  wfa1 := (205, 276)
  wg2 := (503, 651)
  wa02 := (669, 955)
  wfa2 := (519, 677)
  o6 := (100, 124)
  o5 := (93, 157)

/-- Seed 1, slow: the RT conditions for every record in `rtS1Slow` with `smin ≥ 6` (binding: g1). -/
theorem rt_s1_slow (D : ArbHeldTimed.Dl) (hB : rtS1Slow.has D) (H_SERVER_MIN : 6 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS1Slow] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 2, slow reading. -/
def rtS2Slow : RtBox where
  wr1s := (643, 906)
  wr2s := (777, 1114)
  wr1g := (795, 1100)
  wr2g := (437, 686)
  wfb := (216, 288)
  wa0s := (578, 849)
  wq := (525, 677)
  wg1 := (610, 801)
  wa01 := (504, 760)
  wfa1 := (314, 423)
  wg2 := (785, 1015)
  wa02 := (649, 940)
  wfa2 := (216, 288)
  o6 := (100, 124)
  o5 := (93, 157)

/-- Seed 2, slow: the RT conditions for every record in `rtS2Slow` with `smin ≥ 189` (binding: g1). -/
theorem rt_s2_slow (D : ArbHeldTimed.Dl) (hB : rtS2Slow.has D) (H_SERVER_MIN : 189 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS2Slow] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 3, slow reading. -/
def rtS3Slow : RtBox where
  wr1s := (433, 669)
  wr2s := (645, 901)
  wr1g := (523, 774)
  wr2g := (775, 1099)
  wfb := (757, 973)
  wa0s := (505, 761)
  wq := (543, 714)
  wg1 := (662, 972)
  wa01 := (419, 809)
  wfa1 := (186, 298)
  wg2 := (677, 879)
  wa02 := (670, 965)
  wfa2 := (531, 685)
  o6 := (100, 124)
  o5 := (93, 157)

/-- Seed 3, slow: the RT conditions for every record in `rtS3Slow` with `smin ≥ 24` (binding: g2). -/
theorem rt_s3_slow (D : ArbHeldTimed.Dl) (hB : rtS3Slow.has D) (H_SERVER_MIN : 24 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS3Slow] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 4, slow reading. -/
def rtS4Slow : RtBox where
  wr1s := (800, 1112)
  wr2s := (613, 874)
  wr1g := (414, 620)
  wr2g := (756, 1046)
  wfb := (216, 288)
  wa0s := (749, 1079)
  wq := (434, 571)
  wg1 := (356, 471)
  wa01 := (667, 978)
  wfa1 := (534, 689)
  wg2 := (671, 863)
  wa02 := (643, 942)
  wfa2 := (205, 274)
  o6 := (100, 124)
  o5 := (93, 157)

/-- Seed 4, slow: the RT conditions for every record in `rtS4Slow` with `smin ≥ 0` (any server). -/
theorem rt_s4_slow (D : ArbHeldTimed.Dl) (hB : rtS4Slow.has D) (H_SERVER_MIN : 0 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS4Slow] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 1, fast reading. -/
def rtS1Fast : RtBox where
  wr1s := (260, 445)
  wr2s := (175, 340)
  wr1g := (313, 532)
  wr2g := (129, 275)
  wfb := (76, 119)
  wa0s := (262, 442)
  wq := (122, 184)
  wg1 := (209, 290)
  wa01 := (196, 375)
  wfa1 := (71, 114)
  wg2 := (176, 252)
  wa02 := (259, 453)
  wfa2 := (195, 281)
  o6 := (45, 56)
  o5 := (42, 63)

/-- Seed 1, fast: the RT conditions for every record in `rtS1Fast` with `smin ≥ 66` (binding: g1). -/
theorem rt_s1_fast (D : ArbHeldTimed.Dl) (hB : rtS1Fast.has D) (H_SERVER_MIN : 66 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS1Fast] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 2, fast reading. -/
def rtS2Fast : RtBox where
  wr1s := (254, 430)
  wr2s := (295, 526)
  wr1g := (326, 527)
  wr2g := (153, 344)
  wfb := (76, 119)
  wa0s := (225, 418)
  wq := (202, 281)
  wg1 := (241, 353)
  wa01 := (192, 378)
  wfa1 := (115, 183)
  wg2 := (325, 453)
  wa02 := (262, 466)
  wfa2 := (76, 119)
  o6 := (45, 56)
  o5 := (42, 63)

/-- Seed 2, fast: the RT conditions for every record in `rtS2Fast` with `smin ≥ 153` (binding: g1). -/
theorem rt_s2_fast (D : ArbHeldTimed.Dl) (hB : rtS2Fast.has D) (H_SERVER_MIN : 153 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS2Fast] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 3, fast reading. -/
def rtS3Fast : RtBox where
  wr1s := (166, 347)
  wr2s := (264, 434)
  wr1g := (202, 380)
  wr2g := (309, 531)
  wfb := (286, 400)
  wa0s := (178, 361)
  wq := (218, 321)
  wg1 := (274, 429)
  wa01 := (183, 404)
  wfa1 := (69, 122)
  wg2 := (268, 382)
  wa02 := (258, 461)
  wfa2 := (211, 292)
  o6 := (45, 56)
  o5 := (42, 63)

/-- Seed 3, fast: the RT conditions for every record in `rtS3Fast` with `smin ≥ 101` (binding: g2). -/
theorem rt_s3_fast (D : ArbHeldTimed.Dl) (hB : rtS3Fast.has D) (H_SERVER_MIN : 101 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS3Fast] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- Seed 4, fast reading. -/
def rtS4Fast : RtBox where
  wr1s := (317, 522)
  wr2s := (239, 418)
  wr1g := (152, 298)
  wr2g := (314, 505)
  wfb := (76, 119)
  wa0s := (312, 544)
  wq := (172, 254)
  wg1 := (127, 191)
  wa01 := (246, 464)
  wfa1 := (214, 296)
  wg2 := (258, 357)
  wa02 := (256, 468)
  wfa2 := (71, 112)
  o6 := (45, 56)
  o5 := (42, 63)

/-- Seed 4, fast: the RT conditions for every record in `rtS4Fast` with `smin ≥ 37` (binding: g2). -/
theorem rt_s4_fast (D : ArbHeldTimed.Dl) (hB : rtS4Fast.has D) (H_SERVER_MIN : 37 ≤ D.smin) :
    ArbHeldTimed.RT1 D ∧ ArbHeldTimed.RT2 D ∧ ArbHeldTimed.A0Fork D ∧
    ArbHeldTimed2.RT1b D ∧ ArbHeldTimed2.RT2b D ∧ ArbHeldTimed2.A0Fork2 D := by
  simp only [RtBox.has, inI, rtS4Fast] at hB
  unfold ArbHeldTimed.RT1 ArbHeldTimed2.RT1b ArbHeldTimed.A0Fork ArbHeldTimed2.A0Fork2
  exact ⟨Or.inl (by omega), ⟨by omega, by omega, by omega, by omega⟩, by omega, Or.inl (by omega),
    ⟨by omega, by omega, by omega, by omega⟩, by omega⟩
/-! ### Tightness: one less ps of `smin` and some record in the box violates the binding condition -/

/-- Seed 1, box: with `smin = 717` the record at the worst corner of `rtS1Box` breaks `g1`. -/
theorem rt_s1_box_tight : ∃ D : ArbHeldTimed.Dl, rtS1Box.has D ∧ D.smin = 717 ∧ ¬ ArbHeldTimed.RT2 D :=
  ⟨{ wr1s := 260, wr2s := 175, wr1g := 1125, wr2g := 129, wfb := 76, wa0s := 262, wq := 122, wg1 := 677, wa01 := 196, wfa1 := 276, wg2 := 176, wa02 := 259, wfa2 := 195, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 157, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 45, c1r := 45, c1f := 124, c2r := 45, c2f := 45, smin := 717,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS1Box], rfl, fun h => absurd h.g1 (by decide)⟩

/-- Seed 2, box: with `smin = 864` the record at the worst corner of `rtS2Box` breaks `g1`. -/
theorem rt_s2_box_tight : ∃ D : ArbHeldTimed.Dl, rtS2Box.has D ∧ D.smin = 864 ∧ ¬ ArbHeldTimed.RT2 D :=
  ⟨{ wr1s := 254, wr2s := 295, wr1g := 1100, wr2g := 153, wfb := 76, wa0s := 225, wq := 202, wg1 := 801, wa01 := 192, wfa1 := 423, wg2 := 325, wa02 := 262, wfa2 := 76, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 157, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 45, c1r := 45, c1f := 124, c2r := 45, c2f := 45, smin := 864,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS2Box], rfl, fun h => absurd h.g1 (by decide)⟩

/-- Seed 3, box: with `smin = 897` the record at the worst corner of `rtS3Box` breaks `g2`. -/
theorem rt_s3_box_tight : ∃ D : ArbHeldTimed.Dl, rtS3Box.has D ∧ D.smin = 897 ∧ ¬ ArbHeldTimed2.RT2b D :=
  ⟨{ wr1s := 166, wr2s := 264, wr1g := 202, wr2g := 1099, wfb := 286, wa0s := 178, wq := 218, wg1 := 274, wa01 := 183, wfa1 := 69, wg2 := 879, wa02 := 258, wfa2 := 685, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 42, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 124, c1r := 45, c1f := 45, c2r := 45, c2f := 124, smin := 897,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS3Box], rfl, fun h => absurd h.g2 (by decide)⟩

/-- Seed 4, box: with `smin = 709` the record at the worst corner of `rtS4Box` breaks `g2`. -/
theorem rt_s4_box_tight : ∃ D : ArbHeldTimed.Dl, rtS4Box.has D ∧ D.smin = 709 ∧ ¬ ArbHeldTimed2.RT2b D :=
  ⟨{ wr1s := 317, wr2s := 239, wr1g := 152, wr2g := 1046, wfb := 76, wa0s := 312, wq := 172, wg1 := 127, wa01 := 246, wfa1 := 214, wg2 := 863, wa02 := 256, wfa2 := 274, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 42, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 124, c1r := 45, c1f := 45, c2r := 45, c2f := 124, smin := 709,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS4Box], rfl, fun h => absurd h.g2 (by decide)⟩

/-- Seed 1, slow: with `smin = 5` the record at the worst corner of `rtS1Slow` breaks `g1`. -/
theorem rt_s1_slow_tight : ∃ D : ArbHeldTimed.Dl, rtS1Slow.has D ∧ D.smin = 5 ∧ ¬ ArbHeldTimed.RT2 D :=
  ⟨{ wr1s := 667, wr2s := 467, wr1g := 1125, wr2g := 358, wfb := 216, wa0s := 638, wq := 325, wg1 := 677, wa01 := 540, wfa1 := 276, wg2 := 503, wa02 := 669, wfa2 := 519, qr := 100, qf := 100, Rr1 := 93, Rf1 := 93, Rr2 := 93, Rf2 := 93, Rrq := 93, Rfq := 93, g1r1 := 93, g1f1 := 157, g1r2 := 93, g1f2 := 93, g1rq := 93, g1fq := 93, g2r := 100, g2f := 100, c1r := 100, c1f := 124, c2r := 100, c2f := 100, smin := 5,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS1Slow], rfl, fun h => absurd h.g1 (by decide)⟩

/-- Seed 2, slow: with `smin = 188` the record at the worst corner of `rtS2Slow` breaks `g1`. -/
theorem rt_s2_slow_tight : ∃ D : ArbHeldTimed.Dl, rtS2Slow.has D ∧ D.smin = 188 ∧ ¬ ArbHeldTimed.RT2 D :=
  ⟨{ wr1s := 643, wr2s := 777, wr1g := 1100, wr2g := 437, wfb := 216, wa0s := 578, wq := 525, wg1 := 801, wa01 := 504, wfa1 := 423, wg2 := 785, wa02 := 649, wfa2 := 216, qr := 100, qf := 100, Rr1 := 93, Rf1 := 93, Rr2 := 93, Rf2 := 93, Rrq := 93, Rfq := 93, g1r1 := 93, g1f1 := 157, g1r2 := 93, g1f2 := 93, g1rq := 93, g1fq := 93, g2r := 100, g2f := 100, c1r := 100, c1f := 124, c2r := 100, c2f := 100, smin := 188,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS2Slow], rfl, fun h => absurd h.g1 (by decide)⟩

/-- Seed 3, slow: with `smin = 23` the record at the worst corner of `rtS3Slow` breaks `g2`. -/
theorem rt_s3_slow_tight : ∃ D : ArbHeldTimed.Dl, rtS3Slow.has D ∧ D.smin = 23 ∧ ¬ ArbHeldTimed2.RT2b D :=
  ⟨{ wr1s := 433, wr2s := 645, wr1g := 523, wr2g := 1099, wfb := 757, wa0s := 505, wq := 543, wg1 := 662, wa01 := 419, wfa1 := 186, wg2 := 879, wa02 := 670, wfa2 := 685, qr := 100, qf := 100, Rr1 := 93, Rf1 := 93, Rr2 := 93, Rf2 := 93, Rrq := 93, Rfq := 93, g1r1 := 93, g1f1 := 93, g1r2 := 93, g1f2 := 93, g1rq := 93, g1fq := 93, g2r := 100, g2f := 124, c1r := 100, c1f := 100, c2r := 100, c2f := 124, smin := 23,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS3Slow], rfl, fun h => absurd h.g2 (by decide)⟩

/-- Seed 1, fast: with `smin = 65` the record at the worst corner of `rtS1Fast` breaks `g1`. -/
theorem rt_s1_fast_tight : ∃ D : ArbHeldTimed.Dl, rtS1Fast.has D ∧ D.smin = 65 ∧ ¬ ArbHeldTimed.RT2 D :=
  ⟨{ wr1s := 260, wr2s := 175, wr1g := 532, wr2g := 129, wfb := 76, wa0s := 262, wq := 122, wg1 := 290, wa01 := 196, wfa1 := 114, wg2 := 176, wa02 := 259, wfa2 := 195, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 63, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 45, c1r := 45, c1f := 56, c2r := 45, c2f := 45, smin := 65,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS1Fast], rfl, fun h => absurd h.g1 (by decide)⟩

/-- Seed 2, fast: with `smin = 152` the record at the worst corner of `rtS2Fast` breaks `g1`. -/
theorem rt_s2_fast_tight : ∃ D : ArbHeldTimed.Dl, rtS2Fast.has D ∧ D.smin = 152 ∧ ¬ ArbHeldTimed.RT2 D :=
  ⟨{ wr1s := 254, wr2s := 295, wr1g := 527, wr2g := 153, wfb := 76, wa0s := 225, wq := 202, wg1 := 353, wa01 := 192, wfa1 := 183, wg2 := 325, wa02 := 262, wfa2 := 76, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 63, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 45, c1r := 45, c1f := 56, c2r := 45, c2f := 45, smin := 152,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS2Fast], rfl, fun h => absurd h.g1 (by decide)⟩

/-- Seed 3, fast: with `smin = 100` the record at the worst corner of `rtS3Fast` breaks `g2`. -/
theorem rt_s3_fast_tight : ∃ D : ArbHeldTimed.Dl, rtS3Fast.has D ∧ D.smin = 100 ∧ ¬ ArbHeldTimed2.RT2b D :=
  ⟨{ wr1s := 166, wr2s := 264, wr1g := 202, wr2g := 531, wfb := 286, wa0s := 178, wq := 218, wg1 := 274, wa01 := 183, wfa1 := 69, wg2 := 382, wa02 := 258, wfa2 := 292, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 42, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 56, c1r := 45, c1f := 45, c2r := 45, c2f := 56, smin := 100,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS3Fast], rfl, fun h => absurd h.g2 (by decide)⟩

/-- Seed 4, fast: with `smin = 36` the record at the worst corner of `rtS4Fast` breaks `g2`. -/
theorem rt_s4_fast_tight : ∃ D : ArbHeldTimed.Dl, rtS4Fast.has D ∧ D.smin = 36 ∧ ¬ ArbHeldTimed2.RT2b D :=
  ⟨{ wr1s := 317, wr2s := 239, wr1g := 152, wr2g := 505, wfb := 76, wa0s := 312, wq := 172, wg1 := 127, wa01 := 246, wfa1 := 214, wg2 := 357, wa02 := 256, wfa2 := 112, qr := 45, qf := 45, Rr1 := 42, Rf1 := 42, Rr2 := 42, Rf2 := 42, Rrq := 42, Rfq := 42, g1r1 := 42, g1f1 := 42, g1r2 := 42, g1f2 := 42, g1rq := 42, g1fq := 42, g2r := 45, g2f := 56, c1r := 45, c1f := 45, c2r := 45, c2f := 56, smin := 36,
     H_NONNEG := by decide, H_RISE_LE_FALL := by decide, H_LOOP_POS := by decide },
   by simp [RtBox.has, inI, rtS4Fast], rfl, fun h => absurd h.g2 (by decide)⟩
end Formal.Cells.OnNetlistArb
