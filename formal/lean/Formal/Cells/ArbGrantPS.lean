import Formal.Cells.ArbViewPS
import Formal.Cells.GrantExcl
import Formal.Cells.SpecLatchFact

/-!
# Formal.Cells.ArbGrantPS — THE target's arbiter grants are exclusive once H_ARB(T) has settled the state, every behaviour

Shard B, THE goal, H_ARB(T). For each of THE target's nine arbiters (`DecodedPS.arbs`), its two grant LUTs (ugrant O5:
fires only if its q pin reads 1; ugrant O6: only if it reads 0, with its VCC-tied pin at 1), GENERATED with every
pin's copy chain. `grows_ok` (kernel decide): both grant gates are collapsed through checked chains, read the
arbiter's state node, meet their INIT fact (`gfact`), and their tied pins are constant gates.
`target_ps_grants_excl`: in every behaviour of THE circuit, at its corner, for every T with H_ARB(T) (`ArbOK T arbs`),
whenever an arbiter's state-LUT inputs are constant on `[t1, t2]`, its two grants are never both high at any t with
`t1 + T + hi ≤ t ≤ t2 + lo` for both grant gates' q-pin bands (and t past both collapse starts).
Not covered: the settling window itself (H_ARB lets q move for T; ArbTSpec.spec_double_ack), the ack C-elements.
-/

namespace Formal.Cells.ArbGrantPS
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecFbChain
  Formal.Cells.SpecCElemFact Formal.Cells.SpecLatchFact Formal.Cells.ArbViewPS Formal.Cells.GrantExcl

structure GSide where
  q : Nat
  pins : Pins
  j : Nat
  held : List Bool
  ov : List Bool

def GSide.g (s : GSide) : Gate := gateAt s.q
def GSide.src (s : GSide) (i : Nat) : Nat := ((pcsOf s.pins).getD i ⟨0, []⟩).src
def GSide.arcs (s : GSide) : Nat → List Arc := pinArcs s.g (pcsOf s.pins)
def GSide.S (p : DelayPar) (s : GSide) : Nat := cStart p s.g (pcsOf s.pins)
def GSide.lo (p : DelayPar) (c : ℚ) (s : GSide) (i : Nat) : Nat :=
  ((s.arcs i).map (Formal.Cells.Ua1Static.lo p.g p.κ c)).sum.toNat
def GSide.hi (p : DelayPar) (c : ℚ) (s : GSide) (i : Nat) : Nat :=
  ((s.arcs i).map (Formal.Cells.Ua1Static.hi p.g p.κ c)).sum.toNat

def gfact (k init j : Nat) (b : Bool) (held ov : Nat → Bool) : Bool :=
  (List.range (2 ^ k)).all fun a => !(heldAt k held ov a && init.testBit a) || (a.testBit j == b)

theorem hf_of_gfact {k init j : Nat} {b : Bool} {held ov : Nat → Bool} (h : gfact k init j b held ov = true)
    (hj : j < k) : ∀ v : Nat → Bool, (∀ i, i < k → held i = true → v i = ov i) →
      init.testBit (addr k v) = true → v j = b := by
  intro v hh ho
  simp only [gfact, List.all_eq_true, List.mem_range] at h
  have := h _ (Formal.Timing.SpecLoop.addr_lt k v)
  rw [heldAt_of hh, ho, Formal.Timing.SpecLoop.addr_testBit k v j hj] at this
  simpa using this

def sideOK (s : GSide) (qn : Nat) (b : Bool) : Bool :=
  s.g.k == s.pins.length && decide (s.j < s.g.k) && gfact s.g.k s.g.init s.j b (fl s.held) (fl s.ov) &&
  viewOK s.q s.pins && (s.pins.getD s.j ([], 0)).2 == qn && (gateAt s.q).out == s.q &&
  (List.range s.g.k).all fun i => !(fl s.held i) || constAt (s.pins.getD i ([], 0)).2 (fl s.ov i)

/-- Arbiter `i` of the netlist's list. -/
def arbAt (i : Nat) : ArbNodes := arbs.getD i ⟨0, []⟩

structure GRow where
  ai : Nat
  s1 : GSide
  s2 : GSide

def growOK (r : GRow) : Bool :=
  decide (r.ai < arbs.length) && sideOK r.s1 (arbAt r.ai).q true &&
    sideOK r.s2 (arbAt r.ai).q false

theorem src_eq (s : GSide) {i : Nat} (hi : i < s.pins.length) : s.src i = (s.pins.getD i ([], 0)).2 := by
  simp only [GSide.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

theorem side_facts {p : DelayPar} {x : Beh} (hb : Behaves p (circuit net boundary) x) {s : GSide} {qn : Nat}
    {b : Bool} (h : sideOK s qn b = true) :
    s.j < s.g.k ∧ s.src s.j = qn ∧
    (∀ v : Nat → Bool, (∀ i, i < s.g.k → fl s.held i = true → v i = fl s.ov i) →
      s.g.init.testBit (addr s.g.k v) = true → v s.j = b) ∧
    (∀ i, i < s.g.k → fl s.held i = true → ∀ t, x (s.src i) t = fl s.ov i) ∧ s.g.out = s.q := by
  simp only [sideOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hj⟩, hf⟩, -⟩, hq⟩, hout⟩, hh⟩ := h
  refine ⟨hj, by rw [src_eq s (by omega), hq], hf_of_gfact hf hj, fun i hi hheld t => ?_, hout⟩
  have h := hh i hi
  simp only [hheld, Bool.not_true, Bool.false_or, constAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := h
  rw [src_eq s (by omega), const_hold hb hs1 hs2 hs3 hs4 t, hs5]

set_option maxRecDepth 100000 in
/-- THE target's nine arbiters' grant pairs (GENERATED). -/
def grows : List GRow := [
  ⟨0, ⟨144448, [([144425, 144424, 144423, 144422, 144426], 144471), ([144430, 144429, 144428, 144427, 144431], 144547), ([144434, 144433, 144432], 144435), ([144440, 144439, 144438, 144437, 144436, 144441], 151633), ([144443, 144442], 144444)], 0, [false, false, true, false, true], [false, false, false, false, true]⟩, ⟨144447, [([144425, 144424, 144423, 144422, 144426], 144471), ([144430, 144429, 144428, 144427, 144431], 144547), ([144434, 144433, 144432], 144435), ([144440, 144439, 144438, 144437, 144436, 144441], 151633), ([144443, 144442], 144444), ([144446, 144445], 144444)], 0, [false, false, true, false, true, true], [false, false, false, false, true, true]⟩⟩,
  ⟨1, ⟨146237, [([146221, 146220, 146194, 146197], 146200), ([146226, 146225, 146224, 146223, 146222, 146184, 146183, 146190], 143891), ([146228, 146227, 143822], 143802), ([146230, 146229], 143777), ([146233, 146232, 146231, 146178, 146177, 146176, 146175, 146174, 146173, 146182], 81162)], 0, [false, false, true, true, false], [false, false, false, true, false]⟩, ⟨146236, [([146221, 146220, 146194, 146197], 146200), ([146226, 146225, 146224, 146223, 146222, 146184, 146183, 146190], 143891), ([146228, 146227, 143822], 143802), ([146230, 146229], 143777), ([146233, 146232, 146231, 146178, 146177, 146176, 146175, 146174, 146173, 146182], 81162), ([146235, 146234], 143777)], 0, [false, false, true, true, false, true], [false, false, false, true, false, true]⟩⟩,
  ⟨2, ⟨37747, [([37722, 37721, 37720, 37719, 37723], 37766), ([37730, 37729, 37728, 37727, 37726, 37725, 37724, 37731], 154001), ([37734, 37733, 37732], 37735), ([37739, 37738, 37737, 37736, 37740], 33548), ([37742, 37741], 37743)], 0, [false, false, true, false, true], [false, false, false, false, true]⟩, ⟨37746, [([37722, 37721, 37720, 37719, 37723], 37766), ([37730, 37729, 37728, 37727, 37726, 37725, 37724, 37731], 154001), ([37734, 37733, 37732], 37735), ([37739, 37738, 37737, 37736, 37740], 33548), ([37742, 37741], 37743), ([37745, 37744], 37743)], 0, [false, false, true, false, true, true], [false, false, false, false, true, true]⟩⟩,
  ⟨3, ⟨37996, [([37982, 37981, 37980, 37965, 37964, 37963, 37970], 37767), ([37984, 37983, 37954, 37953, 37952, 37951, 37950, 37949, 37948, 37947, 37946, 37957], 146120), ([37987, 37986, 37985], 37988), ([37990, 37989], 37977), ([37992, 37991, 37971, 37974], 37978)], 4, [false, false, true, true, false], [false, false, false, true, false]⟩, ⟨37995, [([37982, 37981, 37980, 37965, 37964, 37963, 37970], 37767), ([37984, 37983, 37954, 37953, 37952, 37951, 37950, 37949, 37948, 37947, 37946, 37957], 146120), ([37987, 37986, 37985], 37988), ([37990, 37989], 37977), ([37992, 37991, 37971, 37974], 37978), ([37994, 37993], 37977)], 4, [false, false, true, true, false, true], [false, false, false, true, false, true]⟩⟩,
  ⟨4, ⟨37292, [([37272, 37271, 37270, 28269, 28272], 28275), ([37276, 37275, 37274, 37273, 37255], 37258), ([37280, 37279, 37278, 37277, 37281], 37325), ([37283, 37282], 37265), ([37287, 37286, 37285, 37284, 37288], 28334)], 2, [false, true, false, true, false], [false, false, false, true, false]⟩, ⟨37291, [([37272, 37271, 37270, 28269, 28272], 28275), ([37276, 37275, 37274, 37273, 37255], 37258), ([37280, 37279, 37278, 37277, 37281], 37325), ([37283, 37282], 37265), ([37287, 37286, 37285, 37284, 37288], 28334), ([37290, 37289], 37265)], 2, [false, true, false, true, false, true], [false, false, false, true, false, true]⟩⟩,
  ⟨5, ⟨37269, [([37250, 37249, 37248, 28287, 28291], 33245), ([37254, 37253, 37252, 37251, 28297, 28300], 28304), ([37257, 37256, 37255], 37258), ([37262, 37261, 37260, 37259, 28277, 28280], 28335), ([37264, 37263], 37265)], 1, [false, false, true, false, true], [false, false, false, false, true]⟩, ⟨37268, [([37250, 37249, 37248, 28287, 28291], 33245), ([37254, 37253, 37252, 37251, 28297, 28300], 28304), ([37257, 37256, 37255], 37258), ([37262, 37261, 37260, 37259, 28277, 28280], 28335), ([37264, 37263], 37265), ([37267, 37266], 37265)], 1, [false, false, true, false, true, true], [false, false, false, false, true, true]⟩⟩,
  ⟨6, ⟨37347, [([37329, 37328, 37327], 37330), ([37334, 37333, 37332, 37331, 28351, 10291, 10290, 10289, 10301], 130408), ([37336, 37335], 37337), ([37340, 37339, 37338, 28344, 28350], 28366), ([37343, 37342, 37341, 28337, 28336, 28341], 37517)], 3, [true, false, true, false, false], [false, false, true, false, false]⟩, ⟨37346, [([37329, 37328, 37327], 37330), ([37334, 37333, 37332, 37331, 28351, 10291, 10290, 10289, 10301], 130408), ([37336, 37335], 37337), ([37340, 37339, 37338, 28344, 28350], 28366), ([37343, 37342, 37341, 28337, 28336, 28341], 37517), ([37345, 37344], 37337)], 3, [true, false, true, false, false, true], [false, false, true, false, false, true]⟩⟩,
  ⟨7, ⟨47343, [([47326, 47325, 47324], 47327), ([47329, 47328], 47330), ([47334, 47333, 47332, 47331, 47276, 47279], 47283), ([47337, 47336, 47335, 47272, 47275], 47304), ([47339, 47338, 47253, 47252, 47251, 47250, 47249, 47258], 53361)], 2, [true, true, false, false, false], [false, true, false, false, false]⟩, ⟨47342, [([47326, 47325, 47324], 47327), ([47329, 47328], 47330), ([47334, 47333, 47332, 47331, 47276, 47279], 47283), ([47337, 47336, 47335, 47272, 47275], 47304), ([47339, 47338, 47253, 47252, 47251, 47250, 47249, 47258], 53361), ([47341, 47340], 47330)], 2, [true, true, false, false, false, true], [false, true, false, false, false, true]⟩⟩,
  ⟨8, ⟨143662, [([143632, 143631, 143630, 143629, 143628, 143627, 143633], 143892), ([143636, 143635, 143634], 143637), ([143642, 143641, 143640, 143639, 143638, 143643], 146154), ([143645, 143644], 143646), ([143657, 143656, 143655, 143654, 143653, 143652, 143651, 143650, 143649, 143648, 143647, 143658], 81163)], 2, [false, true, false, true, false], [false, false, false, true, false]⟩, ⟨143661, [([143632, 143631, 143630, 143629, 143628, 143627, 143633], 143892), ([143636, 143635, 143634], 143637), ([143642, 143641, 143640, 143639, 143638, 143643], 146154), ([143645, 143644], 143646), ([143657, 143656, 143655, 143654, 143653, 143652, 143651, 143650, 143649, 143648, 143647, 143658], 81163), ([143660, 143659], 143646)], 2, [false, true, false, true, false, true], [false, false, false, true, false, true]⟩⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem grows_ok : grows.all growOK = true := by decide +kernel

/-- **Grants exclusive after H_ARB(T) settles, for THE target's nine arbiters, in every behaviour.** -/
theorem target_ps_grants_excl {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ grows, ∀ T : Nat, ArbOK T arbs x → ∀ t1 t2 : Nat,
      (∀ n ∈ (arbAt r.ai).ins, ConstOn (x n) t1 t2) →
      ∀ t, r.s1.S p ≤ t → r.s2.S p ≤ t → t1 + T + r.s1.hi p c r.s1.j ≤ t → t ≤ t2 + r.s1.lo p c r.s1.j →
        t1 + T + r.s2.hi p c r.s2.j ≤ t → t ≤ t2 + r.s2.lo p c r.s2.j →
        ¬ (x r.s1.q t = true ∧ x r.s2.q t = true) := by
  have hall : ∀ r ∈ grows, growOK r = true := by
    have := grows_ok; simp only [List.all_eq_true] at this; exact this
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb
    (grows.flatMap fun r => [(r.s1.q, r.s1.pins), (r.s2.q, r.s2.pins)]) (by
      simp only [List.all_eq_true, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      rintro e ⟨r, hr, he⟩
      have h := hall r hr
      simp only [growOK, sideOK, Bool.and_eq_true] at h
      rcases he with rfl | rfl
      · exact h.1.2.1.1.1.2
      · exact h.2.1.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr T harb t1 t2 hin => ?_⟩
  have h := hall r hr
  simp only [growOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hai, h1⟩, h2⟩ := h
  obtain ⟨j1, q1, f1, hh1, o1⟩ := side_facts hb h1
  obtain ⟨j2, q2, f2, hh2, o2⟩ := side_facts hb h2
  have hA : arbAt r.ai ∈ arbs := by
    unfold arbAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hai]; exact List.getElem_mem hai
  have harb1 : ArbOK T [arbAt r.ai] x := fun a ha => by
    rw [List.mem_singleton] at ha; subst ha; exact harb _ hA
  have g1 : CGateOK p c r.s1.g r.s1.src r.s1.arcs (r.s1.S p) x :=
    hcol (r.s1.q, r.s1.pins) (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
  have g2 : CGateOK p c r.s2.g r.s2.src r.s2.arcs (r.s2.S p) x :=
    hcol (r.s2.q, r.s2.pins) (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
  have key := grants_excl_arb g1 g2 (cbands_of_sums r.s1.arcs) (cbands_of_sums r.s2.arcs) _ j1 j2 q1 q2
    (fl r.s1.held) (fl r.s1.ov) (fl r.s2.held) (fl r.s2.ov) f1 f2 hh1 hh2 T harb1 hin
  rw [o1, o2] at key
  exact key

end Formal.Cells.ArbGrantPS
