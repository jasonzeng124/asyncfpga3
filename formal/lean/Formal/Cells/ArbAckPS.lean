import Formal.Cells.ArbGrantPS
import Formal.Cells.AckLow

/-!
# Formal.Cells.ArbAckPS — THE target's arbiters do not acknowledge the losing client while the state is settled

Shard B, THE goal, H_ARB(T). For 8 of THE target's 9 arbiters (those named `uarb1`; 16 ack C-elements ua1/ua2), each
ack gate paired with the grant it reads and the arbiter state that grant reads (GENERATED, every pin's chain;
`arows_ok` by kernel decide: chains, wiring grant -> ack and state -> grant, INIT facts, ties).
`target_ps_ack_low`: in every behaviour of THE circuit, at its corner: if the arbiter's state node shows the losing
value (!b, b = the value this grant needs) on [a, e], and the ack was low on its feedback window before s, then the
ack stays low on [s, e'] whatever the server's A0 does, provided s and e' sit inside the grant's settled window
(`grant.S + hi gp ≤ s`, `a + hi j + hi gp ≤ s`, `e' + ... ≤ e + lo j + lo gp`). With `ArbOK T` (state constant T
after its inputs) this is the arbiter's one-acknowledge property while the state stays settled.
Not covered: the settling window; that the server's A0 only rises after it (server path); the ninth arbiter.
-/

namespace Formal.Cells.ArbAckPS
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecFbChain
  Formal.Cells.SpecCElemFact Formal.Cells.SpecLatchFact Formal.Cells.ArbViewPS Formal.Cells.ArbGrantPS
  Formal.Cells.AckLow

structure ASide where
  q : Nat
  pins : Pins
  gp : Nat
  fb : Nat
  held : List Bool
  ov : List Bool

def ASide.g (s : ASide) : Gate := gateAt s.q
def ASide.src (s : ASide) (i : Nat) : Nat := ((pcsOf s.pins).getD i ⟨0, []⟩).src
def ASide.arcs (s : ASide) : Nat → List Arc := pinArcs s.g (pcsOf s.pins)
def ASide.S (p : DelayPar) (s : ASide) : Nat := cStart p s.g (pcsOf s.pins)
def ASide.lo (p : DelayPar) (c : ℚ) (s : ASide) (i : Nat) : Nat :=
  ((s.arcs i).map (Formal.Cells.Ua1Static.lo p.g p.κ c)).sum.toNat
def ASide.hi (p : DelayPar) (c : ℚ) (s : ASide) (i : Nat) : Nat :=
  ((s.arcs i).map (Formal.Cells.Ua1Static.hi p.g p.κ c)).sum.toNat

def afact (k init gp fb : Nat) (held ov : Nat → Bool) : Bool :=
  (List.range (2 ^ k)).all fun a => !(heldAt k held ov a && !a.testBit gp && !a.testBit fb) || !init.testBit a

theorem hf_of_afact {k init gp fb : Nat} {held ov : Nat → Bool} (h : afact k init gp fb held ov = true)
    (hgp : gp < k) (hfb : fb < k) : ∀ v : Nat → Bool, (∀ i, i < k → held i = true → v i = ov i) →
      v gp = false → v fb = false → init.testBit (addr k v) = false := by
  intro v hh h1 h2
  simp only [afact, List.all_eq_true, List.mem_range] at h
  have := h _ (Formal.Timing.SpecLoop.addr_lt k v)
  rw [heldAt_of hh, Formal.Timing.SpecLoop.addr_testBit k v gp hgp, Formal.Timing.SpecLoop.addr_testBit k v fb hfb,
    h1, h2] at this
  simpa using this

def asideOK (s : ASide) (grantNode : Nat) : Bool :=
  s.g.k == s.pins.length && decide (s.gp < s.g.k) && decide (s.fb < s.g.k) &&
  afact s.g.k s.g.init s.gp s.fb (fl s.held) (fl s.ov) && viewOK s.q s.pins &&
  (s.pins.getD s.gp ([], 0)).2 == grantNode && (s.pins.getD s.fb ([], 0)).2 == s.q && (gateAt s.q).out == s.q &&
  (List.range s.g.k).all fun i => !(fl s.held i) || constAt (s.pins.getD i ([], 0)).2 (fl s.ov i)

structure ARow where
  ai : Nat
  b : Bool
  gr : GSide
  ack : ASide

def arowOK (r : ARow) : Bool :=
  decide (r.ai < arbs.length) && sideOK r.gr (arbAt r.ai).q r.b && asideOK r.ack r.gr.q

theorem asrc_eq (s : ASide) {i : Nat} (hi : i < s.pins.length) : s.src i = (s.pins.getD i ([], 0)).2 := by
  simp only [ASide.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

set_option maxRecDepth 100000 in
/-- THE target's 16 arbiter acks with their grants (GENERATED). -/
def arows : List ARow := [
  ⟨0, true, ⟨144448, [([144425, 144424, 144423, 144422, 144426], 144471), ([144430, 144429, 144428, 144427, 144431], 144547), ([144434, 144433, 144432], 144435), ([144440, 144439, 144438, 144437, 144436, 144441], 151633), ([144443, 144442], 144444)], 0, [false, false, true, false, true], [false, false, false, false, true]⟩, ⟨146522, [([146507, 146506, 144432], 144435), ([146510, 146509, 146508, 146511], 144448), ([146513, 146512, 144460, 144459, 144465], 144585), ([146515, 146514, 144532, 144531, 140810, 127324, 87313, 87312, 9573, 5001, 2383, 1181, 1180, 1179, 1185], 186905), ([146518, 146517, 146516, 146519], 146522), ([146521, 146520, 144432], 144435)], 1, 4, [true, false, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨0, false, ⟨144447, [([144425, 144424, 144423, 144422, 144426], 144471), ([144430, 144429, 144428, 144427, 144431], 144547), ([144434, 144433, 144432], 144435), ([144440, 144439, 144438, 144437, 144436, 144441], 151633), ([144443, 144442], 144444), ([144446, 144445], 144444)], 0, [false, false, true, false, true, true], [false, false, false, false, true, true]⟩, ⟨144569, [([144550, 144549, 144459, 144465], 144585), ([144554, 144553, 144552, 144551, 140990, 87314, 87313, 87312, 9573, 5001, 2383, 1181, 1180, 1179, 1185], 186905), ([144558, 144557, 144556, 144555, 144559], 144447), ([144562, 144561, 144560], 144563), ([144565, 144564, 144522, 144526], 144569), ([144568, 144567, 144566], 144563)], 2, 4, [false, false, false, true, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨1, true, ⟨146237, [([146221, 146220, 146194, 146197], 146200), ([146226, 146225, 146224, 146223, 146222, 146184, 146183, 146190], 143891), ([146228, 146227, 143822], 143802), ([146230, 146229], 143777), ([146233, 146232, 146231, 146178, 146177, 146176, 146175, 146174, 146173, 146182], 81162)], 0, [false, false, true, true, false], [false, false, false, true, false]⟩, ⟨143846, [([143829, 143828, 143827, 143830], 143846), ([143834, 143833, 143832, 143831, 143835], 146237), ([143837, 143836, 143796, 134492, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([143839, 143838, 143822], 143802), ([143843, 143842, 143841, 143840, 143813, 143812, 143811, 143810, 143809, 143808, 143807, 92401, 92404], 92411), ([143845, 143844, 143799], 143802)], 1, 0, [false, false, false, true, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨1, false, ⟨146236, [([146221, 146220, 146194, 146197], 146200), ([146226, 146225, 146224, 146223, 146222, 146184, 146183, 146190], 143891), ([146228, 146227, 143822], 143802), ([146230, 146229], 143777), ([146233, 146232, 146231, 146178, 146177, 146176, 146175, 146174, 146173, 146182], 81162), ([146235, 146234], 143777)], 0, [false, false, true, true, false, true], [false, false, false, true, false, true]⟩, ⟨143825, [([143798, 143797, 143796, 134492, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([143801, 143800, 143799], 143802), ([143806, 143805, 143804, 143803, 143786, 143789], 143825), ([143816, 143815, 143814, 143813, 143812, 143811, 143810, 143809, 143808, 143807, 92401, 92404], 92411), ([143820, 143819, 143818, 143817, 143821], 146236), ([143824, 143823, 143822], 143802)], 4, 2, [false, true, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨2, true, ⟨37747, [([37722, 37721, 37720, 37719, 37723], 37766), ([37730, 37729, 37728, 37727, 37726, 37725, 37724, 37731], 154001), ([37734, 37733, 37732], 37735), ([37739, 37738, 37737, 37736, 37740], 33548), ([37742, 37741], 37743)], 0, [false, false, true, false, true], [false, false, false, false, true]⟩, ⟨37787, [([37769, 37768, 37755, 37754, 37753, 37752, 37758], 38015), ([37773, 37772, 37771, 37770, 28766, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([37776, 37775, 37774], 37735), ([37779, 37778, 37777, 37780], 37747), ([37783, 37782, 37781, 37784], 37787), ([37786, 37785, 37732], 37735)], 3, 4, [false, false, true, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨2, false, ⟨37746, [([37722, 37721, 37720, 37719, 37723], 37766), ([37730, 37729, 37728, 37727, 37726, 37725, 37724, 37731], 154001), ([37734, 37733, 37732], 37735), ([37739, 37738, 37737, 37736, 37740], 33548), ([37742, 37741], 37743), ([37745, 37744], 37743)], 0, [false, false, true, false, true, true], [false, false, false, false, true, true]⟩, ⟨43220, [([43205, 43204, 37755, 37754, 37753, 37752, 37758], 38015), ([43209, 43208, 43207, 43206, 29105, 29112], 37746), ([43211, 43210, 37774], 37735), ([43214, 43213, 43212, 43215], 43220), ([43217, 43216, 37771, 37770, 28766, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([43219, 43218, 37732], 37735)], 1, 3, [false, false, true, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨4, true, ⟨37292, [([37272, 37271, 37270, 28269, 28272], 28275), ([37276, 37275, 37274, 37273, 37255], 37258), ([37280, 37279, 37278, 37277, 37281], 37325), ([37283, 37282], 37265), ([37287, 37286, 37285, 37284, 37288], 28334)], 2, [false, true, false, true, false], [false, false, false, true, false]⟩, ⟨43044, [([43031, 43030, 28211, 17746, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([43033, 43032, 37274, 37273, 37255], 37258), ([43036, 43035, 43034, 43037], 37292), ([43039, 43038, 37310, 37309, 37313], 33173), ([43041, 43040, 42973, 42976], 43044), ([43043, 43042, 37274, 37273, 37255], 37258)], 2, 4, [false, true, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨4, false, ⟨37291, [([37272, 37271, 37270, 28269, 28272], 28275), ([37276, 37275, 37274, 37273, 37255], 37258), ([37280, 37279, 37278, 37277, 37281], 37325), ([37283, 37282], 37265), ([37287, 37286, 37285, 37284, 37288], 28334), ([37290, 37289], 37265)], 2, [false, true, false, true, false, true], [false, false, false, true, false, true]⟩, ⟨42957, [([42944, 42943, 37176], 37179), ([42946, 42945, 37181, 37180, 37184], 37291), ([42949, 42948, 42947, 28211, 17746, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([42952, 42951, 42950, 37309, 37313], 33173), ([42954, 42953, 37185, 37188], 42957), ([42956, 42955, 37176], 37179)], 1, 4, [true, false, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨5, true, ⟨37269, [([37250, 37249, 37248, 28287, 28291], 33245), ([37254, 37253, 37252, 37251, 28297, 28300], 28304), ([37257, 37256, 37255], 37258), ([37262, 37261, 37260, 37259, 28277, 28280], 28335), ([37264, 37263], 37265)], 1, [false, false, true, false, true], [false, false, false, false, true]⟩, ⟨43028, [([43013, 43012, 42983, 42986], 43028), ([43016, 43015, 43014, 43017], 37269), ([43019, 43018, 42992, 42991, 42995], 43085), ([43021, 43020, 37317, 37316, 28211, 17746, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([43025, 43024, 43023, 43022, 37255], 37258), ([43027, 43026, 37274, 37273, 37255], 37258)], 1, 0, [false, false, false, false, true, true], [false, false, false, false, false, false]⟩⟩,
  ⟨5, false, ⟨37268, [([37250, 37249, 37248, 28287, 28291], 33245), ([37254, 37253, 37252, 37251, 28297, 28300], 28304), ([37257, 37256, 37255], 37258), ([37262, 37261, 37260, 37259, 28277, 28280], 28335), ([37264, 37263], 37265), ([37267, 37266], 37265)], 1, [false, false, true, false, true, true], [false, false, false, false, true, true]⟩, ⟨43010, [([42994, 42993, 42992, 42991, 42995], 43085), ([42997, 42996, 37317, 37316, 28211, 17746, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([42999, 42998, 33202, 33206], 37268), ([43002, 43001, 43000, 43003], 43010), ([43005, 43004, 37255], 37258), ([43009, 43008, 43007, 43006, 37274, 37273, 37255], 37258)], 2, 3, [false, false, false, false, true, true], [false, false, false, false, false, false]⟩⟩,
  ⟨6, true, ⟨37347, [([37329, 37328, 37327], 37330), ([37334, 37333, 37332, 37331, 28351, 10291, 10290, 10289, 10301], 130408), ([37336, 37335], 37337), ([37340, 37339, 37338, 28344, 28350], 28366), ([37343, 37342, 37341, 28337, 28336, 28341], 37517)], 3, [true, false, true, false, false], [false, false, true, false, false]⟩, ⟨37369, [([37350, 37349, 37348, 37351], 37369), ([37357, 37356, 37355, 37354, 37353, 37352, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([37359, 37358, 37327], 37330), ([37362, 37361, 37360, 37363], 37347), ([37365, 37364, 28358, 28357, 28356, 28362], 43152), ([37368, 37367, 37366], 37330)], 3, 0, [false, false, true, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨6, false, ⟨37346, [([37329, 37328, 37327], 37330), ([37334, 37333, 37332, 37331, 28351, 10291, 10290, 10289, 10301], 130408), ([37336, 37335], 37337), ([37340, 37339, 37338, 28344, 28350], 28366), ([37343, 37342, 37341, 28337, 28336, 28341], 37517), ([37345, 37344], 37337)], 3, [true, false, true, false, false, true], [false, false, true, false, false, true]⟩, ⟨37463, [([37443, 37442, 28357, 28356, 28362], 43152), ([37446, 37445, 37444], 37447), ([37451, 37450, 37449, 37448, 37452], 37346), ([37455, 37454, 37453, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([37458, 37457, 37456, 37459], 37463), ([37462, 37461, 37460], 37447)], 2, 4, [false, true, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨7, true, ⟨47343, [([47326, 47325, 47324], 47327), ([47329, 47328], 47330), ([47334, 47333, 47332, 47331, 47276, 47279], 47283), ([47337, 47336, 47335, 47272, 47275], 47304), ([47339, 47338, 47253, 47252, 47251, 47250, 47249, 47258], 53361)], 2, [true, true, false, false, false], [false, true, false, false, false]⟩, ⟨52886, [([52872, 52871, 47268, 47267, 47266, 47265, 47264, 47263, 47271], 53219), ([52874, 52873, 47285], 47288), ([52878, 52877, 52876, 52875, 52879], 47343), ([52881, 52880, 37770, 28766, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([52883, 52882, 47310, 47313], 52886), ([52885, 52884, 47319], 47288)], 2, 4, [false, true, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨7, false, ⟨47342, [([47326, 47325, 47324], 47327), ([47329, 47328], 47330), ([47334, 47333, 47332, 47331, 47276, 47279], 47283), ([47337, 47336, 47335, 47272, 47275], 47304), ([47339, 47338, 47253, 47252, 47251, 47250, 47249, 47258], 53361), ([47341, 47340], 47330)], 2, [true, true, false, false, false, true], [false, true, false, false, false, true]⟩, ⟨53165, [([53150, 53149, 53133, 53136], 53165), ([53152, 53151, 14286, 14285, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([53154, 53153, 47623, 47622, 47621, 47620, 47626], 47342), ([53157, 53156, 53155], 47615), ([53161, 53160, 53159, 53158, 53162], 53219), ([53164, 53163, 47612], 47615)], 2, 0, [false, false, false, true, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨8, true, ⟨143662, [([143632, 143631, 143630, 143629, 143628, 143627, 143633], 143892), ([143636, 143635, 143634], 143637), ([143642, 143641, 143640, 143639, 143638, 143643], 146154), ([143645, 143644], 143646), ([143657, 143656, 143655, 143654, 143653, 143652, 143651, 143650, 143649, 143648, 143647, 143658], 81163)], 2, [false, true, false, true, false], [false, false, false, true, false]⟩, ⟨143689, [([143665, 143664, 143663, 134492, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([143667, 143666, 143634], 143637), ([143671, 143670, 143669, 143668, 143672], 143689), ([143679, 143678, 143677, 143676, 143675, 143674, 143673, 143680], 146367), ([143684, 143683, 143682, 143681, 143685], 143662), ([143688, 143687, 143686], 143637)], 4, 2, [false, true, false, false, false, true], [false, false, false, false, false, false]⟩⟩,
  ⟨8, false, ⟨143661, [([143632, 143631, 143630, 143629, 143628, 143627, 143633], 143892), ([143636, 143635, 143634], 143637), ([143642, 143641, 143640, 143639, 143638, 143643], 146154), ([143645, 143644], 143646), ([143657, 143656, 143655, 143654, 143653, 143652, 143651, 143650, 143649, 143648, 143647, 143658], 81163), ([143660, 143659], 143646)], 2, [false, true, false, true, false, true], [false, false, false, true, false, true]⟩, ⟨143712, [([143693, 143692, 143691, 143694], 143712), ([143698, 143697, 143696, 143695, 143676, 143675, 143674, 143673, 143680], 146367), ([143701, 143700, 143699, 120291, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([143706, 143705, 143704, 143703, 143702, 143707], 143661), ([143709, 143708, 143686], 143637), ([143711, 143710, 143634], 143637)], 3, 0, [false, false, false, false, true, true], [false, false, false, false, false, false]⟩⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem arows_ok : arows.all arowOK = true := by decide +kernel

/-- **The losing client's acknowledge stays low while the arbiter state shows the other value.** -/
theorem target_ps_ack_low {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ arows, ∀ a e s e' : Nat,
      (∀ t, a ≤ t → t ≤ e → x (arbAt r.ai).q t = !r.b) →
      r.gr.S p + r.ack.hi p c r.ack.gp ≤ s → a + r.gr.hi p c r.gr.j + r.ack.hi p c r.ack.gp ≤ s →
      e' ≤ e + r.gr.lo p c r.gr.j + r.ack.lo p c r.ack.gp → r.ack.S p ≤ s → 1 ≤ r.ack.lo p c r.ack.fb →
      (∀ t, s ≤ t + r.ack.hi p c r.ack.fb → t < s → x r.ack.q t = false) →
      ∀ t, s ≤ t → t ≤ e' → x r.ack.q t = false := by
  have hall : ∀ r ∈ arows, arowOK r = true := by
    have := arows_ok; simp only [List.all_eq_true] at this; exact this
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb
    (arows.flatMap fun r => [(r.gr.q, r.gr.pins), (r.ack.q, r.ack.pins)]) (by
      simp only [List.all_eq_true, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      rintro e ⟨r, hr, he⟩
      have h := hall r hr
      simp only [arowOK, sideOK, asideOK, Bool.and_eq_true] at h
      rcases he with rfl | rfl
      · exact h.1.2.1.1.1.2
      · exact h.2.1.1.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr a e s e' hq h1 h2 h3 hS hlo hpre => ?_⟩
  have h := hall r hr
  simp only [arowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hg⟩, ha⟩ := h
  obtain ⟨j1, q1, f1, hh1, o1⟩ := side_facts hb hg
  simp only [asideOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ha
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hgp⟩, hfbk⟩, hf⟩, -⟩, hgn⟩, hfbn⟩, hout⟩, hh⟩ := ha
  have gg : CGateOK p c r.gr.g r.gr.src r.gr.arcs (r.gr.S p) x := hcol (r.gr.q, r.gr.pins) (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
  have ga : CGateOK p c r.ack.g r.ack.src r.ack.arcs (r.ack.S p) x := hcol (r.ack.q, r.ack.pins) (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
  have glow := grant_low gg (cbands_of_sums r.gr.arcs) j1 q1 r.b (fl r.gr.held) (fl r.gr.ov) f1 hh1 hq
  rw [o1] at glow
  have hout' : r.ack.g.out = r.ack.q := hout
  have hfb' : r.ack.src r.ack.fb = r.ack.g.out := by rw [asrc_eq r.ack (by omega), hfbn, hout']
  have hhA : ∀ i, i < r.ack.g.k → fl r.ack.held i = true → ∀ t, x (r.ack.src i) t = fl r.ack.ov i := by
    intro i hi hheld t
    have h := hh i hi
    simp only [hheld, Bool.not_true, Bool.false_or, constAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := h
    rw [asrc_eq r.ack (by omega), const_hold hb hs1 hs2 hs3 hs4 t, hs5]
  have key := ack_low ga (cbands_of_sums r.ack.arcs) hgp hfbk hfb' hlo (fl r.ack.held) (fl r.ack.ov)
    (hf_of_afact hf hgp hfbk) hhA (s := s) (e := e') hS (by rw [hout']; exact hpre)
    (fun t ht1 ht2 => by
      rw [asrc_eq r.ack (by omega), hgn]
      refine glow t ?_ ?_ ?_ <;> simp only [GSide.hi, GSide.lo, ASide.hi, ASide.lo, GSide.S] at h1 h2 h3 ht1 ht2 ⊢ <;> omega)
  rw [hout'] at key
  exact key

end Formal.Cells.ArbAckPS
