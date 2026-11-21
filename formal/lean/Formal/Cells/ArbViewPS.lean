import Formal.Cells.CElemView
import Formal.Cells.ArbCleanChain

/-!
# Formal.Cells.ArbViewPS — THE target's nine arbiter state LUTs decide a separated arbitration cleanly, in every behaviour

Shard B, THE goal, S3/H_ARB.

## Problem, plainly
`ArbCleanChain.cq_clean_set_gen`: an arbiter state LUT whose set condition (r1 high, r2 low, reset low, A0 low) is
seen by its reads for at least its routed feedback's longest delay, and whose r1 stays high (reset low) afterwards,
goes to 1 and stays there, without H_ARB. For THE target's nine arbiters, does that hold in every behaviour of THE
circuit, with the collapsed relation coming from `Behaves` and the tied pin (VCC) derived?

## Result
`arows` (9 rows: gate, ArbClean roles, every pin's copy chain and source; GENERATED from ArbCleanPS.targetQPS and
the netlist) passes `arowOK` (setFact, confFact, viewOK, feedback source = own output, tied pins = constant gates of
the stated value). `target_arb_clean_set`: in every behaviour of THE circuit, at its corner, for every listed arbiter
and every window: if r1 is read high on [s, e'], r2 low on [s, e], reset low on [s, e'], A0 low on [s, e], with
s + hi fb ≤ e + 1 (summed window ends), then q = 1 on [s, e']. (By symmetry of the cell the reset direction is the
same argument with r1, r2 exchanged; not stated here.)

## Not covered
That every arbitration of the target is separated that much (simulation: >= 49.9 ns, JOURNAL-B 11-02); close
arbitrations (H_ARB(T) and the server-path obligation, ArbTSpec.spec_one_ack); the grants and ack C-elements.
-/

namespace Formal.Cells.ArbViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecFbChain
  Formal.Cells.ArbClean Formal.Cells.ArbCleanChain

structure ARow where
  q : Nat
  R : Roles
  pins : Pins

def ARow.g (r : ARow) : Gate := gateAt r.q
def ARow.src (r : ARow) (i : Nat) : Nat := ((pcsOf r.pins).getD i ⟨0, []⟩).src
def ARow.arcs (r : ARow) : Nat → List Arc := pinArcs r.g (pcsOf r.pins)
def ARow.S (p : DelayPar) (r : ARow) : Nat := cStart p r.g (pcsOf r.pins)
def ARow.lo (p : DelayPar) (c : ℚ) (r : ARow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.lo p.g p.κ c)).sum.toNat
def ARow.hi (p : DelayPar) (c : ℚ) (r : ARow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.hi p.g p.κ c)).sum.toNat

def constAt (s : Nat) (b : Bool) : Bool :=
  decide (s < 186873) && keepPS (gateAt s) && (gateAt s).k == 0 && (gateAt s).out == s && (gateAt s).init.testBit 0 == b

def arowOK (r : ARow) : Bool :=
  r.g.k == r.pins.length && decide (r.R.r1 < r.g.k) && decide (r.R.r2 < r.g.k) && decide (r.R.fb < r.g.k) &&
  decide (r.R.rst < r.g.k) && decide (r.R.a0 < r.g.k) &&
  r.R.r1 != r.R.fb && r.R.r2 != r.R.fb && r.R.rst != r.R.fb && r.R.a0 != r.R.fb &&
  (r.R.tied.all fun jb => decide (jb.1 < r.g.k) && jb.1 != r.R.fb && constAt (r.pins.getD jb.1 ([], 0)).2 jb.2) &&
  setFact r.g.k r.g.init r.R && confFact r.g.k r.g.init r.R &&
  viewOK r.q r.pins && (r.pins.getD r.R.fb ([], 0)).2 == r.q && (gateAt r.q).out == r.q

theorem src_eq (r : ARow) {i : Nat} (hi : i < r.pins.length) : r.src i = (r.pins.getD i ([], 0)).2 := by
  simp only [ARow.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

/-- **Separated arbitrations are decided cleanly, for every listed arbiter, in every behaviour of THE circuit.** -/
theorem target_arb_clean_set (L : List ARow) (hL : L.all arowOK = true) {p : DelayPar} (hp : Sane p) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, ∀ s e e' : Nat, r.S p ≤ s → s + r.hi p c r.R.fb ≤ e + 1 → e ≤ e' →
      1 ≤ r.lo p c r.R.fb →
      OnReads x (r.lo p c) (r.hi p c) r.R.r1 (r.src r.R.r1) true s e' →
      OnReads x (r.lo p c) (r.hi p c) r.R.r2 (r.src r.R.r2) false s e →
      OnReads x (r.lo p c) (r.hi p c) r.R.rst (r.src r.R.rst) false s e' →
      OnReads x (r.lo p c) (r.hi p c) r.R.a0 (r.src r.R.a0) false s e →
      ∀ t, s ≤ t → t ≤ e' → x r.q t = true := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb (L.map fun r => (r.q, r.pins)) (by
    simp only [List.all_map, List.all_eq_true] at hL ⊢
    intro r hr
    have := hL r hr
    simp only [arowOK, Bool.and_eq_true] at this
    exact this.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr s e e' hs hlong hee hlo h1 h2 h3 h4 => ?_⟩
  have hok : arowOK r = true := by simp only [List.all_eq_true] at hL; exact hL r hr
  simp only [arowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, n1⟩, n2⟩, n3⟩, n4⟩, ht⟩, hsf⟩, hcf⟩, -⟩, hfb⟩, hout⟩ := hok
  have hg : CGateOK p c r.g r.src r.arcs (r.S p) x := hcol _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.R.fb = r.g.out := by rw [src_eq r (by omega), hfb, hout']
  have htk : ∀ jb ∈ r.R.tied, jb.1 < r.g.k ∧ jb.1 ≠ r.R.fb := fun jb hj => ⟨(ht jb hj).1.1, (ht jb hj).1.2⟩
  have key := cq_clean_set_gen hg r.R ⟨k1, k2, k3, k4, k5⟩ ⟨n1, n2, n3, n4⟩ htk
    (hset_of_fact hsf ⟨k1, k2, k4, k5⟩ (fun jb hj => (htk jb hj).1))
    (hconf_of_fact hcf ⟨k1, k3, k4⟩ (fun jb hj => (htk jb hj).1)) hfb' (cbands_of_sums r.arcs) hlo hs hlong hee
    (fun jb hj t u _ _ _ _ => by
      have h := (ht jb hj).2
      simp only [constAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := h
      rw [src_eq r (by have := (htk jb hj).1; omega), const_hold hb hs1 hs2 hs3 hs4 u, hs5])
    h1 h2 h3 h4
  rw [hout'] at key
  exact key

set_option maxRecDepth 100000 in
/-- THE target's nine arbiter state LUTs (GENERATED from ArbCleanPS.targetQPS's names, roles, and the netlist's chains). -/
def arows : List ARow := [
  ⟨144471, ⟨2, 1, 0, 4, 3, [(5, true)]⟩, [([144450, 144449, 144423, 144422, 144426], 144471), ([144452, 144451, 144428, 144427, 144431], 144547), ([144457, 144456, 144455, 144454, 144453, 144458], 151633), ([144464, 144463, 144462, 144461, 144460, 144459, 144465], 144585), ([144468, 144467, 144466, 87314, 87313, 87312, 9573, 5001, 2383, 1181, 1180, 1179, 1185], 186905), ([144470, 144469], 144444)]⟩,
  ⟨146200, ⟨1, 2, 4, 0, 3, [(5, true)]⟩, [([146172, 146171, 143796, 134492, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([146181, 146180, 146179, 146178, 146177, 146176, 146175, 146174, 146173, 146182], 81162), ([146189, 146188, 146187, 146186, 146185, 146184, 146183, 146190], 143891), ([146193, 146192, 146191, 143841, 143840, 143813, 143812, 143811, 143810, 143809, 143808, 143807, 92401, 92404], 92411), ([146196, 146195, 146194, 146197], 146200), ([146199, 146198], 143777)]⟩,
  ⟨37766, ⟨3, 1, 0, 4, 2, [(5, true)]⟩, [([37749, 37748, 37720, 37719, 37723], 37766), ([37751, 37750, 37737, 37736, 37740], 33548), ([37757, 37756, 37755, 37754, 37753, 37752, 37758], 38015), ([37760, 37759, 37728, 37727, 37726, 37725, 37724, 37731], 154001), ([37763, 37762, 37761, 28769, 28768, 28767, 28766, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([37765, 37764], 37743)]⟩,
  ⟨37978, ⟨3, 1, 4, 2, 0, [(5, true)]⟩, [([37944, 37943, 37942, 37945], 38036), ([37956, 37955, 37954, 37953, 37952, 37951, 37950, 37949, 37948, 37947, 37946, 37957], 146120), ([37962, 37961, 37960, 37959, 37958, 28881, 8035, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([37969, 37968, 37967, 37966, 37965, 37964, 37963, 37970], 37767), ([37973, 37972, 37971, 37974], 37978), ([37976, 37975], 37977)]⟩,
  ⟨37325, ⟨0, 2, 4, 3, 1, [(5, true)]⟩, [([37308, 37307, 37285, 37284, 37288], 28334), ([37312, 37311, 37310, 37309, 37313], 33173), ([37315, 37314, 37270, 28269, 28272], 28275), ([37320, 37319, 37318, 37317, 37316, 28211, 17746, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([37322, 37321, 37277, 37281], 37325), ([37324, 37323], 37265)]⟩,
  ⟨28304, ⟨0, 2, 4, 1, 3, [(5, true)]⟩, [([28279, 28278, 28277, 28280], 28335), ([28286, 28285, 28284, 28283, 28282, 28281, 24166, 14071, 8036, 8035, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([28290, 28289, 28288, 28287, 28291], 33245), ([28295, 28294, 28293, 28292, 28296], 43085), ([28299, 28298, 28297, 28300], 28304), ([28302, 28301], 28303)]⟩,
  ⟨28366, ⟨3, 0, 2, 1, 4, [(5, true)]⟩, [([28340, 28339, 28338, 28337, 28336, 28341], 37517), ([28343, 28342, 17746, 17745, 17744, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([28349, 28348, 28347, 28346, 28345, 28344, 28350], 28366), ([28355, 28354, 28353, 28352, 28351, 10291, 10290, 10289, 10301], 130408), ([28361, 28360, 28359, 28358, 28357, 28356, 28362], 43152), ([28364, 28363], 28365)]⟩,
  ⟨47283, ⟨3, 0, 4, 1, 2, [(5, true)]⟩, [([47257, 47256, 47255, 47254, 47253, 47252, 47251, 47250, 47249, 47258], 53361), ([47262, 47261, 47260, 47259, 37770, 28766, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([47270, 47269, 47268, 47267, 47266, 47265, 47264, 47263, 47271], 53219), ([47274, 47273, 47272, 47275], 47304), ([47278, 47277, 47276, 47279], 47283), ([47281, 47280], 47282)]⟩,
  ⟨146154, ⟨4, 2, 0, 3, 1, [(5, true)]⟩, [([146141, 146140, 143640, 143639, 143638, 143643], 146154), ([146143, 146142, 143696, 143695, 143676, 143675, 143674, 143673, 143680], 146367), ([146145, 146144, 143630, 143629, 143628, 143627, 143633], 143892), ([146148, 146147, 146146, 134035, 134034, 120291, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([146151, 146150, 146149, 143655, 143654, 143653, 143652, 143651, 143650, 143649, 143648, 143647, 143658], 81163), ([146153, 146152], 143646)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem arows_ok : arows.all arowOK = true := by decide +kernel

theorem target_ps_arb_clean_set : type_of% (@target_arb_clean_set arows arows_ok) :=
  @target_arb_clean_set arows arows_ok

end Formal.Cells.ArbViewPS
