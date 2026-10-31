import Formal.Timing.Unroll
import Formal.Timing.SharedPrefix
import Tcheck.Sound

/-!
# Late sides on the cyclic routed graph, by checked potential (probe C-10h)

10g emitted the late (request) side of rules F, R and H as ONE path chosen by a
Python Dijkstra (H_EXTRACT_MIN). Here the late side is the whole routed graph
(one `GArc` list per corner variant, emitted once per file), seen through a
small per-obligation **phase rule** (`Late`), and its earliest change is bounded
by a potential that tcheck **checks** (`Formal.Timing.potOK_sound`). Python
still proposes the potential (its Dijkstra distances), but any proposal that
passes the check is sound, so the extractor's choice is no longer trusted.

The phase rule is the modelling content (it says which arcs can carry the
response); it is stated here, in Lean, instead of inside the Python search:

* node `(p, ph)` = routed pin `p` in phase `ph ∈ {0, 1}`; `(s, 0)` is the launch
  (node 0 of the netlist), every other `(p, ph)` is `2 (p + 1) + ph`;
* `noFr0`: phase 0 drops FASTRISE-side arcs (a falling wave does not travel
  through a rise-only tap, tighten's polarity rule), except out of a storage node
  that switches the phase (`swStor`: it fires, so any polarity leaves it);
* `stop0`: phase 0 does not leave a storage node other than the launch (tighten's
  segment walk);
* `swStor`: leaving a storage node other than the launch enters phase 1
  (rule H: past the first state node any polarity);
* `sw`: pins with a `[0,0]` switch `(p,0) → (p,1)` (rule F: the line's tail);
* `blocked`: pins whose arcs are dropped in both phases (rule H: ctl's own,
  closed, latch bits);
* `two = false`: no phase 1 at all (rule R: the raw graph).
-/

namespace Tcheck
open Formal.Timing Formal.Net

/-- One routed arc of one corner variant, with its FASTRISE-side flag. -/
structure GArc where
  src : Nat
  dst : Nat
  lo : Nat
  hi : Nat
  fr : Bool

/-- The per-obligation phase rule (see the module doc). -/
structure Late where
  s : Nat
  two : Bool := false
  noFr0 : Bool := false
  stop0 : Bool := false
  swStor : Bool := false
  sw : List Nat := []
  blocked : List Nat := []
  targets : List (Nat × Nat) := []
  /-- C-10k: routed arcs `(src, dst)` dropped in both phases (rule Z: the
  fast-fall side taps of the cell's own delay line, inert on a rise under
  H_FF_DRAINED, which rule Fd checks). -/
  cut : List (Nat × Nat) := []
  /-- C-10l: pins whose arcs are dropped in phase 0 only (rules Xm, K: the launch
  controller's own latch bits, closed by the launch edge with D = Q, H_OWN_LATCH_CLOSED;
  they reopen only after the controller's next edge, i.e. in phase 1). -/
  blocked0 : List Nat := []

def enc (L : Late) (p ph : Nat) : Nat := if p = L.s ∧ ph = 0 then 0 else 2 * (p + 1) + ph

/-- The product arcs one routed arc contributes. -/
def expand (L : Late) (stor : Nat → Bool) (g : GArc) : List Arc :=
  if L.blocked.contains g.src || L.cut.contains (g.src, g.dst) then [] else
  let st := stor g.src && g.src != L.s
  let a0 : List Arc :=
    if (L.noFr0 && g.fr && !(L.swStor && st)) || (L.stop0 && st) || L.blocked0.contains g.src then []
    else [⟨enc L g.src 0, enc L g.dst (if L.swStor && st then 1 else 0), g.lo, g.hi⟩]
  let a1 : List Arc := if L.two then [⟨enc L g.src 1, enc L g.dst 1, g.lo, g.hi⟩] else []
  a0 ++ a1

def switches (L : Late) : List Arc := L.sw.map fun p => ⟨enc L p 0, enc L p 1, 0, 0⟩

/-- The late-side netlist (cyclic in general): the hypothesis of a cert verdict is
that the circuit's response to the launch is a 10a `Run` of this netlist. -/
def lateNet (L : Late) (stor : Nat → Bool) (G : List GArc) : Netlist :=
  ⟨switches L ++ G.flatMap (expand L stor)⟩

/-- The same check as `potOK (lateNet ..).arcs`, without building the list. -/
def lateOK (L : Late) (stor : Nat → Bool) (G : List GArc) (pot : Nat → Nat) : Bool :=
  (switches L).all (potArcOK pot) && G.all fun g => (expand L stor g).all (potArcOK pot)

theorem lateOK_eq (L : Late) (stor : Nat → Bool) (G : List GArc) (pot : Nat → Nat) :
    lateOK L stor G pot = potOK (lateNet L stor G).arcs pot := by
  simp [lateOK, potOK, lateNet, List.all_append, List.all_flatMap]

/-- One cert obligation: a data DAG (10a/10d, must be early) and a late side on the
cyclic graph (must be late), both launched by the same event at time 0. -/
structure CInst where
  dag : Netlist
  data : List Nat
  setup : Nat
  late : Late
  pot : Array Nat
  cap : Nat

def CInst.potf (i : CInst) (x : Nat) : Nat := i.pot.getD x i.cap

/-- What tcheck prints as PASS for a cert obligation. -/
def cverdict (stor : Nat → Bool) (G : List GArc) (i : CInst) : Bool :=
  decide i.dag.WF && lateOK i.late stor G i.potf &&
  i.late.targets.all (fun q => enc i.late q.1 q.2 != 0) &&
  i.data.all fun d => match winArr i.dag d with
    | none => true
    | some (_, l) => i.late.targets.all fun q => decide (l + i.setup ≤ i.potf (enc i.late q.1 q.2))

/-- The late bound tcheck prints: the least potential over the targets. -/
def cbound (i : CInst) : Option Nat :=
  i.late.targets.foldl (fun acc q => let b := i.potf (enc i.late q.1 q.2)
    match acc with | none => some b | some a => some (min a b)) none

/-- **Soundness of a cert PASS.** If the data side is a `Run` of the emitted DAG and
the response is a `Run` of the late-side netlist (same launch at time 0), every
data change precedes every change of every target by at least `setup`. -/
theorem cverdict_sound {stor : Nat → Bool} {G : List GArc} {i : CInst}
    (h : cverdict stor G i = true) {sigD sigL : Nat → Trace}
    (rD : Run i.dag sigD) (rL : Run (lateNet i.late stor G) sigL) :
    ∀ d ∈ i.data, ∀ q ∈ i.late.targets, ∀ s t, changes (sigD d) s →
      changes (sigL (enc i.late q.1 q.2)) t → s + i.setup ≤ t := by
  intro d hd q hq s t hs ht
  simp only [cverdict, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hwf, hlate⟩, hnz⟩, hdata⟩ := h
  rw [lateOK_eq] at hlate
  have hq0 : enc i.late q.1 q.2 ≠ 0 := by
    have := hnz q hq; simpa using this
  have hb := potOK_sound hlate rL t _ hq0 ht
  obtain ⟨e, l, hw, _, hsl⟩ := changes_in_winArr hwf rD d s hs
  have := hdata d hd
  rw [hw] at this
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  have := this q hq
  omega

/-! ## C-10k: per-pair verdicts

A cert obligation with several data nodes and several targets is a cross
product in `cverdict` (every data node before every target). Rules Fd and Z
need it per PAIR: stage `i`'s fall at stage `i+1`'s chain pin against stage
`i+1`'s own side tap (Fd); a consumer link's latch data against that link's own
latch enables (Z). `pairs` lists `(data node, target pin, target phase)`. -/

def pverdict (stor : Nat → Bool) (G : List GArc) (i : CInst) (pairs : List (Nat × Nat × Nat)) :
    Bool :=
  decide i.dag.WF && lateOK i.late stor G i.potf &&
  pairs.all fun (d, x, ph) => enc i.late x ph != 0 &&
    match winArr i.dag d with
    | none => true
    | some (_, l) => decide (l + i.setup ≤ i.potf (enc i.late x ph))

/-- **Soundness of a per-pair cert PASS**: under the same two `Run` hypotheses as
`cverdict_sound`, every change of each pair's data node precedes every change of
that pair's target by at least `setup`. -/
theorem pverdict_sound {stor : Nat → Bool} {G : List GArc} {i : CInst}
    {pairs : List (Nat × Nat × Nat)}
    (h : pverdict stor G i pairs = true) {sigD sigL : Nat → Trace}
    (rD : Run i.dag sigD) (rL : Run (lateNet i.late stor G) sigL) :
    ∀ d x ph, (d, x, ph) ∈ pairs → ∀ s t, changes (sigD d) s →
      changes (sigL (enc i.late x ph)) t → s + i.setup ≤ t := by
  intro d x ph hp s t hs ht
  simp only [pverdict, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hwf, hlate⟩, hpairs⟩ := h
  rw [lateOK_eq] at hlate
  have hq := hpairs (d, x, ph) hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hq
  obtain ⟨hnz, hd⟩ := hq
  have hb := potOK_sound hlate rL t _ hnz ht
  obtain ⟨e, l, hw, _, hsl⟩ := changes_in_winArr hwf rD d s hs
  rw [hw] at hd
  simp only [decide_eq_true_eq] at hd
  omega

/-! ## C-10l: shared-prefix credit and C-element max nodes (`xverdict`)

One credited obligation (`XInst`): the late side is the same `lateNet` as
before, read through TWO checked potentials (`Formal.Timing.SharedPrefix`):
`potB` with the credited node `e` (= `enc late X 0`) blocked, `potA` launched
at `e`. The data side is split the same way: `dagD` from the launch `D` (the
whole data DAG), `dagA` from `X` (its suffix). `maxg` lists the max nodes
(encoded late node, encoded source nodes of its group): a C-element whose
listed pins all agree with its output at the origin (`MaxNode.cel_needs_pin`).
`pairs` are `(data node in dagD, data node in dagA, target pin, phase)`. -/

def condBb (e : Nat) (potB : Nat → Nat) (v : Nat) (a : Arc) : Bool :=
  a.src == e || decide (potB v ≤ rho potB a.src + a.lo)

def condAb (e : Nat) (potA : Nat → Nat) (v : Nat) (a : Arc) : Bool :=
  a.src == 0 || decide (potA v ≤ (if a.src = e then 0 else potA a.src) + a.lo)

def isMaxB (maxg : List (Nat × List Nat)) (v : Nat) : Bool := maxg.any (·.1 == v)

def srcsOf (maxg : List (Nat × List Nat)) (v : Nat) : List Nat :=
  ((maxg.find? (·.1 == v)).map (·.2)).getD []

def arcOK2 (maxg : List (Nat × List Nat)) (e : Nat) (potB potA : Nat → Nat) (a : Arc) : Bool :=
  a.dst == 0 || isMaxB maxg a.dst ||
    ((a.lo != 0 || decide (a.src < a.dst)) && condBb e potB a.dst a && condAb e potA a.dst a)

def maxArcOK (maxg : List (Nat × List Nat)) (e : Nat) (potB potA : Nat → Nat) (v : Nat)
    (a : Arc) : Bool :=
  a.dst == v && (srcsOf maxg v).contains a.src && (a.lo != 0 || decide (a.src < v)) &&
    condBb e potB v a && condAb e potA v a

/-- The group of a max node: the indices of its in-arcs from its listed sources. -/
def xM (net : Netlist) (maxg : List (Nat × List Nat)) (v : Nat) : List Nat :=
  if isMaxB maxg v then
    (List.range net.arcs.length).filter fun k => match net.arcs[k]? with
      | some a => a.dst == v && (srcsOf maxg v).contains a.src
      | none => false
  else []

/-- The executable two-potential check (arcs through `expand`, as `lateOK`). -/
def pot2OKb (L : Late) (stor : Nat → Bool) (G : List GArc) (maxg : List (Nat × List Nat))
    (e : Nat) (potB potA : Nat → Nat) : Bool :=
  ((switches L).all (arcOK2 maxg e potB potA) &&
    G.all fun g => (expand L stor g).all (arcOK2 maxg e potB potA)) &&
  maxg.all fun m => m.1 != 0 && (lateNet L stor G).arcs.any (maxArcOK maxg e potB potA m.1)

theorem pot2OKb_sound {L : Late} {stor : Nat → Bool} {G : List GArc}
    {maxg : List (Nat × List Nat)} {e : Nat} {potB potA : Nat → Nat}
    (h : pot2OKb L stor G maxg e potB potA = true) :
    SharedPrefix.Pot2OK (lateNet L stor G) (xM (lateNet L stor G) maxg) e potB potA := by
  simp only [pot2OKb, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsw, hG⟩, hmx⟩ := h
  have harcs : ∀ a ∈ (lateNet L stor G).arcs, arcOK2 maxg e potB potA a = true := by
    intro a ha
    simp only [lateNet, List.mem_append, List.mem_flatMap] at ha
    rcases ha with ha | ⟨g, hg, ha⟩
    · exact hsw a ha
    · exact hG g hg a ha
  -- every listed max node has a group arc, so its group is non-empty
  have hmx' : ∀ v, isMaxB maxg v = true → v ≠ 0 ∧
      ∃ a ∈ (lateNet L stor G).arcs, maxArcOK maxg e potB potA v a = true := by
    intro v hv
    simp only [isMaxB, List.any_eq_true, beq_iff_eq] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    have := hmx m hm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true] at this
    exact this
  have grp : ∀ v, isMaxB maxg v = true → ∃ k ∈ xM (lateNet L stor G) maxg v, ∃ a,
      (lateNet L stor G).arcs[k]? = some a ∧ maxArcOK maxg e potB potA v a = true := by
    intro v hv
    obtain ⟨_, a, ha, hok⟩ := hmx' v hv
    obtain ⟨k, hk, hka⟩ := List.getElem_of_mem ha
    refine ⟨k, ?_, a, by rw [List.getElem?_eq_getElem hk, hka], hok⟩
    simp only [xM, hv, ite_true, List.mem_filter, List.mem_range, List.getElem?_eq_getElem hk, hka]
    simp only [maxArcOK, Bool.and_eq_true] at hok
    have h2 := hok.1.1.1.2
    simp only [List.contains_iff_mem] at h2
    exact ⟨hk, by simp [hok.1.1.1.1, h2]⟩
  refine ⟨?_, ?_⟩
  · intro a ha
    have := harcs a ha
    simp only [arcOK2, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at this
    rcases this with (h0 | hm) | ⟨⟨hz, hB⟩, hA⟩
    · exact Or.inl h0
    · right; left
      obtain ⟨k, hk, _⟩ := grp a.dst hm
      intro hnil; rw [hnil] at hk; simp at hk
    · right; right
      refine ⟨fun hl => ?_, ?_, ?_⟩
      · rcases hz with hz | hz
        · exact absurd hl hz
        · exact hz
      · simp only [condBb, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
        exact hB
      · simp only [condAb, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hA
        exact hA
  · intro v hv hne
    have hmax : isMaxB maxg v = true := by
      apply Classical.byContradiction; intro hn
      apply hne; simp [xM, hn]
    obtain ⟨k, hk, a, hka, hok⟩ := grp v hmax
    simp only [maxArcOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
      Bool.or_eq_true, condBb, condAb] at hok
    obtain ⟨⟨⟨⟨_, _⟩, hz⟩, hB⟩, hA⟩ := hok
    refine ⟨k, hk, a, hka, fun hl => ?_, hB, hA⟩
    rcases hz with hz | hz
    · exact absurd hl hz
    · exact hz

structure XInst where
  dagD : Netlist
  dagA : Netlist
  setup : Nat
  late : Late
  e : Nat
  potB : Array Nat
  capB : Nat
  potA : Array Nat
  capA : Nat
  maxg : List (Nat × List Nat)
  pairs : List (Nat × Nat × Nat × Nat)

def XInst.potBf (i : XInst) (x : Nat) : Nat := i.potB.getD x i.capB
def XInst.potAf (i : XInst) (x : Nat) : Nat := i.potA.getD x i.capA

/-- What tcheck prints as PASS for a credited obligation. -/
def xverdict (stor : Nat → Bool) (G : List GArc) (i : XInst) : Bool :=
  decide i.dagD.WF && decide i.dagA.WF && i.e != 0 &&
  pot2OKb i.late stor G i.maxg i.e i.potBf i.potAf &&
  i.pairs.all fun (dD, dA, x, ph) => enc i.late x ph != 0 &&
    (match winArr i.dagD dD with
      | none => true
      | some (_, l) => decide (l + i.setup ≤ i.potBf (enc i.late x ph))) &&
    (match winArr i.dagA dA with
      | none => true
      | some (_, l) => decide (l + i.setup ≤ i.potAf (enc i.late x ph)))

/-- **Soundness of a credited PASS.** Hypotheses, besides the three `Run`s
(data from `D`, data from `X`, late side):
* H_CLEAN_EDGE(X) (`hcl`): the credited late node changes only at `τ`;
* H_ONE_SAMPLE_PER_WIRE (`hshift`): the data the pairs name is driven through
  `X`'s one edge, so each change of a data node is `τ` plus a change of its
  copy in the `X`-launched run;
* H_ALL at the max nodes (`MaxNode.cel_needs_pin`).
Conclusion: each pair's data change precedes each change of its target. -/
theorem xverdict_sound {stor : Nat → Bool} {G : List GArc} {i : XInst}
    (h : xverdict stor G i = true) {sigD sigA sigL : Nat → Trace}
    (rD : Run i.dagD sigD) (rA : Run i.dagA sigA) (rL : Run (lateNet i.late stor G) sigL)
    (hall : ∀ v, v ≠ 0 → xM (lateNet i.late stor G) i.maxg v ≠ [] →
      MaxNode.AllBefore rL v (xM (lateNet i.late stor G) i.maxg v))
    {τ : Nat} (hcl : ∀ t, changes (sigL i.e) t → t = τ)
    (hshift : ∀ dD dA x ph, (dD, dA, x, ph) ∈ i.pairs → ∀ s, changes (sigD dD) s →
      ∃ s', changes (sigA dA) s' ∧ s = τ + s') :
    ∀ dD dA x ph, (dD, dA, x, ph) ∈ i.pairs → ∀ s t, changes (sigD dD) s →
      changes (sigL (enc i.late x ph)) t → s + i.setup ≤ t := by
  intro dD dA x ph hp s t hs ht
  simp only [xverdict, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨hwD, hwA⟩, he⟩, hpot⟩, hpairs⟩ := h
  have hq := hpairs (dD, dA, x, ph) hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hq
  obtain ⟨⟨hnz, hdD⟩, hdA⟩ := hq
  have hb := SharedPrefix.pot2_sound (pot2OKb_sound hpot) he rL hall hcl t _ hnz ht
  obtain ⟨_, lD, hwinD, _, hsD⟩ := changes_in_winArr hwD rD dD s hs
  obtain ⟨s', hs', rfl⟩ := hshift dD dA x ph hp s hs
  obtain ⟨_, lA, hwinA, _, hsA⟩ := changes_in_winArr hwA rA dA s' hs'
  rw [hwinD] at hdD; rw [hwinA] at hdA
  simp only [decide_eq_true_eq] at hdD hdA
  omega

end Tcheck
