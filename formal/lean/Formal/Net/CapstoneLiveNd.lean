import Formal.Net.CapstoneLiveNdCount
import Formal.Net.CapstoneLiveNdStart
import Formal.Net.CapstoneLiveSpine

/-!
# Probe C-8z (3): gcd_hw liveness, repaired statement; H_FIRING_BOUND reduced to offer counts

8u's `gcd_hw_live` has two defects in its open obligations, both repaired here:

1. **`start`'s source.** H_BOUNDED_DELAY on `start`'s `bd_src` LUT together with H_START_ONCE
   forces the start token never to be released (`CapstoneLiveNdStart.start_never_closes`).
   Here the `start` LUT gets a settle bound only before its first offer (**H_START_ENV**: the
   environment offers `start` within `H` of reset-enabled), and the quiescence predicate drops
   the `start` LUT once it has offered (`QuietS`). All other gates, including the free-running
   `a`/`b` sources, keep H_BOUNDED_DELAY.
2. **What a "state change" is.** 8u's H_FIRING_BOUND counts changes of the whole global state
   `gsAt`, which includes internal traces that no gate model constrains (`itr p k` for indices
   the operator does not use) and buses of idle channels. Junk there can change at every tick
   while every other hypothesis holds, so no bound `N` independent of the delays can hold
   in general. Here the state is the projection `pj`: every request and acknowledge, the
   USED internal nodes (`nI` per operator: mux 2, muxn 3, amerge 2, link 1), and each bus
   only while its request is high (`if rq then dt else 0`), plus the flag "start was offered".
   Every excitation reads only this projection (`gate_pj`), so a frozen projection is still
   quiescent (`frozen_quietS`).

## The reduction of the firing bound (`firing_bound`)

Every projected change flips one of `nBits = 1168` bits (2 per channel + 238 internal nodes,
`nBits_eq`). Every bit's rises are bounded by the request rises (offers) of one channel:
the acknowledge by its own request (protocol), each internal node by the request it follows
(`follow_rises`: mux joins by `x`/`y`, 3-way joins by `x_k`, arbiter grants by their
requests, the link C-element by its input request). So **H_OFFER_BOUND `M`** (every channel
offers at most `M` tokens before the first `out0` close) gives
`#changes ≤ 1168 * (2M + 1)`.

For the 67 spine channels `M ≤ L` is 8u's `gcd_hw_spine_offers_bounded` (under H_WALK_ENDS
`L`). What remains is **H_OFFER_BOUND_NS `M`**, the same bound for the 398 non-spine
channels. It is open (see the note C-8z-nodeadlock.md).

## The theorem (`gcd_hw_live_nd`)

Hypotheses: H_CELLS, H_BUNDLE, H_START_ONCE, H_WALK (8r), H_WALK_ENDS `L` (8u),
H_BOUNDED_DELAY' `H` (every gate except `start`'s LUT), H_START_ENV `H`,
H_ARB_UNCONTESTED_BOUNDED `H` (8u), **H_NO_DEADLOCK'** (open) and **H_OFFER_BOUND_NS `M`**
(open). Conclusion: the first `out0` token closes at some `e < (N + 1) * (H + 1)` with
`N = 1168 * (2 * max L M + 1)`, and carries `Nat.gcd a b`.

H_NO_DEADLOCK' reads: before the first `out0` close, either some gate other than `start`'s
LUT is excited, or `start` has not yet been offered and is enabled (ack low) without being
requested. It implies 8u's H_NO_DEADLOCK only for the gate part; it is the form that can be
true of a run meeting H_START_ONCE.
-/

namespace Formal.Net.CapNet.Live.Nd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live
open Formal.Net.CapSafe (Good)
open Formal.Cells.LinkHandshake (ctlB ctlB_eq)

/-- Number of internal nodes an operator's gate model uses. -/
def nI : K NC → Nat
  | .mux .. => 2
  | .muxn .. => 3
  | .amerge .. => 2
  | .link .. => 1
  | _ => 0

/-- The observable projection of the global state. -/
def pj (s : GS) : GS :=
  ⟨s.rq, s.ak, fun c => if s.rq c then s.dt c else 0,
   fun p k => if k < nI (opAt p) then s.it p k else false⟩

@[simp] theorem pj_rq (s : GS) : (pj s).rq = s.rq := rfl
@[simp] theorem pj_ak (s : GS) : (pj s).ak = s.ak := rfl

theorem mask (s : GS) (c : Fin NC) (f : Nat → Bool) :
    ((pj s).rq c && f ((pj s).dt c)) = (s.rq c && f (s.dt c)) := by
  simp only [pj]; cases s.rq c <;> simp

/-- A gate reads only the projection. -/
def PjInv (g : Gate) : Prop := ∀ s, g.out (pj s) = g.out s ∧ ∀ v, (g.exc v (pj s) ↔ g.exc v s)

theorem gw_inv (o e : GS → Bool) (ho : ∀ s, o (pj s) = o s) (he : ∀ s, e (pj s) = e s) :
    PjInv (gw o e) := fun s => ⟨ho s, fun v => by simp only [gw, he s]⟩

theorem it_pj {s : GS} {p : Fin NO} {k : Nat} (h : k < nI (opAt p)) : (pj s).it p k = s.it p k := by
  simp [pj, h]

/-- **Every gate of gcd_hw reads only the projection.** -/
theorem gate_pj (p : Fin NO) : ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p), PjInv g := by
  intro g hg
  cases hk : opAt p with
  | forkG i os =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_append, List.mem_map,
      List.mem_singleton] at hg
    rcases hg with ⟨c, -, rfl⟩ | rfl
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
    · exact fun s => ⟨rfl, fun v => Iff.rfl⟩
  | forkH i os l h d hs =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_append, List.mem_map,
      List.mem_singleton] at hg
    rcases hg with ⟨c, -, rfl⟩ | rfl
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
    · exact fun s => ⟨rfl, fun v => Iff.rfl⟩
  | join ins o e js jw =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨c, -, rfl⟩
    · exact fun s => ⟨rfl, fun v => Iff.rfl⟩
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | bjoin ins o ec ed =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨c, -, rfl⟩
    · exact fun s => ⟨rfl, fun v => Iff.rfl⟩
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | steerC j t f =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact gw_inv _ _ (fun _ => rfl) (fun s => mask s j (fun d => sel2 d == true))
    · exact gw_inv _ _ (fun _ => rfl) (fun s => mask s j (fun d => sel2 d == false))
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | steerD j t f fd sw =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact gw_inv _ _ (fun _ => rfl) (fun s => mask s j (fun d => sel2 d == true))
    · exact gw_inv _ _ (fun _ => rfl) (fun s => mask s j (fun d => sel2 d == false))
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | mux c x y z mw =>
    have h0 : ∀ s : GS, (pj s).it p 0 = s.it p 0 := fun s => it_pj (by rw [hk]; simp [nI])
    have h1 : ∀ s : GS, (pj s).it p 1 = s.it p 1 := fun s => it_pj (by rw [hk]; simp [nI])
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun s => ⟨h0 s, fun v => by simp only [mask s c (fun d => !sel2 d)]; rfl⟩
    · exact fun s => ⟨h1 s, fun v => by simp only [mask s c (fun d => sel2 d)]; rfl⟩
    · exact gw_inv _ _ (fun _ => rfl) (fun s => by simp only [h0, h1])
    · exact fun s => ⟨rfl, fun v => by simp only [h0, pj_ak]⟩
    · exact fun s => ⟨rfl, fun v => by simp only [h1, pj_ak]⟩
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | muxn c x0 x1 x2 z nw =>
    have hi : ∀ s : GS, ∀ k, k < 3 → (pj s).it p k = s.it p k :=
      fun s k h => it_pj (by rw [hk]; exact h)
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_append, List.mem_map,
      List.mem_range, List.mem_singleton] at hg
    rcases hg with ((⟨k, hk3, rfl⟩ | rfl) | ⟨k, hk3, rfl⟩) | rfl
    · exact fun s => ⟨hi s k hk3, fun v => by
        simp only [mask s c (fun d => selD d == k)]; rfl⟩
    · exact gw_inv _ _ (fun _ => rfl) (fun s => by
        simp only [hi s 0 (by decide), hi s 1 (by decide), hi s 2 (by decide)])
    · exact fun s => ⟨rfl, fun v => by simp only [hi s k hk3, pj_ak]⟩
    · exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | amerge x y z w =>
    have h0 : ∀ s : GS, (pj s).it p 0 = s.it p 0 := fun s => it_pj (by rw [hk]; simp [nI])
    have h1 : ∀ s : GS, (pj s).it p 1 = s.it p 1 := fun s => it_pj (by rw [hk]; simp [nI])
    rw [hk] at hg; simp only [gatesK, grantsK, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl | rfl) | (rfl | rfl)
    · exact fun s => ⟨rfl, fun v => by simp only [h0, h1, pj_ak]⟩
    · exact fun s => ⟨rfl, fun v => by simp only [h0, pj_ak]⟩
    · exact fun s => ⟨rfl, fun v => by simp only [h1, pj_ak]⟩
    · exact fun s => ⟨h0 s, fun v => by simp only [h1]; rfl⟩
    · exact fun s => ⟨h1 s, fun v => by simp only [h0]; rfl⟩
  | link i o =>
    have h0 : ∀ s : GS, (pj s).it p 0 = s.it p 0 := fun s => it_pj (by rw [hk]; simp [nI])
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact gw_inv _ _ h0 (fun s => by simp only [h0, pj_rq, pj_ak])
    · exact gw_inv _ _ (fun _ => rfl) h0
    · exact gw_inv _ _ (fun _ => rfl) h0
  | src z which d =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    subst hg; exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)
  | sink i =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    subst hg; exact gw_inv _ _ (fun _ => rfl) (fun _ => rfl)

/-- Quiescence of every gate except `start`'s source LUT. -/
def Quiet2 (s : GS) : Prop :=
  ∀ p : Fin NO, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p),
    ∀ v, g.exc v s → g.out s = v

/-- The state for the ranking argument: the projection plus "start was offered". -/
noncomputable def St (ch : Fin NC → Chan) (itr : Itr) (t : Nat) : GS × Bool :=
  (pj (gsAt ch itr t), decide (1 ≤ cnt (riseB (ch start).req) t))

/-- Quiescent: no gate but `start`'s LUT excited, and `start`'s LUT not excited before its
first offer. -/
def QuietS (x : GS × Bool) : Prop :=
  Quiet2 x.1 ∧ (x.2 = false → x.1.ak start = false → x.1.rq start = true)

/-- H_START_ENV: before its first offer, `start` is offered within `H` of being enabled. -/
def StartEnv (H : Nat) (c : Chan) : Prop :=
  ∀ t, Win H t (fun u => cnt (riseB c.req) u = 0 ∧ c.ack u = false) → Ev H t (fun u => c.req u = true)

theorem quiet2_pj {s : GS} (h : Quiet2 s) : Quiet2 (pj s) := by
  intro p hp g hg v he
  have := gate_pj p g hg s
  rw [this.1]; exact h p hp g hg v ((this.2 v).mp he)

/-- **Frozen ⇒ quiescent, for the repaired state.** -/
theorem frozen_quietS (H : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (hB : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (hA : ∀ p x u z w, opAt p = .amerge x u z w → ArbSettle H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (hS : StartEnv H (ch start))
    {t : Nat} (hfz : ∀ u, t ≤ u → u ≤ t + H → St ch itr u = St ch itr t) :
    QuietS (St ch itr t) := by
  have hpj : ∀ u, t ≤ u → u ≤ t + H → pj (gsAt ch itr u) = pj (gsAt ch itr t) :=
    fun u h1 h2 => congrArg Prod.fst (hfz u h1 h2)
  refine ⟨quiet2_pj ?_, ?_⟩
  · intro p hp g hg v he
    have hI := gate_pj p g hg
    have hbg : BndG H (gsAt ch itr) g := by
      rcases List.mem_append.mp hg with hg' | hg'
      · exact hB p hp g hg'
      · cases hk : opAt p with
        | amerge x u z w =>
          rw [hk] at hg'
          exact grants_bnd (hA p x u z w hk) g hg'
        | _ => rw [hk] at hg'; simp [grantsK] at hg'
    have hex : ∀ u, t ≤ u → u ≤ t + H → (g.exc v (gsAt ch itr u) ↔ g.exc v (gsAt ch itr t)) := by
      intro u h1 h2
      rw [← (hI (gsAt ch itr u)).2 v, ← (hI (gsAt ch itr t)).2 v, hpj u h1 h2]
    obtain ⟨u, h1, h2, ho⟩ := hbg v t (fun u h1 h2 => (hex u h1 h2).mpr he)
    rw [← (hI _).1, hpj u h1 h2, (hI _).1] at ho
    exact ho
  · intro hf ha
    simp only [St] at hf ha ⊢
    have h0 : cnt (riseB (ch start).req) t = 0 := by
      have := of_decide_eq_false hf; omega
    obtain ⟨u, h1, h2, hu⟩ := hS t (fun u h1 h2 => by
      have e := hfz u h1 h2
      simp only [St, Prod.mk.injEq] at e
      refine ⟨?_, ?_⟩
      · have := e.2; rw [h0] at this
        have := of_decide_eq_false this; omega
      · have := congrArg (fun s : GS => s.ak start) e.1
        simp only [pj, gsAt] at this ha; rw [this]; exact ha)
    have := congrArg (fun s : GS => s.rq start) (hpj u h1 h2)
    simp only [pj, gsAt] at this ⊢; rw [← this]; exact hu

/-- Change marker of the repaired state. -/
noncomputable def chS (ch : Fin NC → Chan) (itr : Itr) (u : Nat) : Bool :=
  @decide (St ch itr (u + 1) ≠ St ch itr u) (Classical.propDecidable _)

theorem chS_false {ch : Fin NC → Chan} {itr : Itr} {u : Nat} (h : chS ch itr u = false) :
    St ch itr (u + 1) = St ch itr u := by
  unfold chS at h
  apply Classical.byContradiction
  intro hne
  have := @decide_eq_true _ (Classical.propDecidable _) hne
  rw [this] at h; cases h

/-! ## The firing bound -/

/-- The bits of the projected state, as traces. -/
def bitsL (ch : Fin NC → Chan) (itr : Itr) : List Trace :=
  (List.finRange NC).flatMap (fun c => [(ch c).req, (ch c).ack]) ++
  (List.finRange NO).flatMap (fun p => (List.range (nI (opAt p))).map (itr p))

def nBits : Nat :=
  ((List.finRange NC).map (fun _ => 2)).sum + ((List.finRange NO).map (fun p => nI (opAt p))).sum

theorem bitsL_len (ch : Fin NC → Chan) (itr : Itr) : (bitsL ch itr).length = nBits := by
  simp [bitsL, nBits, List.length_flatMap]

theorem nBits_eq : nBits = 1168 := by decide +kernel

theorem req_mem (ch : Fin NC → Chan) (itr : Itr) (c : Fin NC) : (ch c).req ∈ bitsL ch itr :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_finRange c, by simp⟩)

theorem ack_mem (ch : Fin NC → Chan) (itr : Itr) (c : Fin NC) : (ch c).ack ∈ bitsL ch itr :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_finRange c, by simp⟩)

theorem it_mem (ch : Fin NC → Chan) (itr : Itr) (p : Fin NO) (k : Nat) (hk : k < nI (opAt p)) :
    itr p k ∈ bitsL ch itr :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, List.mem_finRange p,
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩)

/-- A change of the repaired state flips some bit. -/
theorem chS_bit (ch : Fin NC → Chan) (itr : Itr) (H_BUNDLE : ∀ c, Held (ch c)) (u : Nat)
    (h : chS ch itr u = true) : ∃ x ∈ bitsL ch itr, (x u != x (u + 1)) = true := by
  apply Classical.byContradiction
  intro hno
  have hs : ∀ x ∈ bitsL ch itr, x (u + 1) = x u := by
    intro x hx
    cases e : (x u != x (u + 1))
    · simp at e; exact e.symm
    · exact absurd ⟨x, hx, e⟩ hno
  have hr : ∀ c, (ch c).req (u + 1) = (ch c).req u := fun c => hs _ (req_mem ch itr c)
  have hak : ∀ c, (ch c).ack (u + 1) = (ch c).ack u := fun c => hs _ (ack_mem ch itr c)
  have heq : St ch itr (u + 1) = St ch itr u := by
    simp only [St, pj, gsAt, Prod.mk.injEq, GS.mk.injEq]
    refine ⟨⟨funext hr, funext hak, funext fun c => ?_, funext fun p => funext fun k => ?_⟩, ?_⟩
    · simp only [hr c]
      by_cases hq : (ch c).req u = true
      · simp only [hq]
        exact H_BUNDLE c u (by simp [inTx, hq]) (by simp [inTx, hr c, hq])
      · simp [hq]
    · by_cases hk : k < nI (opAt p)
      · simp only [hk, ite_true]; exact hs _ (it_mem ch itr p k hk)
      · simp only [hk, ite_false]
    · have : cnt (riseB (ch start).req) (u + 1) = cnt (riseB (ch start).req) u := by
        simp [cnt, riseB, hr start]
      rw [this]
  have := chS_false (ch := ch) (itr := itr) (u := u)
  unfold chS at h
  have := of_decide_eq_true (inst := Classical.propDecidable _) h
  exact this heq

/-- **H_OFFER_BOUND ⇒ firing bound.** If every channel offers at most `M` tokens before the
first `out0` close, the repaired state changes at most `1168 * (2M + 1)` times before it. -/
theorem firing_bound (a b M : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_OFFER_BOUND : ∀ c T, cnt (fallB (ch out0).ack) T = 0 → cnt (riseB (ch c).req) T ≤ M) :
    ∀ T, cnt (fallB (ch out0).ack) T = 0 → cnt (chS ch itr) T ≤ 1168 * (2 * M + 1) := by
  intro T hT
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hP := gcd_hw_protocol a b ch hC H_BUNDLE
  have hreq : ∀ c, cnt (riseB (ch c).req) T ≤ M := fun c => H_OFFER_BOUND c T hT
  -- every bit rises at most `M` times
  have hfol : ∀ (x : Trace) (c : Fin NC), (∀ t, x (t + 1) ≠ x t → (ch c).req t = x (t + 1)) →
      cnt (riseB x) T ≤ M := by
    intro x c hf
    have := follow_rises x (ch c).req hf T
    rw [show bn ((ch c).req 0) = 0 by simp [bn, (hP c).1.1]] at this
    have := hreq c; omega
  have hbit : ∀ x ∈ bitsL ch itr, cnt (riseB x) T ≤ M := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hreq c
      · refine hfol _ c (fun t ht => ?_)
        have := (hP c).2 t |>.2 ht
        cases h1 : (ch c).ack (t + 1) <;> cases h2 : (ch c).ack t <;> cases h3 : (ch c).req t <;>
          simp_all
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      have hk := List.mem_range.mp hk
      have M := H_CELLS p
      cases ho : opAt p with
      | mux c x y z mw =>
        rw [ho] at M hk; simp only [nI] at hk
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · exact hfol _ x (fun t ht => (M.cj0 t ht).1)
        · exact hfol _ y (fun t ht => (M.cj1 t ht).1)
      | muxn c x0 x1 x2 z nw =>
        rw [ho] at M hk; simp only [nI] at hk
        exact hfol _ (cx3 x0 x1 x2 k) (fun t ht => (M.cj k hk t ht).1)
      | amerge x y z w =>
        rw [ho] at M hk; simp only [nI] at hk
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · exact hfol _ x (fun t ht => (M.H_ARB1 t ht).1.symm)
        · exact hfol _ y (fun t ht => (M.H_ARB2 t ht).1.symm)
      | link i o =>
        rw [ho] at M hk; simp only [nI] at hk
        have : k = 0 := by omega
        subst this
        refine hfol _ i (fun t ht => ?_)
        have e := M.H_CEL_SI t ht
        rw [ctlB_eq] at e
        cases h1 : itr p 0 (t + 1) <;> cases h2 : itr p 0 t <;> cases h3 : (ch i).req t <;>
          cases h4 : (ch o).ack t <;> simp_all
      | _ => rw [ho] at hk; simp [nI] at hk
  have h1 := cnt_le_sum (bitsL ch itr) (fun x u => x u != x (u + 1)) (chS ch itr)
    (chS_bit ch itr H_BUNDLE) T
  have h2 := sum_le_const (bitsL ch itr) (fun x => cnt (fun u => x u != x (u + 1)) T) (2 * M + 1)
    (fun x hx => by have := trans_le' x T; have := hbit x hx; omega)
  rw [bitsL_len, nBits_eq] at h2
  omega

/-! ## The repaired liveness theorem -/

/-- **gcd_hw circuit liveness, repaired reduction.** -/
theorem gcd_hw_live_nd (a b H L M : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : CapSafe.TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (H_WALK_ENDS : (walk (σY a b y) L).cur = none)
    (H_BOUNDED_DELAY' : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (H_START_ENV : StartEnv H (ch start))
    (H_ARB_UNCONTESTED_BOUNDED : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbUnc H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (H_NO_DEADLOCK' : ∀ t, cnt (fallB (ch out0).ack) t = 0 →
      ¬ (Quiet2 (gsAt ch itr t) ∧
         (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true)))
    (H_OFFER_BOUND_NS : ∀ c, sp c = false → ∀ T, cnt (fallB (ch out0).ack) T = 0 →
      cnt (riseB (ch c).req) T ≤ M) :
    ∃ e, e < (1168 * (2 * max L M + 1) + 1) * (H + 1) ∧ TokAt (ch out0) 0 e ∧
      (ch out0).dat e = Nat.gcd a b := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hA : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbSettle H (ch x) (ch u) (ch z) (itr p 0) (itr p 1) := by
    intro p x u z w hp
    have M' := H_CELLS p
    rw [hp] at M'
    exact gcd_hw_arb_settle a b H ch hC H_BUNDLE H_START_ONCE y hy H_WALK p x u z w hp _ _ M'
      (H_ARB_UNCONTESTED_BOUNDED p x u z w hp)
  have hOff : ∀ c T, cnt (fallB (ch out0).ack) T = 0 → cnt (riseB (ch c).req) T ≤ max L M := by
    intro c T hT
    cases hs : sp c
    · have := H_OFFER_BOUND_NS c hs T hT; omega
    · have := (gcd_hw_spine_offers_bounded a b L ch hC H_BUNDLE H_START_ONCE y hy H_WALK
        H_WALK_ENDS c hs T).1
      have := (gcd_hw_spine_offers_bounded a b L ch hC H_BUNDLE H_START_ONCE y hy H_WALK
        H_WALK_ENDS c hs T).2.1
      omega
  obtain ⟨t, ht, hP⟩ := rank_live (St ch itr) QuietS (fun t => cnt (fallB (ch out0).ack) t ≠ 0)
    (chS ch itr) H (1168 * (2 * max L M + 1)) (fun _ h => chS_false h)
    (fun _ hfz => frozen_quietS H ch itr H_BOUNDED_DELAY' hA H_START_ENV hfz)
    (fun t hp hq => by
      apply H_NO_DEADLOCK' t (by omega)
      refine ⟨?_, ?_⟩
      · intro p hp' g hg v he
        have hI := gate_pj p g hg (gsAt ch itr t)
        rw [← hI.1]; exact hq.1 p hp' g hg v ((hI.2 v).mpr he)
      · intro h0 hak
        have := hq.2 (by simp [St, h0]) (by simp [St, pj, gsAt, hak])
        simpa [St, pj, gsAt] using this)
    (fun T hT => firing_bound a b (max L M) ch itr H_CELLS H_BUNDLE hOff T
      (by have := hT T (Nat.le_refl _); omega))
  obtain ⟨e, he, hf, hc0⟩ := first_ev (fallB (ch out0).ack) t (by omega)
  have hsafe := (gcd_hw_circuit_safe'' a b ch hC H_BUNDLE H_START_ONCE ⟨y, hy, H_WALK⟩).1
  exact ⟨e, by omega, ⟨hf, hc0⟩, hsafe 0 e ⟨hf, hc0⟩⟩

end Formal.Net.CapNet.Live.Nd
