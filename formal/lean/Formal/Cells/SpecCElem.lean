import Formal.Cells.SpecFbChain

/-!
# Formal.Cells.SpecCElem — a routed C-element under THE Spec semantics: it switches only when forced

Shard B, THE goal, S3 (the per-cell handshake theorem of `notes/C-route-S4.md` (b), for C-elements).

## Problem, plainly
A C-element on the target is a LUT whose output `q` feeds back, through 4-13 copy gates, to one of its own
pins (`j`). Its other pins are C inputs (each possibly inverted, `pol`) and constant pins (reset, ties,
values `ov`). Every pin reads its SOURCE node through its routing with a composite delay in `[lo i, hi i]`
(shard C's collapsed relation `CGateOK`; `SpecFbChain.cbands_of_sums` gives the bands from the arcs).
`SpecFbChain.cfb_switch` says the node switches cleanly IF its forcing lasts as long as its loop. When is that
guaranteed, for every behaviour, by a condition on the cell's environment alone?

**Environment (hypothesis `hA`, the timed delay-insensitive C-element protocol):** a C input `i` changes only
when `q` already shows the input's current (old) value, and has shown it for the last `Δ i` ps. (In a network,
that is the neighbour's handshake protocol plus a wire-distance bound: the input's change is a response to
`q`'s change, and every return path from `q` to that input's source takes at least `Δ i`; `formal/out/
target_ps_allpaths.json` lists the shortest such paths on THE target.)

**Result (`celem_forced`).** Timing conditions: `hloop`, for every C input, `hi j ≤ Δ i + lo i` (the input's
earliest possible response to a switch of `q` is read after the feedback's latest confirmation: exactly the
loop-vs-path race of RaceTablePS / allpaths.py); `hM`, `hi0`: every C input's window end is at most `M`, and
one C input `i0` responds no sooner than `M`; `H` bounds every window end (it only sizes the start-up window
and the ranges of the other hypotheses), `M ≤ H`. If `q` does not toggle in `(S0 - H, S0]`, then from `S0` on,
every toggle of `q` at `t` is FORCED: at its reads at `t`, every C input (after `pol`) already shows `q`'s new
value; and no other toggle of `q` lies in `(t - M, t)`. So `q` never switches on a stale feedback read (no runt,
no hold-state switch), whatever the per-pin read times inside the bands. `celem_forced'` restates it without
the read functions: every C input's source shows the new value at some time in `[t - hi i, t - lo i]`.

**INIT facts used (decided per instance):** `hall`: if every C input shows `w`, the output is `w` whatever
the feedback reads; `hhold`: if the feedback reads `!w` and the output is `w`, every C input shows `w`. Both
say "a C-element" and nothing else (they hold for C_n with any input polarities, reset held inactive).

## Not covered
That the network supplies `hA` (C's composition: the neighbours' protocol and the path distances); the
`Δ` actually available on THE target (allpaths.py, untrusted, κ* ≈ 0.298 for the tightest node if every
static path were a causal one); arbiters (two inputs racing in opposite senses violate `hA` by design; see
`ArbClean`); latches (a mux-latch is not a C-element: `hall` fails for it).
-/

namespace Formal.Cells.SpecCElem

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain

/-- `s` toggles at `t`. -/
def Tog (s : Sig) (t : Nat) : Prop := s (t - 1) ≠ s t

/-- The last change of a signal before `b`: if `s a ≠ s b` (`a ≤ b`), there is `m ∈ (a, b]` with `s` equal
to `s b` on `[m, b]` and `s (m - 1) ≠ s b`. -/
theorem last_change (s : Sig) (a : Nat) : ∀ b, a ≤ b → s a ≠ s b →
    ∃ m, a < m ∧ m ≤ b ∧ s (m - 1) ≠ s b ∧ ∀ r, m ≤ r → r ≤ b → s r = s b := by
  intro b
  induction b with
  | zero =>
    intro hab hne
    have : a = 0 := by omega
    subst this; exact absurd rfl hne
  | succ b ih =>
    intro hab hne
    by_cases hs : s b = s (b + 1)
    · have hab' : a ≤ b := by
        by_contra h
        have : a = b + 1 := by omega
        subst this; exact hne rfl
      obtain ⟨m, h1, h2, h3, h4⟩ := ih hab' (by rw [hs]; exact hne)
      refine ⟨m, h1, by omega, by rw [← hs]; exact h3, fun r hr1 hr2 => ?_⟩
      by_cases hr : r ≤ b
      · rw [h4 r hr1 hr, hs]
      · have : r = b + 1 := by omega
        rw [this]
    · have hab' : a ≠ b + 1 := by
        intro h; subst h; exact hne rfl
      refine ⟨b + 1, by omega, le_refl _, by simpa using hs, fun r hr1 hr2 => ?_⟩
      have : r = b + 1 := by omega
      rw [this]

/-- Two different values at `a ≤ b` force a toggle in `(a, b]`. -/
theorem tog_between (s : Sig) {a b : Nat} (hab : a ≤ b) (hne : s a ≠ s b) :
    ∃ u, a < u ∧ u ≤ b ∧ Tog s u := by
  obtain ⟨m, h1, h2, h3, h4⟩ := last_change s a b hab hne
  exact ⟨m, h1, h2, by unfold Tog; rw [h4 m le_rfl h2]; exact h3⟩

theorem bool_ne {a b : Bool} (h : a ≠ b) : a = !b := by cases a <;> cases b <;> simp_all

theorem bool_ne' {a b : Bool} (h : a ≠ !b) : a = b := by cases a <;> cases b <;> simp_all

theorem bool_tog {a b w : Bool} (h : a ≠ b) (ha : ¬ a = w) : b = w := by cases a <;> cases b <;> cases w <;> simp_all

/-- The step shared by both halves of the proof: input `i` read `!w` at `q`'s previous toggle `u` and reads `w`
at `t`; then (by the environment hypothesis, and `u`'s separation) the change came after `u` and `t` is at
least `Δ i + lo i` after `u`. -/
theorem tau_step {x : Beh} {q : Nat} {s : Nat} {pol : Bool} {Δ lo hi M : Nat} {Fu Ft u t : Nat} {w : Bool}
    (hmon : Fu ≤ Ft) (hFt : Ft + lo ≤ t) (hFu : u ≤ Fu + hi) (hhi : hi ≤ M)
    (hiu : (x s Fu ^^ pol) = !w) (hit : (x s Ft ^^ pol) = w)
    (hq1 : x q (u - 1) = w) (hqu : ∀ r, u ≤ r → r ≤ t - 1 → x q r = !w) (hut : u < t)
    (hsep : ∀ u', u' < u → u < u' + M → ¬ Tog (x q) u')
    (hA : ∀ τ, Fu < τ → (x s (τ - 1) ^^ pol) ≠ (x s τ ^^ pol) →
      ∀ r, τ - Δ ≤ r → r ≤ τ → x q r = (x s (τ - 1) ^^ pol)) :
    u + Δ + lo ≤ t := by
  set e := fun r => x s r ^^ pol with he
  obtain ⟨τ, hτ1, hτ2, hτ3, hτ4⟩ := last_change e Fu Ft hmon (by
    show (x s Fu ^^ pol) ≠ (x s Ft ^^ pol)
    rw [hiu, hit]; cases w <;> simp)
  have hτ4' : e τ = w := by rw [hτ4 τ le_rfl hτ2]; exact hit
  have hτ3' : e (τ - 1) = !w := bool_ne (by rw [← hit]; exact hτ3)
  have hA' : ∀ r, τ - Δ ≤ r → r ≤ τ → x q r = !w := by
    intro r a b
    have := hA τ hτ1 (by show e (τ - 1) ≠ e τ; rw [hτ3', hτ4']; cases w <;> simp) r a b
    rw [this]; exact hτ3'
  by_cases hτu : u ≤ τ
  · have : ¬ (τ - Δ ≤ u - 1) := by
      intro h
      have := hA' (u - 1) h (by omega)
      rw [hq1] at this; cases w <;> simp at this
    omega
  · exfalso
    have hqτ : x q τ = !w := hA' τ (by omega) le_rfl
    obtain ⟨u', hu'1, hu'2, hu'3⟩ := tog_between (x q) (a := τ) (b := u - 1) (by omega)
      (by rw [hqτ, hq1]; cases w <;> simp)
    exact hsep u' (by omega) (by omega) hu'3

/-- **The routed C-element switches only when forced** (with the read functions of `CGateOK`).
Hypotheses on the timing: `hi i ≤ H` for every pin (`H` only sizes the start-up window and the ranges);
`hloop`: for every C input, `hi j ≤ Δ i + lo i` (the input's earliest response to `q` arrives after the
loop's latest confirmation: the race condition); `hM`/`hi0`: every C input's window end is at most `M`,
and one C input `i0` responds no sooner than `M` (then consecutive toggles of `q` are `M` apart). -/
theorem celem_forced {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi)
    (F : Nat → Nat → Nat) (hFm : ∀ i, i < g.k → Monotone (F i))
    (hF : ∀ t, S ≤ t →
      (∀ i, i < g.k → F i t ≤ t ∧ SumAdm p c (arcs i) (t - F i t)) ∧
      x g.out t = g.init.testBit (addr g.k fun i => x (src i) (F i t)))
    {j : Nat} (hj : j < g.k) (hfb : src j = g.out) (hloj : 1 ≤ lo j)
    (ci pol ov : Nat → Bool) (Δ : Nat → Nat) (H M S0 : Nat) (hSS : S ≤ S0)
    (hH : ∀ i, i < g.k → hi i ≤ H) (hMH : M ≤ H)
    (hM : ∀ i, i < g.k → i ≠ j → ci i = true → hi i ≤ M)
    (hloop : ∀ i, i < g.k → i ≠ j → ci i = true → hi j ≤ Δ i + lo i)
    (i0 : Nat) (hi0k : i0 < g.k) (hi0j : i0 ≠ j) (hi0c : ci i0 = true) (hi0 : M ≤ Δ i0 + lo i0)
    (hall : ∀ (w : Bool) (v : Nat → Bool), (∀ i, i < g.k → i ≠ j → ci i = true → (v i ^^ pol i) = w) →
      (∀ i, i < g.k → i ≠ j → ci i = false → v i = ov i) → g.init.testBit (addr g.k v) = w)
    (hhold : ∀ (w : Bool) (v : Nat → Bool), v j = !w →
      (∀ i, i < g.k → i ≠ j → ci i = false → v i = ov i) → g.init.testBit (addr g.k v) = w →
      ∀ i, i < g.k → i ≠ j → ci i = true → (v i ^^ pol i) = w)
    (hoth : ∀ i, i < g.k → i ≠ j → ci i = false → ∀ t, S0 ≤ t + H → x (src i) t = ov i)
    (hA : ∀ i, i < g.k → i ≠ j → ci i = true → ∀ τ, S0 ≤ τ + H →
      (x (src i) (τ - 1) ^^ pol i) ≠ (x (src i) τ ^^ pol i) →
      ∀ s, τ - Δ i ≤ s → s ≤ τ → x g.out s = (x (src i) (τ - 1) ^^ pol i))
    (hq0 : ∀ u, S0 < u + H → u ≤ S0 → ¬ Tog (x g.out) u) :
    ∀ t, S0 ≤ t → Tog (x g.out) t →
      (∀ i, i < g.k → i ≠ j → ci i = true → (x (src i) (F i t) ^^ pol i) = x g.out t) ∧
      (∀ u, u < t → t < u + M → ¬ Tog (x g.out) u) := by
  have hrd : ∀ t, S ≤ t → ∀ i, i < g.k → lo i ≤ t - F i t ∧ t - F i t ≤ hi i ∧ F i t ≤ t := by
    intro t ht i hi'
    obtain ⟨hr, -⟩ := hF t ht
    have h1 := hr i hi'
    exact ⟨(hb i hi' _ h1.2).1, (hb i hi' _ h1.2).2, h1.1⟩
  have hHj := hH j hj
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht htog
  set q := x g.out with hq
  set w := q t with hw
  have hprev : q (t - 1) = !w := bool_ne htog
  -- the previous toggle u, if q changed in [a, t - 1] (a ≥ S0 - H): it is after S0, forced, separated
  have prevT : ∀ a, t - H ≤ a → a ≤ t - 1 → q a = w →
      ∃ u, a < u ∧ u < t ∧ S0 < u ∧ q (u - 1) = w ∧ (∀ r, u ≤ r → r ≤ t - 1 → q r = !w) ∧
        (∀ i, i < g.k → i ≠ j → ci i = true → (x (src i) (F i u) ^^ pol i) = !w) ∧
        (∀ u', u' < u → u < u' + M → ¬ Tog q u') := by
    intro a ha1 ha2 haw
    obtain ⟨u, hu1, hu2, hu3, hu4⟩ := last_change q a (t - 1) ha2 (by rw [haw, hprev]; cases w <;> simp)
    rw [hprev] at hu3 hu4
    have hu3' : q (u - 1) = w := bool_ne' hu3
    have htu : Tog q u := by unfold Tog; rw [hu3', hu4 u le_rfl hu2]; cases w <;> simp
    have huS0 : S0 < u := by
      by_contra h
      exact hq0 u (by omega) (by omega) htu
    obtain ⟨hfu, hsepu⟩ := ih u (by omega) (by omega) htu
    have hqu : q u = !w := hu4 u le_rfl hu2
    exact ⟨u, hu1, by omega, huS0, hu3', hu4, fun i a b c => by rw [hfu i a b c, hqu], hsepu⟩
  have hothR : ∀ t', t ≤ t' → ∀ i, i < g.k → i ≠ j → ci i = false → x (src i) (F i t') = ov i := by
    intro t' ht' i hi' hij hci
    exact hoth i hi' hij hci _ (by have := hrd t' (by omega) i hi'; have := hH i hi'; omega)
  have hAu : ∀ u, S0 < u → ∀ i, i < g.k → i ≠ j → ci i = true → ∀ τ, F i u < τ →
      (x (src i) (τ - 1) ^^ pol i) ≠ (x (src i) τ ^^ pol i) →
      ∀ s, τ - Δ i ≤ s → s ≤ τ → x g.out s = (x (src i) (τ - 1) ^^ pol i) := by
    intro u hu i hi' hij hci τ hτ
    have := hrd u (by omega) i hi'; have := hH i hi'
    exact hA i hi' hij hci τ (by omega)
  -- (*) the feedback is not stale: q = !w on [t - hi j, t - 1]
  obtain ⟨hrt, hyt⟩ := hF t (by omega)
  have hstar : ∀ s, t - hi j ≤ s → s ≤ t - 1 → q s = !w := by
    intro s hs1 hs2
    by_contra hne
    have hsw : q s = w := bool_ne' hne
    obtain ⟨u, hu1, hut, huS0, hu3, hu4, hfu, hsepu⟩ := prevT s (by omega) hs2 hsw
    -- some C input reads w at t
    have hex : ∃ i, i < g.k ∧ i ≠ j ∧ ci i = true ∧ (x (src i) (F i t) ^^ pol i) = w := by
      by_contra hno
      push Not at hno
      have h1 := hall (!w) (fun i => x (src i) (F i t))
        (fun i hi' hij hci => bool_ne (hno i hi' hij hci))
        (fun i hi' hij hci => hothR t le_rfl i hi' hij hci)
      have : q t = !w := by rw [hyt]; exact h1
      rw [← hw] at this; cases w <;> simp at this
    obtain ⟨i, hik, hij, hci, hwi⟩ := hex
    have hru := hrd u (by omega) i hik
    have hrt' := hrd t (by omega) i hik
    have := tau_step (x := x) (q := g.out) (s := src i) (pol := pol i) (Δ := Δ i) (lo := lo i) (hi := hi i)
      (M := M) (hFm i hik (by omega : u ≤ t)) (by omega) (by omega) (hM i hik hij hci) (hfu i hik hij hci) hwi
      hu3 hu4 hut hsepu (hAu u huS0 i hik hij hci)
    have := hloop i hik hij hci
    omega
  have hrj := hrd t (by omega) j hj
  have hfbr : x (src j) (F j t) = !w := by
    rw [hfb]; exact hstar _ (by omega) (by omega)
  have hforced : ∀ i, i < g.k → i ≠ j → ci i = true → (x (src i) (F i t) ^^ pol i) = w := by
    intro i hik hij hci
    exact hhold w (fun i => x (src i) (F i t)) hfbr (fun i a b c => hothR t le_rfl i a b c)
      (by rw [← hyt]) i hik hij hci
  refine ⟨hforced, fun u0 hu01 hu02 htu0 => ?_⟩
  -- separation: a toggle in (t - M, t) gives a previous toggle u there; input i0 then needs Δ i0 + lo i0 < M
  have hu0w : ∃ a, t - H ≤ a ∧ a ≤ t - 1 ∧ q a = w ∧ t < a + 1 + M := by
    by_cases h : q (u0 - 1) = w
    · exact ⟨u0 - 1, by omega, by omega, h, by omega⟩
    · have h' : q u0 = w := by
        unfold Tog at htu0
        exact bool_tog htu0 h
      by_cases hu0t : u0 ≤ t - 1
      · exact ⟨u0, by omega, hu0t, h', by omega⟩
      · omega
  obtain ⟨a, ha1, ha2, haw, haM⟩ := hu0w
  obtain ⟨u, hu1, hut, huS0, hu3, hu4, hfu, hsepu⟩ := prevT a ha1 ha2 haw
  have hru := hrd u (by omega) i0 hi0k
  have hrt' := hrd t (by omega) i0 hi0k
  have := tau_step (x := x) (q := g.out) (s := src i0) (pol := pol i0) (Δ := Δ i0) (lo := lo i0) (hi := hi i0)
    (M := M) (hFm i0 hi0k (by omega : u ≤ t)) (by omega) (by omega) (hM i0 hi0k hi0j hi0c)
    (hfu i0 hi0k hi0j hi0c) (hforced i0 hi0k hi0j hi0c) hu3 hu4 hut hsepu (hAu u huS0 i0 hi0k hi0j hi0c)
  omega

/-- **Forced switching, read-free form**: in every behaviour meeting the collapsed relation, every toggle of
the C-element from `S0` on happens when every C input's source (after `pol`) has shown the new value at some
time inside that pin's read window `[t - hi i, t - lo i]`, and no other toggle lies within `H` before it. -/
theorem celem_forced' {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi)
    {j : Nat} (hj : j < g.k) (hfb : src j = g.out) (hloj : 1 ≤ lo j)
    (ci pol ov : Nat → Bool) (Δ : Nat → Nat) (H M S0 : Nat) (hSS : S ≤ S0)
    (hH : ∀ i, i < g.k → hi i ≤ H) (hMH : M ≤ H)
    (hM : ∀ i, i < g.k → i ≠ j → ci i = true → hi i ≤ M)
    (hloop : ∀ i, i < g.k → i ≠ j → ci i = true → hi j ≤ Δ i + lo i)
    (i0 : Nat) (hi0k : i0 < g.k) (hi0j : i0 ≠ j) (hi0c : ci i0 = true) (hi0 : M ≤ Δ i0 + lo i0)
    (hall : ∀ (w : Bool) (v : Nat → Bool), (∀ i, i < g.k → i ≠ j → ci i = true → (v i ^^ pol i) = w) →
      (∀ i, i < g.k → i ≠ j → ci i = false → v i = ov i) → g.init.testBit (addr g.k v) = w)
    (hhold : ∀ (w : Bool) (v : Nat → Bool), v j = !w →
      (∀ i, i < g.k → i ≠ j → ci i = false → v i = ov i) → g.init.testBit (addr g.k v) = w →
      ∀ i, i < g.k → i ≠ j → ci i = true → (v i ^^ pol i) = w)
    (hoth : ∀ i, i < g.k → i ≠ j → ci i = false → ∀ t, S0 ≤ t + H → x (src i) t = ov i)
    (hA : ∀ i, i < g.k → i ≠ j → ci i = true → ∀ τ, S0 ≤ τ + H →
      (x (src i) (τ - 1) ^^ pol i) ≠ (x (src i) τ ^^ pol i) →
      ∀ s, τ - Δ i ≤ s → s ≤ τ → x g.out s = (x (src i) (τ - 1) ^^ pol i))
    (hq0 : ∀ u, S0 < u + H → u ≤ S0 → ¬ Tog (x g.out) u) :
    ∀ t, S0 ≤ t → Tog (x g.out) t →
      (∀ i, i < g.k → i ≠ j → ci i = true →
        ∃ r, r + lo i ≤ t ∧ t ≤ r + hi i ∧ (x (src i) r ^^ pol i) = x g.out t) ∧
      (∀ u, u < t → t < u + M → ¬ Tog (x g.out) u) := by
  obtain ⟨F, hFm, hF⟩ := hg
  have key := celem_forced hb F hFm hF hj hfb hloj ci pol ov Δ H M S0 hSS hH hMH hM hloop i0 hi0k hi0j hi0c
    hi0 hall hhold hoth hA hq0
  intro t ht htog
  obtain ⟨h1, h2⟩ := key t ht htog
  refine ⟨fun i hik hij hci => ?_, h2⟩
  obtain ⟨hr, -⟩ := hF t (by omega)
  have hd := hb i hik _ (hr i hik).2
  have := (hr i hik).1
  exact ⟨F i t, by omega, by omega, h1 i hik hij hci⟩

end Formal.Cells.SpecCElem
