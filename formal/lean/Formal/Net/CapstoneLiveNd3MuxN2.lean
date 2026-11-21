import Formal.Net.CapstoneLiveNd3MuxN1

/-!
# Probe C-8z3 (3b): 3-way mux persistence, selects 2 and 3, and the trace lemma

Continuation of `CapstoneLiveNd3MuxN` (split to keep each kernel run under ~2 GB).
-/

namespace Formal.Net.CapNet.Live.Nd3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

set_option maxRecDepth 100000 in
theorem npers2 : NPersS 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem npers3 : NPersS 3 := by decide +kernel

theorem npers_all (e : MuxN.MS) (hs : e.s < 4) : NPersAt e := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩ := e
  simp only at hs
  rcases (show s0 = 0 ∨ s0 = 1 ∨ s0 = 2 ∨ s0 = 3 by omega) with rfl | rfl | rfl | rfl
  · exact npers0 _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact npers1 _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact npers2 _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact npers3 _ _ _ _ _ _ _ _ _ _ _ _ _

section
variable {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}

theorem muxn_step_pers (M : MuxN.MuxN sel xs c z j) (hx : ∀ k, k < 3 → Protocol (xs k))
    (hc : Protocol c) (hz : Protocol z) (hh : Held c) (t : Nat) :
    NPers (MuxN.st sel xs c z j t) ((xs 0).req (t + 1)) ((xs 1).req (t + 1)) ((xs 2).req (t + 1))
      ((xs 0).ack (t + 1)) ((xs 1).ack (t + 1)) ((xs 2).ack (t + 1)) (c.req (t + 1))
      (c.ack (t + 1)) (z.req (t + 1)) (z.ack (t + 1)) (j 0 (t + 1)) (j 1 (t + 1)) (j 2 (t + 1))
      (MuxN.clip (sel (c.dat (t + 1)))) := by
  have hm := (MuxN.muxn_inv M (fun k hk => (hx k hk).1.1) hc.1.1 hz.1.2 hh t
    (fun s _ => ⟨fun k hk => ((hx k hk).2 s).1, (hc.2 s).1, (hz.2 s).2⟩)).1
  have K := npers_all (MuxN.st sel xs c z j t) (MuxN.clip_lt _) hm
  have cb : ∀ k, k < 3 → (MuxN.clip (sel (c.dat t)) == k) = (sel (c.dat t) == k) :=
    fun k hk => MuxN.clip_beq _ k hk
  refine K ((xs 0).req (t + 1)) ((hx 0 (by decide)).2 t).1 ((xs 1).req (t + 1))
    ((hx 1 (by decide)).2 t).1 ((xs 2).req (t + 1)) ((hx 2 (by decide)).2 t).1
    (c.req (t + 1)) (hc.2 t).1 (z.ack (t + 1)) (hz.2 t).2
    (j 0 (t + 1)) ?_ (j 1 (t + 1)) ?_ (j 2 (t + 1)) ?_
    (z.req (t + 1)) (M.zr t) ((xs 0).ack (t + 1)) (M.xa 0 (by decide) t)
    ((xs 1).ack (t + 1)) (M.xa 1 (by decide) t) ((xs 2).ack (t + 1)) (M.xa 2 (by decide) t)
    (c.ack (t + 1)) (M.ca t) _ (MuxN.clip_lt _) ?_
  · intro h; have := M.cj 0 (by decide) t h; simp only [MuxN.st, cb 0 (by decide)]; exact this
  · intro h; have := M.cj 1 (by decide) t h; simp only [MuxN.st, cb 1 (by decide)]; exact this
  · intro h; have := M.cj 2 (by decide) t h; simp only [MuxN.st, cb 2 (by decide)]; exact this
  · intro hs ⟨h1, h2⟩; apply hs; simp only [MuxN.st]; rw [hh t h1 h2]

end

end Formal.Net.CapNet.Live.Nd3
