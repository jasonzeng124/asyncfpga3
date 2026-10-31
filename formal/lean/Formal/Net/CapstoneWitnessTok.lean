import Formal.Net.CapstoneNetDef

/-!
# Probe C-8t: list-form traced token runs, for an explicit complete run `y` with `Good a b y`

`CapSafe.TS` keeps the store and the consumed / produced histories as functions. `TL` is the
same as three lists of length `N` (= 252, every GcdHw channel); `tstepL` / `texecL` fire rules
on it, and `tstepL_ok` / `texecL_ok` prove they agree with `tstep` / `texec` under `TL.ts`.
A run is then certified by the kernel in chunks (`texecL X ls = some X'` with literal `X`,
`X'`), so the final `TS` is a literal whose histories can be read by later kernel checks.

`good_of_texec`: a traced execution from `init a b` that ends in `final (gcd a b)` gives
`Good a b y` (the proof of `CapSafe.good_exists`, for a given run).
-/

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.GcdHw.Gcd Formal.Net.CapSafe

structure TL where
  s : List (List Nat)
  cn : List (List Nat)
  pr : List (List Nat)
  deriving DecidableEq, Repr

def TL.ts (x : TL) : TS := ⟨ofL x.s, ofL x.cn, ofL x.pr⟩

def cnGo (r : Fire Nat Nat) : Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | c, s :: ss, h :: hs => (h ++ s.take (r.1 c)) :: cnGo r (c + 1) ss hs
  | _, _, _ => []

def prGo (r : Fire Nat Nat) : Nat → List (List Nat) → List (List Nat)
  | c, h :: hs => (h ++ r.2 c) :: prGo r (c + 1) hs
  | _, [] => []

def tstepL (x : TL) (l : Nat) : Option TL :=
  match rules[l]? with
  | some r => (r.fire natVI (ofL x.s)).map fun res =>
      ⟨applyL x.s res, cnGo res 0 x.s x.cn, prGo res 0 x.pr⟩
  | none => none

def texecL (x : TL) : List Nat → Option TL
  | [] => some x
  | l :: ls => (tstepL x l).bind (texecL · ls)

def TL.ok (x : TL) : Prop := x.s.length = N ∧ x.cn.length = N ∧ x.pr.length = N

theorem cnGo_get (r : Fire Nat Nat) : ∀ (c : Nat) (ss hs : List (List Nat)) (i : Nat),
    ss.length = hs.length →
    (cnGo r c ss hs).getD i [] = hs.getD i [] ++ (ss.getD i []).take (r.1 (c + i))
  | _, [], [], _, _ => by simp [cnGo]
  | c, s :: ss, h :: hs, i, hl => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    cases i with
    | zero => simp [cnGo]
    | succ i =>
      simp only [cnGo, List.getD_cons_succ]
      rw [cnGo_get r (c + 1) ss hs i hl, show c + 1 + i = c + (i + 1) by omega]
  | _, [], _ :: _, _, hl => by simp at hl
  | _, _ :: _, [], _, hl => by simp at hl

theorem prGo_get (r : Fire Nat Nat) : ∀ (c : Nat) (hs : List (List Nat)) (i : Nat),
    i < hs.length → (prGo r c hs).getD i [] = hs.getD i [] ++ r.2 (c + i)
  | _, [], _, h => by simp at h
  | c, h :: hs, i, hi => by
    cases i with
    | zero => simp [prGo]
    | succ i =>
      simp only [prGo, List.getD_cons_succ]
      rw [prGo_get r (c + 1) hs i (by simp at hi; omega), show c + 1 + i = c + (i + 1) by omega]

theorem cnGo_len (r : Fire Nat Nat) : ∀ (c : Nat) (ss hs : List (List Nat)), ss.length = hs.length →
    (cnGo r c ss hs).length = hs.length
  | _, [], [], _ => rfl
  | c, _ :: ss, _ :: hs, hl => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp [cnGo, cnGo_len r (c + 1) ss hs hl]
  | _, [], _ :: _, hl => by simp at hl
  | _, _ :: _, [], hl => by simp at hl

theorem prGo_len (r : Fire Nat Nat) : ∀ (c : Nat) (hs : List (List Nat)), (prGo r c hs).length = hs.length
  | _, [] => rfl
  | c, _ :: hs => by simp [prGo, prGo_len r (c + 1) hs]

theorem rules_bounded : bounded N rules = true := by decide

theorem tstepL_ok {x x' : TL} {l : Nat} (hx : x.ok) (h : tstepL x l = some x') :
    tstep x.ts l = some x'.ts ∧ x'.ok := by
  unfold tstepL at h
  split at h
  · rename_i r hr
    cases hf : r.fire natVI (ofL x.s) with
    | none => rw [hf] at h; cases h
    | some res =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2, h3⟩ := hx
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold tstep
        have hG : (G l).fire x.ts.s = some res := by rw [graph_fire hr]; exact hf
        rw [hG, Option.map_some]
        congr 1
        simp only [TL.ts, TS.mk.injEq]
        refine ⟨(ofL_applyL rules_bounded h1 hr hf).symm, ?_, ?_⟩
        · funext c
          simp only [ofL]
          rw [cnGo_get res 0 x.s x.cn c (by rw [h1, h2]), Nat.zero_add]
        · funext c
          simp only [ofL]
          by_cases hc : c < x.pr.length
          · rw [prGo_get res 0 x.pr c hc, Nat.zero_add]
          · have e1 : (prGo res 0 x.pr).getD c [] = [] := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [prGo_len]; omega)]; rfl
            have e2 : x.pr.getD c [] = [] := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            have hout : c ∉ r.outsL := by
              intro hm
              have := List.all_eq_true.mp (List.all_eq_true.mp rules_bounded r (List.mem_of_getElem? hr)) c hm
              simp at this; omega
            have e3 := (r.node natVI).push_outs (ofL x.s) res c hf hout
            rw [e1, e2, e3]; rfl
      · simp only [length_applyL, h1]
      · simp only [cnGo_len res 0 x.s x.cn (by rw [h1, h2]), h2]
      · simp only [prGo_len, h3]
  · cases h

theorem texecL_ok : ∀ (ls : List Nat) {x x' : TL}, x.ok → texecL x ls = some x' →
    texec x.ts ls = some x'.ts ∧ x'.ok
  | [], x, x', hx, h => by simp only [texecL, Option.some.injEq] at h; subst h; exact ⟨rfl, hx⟩
  | l :: ls, x, x', hx, h => by
    simp only [texecL] at h
    cases hs : tstepL x l with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      obtain ⟨h1, h2⟩ := tstepL_ok hx hs
      obtain ⟨h3, h4⟩ := texecL_ok ls h2 h
      exact ⟨by simp [texec, h1, h3], h4⟩

theorem texecL_trans : ∀ {l1 l2 : List Nat} {x y z : TL}, texecL x l1 = some y → texecL y l2 = some z →
    texecL x (l1 ++ l2) = some z
  | [], _, x, y, z, h1, h2 => by simp only [texecL, Option.some.injEq] at h1; subst h1; exact h2
  | l :: l1, l2, x, y, z, h1, h2 => by
    simp only [texecL] at h1
    simp only [List.cons_append, texecL]
    cases hs : tstepL x l with
    | none => rw [hs] at h1; cases h1
    | some m => rw [hs] at h1; exact texecL_trans h1 h2

theorem texec_append : ∀ (l1 l2 : List Nat) (x : TS), texec x (l1 ++ l2) = (texec x l1).bind (texec · l2)
  | [], _, _ => rfl
  | l :: l1, l2, x => by
    simp only [List.cons_append, texec]
    cases tstep x l with
    | none => rfl
    | some z => simp [texec_append l1 l2 z]

theorem good_of_texec {a b : Nat} {ls : List Nat} {y : TS}
    (hy : texec ⟨init a b, fun _ => [], fun _ => []⟩ ls = some y) (hys : y.s = final (Nat.gcd a b)) :
    Good a b y := by
  let x0 : TS := ⟨init a b, fun _ => [], fun _ => []⟩
  have P : ∀ {P : TS → Prop}, Pres P → P x0 → P y := fun hP h0 => texec_pres hP ls x0 y hy h0
  refine ⟨hys, P (fifo_pres _) (fun c => by simp [x0]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l i os hr; exact P (fk_pres hr) (fun o _ => rfl)
  · intro l ins o e hr; exact P (cp_pres hr) ⟨0, fun _ _ => rfl, rfl⟩
  · intro l c d t f hr
    have := side_of hr; simp [sideOK] at this
    exact P (br_pres hr this) ⟨rfl, rfl, rfl⟩
  · intro l s ds o iw hr
    have := side_of hr; simp [sideOK] at this
    exact P (mx_pres hr this.1 this.2) ⟨rfl, fun j hj => by simp [x0] at hj, fun m _ => by simp [x0, cntm]⟩
  · intro c hc; exact P (np_pres c hc) rfl
  · intro c hc; exact P (nc_pres c hc) rfl

/-- The initial traced state in list form. -/
def X0 (a b : Nat) : TL := ⟨lmap [a, b] T0, List.replicate N [], List.replicate N []⟩

end Formal.Net.CapNet.Wit
