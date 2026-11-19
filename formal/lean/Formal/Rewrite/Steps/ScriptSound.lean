import Formal.Rewrite.Steps.Script

/-!
# Formal.Rewrite.Steps.ScriptSound — every step `runScript` accepts is sound (shard A, 2026-11-19)

`runScript_sound`: for ANY rule list and ANY script, `runScript rs ss = some (rs', pre, chg)` gives
`Sound rs rs' pre chg` (see `Formal.Rewrite.Steps.Script`). Each `apply*_sound` turns the step's Bool checks into the
pattern structure of its local theorem (`PatAB`, `PatFJ`, `PatFS`, `PatFC`, or same firings / dead sink).
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

theorem or3 {l a b : Nat} {X : Bool} (h : (l == a || l == b || X) = true) (h1 : l ≠ a) (h2 : l ≠ b) : X = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

theorem or2 {l a : Nat} {X : Bool} (h : (l == a || X) = true) (h1 : l ≠ a) : X = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h h1
  · exact h

theorem applyAB_sound {rs : List Rule} {lp lq : Nat} {res : Res} (h : applyAB rs lp lq = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyAB at h
  split at h
  next a0 ar p f ins q g hp hq =>
    split at h
    next hc =>
      obtain ⟨hins, hne, hnd, hqn, hA1, hA2⟩ := hc
      obtain rfl := (Option.some.inj h).symm
      rw [hins] at hq
      have P : PatAB rs ((rs.set lp (.sink p)).set lq (.comp (ins.dropLast ++ a0 :: ar) q
          (absorbE ins.dropLast.length (a0 :: ar).length f g))) lp lq p q a0 ar ins.dropLast f g :=
        { hp := hp
          hq := hq
          hp' := by rw [set_ne (Ne.symm hne), set_self hp]
          hq' := set_self (by rw [set_ne hne]; exact hq)
          hlpq := hne
          hsame := fun l h1 h2 => by rw [set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
          hins := fun l r h1 h2 hr => of_readsNone (or3 (of_allL hA1 l r hr) h1 h2)
          houts := fun l r h1 hr hpo => of_writesNone (or2 (of_allL hA2 l r hr) h1) p hpo (by simp)
          hnd := hnd
          hqn := hqn }
      exact ⟨fun h0 hr ht => ab_forward P (h0 p (by simp)) hr ht,
        fun h0 hr ht => ab_backward P (h0 p (by simp)) hr ht⟩
    next => cases h
  next => cases h

theorem applyFJ_sound {rs : List Rule} {lf lc : Nat} {res : Res} (h : applyFJ rs lf lc = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyFJ at h
  split at h
  next x c0 cr ins y g hf hc =>
    split at h
    next hk =>
      obtain ⟨hins, hne, hnd, hy, hA1, hA2⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      rw [hins] at hc
      have P : PatFJ rs ((rs.set lf (.comp [x] y (allZero (c0 :: cr) g))).set lc (.sink c0)) lf lc x y c0 cr g :=
        { hf := hf
          hc := hc
          hf' := by rw [set_ne (Ne.symm hne), set_self hf]
          hc' := set_self (by rw [set_ne hne]; exact hc)
          hlfc := hne
          hsame := fun l h1 h2 => by rw [set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
          hins := fun l r h1 h2 hr => of_readsNone (or3 (of_allL hA1 l r hr) h1 h2)
          houts := fun l r h1 hr => of_writesNone (or2 (of_allL hA2 l r hr) h1)
          hnd := hnd
          hy := hy }
      exact ⟨fun h0 hr ht => fj_forward P h0 hr ht, fun h0 hr ht => fj_backward P h0 hr ht⟩
    next => cases h
  next => cases h

theorem applyFS_sound {rs : List Rule} {lf k e : Nat} {res : Res} (h : applyFS rs lf k e = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyFS at h
  split at h
  next x os hf0 =>
    split at h
    next hk =>
      obtain ⟨hnd, hA1, hA2⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      have hlen : (rs.set lf (.fork x (e :: os.drop k))).length = rs.length := List.length_set
      have hlt := lt_of_some hf0
      have P : PatFS rs (rs.set lf (.fork x (e :: os.drop k)) ++ [.fork e (os.take k)]) lf rs.length x e
          (os.take k) (os.drop k) :=
        { hf := by rw [hf0, List.take_append_drop]
          hf' := by rw [app_lt (by rw [hlen]; exact hlt), set_self hf0]
          he := none_gt (Nat.le_refl _)
          he' := by rw [← hlen]; exact app_len
          hsame := fun l h1 h2 => by
            rcases Nat.lt_or_ge l rs.length with hl | hl
            · rw [app_lt (by rw [hlen]; exact hl), set_ne (Ne.symm h1)]
            · rw [app_gt (by rw [hlen]; omega), none_gt hl]
          hins := fun l r h1 hr he => of_readsNone (or2 (of_allL hA1 l r hr) h1) e he (by simp)
          houts := fun l r h1 hr => of_writesNone (or2 (of_allL hA2 l r hr) h1)
          hnd := hnd }
      exact ⟨fun h0 hr ht => fs_forward P (h0 e (by simp)) hr ht,
        fun h0 hr ht => fs_backward P (h0 e (by simp)) hr ht⟩
    next => cases h
  next => cases h

theorem applyFC_sound {rs : List Rule} {lc lf x0 x1 : Nat} {res : Res} (h : applyFC rs lc lf x0 x1 = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyFC at h
  split at h
  next x y G y' y0 y1 hc hf =>
    split at h
    next hk =>
      obtain ⟨hyy, hnd, hA1, hA2⟩ := hk
      subst hyy
      obtain rfl := (Option.some.inj h).symm
      have hne : lc ≠ lf := fun e => by rw [e, hf] at hc; cases hc
      have hlen : ((rs.set lc (.fork x [x0, x1])).set lf (.comp [x0] y0 G)).length = rs.length := by simp
      have P : PatFC rs (((rs.set lc (.fork x [x0, x1])).set lf (.comp [x0] y0 G)) ++ [.comp [x1] y1 G])
          lc lf rs.length x y' x0 x1 y0 y1 G :=
        { hc := hc
          hf := hf
          he := none_gt (Nat.le_refl _)
          hc' := by rw [app_lt (by rw [hlen]; exact lt_of_some hc), set_ne (Ne.symm hne), set_self hc]
          hf' := by rw [app_lt (by rw [hlen]; exact lt_of_some hf), set_self (by rw [set_ne hne]; exact hf)]
          he' := by rw [← hlen]; exact app_len
          hsame := fun l h1 h2 h3 => by
            rcases Nat.lt_or_ge l rs.length with hl | hl
            · rw [app_lt (by rw [hlen]; exact hl), set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
            · rw [app_gt (by rw [hlen]; omega), none_gt hl]
          hins := fun l r h1 h2 hr => of_readsNone (or3 (of_allL hA1 l r hr) h1 h2)
          houts := fun l r h1 h2 hr => of_writesNone (or3 (of_allL hA2 l r hr) h1 h2)
          hnd := hnd }
      exact ⟨fun h0 hr ht => fc_forward P (h0 y' (by simp)) (h0 x0 (by simp)) (h0 x1 (by simp)) hr ht,
        fun h0 hr ht => fc_backward P (h0 y' (by simp)) (h0 x0 (by simp)) (h0 x1 (by simp)) hr ht⟩
    next => cases h
  next => cases h

theorem applyRO_sound {rs : List Rule} {l : Nat} {ins' : List Nat} {res : Res} (h : applyRO rs l ins' = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyRO at h
  split at h
  next ins o F hl =>
    split at h
    next hk =>
      obtain ⟨h1, h2⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      have hmem : ∀ c, c ∈ ins ↔ c ∈ ins' := fun c =>
        ⟨fun hc => by simpa using List.all_eq_true.mp h1 c hc, fun hc => by simpa using List.all_eq_true.mp h2 c hc⟩
      exact Sound.of_steps (same_steps hl (set_self hl) (fun k hk => set_ne (Ne.symm hk)) (reorder_fire hmem))
    next => cases h
  next => cases h

theorem applyFO_sound {rs : List Rule} {l : Nat} {os' : List Nat} {res : Res} (h : applyFO rs l os' = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyFO at h
  split at h
  next i os hl =>
    split at h
    next hk =>
      obtain ⟨h1, h2⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      have hmem : ∀ c, c ∈ os ↔ c ∈ os' := fun c =>
        ⟨fun hc => by simpa using List.all_eq_true.mp h1 c hc, fun hc => by simpa using List.all_eq_true.mp h2 c hc⟩
      exact Sound.of_steps (same_steps hl (set_self hl) (fun k hk => set_ne (Ne.symm hk)) (forder_fire hmem))
    next => cases h
  next => cases h

theorem applyID_sound {rs : List Rule} {l w : Nat} {res : Res} (h : applyID rs l w = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyID at h
  split at h
  next ins o F hl =>
    split at h
    next hk =>
      obtain ⟨hF, hw⟩ := hk
      subst hF
      obtain rfl := (Option.some.inj h).symm
      exact Sound.of_steps (same_steps hl (set_self hl) (fun k hk => set_ne (Ne.symm hk))
        (ident_fire (fun vs _ => colIdent w hw vs)))
    next => cases h
  next => cases h

theorem applyDR_sound {rs : List Rule} {l : Nat} {res : Res} (h : applyDR rs l = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyDR at h
  split at h
  next c hl =>
    split at h
    next hk =>
      obtain rfl := (Option.some.inj h).symm
      have hw : NoWrite rs c := fun k r hr hc => of_writesNone (of_allL hk k r hr) c hc (by simp)
      exact ⟨fun h0 hr ht => by
          obtain ⟨r, t⟩ := drop_forward hl hw (h0 c (by simp)) hr ht
          exact ⟨_, _, r, t, fun _ _ => rfl⟩,
        fun h0 hr ht => by
          obtain ⟨r, t⟩ := drop_backward hl hw (h0 c (by simp)) hr ht
          exact ⟨_, _, r, t, fun _ _ => rfl⟩⟩
    next => cases h
  next => cases h

theorem applyDD_sound {rs : List Rule} {lf lc a b : Nat} {res : Res} (h : applyDD rs lf lc a b = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyDD at h
  split at h
  next x os ins y F hf hc =>
    split at h
    next hk =>
      obtain ⟨hao, hbo, hai, hbi, hab, hosnd, hinsnd, hx, hy, hA1, hA2⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      have hne : lf ≠ lc := fun e => by rw [e, hc] at hf; cases hf
      have P : PatDD rs ((rs.set lf (.fork x (os.erase b))).set lc (.comp (ins.erase b) y (dedupE ins a b F)))
          lf lc x y a b os ins F :=
        { hf := hf
          hc := hc
          hf' := by rw [set_ne (Ne.symm hne), set_self hf]
          hc' := set_self (by rw [set_ne hne]; exact hc)
          hsame := fun l h1 h2 => by rw [set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
          hins := fun l r h1 hr => by
            have := of_readsNone (or2 (of_allL hA1 l r hr) h1)
            exact ⟨fun h => this a h (by simp), fun h => this b h (by simp)⟩
          houts := fun l r h1 hr => by
            have := of_writesNone (or2 (of_allL hA2 l r hr) h1)
            exact ⟨fun h => this a h (by simp), fun h => this b h (by simp)⟩
          hao := hao, hbo := hbo, hai := hai, hbi := hbi, hab := hab, hosnd := hosnd, hinsnd := hinsnd,
          hx := hx, hy := hy }
      exact ⟨fun h0 hr ht => dd_forward P (h0 a (by simp)) (h0 b (by simp)) hr ht,
        fun h0 hr ht => dd_backward P (h0 a (by simp)) (h0 b (by simp)) hr ht⟩
    next => cases h
  next => cases h

theorem applyW_sound {rs : List Rule} {lf lc : Nat} {res : Res} (h : applyW rs lf lc = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyW at h
  split at h
  next x a ins y F hf hc =>
    split at h
    next hk =>
      obtain ⟨hai, hnd, hxi, hxa, hy, hA1, hA2⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      have hne : lf ≠ lc := fun e => by rw [e, hc] at hf; cases hf
      have P : PatW rs ((rs.set lf (.sink a)).set lc (.comp (ins.map (swA a x)) y F)) lf lc x a y ins F :=
        { hf := hf
          hc := hc
          hf' := by rw [set_ne (Ne.symm hne), set_self hf]
          hc' := set_self (by rw [set_ne hne]; exact hc)
          hsame := fun l h1 h2 => by rw [set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
          hins := fun l r h1 h2 hr => by
            have := of_readsNone (or3 (of_allL hA1 l r hr) h1 h2)
            exact ⟨fun h => this x h (by simp), fun h => this a h (by simp)⟩
          houts := fun l r h1 hr h => of_writesNone (or2 (of_allL hA2 l r hr) h1) a h (by simp)
          hai := hai, hnd := hnd, hxi := hxi, hxa := hxa, hy := hy }
      exact ⟨fun h0 hr ht => w_forward P (h0 a (by simp)) hr ht, fun h0 hr ht => w_backward P (h0 a (by simp)) hr ht⟩
    next => cases h
  next => cases h

theorem applyCD_sound {rs : List Rule} {lc i v : Nat} {C : List Nat} {res : Res} (h : applyCD rs lc i v C = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyCD at h
  split at h
  next ins y F hc =>
    split at h
    next hk =>
      obtain ⟨hi, hC, hy, hA⟩ := hk
      obtain rfl := (Option.some.inj h).symm
      have P : PatCD rs (rs.set lc (.comp ins y (constE ins.length i v F))) lc y i v ins C F :=
        { hc := hc
          hc' := set_self hc
          hsame := fun l h1 => set_ne (Ne.symm h1)
          hi := hi
          hC := hC
          hw := fun l r hr => of_constWriterB (of_allL hA l r hr)
          hy := hy }
      exact ⟨fun h0 hr ht => cd_forward P h0 hr ht, fun h0 hr ht => cd_backward P h0 hr ht⟩
    next => cases h
  next => cases h

theorem applyStep_sound {rs : List Rule} {s : Step} {res : Res} (h : applyStep rs s = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  cases s with
  | absorb lp lq => exact applyAB_sound h
  | forkjoin lf lc => exact applyFJ_sound h
  | forksplit lf k e => exact applyFS_sound h
  | forkcomm lc lf x0 x1 => exact applyFC_sound h
  | reorder l ins' => exact applyRO_sound h
  | forder l os' => exact applyFO_sound h
  | ident l w => exact applyID_sound h
  | drop l => exact applyDR_sound h
  | dedupe lf lc a b => exact applyDD_sound h
  | wire lf lc => exact applyW_sound h
  | constdata lc i v C => exact applyCD_sound h

/-- **The pass theorem.** Whatever the rule list and the script, a script `runScript` accepts is sound. -/
theorem runScript_sound : ∀ {rs : List Rule} {ss : List Step} {rs' : List Rule} {pre chg : List Nat},
    runScript rs ss = some (rs', pre, chg) → Sound rs rs' pre chg := by
  intro rs ss
  induction ss generalizing rs with
  | nil => intro rs' pre chg h; simp only [runScript, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl, rfl⟩ := h; exact Sound.refl rs
  | cons s ss ih =>
    intro rs' pre chg h
    simp only [runScript] at h
    split at h
    next rs1 p1 c1 h1 =>
      split at h
      next rs2 p2 c2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (applyStep_sound h1).trans (ih h2)
      next => cases h
    next => cases h

end Formal.Rewrite.Steps
