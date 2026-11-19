import Formal.Rewrite.Steps.ScriptSound
import Formal.Rewrite.Steps.JoinExtSim
import Formal.Rewrite.Steps.ForkComm2

/-!
# Formal.Rewrite.Steps.ScriptRF — checked rewrite scripts with the ring-fusion steps (shard A, 2026-11-19)

**Problem, plainly.** research's `BDC_RING_FUSE` replaces a loop's update `u = F(x)` and test `c = G(x, n)` by one
cell that waits for `x` and `n` and packs both results into one word (`c` in the low bits), followed by a fork and
one slice per result. Can Lean check, per kernel, that the fused graph has the same complete runs as the unfused one,
without the C source?

**Proved** (`runScriptRF_sound`): for ANY rule list and ANY script over `Step` (the steps of `Script`) and three more
steps, if `runScriptRF rs ss = some (rs', pre, chg)` then `Sound rs rs' pre chg`. The new steps:
* `forkcomm2 lc lf x0 x1 n0 n1`: a fork after a two-input comp moves before two copies of it (`ForkComm2`);
* `unpack l`: a comp whose expression is a slice of a two-part packed word, `trunci w (shrui W (addi W e0 (shli W e1
  w0)) lo)`, computes the part directly (`e0` when `lo = 0, w = w0`; `e1` when `lo = w0`), given that `e0` fits in
  `w0` bits and `e1` in `W - w0` and in `w` bits, from the widths of their top operators (`unslice_eval`);
* `unjoin lx ln lc lk lb lu`: the update `comp [x2, n2] u F` that also waits for its own copy `n2` of the loop bound,
  with `F` not reading `n2`, waits for `x2` only, and `n2` leaves the bound's fork (`JoinExtSim`, read backward).

**Not covered:** token level only; packed words of more than two parts; more than two inputs to a fused cell.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## Expressions that read only their first input -/

def only0 : E → Bool
  | .var k => k == 0
  | .lit _ => true
  | .un _ _ a => only0 a
  | .bin _ _ a b => only0 a && only0 b
  | .sel s a b => only0 s && only0 a && only0 b

theorem eval_only0 : ∀ (e : E), only0 e = true → ∀ (env env' : List Nat), env.getD 0 0 = env'.getD 0 0 →
    e.eval env = e.eval env'
  | .var k, h, env, env', he => by
    simp only [only0, beq_iff_eq] at h; subst h; exact he
  | .lit _, _, _, _, _ => rfl
  | .un _ _ a, h, env, env', he => by
    simp only [only0] at h; simp only [E.eval, eval_only0 a h env env' he]
  | .bin _ _ a b, h, env, env', he => by
    simp only [only0, Bool.and_eq_true] at h
    simp only [E.eval, eval_only0 a h.1 env env' he, eval_only0 b h.2 env env' he]
  | .sel s a b, h, env, env', he => by
    simp only [only0, Bool.and_eq_true] at h
    simp only [E.eval, eval_only0 s h.1.1 env env' he, eval_only0 a h.1.2 env env' he,
      eval_only0 b h.2 env env' he]

/-! ## Width bounds from the top operator -/

def bw : E → Option Nat
  | .un .trunci w _ => some w
  | .un .extui w _ => some w
  | .bin .addi w _ _ => some w
  | .bin .subi w _ _ => some w
  | .bin .muli w _ _ => some w
  | .bin .andi w _ _ => some w
  | .bin .ori w _ _ => some w
  | .bin .xori w _ _ => some w
  | .bin .shli w _ _ => some w
  | .bin (.cmpi _) _ _ _ => some 1
  | _ => none

theorem b2n_lt (b : Bool) : Ops.b2n b < 2 ^ 1 := by cases b <;> decide

theorem bw_lt : ∀ (e : E) (b : Nat), bw e = some b → ∀ env, e.eval env < 2 ^ b := by
  intro e b h env
  have P : ∀ w a, a % 2 ^ w < 2 ^ w := fun w a => Nat.mod_lt _ (Nat.two_pow_pos w)
  cases e with
  | var k => simp [bw] at h
  | lit v => simp [bw] at h
  | un o w a =>
    cases o with
    | trunci => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | extui => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | extsi => simp [bw] at h
  | bin o w a c =>
    cases o with
    | addi => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | subi => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | muli => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | andi => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | ori => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | xori => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | shli => simp only [bw, Option.some.injEq] at h; subst h; exact P _ _
    | shrsi => simp [bw] at h
    | shrui => simp [bw] at h
    | cmpi p => simp only [bw, Option.some.injEq] at h; subst h; exact b2n_lt _
  | sel s a c => simp [bw] at h

/-! ## Slices of a two-part packed word -/

theorem pack_val {a b w0 b1 W : Nat} (ha : a < 2 ^ w0) (hb : b < 2 ^ b1) (hW : w0 + b1 ≤ W) :
    Ops.addi W a (Ops.shli W b w0) = a + b * 2 ^ w0 := by
  have hp : 2 ^ (w0 + b1) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  have hbig : a + b * 2 ^ w0 < 2 ^ (w0 + b1) := by
    have h1 : a + b * 2 ^ w0 < (b + 1) * 2 ^ w0 := by rw [Nat.succ_mul]; omega
    have h2 : (b + 1) * 2 ^ w0 ≤ 2 ^ b1 * 2 ^ w0 := Nat.mul_le_mul_right _ hb
    rw [Nat.pow_add, Nat.mul_comm (2 ^ w0)]; omega
  have hsh : Ops.shli W b w0 = b * 2 ^ w0 := by
    simp only [Ops.shli, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  simp only [Ops.addi, hsh]; exact Nat.mod_eq_of_lt (by omega)

theorem pack_lo {a b w0 b1 W : Nat} (ha : a < 2 ^ w0) (hb : b < 2 ^ b1) (hW : w0 + b1 ≤ W) :
    Ops.trunci w0 (Ops.shrui W (Ops.addi W a (Ops.shli W b w0)) 0) = a := by
  rw [pack_val ha hb hW]
  have hp : 2 ^ (w0 + b1) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  simp only [Ops.trunci, Ops.shrui, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : w0 ≤ W)), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt ha]

theorem pack_hi {a b w0 b1 W w : Nat} (ha : a < 2 ^ w0) (hb : b < 2 ^ b1) (hW : w0 + b1 ≤ W) (hw : b1 ≤ w) :
    Ops.trunci w (Ops.shrui W (Ops.addi W a (Ops.shli W b w0)) w0) = b := by
  have hv := pack_val ha hb hW
  have hp : 2 ^ (w0 + b1) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  have hbig : a + b * 2 ^ w0 < 2 ^ W := by
    have h1 : a + b * 2 ^ w0 < (b + 1) * 2 ^ w0 := by rw [Nat.succ_mul]; omega
    have h2 : (b + 1) * 2 ^ w0 ≤ 2 ^ b1 * 2 ^ w0 := Nat.mul_le_mul_right _ hb
    rw [Nat.pow_add, Nat.mul_comm (2 ^ w0)] at hp; omega
  rw [hv]
  simp only [Ops.trunci, Ops.shrui, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hbig, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w0),
    Nat.div_eq_of_lt ha, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hw))

/-- The part a slice of a two-part packed word reads, when the widths allow it. -/
def unslice : E → Option E
  | .un .trunci w (.bin .shrui W (.bin .addi W1 e0 (.bin .shli W2 e1 (.lit w0))) (.lit lo)) =>
    match bw e0, bw e1 with
    | some b0, some b1 =>
      if W1 = W ∧ W2 = W ∧ b0 ≤ w0 ∧ w0 + b1 ≤ W then
        if lo = 0 ∧ w = w0 then some e0
        else if lo = w0 ∧ b1 ≤ w then some e1
        else none
      else none
    | _, _ => none
  | _ => none

theorem unslice_eval {F F' : E} (h : unslice F = some F') (env : List Nat) : F'.eval env = F.eval env := by
  unfold unslice at h
  split at h
  next w W W1 e0 W2 e1 w0 lo =>
    split at h
    next b0 b1 hb0 hb1 =>
      split at h
      next hk =>
        obtain ⟨rfl, rfl, h0, h1⟩ := hk
        have ha : e0.eval env < 2 ^ w0 :=
          Nat.lt_of_lt_of_le (bw_lt e0 b0 hb0 env) (Nat.pow_le_pow_right (by decide) h0)
        have hb : e1.eval env < 2 ^ b1 := bw_lt e1 b1 hb1 env
        split at h
        next hl =>
          obtain ⟨rfl, rfl⟩ := hl
          obtain rfl := (Option.some.inj h).symm
          simp only [E.eval, UOp.ev, BOp.ev]
          exact (pack_lo ha hb h1).symm
        next =>
          split at h
          next hl =>
            obtain ⟨rfl, hw⟩ := hl
            obtain rfl := (Option.some.inj h).symm
            simp only [E.eval, UOp.ev, BOp.ev]
            exact (pack_hi ha hb h1 hw).symm
          next => cases h
      next => cases h
    next => cases h
  next => cases h

/-! ## The three steps -/

def applyFC2 (rs : List Rule) (lc lf x0 x1 n0 n1 : Nat) : Option Res :=
  match rs[lc]?, rs[lf]? with
  | some (.comp [x, n] y G), some (.fork y' [y0, y1]) =>
    if y' = y ∧ [x, n, y, x0, x1, n0, n1, y0, y1].Nodup ∧
        allL rs (fun l r => l == lc || l == lf || readsNone [x, n, y, x0, x1, n0, n1] r) = true ∧
        allL rs (fun l r => l == lc || l == lf || writesNone [y, x0, x1, n0, n1, y0, y1] r) = true then
      some (((rs.set lc (.fork x [x0, x1])).set lf (.fork n [n0, n1])) ++ [.comp [x0, n0] y0 G, .comp [x1, n1] y1 G],
        [y, x0, x1, n0, n1], [x, n, y, x0, x1, n0, n1])
    else none
  | _, _ => none

def applyUP (rs : List Rule) (l : Nat) : Option Res :=
  match rs[l]? with
  | some (.comp ins o F) =>
    match unslice F with
    | some F' => some (rs.set l (.comp ins o F'), [], [])
    | none => none
  | _ => none

/-- The seven internal channels of the join-extension pattern. -/
def jeI (x1 x2 n1 n2 c cc u : Nat) : List Nat := [x1, x2, n1, n2, c, cc, u]

def applyUJ (rs : List Rule) (lx ln lc lk lb lu : Nat) : Option Res :=
  match rs[lx]?, rs[ln]?, rs[lc]?, rs[lk]?, rs[lb]?, rs[lu]? with
  | some (.fork x xs), some (.fork n (n2 :: ns)), some (.comp [x1, n1] c G), some (.fork c' cs),
    some (.branch cc u t f), some (.comp [x2, n2'] u' F) =>
    if c' = c ∧ n2' = n2 ∧ u' = u ∧ only0 F = true ∧ [lx, ln, lc, lk, lb, lu].Nodup ∧
        [x, n, x1, x2, n1, n2, c, cc, u].Nodup then
      if (x1 ∈ xs ∧ x2 ∈ xs ∧ x ∉ xs ∧ n1 ∉ xs ∧ n2 ∉ xs ∧ c ∉ xs ∧ cc ∉ xs ∧ u ∉ xs) ∧
          (n1 ∈ ns ∧ n ∉ ns ∧ x1 ∉ ns ∧ x2 ∉ ns ∧ n2 ∉ ns ∧ c ∉ ns ∧ cc ∉ ns ∧ u ∉ ns) then
        if (cc ∈ cs ∧ c ∉ cs ∧ x1 ∉ cs ∧ x2 ∉ cs ∧ n1 ∉ cs ∧ n2 ∉ cs ∧ u ∉ cs) ∧
            t ∉ jeI x1 x2 n1 n2 c cc u ∧ f ∉ jeI x1 x2 n1 n2 c cc u ∧
            allL rs (fun l r => l == lx || l == ln || l == lc || l == lk || l == lb || l == lu ||
              (readsNone (jeI x1 x2 n1 n2 c cc u) r && writesNone (jeI x1 x2 n1 n2 c cc u) r)) = true then
          some ((rs.set ln (.fork n ns)).set lu (.comp [x2] u F), jeI x1 x2 n1 n2 c cc u, [x2, n2, u])
        else none
      else none
    else none
  | _, _, _, _, _, _ => none

/-! ## Their soundness -/

theorem app2_lt {rs : List Rule} {k : Nat} {a b : Rule} (h : k < rs.length) : (rs ++ [a, b])[k]? = rs[k]? :=
  List.getElem?_append_left h
theorem app2_0 {rs : List Rule} {a b : Rule} : (rs ++ [a, b])[rs.length]? = some a := by simp
theorem app2_1 {rs : List Rule} {a b : Rule} : (rs ++ [a, b])[rs.length + 1]? = some b := by simp
theorem app2_gt {rs : List Rule} {k : Nat} {a b : Rule} (h : rs.length + 1 < k) : (rs ++ [a, b])[k]? = none :=
  List.getElem?_eq_none (by simp; omega)

theorem applyFC2_sound {rs : List Rule} {lc lf x0 x1 n0 n1 : Nat} {res : Res}
    (h : applyFC2 rs lc lf x0 x1 n0 n1 = some res) : Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyFC2 at h
  split at h
  next x n y G y' y0 y1 hc hf =>
    split at h
    next hk =>
      obtain ⟨hyy, hnd, hA1, hA2⟩ := hk
      subst hyy
      obtain rfl := (Option.some.inj h).symm
      have hne : lc ≠ lf := fun e => by rw [e, hf] at hc; cases hc
      have hlen : ((rs.set lc (.fork x [x0, x1])).set lf (.fork n [n0, n1])).length = rs.length := by simp
      have P : PatFC2 rs (((rs.set lc (.fork x [x0, x1])).set lf (.fork n [n0, n1])) ++
          [.comp [x0, n0] y0 G, .comp [x1, n1] y1 G]) lc lf rs.length (rs.length + 1) x n y' x0 x1 n0 n1 y0 y1 G :=
        { hc := hc
          hf := hf
          ha := none_gt (Nat.le_refl _)
          hb := none_gt (Nat.le_succ _)
          hc' := by rw [app2_lt (by rw [hlen]; exact lt_of_some hc), set_ne (Ne.symm hne), set_self hc]
          hf' := by rw [app2_lt (by rw [hlen]; exact lt_of_some hf), set_self (by rw [set_ne hne]; exact hf)]
          ha' := by rw [← hlen]; exact app2_0
          hb' := by rw [← hlen]; exact app2_1
          hab := by omega
          hsame := fun l h1 h2 h3 h4 => by
            rcases Nat.lt_or_ge l rs.length with hl | hl
            · rw [app2_lt (by rw [hlen]; exact hl), set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
            · rw [app2_gt (by rw [hlen]; omega), none_gt hl]
          hins := fun l r h1 h2 hr => of_readsNone (or3 (of_allL hA1 l r hr) h1 h2)
          houts := fun l r h1 h2 hr => of_writesNone (or3 (of_allL hA2 l r hr) h1 h2)
          hnd := hnd }
      exact ⟨fun h0 hr ht => fc2_forward P h0 hr ht, fun h0 hr ht => fc2_backward P h0 hr ht⟩
    next => cases h
  next => cases h

theorem applyUP_sound {rs : List Rule} {l : Nat} {res : Res} (h : applyUP rs l = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyUP at h
  split at h
  next ins o F hl =>
    split at h
    next F' hF =>
      obtain rfl := (Option.some.inj h).symm
      exact Sound.of_steps (same_steps hl (set_self hl) (fun k hk => set_ne (Ne.symm hk))
        (ident_fire (fun vs _ => unslice_eval hF vs)))
    next => cases h
  next => cases h

theorem or6 {l a b c d e g : Nat} {X : Bool}
    (h : (l == a || l == b || l == c || l == d || l == e || l == g || X) = true)
    (h1 : l ≠ a) (h2 : l ≠ b) (h3 : l ≠ c) (h4 : l ≠ d) (h5 : l ≠ e) (h6 : l ≠ g) : X = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4
  · exact absurd h h5
  · exact absurd h h6
  · exact h

theorem applyUJ_sound {rs : List Rule} {lx ln lc lk lb lu : Nat} {res : Res}
    (h : applyUJ rs lx ln lc lk lb lu = some res) : Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyUJ at h
  split at h
  next x xs n n2 ns x1 n1 c G c' cs cc u t f x2 n2' u' F hx hn hc hk hb hu =>
    split at h
    · split at h
      · split at h
        · rename_i hk1 hk2 hk3
          obtain ⟨e1, e2, e3, hF, hlab, hnd⟩ := hk1
          obtain ⟨hxs, hns⟩ := hk2
          obtain ⟨hcs, ht, hf, hA⟩ := hk3
          rw [e1] at hk; rw [e2, e3] at hu
          obtain rfl := (Option.some.inj h).symm
          have hlab' := hlab
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hlab'
          obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1, -⟩ := hlab'
          have gx : ((rs.set ln (.fork n ns)).set lu (.comp [x2] u F))[lx]? = rs[lx]? := by
            rw [set_ne (Ne.symm a5), set_ne (Ne.symm a1)]
          have P : PatJE ((rs.set ln (.fork n ns)).set lu (.comp [x2] u F)) rs lx ln lc lk lb lu x n x1 x2 n1 n2 c cc u
              t f xs ns cs G F F :=
            { hx := by rw [gx]; exact hx
              hn := by rw [set_ne (Ne.symm b4)]; exact set_self hn
              hn' := hn
              hc := by rw [set_ne (Ne.symm c3), set_ne b1]; exact hc
              hk := by rw [set_ne (Ne.symm d2), set_ne b2]; exact hk
              hb := by rw [set_ne (Ne.symm e1), set_ne b3]; exact hb
              hu := set_self (by rw [set_ne b4]; exact hu)
              hu' := hu
              hsame := fun l h1 h2 => by rw [set_ne (Ne.symm h2), set_ne (Ne.symm h1)]
              hlab := hlab
              hout := fun l r h1 h2 h3 h4 h5 h6 hr => by
                rw [set_ne (Ne.symm h6), set_ne (Ne.symm h2)] at hr
                have := or6 (of_allL hA l r hr) h1 h2 h3 h4 h5 h6
                simp only [Bool.and_eq_true] at this
                intro ch hch
                exact ⟨fun hi => of_readsNone this.1 ch hi hch, fun ho => of_writesNone this.2 ch ho hch⟩
              hnd := hnd
              hxs := hxs
              hns := hns
              hcs := hcs
              ht := ht
              hf := hf
              hF := fun v w => eval_only0 F hF [v, w] [v] rfl }
          exact Sound.symm ⟨fun h0 hr ht => je_forward P h0 hr ht, fun h0 hr ht => je_backward P h0 hr ht⟩
        · cases h
      · cases h
    · cases h
  next => cases h

/-! ## Scripts with the ring-fusion steps -/

inductive StepRF
  | base (s : Step)
  | forkcomm2 (lc lf x0 x1 n0 n1 : Nat)
  | unpack (l : Nat)
  | unjoin (lx ln lc lk lb lu : Nat)
  deriving Repr

def applyStepRF (rs : List Rule) : StepRF → Option Res
  | .base s => applyStep rs s
  | .forkcomm2 lc lf x0 x1 n0 n1 => applyFC2 rs lc lf x0 x1 n0 n1
  | .unpack l => applyUP rs l
  | .unjoin lx ln lc lk lb lu => applyUJ rs lx ln lc lk lb lu

def runScriptRF : List Rule → List StepRF → Option Res
  | rs, [] => some (rs, [], [])
  | rs, s :: ss =>
    match applyStepRF rs s with
    | some (rs1, p1, c1) =>
      match runScriptRF rs1 ss with
      | some (rs2, p2, c2) => some (rs2, p1 ++ p2, c1 ++ c2)
      | none => none
    | none => none

theorem applyStepRF_sound {rs : List Rule} {s : StepRF} {res : Res} (h : applyStepRF rs s = some res) :
    Sound rs res.1 res.2.1 res.2.2 := by
  cases s with
  | base s => exact applyStep_sound h
  | forkcomm2 lc lf x0 x1 n0 n1 => exact applyFC2_sound h
  | unpack l => exact applyUP_sound h
  | unjoin lx ln lc lk lb lu => exact applyUJ_sound h

/-- **The pass theorem with the ring-fusion steps.** A script `runScriptRF` accepts is sound. -/
theorem runScriptRF_sound : ∀ {rs : List Rule} {ss : List StepRF} {rs' : List Rule} {pre chg : List Nat},
    runScriptRF rs ss = some (rs', pre, chg) → Sound rs rs' pre chg := by
  intro rs ss
  induction ss generalizing rs with
  | nil => intro rs' pre chg h; simp only [runScriptRF, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl, rfl⟩ := h; exact Sound.refl rs
  | cons s ss ih =>
    intro rs' pre chg h
    simp only [runScriptRF] at h
    split at h
    next rs1 p1 c1 h1 =>
      split at h
      next rs2 p2 c2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (applyStepRF_sound h1).trans (ih h2)
      next => cases h
    next => cases h

end Formal.Rewrite.Steps
