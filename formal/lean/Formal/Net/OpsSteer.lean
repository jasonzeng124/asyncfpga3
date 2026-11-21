import Formal.Net.Ops
import Formal.Net.OpsFork

/-!
# C-8f: `bd_steer` (Dynamatic `cond_br`, behind bdc's `bd_join(cond, data)`)

`cells/rtl/bd_ctl.v`: `req0 = req . ~s`, `req1 = req . s` (one LUT6_2,
INIT 8888_8888_2222_2222, B's `steer_req0/1`), `ack = ack0 + ack1` (LUT2 E,
B's `or2_spec`), data broadcast to both branches. `emit.py _op_cond_br`: the
steer's input is the join of the condition and data channels, `s` is
`cond.data[0]`, branch 1 (`s = 1`) is the TRUE result.

Here the steer's input channel `j` is that join's output (`OpsJoin`), whose bus
carries both values; `sel` reads the condition out of it and `f` the data
(bdc: `s` and the branch buses are wires from the cond and data buses;
with `Join g` choose `g [c, d] = 2 * d + c % 2`, `sel x = x % 2 == 1`,
`f x = x / 2`).

Gate model `Steer sel f j out` (`out true` = TRUE branch, `out false` = FALSE):
* H_LUT_SI: each branch request LUT moves only to `req ∧ (s == b)` of the
  previous tick; the OR LUT moves only to `ack0 ∨ ack1` of the previous tick.
  Binary, no hazard: with `req = 0` both table entries along `s` are 0, so a
  moving `s` cannot glitch it (B's `steer_tied_dontcare` / mux-tree work).
* H_DATA_WIRE: `s t = sel (j.dat t)`, branch buses `= f (j.dat t)`.
* `Held j` (the input's bundling) is what keeps `s` still inside a
  transaction: this is the steer's "select before request" obligation
  (H_STEER_SEL in the notes: the condition bus must be valid at the steer's
  `s` pin before the joined request reaches its `req` pin).

Proved: `steer_proto` (causal assume-guarantee) and `steer_data` / `steer_op`
with the forward token equations of a branch: the `i`-th input token goes to
branch `sel(σ j i)`, as that branch's token number
`#{i' < i | sel (σ j i') = b}` (branch ROUTES by the condition token).
-/

namespace Formal.Net.Ops.Steer
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.Ops.Fork

structure Steer (sel : Nat → Bool) (f : Nat → Nat) (j : Chan) (out : Bool → Chan) : Prop where
  lut : ∀ b t, (out b).req (t + 1) ≠ (out b).req t →
    (out b).req (t + 1) = (j.req t && (sel (j.dat t) == b))
  orr : ∀ t, j.ack (t + 1) ≠ j.ack t → j.ack (t + 1) = ((out true).ack t || (out false).ack t)
  dat : ∀ b t, (out b).dat t = f (j.dat t)
  initJ : j.ack 0 = false
  initO : ∀ b, (out b).req 0 = false

/-- Selected branch follows the input like a fork branch; the other is idle. -/
def SInv (jr ja s rT kT rF kF : Bool) : Bool :=
  if s then FInv jr ja rT kT && !rF && !kF else FInv jr ja rF kF && !rT && !kT

theorem sinv_step : ∀ jr ja s rT kT rF kF jr' ja' s' rT' kT' rF' kF' : Bool,
    SInv jr ja s rT kT rF kF = true →
    (jr' ≠ jr → jr = ja) → (rT' ≠ rT → rT' = (jr && (s == true))) →
    (rF' ≠ rF → rF' = (jr && (s == false))) → (ja' ≠ ja → ja' = (kT || kF)) →
    (kT' ≠ kT → kT ≠ rT) → (kF' ≠ kF → kF ≠ rF) →
    ((jr || ja) = true → (jr' || ja') = true → s' = s) →
    SInv jr' ja' s' rT' kT' rF' kF' = true := by
  intro jr ja s rT kT rF kF
  cases jr <;> cases ja <;> cases s <;> cases rT <;> cases kT <;> cases rF <;> cases kF <;> decide

theorem sinv_recv : ∀ jr ja s rT kT rF kF ja' : Bool, SInv jr ja s rT kT rF kF = true →
    (ja' ≠ ja → ja' = (kT || kF)) → ja' ≠ ja → ja ≠ jr := by decide

theorem sinv_sendT : ∀ jr ja s rT kT rF kF rT' : Bool, SInv jr ja s rT kT rF kF = true →
    (rT' ≠ rT → rT' = (jr && (s == true))) → rT' ≠ rT → rT = kT := by decide

theorem sinv_sendF : ∀ jr ja s rT kT rF kF rF' : Bool, SInv jr ja s rT kT rF kF = true →
    (rF' ≠ rF → rF' = (jr && (s == false))) → rF' ≠ rF → rF = kF := by decide

theorem sinv_off : ∀ b ja s rT kT rF kF : Bool, SInv true ja s rT kT rF kF = true →
    (s == b) = true → (if b then rT else rF) = false → ja = false := by decide

theorem scnt_incr : ∀ b jr ja s rT kT rF kF jr' ja' s' rB' : Bool,
    SInv jr ja s rT kT rF kF = true → (jr' ≠ jr → jr = ja) →
    (rB' ≠ (if b then rT else rF) → rB' = (jr && (s == b))) →
    ((jr || ja) = true → (jr' || ja') = true → s' = s) →
    (if (!jr && jr' && (s' == b)) = true then 1 else 0) +
      (if (jr && (s == b) && !(if b then rT else rF)) = true then 1 else 0) =
    (if (!(if b then rT else rF) && rB') = true then 1 else 0) +
      (if (jr' && (s' == b) && !rB') = true then 1 else 0) := by
  intro b jr ja s rT kT rF kF
  cases b <;> cases jr <;> cases ja <;> cases s <;> cases rT <;> cases kT <;> cases rF <;>
    cases kF <;> decide

variable {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}

/-- The steer's state invariant, given the protocol before `t` and the input's
bundling (which keeps the select still inside each transaction). -/
theorem steer_inv (S : Steer sel f j out) (hjr : j.req 0 = false)
    (hk : ∀ b, (out b).ack 0 = false) (hh : Held j) : ∀ t,
    (∀ s, s < t → Rules j s ∧ ∀ b, Rules (out b) s) →
    SInv (j.req t) (j.ack t) (sel (j.dat t)) ((out true).req t) ((out true).ack t)
      ((out false).req t) ((out false).ack t) = true := by
  intro t
  induction t with
  | zero =>
    intro _
    have h1 := S.initO true; have h2 := S.initO false
    have h3 := hk true; have h4 := hk false
    simp only [SInv, hjr, S.initJ, h1, h2, h3, h4]
    cases sel (j.dat 0) <;> decide
  | succ t ih =>
    intro hp
    have h0 := ih (fun s hs => hp s (by omega))
    obtain ⟨⟨hj1, _⟩, hb⟩ := hp t (by omega)
    exact sinv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 hj1 (S.lut true t) (S.lut false t) (S.orr t)
      (hb true).2 (hb false).2 (fun a b => by rw [hh t a b])

theorem steer_proto (S : Steer sel f j out) (hjr : j.req 0 = false)
    (hk : ∀ b, (out b).ack 0 = false) (hh : Held j) : ∀ t,
    (∀ s, s < t → Rules j s ∧ ∀ b, Rules (out b) s) →
    RecvStep j t ∧ ∀ b, SendStep (out b) t := by
  intro t hp
  have hi := steer_inv S hjr hk hh t hp
  refine ⟨fun h => sinv_recv _ _ _ _ _ _ _ _ hi (S.orr t) h, fun b h => ?_⟩
  cases b
  · exact sinv_sendF _ _ _ _ _ _ _ _ hi (S.lut false t) h
  · exact sinv_sendT _ _ _ _ _ _ _ _ hi (S.lut true t) h

/-! ## Network level -/

variable {C : Type}

/-- Forward token equations of a branch: the `i`-th input token goes to branch
`b = sel (σ cj i)`, as that branch's token number `#{i' < i | sel (σ cj i') = b}`,
with the data projection `f` applied. -/
def steerEq (sel : Nat → Bool) (f : Nat → Nat) (cj : C) (cout : Bool → C)
    (σ : C → Nat → Nat) : Prop :=
  ∀ i b, sel (σ cj i) = b → σ (cout b) (cnt (fun i' => sel (σ cj i') == b) i) = f (σ cj i)

theorem steer_op (ch : C → Chan) (cj : C) (cout : Bool → C)
    (S : Steer sel f (ch cj) (fun b => ch (cout b))) :
    OpProto ch [cj] [cout true, cout false] ∧
    OpData ch [cj] [cout true, cout false] (steerEq sel f cj cout) := by
  have memo : ∀ c, c ∈ [cout true, cout false] → ∃ b, c = cout b := by
    intro c hc; simp at hc; rcases hc with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have memb : ∀ b, cout b ∈ [cout true, cout false] := by intro b; cases b <;> simp
  have hcj : cj ∈ [cj] := List.mem_singleton_self _
  refine ⟨⟨fun t hi ho hhd hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := steer_proto S (hi cj hcj).1 (fun b => (ho _ (memb b)).2) (hhd cj hcj) t
      (fun s hs => ⟨(hp s hs).1 cj hcj, fun b => (hp s hs).2 _ (memb b)⟩)
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [List.mem_singleton.1 hc]; exact h.1
    · obtain ⟨b, rfl⟩ := memo c hc; exact h.2 b
  · intro c hc; rw [List.mem_singleton.1 hc]; exact S.initJ
  · intro c hc; obtain ⟨b, rfl⟩ := memo c hc; exact S.initO b
  · intro hin hout c hc k r' hoff σ hag hE
    obtain ⟨b, rfl⟩ := memo c hc
    have ⟨hpj, hhj⟩ := hin cj hcj
    have hpo : ∀ b, Protocol (ch (cout b)) := fun b => (hout _ (memb b)).1
    have hinv := fun t => steer_inv S hpj.1.1 (fun b => (hpo b).1.2) hhj t
      (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)
    have hrb : ∀ t, (ch (cout b)).req t =
        if b then (ch (cout true)).req t else (ch (cout false)).req t := by
      intro t; cases b <;> rfl
    -- count invariant for branch b
    have hcnt : ∀ t, cnt (fun u => riseB (ch cj).req u && (sel ((ch cj).dat (u + 1)) == b)) t =
        cnt (riseB (ch (cout b)).req) t +
          (if ((ch cj).req t && (sel ((ch cj).dat t) == b) && !(ch (cout b)).req t) = true
            then 1 else 0) := by
      intro t
      induction t with
      | zero => simp [cnt, hpj.1.1]
      | succ t ih =>
        have s1 : cnt (fun u => riseB (ch cj).req u && (sel ((ch cj).dat (u + 1)) == b)) (t + 1) =
            cnt (fun u => riseB (ch cj).req u && (sel ((ch cj).dat (u + 1)) == b)) t +
            (if (!(ch cj).req t && (ch cj).req (t + 1) && (sel ((ch cj).dat (t + 1)) == b)) = true
              then 1 else 0) := rfl
        have s2 : cnt (riseB (ch (cout b)).req) (t + 1) = cnt (riseB (ch (cout b)).req) t +
            (if (!(ch (cout b)).req t && (ch (cout b)).req (t + 1)) = true then 1 else 0) := rfl
        rw [s1, s2]
        have e := scnt_incr b _ _ _ _ _ _ _ ((ch cj).req (t + 1)) ((ch cj).ack (t + 1))
          (sel ((ch cj).dat (t + 1))) ((ch (cout b)).req (t + 1)) (hinv t) (hpj.2 t).1
          (by rw [← hrb t]; exact S.lut b t) (fun a1 a2 => by rw [hhj t a1 a2])
        rw [← hrb t] at e
        omega
    have hr0 : (ch (cout b)).req r' = false := by
      have := hoff.1; simp [riseB] at this; exact this.1
    have hr1 : (ch (cout b)).req (r' + 1) = true := by
      have := hoff.1; simp [riseB] at this; exact this.2
    have hl := S.lut b r' (by rw [hr0, hr1]; decide)
    rw [hr1] at hl
    have hl2 : ((ch cj).req r' && (sel ((ch cj).dat r') == b)) = true := hl.symm
    have hjr : (ch cj).req r' = true := (Bool.and_eq_true _ _ ▸ hl2).1
    have hsb : (sel ((ch cj).dat r') == b) = true := (Bool.and_eq_true _ _ ▸ hl2).2
    have hja : (ch cj).ack r' = false := by
      have := hinv r'; rw [hjr] at this
      exact sinv_off b _ _ _ _ _ _ this hsb (by rw [← hrb r']; exact hr0)
    obtain ⟨ri, i, hri, hoffj, hcr, hcf, _⟩ := open_offer hpj hjr
    have hcf' : cnt (fallB (ch cj).ack) (r' + 1) = i := by simp [cnt, fallB, hja, hcf]
    have hd0 := held_at hpj hhj hoffj hri hcf
    have hd1 := held_at hpj hhj hoffj (by omega) hcf'
    have hc := hcnt r'
    rw [hjr, hsb, hr0, hoff.2] at hc
    have hag' : ∀ i' u, u < r' → OffAt (ch cj) i' u → σ cj i' = (ch cj).dat (u + 1) :=
      fun i' u hu ho => hag cj i' u hu ho
    have hco := cnt_offers (σ := σ cj) (fun x => sel x == b) hag' r' (Nat.le_refl _)
    rw [hcr] at hco
    have hσi : σ cj i = (ch cj).dat (ri + 1) := hag cj i ri hri hoffj
    have hselb : sel (σ cj i) = b := by
      rw [hσi, ← hd0]; exact beq_iff_eq.1 hsb
    have hc1 : cnt (fun u => riseB (ch cj).req u && (sel ((ch cj).dat (u + 1)) == b)) r' =
        k + 1 := by rw [hc]; rfl
    have hsucc : cnt (fun i' => sel (σ cj i') == b) (i + 1) =
        cnt (fun i' => sel (σ cj i') == b) i + 1 := by
      show cnt (fun i' => sel (σ cj i') == b) i +
        (if (sel (σ cj i) == b) = true then 1 else 0) = _
      rw [hselb]; simp
    have hk : cnt (fun i' => sel (σ cj i') == b) i = k := by omega
    have := hE i b hselb
    rw [hk] at this
    rw [this, hσi, S.dat b, hd1]

end Formal.Net.Ops.Steer
