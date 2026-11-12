# B probe 5a: C-elements of `bd_ce.v`, functional and Kleene

File: `formal/lean/Formal/Cells/CElemFn.lean` (core Lean, imports only
`Formal.Cells.Prelim`; no new shared defs needed beyond a local
`Decidable (∀ k : K3, P k)` instance, defined in this file).

Check (clean, about 12 s wall, 95 theorems, no `sorry`/`admit`/`axiom`/`native_decide`;
`#print axioms` on the main theorems shows only `propext`):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/CElemFn.lean

## Model

All 8 cells use the real INITs and pin maps of `cells/rtl/bd_ce.v`
(bd_c2, bd_c2_set, bd_c2n, bd_c2n_set, bd_c3, bd_c4, bd_c2_norst,
bd_c3_norst), evaluated through `lutB` (binary) and `lutK` (Kleene). The
feedback pin is read as an independent input `q`, so `lutB INIT pins` is
the next-state function of the loop. Spec: `cSpec ins q` = 1 if all inputs 1,
0 if all 0, else `q`; reset is `clr rst v = !rst && v` or `set rst v = rst || v`.
Kleene spec: `cK ins q` = t if all t, f if all f, `q` if `q` definite and some
input equals `q`, else x; reset is strong-Kleene AND/OR.

## Theorems (all by `decide` unless noted)

### 1. Binary function = spec (all 8 cells)
- `c2_spec`, `c2_set_spec`, `c2n_spec` (C(a,~b)), `c2n_set_spec`, `c3_spec`,
  `c4_spec`, `c2_norst_spec`, `c3_norst_spec`: next-state of the real INIT with
  the real pin map equals the C-element spec with the cell's reset polarity,
  for all Boolean inputs.
- `c2_init_is_majority` (header's claim C(a,b) = maj(a,b,q)); `c2n_is_sr`
  (bd_c2n as SR latch: set = a.~b, reset = ~a.b, hold on tie).
- Tied pins are don't-cares: `*_tied_dontcare` (binary, every cell with tied
  pins) and `c2_tied_dontcare_K`, `c3_tied_dontcare_K` (even X on a tied pin
  does not reach O). The INIT is replicated across every tied pin, so the
  proofs do not depend on how the toolchain realises `1'b0`.

### 2. Fixed points (hold vs forced)
- `Settled next q` is a structure with the named hypothesis **H_FB_SETTLED**
  (`next q = q`: the feedback net carries O, no transition in flight; testable
  on GLS by comparing the feedback pin and O after all inputs have been stable
  longer than the loop's max routed delay at the slow corner).
- `*_fixed_iff` (all 8 cells, rst=0): `q` is stable iff the inputs are not
  unanimously `!q` (for c2n: not `a = !q ∧ b = q`).
- `c2/c2n/c3/c4_forced`: unanimous inputs give that value regardless of q.
  `c2/c2n/c3/c4_hold`: non-unanimous inputs give q (bistable hold).
- `*_rst_forced` (6 cells with rst): rst=1 forces the reset value.
- `c2_settled_unanimous`, `c4_settled_unanimous`, `c2_settled_iff` (stated
  with H_FB_SETTLED as hypothesis); `c2_nStable`, `c4_nStable`: exactly 1
  stable state when inputs unanimous, 2 otherwise; `c2_nStable_rst`: 1 under reset.

### 3. Kleene (under H_KLEENE_LUT of Prelim)
- Exact closed forms for all 3^n Kleene input vectors, rst included:
  `c2K_closed` (= kand (not rst) (cK [a,b] q)), `c2setK_closed` (kor),
  `c2nK_closed`, `c2nsetK_closed`, `c3K_closed`, `c4K_closed` (729 vectors),
  `c2norstK_closed`, `c3norstK_closed`. Note: an X reset composes as Kleene
  AND/OR with the C value; this holds because rst is a separate pin.
- `c2K_ofBool`, `c4K_ofBool`: Kleene agrees with binary on definite inputs.
- Definiteness: `c2K_both_one`/`both_zero` (a=b=1 gives 1 even with q=X);
  `c2K_x_contained` (X on b, a = held q: q undisturbed);
  `c2K_x_escapes` (X on b, a ≠ q: output X);
  `c2K_xb_definite_iff`, `c2K_xa_definite_iff`, `c2nK_xa_definite_iff`,
  `c4K_xd_definite_iff`: with X on one input, the output is definite iff q is
  definite and some other input equals q.
- Glitch freedom: `SingleX init` = for every binary vector and each of the 6
  pins, `lutK` with X on that pin equals `join` of the two endpoint binary
  values. Proved for all 8 INITs (`*_singleX`), all pins including feedback,
  rst, and tied pins. `glitchFree_of_singleX` (term proof): equal endpoints ⇒
  transit value is that definite value. Named-pin forms: `c2_glitchfree_a`,
  `c2_glitchfree_b`, `c2_glitchfree_rst`, `c4_glitchfree_d`.
- Logical metastability (X on the feedback pin): `*_meta_resolve` (all 8):
  the LUT restores a definite value from q = X iff inputs are unanimous and
  definite (c2n: a = ~b). `c2K_meta_resolves_to`: it is the common value.
  `c2K_rst_clears_x`, `c2setK_rst_sets_x`, `c4K_rst_clears_x`: definite reset
  removes X; `c2K_xrst_keeps_x`: X reset keeps X unless both inputs are f.
- Dynamics: `kIter` iterates the Kleene loop with steady inputs.
  `c2K_x_persists`: with non-unanimous inputs X is a fixed point forever
  (Kleene never resolves held metastability: that needs the analog model, 7c).
  `c2K_x_resolves`: unanimous inputs resolve X in one step and stay.
  `c2K_hold_fixed`: in hold mode f, t, x are all fixed points.

## What did not work / not done
- Nothing failed to prove. First draft had a false claim (X reset on X state
  always X): `decide` refuted it for a=b=f; corrected statement proved.
- A generic n-input theorem (for any list `ins`) of the fixed-point
  characterisation was not attempted beyond per-cell `decide`; it is not
  needed since the library has exactly these 8 cells.
- `SingleX` is proved per INIT by enumeration; the general "any INIT"
  version belongs to track 4 (Kleene LUT probes).
- Not modelled: timing of the feedback wire (5b), or the per-mux reading
  of H_KLEENE_LUT (probe Bf MuxTree); bd_ctree (5c).
- Check time is ~12 s (the 8 `SingleX` and the 729-vector `c4K_closed`
  dominate), above the "under a second" target but fine.

## Verdict
**Works.** Functional correctness of every `bd_ce.v` cell from its real INIT
and pin map, its fixed-point structure, and its complete Kleene behaviour
(including X containment, single-change glitch freedom and logical
metastability) are proved by `decide` in core Lean. Effort to finish: none for
this scope; ~0.5 day to port to A's `Formal/Core` LUT semantics when it lands.
Buys: the INITs are machine-checked against the C-element spec (closes the
"derived, never written" claim for bd_ce.v formally); the per-cell Kleene
closed forms are the lemma library the timing probe (5b) and the
composition track (8) need; and it pins down precisely that Kleene logic
cannot resolve a held X — mutual exclusion/resolution claims must come from
the analog track.

## Fidelity per primitive
- LUT6 (binary): exact as a Boolean function of the real INIT with I0 = LSB
  (Prelim's `lutB`); this is the steady-state function of the mux tree,
  ignoring transients.
- LUT6 (Kleene): relies on **H_KLEENE_LUT** (closure semantics) from Prelim;
  whether the pass-transistor tree gives exactly this is the MuxTree probe.
  Note `SingleX` (one X at a time) is the case where closure and per-mux
  semantics are most likely to coincide.
- Feedback wire: not modelled as a timed wire; only the settled reading
  **H_FB_SETTLED** (structure `Settled`) is used. Kleene iteration `kIter`
  is an untimed step model of the loop (each step = one settled LUT+wire
  traversal), not a delay model.
- Tied pins: read as constant 0 but proved irrelevant (binary and Kleene),
  so this choice carries no fidelity risk.
- Input buffers / routing: not modelled (no timing in this probe).
