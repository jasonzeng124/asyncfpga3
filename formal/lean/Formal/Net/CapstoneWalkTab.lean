import Formal.Net.CapstoneCut

/-!
# Probe C-8s: tables for the proof of H_WALK (kernel-checked)

GENERATED tables by `Wip/C8s/walkgen.py` (not trusted), followed by the checks the proof in
`CapstoneWalk.lean` uses, all by kernel evaluation.

For every circuit spine channel `c` (C-8r's `spL`, 67 channels):
* `grp c`: the GcdHw spine channel whose token `c` carries (its group);
* `rho c`: its position along the group's chain of circuit channels;
* `adj c`: false only for `acc251` (the 3-input cascade's stage-1 output), which is not on
  every path through group 251;
* `al c`: the GcdHw channels whose consumption counts give `c`'s visit count (`[grp c]`, or
  `[13, 27]` for `acc251`);
* `lc c`: the GcdHw rule consuming `grp c`.

The visit-count relation the proof carries (`Rel` in `CapstoneWalk`) is
`W c' + [cur = c'] = Σ_{h ∈ al c'} #consumed(h) + Bo cur c'`, with `Bo cur c' = 1` iff `c'` is
`adj`, in the group of `cur`, and not after `cur` in it. `transOK c o dg` checks, for every spine
channel, that one walk step `c → o` (consuming GcdHw channel `dg` in the token run, or nothing
for a step inside a group) preserves it. `cOK c` checks the step out of `c` against the circuit
operator consuming `c` and the GcdHw rule consuming `grp c`.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.CapNet Formal.Net.GcdHw Formal.Net.GcdHw.Gcd

set_option maxRecDepth 100000

def spN : List Nat := [2, 4, 16, 17, 24, 34, 35, 46, 50, 77, 78, 101, 103, 104, 105, 106, 132, 151, 182, 184, 185, 186, 187, 205, 207, 238, 240, 241, 242, 243, 255, 261, 280, 281, 290, 291, 314, 315, 339, 340, 341, 342, 380, 382, 383, 384, 385, 408, 417, 419, 422, 427, 431, 435, 440, 444, 448, 454, 456, 457, 458, 459, 460, 461, 462, 463, 464]

def grpL : List Nat := [0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 70, 70, 70, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 0, 113, 113, 113, 113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143, 0, 145, 145, 145, 145, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 172, 173, 0, 0, 0, 0, 0, 0, 0, 0, 179, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 195, 196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 209, 209, 209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 0, 231, 231, 231, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 246, 0, 0, 0, 0, 0, 0, 0, 0, 251, 0, 4, 0, 0, 19, 0, 0, 0, 0, 39, 0, 0, 0, 68, 0, 0, 0, 111, 0, 0, 0, 0, 143, 0, 0, 0, 161, 0, 0, 0, 180, 0, 0, 0, 0, 0, 229, 0, 68, 95, 111, 143, 209, 229, 246, 251, 251]

def rhoL : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def adjL : List Bool := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true]

def alL : List (List Nat) := [[0], [0], [2], [0], [4], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [13], [14], [0], [0], [0], [0], [0], [0], [19], [0], [0], [0], [0], [0], [0], [0], [0], [0], [27], [28], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [35], [0], [0], [0], [39], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [57], [58], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [68], [0], [70], [70], [70], [70], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [88], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [95], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [111], [0], [113], [113], [113], [113], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [125], [0], [127], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [143], [0], [145], [145], [145], [145], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [157], [0], [0], [0], [0], [0], [161], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [172], [173], [0], [0], [0], [0], [0], [0], [0], [0], [179], [180], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [195], [196], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [209], [209], [209], [209], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [229], [0], [231], [231], [231], [231], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [246], [0], [0], [0], [0], [0], [0], [0], [0], [251], [0], [4], [0], [0], [19], [0], [0], [0], [0], [39], [0], [0], [0], [68], [0], [0], [0], [111], [0], [0], [0], [0], [143], [0], [0], [0], [161], [0], [0], [0], [180], [0], [0], [0], [0], [0], [229], [0], [68], [95], [111], [143], [209], [229], [246], [13, 27], [251]]

def lcL : List Nat := [0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 154, 9, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 155, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 38, 38, 38, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 0, 65, 65, 65, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 0, 85, 85, 85, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98, 0, 0, 0, 0, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 123, 0, 0, 0, 0, 0, 0, 0, 0, 108, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 124, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 133, 133, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 134, 134, 134, 134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 0, 0, 0, 0, 0, 0, 0, 0, 157, 0, 5, 0, 0, 14, 0, 0, 0, 0, 33, 0, 0, 0, 52, 0, 0, 0, 74, 0, 0, 0, 0, 94, 0, 0, 0, 104, 0, 0, 0, 115, 0, 0, 0, 0, 0, 144, 0, 52, 64, 74, 94, 133, 144, 156, 157, 157]

def recs : List (Nat × Nat × Nat × Bool × List Nat) := [(2, 2, 0, true, [2]), (4, 4, 0, true, [4]), (16, 13, 0, true, [13]), (17, 14, 0, true, [14]), (24, 19, 0, true, [19]), (34, 27, 0, true, [27]), (35, 28, 0, true, [28]), (46, 35, 0, true, [35]), (50, 39, 0, true, [39]), (77, 57, 0, true, [57]), (78, 58, 0, true, [58]), (101, 68, 1, true, [68]), (103, 70, 0, true, [70]), (104, 70, 1, true, [70]), (105, 70, 2, true, [70]), (106, 70, 3, true, [70]), (132, 88, 0, true, [88]), (151, 95, 1, true, [95]), (182, 111, 1, true, [111]), (184, 113, 0, true, [113]), (185, 113, 1, true, [113]), (186, 113, 2, true, [113]), (187, 113, 3, true, [113]), (205, 125, 0, true, [125]), (207, 127, 0, true, [127]), (238, 143, 1, true, [143]), (240, 145, 0, true, [145]), (241, 145, 1, true, [145]), (242, 145, 2, true, [145]), (243, 145, 3, true, [145]), (255, 157, 0, true, [157]), (261, 161, 0, true, [161]), (280, 172, 0, true, [172]), (281, 173, 0, true, [173]), (290, 179, 0, true, [179]), (291, 180, 0, true, [180]), (314, 195, 0, true, [195]), (315, 196, 0, true, [196]), (339, 209, 1, true, [209]), (340, 209, 2, true, [209]), (341, 209, 3, true, [209]), (342, 209, 4, true, [209]), (380, 229, 1, true, [229]), (382, 231, 0, true, [231]), (383, 231, 1, true, [231]), (384, 231, 2, true, [231]), (385, 231, 3, true, [231]), (408, 246, 1, true, [246]), (417, 251, 2, true, [251]), (419, 4, 1, true, [4]), (422, 19, 1, true, [19]), (427, 39, 1, true, [39]), (431, 68, 2, true, [68]), (435, 111, 2, true, [111]), (440, 143, 2, true, [143]), (444, 161, 1, true, [161]), (448, 180, 1, true, [180]), (454, 229, 2, true, [229]), (456, 68, 0, true, [68]), (457, 95, 0, true, [95]), (458, 111, 0, true, [111]), (459, 143, 0, true, [143]), (460, 209, 0, true, [209]), (461, 229, 0, true, [229]), (462, 246, 0, true, [246]), (463, 251, 0, false, [13, 27]), (464, 251, 1, true, [251])]


def grp (c : Fin NC) : Nat := grpL.getD c.val 0
def rho (c : Fin NC) : Nat := rhoL.getD c.val 0
def adj (c : Fin NC) : Bool := adjL.getD c.val true
def al (c : Fin NC) : List Nat := alL.getD c.val []
def lc (c : Fin NC) : Nat := lcL.getD c.val 0
def acc : Fin NC := 463

def gr (c : Fin NC) : Nat × Nat := (grp c, rho c)

/-- The group-position indicator of channel (g, r, a) relative to the walk's current channel. -/
def Bo (cur : Option (Nat × Nat)) (g r : Nat) (a : Bool) : Nat :=
  match cur with
  | none => 0
  | some (gc, rc) => bn (a && g == gc && decide (r ≤ rc))

def dcount (dg : Option Nat) (l : List Nat) : Nat :=
  match dg with | some h => l.count h | none => 0

def transR (c : Nat × Nat) (o : Option (Nat × Nat)) (on : Option Nat) (dg : Option Nat) :
    Nat × Nat × Nat × Bool × List Nat → Bool
  | (d, g, r, a, l) => Bo (some c) g r a + bn (on == some d) ==
      dcount dg l + Bo o g r a

def transOK (c : Fin NC) (o : Option (Fin NC)) (dg : Option Nat) : Bool :=
  recs.all (transR (gr c) (o.map gr) (o.map Fin.val) dg)

def condOK (c : Fin NC) (gc : Nat) : Bool :=
  match tab.d c.val with
  | .bj ec ed [cc, _] => ec == .var 0 && ed == .lit 0 &&
      (match tab.d cc with | .hist h _ => h == gc | _ => false)
  | _ => false

def stayOK (c o : Fin NC) : Bool := sp o && grp o == grp c && o != acc && transOK c (some o) none

def forkR (c o : Fin NC) : Bool :=
  o != acc && grp o != grp c &&
  match rules[lc c]? with
  | some (.fork i hs) => i == grp c && hs.filter (fun h => spine.contains h) == [grp o]
  | some (.cm i res idx _) => i == grp c && res == grp o && !(spine.contains idx) && res != idx
  | _ => false

def steerR (c t f : Fin NC) : Bool :=
  match rules[lc c]? with
  | some (.branch gc gd gt gf) => adj c && gd == grp c && grp t == gt && grp f == gf && gt != gf &&
      !(spine.contains gc) && gc != 3 && gc != 250 && condOK c gc && t != acc && f != acc &&
      grp t != grp c && grp f != grp c
  | _ => false

def amR (c y z : Fin NC) (w : Nat) : Bool :=
  sp z && grp z != grp c &&
  match rules[lc c]? with
  | some (.cm i res idx kk) => i == grp c && res == grp z && !(spine.contains idx) && res != idx &&
      decide (3 ≤ idx) && decide (3 ≤ res) && idx != 250 &&
      (z != acc || (res == 251 && idx == 249 && kk % 4 != 2)) &&
      (match tab.w w with
       | .lab2 gi => gi == idx && al z == [res] && kk == bn (c == y)
       | .lo3 gi => gi == 249 && idx == 249 && al z == [13, 27] && kk == bn (c == y)
       | .hi3 gi => gi == idx && al z == [res] && c == y && kk == 2)
  | _ => false

def accOK (c x y z : Fin NC) (w : Nat) : Bool :=
  c == acc && c == x && x != y && al z == [251] && tab.w w == .hi3 249 &&
    Bo (some (gr c)) (grp z) (rho z) (adj z) == 0

def sinkR (c : Fin NC) : Bool := rules[lc c]? == some (.sink (grp c))

/-- The step out of spine channel `c`. -/
def cOK (c : Fin NC) : Bool :=
  match opAt (consOf c) with
  | .link _ o => stayOK c o
  | .bjoin _ o _ _ => stayOK c o
  | .forkG _ os => match os.find? sp with
    | some o => stayOK c o || (transOK c (some o) (some (grp c)) && forkR c o)
    | none => false
  | .steerC _ t f => sp t && transOK c (some t) (some (grp c)) &&
      transOK c (some f) (some (grp c)) && steerR c t f
  | .amerge x y z w => (stayOK c z && accOK c x y z w) ||
      (transOK c (some z) (some (grp c)) && amR c y z w)
  | .sink _ => transOK c none (some (grp c)) && sinkR c
  | _ => false

def cOKn (n : Nat) : Bool := if h : n < NC then cOK ⟨n, h⟩ else false

/-! ## Kernel checks -/

theorem spN_chk : (List.range NC).all (fun n => spL.getD n false == spN.contains n) = true := by
  decide +kernel

theorem recs_chk : recs == spN.map (fun n => (n, grpL.getD n 0, rhoL.getD n 0, adjL.getD n true,
    alL.getD n [])) := by decide +kernel

theorem cOK_chk : spN.all cOKn = true := by decide +kernel

theorem recs_glob : recs.all (fun r => spine.contains r.2.1 && r.2.2.2.2.all spine.contains &&
    (!r.2.2.2.1 || r.2.2.2.2 == [r.2.1])) = true := by decide +kernel

theorem init_chk : recs.all (fun r => bn (r.1 == 2) == Bo (some (2, rhoL.getD 2 0)) r.2.1 r.2.2.1 r.2.2.2.1)
    = true := by decide +kernel

theorem grp_start : grp start = 2 := by decide

theorem spine_noend : spine.all (fun g => g != 3 && g != 250) = true := by decide

/-- Producers of a control_merge's result or index channel are that control_merge's rules. -/
def cmPairOK (r : Rule) : Bool :=
  match r with
  | .cm _ res idx _ => res != idx && decide (3 ≤ res) && decide (3 ≤ idx) &&
      rules.all (fun r2 => !(r2.outsL.contains res || r2.outsL.contains idx) ||
        (match r2 with | .cm _ res2 idx2 _ => res2 == res && idx2 == idx | _ => false))
  | _ => true

theorem cmPair_chk : rules.all cmPairOK = true := by decide +kernel

/-- The labels of control_merge12 (index channel 249). -/
def lab249OK (r : Rule) : Bool :=
  match r with
  | .cm i _ idx kk => idx != 249 || ((i, kk) == (13, 0) || (i, kk) == (27, 1) || (i, kk) == (246, 2))
  | _ => true

theorem lab249_chk : rules.all lab249OK = true := by decide +kernel

theorem r154 : rules[154]? = some (.cm 13 251 249 0) := by decide
theorem r155 : rules[155]? = some (.cm 27 251 249 1) := by decide

end Formal.Net.CapNet.Gcd
