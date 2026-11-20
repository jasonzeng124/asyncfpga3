#!/usr/bin/env python3
"""xinv_patch.py TOOLSCOPY -- runtime patch (after ineq_patch.py and truncinv_patch.py if those are set) to a COPY of
autoproof.py, AP_XINV=1: extra template invariants given by hand, read from xinv_<func>.txt next to this patch
(directory overridable with AP_XINV_DIR). They are HINTS only: autoproof adds them to `Is` (after its own inference)
and the generated Lean file re-checks every one of them like the inferred ones (entry, every obligation that
targets the template, and they become hypotheses `hI` of the template's own obligations). A wrong hint makes the
numerical check or Lean fail; it cannot make a false theorem pass.

File format, one template per line (# comments):   T<k>@<p>: inv; inv; ...
  k = template index, p = the C test point autoproof aligned it with (checked: refused if different);
  inv = `trunc(x)` (trunci 32 x = x, x < 2^32 as a Nat) | `A = B` | `B` (meaning B = 1);
  expressions over the C variable names and decimal literals: slt sle sgt sge eq ne ult ule (cmpi .. 32, a 0/1
  value), addi subi shrsi shli andi ori (32 bits), sel(c, a, b), trunci32(x)."""
import sys, os
T = sys.argv[1]
HERE = os.path.dirname(os.path.abspath(__file__))
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()


def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old, s.count(old))
    s = s.replace(old, new)


rep("        self.bad = self.search()\n",
    "        if os.environ.get('AP_XINV') == '1':\n            self.xinv()\n        self.bad = self.search()\n")
rep("    # ---- obligations in substituted form, and their numerical check ----\n", '''    def xinv(self):
        import re as _re
        P = self.P
        d = os.environ.get("AP_XINV_DIR", %r)
        path = os.path.join(d, f"xinv_{P.func}.txt")
        if not os.path.exists(path):
            print(f"  xinv: no {path}", file=sys.stderr)
            return
        toks = []

        def parse(txt):
            toks[:] = _re.findall(r"\\d+|[A-Za-z_]\\w*|[(),=]", txt)
            e = expr()
            if toks and toks[0] == "=":
                toks.pop(0)
                e2 = expr()
            elif e[0] == "trunc":
                e, e2 = ("un", "trunci", 32, e[1]), e[1]
            else:
                e2 = ("lit", 1)
            if toks:
                raise NotProved(f"xinv: trailing {toks} in {txt!r}")
            return e, e2

        def expr():
            t = toks.pop(0)
            if t.isdigit():
                return ("lit", int(t))
            if toks and toks[0] == "(":
                toks.pop(0)
                args = [expr()]
                while toks[0] == ",":
                    toks.pop(0)
                    args.append(expr())
                assert toks.pop(0) == ")"
                if t in ("slt", "sle", "sgt", "sge", "eq", "ne", "ult", "ule"):
                    return ("bin", ("cmpi", t), 32, args[0], args[1])
                if t in ("addi", "subi", "shrsi", "shli", "andi", "ori"):
                    return ("bin", t, 32, args[0], args[1])
                if t == "sel":
                    return ("sel", args[0], args[1], args[2])
                if t == "trunci32":
                    return ("un", "trunci", 32, args[0])
                if t == "trunc":
                    return ("trunc", args[0])
                raise NotProved(f"xinv: unknown function {t}")
            if t not in P.vars:
                raise NotProved(f"xinv: unknown variable {t}")
            return ("var", P.vars.index(t))

        for line in open(path):
            line = line.split("#")[0].strip()
            if not line:
                continue
            m = _re.fullmatch(r"T(\\d+)@(\\d+)\\s*:(.*)", line)
            if not m:
                raise NotProved(f"xinv: bad line {line!r}")
            k, p = int(m.group(1)), int(m.group(2))
            if k >= len(self.Is) or self.L[k] != p:
                raise NotProved(f"xinv: T{k} is aligned with C test point {self.L[k] if k < len(self.L) else None}, "
                                f"not {p}")
            for part in m.group(3).split(";"):
                if part.strip():
                    inv = parse(part)
                    if inv not in self.Is[k]:
                        self.Is[k].append(inv)
            print(f"  xinv T{k}: " + ", ".join(f"{show(x, P.vars)}={show(y, P.vars)}" for x, y in self.Is[k]),
                  file=sys.stderr)

    # ---- obligations in substituted form, and their numerical check ----
''' % HERE)
open(a, 'w').write(s)
