#!/usr/bin/env python3
"""cfront_ppif_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py, CF_PPIF=1: conditional inclusion
(#if / #elif / #else / #endif, nesting allowed) whose conditions are `NAME op LITERAL`, `LITERAL op LITERAL`,
a bare NAME or LITERAL (op in == != < <= > >=), where NAME is an object-like `#define NAME LITERAL` seen earlier in
the file (decimal/hex, optional u/U) -- what the preprocessor does for this form. Lines in groups that are not
selected become empty lines (line numbers kept); the directive lines too. Anything else in a condition (undefined
names, &&, ||, defined(), arithmetic), #ifdef / #ifndef, or a selected #error is refused (SyntaxError).
Defines are NOT substituted into the code by this patch (that is CF_DEFINE). (factorial: #if UNROLL_FACTOR == 3.)"""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
FN = r'''

def ppif(src):
    """CF_PPIF (cfront_ppif_patch.py): evaluate #if/#elif/#else/#endif over `#define NAME LITERAL` constants"""
    defs, out, stack = {}, [], []   # stack entries: [this group active, some group taken, parent active]
    lit = lambda t: int(t.rstrip("uU"), 0)  # noqa: E731

    def val(t):
        if re.fullmatch(r"0[xX][0-9a-fA-F]+[uU]?|\d+[uU]?", t):
            return lit(t)
        if t in defs:
            return defs[t]
        raise SyntaxError(f"cfront: #if on {t!r} (not a #define NAME LITERAL constant)")

    def cond(e):
        m = re.fullmatch(r"\s*(\w+)\s*(==|!=|<=|>=|<|>)\s*(\w+)\s*", e)
        if m:
            a, op, b = val(m.group(1)), m.group(2), val(m.group(3))
            return {"==": a == b, "!=": a != b, "<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b}[op]
        m = re.fullmatch(r"\s*(\w+)\s*", e)
        if m:
            return val(m.group(1)) != 0
        raise SyntaxError(f"cfront: #if condition {e.strip()!r} not supported")

    for line in src.split("\n"):
        act = all(g[0] for g in stack)
        m = re.match(r"^[ \t]*#[ \t]*(\w+)(.*)$", line)
        d = m.group(1) if m else None
        if d in ("ifdef", "ifndef"):
            raise SyntaxError("cfront: #ifdef / #ifndef not supported")
        if d == "if":
            v = act and cond(m.group(2))
            stack.append([v, v, act])
            out.append("")
        elif d == "elif":
            if not stack:
                raise SyntaxError("cfront: #elif without #if")
            g = stack[-1]
            v = g[2] and not g[1] and cond(m.group(2))
            g[0] = v
            g[1] = g[1] or v
            out.append("")
        elif d == "else":
            if not stack:
                raise SyntaxError("cfront: #else without #if")
            g = stack[-1]
            g[0] = g[2] and not g[1]
            g[1] = True
            out.append("")
        elif d == "endif":
            if not stack:
                raise SyntaxError("cfront: #endif without #if")
            stack.pop()
            out.append("")
        elif not act:
            out.append("")
        else:
            if d == "error":
                raise SyntaxError(f"cfront: selected #error{m.group(2)}")
            if d == "define":
                md = re.fullmatch(r"[ \t]+([A-Za-z_]\w*)[ \t]+(0[xX][0-9a-fA-F]+[uU]?|\d+[uU]?)[ \t]*", m.group(2))
                if md:
                    defs[md.group(1)] = lit(md.group(2))
            out.append(line)
    if stack:
        raise SyntaxError("cfront: unterminated #if")
    return "\n".join(out)
'''
old = "\ndef front(path, func):\n    src = open(path).read()\n"
assert s.count(old) == 1
s = s.replace(old, FN + "\n\ndef front(path, func):\n    src = open(path).read()\n"
              "    if os.environ.get('CF_PPIF') == '1':\n        src = ppif(src)\n")
open(c, 'w').write(s)
