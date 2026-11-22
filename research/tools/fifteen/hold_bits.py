#!/usr/bin/env python3
"""hold_bits.py DUMPDIR KERNEL_V -- trace-measured hold per LATCH BIT, closing time taken at the bit's own enable pin.

hold_trace.py times a stage's close at its C node and reads only stages whose node is kept by name.  The xf2_1
corruption (JOURNAL 2026-11-15) was one bit of ulink_n7 whose ENABLE WIRE was 1637 ps long: the node had fallen, the
acknowledge had released the sender, and that bit was still open when the next value arrived.  This reads the bits
themselves, from the fullstack_dump.sh run's netlist_baked.v (every pin's wire delay, ICBUF D) and dump.vcd:
  - a latch bit is a SLICE_LUTX output with a feedback pin (FB6 / FB5) whose function is  en ? d : q  for one pin en
    and one pin d (decoded from INIT, constant pins resolved);
  - the stage it belongs to: its Q net's name in nets.map, matched against every bd_link / bd_pipe in KERNEL_V
    (data_out of a link, a pipe's internal dat[] and data_out), and that stage's P = the request it passes on
    (req_out, or the pipe's r[k+1]);
  - per bit, every enable window: open = en-pin rise, close = en-pin fall + the LUT's en arc (both at the PIN: driver
    event + wire delay); P = the stage's first request rise inside the window, at the earliest the en-pin rise.  A token is safe only if the d pin does
    not change between P and close.  margin = (first d-pin change after P) - close, negative = moved while open.
When the stage's request IS its node (DELAY 0) or is not kept by name (marked *), nothing marks the token passed on
and the window opens at the node's fall at its driver (rule H's start: the acknowledge releasing the sender).
Prints per stage: bits seen, windows, violations, min margin, the bit / time of the worst, and glitch_only (every
violating change back at its value by the close).  Same limits as hold_trace: only what the vectors exercise, at the
corner simulated.
"""
import bisect, collections, os, re, sys

d, kv = sys.argv[1], sys.argv[2]
src = open(kv).read()
nl = open(d + "/netlist_baked.v").read()
P = "bridge_i.udut."

# ---- wires: ICBUF w <- n with delay
icb = {}
for m in re.finditer(r"ICBUF #\(\.D\((\d+)\)\) \S+ \(\.I\((n\d+)\), \.O\((w\d+)\)\)", nl):
    icb[m.group(3)] = (m.group(2), int(m.group(1)))
const = {}
for l in open(d + "/nets.map"):
    if l.startswith("#"):
        continue
    a, b = l.split()[:2]
    if "PACKER_VCC" in b:
        const[a] = 1
    elif "PACKER_GND" in b:
        const[a] = 0
nm = collections.defaultdict(list)          # verilog wire -> routed names
rn = {}                                      # routed name -> verilog wire
for l in open(d + "/nets.map"):
    if l.startswith("#"):
        continue
    a, b = l.split()[:2]
    nm[a].append(b)
    rn.setdefault(b, a)


def m6(t, s):                                # s = [a1..a6] values; the FID mux tree
    idx = sum(v << i for i, v in enumerate(s))
    return (t >> idx) & 1


# ---- latch bits
bits = {}                                    # Q wire -> dict(en=(n, D, arc), d=(n, D), q)
for m in re.finditer(r"SLICE_LUTX #\(([^;]*?)\) (\S+) \(([^;]*?)\);", nl):
    params, cell, body = m.groups()
    pd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", params))
    pins = dict(re.findall(r"\.(A\d)\((w\d+)\)", body))
    for o, fbk, arck in (("O6", "FB6", "O6"), ("O5", "FB5", "O5")):
        mo = re.search(r"\." + o + r"\((n\d+)\)", body)
        if not mo or int(pd.get(fbk, "0")) == 0:
            continue
        init = int(re.sub(r"^\d*'[hH]", "", pd["INIT"]), 16)
        if o == "O5":
            init &= (1 << 32) - 1
        npins = 6 if o == "O6" else 5
        fb = int(pd[fbk]).bit_length() - 1
        val = {}                              # pin index -> constant or None
        for i in range(npins):
            w = pins.get("A%d" % (i + 1))
            n = icb.get(w, (None, 0))[0] if w else None
            val[i] = const.get(n) if n else 0
        if o == "O5":
            val[5] = 0
        free = [i for i in range(npins) if val[i] is None]
        found = None
        for en in free:
            if en == fb:
                continue
            for dd in free:
                if dd in (en, fb):
                    continue
                ok = True
                for k in range(1 << len(free)):
                    s = [val.get(i) or 0 for i in range(6)]
                    for j, i in enumerate(free):
                        s[i] = (k >> j) & 1
                    want = s[dd] if s[en] else s[fb]
                    if m6(init, s) != want:
                        ok = False
                        break
                if ok:
                    found = (en, dd)
                    break
            if found:
                break
        if not found:
            continue
        en, dd = found
        we, wd = pins["A%d" % (en + 1)], pins["A%d" % (dd + 1)]
        arc = int(pd.get("TA%d%s" % (en + 1, arck), "124"))
        bits[mo.group(1)] = {"en": icb[we] + (arc,), "d": icb[wd], "cell": cell}

# ---- stages: Q bus names -> (stage label, P wire)
stages = []                                   # (label, [Q routed names], P routed name)
for m in re.finditer(r"(bd_link|bd_pipe)\s*#\(([^;]*?)\)\s*(\w+)\s*\(([^;]*?)\);", src, re.S):
    kind, params, name, ports = m.groups()
    w = int((re.search(r"\.W\((\d+)\)", params) or [0, 1])[1])
    n = int((re.search(r"\.N\((\d+)\)", params) or [0, 1])[1]) if kind == "bd_pipe" else 1
    pr = dict(re.findall(r"\.(\w+)\(([^()]*)\)", ports))
    dout, rout = pr.get("data_out", "").strip(), pr.get("req_out", "").strip()
    for k in range(n):
        if n == 1:
            q = [P + "%s[%d]" % (dout, b) for b in range(w)] if w > 1 else [P + dout]
            pw = P + rout
            lab = name
        else:
            q = [P + "%s.many.dat[%d]" % (name, w * (k + 1) + b) for b in range(w)]
            if k == n - 1:
                q += [P + "%s[%d]" % (dout, b) for b in range(w)]
            pw = P + ("%s.many.r[%d]" % (name, k + 1) if k < n - 1 else rout)
            lab = "%s.stage[%d]" % (name, k)
        stages.append((lab, q, pw))

want = set()
plan = []
for lab, qs, pw in stages:
    qw = sorted({rn[x] for x in qs if x in rn and rn[x] in bits})
    if not qw:
        continue
    pwire = rn.get(pw)
    if not pwire:                          # request not kept by name (e.g. absorbed into a 1-input join): the
        ens = {bits[q]["en"][0] for q in qw}   # node itself: the window opens at the node's fall (below)
        if len(ens) != 1:
            continue
        pwire = ens.pop()
        lab += "*"
    plan.append((lab, qw, pwire))
    want.add(pwire)
    for q in qw:
        want.add(bits[q]["en"][0])
        want.add(bits[q]["d"][0])

ev = collections.defaultdict(list)
ids = collections.defaultdict(list)
t = 0
for l in open(d + "/dump.vcd"):
    if l.startswith("$var"):
        p = l.split()
        if p[4] in want:
            ids[p[3]].append(p[4])
    elif l[0] == "#":
        t = int(l[1:])
    elif l[0] in "01xz":
        for x in ids.get(l[1:].strip(), ()):
            ev[x].append((t, l[0]))


def valat(evs, t):
    v = None
    for tt, vv in evs:
        if tt > t:
            break
        v = vv
    return v


print("stage\tbits\twindows\tviolations\tmin_margin_ps\tworst_bit\tworst_close_ps\tglitch_only")
rows = []
for lab, qw, pwire in plan:
    prise = sorted(tt for tt, v in ev[pwire] if v == "1")
    win = viol = glitch = 0
    mm = None
    worst = ("", "")
    for q in qw:
        (en_n, en_d, arc), (d_n, d_d) = bits[q]["en"], bits[q]["d"]
        rises = [tt + en_d for tt, v in ev[en_n] if v == "1"]
        falls = [tt + en_d + arc for tt, v in ev[en_n] if v == "0"]
        dch = [(tt + d_d, v) for tt, v in ev[d_n]]
        dts = [x[0] for x in dch]
        for r in rises:
            j = bisect.bisect_right(falls, r)
            if j >= len(falls):
                continue
            f = falls[j]
            if pwire == en_n:
                # no delayed request to mark the token passed on (DELAY 0, or the request not kept): rule H's start,
                # the node's fall at its driver -- the acknowledge that releases the sender
                pr_ = f - arc - en_d
            else:
                k = bisect.bisect_left(prise, r - en_d)       # P is a driver event
                if k >= len(prise) or prise[k] > f:
                    continue
                pr_ = max(prise[k], r)      # a d change before the latch opened AT THE PIN is the token arriving
            win += 1
            i = bisect.bisect_right(dts, pr_)
            first = dts[i] if i < len(dts) else None
            nxt_i = bisect.bisect_right(rises, f)
            nxt = rises[nxt_i] if nxt_i < len(rises) else None
            if first is not None and first <= f:
                viol += 1
                m = first - f
                if valat(dch, f) == valat(dch, pr_):
                    glitch += 1
            elif first is not None and (nxt is None or first < nxt):
                m = first - f
            else:
                m = (nxt - f) if nxt else None
            if m is not None and (mm is None or m < mm):
                mm = m
                worst = (nm[q][0].replace(P, "") if nm[q] else q, f)
    if os.environ.get("HOLD_BITS_DEBUG") and not win:
        q = qw[0]
        print("  debug %s: P %s rises %d; bit %s en %s rises %d falls %d" % (
            lab, pwire, len(prise), q, bits[q]["en"][0], sum(v == "1" for _, v in ev[bits[q]["en"][0]]),
            sum(v == "0" for _, v in ev[bits[q]["en"][0]])), file=sys.stderr)
    rows.append((mm if mm is not None else 10 ** 9,
                 "%s\t%d\t%d\t%d\t%s\t%s\t%s\t%d" % (lab, len(qw), win, viol, mm if mm is not None else "NA",
                                                     worst[0], worst[1], glitch)))
for _, r in sorted(rows):
    print(r)
print("# %d latch bits decoded, %d stages measured of %d in the kernel" % (len(bits), len(plan), len(stages)),
      file=sys.stderr)
