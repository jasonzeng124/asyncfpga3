#!/usr/bin/env python3
"""[C-10n copy of formal/tools/tcheck/compare2.py: reads one route directory instead of
tcheck/build, and adds the fallback count of the deciding tcheck instance to the note.
Usage: python3 compare2k.py DIR  (DIR holds t.out, obl.json, tighten.log, skew_v.log,
arbfork.log; writes DIR/compare2.tsv).  Logic otherwise unchanged.]

C-10g row-by-row comparison: tcheck verdicts for rules A, E, F, J against the
project's own rule outputs on the same route.

    python3 compare2.py SEED      (reads build/t2_SEED.out, build/obl2_SEED.json,
                                   build/tighten_SEED.log, build/skew_v_SEED.log,
                                   build/arbfork_SEED.log; writes build/compare2_SEED.tsv)

Per project row (A: request site, E: select gate, F: fast-fall line, J: arbiter client)
the tcheck margin per variant is the MINIMUM over that row's instances (A: over start
points; E: over launches, each launch taken credited (E) when a dominator X exists,
else E0; F: one instance; J: per flavour).  tcheck VERDICT = PASS at fastG and slowG.
"""
import json
import re
import sys
from collections import defaultdict

V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
HERE = __file__.rsplit("/", 1)[0] or "."


FB = {}


def tc_rows(path):
    """{(rule, key): {variant: [(margin, label)]}}"""
    rows = defaultdict(lambda: defaultdict(list))
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 3:
            continue
        lab = f[0].split()
        rule, key, var = lab[0], lab[1], lab[-2]
        m = None if f[2] == "none" else int(f[2])
        if f[1] == "ILLFORMED":
            m = None
        if f[1] == "FAIL" and m is None:
            m = -10**9            # request never changes: unreachable, FAIL
        rows[(rule, key)][var].append((m, " ".join(lab[2:-2])))
        FB[(rule, key, var, m)] = lab[-1].replace("fallback=", "")
    return rows


def proj_A(path):
    out, sec = {}, None
    for line in open(path):
        if re.match(r"^[A-Z]\. ", line):
            sec = line[0]
        if sec != "A":
            continue
        m = re.match(r"^\s+(\S+)\s+(\d+) links\s+\S+(?: ps)?\s+req\s+(-?\d+)\s+peak\s+(-?\d+)\s+guard\s+(\d+)"
                     r"\s+margin\s+(-?\d+)\s+(.*)$", line)
        if m:
            g, mg = int(m.group(5)), int(m.group(6))
            out[m.group(1)] = {"raw": mg + g, "guard": g, "margin": mg,
                               "verdict": "FAIL" if "VIOLATION" in m.group(7) else "PASS"}
    return out


def proj_E(path):
    out, cur = {}, None
    for line in open(path):
        m = re.match(r"^\s+(ok|VIOLATED|SLACK)\s+(\S+) (\S+)$", line)
        if m:
            cur = {"verdict": "FAIL" if m.group(1) == "VIOLATED" else "PASS"}
            continue
        if cur is None:
            continue
        m = re.match(r"^\s+launch (\S+)", line)
        if m:
            cur["launch"] = m.group(1)
        m = re.match(r"^\s+divergence point (\d+)", line)
        if m:
            cur["tc"] = int(m.group(1))
        m = re.match(r"^\s+req\s+(\S+)$", line)
        if m:
            cur["cell"] = m.group(1).rsplit("/", 1)[0]
        m = re.match(r"^\s+earliest (\d+) ps, (\d+)", line)
        if m:
            cur["t_req"], cur["k_req"] = int(m.group(1)), int(m.group(2))
        m = re.match(r"^\s+latest\s+(\d+) ps, (\d+)", line)
        if m:
            cur["t_sel"], cur["k_sel"] = int(m.group(1)), int(m.group(2))
        m = re.match(r"^\s+margin ([+-]?\d+) ps raw, ([+-]?\d+) ps guarded", line)
        if m:
            cur["raw"], cur["margin"] = int(m.group(1)), int(m.group(2))
            out[cur["cell"]] = cur
            cur = None
    return out


def proj_J(path):
    out = {}
    for line in open(path):
        m = re.match(r"^\s+(ok|VIOLATED)\s+(\S+) client (\d): A0 late (\d+) ps, grant early (\d+) ps, "
                     r"shared (\d+) ps, raw ([+-]?\d+), guarded ([+-]?\d+)", line)
        if m:
            out[f"{m.group(2)}#{m.group(3)}"] = {
                "verdict": "PASS" if m.group(1) == "ok" else "FAIL", "late": int(m.group(4)),
                "early": int(m.group(5)), "c": int(m.group(6)), "raw": int(m.group(7)),
                "margin": int(m.group(8))}
    return out


def vmin(d, v):
    xs = [m for m, _ in d.get(v, []) if m is not None]
    return min(xs) if xs else None


def verdict(mins):
    if mins["fastG"] is None or mins["slowG"] is None:
        return None
    return "PASS" if min(mins["fastG"], mins["slowG"]) >= 0 else "FAIL"


def main():
    b = sys.argv[1]
    s = b
    C = tc_rows(f"{b}/t.out")
    meta = json.load(open(f"{b}/obl.json"))["obligations"]
    P = {"A": proj_A(f"{b}/tighten.log"), "E": proj_E(f"{b}/skew_v.log"),
         "J": proj_J(f"{b}/arbfork.log"), "F": {}}
    for x in meta:
        if x["rule"] in ("F", "Fc") and x.get("project"):
            n, tf, tr, g, mg = x["project"]
            if mg is not None:
                P["F"][x["ctl"]] = {"raw": tr - tf, "guard": g, "margin": mg,
                                    "verdict": "PASS" if mg >= 0 else "FAIL"}
    lines = ["\t".join(("rule", "row", "flavour", "proj_raw", "proj_guarded", "proj",
                        *[f"tc_{v}" for v in V], "tcheck", "agree", "note"))]
    stats = defaultdict(int)
    # E: per gate, combine E0/E per launch
    E = defaultdict(lambda: defaultdict(dict))     # gate -> launch -> rule -> {v: m}
    for (rule, key), d in C.items():
        if rule in ("E", "E0"):
            for v in V:
                for m, rest in d.get(v, []):
                    launch = rest.split()[0]
                    E[key][launch].setdefault(rule, {})[v] = m
    flav = {"A": ["A"], "F": ["F", "Fc"], "J": ["J0", "Jx", "Jp"], "E": ["E", "E0"]}
    for rule in ("A", "E", "F", "J"):
        keys = sorted(set(P[rule]) | {k for (r, k) in C if r in flav[rule]})
        for key in keys:
            p = P[rule].get(key, {})
            for fl in flav[rule]:
                if rule == "E":
                    mins = {}
                    for v in V:
                        xs = []
                        for launch, rr in E.get(key, {}).items():
                            src = rr.get("E", rr.get("E0")) if fl == "E" else rr.get("E0")
                            if src and src.get(v) is not None:
                                xs.append(src[v])
                        mins[v] = min(xs) if xs else None
                else:
                    mins = {v: vmin(C.get((fl, key), {}), v) for v in V}
                cv = verdict(mins)
                pv = p.get("verdict")
                agree = "-" if (cv is None or pv is None) else ("yes" if cv == pv else "NO")
                stats[(rule, fl, pv, cv)] += 1
                note = ""
                if rule != "E":
                    fbs = sorted({FB.get((fl, key, v, mins[v]), "?") for v in ("fastG", "slowG")
                                  if mins[v] is not None})
                    note = "fallback=" + ",".join(fbs) + " "
                if rule == "E" and p:
                    note += f"proj launch={p.get('launch','?').split('.')[-4:]} tc={p.get('tc')}"
                if rule == "J" and p:
                    note += f"c_proj={p.get('c')}"
                    mj = next((x for x in meta if x.get("ctl") == key and x["rule"] == "Jx"), None)
                    if mj:
                        note += f" c_exact_sdf={mj.get('c_x_sdf')} shared_prjx={mj.get('shared_prjx')}"
                lines.append("\t".join(str(x) for x in (
                    rule, key, fl, p.get("raw", "-"), p.get("margin", "-"), pv or "-",
                    *[mins[v] if mins[v] is not None else "-" for v in V], cv or "-", agree, note)))
    txt = "\n".join(lines) + "\n"
    open(f"{b}/compare2.tsv", "w").write(txt)
    print(f"# seed {s}: rule flavour project tcheck count")
    for k, n in sorted(stats.items(), key=lambda x: str(x)):
        print("#", *k, n)


if __name__ == "__main__":
    main()
