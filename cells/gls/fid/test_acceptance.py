"""cells/gls/fid/acceptance.py: the SDF reading and the ring walk, by hand."""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import acceptance as A  # noqa: E402

RING = """(DELAYFILE (TIMESCALE {ts})
 (CELL (CELLTYPE "LUT1") (INSTANCE ro\\[0\\].inv)
  (DELAY (ABSOLUTE (IOPATH I0 O6 ({a}) ({b})))))
 (CELL (CELLTYPE "LUT1") (INSTANCE ro\\[0\\].g)
  (DELAY (ABSOLUTE (IOPATH I0 O6 (100:120:140) (200:220:240)))))
 (CELL (CELLTYPE "top") (INSTANCE )
  (DELAY (ABSOLUTE
   (INTERCONNECT ro\\[0\\].inv/O6 ro\\[0\\].g/I0 (10:20:30) (40:50:60))
   (INTERCONNECT ro\\[0\\].g/O6 ro\\[0\\].inv/I0 (1:2:3))
   (INTERCONNECT ro\\[0\\].g/O6 ro\\[0\\].bg/I (999:999:999))))))
"""


def write(tmp_path, ts="1ps", a="5:6:7", b="8:9:10"):
    p = tmp_path / "r.sdf"
    p.write_text(RING.format(ts=ts, a=a, b=b))
    return p


def test_ring_period_sums_rise_and_fall_at_the_corner(tmp_path):
    e = A.parse_sdf_rf(write(tmp_path), "max")
    p, err = A.ring_period(e, "ro[0].", exclude={"ro[0].bg"})
    # max corner: inv 7+10, g 140+240, wires 30+60 and 3+3 (no fall triple)
    assert err is None and p == 7 + 10 + 140 + 240 + 30 + 60 + 3 + 3
    p, _ = A.ring_period(A.parse_sdf_rf(write(tmp_path), "min"), "ro[0].", exclude={"ro[0].bg"})
    assert p == 5 + 8 + 100 + 200 + 10 + 40 + 1 + 1


def test_ns_timescale_is_scaled_to_ps(tmp_path):
    e = A.parse_sdf_rf(write(tmp_path, ts="1ns"), "typ")
    p, _ = A.ring_period(e, "ro[0].", exclude={"ro[0].bg"})
    assert p == 1000 * (6 + 9 + 120 + 220 + 20 + 50 + 2 + 2)


def test_a_tap_inside_the_ring_scope_must_be_excluded(tmp_path):
    e = A.parse_sdf_rf(write(tmp_path), "max")
    p, err = A.ring_period(e, "ro[0].")          # the bg tap is a second successor
    assert p is None and "2 in-ring successors" in err


def test_inventory_is_well_formed():
    inv = json.load(open(os.path.join(HERE, "../../../research/data/fid/inventory.json")))
    ids = [i["id"] for i in inv["items"]]
    assert len(ids) == len(set(ids))
    for it in inv["items"]:
        assert it["grade"] in ("hard", "soft", "excluded"), it["id"]
        assert it["sources"] and it["grade_reason"], it["id"]
        assert it["kind"] in ("ring_route", "ring_population", "bitstream_bug",
                              "property", "record"), it["id"]


# ------------------------------------------------------------ --stack full
import subprocess  # noqa: E402
import types  # noqa: E402
from pathlib import Path  # noqa: E402

import pytest  # noqa: E402


def test_band_reads_both_ends_of_each_triple(tmp_path):
    b = 0.25
    e = A.parse_sdf_rf(write(tmp_path), "band", band=b)
    p, err = A.ring_period(e, "ro[0].", exclude={"ro[0].bg"})
    arcs = [(5, 7), (8, 10), (100, 140), (200, 240), (10, 30), (40, 60), (1, 3), (1, 3)]
    assert err is None and p == pytest.approx(sum(lo + b * (hi - lo) for lo, hi in arcs))
    # band 0 is the min column, band 1 the max column
    for band, col in ((0.0, "min"), (1.0, "max")):
        q, _ = A.ring_period(A.parse_sdf_rf(write(tmp_path), "band", band=band), "ro[0].", exclude={"ro[0].bg"})
        r, _ = A.ring_period(A.parse_sdf_rf(write(tmp_path), col), "ro[0].", exclude={"ro[0].bg"})
        assert q == pytest.approx(r)


def args(**kw):
    d = dict(sdf_cmd=None, netlist_cmd=None, corner="max", stack="default", band=0.38)
    d.update(kw)
    return types.SimpleNamespace(**d)


def test_default_config_is_unchanged(tmp_path):
    c = A.Config(args(), tmp_path)
    assert c.describe() == {"sdf": "nextpnr routed SDF",
                            "netlist": "nextpnr routed JSON (FASM not read)", "corner": "max"}
    assert c.gls_env() == {}
    assert c.sdf_for("r.json", "n.sdf", "t") == Path("n.sdf")
    # an old-style namespace (no stack/band attributes) still works
    old = types.SimpleNamespace(sdf_cmd=None, netlist_cmd=None, corner="min")
    assert A.Config(old, tmp_path).describe()["corner"] == "min"


def test_full_stack_env_per_corner(tmp_path, monkeypatch):
    monkeypatch.setattr(A, "git_rev", lambda p: "deadbeef")
    for corner in ("min", "typ", "max"):
        c = A.Config(args(stack="full", corner=corner), tmp_path)
        assert c.gls_env() == {"GLS_MODEL": "fid", "GLS_SDF_FIELD": corner}
    c = A.Config(args(stack="full", corner="band", band=0.5), tmp_path)
    assert c.gls_env() == {"GLS_MODEL": "fid", "GLS_SDF_FIELD": "band", "GLS_SDF_BAND": "0.5"}
    d = c.describe()
    assert d["stack"] == "full" and d["model"] == "GLS_MODEL=fid" and "deadbeef" in d["sdf"]


def test_full_stack_refuses_the_hooks_and_band_needs_it(tmp_path):
    with pytest.raises(ValueError):
        A.Config(args(stack="full", sdf_cmd="x"), tmp_path)
    with pytest.raises(ValueError):
        A.Config(args(stack="full", netlist_cmd="x"), tmp_path)
    with pytest.raises(ValueError):
        A.Config(args(corner="band"), tmp_path)


@pytest.mark.parametrize("extra", [["--corner", "band"], ["--stack", "full", "--sdf-cmd", "x"]])
def test_cli_rejects_bad_combinations(tmp_path, extra):
    r = subprocess.run([sys.executable, os.path.join(HERE, "acceptance.py"), "--items", "none",
                        "--work", str(tmp_path), *extra], capture_output=True, text=True)
    assert r.returncode == 2 and "error" in r.stderr


def run_(passes, refused=(), gate_ok=True):
    return {"sim_passes": passes, "refused": list(refused), "gate_ok": gate_ok}


def test_judge_full():
    ok, weak, v = A.judge_full({"patched": run_(True), "unpatched": run_(False)})
    assert ok is True and weak is False
    ok, weak, v = A.judge_full({"patched": run_(True), "unpatched": run_(False, ["1 REFUSED: DSP"])})
    assert ok is True and weak is True and "REFUSAL" in v
    ok, weak, v = A.judge_full({"patched": run_(True), "unpatched": run_(True)})
    assert ok is False and "PASSES" in v
    ok, weak, v = A.judge_full({"patched": run_(False), "unpatched": run_(False)})
    assert ok is False and "fails the bitstream the board passed" in v
    ok, weak, v = A.judge_full({"patched": run_(True, gate_ok=False), "unpatched": run_(False)})
    assert ok is None and "INVALID" in v


def fake_gcd_route(tmp_path):
    rd = tmp_path / "route"
    rd.mkdir()
    for f, t in (("gcd_hw_routed.json", "{}"), ("gcd_hw.sdf", "sdf"), ("gcd_hw.fasm", "GOOD\n")):
        (rd / f).write_text(t)
    return rd


def wire_fakes(monkeypatch, tmp_path, changed=1, assembler=None):
    """A bit is the FASM text; the decoded netlist says which bits it came
    from; the GLS passes iff the netlist came from the good bits."""
    seen = {}

    def write_unpatched(kind, routed, fin, fout):
        Path(fout).write_text(Path(fin).read_text().replace("GOOD", "BAD" if changed else "GOOD"))
        return changed
    monkeypatch.setitem(sys.modules, "fasm_audit", types.SimpleNamespace(write_unpatched=write_unpatched))

    def to_bit(fasm, out_dir):
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "x.bit").write_text(assembler(fasm) if assembler else Path(fasm).read_text())
        return out_dir / "x.bit"
    monkeypatch.setattr(A, "to_bit", to_bit)

    def decode(bit, routed, sdf, out):
        out.mkdir(parents=True, exist_ok=True)
        (out / "fasm_routed.json").write_text(Path(bit).read_text())
        (out / "fasm.sdf").write_text("re-keyed " + Path(sdf).read_text())
        return {"json": out / "fasm_routed.json", "sdf": out / "fasm.sdf", "refused": [],
                "equiv": "VERDICT: ?"}
    monkeypatch.setattr(A, "decode_bits", decode)

    def gls(net, sdf, work, vectors, env):
        seen.setdefault("env", []).append(env)
        seen.setdefault("sdf", []).append(Path(sdf).read_text())
        good = Path(net).read_text().startswith("GOOD")
        return {v: (good or v % 2 == 0, "RESULT") for v in vectors}, True
    monkeypatch.setattr(A, "gls_gcd", gls)
    return seen


def full_cfg(tmp_path, monkeypatch):
    c = A.Config(args(stack="full", corner="max"), tmp_path / "work")
    c.work.mkdir()
    monkeypatch.setattr(c, "xray_sdf", lambda r, s, t: (tmp_path / "x.sdf", (tmp_path / "x.sdf").write_text("XRAY"))[0])
    return c


def test_full_stack_gcd_item_runs_the_buggy_bits(tmp_path, monkeypatch):
    rd = fake_gcd_route(tmp_path)
    seen = wire_fakes(monkeypatch, tmp_path)
    it = {"id": "lutpinmap_x", "route_dir": str(rd), "bug": "pinmap"}
    r = A.run_bitstream_bug(it, full_cfg(tmp_path, monkeypatch), [0, 1, 2, 3])
    assert r["stack"] == "full" and r["ok"] is True and r["weak"] is False
    assert r["runs"]["patched"]["complete"] == "4/4"
    assert r["runs"]["unpatched"]["never_complete"] == [1, 3]
    assert all(e == {"GLS_MODEL": "fid", "GLS_SDF_FIELD": "max"} for e in seen["env"])
    assert seen["sdf"] == ["re-keyed XRAY"] * 2          # the prjxray SDF, through the decoder
    assert "no .bit" in r["patched_bit"]


def test_full_stack_prefers_the_builds_bit_and_checks_reassembly(tmp_path, monkeypatch):
    rd = fake_gcd_route(tmp_path)
    (rd / "gcd_hw.bit").write_text("GOOD\n")
    wire_fakes(monkeypatch, tmp_path)
    it = {"id": "lutpinmap_x", "route_dir": str(rd), "bug": "pinmap"}
    r = A.run_bitstream_bug(it, full_cfg(tmp_path, monkeypatch), [0, 1])
    assert "byte-identical" in r["patched_bit"] and r["ok"] is True
    (rd / "gcd_hw.bit").write_text("OTHER\n")
    (tmp_path / "b").mkdir()
    r = A.run_bitstream_bug(it, full_cfg(tmp_path / "b", monkeypatch), [0, 1])
    assert "DIFFERS" in r["patched_bit"]


def test_full_stack_negative_controls(tmp_path, monkeypatch):
    """The harness must not report a MATCH when nothing reaches the bits."""
    rd = fake_gcd_route(tmp_path)
    it = {"id": "lutpinmap_x", "route_dir": str(rd), "bug": "pinmap"}
    # an assembler that ignores its input: the two bitstreams are the same
    wire_fakes(monkeypatch, tmp_path, assembler=lambda f: "GOOD\n")
    with pytest.raises(RuntimeError, match="byte-identical"):
        A.run_bitstream_bug(it, full_cfg(tmp_path, monkeypatch), [0, 1])
    # a writer that changes nothing: blocked, not a match
    (tmp_path / "w2").mkdir()
    wire_fakes(monkeypatch, tmp_path, changed=0)
    r = A.run_bitstream_bug(it, full_cfg(tmp_path / "w2", monkeypatch), [0, 1])
    assert r["ok"] is None and r["blocked"]


def test_full_stack_soak_item_refusal_is_weak(tmp_path, monkeypatch):
    rd = tmp_path / "ipow"
    pnr = rd / "seed29/pnr"
    pnr.mkdir(parents=True)
    for f, t in (("soak_routed.json", "{}"), ("soak.sdf", "sdf"), ("soak.fasm", "GOOD\n")):
        (pnr / f).write_text(t)
    wire_fakes(monkeypatch, tmp_path)
    calls = []

    def soak(seeddir, bit, sdf, work, env):
        calls.append((seeddir, Path(bit).read_text(), Path(sdf).read_text(), env))
        if Path(bit).read_text().startswith("GOOD"):
            return True, ["SOAK stalled PASS lat=1", "SOAK_VERDICT PASS"], False
        return False, ["SOAK all FAIL: the bits decode to something the model refuses: 1 REFUSED",
                       "SOAK_VERDICT FAIL"], True
    monkeypatch.setattr(A, "soak_bit", soak)
    it = {"id": "dsp_constpins", "route_dir": str(rd), "bug": "constpins-packer"}
    r = A.run_bitstream_bug(it, full_cfg(tmp_path, monkeypatch), [0])
    assert r["ok"] is True and r["weak"] is True
    assert [c[1] for c in calls] == ["GOOD\n", "BAD\n"] and all(c[2] == "XRAY" for c in calls)
    assert calls[0][0] == rd / "seed29"


def test_print_report_marks_weak(capsys):
    r = {"id": "x", "grade": "hard", "kind": "bitstream_bug", "title": "t", "sources": ["s"],
         "oracle": None, "ok": True, "weak": True, "verdict": "v", "stack": "full",
         "unpatched_lines_changed": 3, "patched_bit": "b", "md5s": {"xray_sdf": "0123456789"},
         "runs": {"patched": {"sim_passes": True, "status": "SOAK"},
                  "unpatched": {"sim_passes": False, "status": "SOAK", "refused": ["1 REFUSED"]}}}
    A.print_report({"config": {}, "results": [r]})
    out = capsys.readouterr().out
    assert "[MATCH (WEAK: by refusal)]" in out and "refused: 1 REFUSED" in out
