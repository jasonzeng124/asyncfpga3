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
