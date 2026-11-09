"""BDC_CONST_DATA: a fused region reads a known-constant channel's data as a literal, and nothing else changes.

Checks, on collatz (constant4 = 1, fired by the loop's control and forked five ways):
  - off (the default): the emitted Verilog is what it was -- the shifts read e1_data / e3_data;
  - on: the same shifts read 32'h1, and every fused region keeps the same ports, joins and links (the channel
    stays; only its data wire is replaced), i.e. the two outputs differ only on datapath expression lines.
Run from the repo root or bdc/ (pytest bdc).
"""
import os
import re
import subprocess
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
MLIR = os.path.join(HERE, "..", "build", "frontend", "collatz", "comp", "handshake_transformed.mlir")


def emit(flag):
    env = dict(os.environ, BDC_CONST_DATA=flag)
    return subprocess.run([sys.executable, os.path.join(HERE, "emit.py"), MLIR], env=env, cwd=HERE,
                          check=True, capture_output=True, text=True).stdout


@pytest.mark.skipif(not os.path.exists(MLIR), reason="collatz frontend output not built")
def test_const_data_only_replaces_datapath_reads():
    off, on = emit("0"), emit("1")
    assert re.search(r"e0_data << e1_data;", off)
    assert re.search(r"\$signed\(e2_data\) >>> e3_data;", off)
    assert re.search(r"e0_data << 32'h1;", on)
    assert re.search(r"\$signed\(e2_data\) >>> 32'h1;", on)
    a, b = off.splitlines(), on.splitlines()
    assert len(a) == len(b)
    changed = [(x, y) for x, y in zip(a, b) if x != y]
    assert changed
    for x, y in changed:                      # datapath wires only: no port, join, link or delay line moved
        assert x.lstrip().startswith("wire ") and y.lstrip().startswith("wire "), (x, y)
        k = lambda s: re.sub(r"e\d+_data|32'h[0-9a-f]+", "K", s)
        assert k(x) == k(y) and x.count("_data") > y.count("_data"), (x, y)   # a data read became a literal
