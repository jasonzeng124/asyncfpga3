#!/usr/bin/env python3
"""test_inc_cmp.py FIR.mlir -- synthetic cases for inc_cmp.py, built by editing Dynamatic's fir fixture
(cloud/fixtures/frontend/fir/comp/handshake_transformed.mlir, whose loop test is
`%24 = cmpi ult, %21#1, %23` with %21 = fork(addi(extui i10->i11, 1)) and %23 = constant 1000 : i11).

Each case: an edit of the text, whether inc_cmp must APPLY or SKIP, and (for APPLY) ssa_check + a differential run
(hsinterp, original vs rewritten, 5 vectors x 2 schedules, 400k-step limit).  Exit 1 on any unexpected outcome.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
src = open(sys.argv[1]).read()

CMP = '%24 = cmpi ult, %21#1, %23 {'
CST = 'value = 1000 : i11}'
ADDK = 'handshake.name = "constant2", value = 1 : i11}'
FORKED_BOUND = ('%23 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1000 : i11} : <>, <i11>',
                '%23x = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1000 : i11} : <>, <i11>\n'
                '    %23:2 = fork [2] %23x {handshake.bb = 1 : ui32, handshake.name = "forkb"} : <i11>\n'
                '    %23e = extui %23#1 {handshake.bb = 1 : ui32, handshake.name = "extuib"} : <i11> to <i32>\n'
                '    %18 = addi %18m, %23e {handshake.bb = 1 : ui32, handshake.name = "addib"} : <i32>')
MUL = ('%18 = muli %dataResult, %dataResult_3', '%18m = muli %dataResult, %dataResult_3')

CTRL_TRIG = ('%13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>',
             '%13s = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>\n'
             '    %13 = br %13s {handshake.bb = 1 : ui32, handshake.name = "brtrig"} : <>')

cases = [
    ('ult as is', [], 'APPLY'),
    ('ule 999', [(CMP, '%24 = cmpi ule, %21#1, %23 {'), (CST, 'value = 999 : i11}')], 'APPLY'),
    ('ne 1000', [(CMP, '%24 = cmpi ne, %21#1, %23 {')], 'APPLY'),
    ('eq 1000 (one trip)', [(CMP, '%24 = cmpi eq, %21#1, %23 {')], 'APPLY'),
    ('ne, add on the right', [(CMP, '%24 = cmpi ne, %23, %21#1 {')], 'APPLY'),
    ('bound read through a fork, source-fired (new constant)', [FORKED_BOUND, MUL, (CMP, '%24 = cmpi ult, %21#1, %23#0 {')], 'APPLY'),
    ('bound read through a fork, control-fired', [FORKED_BOUND, MUL, (CMP, '%24 = cmpi ult, %21#1, %23#0 {'), CTRL_TRIG], 'SKIP'),
    ('bound read directly, control-fired (in place)', [CTRL_TRIG], 'APPLY'),
    ('ult bound -2 (= 2046; the i10 loop never exits)', [(CST, 'value = -2 : i11}')], 'APPLY-NONTERM'),
    ('k = 1024 (2^10-1+1024 < 2^11)', [(ADDK, 'handshake.name = "constant2", value = 1024 : i11}'), (CST, 'value = -1 : i11}')], 'APPLY-NONTERM'),
    ('ult bound 0 (C < k)', [(CST, 'value = 0 : i11}')], 'SKIP'),
    ('ult bound 1, k = 2 (C < k)', [(CST, 'value = 1 : i11}'), (ADDK, 'handshake.name = "constant2", value = 2 : i11}')], 'SKIP'),
    ('k = 1025 (may wrap)', [(ADDK, 'handshake.name = "constant2", value = 1025 : i11}')], 'SKIP'),
    ('k = 0', [(ADDK, 'handshake.name = "constant2", value = 0 : i11}')], 'SKIP'),
    ('k = -1', [(ADDK, 'handshake.name = "constant2", value = -1 : i11}')], 'SKIP'),
    ('ult, add on the right', [(CMP, '%24 = cmpi ult, %23, %21#1 {')], 'SKIP'),
    ('slt', [(CMP, '%24 = cmpi slt, %21#1, %23 {')], 'SKIP'),
    ('ugt', [(CMP, '%24 = cmpi ugt, %21#1, %23 {')], 'SKIP'),
]

bad = 0
with tempfile.TemporaryDirectory() as d:
    for name, edits, want in cases:
        t = src
        for a, b in edits:
            assert t.count(a) == 1, (name, a)
            t = t.replace(a, b)
        i, o = os.path.join(d, 'in.mlir'), os.path.join(d, 'out.mlir')
        open(i, 'w').write(t)
        log = subprocess.run([sys.executable, os.path.join(HERE, 'inc_cmp.py'), i, o], capture_output=True, text=True).stdout
        got = 'APPLY' if 'APPLY' in log else 'SKIP' if 'SKIP' in log else 'NONE'
        detail = [l for l in log.splitlines() if l.startswith(('APPLY', 'SKIP'))]
        nonterm = want == 'APPLY-NONTERM'   # both versions loop forever: the differential run must not FAIL
        ok = got == want.replace('-NONTERM', '')
        extra = ''
        if got == 'APPLY':
            sc = subprocess.run([sys.executable, os.path.join(HERE, 'ssa_check.py'), o], capture_output=True, text=True)
            dc = subprocess.run([sys.executable, os.path.join(HERE, 'diffcheck.py'), i, o, '--vectors', '5', '--limit', '400000'],
                                capture_output=True, text=True)
            extra = f' | ssa {"ok" if sc.returncode == 0 else "BAD"} | {dc.stdout.strip().splitlines()[-1]}'
            ok = ok and sc.returncode == 0 and (dc.returncode == 0 or (nonterm and dc.returncode == 2))
        elif open(o).read() != t:
            ok, extra = False, ' | OUT differs from IN with nothing applied'
        bad += not ok
        print(f'{"ok " if ok else "BAD"} {name}: want {want}, got {got}: {detail}{extra}')
print(f'{len(cases) - bad}/{len(cases)} cases as expected')
sys.exit(1 if bad else 0)
