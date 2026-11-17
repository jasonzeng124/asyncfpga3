#!/usr/bin/env bash
# T148: research 8d3e64ccc "Dynamatic's 95 integration tests through the compiler: 12 emit". Own count: bdc/emit.py (clean
# worktree of the commit) on every handshake_transformed.mlir under cloud/fixtures/frontend (including group subdirs),
# default flags and BDC_AUTO=1, exit code 0 and a non-empty .v = emits. Prints per-test results and the tallies; compared
# by name against research's triage.tsv emit column.
set -u
R=/root/wt-t148; O=/root/t148; rm -rf $O; mkdir -p $O
git -C /root/wt-r91 worktree remove --force $R 2>/dev/null; git -C /root/wt-r91 worktree add -q --detach $R 8d3e64ccc
cd $R
for m in $(find cloud/fixtures/frontend -name handshake_transformed.mlir | sort); do
  n=$(echo $m | sed 's#cloud/fixtures/frontend/##; s#/comp/handshake_transformed.mlir##')
  for mode in def auto; do e=""; [ $mode = auto ] && e="BDC_AUTO=1"
    env $e timeout 300 python3 bdc/emit.py $m -o $O/$(echo $n | tr / _)_$mode.v > $O/$(echo $n | tr / _)_$mode.log 2>&1; rc=$?
    ok=FAIL; [ $rc = 0 ] && [ -s $O/$(echo $n | tr / _)_$mode.v ] && ok=ok
    echo -e "$n\t$mode\t$ok"
  done
done > $O/results.tsv
echo "fixtures: $(cut -f1 $O/results.tsv | sort -u | wc -l)"
echo "emit default ok: $(awk -F'\t' '$2=="def" && $3=="ok"' $O/results.tsv | wc -l); auto ok: $(awk -F'\t' '$2=="auto" && $3=="ok"' $O/results.tsv | wc -l)"
awk -F'\t' '$2=="def" && $3=="ok"{print $1}' $O/results.tsv | tr '\n' ' '; echo
